#[cfg(feature = "check-secret-independence")]
use libcrux_secrets::IntOps as _;
use libcrux_secrets::{CastOps as _, Classify as _, Declassify as _, I32, I64, U64};

use super::vector_type::{Coefficients, FieldElement};
use crate::{
    constants::{Gamma2, BITS_IN_LOWER_PART_OF_T, GAMMA2_V261_888, GAMMA2_V95_232},
    simd::traits::{
        FieldElementTimesMontgomeryR, FIELD_MODULUS, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R,
    },
};

pub(crate) const MONTGOMERY_SHIFT: u8 = 32;

#[inline(always)]
pub fn add(lhs: &mut Coefficients, rhs: &Coefficients) {
    for i in 0..lhs.values.len() {
        lhs.values[i] = lhs.values[i].wrapping_add(rhs.values[i]);
    }
}

#[inline(always)]
pub fn subtract(lhs: &mut Coefficients, rhs: &Coefficients) {
    for i in 0..lhs.values.len() {
        lhs.values[i] = lhs.values[i].wrapping_sub(rhs.values[i]);
    }
}

#[inline(always)]
#[hax_lib::requires(n < 64)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub(crate) fn get_n_least_significant_bits(n: u8, value: U64) -> U64 {
    value & ((1u64 << n).wrapping_sub(1)) // XXX: Get rid of wrapping sub
}

#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub(crate) fn montgomery_reduce_element(value: I64) -> FieldElementTimesMontgomeryR {
    let t = get_n_least_significant_bits(MONTGOMERY_SHIFT, value.as_u64())
        .wrapping_mul(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R);
    let k = get_n_least_significant_bits(MONTGOMERY_SHIFT, t).as_i32();

    let k_times_modulus = (k.as_i64()).wrapping_mul((FIELD_MODULUS as i64).classify());

    let c = (k_times_modulus >> MONTGOMERY_SHIFT).as_i32();
    let value_high = (value >> MONTGOMERY_SHIFT).as_i32();

    value_high.wrapping_sub(c)
}

#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub(crate) fn montgomery_multiply_fe_by_fer(
    fe: FieldElement,
    fer: FieldElementTimesMontgomeryR,
) -> FieldElement {
    montgomery_reduce_element((fe.as_i64()).wrapping_mul(fer.as_i64()))
}

#[inline(always)]
pub(crate) fn montgomery_multiply_by_constant(simd_unit: &mut Coefficients, c: I32) {
    for i in 0..simd_unit.values.len() {
        simd_unit.values[i] =
            montgomery_reduce_element((simd_unit.values[i].as_i64()).wrapping_mul(c.as_i64()))
    }
}

#[inline(always)]
pub(crate) fn montgomery_multiply(lhs: &mut Coefficients, rhs: &Coefficients) {
    for i in 0..lhs.values.len() {
        lhs.values[i] =
            montgomery_reduce_element((lhs.values[i].as_i64()).wrapping_mul(rhs.values[i].as_i64()))
    }
}

// Splits t ∈ {0, ..., q-1} into t0 and t1 with a = t1*2ᴰ + t0
// and -2ᴰ⁻¹ < t0 < 2ᴰ⁻¹.  Returns t0 and t1 computed as.
//
// - t0 = t mod± 2ᵈ
// - t1 = (t - t0) / 2ᵈ.
//
// We assume the input t is in the signed representative range and convert it
// to the standard unsigned range.
#[inline(always)]
fn power2round_element(t: I32) -> (I32, I32) {
    // Hax issue: https://github.com/hacspec/hax/issues/1082
    // XXX: Below debug assert violates the classification regime
    // in Debug mode. It should be a precondition for hax
    // instead.
    // #[cfg(not(eurydice))]
    // debug_assert!(t > -FIELD_MODULUS && t < FIELD_MODULUS);

    // Convert the signed representative to the standard unsigned one.
    let t = t.wrapping_add((t >> 31) & FIELD_MODULUS);

    // t0 = t - (2^{BITS_IN_LOWER_PART_OF_T} * t1)
    // t1 = ⌊(t - 1)/2^{BITS_IN_LOWER_PART_OF_T} + 1/2⌋
    //
    // See Lemma 10 of the implementation notes document for more information
    // on what these compute.
    let t1 = (t
        .wrapping_sub(1)
        .wrapping_add(1 << (BITS_IN_LOWER_PART_OF_T - 1)))
        >> BITS_IN_LOWER_PART_OF_T;
    let t0 = t.wrapping_sub(t1 << BITS_IN_LOWER_PART_OF_T);

    (t0, t1)
}

#[inline(always)]
pub(super) fn power2round(t0: &mut Coefficients, t1: &mut Coefficients) {
    for i in 0..t0.values.len() {
        (t0.values[i], t1.values[i]) = power2round_element(t0.values[i]);
    }
}

// TODO: Revisit this function when doing the range analysis and testing
// additional KATs.
#[inline(always)]
pub(super) fn infinity_norm_exceeds(simd_unit: &Coefficients, bound: i32) -> bool {
    let mut result = false;
    // Declassification: It is ok to leak which coefficient violates the bound since
    // the probability for each coefficient is independent of secret
    // data but we must not leak the sign of the centralized representative.
    for i in 0..simd_unit.values.len() {
        let coefficient = simd_unit.values[i];
        // XXX: Below debug assert violates the classification regime
        // in Debug mode. It should be a precondition for hax
        // instead.
        // #[cfg(not(eurydice))]
        // debug_assert!(
        //     coefficient > -FIELD_MODULUS && coefficient < FIELD_MODULUS
        // );

        // This norm is calculated using the absolute value of the
        // signed representative in the range:
        //
        // -FIELD_MODULUS / 2 < r <= FIELD_MODULUS / 2.
        //
        // So if the coefficient is negative, get its absolute value, but
        // don't convert it into a different representation.
        let sign = coefficient >> 31;
        let normalized =
            coefficient.wrapping_sub(sign & (2i32.classify().wrapping_mul(coefficient)));

        // FIXME: return
        // [hax] https://github.com/hacspec/hax/issues/1204
        result = result || normalized.declassify() >= bound;
    }

    result
}

#[inline(always)]
fn reduce_element(fe: FieldElement) -> FieldElement {
    let quotient = (fe.wrapping_add(1 << 22)) >> 23;

    fe.wrapping_sub(quotient.wrapping_mul(FIELD_MODULUS))
}

#[inline(always)]
#[hax_lib::requires(SHIFT_BY >= 0 && SHIFT_BY < 32)]
pub(super) fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Coefficients) {
    for i in 0..simd_unit.values.len() {
        simd_unit.values[i] = reduce_element(simd_unit.values[i] << SHIFT_BY);
    }
}

#[inline(always)]
#[hax_lib::requires(gamma2 != i32::MIN)]
#[hax_lib::ensures(|out| out >= 0 && out <= 1)]
fn compute_one_hint(low: i32, high: i32, gamma2: i32) -> i32 {
    if (low > gamma2) || (low < -gamma2) || (low == -gamma2 && high != 0) {
        1
    } else {
        0
    }
}

#[inline(always)]
#[hax_lib::requires(gamma2 != i32::MIN)]
pub(super) fn compute_hint(
    low: &Coefficients,
    high: &Coefficients,
    gamma2: i32,
    hint: &mut Coefficients,
) -> usize {
    let mut one_hints_count = 0;

    // Declassifications: The hint values are not secret, but we store
    // them in `Coefficients` structs which treat their elements as
    // secret by default.
    for i in 0..hint.values.len() {
        hax_lib::loop_invariant!(|i: usize| one_hints_count <= i);
        hint.values[i] = compute_one_hint(
            low.values[i].declassify(),
            high.values[i].declassify(),
            gamma2,
        )
        .classify();
        one_hints_count += hint.values[i].declassify() as usize;
    }

    one_hints_count
}

// Take a representative -q < r < q and convert it
// to the standard unsigned one in the interval [0, q).
//
// Splits this representative r into r₀ and r₁ such that:
//
// - r = r₁*α + r₀
// - -α/2 < r₀ ≤ α/2
//
// except when r₁ = (q-1)/α; in this case:
//
// - r₁ is set to 0 is taken
// - α/2 ≤ r₀ < 0.
//
// Note that 0 ≤ r₁ < (q-1)/α.
#[inline(always)]
#[hax_lib::requires(gamma2 == GAMMA2_V95_232 || gamma2 == GAMMA2_V261_888)]
fn decompose_element(gamma2: Gamma2, r: I32) -> (I32, I32) {
    // #[cfg(not(eurydice))]
    // // XXX: Below debug assert violates the classification regime
    // // in Debug mode. It should be a precondition for hax
    // // instead.
    // debug_assert!(r > -FIELD_MODULUS && r < FIELD_MODULUS);

    // Convert the signed representative to the standard unsigned one.
    let r = r.wrapping_add((r >> 31) & FIELD_MODULUS);

    let r1 = {
        // Compute ⌈r / 128⌉
        let ceil_of_r_by_128 = (r.wrapping_add(127)) >> 7;

        match gamma2 {
            GAMMA2_V95_232 => {
                // We approximate 1 / 1488 as:
                // ⌊2²⁴ / 1488⌋ / 2²⁴ = 11,275 / 2²⁴
                let result = ((ceil_of_r_by_128.wrapping_mul(11_275)).wrapping_add(1 << 23)) >> 24;

                // For the corner-case a₁ = (q-1)/α = 44, we have to set a₁=0.
                (result ^ (43i32.classify().wrapping_sub(result)) >> 31) & result
            }
            GAMMA2_V261_888 => {
                // We approximate 1 / 4092 as:
                // ⌊2²² / 4092⌋ / 2²² = 1025 / 2²²
                let result = (ceil_of_r_by_128.wrapping_mul(1025).wrapping_add(1 << 21)) >> 22;

                // For the corner-case a₁ = (q-1)/α = 16, we have to set a₁=0.
                result & 15
            }

            _ => unreachable!(),
        }
    };

    let alpha = gamma2 * 2;
    let mut r0 = r.wrapping_sub(r1.wrapping_mul(alpha));

    // In the corner-case, when we set a₁=0, we will incorrectly
    // have a₀ > (q-1)/2 and we'll need to subtract q.  As we
    // return a₀ + q, that comes down to adding q if a₀ < (q-1)/2.
    r0 = r0.wrapping_sub(
        ((((FIELD_MODULUS - 1) / 2).classify().wrapping_sub(r0)) >> 31) & FIELD_MODULUS,
    );

    (r0, r1)
}

#[inline(always)]
#[hax_lib::requires(gamma2 == GAMMA2_V95_232 || gamma2 == GAMMA2_V261_888)]
pub(crate) fn use_one_hint(gamma2: Gamma2, r: i32, hint: i32) -> i32 {
    let (r0, r1) = decompose_element(gamma2, r.classify());

    // Declassification: Hint values are not secret.
    let (r0, r1) = (r0.declassify(), r1.declassify());
    if hint == 0 {
        return r1;
    }

    match gamma2 {
        GAMMA2_V95_232 => {
            if r0 > 0 {
                if r1 == 43 {
                    0
                } else {
                    r1.wrapping_add(hint)
                }
            } else if r1 == 0 {
                43
            } else {
                r1.wrapping_sub(hint)
            }
        }

        GAMMA2_V261_888 => {
            if r0 > 0 {
                (r1.wrapping_add(hint)) & 15
            } else {
                (r1.wrapping_sub(hint)) & 15
            }
        }

        _ => unreachable!(),
    }
}

#[inline(always)]
#[hax_lib::requires(gamma2 == GAMMA2_V95_232 || gamma2 == GAMMA2_V261_888)]
pub fn decompose(
    gamma2: Gamma2,
    simd_unit: &Coefficients,
    low: &mut Coefficients,
    high: &mut Coefficients,
) {
    for i in 0..low.values.len() {
        (low.values[i], high.values[i]) = decompose_element(gamma2, simd_unit.values[i]);
    }
}

#[inline(always)]
#[hax_lib::requires(gamma2 == GAMMA2_V95_232 || gamma2 == GAMMA2_V261_888)]
pub fn use_hint(gamma2: Gamma2, simd_unit: &Coefficients, hint: &mut Coefficients) {
    for i in 0..hint.values.len() {
        // Declassifications: The hint values themselves are not
        // secret, but we classify them to store them in a
        // `Coefficients` struct.
        hint.values[i] = use_one_hint(
            gamma2,
            simd_unit.values[i].declassify(),
            hint.values[i].declassify(),
        )
        .classify();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_montgomery_reduce_element() {
        assert_eq!(
            montgomery_reduce_element(10933346042510.classify()).declassify(),
            -1553279
        );
        assert_eq!(
            montgomery_reduce_element((-20392060523118).classify()).declassify(),
            1331779
        );
        assert_eq!(
            montgomery_reduce_element(13704140696092.classify()).declassify(),
            -1231016
        );
        assert_eq!(
            montgomery_reduce_element((-631922212176).classify()).declassify(),
            -2580954
        );
    }

    #[test]
    fn test_use_one_hint() {
        assert_eq!(use_one_hint(GAMMA2_V95_232, 7622170, 0), 40);
        assert_eq!(use_one_hint(GAMMA2_V95_232, 2332762, 1), 13);

        assert_eq!(use_one_hint(GAMMA2_V261_888, 7691572, 0), 15);
        assert_eq!(use_one_hint(GAMMA2_V261_888, 6635697, 1), 12);
    }
}
