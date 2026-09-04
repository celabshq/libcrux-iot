use libcrux_secrets::I32;

use crate::{
    helper::cloop,
    simd::traits::{Operations, COEFFICIENTS_IN_SIMD_UNIT, SIMD_UNITS_IN_RING_ELEMENT},
};

#[derive(Clone, Copy)]
pub(crate) struct PolynomialRingElement<SIMDUnit: Operations> {
    pub(crate) simd_units: [SIMDUnit; SIMD_UNITS_IN_RING_ELEMENT],
}

// Spec-only impl->spec lift, the Rust counterpart of Lean's
// `Polynomial.HacspecNorm.canon_raw`: regather the 32x8 SIMD layout into a flat
// `[i32; 256]`, canonicalising each lane into `[0, Q)` with the hacspec's own
// `mod_q`.
//
// NAMED `canon_raw`, NOT `lift_poly_res`. The Lean tree has THREE lifts and they
// differ by Montgomery factors -- getting this wrong silently produces an
// unprovable post:
//
//   canon_raw           canonical residue of the RAW lane            (this one)
//   lift_poly_res       canon_raw composed with `* R^-1`             (poly_add/sub/mul, ntt)
//   lift_poly_res_intt  a further `* R^-1` (the impl's intt leaves R) (intt)
//
// `Spec/Lift.lean` puts the factor in `liftZ x = (x : Zq) * RINV`; only
// `canon_raw` omits it, which is why only the infinity-norm theorem speaks this
// lift. The other two need `RINV` as a Rust constant and a modular multiply.
//
// Generic over `SIMDUnit` via the spec-only `Operations::lane`, so it can appear
// in an `#[ensures]` on the generic `PolynomialRingElement` API -- which is the
// whole point, and what a concrete-only version could not do.
#[cfg(hax)]
pub(crate) fn canon_raw<SIMDUnit: Operations>(
    re: &PolynomialRingElement<SIMDUnit>,
) -> [i32; crate::constants::COEFFICIENTS_IN_RING_ELEMENT] {
    core::array::from_fn(|i| {
        hacspec_ml_dsa::arithmetic::mod_q(
            SIMDUnit::lane(&re.simd_units[i / COEFFICIENTS_IN_SIMD_UNIT],
                           i % COEFFICIENTS_IN_SIMD_UNIT) as i64,
        )
    })
}

// Spec-only bound predicates for `infinity_norm_exceeds`'s `#[requires]`.
//
// The FC theorem (`Polynomial/HacspecNorm.lean`, `infinity_norm_exceeds_hacspec_fc`)
// needs every coefficient to be a CENTERED representative, `|c| <= (Q-1)/2`:
// the impl computes the RAW `|coefficient|` while the extracted spec computes
// the centered FIPS norm `coeff_norm`, and the two agree exactly on centered
// values. The FIPS signing context feeds centered values, so this is a
// documented representation choice, not a missing bound. (It also implies the
// impl's own no-overflow precondition `|c| <= 2^30`, since (Q-1)/2 = 4190208.)
//
// Explicit conjunctions, not a loop or `forall`: the generated `pre` is then a
// flat Bool expression the Lean discharge can destructure, the same idiom as
// `coefficients_in_field` in `simd/portable/arithmetic.rs`, lifted to the
// generic level via the spec-only `Operations::lane`.
#[cfg(hax)]
fn lane_centered(x: i32) -> bool {
    -((crate::constants::FIELD_MODULUS - 1) / 2) <= x
        && x <= (crate::constants::FIELD_MODULUS - 1) / 2
}

#[cfg(hax)]
fn unit_centered<SIMDUnit: Operations>(u: &SIMDUnit) -> bool {
    lane_centered(SIMDUnit::lane(u, 0))
        && lane_centered(SIMDUnit::lane(u, 1))
        && lane_centered(SIMDUnit::lane(u, 2))
        && lane_centered(SIMDUnit::lane(u, 3))
        && lane_centered(SIMDUnit::lane(u, 4))
        && lane_centered(SIMDUnit::lane(u, 5))
        && lane_centered(SIMDUnit::lane(u, 6))
        && lane_centered(SIMDUnit::lane(u, 7))
}

#[cfg(hax)]
pub(crate) fn coefficients_centered<SIMDUnit: Operations>(
    re: &PolynomialRingElement<SIMDUnit>,
) -> bool {
    unit_centered(&re.simd_units[0])
        && unit_centered(&re.simd_units[1])
        && unit_centered(&re.simd_units[2])
        && unit_centered(&re.simd_units[3])
        && unit_centered(&re.simd_units[4])
        && unit_centered(&re.simd_units[5])
        && unit_centered(&re.simd_units[6])
        && unit_centered(&re.simd_units[7])
        && unit_centered(&re.simd_units[8])
        && unit_centered(&re.simd_units[9])
        && unit_centered(&re.simd_units[10])
        && unit_centered(&re.simd_units[11])
        && unit_centered(&re.simd_units[12])
        && unit_centered(&re.simd_units[13])
        && unit_centered(&re.simd_units[14])
        && unit_centered(&re.simd_units[15])
        && unit_centered(&re.simd_units[16])
        && unit_centered(&re.simd_units[17])
        && unit_centered(&re.simd_units[18])
        && unit_centered(&re.simd_units[19])
        && unit_centered(&re.simd_units[20])
        && unit_centered(&re.simd_units[21])
        && unit_centered(&re.simd_units[22])
        && unit_centered(&re.simd_units[23])
        && unit_centered(&re.simd_units[24])
        && unit_centered(&re.simd_units[25])
        && unit_centered(&re.simd_units[26])
        && unit_centered(&re.simd_units[27])
        && unit_centered(&re.simd_units[28])
        && unit_centered(&re.simd_units[29])
        && unit_centered(&re.simd_units[30])
        && unit_centered(&re.simd_units[31])
}

// Spec-only impl->spec lift, the Rust counterpart of Lean's
// `Spec.HacspecBridge.lift_poly_res`: `canon_raw` composed with the Montgomery
// factor strip `* R^-1` (`Spec/Lift.lean`: `liftZ x = (x : Zq) * RINV`,
// `Spec/Montgomery.lean`: `RINV = 8265825`). One `mod_q` suffices:
// `|lane| * RINV < 2^31 * 2^23 = 2^54` fits an i64, and the residue class of
// `lane * RINV` IS `liftZ lane`.
//
// This is the lift the poly_add/poly_sub/poly_pointwise_mul and ntt top-level
// theorems speak (see the three-lift table at `canon_raw` above).
#[cfg(hax)]
pub(crate) const RINV: i64 = 8_265_825;

#[cfg(hax)]
pub(crate) fn lift_poly_res<SIMDUnit: Operations>(
    re: &PolynomialRingElement<SIMDUnit>,
) -> [i32; crate::constants::COEFFICIENTS_IN_RING_ELEMENT] {
    core::array::from_fn(|i| {
        hacspec_ml_dsa::arithmetic::mod_q(
            SIMDUnit::lane(&re.simd_units[i / COEFFICIENTS_IN_SIMD_UNIT],
                           i % COEFFICIENTS_IN_SIMD_UNIT) as i64
                * RINV,
        )
    })
}

// Spec-only per-lane no-overflow predicates for `add`/`subtract`'s
// `#[requires]`: the FC theorems (`Polynomial/HacspecFC.lean`) need
// `|a ± b| <= i32::MAX` per lane (the impl adds/subtracts lanes directly).
// The sums are computed in i64 so the PREDICATE cannot itself overflow.
// Explicit conjunctions, as for `coefficients_centered` above.
#[cfg(hax)]
fn lane_add_in_range(x: i32, y: i32) -> bool {
    -2_147_483_647 <= (x as i64) + (y as i64) && (x as i64) + (y as i64) <= 2_147_483_647
}

#[cfg(hax)]
fn lane_sub_in_range(x: i32, y: i32) -> bool {
    -2_147_483_647 <= (x as i64) - (y as i64) && (x as i64) - (y as i64) <= 2_147_483_647
}

#[cfg(hax)]
fn unit_add_in_range<SIMDUnit: Operations>(a: &SIMDUnit, b: &SIMDUnit) -> bool {
    lane_add_in_range(SIMDUnit::lane(a, 0), SIMDUnit::lane(b, 0))
        && lane_add_in_range(SIMDUnit::lane(a, 1), SIMDUnit::lane(b, 1))
        && lane_add_in_range(SIMDUnit::lane(a, 2), SIMDUnit::lane(b, 2))
        && lane_add_in_range(SIMDUnit::lane(a, 3), SIMDUnit::lane(b, 3))
        && lane_add_in_range(SIMDUnit::lane(a, 4), SIMDUnit::lane(b, 4))
        && lane_add_in_range(SIMDUnit::lane(a, 5), SIMDUnit::lane(b, 5))
        && lane_add_in_range(SIMDUnit::lane(a, 6), SIMDUnit::lane(b, 6))
        && lane_add_in_range(SIMDUnit::lane(a, 7), SIMDUnit::lane(b, 7))
}

#[cfg(hax)]
fn unit_sub_in_range<SIMDUnit: Operations>(a: &SIMDUnit, b: &SIMDUnit) -> bool {
    lane_sub_in_range(SIMDUnit::lane(a, 0), SIMDUnit::lane(b, 0))
        && lane_sub_in_range(SIMDUnit::lane(a, 1), SIMDUnit::lane(b, 1))
        && lane_sub_in_range(SIMDUnit::lane(a, 2), SIMDUnit::lane(b, 2))
        && lane_sub_in_range(SIMDUnit::lane(a, 3), SIMDUnit::lane(b, 3))
        && lane_sub_in_range(SIMDUnit::lane(a, 4), SIMDUnit::lane(b, 4))
        && lane_sub_in_range(SIMDUnit::lane(a, 5), SIMDUnit::lane(b, 5))
        && lane_sub_in_range(SIMDUnit::lane(a, 6), SIMDUnit::lane(b, 6))
        && lane_sub_in_range(SIMDUnit::lane(a, 7), SIMDUnit::lane(b, 7))
}

#[cfg(hax)]
pub(crate) fn poly_add_in_range<SIMDUnit: Operations>(
    a: &PolynomialRingElement<SIMDUnit>,
    b: &PolynomialRingElement<SIMDUnit>,
) -> bool {
    unit_add_in_range(&a.simd_units[0], &b.simd_units[0])
        && unit_add_in_range(&a.simd_units[1], &b.simd_units[1])
        && unit_add_in_range(&a.simd_units[2], &b.simd_units[2])
        && unit_add_in_range(&a.simd_units[3], &b.simd_units[3])
        && unit_add_in_range(&a.simd_units[4], &b.simd_units[4])
        && unit_add_in_range(&a.simd_units[5], &b.simd_units[5])
        && unit_add_in_range(&a.simd_units[6], &b.simd_units[6])
        && unit_add_in_range(&a.simd_units[7], &b.simd_units[7])
        && unit_add_in_range(&a.simd_units[8], &b.simd_units[8])
        && unit_add_in_range(&a.simd_units[9], &b.simd_units[9])
        && unit_add_in_range(&a.simd_units[10], &b.simd_units[10])
        && unit_add_in_range(&a.simd_units[11], &b.simd_units[11])
        && unit_add_in_range(&a.simd_units[12], &b.simd_units[12])
        && unit_add_in_range(&a.simd_units[13], &b.simd_units[13])
        && unit_add_in_range(&a.simd_units[14], &b.simd_units[14])
        && unit_add_in_range(&a.simd_units[15], &b.simd_units[15])
        && unit_add_in_range(&a.simd_units[16], &b.simd_units[16])
        && unit_add_in_range(&a.simd_units[17], &b.simd_units[17])
        && unit_add_in_range(&a.simd_units[18], &b.simd_units[18])
        && unit_add_in_range(&a.simd_units[19], &b.simd_units[19])
        && unit_add_in_range(&a.simd_units[20], &b.simd_units[20])
        && unit_add_in_range(&a.simd_units[21], &b.simd_units[21])
        && unit_add_in_range(&a.simd_units[22], &b.simd_units[22])
        && unit_add_in_range(&a.simd_units[23], &b.simd_units[23])
        && unit_add_in_range(&a.simd_units[24], &b.simd_units[24])
        && unit_add_in_range(&a.simd_units[25], &b.simd_units[25])
        && unit_add_in_range(&a.simd_units[26], &b.simd_units[26])
        && unit_add_in_range(&a.simd_units[27], &b.simd_units[27])
        && unit_add_in_range(&a.simd_units[28], &b.simd_units[28])
        && unit_add_in_range(&a.simd_units[29], &b.simd_units[29])
        && unit_add_in_range(&a.simd_units[30], &b.simd_units[30])
        && unit_add_in_range(&a.simd_units[31], &b.simd_units[31])
}

#[cfg(hax)]
pub(crate) fn poly_sub_in_range<SIMDUnit: Operations>(
    a: &PolynomialRingElement<SIMDUnit>,
    b: &PolynomialRingElement<SIMDUnit>,
) -> bool {
    unit_sub_in_range(&a.simd_units[0], &b.simd_units[0])
        && unit_sub_in_range(&a.simd_units[1], &b.simd_units[1])
        && unit_sub_in_range(&a.simd_units[2], &b.simd_units[2])
        && unit_sub_in_range(&a.simd_units[3], &b.simd_units[3])
        && unit_sub_in_range(&a.simd_units[4], &b.simd_units[4])
        && unit_sub_in_range(&a.simd_units[5], &b.simd_units[5])
        && unit_sub_in_range(&a.simd_units[6], &b.simd_units[6])
        && unit_sub_in_range(&a.simd_units[7], &b.simd_units[7])
        && unit_sub_in_range(&a.simd_units[8], &b.simd_units[8])
        && unit_sub_in_range(&a.simd_units[9], &b.simd_units[9])
        && unit_sub_in_range(&a.simd_units[10], &b.simd_units[10])
        && unit_sub_in_range(&a.simd_units[11], &b.simd_units[11])
        && unit_sub_in_range(&a.simd_units[12], &b.simd_units[12])
        && unit_sub_in_range(&a.simd_units[13], &b.simd_units[13])
        && unit_sub_in_range(&a.simd_units[14], &b.simd_units[14])
        && unit_sub_in_range(&a.simd_units[15], &b.simd_units[15])
        && unit_sub_in_range(&a.simd_units[16], &b.simd_units[16])
        && unit_sub_in_range(&a.simd_units[17], &b.simd_units[17])
        && unit_sub_in_range(&a.simd_units[18], &b.simd_units[18])
        && unit_sub_in_range(&a.simd_units[19], &b.simd_units[19])
        && unit_sub_in_range(&a.simd_units[20], &b.simd_units[20])
        && unit_sub_in_range(&a.simd_units[21], &b.simd_units[21])
        && unit_sub_in_range(&a.simd_units[22], &b.simd_units[22])
        && unit_sub_in_range(&a.simd_units[23], &b.simd_units[23])
        && unit_sub_in_range(&a.simd_units[24], &b.simd_units[24])
        && unit_sub_in_range(&a.simd_units[25], &b.simd_units[25])
        && unit_sub_in_range(&a.simd_units[26], &b.simd_units[26])
        && unit_sub_in_range(&a.simd_units[27], &b.simd_units[27])
        && unit_sub_in_range(&a.simd_units[28], &b.simd_units[28])
        && unit_sub_in_range(&a.simd_units[29], &b.simd_units[29])
        && unit_sub_in_range(&a.simd_units[30], &b.simd_units[30])
        && unit_sub_in_range(&a.simd_units[31], &b.simd_units[31])
}

// `hax_lib::attributes` so that methods of this inherent impl can carry
// `#[hax_lib::requires]`/`#[ensures]` (they mention `Self`; the plain macros
// reject that outside an annotated block).
#[cfg_attr(hax, hax_lib::attributes)]
impl<SIMDUnit: Operations> PolynomialRingElement<SIMDUnit> {
    pub(crate) fn zero() -> Self {
        Self {
            simd_units: [SIMDUnit::zero(); SIMD_UNITS_IN_RING_ELEMENT],
        }
    }

    // This is used in `make_hint` and for tests
    pub(crate) fn to_i32_array(&self) -> [i32; 256] {
        let mut result = [0i32; 256];

        cloop! {
            for (i, simd_unit) in self.simd_units.iter().enumerate() {
                SIMDUnit::to_coefficient_array(simd_unit, &mut result[i * COEFFICIENTS_IN_SIMD_UNIT..(i + 1) * COEFFICIENTS_IN_SIMD_UNIT]);
            }
        }

        result
    }

    pub(crate) fn from_i32_array(array: &[I32], result: &mut Self) {
        #[cfg(not(eurydice))]
        debug_assert!(array.len() >= 256);
        for i in 0..SIMD_UNITS_IN_RING_ELEMENT {
            SIMDUnit::from_coefficient_array(
                &array[i * COEFFICIENTS_IN_SIMD_UNIT..(i + 1) * COEFFICIENTS_IN_SIMD_UNIT],
                &mut result.simd_units[i],
            );
        }
        // [hax] https://github.com/hacspec/hax/issues/720
        ()
    }

    #[cfg(test)]
    pub(crate) fn from_i32_array_test(array: &[I32]) -> Self {
        let mut result = PolynomialRingElement::zero();
        Self::from_i32_array(array, &mut result);
        result
    }

    #[inline(always)]
    // Full functional correctness against the extracted FIPS-204 hacspec: the
    // spec has no direct `infinity_norm_exceeds`, so the post states the
    // equivalence through `poly_infinity_norm` on the canonical-residue array
    // `canon_raw(self)` -- exactly the shape of the FC theorem
    // `infinity_norm_exceeds_hacspec_fc` (`Polynomial/HacspecNorm.lean`).
    // `canon_raw`, not `lift_poly_res`: the norm theorem is the one place the
    // RAW (Montgomery-domain-agnostic) lift is the right one; see the note at
    // `canon_raw`'s definition.
    #[cfg_attr(hax, hax_lib::requires(coefficients_centered(self)))]
    #[cfg_attr(hax, hax_lib::ensures(|result| result
        == (bound <= hacspec_ml_dsa::polynomial::poly_infinity_norm(&canon_raw(self)))))]
    pub(crate) fn infinity_norm_exceeds(&self, bound: i32) -> bool {
        let mut result = false;
        for i in 0..self.simd_units.len() {
            result = result || SIMDUnit::infinity_norm_exceeds(&self.simd_units[i], bound);
        }

        result
    }

    #[inline(always)]
    // Full functional correctness against the extracted FIPS-204 hacspec, the
    // README's `poly_add_hacspec_fc` stated at the Rust level: the outputs of
    // impl `add` and spec `poly_add` agree through the Montgomery-stripping
    // lift `lift_poly_res`. `self` in the `ensures` is the INPUT value,
    // `future(self)` the output.
    #[cfg_attr(hax, hax_lib::requires(poly_add_in_range(self, rhs)))]
    #[cfg_attr(hax, hax_lib::ensures(|_|
        hacspec_ml_dsa::polynomial::poly_add(&lift_poly_res(self), &lift_poly_res(rhs))
            == lift_poly_res(future(self))))]
    pub(crate) fn add(&mut self, rhs: &Self) {
        for i in 0..self.simd_units.len() {
            SIMDUnit::add(&mut self.simd_units[i], &rhs.simd_units[i]);
        }
        // [hax] https://github.com/hacspec/hax/issues/720
        ()
    }

    #[inline(always)]
    // `poly_sub_hacspec_fc` at the Rust level; see `add` above.
    #[cfg_attr(hax, hax_lib::requires(poly_sub_in_range(self, rhs)))]
    #[cfg_attr(hax, hax_lib::ensures(|_|
        hacspec_ml_dsa::polynomial::poly_sub(&lift_poly_res(self), &lift_poly_res(rhs))
            == lift_poly_res(future(self))))]
    pub(crate) fn subtract(&mut self, rhs: &Self) {
        for i in 0..self.simd_units.len() {
            SIMDUnit::subtract(&mut self.simd_units[i], &rhs.simd_units[i]);
        }
        // [hax] https://github.com/hacspec/hax/issues/720
        ()
    }
}
