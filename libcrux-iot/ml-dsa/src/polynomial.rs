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
    pub(crate) fn infinity_norm_exceeds(&self, bound: i32) -> bool {
        let mut result = false;
        for i in 0..self.simd_units.len() {
            result = result || SIMDUnit::infinity_norm_exceeds(&self.simd_units[i], bound);
        }

        result
    }

    #[inline(always)]
    pub(crate) fn add(&mut self, rhs: &Self) {
        for i in 0..self.simd_units.len() {
            SIMDUnit::add(&mut self.simd_units[i], &rhs.simd_units[i]);
        }
        // [hax] https://github.com/hacspec/hax/issues/720
        ()
    }

    #[inline(always)]
    pub(crate) fn subtract(&mut self, rhs: &Self) {
        for i in 0..self.simd_units.len() {
            SIMDUnit::subtract(&mut self.simd_units[i], &rhs.simd_units[i]);
        }
        // [hax] https://github.com/hacspec/hax/issues/720
        ()
    }
}
