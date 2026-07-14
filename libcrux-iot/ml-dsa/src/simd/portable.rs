use crate::{
    constants::{Eta, Gamma2},
    simd::traits::{Operations, SIMD_UNITS_IN_RING_ELEMENT},
};
#[cfg(hax)]
use crate::{
    constants::{GAMMA2_V261_888, GAMMA2_V95_232},
    simd::traits::COEFFICIENTS_IN_SIMD_UNIT,
};

mod arithmetic;
mod vector_type;
// Some of the portable implementations are used in lieu of vectorized ones in
// the AVX2 module.
pub(crate) mod encoding;
mod invntt;
mod ntt;
mod sample;

use libcrux_secrets::{I32, U8};
/// Portable SIMD coefficients
pub(crate) use vector_type::Coefficients as PortableSIMDUnit;
use vector_type::Coefficients;

#[hax_lib::attributes]
impl Operations for Coefficients {
    fn zero() -> Coefficients {
        vector_type::zero()
    }

    #[hax_lib::requires(array.len() == COEFFICIENTS_IN_SIMD_UNIT)]
    fn from_coefficient_array(array: &[I32], out: &mut Coefficients) {
        vector_type::from_coefficient_array(array, out)
    }

    #[hax_lib::requires(out.len() == COEFFICIENTS_IN_SIMD_UNIT)]
    #[hax_lib::ensures(|result| future(out).len() == out.len())]
    fn to_coefficient_array(value: &Coefficients, out: &mut [i32]) {
        vector_type::to_coefficient_array(value, out)
    }

    fn add(lhs: &mut Coefficients, rhs: &Coefficients) {
        arithmetic::add(lhs, rhs)
    }

    fn subtract(lhs: &mut Coefficients, rhs: &Coefficients) {
        arithmetic::subtract(lhs, rhs)
    }

    fn montgomery_multiply(lhs: &mut Coefficients, rhs: &Coefficients) {
        arithmetic::montgomery_multiply(lhs, rhs);
    }

    #[hax_lib::requires(SHIFT_BY >= 0 && SHIFT_BY < 32)]
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Coefficients) {
        arithmetic::shift_left_then_reduce::<SHIFT_BY>(simd_unit);
    }

    fn power2round(t0: &mut Coefficients, t1: &mut Coefficients) {
        arithmetic::power2round(t0, t1)
    }

    fn infinity_norm_exceeds(simd_unit: &Coefficients, bound: i32) -> bool {
        arithmetic::infinity_norm_exceeds(simd_unit, bound)
    }

    #[hax_lib::requires(gamma2 == GAMMA2_V95_232 || gamma2 == GAMMA2_V261_888)]
    fn decompose(gamma2: Gamma2, simd_unit: &Self, low: &mut Self, high: &mut Self) {
        arithmetic::decompose(gamma2, simd_unit, low, high)
    }

    #[hax_lib::requires(gamma2 != i32::MIN)]
    fn compute_hint(
        low: &Coefficients,
        high: &Coefficients,
        gamma2: i32,
        hint: &mut Coefficients,
    ) -> usize {
        arithmetic::compute_hint(low, high, gamma2, hint)
    }

    #[hax_lib::requires(gamma2 == GAMMA2_V95_232 || gamma2 == GAMMA2_V261_888)]
    fn use_hint(gamma2: Gamma2, simd_unit: &Coefficients, hint: &mut Coefficients) {
        arithmetic::use_hint(gamma2, simd_unit, hint)
    }

    #[hax_lib::requires(randomness.len() / 3 <= 4_294_967_295 && out.len() >= randomness.len() / 3)]
    #[hax_lib::ensures(|_| out.len() == future(out).len())]
    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize {
        sample::rejection_sample_less_than_field_modulus(randomness, out)
    }

    #[hax_lib::requires(randomness.len() <= 4_294_967_295 / 2 && randomness.len() * 2 <= out.len())]
    #[hax_lib::ensures(|_| out.len() == future(out).len())]
    fn rejection_sample_less_than_eta_equals_2(randomness: &[U8], out: &mut [I32]) -> usize {
        sample::rejection_sample_less_than_eta_equals_2(randomness, out)
    }

    #[hax_lib::requires(randomness.len() <= 4_294_967_295 / 2 && randomness.len() * 2 <= out.len())]
    #[hax_lib::ensures(|_| out.len() == future(out).len())]
    fn rejection_sample_less_than_eta_equals_4(randomness: &[U8], out: &mut [I32]) -> usize {
        sample::rejection_sample_less_than_eta_equals_4(randomness, out)
    }

    #[hax_lib::requires(
    match gamma1_exponent {
        17 => serialized.len() == 18,
        19 => serialized.len() == 20,
        _ => false
})]
    #[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
    fn gamma1_serialize(simd_unit: &Coefficients, serialized: &mut [u8], gamma1_exponent: usize) {
        encoding::gamma1::serialize(simd_unit, serialized, gamma1_exponent)
    }

    #[hax_lib::requires(
    match gamma1_exponent {
        17 => serialized.len() == 18,
        19 => serialized.len() == 20,
        _ => false
})]
    fn gamma1_deserialize(serialized: &[U8], out: &mut Coefficients, gamma1_exponent: usize) {
        encoding::gamma1::deserialize(serialized, out, gamma1_exponent)
    }

    #[hax_lib::requires(
    match serialized.len() {
        4 | 6 => true,
        _ => false
    }
)]
    #[hax_lib::ensures(|out| future(serialized).len() == serialized.len())]
    fn commitment_serialize(simd_unit: &Coefficients, serialized: &mut [U8]) {
        encoding::commitment::serialize(simd_unit, serialized)
    }

    #[hax_lib::requires(
    match eta {
        Eta::Two => serialized.len() == 3,
        Eta::Four => serialized.len() == 4,
        _ => false
})]
    #[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
    fn error_serialize(eta: Eta, simd_unit: &Coefficients, serialized: &mut [U8]) {
        encoding::error::serialize(eta, simd_unit, serialized)
    }

    #[hax_lib::requires(serialized.len() == (match eta { Eta::Two => 3, Eta::Four => 4 }))]
    fn error_deserialize(eta: Eta, serialized: &[U8], out: &mut Coefficients) {
        encoding::error::deserialize(eta, serialized, out);
    }

    #[hax_lib::requires(out.len() == 13)]
    #[hax_lib::ensures(|_| future(out).len() == out.len())]
    fn t0_serialize(simd_unit: &Coefficients, out: &mut [U8]) {
        encoding::t0::serialize(simd_unit, out)
    }

    #[hax_lib::requires(serialized.len() == 13)]
    fn t0_deserialize(serialized: &[U8], out: &mut Coefficients) {
        encoding::t0::deserialize(serialized, out)
    }

    #[hax_lib::requires(out.len() == 10)]
    #[hax_lib::ensures(|_| future(out).len() == out.len())]
    fn t1_serialize(simd_unit: &Self, out: &mut [u8]) {
        encoding::t1::serialize(simd_unit, out);
    }

    #[hax_lib::requires(serialized.len() == 10)]
    fn t1_deserialize(serialized: &[u8], out: &mut Self) {
        encoding::t1::deserialize(serialized, out);
    }

    fn ntt(simd_units: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
        ntt::ntt(simd_units)
    }

    fn invert_ntt_montgomery(simd_units: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
        invntt::invert_ntt_montgomery(simd_units)
    }

    fn reduce(simd_units: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
        for i in 0..simd_units.len() {
            arithmetic::shift_left_then_reduce::<0>(&mut simd_units[i]);
        }
    }
}
