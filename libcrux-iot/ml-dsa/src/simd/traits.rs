use libcrux_secrets::{I32, U8};

use crate::constants::{Eta, Gamma2};
#[cfg(hax)]
use crate::constants::{GAMMA2_V261_888, GAMMA2_V95_232};

// Each field element occupies 32 bits and the size of a simd_unit is 256 bits.
pub(crate) const COEFFICIENTS_IN_SIMD_UNIT: usize = 8;

pub(crate) const SIMD_UNITS_IN_RING_ELEMENT: usize =
    crate::constants::COEFFICIENTS_IN_RING_ELEMENT / COEFFICIENTS_IN_SIMD_UNIT;

pub const FIELD_MODULUS: i32 = 8_380_417;

// FIELD_MODULUS^{-1} mod MONTGOMERY_R
pub const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u64 = 58_728_449;

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R (mod FIELD_MODULUS).
/// We use 'fer' as a shorthand for this type.
pub(crate) type FieldElementTimesMontgomeryR = I32;

#[hax_lib::attributes]
pub(crate) trait Operations: Copy + Clone {
    #[hax_lib::requires(true)]
    fn zero() -> Self;

    #[hax_lib::requires(array.len() == COEFFICIENTS_IN_SIMD_UNIT)]
    fn from_coefficient_array(array: &[I32], out: &mut Self);

    #[hax_lib::requires(out.len() == COEFFICIENTS_IN_SIMD_UNIT)]
    #[hax_lib::ensures(|result| future(out).len() == out.len())]
    fn to_coefficient_array(value: &Self, out: &mut [i32]);

    // Arithmetic
    #[hax_lib::requires(true)]
    fn add(lhs: &mut Self, rhs: &Self);
    #[hax_lib::requires(true)]
    fn subtract(lhs: &mut Self, rhs: &Self);
    #[hax_lib::requires(true)]
    fn infinity_norm_exceeds(simd_unit: &Self, bound: i32) -> bool;
    #[hax_lib::requires(gamma2 == GAMMA2_V95_232 || gamma2 == GAMMA2_V261_888)]
    fn decompose(gamma2: Gamma2, simd_unit: &Self, low: &mut Self, high: &mut Self);
    #[hax_lib::requires(gamma2 != i32::MIN)]
    fn compute_hint(low: &Self, high: &Self, gamma2: i32, hint: &mut Self) -> usize;
    #[hax_lib::requires(gamma2 == GAMMA2_V95_232 || gamma2 == GAMMA2_V261_888)]
    fn use_hint(gamma2: Gamma2, simd_unit: &Self, hint: &mut Self);

    // Modular operations
    #[hax_lib::requires(true)]
    fn montgomery_multiply(lhs: &mut Self, rhs: &Self);
    #[hax_lib::requires(SHIFT_BY >= 0 && SHIFT_BY < 32)]
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Self);

    // Decomposition operations
    #[hax_lib::requires(true)]
    fn power2round(t0: &mut Self, t1: &mut Self);

    // Sampling
    //
    // In the sampling functions, since each SIMD unit can hold 8 coefficients,
    // we expect that `out` has the capacity for up to 8 coefficients.

    // Since each coefficient could potentially be sampled with 3 bytes, we expect
    // `randomness` to hold 24 bytes.
    #[hax_lib::requires(randomness.len() / 3 <= 4_294_967_295 && out.len() >= randomness.len() / 3)]
    #[hax_lib::ensures(|_| out.len() == future(out).len())]
    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize;

    // Since each coefficient could potentially be sampled with half a byte,
    // we expect `randomness` to hold 4 bytes.
    #[hax_lib::requires(randomness.len() <= 4_294_967_295 / 2 && randomness.len() * 2 <= out.len())]
    #[hax_lib::ensures(|_| out.len() == future(out).len())]
    fn rejection_sample_less_than_eta_equals_2(randomness: &[U8], out: &mut [I32]) -> usize;
    #[hax_lib::requires(randomness.len() <= 4_294_967_295 / 2 && randomness.len() * 2 <= out.len())]
    #[hax_lib::ensures(|_| out.len() == future(out).len())]
    fn rejection_sample_less_than_eta_equals_4(randomness: &[U8], out: &mut [I32]) -> usize;

    // Encoding operations

    // Gamma1
    #[hax_lib::requires(
    match gamma1_exponent {
        17 => serialized.len() == 18,
        19 => serialized.len() == 20,
        _ => false
})]
    #[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
    fn gamma1_serialize(simd_unit: &Self, serialized: &mut [u8], gamma1_exponent: usize);
    #[hax_lib::requires(
    match gamma1_exponent {
        17 => serialized.len() == 18,
        19 => serialized.len() == 20,
        _ => false
})]
    fn gamma1_deserialize(serialized: &[U8], out: &mut Self, gamma1_exponent: usize);

    // Commitment
    #[hax_lib::requires(
    match serialized.len() {
        4 | 6 => true,
        _ => false
    }
)]
    #[hax_lib::ensures(|out| future(serialized).len() == serialized.len())]
    fn commitment_serialize(simd_unit: &Self, serialized: &mut [U8]);

    // Error
    #[hax_lib::requires(
    match eta {
        Eta::Two => serialized.len() == 3,
        Eta::Four => serialized.len() == 4,
        _ => false
})]
    #[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
    fn error_serialize(eta: Eta, simd_unit: &Self, serialized: &mut [U8]);
    #[hax_lib::requires(serialized.len() == (match eta { Eta::Two => 3, Eta::Four => 4 }))]
    fn error_deserialize(eta: Eta, serialized: &[U8], out: &mut Self);

    // t0
    #[hax_lib::requires(out.len() == 13)]
    #[hax_lib::ensures(|_| future(out).len() == out.len())]
    fn t0_serialize(simd_unit: &Self, out: &mut [U8]); // out len 13
    #[hax_lib::requires(serialized.len() == 13)]
    fn t0_deserialize(serialized: &[U8], out: &mut Self);

    // t1
    #[hax_lib::requires(out.len() == 10)]
    #[hax_lib::ensures(|_| future(out).len() == out.len())]
    fn t1_serialize(simd_unit: &Self, out: &mut [u8]); // out len 10
    #[hax_lib::requires(serialized.len() == 10)]
    fn t1_deserialize(serialized: &[u8], out: &mut Self);

    // NTT
    #[hax_lib::requires(true)]
    fn ntt(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);

    // invert NTT and convert to standard domain
    #[hax_lib::requires(true)]
    fn invert_ntt_montgomery(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);

    // Barrett reduce all coefficients
    #[hax_lib::requires(true)]
    fn reduce(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);
}
