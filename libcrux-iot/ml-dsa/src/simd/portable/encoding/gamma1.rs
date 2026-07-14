#[cfg(feature = "check-secret-independence")]
use libcrux_secrets::IntOps as _;
use libcrux_secrets::{CastOps as _, Classify as _, Declassify as _, U8};

use crate::{helper::cloop, simd::portable::vector_type::Coefficients};

#[inline(always)]
#[hax_lib::requires(serialized.len() == 18)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
fn serialize_when_gamma1_is_2_pow_17(simd_unit: &Coefficients, serialized: &mut [u8]) {
    const GAMMA1: i32 = 1 << 17;

    cloop! {
        for (i, coefficients) in simd_unit.values.chunks_exact(4).enumerate() {
            hax_lib::loop_invariant!(|_i: usize| serialized.len() == 18);

            // Declassification: This is part of serializing the signature.
            let coefficient0 = GAMMA1.wrapping_sub(coefficients[0].declassify());
            let coefficient1 = GAMMA1.wrapping_sub(coefficients[1].declassify());
            let coefficient2 = GAMMA1.wrapping_sub(coefficients[2].declassify());
            let coefficient3 = GAMMA1.wrapping_sub(coefficients[3].declassify());

            serialized[9 * i] = coefficient0 as u8;
            serialized[9 * i + 1] = (coefficient0 >> 8) as u8;

            serialized[9 * i + 2] = (coefficient0 >> 16) as u8;
            serialized[9 * i + 2] |= (coefficient1 << 2) as u8;

            serialized[9 * i + 3] = (coefficient1 >> 6) as u8;

            serialized[9 * i + 4] = (coefficient1 >> 14) as u8;
            serialized[9 * i + 4] |= (coefficient2 << 4) as u8;

            serialized[9 * i + 5] = (coefficient2 >> 4) as u8;

            serialized[9 * i + 6] = (coefficient2 >> 12) as u8;
            serialized[9 * i + 6] |= (coefficient3 << 6) as u8;

            serialized[9 * i + 7] = (coefficient3 >> 2) as u8;
            serialized[9 * i + 8] = (coefficient3 >> 10) as u8;
        }
    }
}

#[inline(always)]
#[hax_lib::requires(serialized.len() == 20)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
fn serialize_when_gamma1_is_2_pow_19(simd_unit: &Coefficients, serialized: &mut [u8]) {
    const GAMMA1: i32 = 1 << 19;

    cloop! {
        for (i, coefficients) in simd_unit.values.chunks_exact(2).enumerate() {
            hax_lib::loop_invariant!(|_i: usize| serialized.len() == 20);

            // Declassification: This is part of serializing the signature.
            let coefficient0 = GAMMA1.wrapping_sub(coefficients[0].declassify());
            let coefficient1 = GAMMA1.wrapping_sub(coefficients[1].declassify());

            serialized[5 * i] = coefficient0 as u8;
            serialized[5 * i + 1] = (coefficient0 >> 8) as u8;

            serialized[5 * i + 2] = (coefficient0 >> 16) as u8;
            serialized[5 * i + 2] |= (coefficient1 << 4) as u8;

            serialized[5 * i + 3] = (coefficient1 >> 4) as u8;
            serialized[5 * i + 4] = (coefficient1 >> 12) as u8;
        }
    }
}

#[inline(always)]
#[hax_lib::requires(
    match gamma1_exponent {
        17 => serialized.len() == 18,
        19 => serialized.len() == 20,
        _ => false
})]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
pub(crate) fn serialize(simd_unit: &Coefficients, serialized: &mut [u8], gamma1_exponent: usize) {
    match gamma1_exponent as u8 {
        17 => serialize_when_gamma1_is_2_pow_17(simd_unit, serialized),
        19 => serialize_when_gamma1_is_2_pow_19(simd_unit, serialized),
        _ => unreachable!(),
    }
}

#[inline(always)]
#[hax_lib::requires(serialized.len() == 18)]
fn deserialize_when_gamma1_is_2_pow_17(serialized: &[U8], simd_unit: &mut Coefficients) {
    // Each set of 9 bytes deserializes to 4 elements, and since each PortableSIMDUnit
    // can hold 8, we process 18 bytes in this function.
    #[cfg(not(eurydice))]
    debug_assert!(serialized.len() == 18);

    const GAMMA1: i32 = 1 << 17;
    const GAMMA1_TIMES_2_BITMASK: i32 = (GAMMA1 << 1) - 1;

    cloop! {
        for (i, bytes) in serialized.chunks_exact(9).enumerate() {
            hax_lib::loop_invariant!(|_i: usize| serialized.len() == 18);

            let mut coefficient0 = bytes[0].as_i32();
            coefficient0 |= (bytes[1].as_i32()) << 8;
            coefficient0 |= (bytes[2].as_i32()) << 16;
            coefficient0 &= GAMMA1_TIMES_2_BITMASK;

            let mut coefficient1 = (bytes[2].as_i32()) >> 2;
            coefficient1 |= (bytes[3].as_i32()) << 6;
            coefficient1 |= (bytes[4].as_i32()) << 14;
            coefficient1 &= GAMMA1_TIMES_2_BITMASK;

            let mut coefficient2 = (bytes[4].as_i32()) >> 4;
            coefficient2 |= (bytes[5].as_i32()) << 4;
            coefficient2 |= (bytes[6].as_i32()) << 12;
            coefficient2 &= GAMMA1_TIMES_2_BITMASK;

            let mut coefficient3 = (bytes[6].as_i32()) >> 6;
            coefficient3 |= (bytes[7].as_i32()) << 2;
            coefficient3 |= (bytes[8].as_i32()) << 10;
            coefficient3 &= GAMMA1_TIMES_2_BITMASK;

            simd_unit.values[4 * i] = GAMMA1.classify().wrapping_sub(coefficient0);
            simd_unit.values[4 * i + 1] = GAMMA1.classify().wrapping_sub(coefficient1);
            simd_unit.values[4 * i + 2] = GAMMA1.classify().wrapping_sub(coefficient2);
            simd_unit.values[4 * i + 3] = GAMMA1.classify().wrapping_sub(coefficient3);
        }
    }
}

#[inline(always)]
#[hax_lib::requires(serialized.len() == 20)]
fn deserialize_when_gamma1_is_2_pow_19(serialized: &[U8], simd_unit: &mut Coefficients) {
    // Each set of 5 bytes deserializes to 2 elements, and since each PortableSIMDUnit
    // can hold 8, we process 5 * (8 / 2) = 20 bytes in this function.
    #[cfg(not(eurydice))]
    debug_assert!(serialized.len() == 20);

    const GAMMA1: i32 = 1 << 19;
    const GAMMA1_TIMES_2_BITMASK: i32 = (GAMMA1 << 1) - 1;

    cloop! {
        for (i, bytes) in serialized.chunks_exact(5).enumerate() {
            let mut coefficient0 = bytes[0].as_i32();
            coefficient0 |= (bytes[1].as_i32()) << 8;
            coefficient0 |= (bytes[2].as_i32()) << 16;
            coefficient0 &= GAMMA1_TIMES_2_BITMASK;

            let mut coefficient1 = (bytes[2].as_i32()) >> 4;
            coefficient1 |= (bytes[3].as_i32()) << 4;
            coefficient1 |= (bytes[4].as_i32()) << 12;

            simd_unit.values[2 * i] = GAMMA1.classify().wrapping_sub(coefficient0);
            simd_unit.values[2 * i + 1] = GAMMA1.classify().wrapping_sub(coefficient1);
        }
    }
}

#[inline(always)]
#[hax_lib::requires(
    match gamma1_exponent {
        17 => serialized.len() == 18,
        19 => serialized.len() == 20,
        _ => false
})]
pub(crate) fn deserialize(serialized: &[U8], out: &mut Coefficients, gamma1_exponent: usize) {
    match gamma1_exponent as u8 {
        17 => deserialize_when_gamma1_is_2_pow_17(serialized, out),
        19 => deserialize_when_gamma1_is_2_pow_19(serialized, out),
        _ => unreachable!(),
    }
}
