use libcrux_secrets::{CastOps as _, U8};

use crate::simd::portable::vector_type::Coefficients;

#[inline(always)]
#[hax_lib::requires(serialized.len() == 4)]
#[hax_lib::ensures(|out| future(serialized).len() == serialized.len())]
fn serialize_4(simd_unit: &Coefficients, serialized: &mut [U8]) {
    let coefficient0 = simd_unit.values[0].as_u8();
    let coefficient1 = simd_unit.values[1].as_u8();
    let coefficient2 = simd_unit.values[2].as_u8();
    let coefficient3 = simd_unit.values[3].as_u8();
    let coefficient4 = simd_unit.values[4].as_u8();
    let coefficient5 = simd_unit.values[5].as_u8();
    let coefficient6 = simd_unit.values[6].as_u8();
    let coefficient7 = simd_unit.values[7].as_u8();

    let byte0 = (coefficient1 << 4) | coefficient0;
    let byte1 = (coefficient3 << 4) | coefficient2;
    let byte2 = (coefficient5 << 4) | coefficient4;
    let byte3 = (coefficient7 << 4) | coefficient6;

    serialized[0] = byte0;
    serialized[1] = byte1;
    serialized[2] = byte2;
    serialized[3] = byte3;
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 300")]
#[hax_lib::requires(serialized.len() == 6)]
#[hax_lib::ensures(|out| future(serialized).len() == serialized.len())]
pub fn serialize_6(simd_unit: &Coefficients, serialized: &mut [U8]) {
    // The commitment has coefficients in [0,43] => each coefficient occupies
    // 6 bits.

    let coefficient0 = simd_unit.values[0].as_u8();
    let coefficient1 = simd_unit.values[1].as_u8();
    let coefficient2 = simd_unit.values[2].as_u8();
    let coefficient3 = simd_unit.values[3].as_u8();
    let coefficient4 = simd_unit.values[4].as_u8();
    let coefficient5 = simd_unit.values[5].as_u8();
    let coefficient6 = simd_unit.values[6].as_u8();
    let coefficient7 = simd_unit.values[7].as_u8();

    let byte0 = (coefficient1 << 6) | coefficient0;
    let byte1 = (coefficient2 << 4) | coefficient1 >> 2;
    let byte2 = (coefficient3 << 2) | coefficient2 >> 4;
    let byte3 = (coefficient5 << 6) | coefficient4;
    let byte4 = (coefficient6 << 4) | coefficient5 >> 2;
    let byte5 = (coefficient7 << 2) | coefficient6 >> 4;

    serialized[0] = byte0;
    serialized[1] = byte1;
    serialized[2] = byte2;
    serialized[3] = byte3;
    serialized[4] = byte4;
    serialized[5] = byte5;
}

#[inline(always)]
#[hax_lib::requires(
    match serialized.len() {
        4 | 6 => true,
        _ => false
    }
)]
#[hax_lib::ensures(|out| future(serialized).len() == serialized.len())]
pub(in crate::simd::portable) fn serialize(simd_unit: &Coefficients, serialized: &mut [U8]) {
    match serialized.len() as u8 {
        4 => serialize_4(simd_unit, serialized),
        6 => serialize_6(simd_unit, serialized),
        _ => unreachable!(),
    }
}
