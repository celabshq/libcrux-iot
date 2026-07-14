use crate::{
    constants::{RING_ELEMENT_OF_T1S_SIZE, SEED_FOR_A_SIZE},
    encoding::t1,
    polynomial::PolynomialRingElement,
    simd::traits::Operations,
};

#[inline(always)]
#[hax_lib::requires(
    RING_ELEMENT_OF_T1S_SIZE == crate::encoding::t1::OUTPUT_BYTES_PER_SIMD_UNIT * crate::simd::traits::SIMD_UNITS_IN_RING_ELEMENT
    && t1.len() <= 8
    && seed.len() == SEED_FOR_A_SIZE
    && verification_key_serialized.len() == SEED_FOR_A_SIZE + t1.len() * RING_ELEMENT_OF_T1S_SIZE
)]
#[hax_lib::ensures(|_| future(verification_key_serialized).len() == verification_key_serialized.len())]
pub(crate) fn generate_serialized<SIMDUnit: Operations>(
    seed: &[u8],
    t1: &[PolynomialRingElement<SIMDUnit>],
    verification_key_serialized: &mut [u8],
) {
    #[cfg(hax)]
    let _verification_key_serialized_len = verification_key_serialized.len();

    verification_key_serialized[0..SEED_FOR_A_SIZE].copy_from_slice(seed);

    for i in 0..t1.len() {
        hax_lib::loop_invariant!(
            |i: usize| verification_key_serialized.len() == _verification_key_serialized_len
        );
        let offset = SEED_FOR_A_SIZE + (i * RING_ELEMENT_OF_T1S_SIZE);
        t1::serialize::<SIMDUnit>(
            &t1[i],
            &mut verification_key_serialized[offset..offset + RING_ELEMENT_OF_T1S_SIZE],
        );
    }
}

#[inline(always)]
#[cfg(not(feature = "stack"))]
#[hax_lib::requires(
    (rows_in_a == 4 || rows_in_a == 6 || rows_in_a == 8)
    && verification_key_size == crate::constants::verification_key_size(rows_in_a)
    && t1.len() == rows_in_a
    && serialized.len() == verification_key_size - SEED_FOR_A_SIZE
    && RING_ELEMENT_OF_T1S_SIZE == crate::encoding::t1::OUTPUT_BYTES_PER_SIMD_UNIT * crate::simd::traits::SIMD_UNITS_IN_RING_ELEMENT
    && serialized.len() == rows_in_a * RING_ELEMENT_OF_T1S_SIZE
)]
#[hax_lib::ensures(|_| future(t1).len() == t1.len())]
pub(crate) fn deserialize<SIMDUnit: Operations>(
    rows_in_a: usize,
    verification_key_size: usize,
    serialized: &[u8],
    t1: &mut [PolynomialRingElement<SIMDUnit>],
) {
    #[cfg(not(eurydice))]
    debug_assert!(serialized.len() == verification_key_size - SEED_FOR_A_SIZE);

    #[cfg(hax)]
    let _t1_len = t1.len();

    for i in 0..rows_in_a {
        hax_lib::loop_invariant!(|i: usize| t1.len() == _t1_len);
        t1::deserialize::<SIMDUnit>(
            &serialized[i * RING_ELEMENT_OF_T1S_SIZE..(i + 1) * RING_ELEMENT_OF_T1S_SIZE],
            &mut t1[i],
        );
    }
}
