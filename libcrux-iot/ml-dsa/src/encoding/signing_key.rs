use libcrux_secrets::{mem_requests::ct_declassify, Classify as _, ClassifyRef as _, U8};

use crate::{
    constants::{
        Eta, BYTES_FOR_VERIFICATION_KEY_HASH, RING_ELEMENT_OF_T0S_SIZE, SEED_FOR_A_SIZE,
        SEED_FOR_SIGNING_SIZE,
    },
    encoding,
    hash_functions::shake256,
    polynomial::PolynomialRingElement,
    simd::traits::Operations,
};

#[inline(always)]
#[hax_lib::requires(
    seed_matrix.len() == SEED_FOR_A_SIZE
    && seed_signing.len() == SEED_FOR_SIGNING_SIZE
    && error_ring_element_size == crate::encoding::error::chunk_size(eta) * crate::simd::traits::SIMD_UNITS_IN_RING_ELEMENT
    && s1_2.len() <= 8 + 7
    && t0.len() <= 8
    && signing_key_serialized.len() ==
    SEED_FOR_A_SIZE
    + SEED_FOR_SIGNING_SIZE
    + BYTES_FOR_VERIFICATION_KEY_HASH
    + s1_2.len() * error_ring_element_size
    + t0.len() * RING_ELEMENT_OF_T0S_SIZE
)]
#[hax_lib::ensures(|_| future(signing_key_serialized).len() == signing_key_serialized.len())]
pub(crate) fn generate_serialized<SIMDUnit: Operations, Shake256: shake256::DsaXof>(
    eta: Eta,
    error_ring_element_size: usize,
    seed_matrix: &[U8],
    seed_signing: &[U8],
    verification_key: &[u8],
    s1_2: &[PolynomialRingElement<SIMDUnit>],
    t0: &[PolynomialRingElement<SIMDUnit>],
    signing_key_serialized: &mut [U8],
) {
    let mut offset = 0;

    signing_key_serialized[offset..offset + SEED_FOR_A_SIZE].copy_from_slice(seed_matrix);
    offset += SEED_FOR_A_SIZE;

    signing_key_serialized[offset..offset + SEED_FOR_SIGNING_SIZE].copy_from_slice(seed_signing);
    offset += SEED_FOR_SIGNING_SIZE;

    let mut verification_key_hash = [0.classify(); BYTES_FOR_VERIFICATION_KEY_HASH];
    Shake256::shake256::<BYTES_FOR_VERIFICATION_KEY_HASH>(
        verification_key.classify_ref(),
        &mut verification_key_hash,
    );
    // shake256 requires input to be classified but this marks memory as Undefined longer as intended
    // leading to false positives when executing under valgrind. Therefore we ct_declassify the memory
    // to mark it as defined.
    ct_declassify(verification_key);

    signing_key_serialized[offset..offset + BYTES_FOR_VERIFICATION_KEY_HASH]
        .copy_from_slice(&verification_key_hash);
    offset += BYTES_FOR_VERIFICATION_KEY_HASH;

    #[cfg(hax)]
    let _signing_key_serialized_len = signing_key_serialized.len();

    for i in 0..s1_2.len() {
        hax_lib::loop_invariant!(|i: usize| signing_key_serialized.len()
            == _signing_key_serialized_len
            && offset
                == SEED_FOR_A_SIZE
                    + SEED_FOR_SIGNING_SIZE
                    + BYTES_FOR_VERIFICATION_KEY_HASH
                    + i * error_ring_element_size);
        encoding::error::serialize::<SIMDUnit>(
            eta,
            &s1_2[i],
            &mut signing_key_serialized[offset..offset + error_ring_element_size],
        );
        offset += error_ring_element_size;
    }

    for i in 0..t0.len() {
        hax_lib::loop_invariant!(|i: usize| signing_key_serialized.len()
            == _signing_key_serialized_len
            && offset
                == SEED_FOR_A_SIZE
                    + SEED_FOR_SIGNING_SIZE
                    + BYTES_FOR_VERIFICATION_KEY_HASH
                    + s1_2.len() * error_ring_element_size
                    + i * RING_ELEMENT_OF_T0S_SIZE);

        encoding::t0::serialize::<SIMDUnit>(
            &t0[i],
            &mut signing_key_serialized[offset..offset + RING_ELEMENT_OF_T0S_SIZE],
        );
        offset += RING_ELEMENT_OF_T0S_SIZE;
    }
}
