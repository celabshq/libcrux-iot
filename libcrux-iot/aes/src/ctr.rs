//! AES ctr mode implementation.
//!
//! This implementation is generic over the [`AESState`], which has different,
//! platform dependent implementations.
//!
//! This get's instantiated in [`aes128_ctr`] and [`aes256_ctr`].

use crate::{aes::*, platform::AesCipherState};

#[cfg(test)]
mod test128;

mod aes128_ctr;
mod aes256_ctr;

/// The ctr nonce length. This is different from the AES nonce length
/// [`crate::NONCE_LEN`].
const CTR_NONCE_LEN: usize = 16;

pub(crate) const AES_GCM_CTR_LEN: usize = 4;
pub(crate) const AES_CCM_CTR_LEN: usize = 3;
pub(crate) const AES_GCM_NONCE_START: usize = 0;
pub(crate) const AES_CCM_NONCE_START: usize = 1;

/// Generic AES CTR context.
///
/// - `NUM_KEYS` is the number of sub-keys that are expanded in `extended_key`, i.e. 11 for AES-128, 15 for AES-256.
/// - `CTR_LEN` is how many bytes at the end of `ctr_nonce` are used for the counter
/// - `NONCE_START` is the index in `ctr_nonce`, where the AEAD nonce begins, i.e. 0 in AES-GCM and 1 in AES-CCM (because the first byte is for flags CCM)
pub(crate) struct AesCtrContext<
    T: AesCipherState,
    const NUM_KEYS: usize,
    const CTR_LEN: usize,
    const NONCE_START: usize,
> {
    pub(crate) extended_key: ExtendedKey<T, NUM_KEYS>,
    pub(crate) ctr_nonce: [u8; CTR_NONCE_LEN],
}

impl<T: AesCipherState, const NUM_KEYS: usize, const CTR_LEN: usize, const NONCE_START: usize>
    AesCtrContext<T, NUM_KEYS, CTR_LEN, NONCE_START>
{
    #[inline]
    pub(crate) fn aes_ctr_set_nonce(&mut self, nonce: &[u8]) {
        assert!(nonce.len() == crate::NONCE_LEN);

        self.ctr_nonce[NONCE_START..crate::NONCE_LEN + NONCE_START].copy_from_slice(nonce);
    }

    #[inline]
    pub(crate) fn aes_ctr_key_block(&self, ctr: u32, out: &mut [u8]) {
        assert!(out.len() == AES_BLOCK_LEN);

        let mut st_init = self.ctr_nonce;
        st_init[CTR_NONCE_LEN - CTR_LEN..].copy_from_slice(&ctr.to_be_bytes()[4 - CTR_LEN..]);
        let mut st = T::new();

        st.load_block(&st_init);

        block_cipher(&mut st, &self.extended_key);

        st.store_block(out);
    }

    #[inline]
    fn aes_ctr_xor_block(&self, ctr: u32, input: &mut [u8]) {
        assert!(input.len() <= AES_BLOCK_LEN);

        let mut st_init = self.ctr_nonce;
        st_init[CTR_NONCE_LEN - CTR_LEN..].copy_from_slice(&ctr.to_be_bytes()[4 - CTR_LEN..]);
        let mut st = T::new();
        st.load_block(&st_init);

        block_cipher(&mut st, &self.extended_key);

        st.xor_block(input);
    }

    #[inline]
    /// NOTE: Assumes that `ctr` previous blocks have been encrypted
    /// already, so will only encrypt at most `2^(CTR_LEN * 8) - ctr`
    /// additional blocks.
    fn aes_ctr_xor_blocks(&self, ctr: u32, input: &mut [u8]) {
        assert!(input.len().is_multiple_of(AES_BLOCK_LEN));
        // We don't have to use `div_ceil` here, since `input.len()`
        // is cleanly divided by `AES_BLOCK_LEN`.
        let blocks_to_encrypt = (input.len() / AES_BLOCK_LEN) as u64;
        let safe_to_encrypt = (1u64 << (8 * CTR_LEN as u64)).saturating_sub(ctr as u64);
        assert!(blocks_to_encrypt <= safe_to_encrypt);

        let blocks = input.len() / AES_BLOCK_LEN;
        for i in 0..blocks {
            let offset = i * AES_BLOCK_LEN;
            self.aes_ctr_xor_block(
                ctr.wrapping_add(i as u32),
                &mut input[offset..offset + AES_BLOCK_LEN],
            );
        }
    }

    #[inline]
    /// NOTE: Assumes that `ctr` previous blocks have been encrypted
    /// already. Since the counter value ranges from `0` to
    /// `2^(CTR_LEN * 8) - 1`, this will only encrypt at most
    /// `2^(CTR_LEN * 8) - ctr` additional blocks.
    pub(crate) fn aes_ctr_update(&self, ctr: u32, input: &mut [u8]) {
        let blocks_to_encrypt = input.len().div_ceil(AES_BLOCK_LEN) as u64;
        let safe_to_encrypt = (1u64 << (8 * CTR_LEN as u64)).saturating_sub(ctr as u64);
        assert!(blocks_to_encrypt <= safe_to_encrypt);

        let full_blocks = input.len() / AES_BLOCK_LEN;
        self.aes_ctr_xor_blocks(ctr, &mut input[0..full_blocks * AES_BLOCK_LEN]);

        let last = input.len() - input.len() % AES_BLOCK_LEN;
        if last < input.len() {
            self.aes_ctr_xor_block(ctr.wrapping_add(full_blocks as u32), &mut input[last..]);
        }
    }
}

/// Trait for constructing an [`AesCtrContext`] from a CCM key.
///
/// Implemented for AES-128 (`NUM_KEYS = 11`) and AES-256 (`NUM_KEYS = 15`).
pub(crate) trait CcmInit: Sized {
    fn ccm_init(key: &[u8]) -> Self;
}

/// Trait for constructing an [`AesCtrContext`] from a GCM key.
///
/// Implemented for AES-128 (`NUM_KEYS = 11`) and AES-256 (`NUM_KEYS = 15`).
pub(crate) trait GcmInit: Sized {
    fn gcm_init(key: &[u8]) -> Self;
}
