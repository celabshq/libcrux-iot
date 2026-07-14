use crate::*;

const SHA3_224_RATE: usize = 144;
const SHA3_256_RATE: usize = 136;
const SHA3_384_RATE: usize = 104;
const SHA3_512_RATE: usize = 72;

use crate::keccak::KeccakSpongeState;

macro_rules! impl_incremental_hash {
    ($type:ident, $len:expr, $rate:expr, $method:expr) => {
        /// A type that allows incremental hashing."
        ///
        /// This type also implements the array-ref and slice one-shot hashing [`libcrux_traits::digest`] traits."
        #[derive(Clone)]
        pub struct $type {
            inner: KeccakSpongeState<$rate>,
        }

        impl $type {
            /// Create a new incremental hasher state.
            pub fn new() -> Self {
                Self {
                    inner: KeccakSpongeState::new(),
                }
            }

            /// Update the hasher state with the provided payload.
            pub fn update(&mut self, payload: &[U8]) {
                self.inner.absorb(payload);
            }

            /// Consume the hasher state and return the digest.
            pub fn finish(mut self) -> [U8; $len] {
                self.inner.absorb_final::<0x06>(&[]);
                let mut out = [U8(0); $len];
                self.inner.squeeze(&mut out);
                out
            }
        }

        #[cfg_attr(hax_backend_lean, charon::exclude)]
        impl libcrux_traits::digest::arrayref::Hash<$len> for $type {
            #[inline(always)]
            fn hash(
                digest: &mut [u8; $len],
                payload: &[u8],
            ) -> Result<(), libcrux_traits::digest::arrayref::HashError> {
                use libcrux_traits::libcrux_secrets::{ClassifyRef, ClassifyRefMut};

                if payload.len() > u32::MAX as usize {
                    return Err(libcrux_traits::digest::arrayref::HashError::InvalidPayloadLength);
                }

                $method(
                    digest.as_mut_slice().classify_ref_mut(),
                    payload.classify_ref(),
                );

                Ok(())
            }
        }
    };
}

impl_incremental_hash!(Sha3_224, SHA3_224_DIGEST_SIZE, SHA3_224_RATE, sha224_ema);
impl_incremental_hash!(Sha3_256, SHA3_256_DIGEST_SIZE, SHA3_256_RATE, sha256_ema);
impl_incremental_hash!(Sha3_384, SHA3_384_DIGEST_SIZE, SHA3_384_RATE, sha384_ema);
impl_incremental_hash!(Sha3_512, SHA3_512_DIGEST_SIZE, SHA3_512_RATE, sha512_ema);

// Implement the slice hash trait
// This is excluded for the hax extraction
#[cfg_attr(hax, hax_lib::exclude)]
#[cfg_attr(hax_backend_lean, charon::exclude)]
mod slice {
    use super::*;

    libcrux_traits::digest::slice::impl_hash_trait!(Sha3_224 => SHA3_224_DIGEST_SIZE);
    libcrux_traits::digest::slice::impl_hash_trait!(Sha3_256 => SHA3_256_DIGEST_SIZE);
    libcrux_traits::digest::slice::impl_hash_trait!(Sha3_384 => SHA3_384_DIGEST_SIZE);
    libcrux_traits::digest::slice::impl_hash_trait!(Sha3_512 => SHA3_512_DIGEST_SIZE);
}
