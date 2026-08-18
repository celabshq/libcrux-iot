use libcrux_traits::aead::{
    arrayref::{self},
    consts, slice, typed_owned,
};

use crate::{
    implementations::{
        AesCcm128, AesCcm128ShortTag, AesCcm256, AesCcm256ShortTag, AesGcm128, AesGcm256,
        PortableAesCcm128, PortableAesCcm128ShortTag, PortableAesCcm256, PortableAesCcm256ShortTag,
        PortableAesGcm128, PortableAesGcm256,
    },
    NONCE_LEN,
};

/// Macro to implement the libcrux_traits public API traits
///
/// For the blanket impl of `typed_refs::Aead` to take place,
/// the `$type` must implement `Copy` and `PartialEq`.
macro_rules! impl_traits_public_api {
    ($type:ty, $keylen:expr, $taglen:expr, $noncelen:expr) => {
        // prerequisite for typed_owned::Aead
        impl consts::AeadConsts for $type {
            const KEY_LEN: usize = $keylen;
            const TAG_LEN: usize = $taglen;
            const NONCE_LEN: usize = $noncelen;
        }
        // implement typed_owned::Aead
        typed_owned::impl_aead_typed_owned!($type, $keylen, $taglen, $noncelen);
    };
}

/// Macro to implement the different structs and multiplexing.
macro_rules! api {
    ($mod_name:ident, $variant:ident, $multiplexing:ty, $portable:ident, $key_len:path, $tag_len:path) => {
        mod $mod_name {
            use super::*;
            use libcrux_secrets::{U8, DeclassifyRef, DeclassifyRefMut};

            use libcrux_traits::aead::arrayref::{DecryptError, EncryptError, KeyGenError};

            use $key_len as KEY_LEN;
            use $tag_len as TAG_LEN;

            pub type Key = [U8; KEY_LEN];
            pub type Tag = [U8; TAG_LEN];
            pub type Nonce = [U8; NONCE_LEN];


            mod _libcrux_traits_apis_multiplex {
                use super::*;

                // implement `libcrux_traits` slice trait
                slice::impl_aead_slice_trait!($multiplexing => KEY_LEN, TAG_LEN, NONCE_LEN);

                // implement `libcrux_traits` public API traits
                impl_traits_public_api!($multiplexing, KEY_LEN, TAG_LEN, NONCE_LEN);

                /// The plaintext length must be equal to the ciphertext length.
                impl arrayref::Aead<KEY_LEN, TAG_LEN, NONCE_LEN> for $multiplexing {
                    fn keygen(key: &mut [U8; KEY_LEN], rand: &[U8; KEY_LEN]) -> Result<(), KeyGenError> {
                        *key = *rand;
                        Ok(())
                    }

                    fn encrypt(
                        ciphertext: &mut [u8],
                        tag: &mut Tag,
                        key: &Key,
                        nonce: &Nonce,
                        aad: &[u8],
                        plaintext: &[U8],
                    ) -> Result<(), EncryptError> {
                        $portable::encrypt(ciphertext, tag, key, nonce, aad, plaintext)
                    }

                    fn decrypt(
                        plaintext: &mut [U8],
                        key: &Key,
                        nonce: &Nonce,
                        aad: &[u8],
                        ciphertext: &[u8],
                        tag: &Tag,
                    ) -> Result<(), DecryptError> {
                        $portable::decrypt(plaintext, key, nonce, aad, ciphertext, tag)
                    }
                }
            }

            mod _libcrux_traits_apis_portable {
                use super::*;

                // implement `libcrux_traits` slice trait
                slice::impl_aead_slice_trait!($portable => KEY_LEN, TAG_LEN, NONCE_LEN);

                // implement `libcrux_traits` public API traits
                impl_traits_public_api!($portable, KEY_LEN, TAG_LEN, NONCE_LEN);

                /// The plaintext length must be equal to the ciphertext length.
                impl arrayref::Aead<KEY_LEN, TAG_LEN, NONCE_LEN> for $portable {
                    fn keygen(key: &mut [U8; KEY_LEN], rand: &[U8; KEY_LEN]) -> Result<(), KeyGenError> {
                        *key = *rand;
                        Ok(())
                    }

                    fn encrypt(
                        ciphertext: &mut [u8],
                        tag: &mut Tag,
                        key: &Key,
                        nonce: &Nonce,
                        aad: &[u8],
                        plaintext: &[U8],
                    ) -> Result<(), EncryptError> {
                        if ciphertext.len() != plaintext.len(){
                            return Err(EncryptError::WrongCiphertextLength);
                        }
                        // declassify: for now, we only implement the libcrux-traits APIs in a secrets
                        // aware way, but don't use libcrux-secrets internally within this crate.
                        // Therefore, we need perform declassify operations at the boundaries between
                        // the libcrux-traits APIs and the internal ones.
                        ciphertext.copy_from_slice(plaintext.declassify_ref());
                        crate::portable::$variant::encrypt(key.declassify_ref(), nonce.declassify_ref(), aad.iter().copied(), ciphertext, tag.declassify_ref_mut())
                    }

                    fn decrypt(
                        plaintext: &mut [U8],
                        key: &Key,
                        nonce: &Nonce,
                        aad: &[u8],
                        ciphertext: &[u8],
                        tag: &Tag,
                    ) -> Result<(), DecryptError> {
                        if ciphertext.len() != plaintext.len(){
                            return Err(DecryptError::WrongPlaintextLength);
                        }

                        // declassify: for now, we only implement the libcrux-traits APIs in a secrets
                        // aware way, but don't use libcrux-secrets internally within this crate.
                        // Therefore, we need perform declassify operations at the boundaries between
                        // the libcrux-traits APIs and the internal ones.
                        let plaintext = plaintext.declassify_ref_mut();
                        plaintext.copy_from_slice(ciphertext);
                        crate::portable::$variant::decrypt(key.declassify_ref(), nonce.declassify_ref(), aad.iter().copied(), plaintext, tag.declassify_ref())
                    }
                }
            }
        }
    };
}

api!(
    aes128gcm,
    aes_gcm_128,
    AesGcm128,
    PortableAesGcm128,
    crate::aes::AES_128_KEY_LEN,
    crate::TAG_LEN
);

api!(
    aes256gcm,
    aes_gcm_256,
    AesGcm256,
    PortableAesGcm256,
    crate::aes::AES_256_KEY_LEN,
    crate::TAG_LEN
);

api!(
    aes128ccm,
    aes_ccm_128,
    AesCcm128,
    PortableAesCcm128,
    crate::aes::AES_128_KEY_LEN,
    crate::TAG_LEN
);

api!(
    aes256ccm,
    aes_ccm_256,
    AesCcm256,
    PortableAesCcm256,
    crate::aes::AES_256_KEY_LEN,
    crate::TAG_LEN
);

api!(
    aes128ccm_short_tag,
    aes_ccm_128_8,
    AesCcm128ShortTag,
    PortableAesCcm128ShortTag,
    crate::aes::AES_128_KEY_LEN,
    crate::CCM_SHORT_TAG_LEN
);

api!(
    aes256ccm_short_tag,
    aes_ccm_256_8,
    AesCcm256ShortTag,
    PortableAesCcm256ShortTag,
    crate::aes::AES_256_KEY_LEN,
    crate::CCM_SHORT_TAG_LEN
);
