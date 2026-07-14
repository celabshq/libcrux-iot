//! Common types

use libcrux_secrets::{Classify as _, U8};

macro_rules! impl_struct {
    ($name:ident, $doc:expr) => {
        #[doc = $doc]
        #[derive(Clone)]
        pub struct $name<const SIZE: usize> {
            pub(crate) value: [u8; SIZE],
        }

        impl<const SIZE: usize> $name<SIZE> {
            /// Init with zero
            pub fn zero() -> Self {
                Self { value: [0u8; SIZE] }
            }

            /// Build
            pub fn new(value: [u8; SIZE]) -> Self {
                Self { value }
            }

            /// A reference to the raw byte slice.
            pub fn as_slice(&self) -> &[u8] {
                &self.value
            }

            /// A reference to the raw byte array.
            pub fn as_ref(&self) -> &[u8; SIZE] {
                &self.value
            }

            /// The number of bytes
            pub const fn len() -> usize {
                SIZE
            }
        }
    };
}

impl_struct!(MLDSAVerificationKey, "An ML-DSA verification key.");
impl_struct!(MLDSASignature, "An ML-DSA signature.");

/// An ML-DSA signing key.
pub struct MLDSASigningKey<const SIZE: usize> {
    pub(crate) value: [U8; SIZE],
}

impl<const SIZE: usize> MLDSASigningKey<SIZE> {
    /// Init with zero
    pub fn zero() -> Self {
        Self {
            value: [0u8.classify(); SIZE],
        }
    }

    /// Build
    pub fn new(value: [U8; SIZE]) -> Self {
        Self { value }
    }

    /// A reference to the raw byte slice.
    pub fn as_slice(&self) -> &[U8] {
        &self.value
    }

    /// A reference to the raw byte array.
    pub fn as_ref(&self) -> &[U8; SIZE] {
        &self.value
    }

    /// The number of bytes
    pub const fn len() -> usize {
        SIZE
    }
}

#[cfg(not(hax))]
macro_rules! impl_non_hax_types {
    ($name:ident) => {
        impl<const SIZE: usize> $name<SIZE> {
            /// A mutable reference to the raw byte slice.
            pub fn as_mut_slice(&mut self) -> &mut [u8] {
                &mut self.value
            }

            /// A mutable reference to the raw byte array.
            pub fn as_ref_mut(&mut self) -> &mut [u8; SIZE] {
                &mut self.value
            }
        }
    };
}

// Hax can't handle these.
#[cfg(not(hax))]
mod non_hax_impls {
    use super::*;
    impl<const SIZE: usize> MLDSASigningKey<SIZE> {
        /// A mutable reference to the raw byte slice.
        pub fn as_mut_slice(&mut self) -> &mut [U8] {
            &mut self.value
        }

        /// A mutable reference to the raw byte array.
        pub fn as_ref_mut(&mut self) -> &mut [U8; SIZE] {
            &mut self.value
        }
    }
    impl_non_hax_types!(MLDSAVerificationKey);
    impl_non_hax_types!(MLDSASignature);
}

/// An ML-DSA key pair.
pub struct MLDSAKeyPair<const VERIFICATION_KEY_SIZE: usize, const SIGNING_KEY_SIZE: usize> {
    pub signing_key: MLDSASigningKey<SIGNING_KEY_SIZE>,
    pub verification_key: MLDSAVerificationKey<VERIFICATION_KEY_SIZE>,
}

#[cfg_attr(not(eurydice), derive(Debug))]
pub enum VerificationError {
    MalformedHintError,
    SignerResponseExceedsBoundError,
    CommitmentHashesDontMatchError,
    // FIXME: Eurydice can't handle enum variants with the same name
    // https://github.com/AeneasVerif/eurydice/issues/102
    VerificationContextTooLongError,
}

#[cfg_attr(not(eurydice), derive(Debug))]
pub enum SigningError {
    RejectionSamplingError,
    ContextTooLongError,
}
