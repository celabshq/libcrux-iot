/// AES-GCM 128 key length.
pub const KEY_LEN: usize = 16;
pub(crate) const GCM_KEY_LEN: usize = 16;

/// The AES-GCM 128 state
pub(crate) type State<T, U> = super::aes_gcm::State<T, U, 11>;

use super::aes_gcm::type_aliases;

type_aliases!(AesGcm128, "AES-GCM 128");

/// # Portable implementation of AES-GCM 128
///
/// To use the portable implementation, `Key`, `Nonce`, and `Tag` types
/// must be explicitely parameterized by the portable implementation.
///
/// Example:
/// ```rust
/// // Using the portable implementation.
/// use libcrux_iot_aes::{
///     aes_gcm_128::portable::{Key, Nonce, PortableAesGcm128, Tag},
///     AeadConsts as _, NONCE_LEN, TAG_LEN,
/// };
/// use libcrux_secrets::{Classify, ClassifyRef, ClassifyRefMut};
///
/// let k: Key<PortableAesGcm128> = [0; PortableAesGcm128::KEY_LEN].classify().into();
/// let nonce: Nonce<PortableAesGcm128> = [0; NONCE_LEN].classify().into();
/// let mut tag: Tag<PortableAesGcm128> = [0; TAG_LEN].classify().into();
///
/// let pt = b"the quick brown fox jumps over the lazy dog";
/// let mut ct = [0; 43];
/// let mut pt_out = [0; 43];
///
/// k.encrypt(&mut ct, &mut tag, &nonce, b"", pt.classify_ref()).unwrap();
/// k.decrypt(pt_out.classify_ref_mut(), &nonce, b"", &ct, &tag).unwrap();
/// assert_eq!(pt, &pt_out);
/// ```
pub mod portable {
    pub use libcrux_traits::aead::{
        typed_owned::{Key, Nonce, Tag},
        typed_refs::{KeyMut, KeyRef, NonceRef, TagMut, TagRef},
    };

    pub use crate::implementations::PortableAesGcm128;
}
