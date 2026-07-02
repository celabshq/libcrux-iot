/// AES-GCM 256 key length.
pub const KEY_LEN: usize = 32;

/// The AES-GCM 256 state
pub(crate) type State<T, U> = super::aes_gcm::State<T, U, 15>;

use super::aes_gcm::type_aliases;

type_aliases!(AesGcm256, "AES-GCM 256");

/// # Portable implementation of AES-GCM 256
///
/// To use the portable implementation, `Key`, `Nonce`, and `Tag` types
/// must be explicitely parameterized by the portable implementation.
///
/// Example:
/// ```rust
/// // Using the portable implementation.
/// use libcrux_iot_aes::{
///     aes_gcm_256::portable::{Key, Nonce, PortableAesGcm256, Tag},
///     AeadConsts as _, NONCE_LEN, TAG_LEN,
/// };
///
/// let k: Key<PortableAesGcm256> = [0; PortableAesGcm256::KEY_LEN].into();
/// let nonce: Nonce<PortableAesGcm256> = [0; NONCE_LEN].into();
/// let mut tag: Tag<PortableAesGcm256> = [0; TAG_LEN].into();
///
/// let pt = b"the quick brown fox jumps over the lazy dog";
/// let mut ct = [0; 43];
/// let mut pt_out = [0; 43];
///
/// k.encrypt(&mut ct, &mut tag, &nonce, b"", pt).unwrap();
/// k.decrypt(&mut pt_out, &nonce, b"", &ct, &tag).unwrap();
/// assert_eq!(pt, &pt_out);
/// ```
pub mod portable {
    pub use libcrux_traits::aead::{
        typed_owned::{Key, Nonce, Tag},
        typed_refs::{KeyMut, KeyRef, NonceRef, TagMut, TagRef},
    };

    pub use crate::implementations::PortableAesGcm256;
}
