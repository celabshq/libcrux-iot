/// Tag length.
pub const TAG_LEN: usize = 16;

/// Reduced tag length for AES-CCM, as per [RFC 6655](https://datatracker.ietf.org/doc/html/rfc6655).
pub const CCM_SHORT_TAG_LEN: usize = 8;

/// Nonce length.
pub const NONCE_LEN: usize = 12;

// The following values are taken from RFC 5116.

#[cfg(target_pointer_width = "64")]
/// AAD and plain/ciphertext size limits for 64-bit systems.
pub(crate) mod limits {
    /// AES-GCM allows for AAD to be 2^61 - 1 octets long.
    pub(crate) const GCM_AAD_MAX_LEN: usize = (1 << 61) - 1;

    /// AES-GCM allows the plaintext to be 2^36 - 32 octets long. This
    /// is also the maximum length of the ciphertext for us, since we
    /// store the tag separately.
    pub(crate) const GCM_PTXT_MAX_LEN: usize = (1 << 36) - 32;

    /// AES-CCM allows for AAD to be of size `usize::MAX - 10`.
    pub(crate) const CCM_AAD_MAX_LEN: usize = usize::MAX - 10;

    /// AES-CCM allows the plaintext to be 2^24 - 1 octets long, since
    /// the length has to be encoded in three bytes. This is also the
    /// maximum length of the ciphertext for us, since we store the
    /// tag separately.
    pub(crate) const CCM_PTXT_MAX_LEN: usize = (1 << 24) - 1;
}

#[cfg(target_pointer_width = "32")]
/// AAD and plain/ciphertext size limits for 32-bit systems.
pub(crate) mod limits {
    /// AES-GCM allows for AAD to be 2^61 - 1 octets long, but on
    /// 32-bit systems our limit is 2^32 - 1.
    pub(crate) const GCM_AAD_MAX_LEN: usize = usize::MAX;

    /// AES-GCM allows the plaintext to be 2^36 - 32 octets long, but
    /// on 32-bit systems our limit is 2^32 - 1.This is also the
    /// maximum length of the ciphertext for us, since we store the
    /// tag separately.
    pub(crate) const GCM_PTXT_MAX_LEN: usize = usize::MAX;

    /// AES-CCM allows for AAD to be of size `usize::MAX - 6` octets
    /// on 32-bit systems.
    pub(crate) const CCM_AAD_MAX_LEN: usize = usize::MAX - 6;

    /// AES-CCM allows the plaintext to be 2^24 - 1 octets long, since
    /// the length has to be encoded in three bytes. This is also the
    /// maximum length of the ciphertext for us, since we store the
    /// tag separately.
    pub(crate) const CCM_PTXT_MAX_LEN: usize = (1 << 24) - 1;
}
