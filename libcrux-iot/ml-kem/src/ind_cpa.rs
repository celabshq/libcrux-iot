use libcrux_secrets::mem_requests::ct_declassify;

use core::array::from_fn;

use crate::{
    constants::*,
    hash_functions::Hash,
    helper::cloop,
    matrix::*,
    ntt::{ntt_binomially_sampled_ring_element, ntt_vector_u},
    polynomial::PolynomialRingElement,
    sampling::sample_from_binomial_distribution,
    serialize::{
        compress_then_serialize_message, compress_then_serialize_ring_element_u,
        compress_then_serialize_ring_element_v, deserialize_then_decompress_message,
        deserialize_then_decompress_ring_element_u, deserialize_then_decompress_ring_element_v,
        deserialize_to_uncompressed_ring_element, serialize_uncompressed_ring_element,
    },
    utils::{into_padded_array, prf_input_inc},
    variant::Variant,
    vector::Operations,
};

/// Types for the unpacked API.
// We keep this, because key generation still depends on unpacked types.
#[allow(non_snake_case)]
pub(crate) mod unpacked {
    use crate::{polynomial::PolynomialRingElement, vector::traits::Operations};

    /// An unpacked ML-KEM IND-CPA Private Key
    pub(crate) struct IndCpaPrivateKeyUnpacked<const K: usize, Vector: Operations> {
        pub(crate) secret_as_ntt: [PolynomialRingElement<Vector>; K],
    }

    impl<const K: usize, Vector: Operations> Default for IndCpaPrivateKeyUnpacked<K, Vector> {
        #[inline(always)]
        fn default() -> Self {
            Self {
                secret_as_ntt: [PolynomialRingElement::<Vector>::ZERO(); K],
            }
        }
    }

    /// An unpacked ML-KEM IND-CPA Public Key
    #[derive(Clone)]
    pub(crate) struct IndCpaPublicKeyUnpacked<
        const K: usize,
        const K_SQUARED: usize,
        Vector: Operations,
    > {
        pub(crate) t_as_ntt: [PolynomialRingElement<Vector>; K],
        pub(crate) seed_for_A: [u8; 32],
        pub(crate) A: [PolynomialRingElement<Vector>; K_SQUARED],
    }

    impl<const K: usize, const K_SQUARED: usize, Vector: Operations> Default
        for IndCpaPublicKeyUnpacked<K, K_SQUARED, Vector>
    {
        #[inline(always)]
        fn default() -> Self {
            Self {
                t_as_ntt: [PolynomialRingElement::<Vector>::ZERO(); K],
                seed_for_A: [0u8; 32],
                A: [PolynomialRingElement::<Vector>::ZERO(); K_SQUARED],
            }
        }
    }
}
#[cfg(not(hax))]
use libcrux_secrets::ClassifyRefMut as _;
use libcrux_secrets::{Classify as _, Declassify as _, DeclassifyRef as _, I16, I32, U8};
use unpacked::*;

/// Concatenate `t` and `ρ` into the public key.
#[hax_lib::requires(
    (K == 2 || K == 3 || K == 4) &&
    seed_for_a.len() == 32 &&
    serialized.len() == K * BYTES_PER_RING_ELEMENT + 32
)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
#[inline(always)]
pub(crate) fn serialize_public_key_mut<
    const K: usize,
    const PUBLIC_KEY_SIZE: usize,
    Vector: Operations,
>(
    t_as_ntt: &[PolynomialRingElement<Vector>; K],
    seed_for_a: &[u8],
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    // XXX: We need a separate version for hax, entirely without
    // classification. The reason is that hax does not support for
    // `&mut`-returning functions.
    // (see https://github.com/cryspen/hax/issues/420)
    #[cfg(not(hax))]
    serialize_vector::<K, Vector>(
        t_as_ntt,
        (&mut serialized[0..ranked_bytes_per_ring_element(K)]).classify_ref_mut(),
        scratch,
    );
    #[cfg(hax)]
    serialize_vector::<K, Vector>(
        t_as_ntt,
        &mut serialized[0..ranked_bytes_per_ring_element(K)],
        scratch,
    );
    // Above we needed to partially classify_ref the public serialized slice. This marks
    // the memory permanently as Undefined for valgrind and can lead to false positives.
    // Thus we `ct_declassify` the memory here.
    ct_declassify(&serialized[0..ranked_bytes_per_ring_element(K)]);

    serialized[ranked_bytes_per_ring_element(K)..].copy_from_slice(seed_for_a);
}

/// Call [`serialize_uncompressed_ring_element`] for each ring element.
#[hax_lib::requires(K <= 4 && K > 0 && out.len() == K * BYTES_PER_RING_ELEMENT)]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
#[inline(always)]
pub(crate) fn serialize_vector<const K: usize, Vector: Operations>(
    key: &[PolynomialRingElement<Vector>; K],
    out: &mut [U8],
    scratch: &mut Vector,
) {
    cloop! {
        for (i, re) in key.into_iter().enumerate() {
            #[cfg(hax)]
            hax_lib::loop_invariant!(|i: usize| {
                out.len() == K * BYTES_PER_RING_ELEMENT
            });

            serialize_uncompressed_ring_element(&re, scratch, &mut out[i * BYTES_PER_RING_ELEMENT..(i + 1) * BYTES_PER_RING_ELEMENT]);
        }
    }
}

/// Sample a vector of ring elements from a centered binomial distribution.
#[hax_lib::requires(
    (K == 2 || K == 3 || K == 4) &&
    ETA2 == 2 &&
    ETA2_RANDOMNESS_SIZE == 64 * ETA2 &&
    PRF_OUTPUT_SIZE == K * ETA2_RANDOMNESS_SIZE &&
    error_1.len() == K &&
    (domain_separator as usize) < 2 * K
)]
#[hax_lib::ensures(|result|
    future(error_1).len() == error_1.len() &&
    result == domain_separator + K as u8
)]
#[inline(always)]
fn sample_ring_element_cbd<
    const K: usize,
    const ETA2_RANDOMNESS_SIZE: usize,
    const ETA2: usize,
    const PRF_OUTPUT_SIZE: usize,
    Vector: Operations,
    Hasher: Hash,
>(
    prf_input: &[U8; 33],
    mut domain_separator: u8,
    error_1: &mut [PolynomialRingElement<Vector>],
    sample_buffer: &mut [I16; 256],
) -> u8 {
    let mut prf_inputs = [prf_input.clone(); K];
    // See https://github.com/hacspec/hax/issues/1167
    #[cfg(hax)]
    let _domain_separator_init = domain_separator;

    domain_separator = prf_input_inc::<K>(&mut prf_inputs, domain_separator);
    let mut prf_outputs = [0u8.classify(); PRF_OUTPUT_SIZE];
    Hasher::PRFxN(
        prf_inputs.as_slice(),
        &mut prf_outputs,
        ETA2_RANDOMNESS_SIZE,
    );
    for i in 0..K {
        #[cfg(hax)]
        hax_lib::loop_invariant!(|i: usize| { error_1.len() == K });
        let randomness = &prf_outputs[i * ETA2_RANDOMNESS_SIZE..(i + 1) * ETA2_RANDOMNESS_SIZE];
        sample_from_binomial_distribution::<ETA2, Vector>(randomness, sample_buffer);
        PolynomialRingElement::from_i16_array(sample_buffer, &mut error_1[i]);
    }
    domain_separator
}

/// Sample a vector of ring elements from a centered binomial distribution and
/// convert them into their NTT representations.
#[hax_lib::requires(
    (K == 2 || K == 3 || K == 4) &&
    (ETA == 3 || ETA == 2) &&
    ETA_RANDOMNESS_SIZE == 64 * ETA &&
    PRF_OUTPUT_SIZE == K * ETA_RANDOMNESS_SIZE &&
    re_as_ntt.len() == K &&
    (domain_separator as usize) < 2 * K
)]
#[hax_lib::ensures(|result| future(re_as_ntt).len() == re_as_ntt.len() && result == domain_separator + K as u8)]
#[inline(always)]
fn sample_vector_cbd_then_ntt<
    const K: usize,
    const ETA: usize,
    const ETA_RANDOMNESS_SIZE: usize,
    const PRF_OUTPUT_SIZE: usize,
    Vector: Operations,
    Hasher: Hash,
>(
    re_as_ntt: &mut [PolynomialRingElement<Vector>],
    prf_input: &[U8; 33],
    mut domain_separator: u8,
    scratch: &mut Vector,
) -> u8 {
    let mut prf_inputs = [prf_input.clone(); K];

    #[cfg(hax)]
    let _domain_separator_init = domain_separator;

    domain_separator = prf_input_inc::<K>(&mut prf_inputs, domain_separator);
    let mut prf_outputs = [0u8.classify(); PRF_OUTPUT_SIZE];
    Hasher::PRFxN(&prf_inputs, &mut prf_outputs, ETA_RANDOMNESS_SIZE);
    for i in 0..K {
        #[cfg(hax)]
        hax_lib::loop_invariant!(|_i: usize| { re_as_ntt.len() == K });
        let randomness = &prf_outputs[i * ETA_RANDOMNESS_SIZE..(i + 1) * ETA_RANDOMNESS_SIZE];
        let mut sample_buffer = [0i16.classify(); 256];
        sample_from_binomial_distribution::<ETA, Vector>(randomness, &mut sample_buffer);
        PolynomialRingElement::from_i16_array(&sample_buffer, &mut re_as_ntt[i]);
        ntt_binomially_sampled_ring_element(&mut re_as_ntt[i], scratch);
    }
    domain_separator
}

/// This function implements most of <strong>Algorithm 12</strong> of the
/// NIST FIPS 203 specification; this is the Kyber CPA-PKE key generation algorithm.
///
/// We say "most of" since Algorithm 12 samples the required randomness within
/// the function itself, whereas this implementation expects it to be provided
/// through the `key_generation_seed` parameter.
///
/// Algorithm 12 is reproduced below:
///
/// ```plaintext
/// Output: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
/// Output: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
///
/// d ←$ B
/// (ρ,σ) ← G(d)
/// N ← 0
/// for (i ← 0; i < k; i++)
///     for(j ← 0; j < k; j++)
///         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
///     end for
/// end for
/// for(i ← 0; i < k; i++)
///     s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
///     N ← N + 1
/// end for
/// for(i ← 0; i < k; i++)
///     e[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(σ,N))
///     N ← N + 1
/// end for
/// ŝ ← NTT(s)
/// ê ← NTT(e)
/// t̂ ← Â◦ŝ + ê
/// ekₚₖₑ ← ByteEncode₁₂(t̂) ‖ ρ
/// dkₚₖₑ ← ByteEncode₁₂(ŝ)
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
#[hax_lib::requires(
    (K == 2 || K == 3 || K == 4) &&
    K_SQUARED == K * K && 
    (ETA1 == 3 || ETA1 == 2) &&
    ETA1_RANDOMNESS_SIZE == 64 * ETA1 &&
    PRF_OUTPUT_SIZE1 == K * ETA1_RANDOMNESS_SIZE &&
    key_generation_seed.len() == CPA_PKE_KEY_GENERATION_SEED_SIZE
)]
#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn generate_keypair_unpacked<
    const K: usize,
    const K_SQUARED: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    const PRF_OUTPUT_SIZE1: usize,
    Vector: Operations,
    Hasher: Hash,
    Scheme: Variant,
>(
    key_generation_seed: &[U8],
    private_key: &mut IndCpaPrivateKeyUnpacked<K, Vector>,
    public_key: &mut IndCpaPublicKeyUnpacked<K, K_SQUARED, Vector>,
    scratch: &mut PolynomialRingElement<Vector>,
    s_cache: &mut [PolynomialRingElement<Vector>; K],
    accumulator: &mut [I32; 256],
) {
    // (ρ,σ) := G(d) for Kyber, (ρ,σ) := G(d || K) for ML-KEM
    let mut hashed = [0u8.classify(); 64];
    Scheme::cpa_keygen_seed::<K, Hasher>(key_generation_seed, &mut hashed);
    let (seed_for_A, seed_for_secret_and_error) = hashed.split_at(32);

    // Declassification: The seed for A is part of the public key
    sample_matrix_A::<K, Vector, Hasher>(
        &mut public_key.A,
        &(into_padded_array(seed_for_A)).declassify(),
        true,
    );

    let prf_input: [U8; 33] = into_padded_array(seed_for_secret_and_error);
    let domain_separator = sample_vector_cbd_then_ntt::<
        K,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        PRF_OUTPUT_SIZE1,
        Vector,
        Hasher,
    >(
        &mut private_key.secret_as_ntt,
        &prf_input,
        0,
        &mut scratch.coefficients[0],
    );
    let mut error_as_ntt = from_fn(|_| PolynomialRingElement::<Vector>::ZERO());
    let _ = sample_vector_cbd_then_ntt::<
        K,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        PRF_OUTPUT_SIZE1,
        Vector,
        Hasher,
    >(
        &mut error_as_ntt,
        &prf_input,
        domain_separator,
        &mut scratch.coefficients[0],
    );

    // tˆ := Aˆ ◦ sˆ + eˆ
    compute_As_plus_e(
        &mut public_key.t_as_ntt,
        &public_key.A,
        &private_key.secret_as_ntt,
        &error_as_ntt,
        s_cache,
        accumulator,
    );

    // Declassification: Writing out part of the public key.
    public_key
        .seed_for_A
        .copy_from_slice(seed_for_A.declassify_ref());

    // For encapsulation, we need to store A not Aˆ, and so we untranspose A
    // However, we pass A_transpose here and let the IND-CCA layer do the untranspose.
    // We could do it here, but then we would pay the performance cost (if any) for the packed API as well.
}

#[hax_lib::requires(
    (K == 2 || K == 3 || K == 4) &&
    K_SQUARED == K * K &&
    (ETA1 == 3 || ETA1 == 2) &&
    ETA1_RANDOMNESS_SIZE == 64 * ETA1 &&
    PRF_OUTPUT_SIZE1 == K * ETA1_RANDOMNESS_SIZE &&
    PRIVATE_KEY_SIZE == K * BYTES_PER_RING_ELEMENT &&
    PUBLIC_KEY_SIZE == K * BYTES_PER_RING_ELEMENT + 32 &&
    key_generation_seed.len() == CPA_PKE_KEY_GENERATION_SEED_SIZE &&
    serialized_ind_cpa_private_key.len() == PRIVATE_KEY_SIZE &&
    serialized_public_key.len() == PUBLIC_KEY_SIZE
)]
#[hax_lib::ensures(|_|
    future(serialized_ind_cpa_private_key).len() == PRIVATE_KEY_SIZE &&
    future(serialized_public_key).len() == PUBLIC_KEY_SIZE
)]
#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn generate_keypair<
    const K: usize,
    const K_SQUARED: usize,
    const PRIVATE_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    const PRF_OUTPUT_SIZE1: usize,
    Vector: Operations,
    Hasher: Hash,
    Scheme: Variant,
>(
    key_generation_seed: &[U8],
    serialized_ind_cpa_private_key: &mut [U8],
    serialized_public_key: &mut [u8],
    scratch: &mut PolynomialRingElement<Vector>,
    s_cache: &mut [PolynomialRingElement<Vector>; K],
    accumulator: &mut [I32; 256],
) {
    // XXX: Can Eurydice handle these when passind in as &mut from outside?
    let mut private_key = IndCpaPrivateKeyUnpacked::default();
    let mut public_key = IndCpaPublicKeyUnpacked::default();

    generate_keypair_unpacked::<
        K,
        K_SQUARED,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        PRF_OUTPUT_SIZE1,
        Vector,
        Hasher,
        Scheme,
    >(
        key_generation_seed,
        &mut private_key,
        &mut public_key,
        scratch,
        s_cache,
        accumulator,
    );

    serialize_unpacked_secret_key::<K, K_SQUARED, PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE, Vector>(
        &public_key,
        &private_key,
        serialized_ind_cpa_private_key,
        serialized_public_key,
        &mut scratch.coefficients[0],
    )
}

/// Serialize the secret key from the unpacked key pair generation.
#[hax_lib::requires(
    (K == 2 || K == 3 || K == 4) &&
    PRIVATE_KEY_SIZE == K * BYTES_PER_RING_ELEMENT &&
    PUBLIC_KEY_SIZE == K * BYTES_PER_RING_ELEMENT + 32 &&
    serialized_private_key.len() == PRIVATE_KEY_SIZE &&
    serialized_public_key.len() == PUBLIC_KEY_SIZE
)]
#[hax_lib::ensures(|_|
    future(serialized_private_key).len() == PRIVATE_KEY_SIZE &&
    future(serialized_public_key).len() == PUBLIC_KEY_SIZE
)]
pub(crate) fn serialize_unpacked_secret_key<
    const K: usize,
    const K_SQUARED: usize,
    const PRIVATE_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    Vector: Operations,
>(
    public_key: &IndCpaPublicKeyUnpacked<K, K_SQUARED, Vector>,
    private_key: &IndCpaPrivateKeyUnpacked<K, Vector>,
    serialized_private_key: &mut [U8],
    serialized_public_key: &mut [u8],
    scratch: &mut Vector,
) {
    // pk := (Encode_12(tˆ mod^{+}q) || ρ)
    serialize_public_key_mut::<K, PUBLIC_KEY_SIZE, Vector>(
        &public_key.t_as_ntt,
        &public_key.seed_for_A,
        serialized_public_key,
        scratch,
    );

    // sk := Encode_12(sˆ mod^{+}q)
    serialize_vector(&private_key.secret_as_ntt, serialized_private_key, scratch);
}

/// Call [`compress_then_serialize_ring_element_u`] on each ring element.
#[hax_lib::requires(
    (K == 2 || K == 3 || K == 4) && 
    ((U_COMPRESSION_FACTOR == 10 && BLOCK_LEN == crate::polynomial::VECTORS_IN_RING_ELEMENT * 20)
        || (U_COMPRESSION_FACTOR == 11 && BLOCK_LEN == crate::polynomial::VECTORS_IN_RING_ELEMENT * 22)) &&
    C1_LEN == K * BLOCK_LEN && 
    out.len() == C1_LEN
)]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
#[inline(always)]
fn compress_then_serialize_u<
    const K: usize,
    const C1_LEN: usize,
    const U_COMPRESSION_FACTOR: usize,
    const BLOCK_LEN: usize,
    Vector: Operations,
>(
    input: [PolynomialRingElement<Vector>; K],
    out: &mut [u8],
    scratch: &mut Vector,
) {
    cloop! {
        for (i, re) in input.into_iter().enumerate() {
            #[cfg(hax)]
            hax_lib::loop_invariant!(|_:usize| out.len() == C1_LEN);
            compress_then_serialize_ring_element_u::<U_COMPRESSION_FACTOR, BLOCK_LEN, Vector>(&re, &mut out[i * (C1_LEN / K)..(i + 1) * (C1_LEN / K)],scratch);
        }
    };
}

/// This function implements <strong>Algorithm 13</strong> of the
/// NIST FIPS 203 specification; this is the Kyber CPA-PKE encryption algorithm.
///
/// Algorithm 13 is reproduced below:
///
/// ```plaintext
/// Input: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
/// Input: message m ∈ 𝔹^{32}.
/// Input: encryption randomness r ∈ 𝔹^{32}.
/// Output: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
///
/// N ← 0
/// t̂ ← ByteDecode₁₂(ekₚₖₑ[0:384k])
/// ρ ← ekₚₖₑ[384k: 384k + 32]
/// for (i ← 0; i < k; i++)
///     for(j ← 0; j < k; j++)
///         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
///     end for
/// end for
/// for(i ← 0; i < k; i++)
///     r[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(r,N))
///     N ← N + 1
/// end for
/// for(i ← 0; i < k; i++)
///     e₁[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
///     N ← N + 1
/// end for
/// e₂ ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
/// r̂ ← NTT(r)
/// u ← NTT-¹(Âᵀ ◦ r̂) + e₁
/// μ ← Decompress₁(ByteDecode₁(m)))
/// v ← NTT-¹(t̂ᵀ ◦ rˆ) + e₂ + μ
/// c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
/// c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
/// return c ← (c₁ ‖ c₂)
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
#[allow(non_snake_case)]
#[hax_lib::requires(
    (K == 2 || K == 3 || K == 4) &&
    K_SQUARED == K * K &&
    (ETA1 == 3 || ETA1 == 2) &&
    ETA1_RANDOMNESS_SIZE == 64 * ETA1 &&
    PRF_OUTPUT_SIZE1 == K * ETA1_RANDOMNESS_SIZE &&
    ETA2 == 2 &&
    ETA2_RANDOMNESS_SIZE == 64 * ETA2 &&
    PRF_OUTPUT_SIZE2 == K * ETA2_RANDOMNESS_SIZE &&
    ((U_COMPRESSION_FACTOR == 10 && BLOCK_LEN == crate::polynomial::VECTORS_IN_RING_ELEMENT * 20)
        || (U_COMPRESSION_FACTOR == 11 && BLOCK_LEN == crate::polynomial::VECTORS_IN_RING_ELEMENT * 22)) &&
    (V_COMPRESSION_FACTOR == 4 && C2_LEN == 128 ||
        V_COMPRESSION_FACTOR == 5 && C2_LEN == 160) &&
    C1_LEN == K * BLOCK_LEN &&
    CIPHERTEXT_SIZE == C1_LEN + C2_LEN &&
    T_AS_NTT_ENCODED_SIZE == BYTES_PER_RING_ELEMENT * K &&
    public_key.len() == T_AS_NTT_ENCODED_SIZE + 32 &&
    randomness.len() == SHARED_SECRET_SIZE &&
    ciphertext.len() == CIPHERTEXT_SIZE &&
    r_as_ntt.len() == K &&
    cache.len() == K
)]
#[hax_lib::ensures(|_|
    future(ciphertext).len() == CIPHERTEXT_SIZE &&
    future(r_as_ntt).len() == K &&
    future(cache).len() == K
)]
#[inline(always)]
pub(crate) fn encrypt<
    const K: usize,
    const K_SQUARED: usize,
    const CIPHERTEXT_SIZE: usize,
    const T_AS_NTT_ENCODED_SIZE: usize,
    const C1_LEN: usize,
    const C2_LEN: usize,
    const U_COMPRESSION_FACTOR: usize,
    const V_COMPRESSION_FACTOR: usize,
    const BLOCK_LEN: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    const ETA2: usize,
    const ETA2_RANDOMNESS_SIZE: usize,
    const PRF_OUTPUT_SIZE1: usize,
    const PRF_OUTPUT_SIZE2: usize,
    Vector: Operations,
    Hasher: Hash,
>(
    public_key: &[u8],
    message: &[U8; SHARED_SECRET_SIZE],
    randomness: &[U8],
    ciphertext: &mut [u8],
    matrix_entry: &mut PolynomialRingElement<Vector>,
    r_as_ntt: &mut [PolynomialRingElement<Vector>],
    error_2: &mut PolynomialRingElement<Vector>,
    scratch: &mut Vector,
    cache: &mut [PolynomialRingElement<Vector>],
    accumulator: &mut [I32; 256],
) {
    encrypt_c1::<
        K,
        K_SQUARED,
        C1_LEN,
        U_COMPRESSION_FACTOR,
        BLOCK_LEN,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
        PRF_OUTPUT_SIZE1,
        PRF_OUTPUT_SIZE2,
        Vector,
        Hasher,
    >(
        randomness,
        matrix_entry,
        &public_key[T_AS_NTT_ENCODED_SIZE..],
        &mut ciphertext[0..C1_LEN],
        r_as_ntt,
        error_2,
        scratch,
        cache,
        accumulator,
    );

    encrypt_c2::<K, V_COMPRESSION_FACTOR, C2_LEN, Vector>(
        &public_key[..T_AS_NTT_ENCODED_SIZE],
        matrix_entry,
        r_as_ntt,
        error_2,
        message,
        &mut ciphertext[C1_LEN..],
        scratch,
        cache,
        accumulator,
    );
}

#[hax_lib::requires(
    (K == 2 || K == 3 || K == 4) &&
    (ETA1 == 3 || ETA1 == 2) &&
    ETA1_RANDOMNESS_SIZE == 64 * ETA1 &&
    PRF_OUTPUT_SIZE1 == K * ETA1_RANDOMNESS_SIZE &&
    ETA2 == 2 &&
    ETA2_RANDOMNESS_SIZE == 64 * ETA2 &&
    PRF_OUTPUT_SIZE2 == K * ETA2_RANDOMNESS_SIZE &&
    ((U_COMPRESSION_FACTOR == 10 && BLOCK_LEN == crate::polynomial::VECTORS_IN_RING_ELEMENT * 20)
        || (U_COMPRESSION_FACTOR == 11 && BLOCK_LEN == crate::polynomial::VECTORS_IN_RING_ELEMENT * 22)) &&
    C1_LEN == K * BLOCK_LEN && 
    randomness.len() == 32 &&
    seed_for_a.len() == 32 &&
    ciphertext.len() == C1_LEN &&
    r_as_ntt.len() == K &&
    cache.len() == K
)]
#[hax_lib::ensures(|_|
    future(ciphertext).len() == C1_LEN &&
    future(r_as_ntt).len() == K &&
    future(cache).len() == K
)]
#[inline(always)]
pub(crate) fn encrypt_c1<
    const K: usize,
    const K_SQUARED: usize,
    const C1_LEN: usize,
    const U_COMPRESSION_FACTOR: usize,
    const BLOCK_LEN: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    const ETA2: usize,
    const ETA2_RANDOMNESS_SIZE: usize,
    const PRF_OUTPUT_SIZE1: usize,
    const PRF_OUTPUT_SIZE2: usize,
    Vector: Operations,
    Hasher: Hash,
>(
    randomness: &[U8],
    matrix_entry: &mut PolynomialRingElement<Vector>,
    seed_for_a: &[u8],
    ciphertext: &mut [u8], // C1_LEN
    r_as_ntt: &mut [PolynomialRingElement<Vector>],
    error_2: &mut PolynomialRingElement<Vector>,
    scratch: &mut Vector,
    cache: &mut [PolynomialRingElement<Vector>],
    accumulator: &mut [I32; 256],
) {
    // for i from 0 to k−1 do
    //     r[i] := CBD{η1}(PRF(r, N))
    //     N := N + 1
    // end for
    // rˆ := NTT(r)
    let mut prf_input: [U8; 33] = into_padded_array(randomness);
    let domain_separator = sample_vector_cbd_then_ntt::<
        K,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        PRF_OUTPUT_SIZE1,
        Vector,
        Hasher,
    >(r_as_ntt, &prf_input, 0, scratch);

    // for i from 0 to k−1 do
    //     e1[i] := CBD_{η2}(PRF(r,N))
    //     N := N + 1
    // end for
    let mut error_1: [PolynomialRingElement<Vector>; K] =
        from_fn(|_i| PolynomialRingElement::<Vector>::ZERO());
    let mut sampling_buffer = [0i16.classify(); 256];
    let domain_separator =
        sample_ring_element_cbd::<K, ETA2_RANDOMNESS_SIZE, ETA2, PRF_OUTPUT_SIZE2, Vector, Hasher>(
            &prf_input,
            domain_separator,
            &mut error_1,
            &mut sampling_buffer,
        );

    // e_2 := CBD{η2}(PRF(r, N))
    prf_input[32] = domain_separator.classify();

    let mut prf_output = [0u8.classify(); ETA2_RANDOMNESS_SIZE];
    Hasher::PRF::<ETA2_RANDOMNESS_SIZE>(&prf_input, &mut prf_output);
    sample_from_binomial_distribution::<ETA2, Vector>(&prf_output, &mut sampling_buffer);
    PolynomialRingElement::from_i16_array(&sampling_buffer, error_2);

    // u := NTT^{-1}(AˆT ◦ rˆ) + e_1
    let mut u = from_fn(|_i| PolynomialRingElement::<Vector>::ZERO());

    compute_vector_u::<K, Vector, Hasher>(
        matrix_entry,
        seed_for_a,
        r_as_ntt,
        &error_1,
        &mut u,
        scratch,
        cache,
        accumulator,
    );

    // // c_1 := Encode_{du}(Compress_q(u,d_u))
    compress_then_serialize_u::<K, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, Vector>(
        u, ciphertext, scratch,
    );
}

#[hax_lib::requires(
    K > 0 && K <= 4 &&
    (V_COMPRESSION_FACTOR == 4 && C2_LEN == 128 ||
        V_COMPRESSION_FACTOR == 5 && C2_LEN == 160) &&
    public_key.len() == BYTES_PER_RING_ELEMENT * K &&
    cache.len() == K &&
    r_as_ntt.len() == K &&
    ciphertext.len() == C2_LEN
)]
#[hax_lib::ensures(|_| future(ciphertext).len() == C2_LEN)]
#[inline(always)]
pub(crate) fn encrypt_c2<
    const K: usize,
    const V_COMPRESSION_FACTOR: usize,
    const C2_LEN: usize,
    Vector: Operations,
>(
    public_key: &[u8],
    t_as_ntt_entry: &mut PolynomialRingElement<Vector>,
    r_as_ntt: &[PolynomialRingElement<Vector>],
    error_2: &PolynomialRingElement<Vector>,
    message: &[U8; SHARED_SECRET_SIZE],
    ciphertext: &mut [u8],
    scratch: &mut Vector,
    cache: &[PolynomialRingElement<Vector>],
    accumulator: &mut [I32; 256],
) {
    // v := NTT^{−1}(tˆT ◦ rˆ) + e_2 + Decompress_q(Decode_1(m),1)
    let mut message_as_ring_element = PolynomialRingElement::<Vector>::ZERO();
    deserialize_then_decompress_message(message, &mut message_as_ring_element);
    let mut v = PolynomialRingElement::<Vector>::ZERO();
    compute_ring_element_v::<K, Vector>(
        public_key,
        t_as_ntt_entry,
        r_as_ntt,
        error_2,
        &message_as_ring_element,
        &mut v,
        scratch,
        cache,
        accumulator,
    );

    // c_2 := Encode_{dv}(Compress_q(v,d_v))
    compress_then_serialize_ring_element_v::<K, V_COMPRESSION_FACTOR, C2_LEN, Vector>(
        v, ciphertext, scratch,
    );
}

/// Call [`deserialize_then_decompress_ring_element_u`] on each ring element
/// in the `ciphertext`.
#[hax_lib::requires(
    (K == 2 || K == 3 || K ==4) &&
    (U_COMPRESSION_FACTOR == 10 || U_COMPRESSION_FACTOR == 11) &&
    ciphertext.len() == K * 32 * U_COMPRESSION_FACTOR &&
    u_as_ntt.len() == K
)]
#[hax_lib::ensures(|_| future(u_as_ntt).len() == K)]
#[inline(always)]
fn deserialize_then_decompress_u<
    const K: usize,
    const CIPHERTEXT_SIZE: usize,
    const U_COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    ciphertext: &[u8],
    u_as_ntt: &mut [PolynomialRingElement<Vector>],
    scratch: &mut Vector,
) {
    cloop! {
        for (i, u_bytes) in ciphertext
            .chunks_exact((COEFFICIENTS_IN_RING_ELEMENT * U_COMPRESSION_FACTOR) / 8)
            .enumerate()
        {
            #[cfg(hax)]
            hax_lib::loop_invariant!(|_i: usize| u_as_ntt.len() == K);
            deserialize_then_decompress_ring_element_u::<U_COMPRESSION_FACTOR, Vector>(u_bytes, &mut u_as_ntt[i]);
            ntt_vector_u::<U_COMPRESSION_FACTOR, Vector>(&mut u_as_ntt[i], scratch);
        }
    }
}

/// Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
#[hax_lib::requires(
    K > 0 && K <= 4 &&
    secret_key.len() == K * BYTES_PER_RING_ELEMENT &&
    secret_as_ntt.len() == K
)]
#[hax_lib::ensures(|_| future(secret_as_ntt).len() == K)]
#[inline(always)]
pub(crate) fn deserialize_vector<const K: usize, Vector: Operations>(
    secret_key: &[U8],
    secret_as_ntt: &mut [PolynomialRingElement<Vector>],
) {
    for i in 0..K {
        #[cfg(hax)]
        hax_lib::loop_invariant!(|i: usize| secret_as_ntt.len() == K);
        deserialize_to_uncompressed_ring_element(
            &secret_key[i * BYTES_PER_RING_ELEMENT..(i + 1) * BYTES_PER_RING_ELEMENT],
            &mut secret_as_ntt[i],
        );
    }
}

/// This function implements <strong>Algorithm 14</strong> of the
/// NIST FIPS 203 specification; this is the Kyber CPA-PKE decryption algorithm.
///
/// Algorithm 14 is reproduced below:
///
/// ```plaintext
/// Input: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
/// Input: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
/// Output: message m ∈ 𝔹^{32}.
///
/// c₁ ← c[0 : 32dᵤk]
/// c₂ ← c[32dᵤk : 32(dᵤk + dᵥ)]
/// u ← Decompress_{dᵤ}(ByteDecode_{dᵤ}(c₁))
/// v ← Decompress_{dᵥ}(ByteDecode_{dᵥ}(c₂))
/// ŝ ← ByteDecode₁₂(dkₚₖₑ)
/// w ← v - NTT-¹(ŝᵀ ◦ NTT(u))
/// m ← ByteEncode₁(Compress₁(w))
/// return m
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
#[allow(non_snake_case)]
#[hax_lib::requires(
    (K == 2 || K == 3 || K ==4) &&
    ((U_COMPRESSION_FACTOR == 10 && VECTOR_U_ENCODED_SIZE == K * crate::polynomial::VECTORS_IN_RING_ELEMENT * 20)
        || (U_COMPRESSION_FACTOR == 11 && VECTOR_U_ENCODED_SIZE == K * crate::polynomial::VECTORS_IN_RING_ELEMENT * 22)) &&
    (V_COMPRESSION_FACTOR == 4 || V_COMPRESSION_FACTOR == 5) &&
    CIPHERTEXT_SIZE == K * 32 * U_COMPRESSION_FACTOR + 32 * V_COMPRESSION_FACTOR &&
    decrypted.len() == SHARED_SECRET_SIZE
)]
#[hax_lib::ensures(|_| future(decrypted).len() == decrypted.len())]
#[inline(always)]
pub(crate) fn decrypt_unpacked<
    const K: usize,
    const CIPHERTEXT_SIZE: usize,
    const VECTOR_U_ENCODED_SIZE: usize,
    const U_COMPRESSION_FACTOR: usize,
    const V_COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    secret_key: &IndCpaPrivateKeyUnpacked<K, Vector>,
    ciphertext: &[u8; CIPHERTEXT_SIZE],
    decrypted: &mut [U8],
    scratch: &mut Vector,
    accumulator: &mut [I32; 256],
) {
    // u := Decompress_q(Decode_{d_u}(c), d_u)
    let mut u_as_ntt = from_fn(|_| PolynomialRingElement::<Vector>::ZERO());
    deserialize_then_decompress_u::<K, CIPHERTEXT_SIZE, U_COMPRESSION_FACTOR, Vector>(
        &ciphertext[..VECTOR_U_ENCODED_SIZE],
        &mut u_as_ntt,
        scratch,
    );

    // v := Decompress_q(Decode_{d_v}(c + d_u·k·n / 8), d_v)
    let mut v = PolynomialRingElement::<Vector>::ZERO();
    deserialize_then_decompress_ring_element_v::<K, V_COMPRESSION_FACTOR, Vector>(
        &ciphertext[VECTOR_U_ENCODED_SIZE..],
        &mut v,
    );

    // // m := Encode_1(Compress_q(v − NTT^{−1}(sˆT ◦ NTT(u)) , 1))
    let mut message = PolynomialRingElement::<Vector>::ZERO();
    compute_message(
        &v,
        &secret_key.secret_as_ntt,
        &u_as_ntt,
        &mut message,
        scratch,
        accumulator,
    );
    compress_then_serialize_message(&message, decrypted, scratch);
}

#[hax_lib::requires(
    (K == 2 || K == 3 || K ==4) &&
    ((U_COMPRESSION_FACTOR == 10 && VECTOR_U_ENCODED_SIZE == K * crate::polynomial::VECTORS_IN_RING_ELEMENT * 20)
        || (U_COMPRESSION_FACTOR == 11 && VECTOR_U_ENCODED_SIZE == K * crate::polynomial::VECTORS_IN_RING_ELEMENT * 22)) &&
    (V_COMPRESSION_FACTOR == 4 || V_COMPRESSION_FACTOR == 5) &&
    CIPHERTEXT_SIZE == K * 32 * U_COMPRESSION_FACTOR + 32 * V_COMPRESSION_FACTOR &&
    secret_key.len() == BYTES_PER_RING_ELEMENT * K &&
    decrypted.len() == SHARED_SECRET_SIZE
)]
#[hax_lib::ensures(|_| future(decrypted).len() == decrypted.len())]
#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn decrypt<
    const K: usize,
    const CIPHERTEXT_SIZE: usize,
    const VECTOR_U_ENCODED_SIZE: usize,
    const U_COMPRESSION_FACTOR: usize,
    const V_COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    secret_key: &[U8],
    ciphertext: &[u8; CIPHERTEXT_SIZE],
    decrypted: &mut [U8],
    scratch: &mut Vector,
    accumulator: &mut [I32; 256],
) {
    // sˆ := Decode_12(sk)
    let mut secret_as_ntt = from_fn(|_| PolynomialRingElement::<Vector>::ZERO());
    deserialize_vector::<K, Vector>(secret_key, &mut secret_as_ntt);
    let secret_key_unpacked = IndCpaPrivateKeyUnpacked { secret_as_ntt };

    decrypt_unpacked::<
        K,
        CIPHERTEXT_SIZE,
        VECTOR_U_ENCODED_SIZE,
        U_COMPRESSION_FACTOR,
        V_COMPRESSION_FACTOR,
        Vector,
    >(
        &secret_key_unpacked,
        ciphertext,
        decrypted,
        scratch,
        accumulator,
    );
}
