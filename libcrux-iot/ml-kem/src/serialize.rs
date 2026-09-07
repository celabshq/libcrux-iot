use libcrux_secrets::{mem_requests::ct_declassify, ClassifyRef as _, U8};

use crate::{
    constants::{BYTES_PER_RING_ELEMENT, SHARED_SECRET_SIZE},
    helper::cloop,
    polynomial::{PolynomialRingElement, VECTORS_IN_RING_ELEMENT},
    vector::{decompress_1, to_unsigned_representative, Operations},
};

#[inline(always)]
pub(super) fn to_unsigned_field_modulus<Vector: Operations>(a: &Vector, out: &mut Vector) {
    to_unsigned_representative::<Vector>(a, out)
}

#[hax_lib::requires(serialized.len() == SHARED_SECRET_SIZE)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
#[inline(always)]
pub(super) fn compress_then_serialize_message<Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
    serialized: &mut [U8],
    scratch: &mut Vector,
) {
    for i in 0..16 {
        #[cfg(hax)]
        #[cfg(not(hax_backend_lean))]
        hax_lib::loop_invariant!(|i: usize| { serialized.len() == SHARED_SECRET_SIZE });
        to_unsigned_field_modulus(&re.coefficients[i], scratch);
        Vector::compress_1(scratch);

        Vector::serialize_1(scratch, &mut serialized[2 * i..2 * i + 2]);
    }
}

#[inline(always)]
pub(super) fn deserialize_then_decompress_message<Vector: Operations>(
    serialized: &[U8; SHARED_SECRET_SIZE],
    re: &mut PolynomialRingElement<Vector>,
) {
    for i in 0..16 {
        Vector::deserialize_1(&serialized[2 * i..2 * i + 2], &mut re.coefficients[i]);
        decompress_1::<Vector>(&mut re.coefficients[i]);
    }
}

#[hax_lib::requires(serialized.len() == BYTES_PER_RING_ELEMENT)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
#[inline(always)]
pub(super) fn serialize_uncompressed_ring_element<Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
    scratch: &mut Vector,
    serialized: &mut [U8],
) {
    #[cfg(not(eurydice))]
    debug_assert!(serialized.len() == BYTES_PER_RING_ELEMENT);

    for i in 0..VECTORS_IN_RING_ELEMENT {
        #[cfg(hax)]
        #[cfg(not(hax_backend_lean))]
        hax_lib::loop_invariant!(|i: usize| { serialized.len() == BYTES_PER_RING_ELEMENT });

        to_unsigned_field_modulus(&re.coefficients[i], scratch);

        Vector::serialize_12(scratch, &mut serialized[24 * i..24 * i + 24]);
    }
}

#[hax_lib::requires(serialized.len() == BYTES_PER_RING_ELEMENT)]
#[inline(always)]
pub(super) fn deserialize_to_uncompressed_ring_element<Vector: Operations>(
    serialized: &[U8],
    re: &mut PolynomialRingElement<Vector>,
) {
    cloop! {
        for (i, bytes) in serialized.chunks_exact(24).enumerate() {
            Vector::deserialize_12(bytes, &mut re.coefficients[i]);
        }
    }
}

/// Only use with public values.
///
/// This MUST NOT be used with secret inputs, like its caller `deserialize_ring_elements_reduced`.
#[hax_lib::requires(
    serialized.len() == BYTES_PER_RING_ELEMENT
)]
#[inline(always)]
pub(crate) fn deserialize_to_reduced_ring_element<Vector: Operations>(
    serialized: &[U8],
    re: &mut PolynomialRingElement<Vector>,
) {
    cloop! {
        for (i, bytes) in serialized.chunks_exact(24).enumerate() {
            Vector::deserialize_12(bytes, &mut re.coefficients[i]);
            Vector::cond_subtract_3329(&mut re.coefficients[i]);
        }
    }
}

/// This function deserializes ring elements and reduces the result by the field
/// modulus.
///
/// This function MUST NOT be used on secret inputs.
#[hax_lib::requires(deserialized_pk.len() == K && public_key.len() / BYTES_PER_RING_ELEMENT == K)]
#[hax_lib::ensures(|_| future(deserialized_pk).len() == deserialized_pk.len())]
#[inline(always)]
pub(super) fn deserialize_ring_elements_reduced<const K: usize, Vector: Operations>(
    public_key: &[u8],
    deserialized_pk: &mut [PolynomialRingElement<Vector>],
) {
    // We need to classify the public key bytes, since the serialization code is the same for
    // secret and non-secret ring elements and will only write to classified output references.
    // We undo this overclassification below.
    let public_key = public_key.classify_ref();
    cloop! {
        for (i, ring_element) in public_key
            .chunks_exact(BYTES_PER_RING_ELEMENT)
            .enumerate()
        {
            #[cfg(hax)]
            #[cfg(not(hax_backend_lean))]
            hax_lib::loop_invariant!(|i: usize| {
                deserialized_pk.len() == K
            });

            deserialize_to_reduced_ring_element(ring_element, &mut deserialized_pk[i]);
        }
    };
    // Above we needed to classify_ref the public key. This marks
    // the memory permanently as Undefined for valgrind and can lead to false positives.
    // Thus we `ct_declassify` the memory here.
    ct_declassify(public_key);
}

#[hax_lib::requires(serialized.len() == BLOCK_LEN && BLOCK_LEN >= VECTORS_IN_RING_ELEMENT * 20)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
#[inline(always)]
fn compress_then_serialize_10<const BLOCK_LEN: usize, Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    #[cfg(not(eurydice))]
    debug_assert!(serialized.len() == BLOCK_LEN);
    for i in 0..VECTORS_IN_RING_ELEMENT {
        #[cfg(hax)]
        #[cfg(not(hax_backend_lean))]
        hax_lib::loop_invariant!(|i: usize| { serialized.len() == BLOCK_LEN });
        to_unsigned_field_modulus(&re.coefficients[i], scratch);
        Vector::compress::<10>(scratch);

        Vector::serialize_10(scratch, &mut serialized[20 * i..20 * i + 20]);
    }
}

#[hax_lib::requires(serialized.len() == BLOCK_LEN && BLOCK_LEN >= VECTORS_IN_RING_ELEMENT * 22)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
#[inline(always)]
fn compress_then_serialize_11<const BLOCK_LEN: usize, Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    #[cfg(not(eurydice))]
    debug_assert!(serialized.len() == BLOCK_LEN);

    for i in 0..VECTORS_IN_RING_ELEMENT {
        #[cfg(hax)]
        #[cfg(not(hax_backend_lean))]
        hax_lib::loop_invariant!(|i: usize| { serialized.len() == BLOCK_LEN });
        to_unsigned_representative::<Vector>(&re.coefficients[i], scratch);
        Vector::compress::<11>(scratch);

        Vector::serialize_11(scratch, &mut serialized[22 * i..22 * i + 22]);
    }
}

#[hax_lib::requires(
    ((U_COMPRESSION_FACTOR == 10 && BLOCK_LEN >= VECTORS_IN_RING_ELEMENT * 20)
      || (U_COMPRESSION_FACTOR == 11 && BLOCK_LEN >= VECTORS_IN_RING_ELEMENT * 22)) &&
    serialized.len() == BLOCK_LEN
)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
#[inline(always)]
pub(super) fn compress_then_serialize_ring_element_u<
    const U_COMPRESSION_FACTOR: usize,
    const BLOCK_LEN: usize,
    Vector: Operations,
>(
    re: &PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    match U_COMPRESSION_FACTOR as u32 {
        10 => compress_then_serialize_10::<BLOCK_LEN, Vector>(re, serialized, scratch),
        11 => compress_then_serialize_11::<BLOCK_LEN, Vector>(re, serialized, scratch),
        _ => unreachable!(),
    }
}

#[hax_lib::requires(serialized.len() == 128)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
#[inline(always)]
fn compress_then_serialize_4<Vector: Operations>(
    re: PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    for i in 0..VECTORS_IN_RING_ELEMENT {
        #[cfg(hax)]
        #[cfg(not(hax_backend_lean))]
        hax_lib::loop_invariant!(|i: usize| { serialized.len() == 128 });
        to_unsigned_field_modulus(&re.coefficients[i], scratch);
        Vector::compress::<4>(scratch);

        Vector::serialize_4(scratch, &mut serialized[8 * i..8 * i + 8]);
    }
}

#[hax_lib::requires(serialized.len() == 160)]
#[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
#[inline(always)]
fn compress_then_serialize_5<Vector: Operations>(
    re: PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    for i in 0..VECTORS_IN_RING_ELEMENT {
        #[cfg(hax)]
        #[cfg(not(hax_backend_lean))]
        hax_lib::loop_invariant!(|i: usize| { serialized.len() == 160 });
        to_unsigned_representative::<Vector>(&re.coefficients[i], scratch);
        Vector::compress::<5>(scratch);

        Vector::serialize_5(scratch, &mut serialized[10 * i..10 * i + 10]);
    }
}

#[hax_lib::requires(
    out.len() == C2_LEN &&
    (V_COMPRESSION_FACTOR == 4 && C2_LEN == 128 ||
        V_COMPRESSION_FACTOR == 5 && C2_LEN == 160))]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
#[inline(always)]
pub(super) fn compress_then_serialize_ring_element_v<
    const K: usize,
    const V_COMPRESSION_FACTOR: usize,
    const C2_LEN: usize,
    Vector: Operations,
>(
    re: PolynomialRingElement<Vector>,
    out: &mut [u8],
    scratch: &mut Vector,
) {
    match V_COMPRESSION_FACTOR as u32 {
        4 => compress_then_serialize_4::<Vector>(re, out, scratch),
        5 => compress_then_serialize_5::<Vector>(re, out, scratch),
        _ => unreachable!(),
    }
}

#[hax_lib::requires(
    serialized.len() == 320
)]
#[inline(always)]
fn deserialize_then_decompress_10<Vector: Operations>(
    serialized: &[u8],
    re: &mut PolynomialRingElement<Vector>,
) {
    cloop! {
        for (i, bytes) in serialized.chunks_exact(20).enumerate() {
            Vector::deserialize_10(bytes, &mut re.coefficients[i]);
            Vector::decompress_ciphertext_coefficient::<10>(&mut re.coefficients[i]);
        }
    }
}

#[hax_lib::requires(
    serialized.len() == 352
)]
#[inline(always)]
fn deserialize_then_decompress_11<Vector: Operations>(
    serialized: &[u8],
    re: &mut PolynomialRingElement<Vector>,
) {
    cloop! {
        for (i, bytes) in serialized.chunks_exact(22).enumerate() {
            Vector::deserialize_11(bytes, &mut re.coefficients[i]);
            Vector::decompress_ciphertext_coefficient::<11>(&mut re.coefficients[i]);
        }
    }
}

#[hax_lib::requires(
    (U_COMPRESSION_FACTOR == 10 || U_COMPRESSION_FACTOR == 11) &&
    serialized.len() == 32 * U_COMPRESSION_FACTOR
)]
#[inline(always)]
pub(super) fn deserialize_then_decompress_ring_element_u<
    const U_COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    serialized: &[u8],
    output: &mut PolynomialRingElement<Vector>,
) {
    match U_COMPRESSION_FACTOR as u32 {
        10 => deserialize_then_decompress_10::<Vector>(serialized, output),
        11 => deserialize_then_decompress_11::<Vector>(serialized, output),
        _ => unreachable!(),
    };
}

#[inline(always)]
#[hax_lib::requires(
    serialized.len() == 128
)]
fn deserialize_then_decompress_4<Vector: Operations>(
    serialized: &[u8],
    re: &mut PolynomialRingElement<Vector>,
) {
    cloop! {
        for (i, bytes) in serialized.chunks_exact(8).enumerate() {
            Vector::deserialize_4(bytes, &mut re.coefficients[i]);
            Vector::decompress_ciphertext_coefficient::<4>(&mut re.coefficients[i]);
        }
    }
}

#[hax_lib::requires(
    serialized.len() == 160
)]
#[inline(always)]
fn deserialize_then_decompress_5<Vector: Operations>(
    serialized: &[u8],
    re: &mut PolynomialRingElement<Vector>,
) {
    cloop! {
        for (i, bytes) in serialized.chunks_exact(10).enumerate() {
            Vector::deserialize_5(bytes, &mut re.coefficients[i]);
            Vector::decompress_ciphertext_coefficient::<5>(&mut re.coefficients[i]);
        }
    }
}

#[hax_lib::requires(
    (V_COMPRESSION_FACTOR == 4 || V_COMPRESSION_FACTOR == 5) &&
    serialized.len() == 32 * V_COMPRESSION_FACTOR)]
#[inline(always)]
pub(super) fn deserialize_then_decompress_ring_element_v<
    const K: usize,
    const V_COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    serialized: &[u8],
    output: &mut PolynomialRingElement<Vector>,
) {
    match V_COMPRESSION_FACTOR as u32 {
        4 => deserialize_then_decompress_4::<Vector>(serialized, output),
        5 => deserialize_then_decompress_5::<Vector>(serialized, output),
        _ => unreachable!(),
    }
}
