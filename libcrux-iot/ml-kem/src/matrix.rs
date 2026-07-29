use libcrux_secrets::{Classify as _, ClassifyRef as _, I32};

use crate::{
    constants::BYTES_PER_RING_ELEMENT, hash_functions::Hash, helper::cloop,
    invert_ntt::invert_ntt_montgomery, polynomial::PolynomialRingElement,
    sampling::sample_from_xof, serialize::deserialize_to_reduced_ring_element, vector::Operations,
};

#[hax_lib::requires(K <= 4 && i < K && j < K && matrix.len() == K * K)]
pub(crate) fn entry<const K: usize, Vector: Operations>(
    matrix: &[PolynomialRingElement<Vector>],
    i: usize,
    j: usize,
) -> &PolynomialRingElement<Vector> {
    #[cfg(not(eurydice))]
    debug_assert!(matrix.len() == K * K);
    #[cfg(not(eurydice))]
    debug_assert!(i < K);
    #[cfg(not(eurydice))]
    debug_assert!(j < K);
    &matrix[i * K + j]
}

#[hax_lib::requires(seed.len() == 32)]
#[inline(always)]
pub(crate) fn sample_matrix_entry<Vector: Operations, Hasher: Hash>(
    out: &mut PolynomialRingElement<Vector>,
    seed: &[u8], // The seed for sampling public matrix A is public itself.
    i: usize,
    j: usize,
) {
    #[cfg(not(eurydice))]
    debug_assert!(seed.len() == 32);
    let mut seed_ij = [0u8; 34];
    seed_ij[0..32].copy_from_slice(seed);
    seed_ij[32] = i as u8;
    seed_ij[33] = j as u8;
    let mut sampled_coefficients = [0usize; 1];
    let mut out_raw = [[0i16; 272]; 1];
    sample_from_xof::<1, Vector, Hasher>(&[seed_ij], &mut sampled_coefficients, &mut out_raw);
    // We classify the matrix entry here to use it in classified arithmetic.
    PolynomialRingElement::from_i16_array(out_raw[0].classify().as_slice(), out);
}

#[hax_lib::requires(K <= 4 && A_transpose.len() == K * K)]
#[hax_lib::ensures(|_| future(A_transpose).len() == A_transpose.len())]
#[inline(always)]
#[allow(non_snake_case)]
pub(crate) fn sample_matrix_A<const K: usize, Vector: Operations, Hasher: Hash>(
    A_transpose: &mut [PolynomialRingElement<Vector>],
    seed: &[u8; 34], // The seed for sampling public matrix A is public itself.
    transpose: bool,
) {
    #[cfg(not(eurydice))]
    debug_assert!(A_transpose.len() == K * K);

    for i in 0..K {
        #[cfg(hax)]
        hax_lib::loop_invariant!(|_: usize| A_transpose.len() == K * K);
        let mut seeds = [*seed; K];
        for j in 0..K {
            #[cfg(hax)]
            hax_lib::loop_invariant!(|_: usize| A_transpose.len() == K * K);
            seeds[j][32] = i as u8;
            seeds[j][33] = j as u8;
        }
        let mut sampled_coefficients = [0usize; K];
        let mut out = [[0i16; 272]; K];
        sample_from_xof::<K, Vector, Hasher>(&seeds, &mut sampled_coefficients, &mut out);
        cloop! {
            for (j, sample) in out.into_iter().enumerate() {
                #[cfg(hax)]
                hax_lib::loop_invariant!(|_:usize| A_transpose.len() == K * K);
                // A[i][j] = A_transpose[j][i]
                if transpose {
                    PolynomialRingElement::from_i16_array(sample[..256].classify_ref(), &mut A_transpose[j * K + i]);
                } else {
                    PolynomialRingElement::from_i16_array(sample[..256].classify_ref(), &mut A_transpose[i * K + j]); // XXX: in this case we might want to copy all of sample at once
                }
            }
        }
    }
}

/// The following functions compute various expressions involving
/// vectors and matrices. The computation of these expressions has been
/// abstracted away into these functions in order to save on loop iterations.

/// Compute v − InverseNTT(sᵀ ◦ NTT(u))
#[inline(always)]
pub(crate) fn compute_message<const K: usize, Vector: Operations>(
    v: &PolynomialRingElement<Vector>,
    secret_as_ntt: &[PolynomialRingElement<Vector>; K],
    u_as_ntt: &[PolynomialRingElement<Vector>; K],
    result: &mut PolynomialRingElement<Vector>,
    scratch: &mut Vector,
    accumulator: &mut [I32; 256],
) {
    *accumulator = [0i32.classify(); 256];
    for i in 0..K {
        secret_as_ntt[i].accumulating_ntt_multiply(&u_as_ntt[i], accumulator);
    }

    PolynomialRingElement::reducing_from_i32_array(accumulator, result);
    invert_ntt_montgomery::<K, Vector>(result, scratch);
    v.subtract_reduce(result);
}

/// Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
#[hax_lib::requires(r_as_ntt.len() == K && cache.len() == K && (public_key.len() / BYTES_PER_RING_ELEMENT) == K)]
#[inline(always)]
pub(crate) fn compute_ring_element_v<const K: usize, Vector: Operations>(
    public_key: &[u8],
    t_as_ntt_entry: &mut PolynomialRingElement<Vector>,
    r_as_ntt: &[PolynomialRingElement<Vector>],
    error_2: &PolynomialRingElement<Vector>,
    message: &PolynomialRingElement<Vector>,
    result: &mut PolynomialRingElement<Vector>,
    scratch: &mut Vector,
    cache: &[PolynomialRingElement<Vector>],
    accumulator: &mut [I32; 256],
) {
    *accumulator = [0i32.classify(); 256];
    cloop! {
        for (i, ring_element) in public_key.chunks_exact(BYTES_PER_RING_ELEMENT).enumerate() {
            deserialize_to_reduced_ring_element(ring_element.classify_ref(), t_as_ntt_entry);
            t_as_ntt_entry.accumulating_ntt_multiply_use_cache(&r_as_ntt[i], accumulator, &cache[i]);
        }
    }
    PolynomialRingElement::reducing_from_i32_array(accumulator, result);

    invert_ntt_montgomery::<K, Vector>(result, scratch);
    error_2.add_message_error_reduce(message, result, scratch);
}

/// Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
#[hax_lib::requires(
    seed.len() == 32 &&
    r_as_ntt.len() == K &&
    error_1.len() == K &&
    result.len() == K &&
    cache.len() == K &&
    K > 0
)]
#[hax_lib::ensures(|_|
    future(result).len() == result.len() &&
    future(cache).len() == cache.len()
)]
#[inline(always)]
pub(crate) fn compute_vector_u<const K: usize, Vector: Operations, Hasher: Hash>(
    matrix_entry: &mut PolynomialRingElement<Vector>,
    seed: &[u8], // The seed for sampling public matrix A is public itself.
    r_as_ntt: &[PolynomialRingElement<Vector>],
    error_1: &[PolynomialRingElement<Vector>],
    result: &mut [PolynomialRingElement<Vector>],
    scratch: &mut Vector,
    cache: &mut [PolynomialRingElement<Vector>],
    accumulator: &mut [I32; 256],
) {
    #[cfg(not(eurydice))]
    debug_assert!(r_as_ntt.len() == K);
    #[cfg(not(eurydice))]
    debug_assert!(error_1.len() == K);

    *accumulator = [0i32.classify(); 256];
    for j in 0..K {
        #[cfg(hax)]
        hax_lib::loop_invariant!(|_: usize| result.len() == K && cache.len() == K);
        sample_matrix_entry::<Vector, Hasher>(matrix_entry, seed, 0, j);
        matrix_entry.accumulating_ntt_multiply_fill_cache(&r_as_ntt[j], accumulator, &mut cache[j]);
    }
    PolynomialRingElement::reducing_from_i32_array(accumulator, &mut result[0]);
    invert_ntt_montgomery::<K, Vector>(&mut result[0], scratch);
    result[0].add_error_reduce(&error_1[0]);

    for i in 1..K {
        #[cfg(hax)]
        hax_lib::loop_invariant!(|_: usize| result.len() == K && cache.len() == K);
        *accumulator = [0i32.classify(); 256];
        for j in 0..K {
            #[cfg(hax)]
            hax_lib::loop_invariant!(|_: usize| result.len() == K && cache.len() == K);
            sample_matrix_entry::<Vector, Hasher>(matrix_entry, seed, i, j);
            matrix_entry.accumulating_ntt_multiply_use_cache(&r_as_ntt[j], accumulator, &cache[j]);
        }
        PolynomialRingElement::reducing_from_i32_array(accumulator, &mut result[i]);

        invert_ntt_montgomery::<K, Vector>(&mut result[i], scratch);
        result[i].add_error_reduce(&error_1[i]);
    }
}

/// Compute Â ◦ ŝ + ê
#[hax_lib::requires(K > 0 && K <= 4 && matrix_A.len() == K * K)]
#[inline(always)]
#[allow(non_snake_case)]
pub(crate) fn compute_As_plus_e<const K: usize, Vector: Operations>(
    t_as_ntt: &mut [PolynomialRingElement<Vector>; K],
    matrix_A: &[PolynomialRingElement<Vector>],
    s_as_ntt: &[PolynomialRingElement<Vector>; K],
    error_as_ntt: &[PolynomialRingElement<Vector>; K],
    s_cache: &mut [PolynomialRingElement<Vector>; K],
    accumulator: &mut [I32; 256],
) {
    // During the first row of multiplications, we build up the cache
    // of intermediate values.
    for j in 0..K {
        entry::<K, Vector>(matrix_A, 0, j).accumulating_ntt_multiply_fill_cache(
            &s_as_ntt[j],
            accumulator,
            &mut s_cache[j],
        );
    }
    PolynomialRingElement::reducing_from_i32_array(accumulator, &mut t_as_ntt[0]);

    t_as_ntt[0].add_standard_error_reduce(&error_as_ntt[0]);

    // The remaining rows can re-use the cached intermediate values.
    for i in 1..K {
        *accumulator = [0i32.classify(); 256];
        for j in 0..K {
            entry::<K, Vector>(matrix_A, i, j).accumulating_ntt_multiply_use_cache(
                &s_as_ntt[j],
                accumulator,
                &s_cache[j],
            );
        }
        PolynomialRingElement::reducing_from_i32_array(accumulator, &mut t_as_ntt[i]);

        t_as_ntt[i].add_standard_error_reduce(&error_as_ntt[i]);
    }
}
