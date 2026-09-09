use libcrux_secrets::{Classify as _, ClassifyRef as _, Declassify as _, I32};

// ============================================================================
// Spec-only impl->spec LIFTS + bound predicates for the four matrix top-level
// theorems (README §L7). Mirror the Lean `Spec/Lift.lean` lifts exactly: the
// impl stores Montgomery/16x16-chunked `i16` lanes, the spec uses canonical
// `FieldElement = u16` in a flat `[_; 256]`. `Repr::repr` is the spec-only pure
// lane reader (16 lanes per SIMD chunk); `FieldElement::from_i16` is the
// canonical-residue constructor (== the Lean `lift_fe`/`feOfZMod` composite).
// ============================================================================

/// Lift one ring element to a hacspec `Polynomial` (`[FieldElement; 256]`),
/// PLAIN domain (`lift_fe`, no Montgomery factor): lane `j` reads SIMD chunk
/// `j/16`, lane `j%16`, then canonicalises with `from_i16`.
#[cfg(hax)]
pub(crate) fn lift_poly<Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
) -> hacspec_ml_kem::parameters::Polynomial {
    core::array::from_fn(|j| {
        hacspec_ml_kem::parameters::FieldElement::from_i16(
            Vector::repr(&re.coefficients[j / 16])[j % 16],
        )
    })
}

/// Lift a length-`K` vector of ring elements (`lift_vec`).
#[cfg(hax)]
pub(crate) fn lift_vec<Vector: Operations, const K: usize>(
    v: &[PolynomialRingElement<Vector>; K],
) -> hacspec_ml_kem::parameters::Vector<K> {
    core::array::from_fn(|i| lift_poly(&v[i]))
}

/// Lift a flat `K*K` slice of ring elements into a `K×K` spec matrix.
/// Mirrors `Spec.Lift.lift_matrix_from_slice`: entry `[j][i] = lift_poly(slice[i*K + j])`.
#[cfg(hax)]
pub(crate) fn lift_matrix_from_slice<Vector: Operations, const K: usize>(
    slice: &[PolynomialRingElement<Vector>],
) -> hacspec_ml_kem::parameters::Matrix<K> {
    core::array::from_fn(|j| core::array::from_fn(|i| lift_poly(&slice[i * K + j])))
}

/// Lift a slice of ring elements (`lift_vec_slice`, the `Slice` analogue of `lift_vec`).
#[cfg(hax)]
pub(crate) fn lift_vec_slice<Vector: Operations, const K: usize>(
    v: &[PolynomialRingElement<Vector>],
) -> hacspec_ml_kem::parameters::Vector<K> {
    core::array::from_fn(|i| lift_poly(&v[i]))
}

/// Lift the matrix sampled on-the-fly from `seed` (spec-only): entry `[i][j]` is
/// `lift_poly(sample_matrix_entry(seed, i, j))`. This is the Rust witness for the
/// opaque `Spec.sample_matrix_A_pure`; the bridge to it is the A1 sampling axiom,
/// applied entry-by-entry.
#[cfg(hax)]
pub(crate) fn lift_matrix_from_seed<Vector: Operations, Hasher: crate::hash_functions::Hash, const K: usize>(
    seed: &[u8],
) -> hacspec_ml_kem::parameters::Matrix<K> {
    core::array::from_fn(|i| {
        core::array::from_fn(|j| {
            let mut entry = PolynomialRingElement::<Vector>::ZERO();
            sample_matrix_entry::<Vector, Hasher>(&mut entry, seed, i, j);
            lift_poly(&entry)
        })
    })
}

/// Lift the `t_as_ntt` vector deserialized from a public key (spec-only): entry
/// `[i]` is `lift_poly(deserialize_to_reduced_ring_element(pk[i*384..(i+1)*384]))`.
/// Rust witness for `Spec.t_as_ntt_from_public_key_pure`; bridged via the A2
/// deserialization axiom, chunk-by-chunk.
#[cfg(hax)]
pub(crate) fn lift_t_as_ntt_from_public_key<Vector: Operations, const K: usize>(
    public_key: &[u8],
) -> hacspec_ml_kem::parameters::Vector<K> {
    core::array::from_fn(|i| {
        let mut re = PolynomialRingElement::<Vector>::ZERO();
        deserialize_to_reduced_ring_element::<Vector>(
            public_key[i * BYTES_PER_RING_ELEMENT..(i + 1) * BYTES_PER_RING_ELEMENT].classify_ref(),
            &mut re,
        );
        lift_poly(&re)
    })
}

/// The NTT-multiply cache that `compute_ring_element_v` consumes is a pure
/// function of `r̂` alone: entry `[j]` is what `accumulating_ntt_multiply_fill_cache`
/// writes for `r_as_ntt[j]` (the second-operand precompute; the `self`/accumulator
/// arguments do not affect the cache output). Spec-only witness so the precondition
/// can name "the correct cache" without a Montgomery predicate on Rust's surface.
#[cfg(hax)]
pub(crate) fn compute_cache<const K: usize, Vector: Operations>(
    r_as_ntt: &[PolynomialRingElement<Vector>],
) -> [PolynomialRingElement<Vector>; K] {
    core::array::from_fn(|j| {
        let mut c = PolynomialRingElement::<Vector>::ZERO();
        let dummy = PolynomialRingElement::<Vector>::ZERO();
        let mut acc = [0i32.classify(); 256];
        dummy.accumulating_ntt_multiply_fill_cache(&r_as_ntt[j], &mut acc, &mut c);
        c
    })
}

/// The cache-pinning predicate (returns `bool` so it folds into `#[requires]` like
/// `poly_bnd`): the caller's `cache` lifts to the same residues as the canonical
/// `compute_cache(r̂)`. Plain-domain lift equality suffices — the Montgomery lane
/// values `cache_post` constrains are `169·` these residues, so equal residues give
/// equal Montgomery values. Together with `vec_slice_bnd` on `cache` (the natAbs
/// half) this reconstructs `compute_ring_element_v`'s internal cache contract.
#[cfg(hax)]
pub(crate) fn cache_matches<const K: usize, Vector: Operations>(
    r_as_ntt: &[PolynomialRingElement<Vector>],
    cache: &[PolynomialRingElement<Vector>],
) -> bool {
    lift_vec_slice::<Vector, K>(cache)
        == lift_vec_slice::<Vector, K>(&compute_cache::<K, Vector>(r_as_ntt))
}

/// One output lane matches a spec field element: the impl lane `x` is the
/// **centered Barrett representative** (`|x| ≤ 1664`) and its canonical residue is
/// `f`. The Rust image of the proof-side `LaneMatches` (PR #190 auditability form):
/// the `#[ensures]` states the result matches the hacspec output lane-wise, rather
/// than through the `lift_poly`/`lift_vec` bijection.
#[cfg(hax)]
pub(crate) fn lane_matches(x: i16, f: hacspec_ml_kem::parameters::FieldElement) -> bool {
    -1664 <= x && x <= 1664 && hacspec_ml_kem::parameters::FieldElement::from_i16(x) == f
}

/// A ring element matches a spec polynomial lane-wise (Rust image of `PolyMatches`).
#[cfg(hax)]
pub(crate) fn poly_matches<Vector: Operations>(
    result: &PolynomialRingElement<Vector>,
    spec: &hacspec_ml_kem::parameters::Polynomial,
) -> hax_lib::prop::Prop {
    hax_lib::forall(|l: usize| {
        if l < 256 {
            lane_matches(Vector::repr(&result.coefficients[l / 16])[l % 16], spec[l])
        } else {
            true
        }
    })
}

/// A vector output matches a spec vector, lane-wise over all `K` rows (Rust image
/// of `VecMatches`). Flattened index `i = r*256 + l` keeps it a single quantifier.
#[cfg(hax)]
pub(crate) fn vec_matches<Vector: Operations, const K: usize>(
    result: &[PolynomialRingElement<Vector>],
    spec: &hacspec_ml_kem::parameters::Vector<K>,
) -> hax_lib::prop::Prop {
    hax_lib::forall(|i: usize| {
        if i < K * 256 {
            lane_matches(
                Vector::repr(&result[i / 256].coefficients[(i % 256) / 16])[(i % 256) % 16],
                spec[i / 256][i % 256],
            )
        } else {
            true
        }
    })
}

/// One lane's centred bound (ordinary fn: the `&&` here is fine, unlike inside a
/// `Prop` quantifier closure).
#[cfg(hax)]
fn lane_bnd(x: i16, b: i16) -> bool {
    -b <= x && x <= b
}

/// All 16 lanes of one SIMD chunk are bounded (unrolled, as `ntt.rs`'s
/// `elements_abs_le` -- through `repr()` since `Vector` is generic).
#[cfg(hax)]
fn chunk_bnd<Vector: Operations>(c: &Vector, b: i16) -> bool {
    let r = Vector::repr(c);
    lane_bnd(r[0], b)
        && lane_bnd(r[1], b)
        && lane_bnd(r[2], b)
        && lane_bnd(r[3], b)
        && lane_bnd(r[4], b)
        && lane_bnd(r[5], b)
        && lane_bnd(r[6], b)
        && lane_bnd(r[7], b)
        && lane_bnd(r[8], b)
        && lane_bnd(r[9], b)
        && lane_bnd(r[10], b)
        && lane_bnd(r[11], b)
        && lane_bnd(r[12], b)
        && lane_bnd(r[13], b)
        && lane_bnd(r[14], b)
        && lane_bnd(r[15], b)
}

/// All 256 lanes of one ring element are bounded (16 chunks, unrolled).
#[cfg(hax)]
pub(crate) fn poly_bnd<Vector: Operations>(re: &PolynomialRingElement<Vector>, b: i16) -> bool {
    chunk_bnd(&re.coefficients[0], b)
        && chunk_bnd(&re.coefficients[1], b)
        && chunk_bnd(&re.coefficients[2], b)
        && chunk_bnd(&re.coefficients[3], b)
        && chunk_bnd(&re.coefficients[4], b)
        && chunk_bnd(&re.coefficients[5], b)
        && chunk_bnd(&re.coefficients[6], b)
        && chunk_bnd(&re.coefficients[7], b)
        && chunk_bnd(&re.coefficients[8], b)
        && chunk_bnd(&re.coefficients[9], b)
        && chunk_bnd(&re.coefficients[10], b)
        && chunk_bnd(&re.coefficients[11], b)
        && chunk_bnd(&re.coefficients[12], b)
        && chunk_bnd(&re.coefficients[13], b)
        && chunk_bnd(&re.coefficients[14], b)
        && chunk_bnd(&re.coefficients[15], b)
}

/// Every ring element of a length-`K` vector is bounded. `K` is a const generic
/// (2/3/4), so this dimension CANNOT be unrolled -- it uses `forall` with an
/// `if k < K { .. } else { true }` body. The `if` keeps the index `v[k]` inside
/// the taken branch, so out-of-range `k` takes `else` and the quantifier is the
/// intended `forall k < K` rather than a vacuous one (the `forall(|k| implies(k
/// < K, ..))` form indexes eagerly and is unsatisfiable).
#[cfg(hax)]
pub(crate) fn vec_bnd<Vector: Operations, const K: usize>(
    v: &[PolynomialRingElement<Vector>; K],
    b: i16,
) -> hax_lib::prop::Prop {
    hax_lib::forall(|k: usize| {
        if k < K {
            poly_bnd(&v[k], b)
        } else {
            true
        }
    })
}

/// Every ring element of a length-`K` slice is bounded (`Slice` analogue of
/// `vec_bnd`, for `compute_vector_u`'s `r`/`error_1` slice arguments).
#[cfg(hax)]
pub(crate) fn vec_slice_bnd<Vector: Operations, const K: usize>(
    v: &[PolynomialRingElement<Vector>],
    b: i16,
) -> hax_lib::prop::Prop {
    hax_lib::forall(|k: usize| {
        if k < K {
            poly_bnd(&v[k], b)
        } else {
            true
        }
    })
}

/// Every ring element of a flat `K*K` matrix slice is bounded (the `matrix_A`
/// dimension of `compute_As_plus_e`). `forall` + `if k < K*K` like `vec_bnd`.
#[cfg(hax)]
pub(crate) fn matrix_slice_bnd<Vector: Operations, const K: usize>(
    slice: &[PolynomialRingElement<Vector>],
    b: i16,
) -> hax_lib::prop::Prop {
    hax_lib::forall(|k: usize| {
        if k < K * K {
            poly_bnd(&slice[k], b)
        } else {
            true
        }
    })
}

/// The `accumulator` scratch is all-zero on entry. `declassify()` is fine here:
/// `#[requires]` is an identity macro outside `cfg(hax)`, so nothing leaks.
#[cfg(hax)]
pub(crate) fn acc_zero(accumulator: &[I32; 256]) -> hax_lib::prop::Prop {
    hax_lib::forall(|n: usize| {
        if n < 256 {
            accumulator[n].declassify() == 0
        } else {
            true
        }
    })
}

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

// `sample_matrix_entry`/`sample_matrix_A` are `--opaque` in the Lean extraction
// (see `hax.toml`): only their signatures are extracted, so there is nothing
// for their contracts to specify there -- and the generated spec blocks for
// opaque items do not type-check. Keep the contracts for the F* extraction only.
#[cfg_attr(not(hax_backend_lean), hax_lib::requires(seed.len() == 32))]
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

#[cfg_attr(not(hax_backend_lean), hax_lib::requires(K <= 4 && A_transpose.len() == K * K))]
#[cfg_attr(not(hax_backend_lean), hax_lib::ensures(|_| future(A_transpose).len() == A_transpose.len()))]
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
        #[cfg(not(hax_backend_lean))]
        hax_lib::loop_invariant!(|_: usize| A_transpose.len() == K * K);
        let mut seeds = [*seed; K];
        for j in 0..K {
            #[cfg(hax)]
            #[cfg(not(hax_backend_lean))]
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
                #[cfg(not(hax_backend_lean))]
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
// Top-level FC (README L7.4, axiom-clean) stated at the Rust level: impl
// `compute_message`, lifted, equals the hacspec `compute_message`. Pre = the
// FC theorem's per-lane bounds (secret ≤ 4095, u ≤ 3328, v ≤ 3328) and K ≤ 4.
#[hax_lib::requires(
    hax_lib::prop::Prop::from_bool(K <= 4)
        .and(vec_bnd(secret_as_ntt, 4095))
        .and(vec_bnd(u_as_ntt, 3328))
        .and(poly_bnd(v, 3328)))]
#[hax_lib::ensures(|_|
    poly_matches(future(result),
        &hacspec_ml_kem::matrix::compute_message(
            &lift_poly(v), &lift_vec(secret_as_ntt), &lift_vec(u_as_ntt))))]
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
// Top-level FC (README L7.3, encrypt): impl `compute_ring_element_v`, lifted, equals
// the hacspec `compute_ring_element_v` on the pk-deserialized `t̂`. Rests on A2
// (deserialization leaf). The cache precondition is NOT the Montgomery
// `cache_post` relation (which has no Rust surface) but the equivalent Rust-stateable
// pair: `vec_slice_bnd(cache)` (the natAbs half) + `cache_matches` (the Montgomery-lift
// half, pinning `cache` to the canonical `compute_cache(r̂)`).
#[hax_lib::requires(
    hax_lib::prop::Prop::from_bool(
        K <= 4
        && public_key.len() == BYTES_PER_RING_ELEMENT * K
        && r_as_ntt.len() == K && cache.len() == K)
        .and(vec_slice_bnd::<Vector, K>(r_as_ntt, 3328))
        .and(vec_slice_bnd::<Vector, K>(cache, 3328))
        .and(poly_bnd(error_2, 3328))
        .and(poly_bnd(message, 3328))
        .and(cache_matches::<K, Vector>(r_as_ntt, cache)))]
#[hax_lib::ensures(|_|
    poly_matches(future(result),
        &hacspec_ml_kem::matrix::compute_ring_element_v::<K>(
            &lift_t_as_ntt_from_public_key::<Vector, K>(public_key),
            &lift_vec_slice::<Vector, K>(r_as_ntt),
            &lift_poly(error_2), &lift_poly(message))))]
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
// Top-level FC (README L7.2, encrypt): impl `compute_vector_u`, lifted, equals the
// hacspec `compute_vector_u` on the seed-sampled matrix. Rests on A1 (sampling leaf).
// Pre = the FC theorem's lengths, `0 < K ≤ 4`, and the bounds `|r| ≤ 3328`,
// `|error_1| ≤ 29439`.
#[hax_lib::requires(
    hax_lib::prop::Prop::from_bool(
        seed.len() == 32 && r_as_ntt.len() == K && error_1.len() == K
        && result.len() == K && cache.len() == K && K > 0 && K <= 4)
        .and(vec_slice_bnd::<Vector, K>(r_as_ntt, 3328))
        .and(vec_slice_bnd::<Vector, K>(error_1, 29439)))]
#[hax_lib::ensures(|_|
    vec_matches::<Vector, K>(future(result),
        &hacspec_ml_kem::matrix::compute_vector_u::<K>(
            &lift_matrix_from_seed::<Vector, Hasher, K>(seed),
            &lift_vec_slice::<Vector, K>(r_as_ntt),
            &lift_vec_slice::<Vector, K>(error_1))))]
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
        #[cfg(not(hax_backend_lean))]
        hax_lib::loop_invariant!(|_: usize| result.len() == K && cache.len() == K);
        sample_matrix_entry::<Vector, Hasher>(matrix_entry, seed, 0, j);
        matrix_entry.accumulating_ntt_multiply_fill_cache(&r_as_ntt[j], accumulator, &mut cache[j]);
    }
    PolynomialRingElement::reducing_from_i32_array(accumulator, &mut result[0]);
    invert_ntt_montgomery::<K, Vector>(&mut result[0], scratch);
    result[0].add_error_reduce(&error_1[0]);

    for i in 1..K {
        #[cfg(hax)]
        #[cfg(not(hax_backend_lean))]
        hax_lib::loop_invariant!(|_: usize| result.len() == K && cache.len() == K);
        *accumulator = [0i32.classify(); 256];
        for j in 0..K {
            #[cfg(hax)]
            #[cfg(not(hax_backend_lean))]
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
// Top-level FC (README L7.1, keygen, axiom-clean) at the Rust level: impl
// `compute_As_plus_e`, lifted, equals the hacspec `compute_As_plus_e`. Pre = the
// FC theorem's bounds (matrix_A ≤ 3328, s ≤ 3328, error ≤ 29439), a zeroed
// accumulator, and 0 < K ≤ 4 with matrix_A a K×K slice.
#[hax_lib::requires(
    hax_lib::prop::Prop::from_bool(K > 0 && K <= 4 && matrix_A.len() == K * K)
        .and(matrix_slice_bnd::<Vector, K>(matrix_A, 3328))
        .and(vec_bnd(s_as_ntt, 3328))
        .and(vec_bnd(error_as_ntt, 29439))
        .and(acc_zero(accumulator)))]
#[hax_lib::ensures(|_|
    vec_matches::<Vector, K>(future(t_as_ntt),
        &hacspec_ml_kem::matrix::compute_As_plus_e::<K>(
            &lift_matrix_from_slice::<Vector, K>(matrix_A),
            &lift_vec(s_as_ntt), &lift_vec(error_as_ntt))))]
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

/// Composed matrix core of K-PKE.Encrypt (spec-only), the L7.3 statement with
/// its cache produced INTERNALLY: `compute_vector_u` fills `cache` (and, as a
/// by-product, establishes it holds the NTT products of `r`), then
/// `compute_ring_element_v` consumes that same `cache`. So there is NO
/// cache-correctness precondition -- it is discharged by the first call. The
/// `#[ensures]` names the hacspec `compute_ring_element_v` on the seed/pk-derived
/// operands; it rests on A1 (the `u` step samples the matrix) and A2 (the `v`
/// step deserializes `t`).
#[hax_lib::requires(
    hax_lib::prop::Prop::from_bool(
        K > 0 && K <= 4 && seed.len() == 32
        && public_key.len() == BYTES_PER_RING_ELEMENT * K
        && r_as_ntt.len() == K && error_1.len() == K
        && result_u.len() == K && cache.len() == K)
        .and(vec_slice_bnd::<Vector, K>(r_as_ntt, 3328))
        .and(vec_slice_bnd::<Vector, K>(error_1, 29439))
        .and(poly_bnd(error_2, 3328))
        .and(poly_bnd(message, 3328)))]
#[hax_lib::ensures(|_|
    poly_matches(future(result_v),
        &hacspec_ml_kem::matrix::compute_ring_element_v::<K>(
            &lift_t_as_ntt_from_public_key::<Vector, K>(public_key),
            &lift_vec_slice::<Vector, K>(r_as_ntt),
            &lift_poly(error_2), &lift_poly(message))))]
#[inline(always)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn compute_u_and_v<const K: usize, Vector: Operations, Hasher: Hash>(
    seed: &[u8],
    public_key: &[u8],
    r_as_ntt: &[PolynomialRingElement<Vector>],
    error_1: &[PolynomialRingElement<Vector>],
    error_2: &PolynomialRingElement<Vector>,
    message: &PolynomialRingElement<Vector>,
    matrix_entry: &mut PolynomialRingElement<Vector>,
    t_as_ntt_entry: &mut PolynomialRingElement<Vector>,
    result_u: &mut [PolynomialRingElement<Vector>],
    result_v: &mut PolynomialRingElement<Vector>,
    scratch: &mut Vector,
    cache: &mut [PolynomialRingElement<Vector>],
    accumulator: &mut [I32; 256],
) {
    compute_vector_u::<K, Vector, Hasher>(
        matrix_entry, seed, r_as_ntt, error_1, result_u, scratch, cache, accumulator,
    );
    compute_ring_element_v::<K, Vector>(
        public_key, t_as_ntt_entry, r_as_ntt, error_2, message, result_v, scratch, cache,
        accumulator,
    );
}
