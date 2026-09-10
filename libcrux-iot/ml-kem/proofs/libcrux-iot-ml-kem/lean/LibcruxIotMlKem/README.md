# ML-KEM matrix-arithmetic core: impl ↔ spec equivalence

This directory contains the Lean 4 proof that the Rust implementation of
ML-KEM's **matrix-arithmetic core** in `libcrux-iot/ml-kem/src/`
computes the same functions as the hacspec-style specification in
`https://github.com/cryspen/libcrux`. Both sides are auto-extracted via the
`cargo hax into lean` pipeline; this directory then proves their
functional-correctness (FC) equivalence.

The four top-level results are the arithmetic heart of ML-KEM
key-generation, encryption, and decryption: `matrix.compute_As_plus_e`,
`matrix.compute_vector_u`, `matrix.compute_ring_element_v`, and `matrix.compute_message`.
The surrounding glue (XOF expansion, rejection sampling, (de)serialization, compression) is **not** proven
here — see [Assumptions](#assumptions-trust-boundary) for the precise
trust boundary.

## Matrix-level theorems

Each of the four functions carries its specification as a hax contract in the
Rust source ([`src/matrix.rs`](../../../src/matrix.rs)): a `#[requires]` giving
the input bounds and an `#[ensures]` stating that the result, lifted, equals the
hacspec function applied to the lifted inputs. hax turns every contract into a
generated `matrix.<fn>.spec` in [`Extraction/Specs.lean`](Extraction/Specs.lean),
and [`Matrix/SpecDischarge.lean`](Matrix/SpecDischarge.lean) proves each of them
(`<fn>_spec_proof`) at the portable `Vector` instance, on top of the hand-written
functional-correctness (FC) theorem named with each function below.

The contracts use a small vocabulary of spec helpers, defined at the top of
`src/matrix.rs` and mirrored on the Lean side:

- `lift_poly`, `lift_vec`, `lift_vec_slice`, `lift_matrix_from_slice`,
  `lift_matrix_from_seed`, `lift_t_as_ntt_from_public_key` map impl values to
  the spec's representation. The impl uses potentially non-canonical values
  mod 3329, stores coefficients in the Montgomery domain, and stores ring
  elements as 16 SIMD-shaped chunks of 16 lanes each; the spec uses canonical
  representatives, plain coefficients, and a flat array of 256 field elements.
- `poly_matches` / `vec_matches`: an impl polynomial (vector of polynomials),
  lifted, equals the given spec value.
- `poly_bnd`, `vec_bnd`, `vec_slice_bnd`, `matrix_slice_bnd` bound the absolute
  value of every lane; `acc_zero` says the `i32` accumulator is all zeros;
  `cache_matches` ties a precomputed NTT-multiplication cache to its vector.

### L7.1 — key generation: `Â · ŝ + ê`

```rust
#[cfg_attr(hax, hax_lib::requires(
    hax_lib::prop::Prop::from_bool(K > 0 && K <= 4 && matrix_A.len() == K * K)
        .and(matrix_slice_bnd::<Vector, K>(matrix_A, 3328))
        .and(vec_bnd(s_as_ntt, 3328))
        .and(vec_bnd(error_as_ntt, 29439))
        .and(acc_zero(accumulator))))]
#[cfg_attr(hax, hax_lib::ensures(|_|
    vec_matches::<Vector, K>(future(t_as_ntt),
        &hacspec_ml_kem::matrix::compute_As_plus_e::<K>(
            &lift_matrix_from_slice::<Vector, K>(matrix_A),
            &lift_vec(s_as_ntt), &lift_vec(error_as_ntt)))))]
pub(crate) fn compute_As_plus_e<const K: usize, Vector: Operations>(
    t_as_ntt: &mut [PolynomialRingElement<Vector>; K],
    matrix_A: &[PolynomialRingElement<Vector>],
    s_as_ntt: &[PolynomialRingElement<Vector>; K],
    error_as_ntt: &[PolynomialRingElement<Vector>; K],
    s_cache: &mut [PolynomialRingElement<Vector>; K],
    accumulator: &mut [I32; 256],
)
```

The impl's `compute_As_plus_e`, lifted, equals the hacspec `compute_As_plus_e`.
The matrix is read from a **stored** array, so this result is fully axiom-clean.
Discharged by `compute_As_plus_e_spec_proof` on the FC theorem
`Matrix.ComputeAsPlusE.compute_As_plus_e_fc`
([`Matrix/ComputeAsPlusE.lean`](Matrix/ComputeAsPlusE.lean)).

### L7.2 — encryption: `Âᵀ · r̂ + ê₁`

```rust
#[cfg_attr(hax, hax_lib::requires(
    hax_lib::prop::Prop::from_bool(
        seed.len() == 32 && r_as_ntt.len() == K && error_1.len() == K
        && result.len() == K && cache.len() == K && K > 0 && K <= 4)
        .and(vec_slice_bnd::<Vector, K>(r_as_ntt, 3328))
        .and(vec_slice_bnd::<Vector, K>(error_1, 29439))))]
#[cfg_attr(hax, hax_lib::ensures(|_|
    vec_matches::<Vector, K>(future(result),
        &hacspec_ml_kem::matrix::compute_vector_u::<K>(
            &lift_matrix_from_seed::<Vector, Hasher, K>(seed),
            &lift_vec_slice::<Vector, K>(r_as_ntt),
            &lift_vec_slice::<Vector, K>(error_1)))))]
pub(crate) fn compute_vector_u<const K: usize, Vector: Operations, Hasher: Hash>(
    matrix_entry: &mut PolynomialRingElement<Vector>,
    seed: &[u8],
    r_as_ntt: &[PolynomialRingElement<Vector>],
    error_1: &[PolynomialRingElement<Vector>],
    result: &mut [PolynomialRingElement<Vector>],
    scratch: &mut Vector,
    cache: &mut [PolynomialRingElement<Vector>],
    accumulator: &mut [I32; 256],
)
```

The impl's `compute_vector_u`, lifted, equals the hacspec `compute_vector_u`.
Here the matrix is **sampled on the fly** from `seed` (`lift_matrix_from_seed`),
so this result is conditional on the matrix-sampling leaf axiom **A1** (see
[Assumptions](#assumptions-trust-boundary)). Discharged by
`compute_vector_u_spec_proof` on the FC theorem
`Matrix.ComputeVectorU.FC.compute_vector_u_fc`
([`Matrix/ComputeVectorU/FC.lean`](Matrix/ComputeVectorU/FC.lean)).

### L7.3 — encryption: `t̂ · r̂ + e₂ + Decompress(message)`

```rust
#[cfg_attr(hax, hax_lib::requires(
    hax_lib::prop::Prop::from_bool(
        K <= 4
        && public_key.len() == BYTES_PER_RING_ELEMENT * K
        && r_as_ntt.len() == K && cache.len() == K)
        .and(vec_slice_bnd::<Vector, K>(r_as_ntt, 3328))
        .and(vec_slice_bnd::<Vector, K>(cache, 3328))
        .and(poly_bnd(error_2, 3328))
        .and(poly_bnd(message, 3328))
        .and(cache_matches::<K, Vector>(r_as_ntt, cache))))]
#[cfg_attr(hax, hax_lib::ensures(|_|
    poly_matches(future(result),
        &hacspec_ml_kem::matrix::compute_ring_element_v::<K>(
            &lift_t_as_ntt_from_public_key::<Vector, K>(public_key),
            &lift_vec_slice::<Vector, K>(r_as_ntt),
            &lift_poly(error_2), &lift_poly(message)))))]
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
)
```

The impl's `compute_ring_element_v`, lifted, equals the hacspec
`compute_ring_element_v`. The function consumes the NTT-multiplication cache that
`compute_vector_u` filled, so its contract requires `cache_matches` (the cache is
the canonical one for `r_as_ntt`). The first vector `t̂` is **deserialized** from
the public key (`lift_t_as_ntt_from_public_key`), so this result is conditional
on the deserialization leaf axiom **A2** (see
[Assumptions](#assumptions-trust-boundary)). Discharged by
`compute_ring_element_v_spec_proof` on the FC theorem
`Matrix.ComputeRingElementV.FC.compute_ring_element_v_fc`
([`Matrix/ComputeRingElementV/FC.lean`](Matrix/ComputeRingElementV/FC.lean)).

### L7.4 — decryption: `NTT⁻¹(v̂ − ŝ · û)`

```rust
#[cfg_attr(hax, hax_lib::requires(
    hax_lib::prop::Prop::from_bool(K <= 4)
        .and(vec_bnd(secret_as_ntt, 4095))
        .and(vec_bnd(u_as_ntt, 3328))
        .and(poly_bnd(v, 3328))))]
#[cfg_attr(hax, hax_lib::ensures(|_|
    poly_matches(future(result),
        &hacspec_ml_kem::matrix::compute_message(
            &lift_poly(v), &lift_vec(secret_as_ntt), &lift_vec(u_as_ntt)))))]
pub(crate) fn compute_message<const K: usize, Vector: Operations>(
    v: &PolynomialRingElement<Vector>,
    secret_as_ntt: &[PolynomialRingElement<Vector>; K],
    u_as_ntt: &[PolynomialRingElement<Vector>; K],
    result: &mut PolynomialRingElement<Vector>,
    scratch: &mut Vector,
    accumulator: &mut [I32; 256],
)
```

The impl's `compute_message`, lifted, equals the hacspec `compute_message`. All
inputs are passed-in polynomials, so this result is fully axiom-clean.
Discharged by `compute_message_spec_proof` on the FC theorem
`Matrix.ComputeMessage.FC.compute_message_fc`
([`Matrix/ComputeMessage/FC.lean`](Matrix/ComputeMessage/FC.lean)).

### Composed encryption: `compute_u_and_v`

The encryption path in `ind_cpa` calls L7.2 and L7.3 back to back through
`compute_u_and_v`, which fills the cache itself. Its contract therefore needs no
`cache_matches` hypothesis and states L7.3's conclusion for `result_v`:

```rust
#[cfg_attr(hax, hax_lib::requires(
    hax_lib::prop::Prop::from_bool(
        K > 0 && K <= 4 && seed.len() == 32
        && public_key.len() == BYTES_PER_RING_ELEMENT * K
        && r_as_ntt.len() == K && error_1.len() == K
        && result_u.len() == K && cache.len() == K)
        .and(vec_slice_bnd::<Vector, K>(r_as_ntt, 3328))
        .and(vec_slice_bnd::<Vector, K>(error_1, 29439))
        .and(poly_bnd(error_2, 3328))
        .and(poly_bnd(message, 3328))))]
#[cfg_attr(hax, hax_lib::ensures(|_|
    poly_matches(future(result_v),
        &hacspec_ml_kem::matrix::compute_ring_element_v::<K>(
            &lift_t_as_ntt_from_public_key::<Vector, K>(public_key),
            &lift_vec_slice::<Vector, K>(r_as_ntt),
            &lift_poly(error_2), &lift_poly(message)))))]
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
)
```

Discharged by `compute_u_and_v_spec_proof`, which chains the L7.2 result (it
establishes `cache_matches` for the cache `compute_vector_u` leaves behind) into
the L7.3 result; it inherits both leaf axioms **A1** and **A2**.

## Polynomial-level theorems

The four matrix-level theorems above are assembled from a stack of
**polynomial-level** FC theorems — each over a single ring element
(`PolynomialRingElement` = 256 coefficients) — stated and proven in
the files listed below. Unlike L7.2/L7.3, **none** of these depend on
non-standard axioms.

The polynomial-level theorems **do not use the hacspec implementation**
but use a pure Lean reference that reimplements the hacspec functions.

### Number-theoretic transform operations

| Theorem | impl function | what it does |
|---------|---------------|--------------|
| `libcrux_iot_ml_kem.Ntt.ntt_binomially_sampled_ring_element_fc` ([`Ntt.lean`](Ntt.lean)) | `ntt.ntt_binomially_sampled_ring_element` | forward NTT |
| `libcrux_iot_ml_kem.InvertNtt.invert_ntt_montgomery_fc` ([`InvertNtt.lean`](InvertNtt.lean)) | `invert_ntt.invert_ntt_montgomery` | inverse NTT |
| `libcrux_iot_ml_kem.Polynomial.NttMultiply.accumulating_ntt_multiply_fc` ([`Polynomial/NttMultiply.lean`](Polynomial/NttMultiply.lean)) | `vector.portable.ntt.accumulating_ntt_multiply` | pointwise NTT multiplication |

### Reduction, error, and message combination

The poly-level arithmetic that finishes each ML-KEM step.

| Theorem | impl function | what it does |
|---------|-----------|--------------|
| `libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett.poly_barrett_reduce_fc` ([`Polynomial/PolyOpsFcBarrett.lean`](Polynomial/PolyOpsFcBarrett.lean)) | `polynomial.PolynomialRingElement.poly_barrett_reduce`               | Barrett-reduce all 256 lanes to canonical residues |
| `libcrux_iot_ml_kem.Polynomial.PolyOpsFc.poly_reducing_from_i32_array_fc` ([`Polynomial/PolyOpsFc.lean`](Polynomial/PolyOpsFc.lean)) | `polynomial.PolynomialRingElement.reducing_from_i32_array` | Montgomery-reduce an `i32[256]` accumulator into a ring element |
| `libcrux_iot_ml_kem.Polynomial.PolyOpsFc.subtract_reduce_fc` ([`Polynomial/PolyOpsFc.lean`](Polynomial/PolyOpsFc.lean)) | `polynomial.PolynomialRingElement.subtract_reduce`              | subtract two ring elements, then Barrett-reduce (decryption tail, L7.4) |
| `libcrux_iot_ml_kem.Polynomial.PolyOpsFc.add_error_reduce_fc` ([`Polynomial/PolyOpsFc.lean`](Polynomial/PolyOpsFc.lean)) | `polynomial.PolynomialRingElement.add_error_reduce`             | add an error polynomial (impl's `1441`-Montgomery multiply), Barrett-reduce |
| `libcrux_iot_ml_kem.Polynomial.PolyOpsFc.add_standard_error_reduce_fc` ([`Polynomial/PolyOpsFc.lean`](Polynomial/PolyOpsFc.lean)) | `polynomial.PolynomialRingElement.add_standard_error_reduce`    | add a standard error polynomial (`R`-Montgomery multiply), Barrett-reduce (keygen tail) |
| `libcrux_iot_ml_kem.Polynomial.PolyOpsFc.add_message_error_reduce_fc` ([`Polynomial/PolyOpsFc.lean`](Polynomial/PolyOpsFc.lean)) | `polynomial.PolynomialRingElement.add_message_error_reduce`     | add error + message to the (`1441`-multiplied) result, Barrett-reduce (L7.3 tail) |

## Assumptions (trust boundary)

The four matrix-arithmetic theorems above are **complete proofs** modulo
the assumptions below. Read this section as the precise statement of what
is *trusted* rather than *proven*.

### Standard Lean axioms

Every theorem depends on Lean's three standard axioms: `propext`,
`Classical.choice`, `Quot.sound`.

### Per-theorem axiom status

The two **subslice** axioms **A3/A4** that every theorem used to carry are
**gone** as of the hax v0.4.0-rc.1 / aeneas nightly-2026.08.24 migration — see
[the note below](#the-two-former-subslice-axioms-a3--a4). The `Subslice` column
is retained only to record that it is now discharged everywhere.

| Theorem | Standard | Subslice (A3/A4) | Deferred leaf axiom |
|---------|----------|------------------|---------------------|
| L7.1 `Matrix.ComputeAsPlusE.compute_As_plus_e_fc`        | ✓ | discharged | — |
| L7.2 `Matrix.ComputeVectorU.FC.compute_vector_u_fc`      | ✓ | discharged | **A1** `Sampling.sample_matrix_entry_fc` (+ the opaque `matrix.sample_matrix_entry`) |
| L7.3 `Matrix.ComputeRingElementV.FC.compute_ring_element_v_fc` | ✓ | discharged | **A2** `Serialize.deserialize_to_reduced_ring_element_fc` |
| L7.4 `Matrix.ComputeMessage.FC.compute_message_fc`       | ✓ | discharged | — |

### The two deferred-leaf axioms (A1 / A2)

- **A1** `libcrux_iot_ml_kem.Sampling.sample_matrix_entry_fc` (stated in
  [`Sampling.lean`](Sampling.lean)) — characterizes one on-the-fly matrix
  entry: running the impl's XOF + rejection-sampling chain on `(seed, i, j)`
  produces the `(i, j)` entry of `lift_matrix_from_seed seed K` (row-major),
  with every coefficient in `[0, 3328]`. The impl entry-point
  `matrix.sample_matrix_entry` is itself an **opaque** function (the XOF/PRF
  internals are outside the extraction), so it also appears as an axiom.

- **A2** `libcrux_iot_ml_kem.Serialize.deserialize_to_reduced_ring_element_fc`
  (stated in [`Serialize.lean`](Serialize.lean)) — characterizes one
  384-byte public-key chunk: running the impl's 16-iteration
  `deserialize_12 + cond_subtract_3329` loop on chunk `i` produces
  `(lift_t_as_ntt_from_public_key public_key K).val[i]!`, coefficients in
  `[0, 3328]`. 
  
These are largly orthogonal to the matrix arithmetic,
which is why we omitted its verification.

### The two former subslice axioms (A3 / A4)

**Resolved by the hax v0.4.0-rc.1 migration — no longer axioms.**

The migration to mainline hax / the CoreModels v0.2 library introduced these:
Aeneas's `Slice.subslice` / `Array.update_subslice` primitives required a
**strict** `start < end` range and failed on empty ranges, whereas Rust's
`&xs[i..i]` is a valid empty slice. The intended `≤` behaviour was localized to
two `≤`-range specs tagged `AENEAS-SUBSLICE-STRICT` and *axiomatized*, to be
discharged once the aeneas primitive was fixed:

- **A3** `libcrux_iot_ml_kem.Util.SliceSpecs.Slice.subslice_le_eq` — reading a
  sub-slice `s[a..b]` for `a ≤ b ≤ s.length` returns `s.val.slice a b`.
- **A4** `libcrux_iot_ml_kem.Util.SliceSpecs.Array.update_subslice_le_eq` —
  writing back a sub-slice over `a ≤ b ≤ length` yields the expected
  `setSlice!`. (The slice-level `Slice.update_subslice_le_eq` is subsumed.)

As of aeneas nightly-2026.08.24 all three primitives guard on `start ≤ end`, so
the aeneas primitive **is** fixed and all three statements are now **theorems**
proved directly from the definitions (`if_pos`/`dif_pos` + `rfl`), kept verbatim
in [`Util/SliceSpecs.lean`](Util/SliceSpecs.lean) so no use site changed. All
four matrix theorems still route their range-slice reads/writes through them and
now depend on nothing beyond the three standard axioms plus their own deferred
leaf.

This also closes a **soundness** gap, not merely a bookkeeping one. While the old
model was strict, A3 asserted success exactly where the definition failed, so
`False` was derivable from A3 at `s = ⟨[], _⟩`, `r = ⟨0,0⟩` (the r3 review
kernel-checked this, then removed the witness). Because
`core_models_Slice_Insts_index_RangeUsize_spec` and its `index_mut` sibling are
`@[spec]`-tagged, `hax_mvcgen` selected the refutable axiom automatically on any
slice-range subscript, so the exposure was every row whose recorded axiom list
mentioned them — which is why the reviews leaned on an axiom allowlist. With A3/A4
discharged against the real definitions that exposure is gone: there is no longer
an inconsistent axiom in the development to inherit.

## Proof architecture

### The lift bridge

The impl works over `PortableVector`-backed `i16`/`i32` coefficients in
the (signed, possibly non-canonical) **Montgomery** domain; the hacspec
works over `parameters.FieldElement` (a `u16` wrapping `ZMod 3329`). The
lift family (in [`Spec/Lift.lean`](Spec/Lift.lean), namespace
`libcrux_iot_ml_kem.Spec.Lift`) maps impl values to canonical spec values.

### Hierarchy (L0 → L7)

The proof is structured into layers L0 to L7:

| Layer | Content |
|-------|---------|
| **L0** | field-element arithmetic (`add`/`sub`/`mul`/`barrett`-reduce in `ZMod 3329`) |
| **L1** | per-vector-element ops (the `PortableVector` lane primitives) |
| **L2** | NTT butterfly layer steps (forward + inverse) |
| **L3** | NTT drivers (full forward/inverse NTT over the 7 layers) |
| **L4** | [*not verified*: sampling / compression] |
| **L5** | [*not verified*: (de)serialization] |
| **L6** | poly-level ops: barrett-reduce, subtract-reduce, add-error-reduce, add-message-error-reduce, reducing-from-`i32`-array |
| **L7** | the matrix-level targets above |


## Reproduction

### Prerequisites

- For running the proofs:
  - [Lean](https://lean-lang.org/install/)
- For extraction:
  - [cargo](https://rust-lang.org/tools/install/)
  - [cargo-binstall](https://github.com/cargo-bins/cargo-binstall#installation)
  - (hax, charon, aeneas will be downloaded automatically)

### Building

From `libcrux-iot/ml-kem/proofs/libcrux-iot-ml-kem/lean`:

```bash
lake exe cache get        # downloading the Mathlib cache
lake build                # building the project
```

A clean build reports ~1806 jobs and no errors. The `#guard_msgs` axiom guards
fail the build if the axiom set drifts from the one documented above.

### Cross-spec regression (Rust)

We have a couple of Rust tests in place as a first sanity check that
implementation and specification agree:

```bash
cargo test --test cross_spec              # 15 tests, KeyGen/Encaps/Decaps at all three sizes
cargo test --test cross_spec_proptests    # the same surface, property-based (slower)
```

This catches mismatches at the Rust level before they propagate into Lean proof failures.

### Extraction from Rust into Lean

The impl side needs the residual fix-ups in `libcrux-iot/hax_mlkem.py` on top
of its scenario: the pipeline drops trait-clause instance arguments at some
generated call sites, and that script re-inserts them (its docstring lists
them exactly).

```bash
# Spec side (from a checkout of cryspen/libcrux):
cd specs
cargo hax extract hacspec-ml-kem

# Impl side:
cd libcrux-iot
./hax_mlkem.py            # = `cargo hax extract libcrux-iot-ml-kem` + fix-ups
```
