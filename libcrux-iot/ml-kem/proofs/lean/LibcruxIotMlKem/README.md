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

All four main results are `mvcgen` Triples of the form
`⦃ True ⦄ <impl> ⦃ ⇓ p => ⌜ <hacspec> (lift args…) = .ok (lift p…) ⌝ ⦄`
— i.e. they link the Aeneas-extracted impl to the hacspec spec through a `lift` bridge.
The `lift` bridge accounts for different representations of the input/output data:
The impl uses potentially non-canonical values mod 3329,
stores coefficients in the Montgomery domain, and
stores ring elements as 16 SIMD-shaped chunks of 16 lanes each.
In contrast, the spec uses canonical representations, plain coefficients, 
and a flat array of 256 field elements.

### L7.1 — key generation: `Â · ŝ + ê`

[`Matrix/ComputeAsPlusE.lean`](Matrix/ComputeAsPlusE.lean) — `libcrux_iot_ml_kem.Matrix.ComputeAsPlusE.compute_As_plus_e_fc`:

```lean
⦃ ⌜ True ⌝ ⦄
  libcrux_iot_ml_kem.matrix.compute_As_plus_e
    (vectortraitsOperationsInst := portable_ops_inst)
    t_as_ntt matrix_A s_as_ntt error_as_ntt s_cache accumulator
⦃ ⇓ p => ⌜ hacspec_ml_kem.matrix.compute_As_plus_e
              (lift_matrix_from_slice matrix_A K)
              (lift_vec s_as_ntt) (lift_vec error_as_ntt)
            = .ok (lift_vec p.1) ⌝ ⦄ 
```

The impl's `compute_As_plus_e`, lifted, equals
the hacspec `compute_As_plus_e`. The matrix is read from a **stored**
array, so this theorem is fully
axiom-clean.

### L7.2 — encryption: `Âᵀ · r̂ + ê₁`

[`Matrix/ComputeVectorU/FC.lean`](Matrix/ComputeVectorU/FC.lean) — `libcrux_iot_ml_kem.Matrix.ComputeVectorU.FC.compute_vector_u_fc`:

```lean
⦃ ⌜ True ⌝ ⦄
  libcrux_iot_ml_kem.matrix.compute_vector_u
    K (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst
    matrix_entry seed r_as_ntt error_1 result scratch cache accumulator
⦃ ⇓ p => ⌜ hacspec_ml_kem.matrix.compute_vector_u
              (lift_matrix_from_seed seed K)
              (lift_vec_slice r_as_ntt K)
              (lift_vec_slice error_1 K)
            = .ok (lift_vec_slice p.2.1 K) ⌝ ⦄
```
The impl's `compute_vector_u`, lifted, equals
the hacspec `compute_vector_u`. Here the matrix is
**sampled on the fly** from `seed` (`lift_matrix_from_seed`), so this
theorem is conditional on the matrix-sampling leaf axiom **A1** (see
[Assumptions](#assumptions-trust-boundary)).

### L7.3 — encryption: `t̂ · r̂ + e₂ + Decompress(message)`

[`Matrix/ComputeRingElementV/FC.lean`](Matrix/ComputeRingElementV/FC.lean) — `libcrux_iot_ml_kem.Matrix.ComputeRingElementV.FC.compute_ring_element_v_fc`:

```lean
⦃ ⌜ True ⌝ ⦄
  libcrux_iot_ml_kem.matrix.compute_ring_element_v
    K (vectortraitsOperationsInst := portable_ops_inst)
    public_key t_as_ntt_entry r_as_ntt error_2 message result scratch
    cache accumulator
⦃ ⇓ p => ⌜ hacspec_ml_kem.matrix.compute_ring_element_v
              (lift_t_as_ntt_from_public_key public_key K)
              (lift_vec_slice r_as_ntt K)
              (lift_poly error_2) (lift_poly message)
            = .ok (lift_poly p.2.1) ⌝ ⦄
```

The impl's `compute_ring_element_v`, lifted, equals
the hacspec `compute_ring_element_v`. The first vector `t̂` is **deserialized**
from the public key (`lift_t_as_ntt_from_public_key`), so this theorem
is conditional on the deserialization leaf axiom **A2** (see
[Assumptions](#assumptions-trust-boundary)).

### L7.4 — decryption: `NTT⁻¹(v̂ − ŝ · û)`

[`Matrix/ComputeMessage/FC.lean`](Matrix/ComputeMessage/FC.lean) — `libcrux_iot_ml_kem.Matrix.ComputeMessage.FC.compute_message_fc`:

```lean
⦃ ⌜ True ⌝ ⦄
  libcrux_iot_ml_kem.matrix.compute_message
    (vectortraitsOperationsInst := portable_ops_inst)
    v secret_as_ntt u_as_ntt result scratch accumulator
⦃ ⇓ p => ⌜ hacspec_ml_kem.matrix.compute_message
              (lift_poly v)
              (lift_vec secret_as_ntt) (lift_vec u_as_ntt)
            = .ok (lift_poly p.1) ⌝ ⦄ 
```

The impl's `compute_message`, lifted, equals
the hacspec `compute_message`. All inputs are passed-in polynomials,
so this theorem is fully axiom-clean.

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

Every theorem additionally depends on the two **subslice** axioms **A3/A4**
below (introduced by the hax-mainline re-extraction — see note); they are
listed once here rather than repeated per row.

| Theorem | Standard | Subslice (A3/A4) | Deferred leaf axiom |
|---------|----------|------------------|---------------------|
| L7.1 `Matrix.ComputeAsPlusE.compute_As_plus_e_fc`        | ✓ | ✓ | — |
| L7.2 `Matrix.ComputeVectorU.FC.compute_vector_u_fc`      | ✓ | ✓ | **A1** `Sampling.sample_matrix_entry_fc` (+ the opaque `matrix.sample_matrix_entry`) |
| L7.3 `Matrix.ComputeRingElementV.FC.compute_ring_element_v_fc` | ✓ | ✓ | **A2** `Serialize.deserialize_to_reduced_ring_element_fc` |
| L7.4 `Matrix.ComputeMessage.FC.compute_message_fc`       | ✓ | ✓ | — |

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

### The two subslice axioms (A3 / A4)

Introduced by the migration to mainline hax / the CoreModels v0.2 library
(see [Reproduction](#reproduction)): the Aeneas `Slice.subslice` /
`Array.update_subslice` primitives require a **strict** `start < end` range
and fail on empty ranges. We localize this to two `≤`-range specs, tagged
`AENEAS-SUBSLICE-STRICT` in [`Util/SliceSpecs.lean`](Util/SliceSpecs.lean),
to be discharged once the aeneas primitive is fixed:

- **A3** `libcrux_iot_ml_kem.Util.SliceSpecs.Slice.subslice_le_eq` — reading a
  sub-slice `s[a..b]` for `a ≤ b ≤ s.length` returns `s.val.slice a b`.
- **A4** `libcrux_iot_ml_kem.Util.SliceSpecs.Array.update_subslice_le_eq` —
  writing back a sub-slice over `a ≤ b ≤ length` yields the expected
  `setSlice!`. (The slice-level `Slice.update_subslice_le_eq` is subsumed.)

All four matrix theorems route their range-slice reads/writes through these,
so all four depend on A3/A4.

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
  - Lean 4 toolchain `leanprover/lean4:v4.31.0` (pinned in `lean-toolchain`).
  - The Hax Lean proof-lib `cryspen/hax-lean` tag `v0.3.12` (provides the
    `CoreModels` library; pulled in by the lakefile).
- For extraction:
  - Mainline Hax at rev `4c9e2b7c` (= `cargo-hax-v0.4.0-rc.1`, the Lean/Aeneas
    backend now lives in `cryspen/hax` main; the old `aeneas-lean` backend was
    renamed to `lean`), with the matching **prebuilt** charon/aeneas binaries:
    - Charon `nightly-2026.08.20`
    - Aeneas `nightly-2026.08.24` (commit `f8a0eb8`)
  - Easiest via the flake: `nix develop .#lean` from the repo root provides a
    version-wrapped `cargo hax` @ `4c9e2b7c` + aeneas + cargo.

### Verifying the Lean proof

From `libcrux-iot/ml-kem/proofs/lean/`:

```bash
lake exe cache get   # fetch the mathlib build cache
lake build
```

A clean build reports ~1783 jobs and no errors. Each top-level `*_fc`
theorem carries a `#print axioms` guard (`#guard_msgs`) that fails the build
if the axiom set drifts from the one documented above.

### Cross-spec regression (Rust)

We have a couple of Rust tests in place as a first sanity check that
implementation and specification agree:

```bash
cargo test --tests cross_spec
```

This catches mismatches at the Rust level before they propagate into Lean proof failures.

### Extraction from Rust into Lean

Both `hax_aeneas.py` scripts run `cargo hax into lean` (+ the charon
`--start-from`/`--opaque` bounding and a few post-processing passes); run
them inside the `nix develop .#lean` environment described above:

```bash
# Spec side (from a checkout of cryspen/libcrux):
cd specs/ml-kem/
./hax_aeneas.py

# Impl side:
cd libcrux-iot/ml-kem/
./hax_aeneas.py
```
