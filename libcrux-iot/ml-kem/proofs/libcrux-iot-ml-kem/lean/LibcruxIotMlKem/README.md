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

Each of the four functions has its functional correctness stated and proven on
the Lean side, as the `*_fc` theorem named with the function below: the impl's
result, lifted, equals the hacspec function applied to the lifted inputs, at the
portable `Vector` instance. The Rust source ([`src/matrix.rs`](../../../../src/matrix.rs))
carries only the length and bound `#[requires]` these functions need, not the
correctness statement.

The lifts that relate the two representations live on the Lean side, in
[`Spec/Lift.lean`](Spec/Lift.lean): the impl uses potentially non-canonical
values mod 3329, stores coefficients in the Montgomery domain, and stores ring
elements as 16 SIMD-shaped chunks of 16 lanes each, whereas the spec uses
canonical representatives, plain coefficients, and a flat array of 256 field
elements.

### L7.1 — key generation: `Â · ŝ + ê`

The impl's `compute_As_plus_e`, lifted, equals the hacspec `compute_As_plus_e`.
The matrix is read from a **stored** array, so this result is fully axiom-clean.
Stated and proven as `Matrix.ComputeAsPlusE.compute_As_plus_e_fc`
([`Matrix/ComputeAsPlusE.lean`](Matrix/ComputeAsPlusE.lean)).

### L7.2 — encryption: `Âᵀ · r̂ + ê₁`

The impl's `compute_vector_u`, lifted, equals the hacspec `compute_vector_u`.
Here the matrix is **sampled on the fly** from `seed` (`lift_matrix_from_seed`),
so this result is conditional on the matrix-sampling leaf axiom **A1** (see
[Assumptions](#assumptions-trust-boundary)). Stated and proven as
`Matrix.ComputeVectorU.FC.compute_vector_u_fc`
([`Matrix/ComputeVectorU/FC.lean`](Matrix/ComputeVectorU/FC.lean)).

### L7.3 — encryption: `t̂ · r̂ + e₂ + Decompress(message)`

The impl's `compute_ring_element_v`, lifted, equals the hacspec
`compute_ring_element_v`. The function consumes the NTT-multiplication cache that
`compute_vector_u` filled, so the theorem assumes the cache is the canonical one
for `r_as_ntt`. The first vector `t̂` is **deserialized** from
the public key (`lift_t_as_ntt_from_public_key`), so this result is conditional
on the deserialization leaf axiom **A2** (see
[Assumptions](#assumptions-trust-boundary)). Stated and proven as
`Matrix.ComputeRingElementV.FC.compute_ring_element_v_fc`
([`Matrix/ComputeRingElementV/FC.lean`](Matrix/ComputeRingElementV/FC.lean)).

### L7.4 — decryption: `NTT⁻¹(v̂ − ŝ · û)`

The impl's `compute_message`, lifted, equals the hacspec `compute_message`. All
inputs are passed-in polynomials, so this result is fully axiom-clean.
Stated and proven as `Matrix.ComputeMessage.FC.compute_message_fc`
([`Matrix/ComputeMessage/FC.lean`](Matrix/ComputeMessage/FC.lean)).

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

Beyond those, each theorem depends only on its own deferred leaf axiom, if any:

| Theorem | Standard | Deferred leaf axiom |
|---------|----------|---------------------|
| L7.1 `Matrix.ComputeAsPlusE.compute_As_plus_e_fc`        | ✓ | — |
| L7.2 `Matrix.ComputeVectorU.FC.compute_vector_u_fc`      | ✓ | **A1** `Sampling.sample_matrix_entry_fc` (+ the opaque `matrix.sample_matrix_entry`) |
| L7.3 `Matrix.ComputeRingElementV.FC.compute_ring_element_v_fc` | ✓ | **A2** `Serialize.deserialize_to_reduced_ring_element_fc` |
| L7.4 `Matrix.ComputeMessage.FC.compute_message_fc`       | ✓ | — |

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
