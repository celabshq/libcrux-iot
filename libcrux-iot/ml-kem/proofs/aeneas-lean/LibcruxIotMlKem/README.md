# ML-KEM matrix-arithmetic core: impl ↔ spec equivalence

This directory contains the Lean 4 proof that the Rust implementation of
ML-KEM's **matrix-arithmetic core** in `libcrux-iot/ml-kem/src/`
computes the same functions as the hacspec-style specification in
`https://github.com/cryspen/libcrux`. Both sides are auto-extracted via the
`cargo hax into aeneas-lean` pipeline; this directory then proves their
functional-correctness (FC) equivalence.

The four top-level results are the arithmetic heart of ML-KEM
key-generation, encryption, and decryption: `matrix.compute_As_plus_e`,
`matrix.compute_vector_u`, `matrix.compute_ring_element_v`, and `matrix.compute_message`.
The surrounding glue (XOF expansion, rejection sampling, (de)serialization, compression) is **not** proven
here — see [Assumptions](#assumptions-trust-boundary) for the precise
trust boundary.

## Matrix-level theorems

All four main results are `mvcgen` Triples of the form
`⦃ True ⦄ <impl> ⦃ ⇓ p => ⌜ ∃ spec_out, <hacspec> (lift args…) = .ok spec_out ∧ <output p relates to spec_out> ⌝ ⦄`
— i.e. they link the Aeneas-extracted impl to the hacspec spec through a `lift`
bridge **on the inputs**, while the output side is stated by a single shared
predicate — `VecMatches impl spec` for the vector results (L7.1, L7.2) and
`PolyMatches impl spec` for the single-polynomial results (L7.3, L7.4). Both reduce
to a per-lane `LaneMatches x f`: each impl output lane `x` is the **unique centered
Barrett representative** of the spec residue — `|x| ≤ 1664 = ⌊q/2⌋` **and**
`(x : ZMod q) = f` (see [The lift bridge](#the-lift-bridge)).
The `lift` bridge accounts for different representations of the input/output data:
The impl uses potentially non-canonical values mod 3329,
stores coefficients in the Montgomery domain, and
stores ring elements as 16 SIMD-shaped chunks of 16 lanes each.
In contrast, the spec uses canonical representations, plain coefficients, 
and a flat array of 256 field elements.

The code blocks below show only the Hoare triple (the precondition really is
`True`); each theorem additionally carries input **hypotheses**, elided here,
that the equivalence is conditional on. In brief: every impl input coefficient
is bounded (`|·| ≤ 3328`, relaxed to `≤ 29439` for the additive error terms),
the rank `K ≤ 4`, the input slices/arrays have their expected lengths, and the
`i32` accumulator starts zeroed. These pin the impl inputs to the range the
arithmetic is designed for; the spec side is unconstrained.

### L7.1 — key generation: `Â · ŝ + ê`

[`Matrix/ComputeAsPlusE.lean`](Matrix/ComputeAsPlusE.lean) — `libcrux_iot_ml_kem.Matrix.ComputeAsPlusE.compute_As_plus_e_fc`:

```lean
⦃ ⌜ True ⌝ ⦄
  libcrux_iot_ml_kem.matrix.compute_As_plus_e
    (vectortraitsOperationsInst := portable_ops_inst)
    t_as_ntt matrix_A s_as_ntt error_as_ntt s_cache accumulator
⦃ ⇓ p => ⌜ ∃ spec_out,
              hacspec_ml_kem.matrix.compute_As_plus_e
                (lift_matrix_from_slice matrix_A K)
                (lift_vec s_as_ntt) (lift_vec error_as_ntt) = .ok spec_out
            ∧ VecMatches p.1.val spec_out ⌝ ⦄
```

The impl's `compute_As_plus_e` inputs are lifted into the hacspec spec, and the
spec output `spec_out` is related to the impl output via `VecMatches`: each impl
coefficient `x` is the **unique centered Barrett representative** of the spec
residue — `|x| ≤ 1664 = ⌊q/2⌋` (a *complete* residue system of exactly `q` values,
so the representative is pinned uniquely) **and** `(x : ZMod q) = <spec lane>`,
the residue equality stated directly in `ZMod q`. The `≤ 1664` bound is threaded up
from `barrett_reduce_fc`. The matrix is read from a **stored** array, so this
theorem is fully axiom-clean.

### L7.2 — encryption: `Âᵀ · r̂ + ê₁`

[`Matrix/ComputeVectorU/FC.lean`](Matrix/ComputeVectorU/FC.lean) — `libcrux_iot_ml_kem.Matrix.ComputeVectorU.FC.compute_vector_u_fc`:

```lean
⦃ ⌜ True ⌝ ⦄
  libcrux_iot_ml_kem.matrix.compute_vector_u
    K (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst
    matrix_entry seed r_as_ntt error_1 result scratch cache accumulator
⦃ ⇓ p => ⌜ ∃ spec_out,
              hacspec_ml_kem.matrix.compute_vector_u
                (lift_matrix_from_seed seed K)
                (lift_vec_slice r_as_ntt K)
                (lift_vec_slice error_1 K)
              = .ok spec_out
            ∧ VecMatches p.2.1.val spec_out ⌝ ⦄
```
The impl's `compute_vector_u` inputs are lifted into the hacspec spec, and the
spec output `spec_out` is related to the impl output via `VecMatches` — the same
centered-representative form as L7.1: each impl lane `x` satisfies `|x| ≤ 1664`
(the unique centered Barrett representative) **and** `(x : ZMod q) = <spec lane>`.
Here the matrix is **sampled on the fly** from `seed` (`lift_matrix_from_seed`),
so this theorem is conditional on the matrix-sampling leaf axiom **A1** (see
[Assumptions](#assumptions-trust-boundary)).

### L7.3 — encryption: `t̂ · r̂ + e₂ + Decompress(message)`

[`Matrix/ComputeRingElementV/FC.lean`](Matrix/ComputeRingElementV/FC.lean) — `libcrux_iot_ml_kem.Matrix.ComputeRingElementV.FC.compute_ring_element_v_fc`:

```lean
⦃ ⌜ True ⌝ ⦄
  libcrux_iot_ml_kem.matrix.compute_ring_element_v
    K (vectortraitsOperationsInst := portable_ops_inst)
    public_key t_as_ntt_entry r_as_ntt error_2 message result scratch
    cache accumulator
⦃ ⇓ p => ⌜ ∃ spec_out,
              hacspec_ml_kem.matrix.compute_ring_element_v
                (lift_t_as_ntt_from_public_key public_key K)
                (lift_vec_slice r_as_ntt K)
                (lift_poly error_2) (lift_poly message)
              = .ok spec_out
            ∧ PolyMatches p.2.1 spec_out ⌝ ⦄
```

The impl's `compute_ring_element_v` inputs are lifted into the hacspec spec, and
the spec output `spec_out` is related to the impl output via `PolyMatches`
(centered-representative form; `|x| ≤ 1664` **and** `(x : ZMod q) = <spec lane>`).
The first vector `t̂` is **deserialized** from the public key
(`lift_t_as_ntt_from_public_key`), so this theorem is conditional on the
deserialization leaf axiom **A2** (see [Assumptions](#assumptions-trust-boundary)).

### L7.4 — decryption: `NTT⁻¹(v̂ − ŝ · û)`

[`Matrix/ComputeMessage/FC.lean`](Matrix/ComputeMessage/FC.lean) — `libcrux_iot_ml_kem.Matrix.ComputeMessage.FC.compute_message_fc`:

```lean
⦃ ⌜ True ⌝ ⦄
  libcrux_iot_ml_kem.matrix.compute_message
    (vectortraitsOperationsInst := portable_ops_inst)
    v secret_as_ntt u_as_ntt result scratch accumulator
⦃ ⇓ p => ⌜ ∃ spec_out,
              hacspec_ml_kem.matrix.compute_message
                (lift_poly v)
                (lift_vec secret_as_ntt) (lift_vec u_as_ntt)
              = .ok spec_out
            ∧ PolyMatches p.1 spec_out ⌝ ⦄
```

The impl's `compute_message` inputs are lifted into the hacspec spec, and the
spec output `spec_out` is related to the impl output via `PolyMatches`
(centered-representative form; `|x| ≤ 1664` **and** `(x : ZMod q) = <spec lane>`).
All inputs are passed-in polynomials, so this theorem is fully axiom-clean.

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
| `libcrux_iot_ml_kem.InvertNtt.invert_ntt_montgomery_fc` ([`InvertNtt.lean`](InvertNtt.lean)) | `invert_ntt.invert_ntt_montgomery` | inverse NTT |
| `libcrux_iot_ml_kem.Polynomial.NttMultiply.accumulating_ntt_multiply_fc` ([`Polynomial/NttMultiply.lean`](Polynomial/NttMultiply.lean)) | `vector.portable.ntt.accumulating_ntt_multiply` | pointwise NTT multiplication |

### Standalone leaf theorems (not consumed by the matrix theorems)

The theorem below is proven at the polynomial level but is **not** used by any
of the four matrix-level theorems above. The matrix operations take their
vector inputs already in the NTT domain (`r_as_ntt`, `t_as_ntt`, etc.); the
forward NTT of freshly binomially-sampled secret/error polynomials happens one
level up, in key generation / encapsulation, *before* the matrix multiply. It
is a proven leaf awaiting that (not-yet-present) keygen/encaps layer.

| Theorem | impl function | what it does |
|---------|---------------|--------------|
| `libcrux_iot_ml_kem.Ntt.ntt_binomially_sampled_ring_element_fc` ([`Ntt.lean`](Ntt.lean)) | `ntt.ntt_binomially_sampled_ring_element` | forward NTT |

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

| Theorem | Standard | Leaf axiom |
|---------|----------|------------|
| L7.1 `Matrix.ComputeAsPlusE.compute_As_plus_e_fc`        | ✓ | — (fully clean) |
| L7.2 `Matrix.ComputeVectorU.FC.compute_vector_u_fc`      | ✓ | **A1** `Sampling.sample_matrix_entry_fc` |
| L7.3 `Matrix.ComputeRingElementV.FC.compute_ring_element_v_fc` | ✓ | **A2** `Serialize.deserialize_to_reduced_ring_element_fc` |
| L7.4 `Matrix.ComputeMessage.FC.compute_message_fc`       | ✓ | — (fully clean) |

Each row is **pinned in the source and checked on every build**: the FC file
for each theorem ends with a `#guard_msgs in` / `#print axioms` block, so the
build fails if a theorem's axiom dependencies ever change (a stray `sorry` or a
new leaf axiom creeping in). You can reproduce any row manually with
`#print axioms <theorem>`.

### The two deferred-leaf axioms (A1 / A2)

- **A1** `libcrux_iot_ml_kem.Sampling.sample_matrix_entry_fc` (stated in
  [`Sampling.lean`](Sampling.lean)) — characterizes one on-the-fly matrix
  entry: running the impl's XOF + rejection-sampling chain on `(seed, i, j)`
  produces the `(i, j)` entry of `lift_matrix_from_seed seed K` (row-major),
  with every coefficient in `[0, 3328]`.

- **A2** `libcrux_iot_ml_kem.Serialize.deserialize_to_reduced_ring_element_fc`
  (stated in [`Serialize.lean`](Serialize.lean)) — characterizes one
  384-byte public-key chunk: running the impl's 16-iteration
  `deserialize_12 + cond_subtract_3329` loop on chunk `i` produces
  `(lift_t_as_ntt_from_public_key public_key K).val[i]!`, coefficients in
  `[0, 3328]`. 
  
These are largely orthogonal to the matrix arithmetic,
which is why we omitted its verification.

## Proof architecture

### The lift bridge

The impl works over `PortableVector`-backed `i16`/`i32` coefficients in
the (signed, possibly non-canonical) **Montgomery** domain; the hacspec
works over `parameters.FieldElement` (a `u16` wrapping `ZMod 3329`). The
lift family (in [`Spec/Lift.lean`](Spec/Lift.lean), namespace
`libcrux_iot_ml_kem.Spec.Lift`) maps impl values to canonical spec values.

All four L7 POSTs lift their *inputs* into the spec (unavoidable — the hacspec is
typed in `FieldElement`), so each is only as strong as `lift` is
information-preserving on those inputs. **The `lift_*` definitions are therefore
the primary object of the audit.** They are short and direct, so the reviewer's
first task is to read the `lift_*` bodies in [`Spec/Lift.lean`](Spec/Lift.lean)
and confirm each one carries the impl coefficients over to the spec
coefficient-by-coefficient, without collapsing or discarding information.

The `§Audit` section at the end of [`Spec/Lift.lean`](Spec/Lift.lean) supports
that reading with two lemmas about the lift itself: it is **faithful**
(`lift_fe_spec`: projecting a lifted lane back yields the impl lane mod
`q = 3329`) and **injective up to `q`** (`lift_fe_inj_mod`: a constant/collapsing
lift is impossible), both lifted up the tower to `lift_poly_*`, `lift_vec_*`, and
`lift_matrix_from_slice_*`. These lemma statements are a confidence check on the
definitions, not a replacement for reading them. (The input lift equates residue
classes mod `q`; it deliberately does not constrain the concrete i16
representative — see the trust boundary.)

**The output-match predicates — all four L7 POSTs.** Rather than an equation
*through* `lift` on the output side, each POST relates the impl output to the spec
via one shared predicate family (all defined in [`Spec/Lift.lean`](Spec/Lift.lean)):

- `LaneMatches x f := x.natAbs ≤ 1664 ∧ (x : ZMod q) = f` — one impl lane vs one
  spec residue;
- `PolyMatches impl spec := ∀ ℓ < 256, LaneMatches (impl lane ℓ) (zmodOfFE (spec.val[ℓ]!))`
  — a ring element (L7.3, L7.4);
- `VecMatches impl spec := ∀ r < K, PolyMatches (impl row r) (spec.val[r]!)`
  — a vector of ring elements (L7.1, L7.2).

Reading `VecMatches p spec_out` (or `PolyMatches`) *is* the equivalence: every impl
output lane is the centered Barrett representative of the corresponding spec
residue. Two guarantees fall out of `LaneMatches`:

- **Uniqueness.** `|x| ≤ 1664 = ⌊q/2⌋` is the *centered* Barrett range — a
  complete residue system of exactly `q = 3329` values — so the residue class
  together with the bound pins the representative `x` uniquely.
- **`ZMod q` residue.** The residue equality is stated directly in `ZMod q`, with
  no `.toNat` and no sign correction on the output.

The `≤ 1664` bound is the output bound of Barrett reduction, proven once in
`barrett_reduce_core` (the pure-`Int` core) and carried by the `barrett_reduce`
spec chain (`barrett_reduce_element_spec` → `barrett_reduce_spec` →
`barrett_reduce_fc`) — the NTT butterfly layers, which only need looseness, weaken
it to `≤ 3328` at their call sites. It threads through the tail poly-level op
(`add_standard_error_reduce_fc` for L7.1, `add_error_reduce_fc` for L7.2,
`add_message_error_reduce_fc` for L7.3, `subtract_reduce_fc` for L7.4), the loop
invariants, and the per-row/finalize glue. Each L7 endgame discharges `LaneMatches`
with `laneMatches_lift_fe` (tight bound + `lift_fe_spec` residue equality) after the
§Audit getters (`lift_poly_getElem`/`lift_vec_getElem`/`lift_vec_slice_lane`)
rewrite the spec lane to `zmodOfFE (lift_fe x)`.

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
  - Lean 4 toolchain `leanprover/lean4:v4.30.0-rc2` (pinned in `lean-toolchain`).
  - Hacspec ML-KEM spec from https://github.com/cryspen/libcrux at commit `a4cfb1ebf26431b2ee81f0dc19383158aaf397b7`
- For extraction:
  - Hax at commit `ffdf432705d409b62ec025d253a340234b59766f`
    (not publicly available yet, https://github.com/cryspen/hax-evit)
    with the corresponding charon/aeneas versions:
    - Charon at https://github.com/AeneasVerif/charon/releases/tag/nightly-2026.06.02
    - Aeneas at https://github.com/cryspen/aeneas/releases/tag/nightly-2026.06.04
      — note: the `aeneas-pin` file in hax-evit at this commit names tag
      `nightly-2026.06.03`, but commit `8d2077c` (the SHA the binary
      must report) actually ships in `nightly-2026.06.04`. Use the
      `06.04` release.

### Verifying the Lean proof

From `libcrux-iot/ml-kem/proofs/aeneas-lean/`:

```bash
lake exe cache get
lake build
```

### Cross-spec regression (Rust)

We have a couple of Rust tests in place as a first sanity check that
implementation and specification agree:

```bash
cargo test --tests cross_spec
```

This catches mismatches at the Rust level before they propagate into Lean proof failures.

### Extraction from Rust into Lean

```bash
# Spec side (from a checkout of cryspen/libcrux):
cd specs/ml-kem/
./hax_aeneas.py

# Impl side:
cd libcrux-iot/ml-kem/
./hax_aeneas.py
```
