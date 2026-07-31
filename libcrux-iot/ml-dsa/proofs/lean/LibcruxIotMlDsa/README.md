# Verification of ML-DSA's polynomial API

This directory contains the Lean 4 proof that the Rust implementation of
ML-DSA's **polynomial API** in `libcrux-iot/ml-dsa/src/` computes the same functions
as the ML-DSA specification in `https://github.com/celabshq/libcrux/tree/main/specs`. Both sides are machine-extracted to Lean by the `cargo hax into aeneas-lean` pipeline.

Every theorem below depends only on Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Top-level theorems — the `PolynomialRingElement` API

The polynomial API (`PolynomialRingElement`) is generic over the
`simd::traits::Operations` trait. The whole layer is dispatched through a single
concrete instance, `Operations Coefficients`. Every top-level theorem
applies the generic impl function at this instance.

Each is an `mvcgen` Triple `⦃ True ⦄ <impl> <args>… ⦃ ⇓ r => ⌜ <spec> (lift_poly_res <args>)… = .ok (lift_poly_res r)⌝ ⦄`
that ties the impl function directly to its counterpart in the extracted spec. The impl stores coefficients as 32 SIMD units × 8 signed,
Montgomery-domain `i32` lanes, wheras the spec uses a flat array `[i32; 256]`,
Montgomery factor stripped lane-wise.
Lifting functions do the conversion.

Representative statement ([`Polynomial/HacspecNtt.lean`](Polynomial/HacspecNtt.lean)):
```lean
theorem ntt_hacspec_fc (re : PolynomialRingElement Coefficients)
    (hin : …per-lane bound ≤ 1577058303…) :
    ⦃ ⌜ True ⌝ ⦄
    ntt.ntt portable_ops_inst re
    ⦃ ⇓ r => ⌜ hacspec_ml_dsa.ntt.ntt (lift_poly_res re) = .ok (lift_poly_res r) ⌝ ⦄
```

| Theorem (file) | impl function | post condition of the triple |
|---|---|---|
| `ntt_hacspec_fc` ([`Polynomial/HacspecNtt.lean`](Polynomial/HacspecNtt.lean)) | `ntt.ntt` | `hacspec_ml_dsa.ntt.ntt (lift_poly_res re) = .ok (lift_poly_res r)` |
| `intt_hacspec_fc` ([`Polynomial/HacspecNtt.lean`](Polynomial/HacspecNtt.lean)) | `ntt.invert_ntt_montgomery` | `hacspec_ml_dsa.ntt.intt (lift_poly_res re) = .ok (lift_poly_res_intt r)` (The impl's inverse NTT leaves its output in the Montgomery domain (`· R`); `lift_poly_res_intt` strips that factor (`· R⁻¹`) so te result matches the extracted `intt`.) |
| `poly_pointwise_mul_hacspec_fc` ([`Polynomial/HacspecFC.lean`](Polynomial/HacspecFC.lean)) | `ntt.ntt_multiply_montgomery` | `hacspec_ml_dsa.polynomial.poly_pointwise_mul (lift_poly_res lhs) (lift_poly_res rhs) = .ok (lift_poly_res r)` |
| `poly_add_hacspec_fc` ([`Polynomial/HacspecFC.lean`](Polynomial/HacspecFC.lean)) | `…PolynomialRingElement.add` | `hacspec_ml_dsa.polynomial.poly_add (lift_poly_res self) (lift_poly_res rhs) = .ok (lift_poly_res r)` |
| `poly_sub_hacspec_fc` ([`Polynomial/HacspecFC.lean`](Polynomial/HacspecFC.lean)) | `…PolynomialRingElement.subtract` | `hacspec_ml_dsa.polynomial.poly_sub (lift_poly_res self) (lift_poly_res rhs) = .ok (lift_poly_res r)` |
| `infinity_norm_exceeds_hacspec_fc` ([`Polynomial/HacspecNorm.lean`](Polynomial/HacspecNorm.lean)) | `…PolynomialRingElement.infinity_norm_exceeds` | `∃ n, hacspec_ml_dsa.polynomial.poly_infinity_norm (canon_raw self) = .ok n ∧ (r = decide (bound.val ≤ n.val))` (The spec does not have a direct equivalent to `infinity_norm_exceeds`. So the postcondition needs to establish equivalence using `poly_infinity_norm`.) |


Four impl ops have no non-trivial counterpart in the spec (it treats them as
identity / a constant / a copy), so they are stated as direct value equations:

| Theorem (file) | impl function | post condition of the triple |
|---|---|---|
| `reduce_fc` ([`Polynomial/NttArith.lean`](Polynomial/NttArith.lean)) | `ntt.reduce` | `lift_poly r = lift_poly re` (Barrett-reduce; residues unchanged) |
| `zero_fc` ([`Polynomial/Convert.lean`](Polynomial/Convert.lean)) | `…zero` | `lift_poly r = Pure.zero_poly` (the zero polynomial) |
| `to_i32_array_fc` ([`Polynomial/Convert.lean`](Polynomial/Convert.lean)) | `…to_i32_array` | `∀ k<256, (r[k]).val = <self coefficient k>` |
| `from_i32_array_fc` ([`Polynomial/Convert.lean`](Polynomial/Convert.lean)) | `…from_i32_array` | `∀ k<256, <r coefficient k> = (array[k]).val` |

## Supporting layers

The top-level theorems are corollaries / loop-compositions of a stack of proven
per-SIMD-unit and NTT-driver results.

### NTT masters (the per-array `[Coefficients; 32]` engines)

| Theorem (file) | impl function |
|---|---|
| `ntt_inner_fc` ([`Vector/Portable/NttMaster.lean`](Vector/Portable/NttMaster.lean)) | `simd.portable.ntt.ntt` (8 forward layers) |
| `invert_ntt_inner_fc` ([`Vector/Portable/InvNttMaster.lean`](Vector/Portable/InvNttMaster.lean)) | `simd.portable.invntt.invert_ntt_montgomery` (8 inverse layers + finalize) |

These compose the per-layer butterfly drivers
([`Vector/Portable/{Ntt,InvNtt,NttDriver,InvNttDriver}.lean`](Vector/Portable/)).

### Per-SIMD-unit (8-lane) arithmetic and rounding

| Theorem (file) | impl function |
|---|---|
| `montgomery_reduce_element_spec` ([`Vector/Portable/Arithmetic.lean`](Vector/Portable/Arithmetic.lean)) | `montgomery_reduce_element` |
| `reduce_element_spec` ([`Vector/Portable/Arithmetic.lean`](Vector/Portable/Arithmetic.lean)) | `reduce_element` (Barrett) |
| `add_spec` / `subtract_spec` / `montgomery_multiply_spec` / `montgomery_multiply_by_constant_spec` ([`Vector/Portable/Element.lean`](Vector/Portable/Element.lean)) | `arithmetic.{add,subtract,montgomery_multiply,montgomery_multiply_by_constant}` |
| `zero_unit_spec` / `to_coefficient_array_spec` / `from_coefficient_array_spec` ([`Vector/Portable/Element.lean`](Vector/Portable/Element.lean)) | `vector_type.{zero,to_coefficient_array,from_coefficient_array}` |
| `shift_left_then_reduce_spec` ([`Vector/Portable/Arithmetic.lean`](Vector/Portable/Arithmetic.lean)) | `shift_left_then_reduce` |
| `infinity_norm_exceeds_unit_spec` ([`Vector/Portable/Arithmetic.lean`](Vector/Portable/Arithmetic.lean)) | `arithmetic.infinity_norm_exceeds` (the bug-fixed sign-mask) |
| `power2round_spec` / `decompose_spec` / `use_hint_spec` / `compute_hint_spec` ([`Vector/Portable/Rounding.lean`](Vector/Portable/Rounding.lean)) | FIPS-204 §7.4 rounding |

## Proof architecture

The proof is built around a **Lean reference spec** that sits between the two
machine-extracted Rust artifacts. We write the spec once in Lean, prove it
equivalent to the Rust implementation *and* to the Rust spec, then compose the
two equivalences to obtain the top-level theorems.

```
   Rust impl  ──(impl FCs)──▶  Lean spec  ◀──(spec bridges)──  Rust spec
 (extracted Funs)            (Spec/Pure.lean)            (extracted hacspec_ml_dsa)
        └──────────────────── composed ─────────────────────▶ *_hacspec_fc
```

**1. The Lean reference spec.** [`Spec/Pure.lean`](Spec/Pure.lean) is a small,
self-contained reference written directly in `ZMod q`: `ntt`, `intt`,
`poly_pointwise_mul`, `poly_add` / `poly_sub`, `infinity_norm_exceeds`, etc. The
rounding operations are in [`Spec/Rounding.lean`](Spec/Rounding.lean) and the
shared constants in [`Spec/Parameters.lean`](Spec/Parameters.lean) /
[`Spec/Montgomery.lean`](Spec/Montgomery.lean). Working in `ZMod q` keeps the
algebra clean and makes both equivalences below tractable.

**2. Lean spec ↔ Rust impl.** Each impl FC theorem proves that an extracted
implementation function, lifted to `ZMod q`, computes the corresponding
`Spec.Pure.*` function — e.g. [`Polynomial/Ntt.lean`](Polynomial/Ntt.lean)'s
`ntt_fc` establishes `lift_poly r = Pure.ntt (lift_poly re)`. These are built
bottom-up from the per-SIMD-unit specs, butterfly drivers and NTT masters in
[`Vector/Portable/`](Vector/Portable/) and the loop combinators in
[`Util/`](Util/). The representation gap — the impl stores 32×8 signed,
Montgomery-domain `i32` lanes, the spec a flat 256-element `ZMod q` array — is
handled by the `lift` family in [`Spec/Lift.lean`](Spec/Lift.lean) (`liftZ`
strips one Montgomery factor; `lift_poly` / `lift_poly_res` flatten the lanes).

**3. Lean spec ↔ Rust spec.** The Rust spec is `hacspec_ml_dsa.*` — the
`specs/ml-dsa` crate machine-extracted to Lean by the same `cargo hax` pipeline
as the impl and wired in as the `HacspecMlDsa` Lake dependency. The *bridge*
lemmas prove each `Spec.Pure.*` function equals its extracted `hacspec_ml_dsa.*`
counterpart under the residue map: see
[`Spec/HacspecBridge.lean`](Spec/HacspecBridge.lean) (`mod_q_eq`,
`createi_pure_eq`, `poly_add_bridge` / `poly_sub_bridge` /
`poly_pointwise_mul_bridge`),
[`Polynomial/HacspecNtt.lean`](Polynomial/HacspecNtt.lean) (`ntt_bridge`,
`intt_bridge`, and the `zetas_bridge` table check), and
[`Polynomial/HacspecNorm.lean`](Polynomial/HacspecNorm.lean)
(`coeff_norm_bridge`, `poly_infinity_norm_bridge`).

**4. Composition.** The top-level `*_hacspec_fc` theorems
([`Polynomial/HacspecNtt.lean`](Polynomial/HacspecNtt.lean),
[`Polynomial/HacspecFC.lean`](Polynomial/HacspecFC.lean),
[`Polynomial/HacspecNorm.lean`](Polynomial/HacspecNorm.lean)) chain the two
halves: the impl FC gives impl ↔ Lean spec and the bridge gives Lean spec ↔ Rust
spec, so the implementation is shown to match the extracted Rust spec directly.
The Lean spec is thus only a proof convenience — it is *proven equal* to the
trusted extracted spec, not an independently trusted artifact.

## Reproduction

### Prerequisites

- For running the proofs:
  - Lean 4 toolchain `leanprover/lean4:v4.30.0-rc2` (pinned in `lean-toolchain`).
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

From `libcrux-iot/ml-dsa/proofs/aeneas-lean/`:

```bash
lake exe cache get
lake build
```

### Extraction from Rust into Lean

```bash
# Spec side (from a checkout of cryspen/libcrux):
cd specs/ml-dsa/
./hax_aeneas.py

# Impl side:
cd libcrux-iot/ml-dsa/
./hax_aeneas.py
```