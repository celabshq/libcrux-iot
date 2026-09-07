# Verification of ML-DSA's polynomial API

This directory contains the Lean 4 proof that the Rust implementation of
ML-DSA's **polynomial API** in `libcrux-iot/ml-dsa/src/` computes the same functions
as the ML-DSA specification in `https://github.com/cryspen/libcrux/tree/main/specs`. Both sides are machine-extracted to Lean by the `cargo hax into lean` pipeline.

**Every** theorem below depends only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). The two array-conversion theorems
`to_i32_array_fc` / `from_i32_array_fc` used to additionally carry two
**subslice** axioms; those are **discharged** as of the hax v0.4.0-rc.1 /
aeneas nightly-2026.08.24 migration — see
[the note below](#the-two-former-subslice-axioms-a1--a2). ML-DSA's polynomial
API involves no sampling/XOF, so there are also **no deferred leaf axioms**.

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

**Rust-annotation status.** ALL TEN top-level theorems now carry their
statements in the Rust source itself (`src/polynomial.rs`, `src/ntt.rs`), and
the generated `<fn>.spec`s are discharged at `portable_ops_inst` in
[`Verification/ProofObligations.lean`](Verification/ProofObligations.lean):

- `infinity_norm_exceeds` — `#[requires(coefficients_centered(self))]` +
  `#[ensures(|result| result == (bound <= poly_infinity_norm(&canon_raw(self))))]`,
  discharged by `infinity_norm_exceeds_spec_proof` on the lift-agreement lemma
  `HacspecNorm.canon_raw_ok`.
- `add` / `subtract` — `#[requires(poly_{add,sub}_in_range(self, rhs))]` +
  `#[ensures(|_| poly_{add,sub}(&lift_poly_res(self), &lift_poly_res(rhs)) ==
  lift_poly_res(future(self)))]`, discharged by `{add,subtract}_spec_proof` on
  `HacspecNorm.lift_poly_res_ok` (the `R⁻¹` lift agreement); the array `==` in
  the post reduces by loop reflexivity (`array_eq_self`).
- `ntt` / `invert_ntt_montgomery` / `ntt_multiply_montgomery` —
  `#[requires(poly_abs_le(…, b))]` with the FC bounds (1577058303 / 8388607 /
  8380416-on-`rhs`) + `#[ensures]` naming `ntt::{ntt,intt}` /
  `polynomial::poly_pointwise_mul` through `lift_poly_res`
  (`lift_poly_res_intt` for the inverse NTT's Montgomery-domain output),
  discharged by `{ntt,invert_ntt_montgomery,ntt_multiply_montgomery}_spec_proof`
  on `HacspecNtt.lift_poly_res_intt_ok` and the machinery above.

- the four value equations, through the RAW lane gather `raw_gather` (identity
  view of the lanes; no `mod_q`, no Montgomery factor — their FC posts are
  per-index value equations, not hacspec calls):
  - `zero` — `#[ensures(|result| raw_gather(&result) == [0i32; 256])]`
    (the raw-lane form; strictly stronger than "residues are zero", and the
    Lean FC states both).
  - `to_i32_array` — `#[ensures(|result| result == raw_gather(self))]`.
  - `from_i32_array` — `#[requires(array.len() == 256)]` +
    `#[ensures(|_| &raw_gather(future(result))[..] == array.declassify_ref())]`
    (slice-shaped, discharged through [`Util/SliceEq.lean`](Util/SliceEq.lean),
    the port of sha3's slice-`==` closed form).
  - `reduce` — `#[requires(poly_abs_le(re, 2_139_095_040))]` +
    `#[ensures(|_| poly_abs_le(future(re), 6_283_009) &&
    lift_poly_res(future(re)) == lift_poly_res(re))]` — BOTH halves of the
    Lean FC: residues unchanged AND the Barrett output bound (a residue-only
    post would be strictly weaker).

Discharged by `{zero,to_i32_array,from_i32_array,reduce}_spec_proof` on
`HacspecNorm.raw_res_ok` (the fourth lift agreement) and, for `reduce`'s
post, the build-direction bound lemmas (`poly_abs_le_of_natAbs`).


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

## Axioms

### Standard Lean axioms

Every theorem depends on Lean's three standard axioms: `propext`,
`Classical.choice`, `Quot.sound`. Each top-level `*_fc` theorem carries a
`#print axioms` guard (`#guard_msgs`) that fails the build if its axiom set
drifts, so the table below is machine-checked.

### Per-theorem axiom status

| Theorem | Standard | Subslice (A1/A2) |
|---------|----------|------------------|
| `ntt_hacspec_fc`, `intt_hacspec_fc`, `poly_add_hacspec_fc`, `poly_sub_hacspec_fc`, `poly_pointwise_mul_hacspec_fc`, `infinity_norm_exceeds_hacspec_fc`, `reduce_fc`, `zero_fc` | ✓ | — |
| `from_i32_array_fc` | ✓ | discharged |
| `to_i32_array_fc`   | ✓ | discharged |

There are **no deferred leaf axioms** — unlike ML-KEM's matrix layer, the
polynomial API involves no sampling/XOF/deserialization, so nothing is stated
as an opaque leaf. Since A1/A2 are discharged, every theorem in the table is now
proven down to the three standard axioms and nothing else.

### The two former subslice axioms (A1 / A2)

**Resolved by the hax v0.4.0-rc.1 migration — no longer axioms.**

The migration to mainline hax / the CoreModels v0.2 library introduced these:
Aeneas's `Slice.subslice` / `Array.update_subslice` primitives required a
**strict** `start < end` range and failed on empty ranges, whereas Rust's
`&xs[i..i]` is a valid empty slice. The intended `≤` behaviour was localized to
two `≤`-range specs tagged `AENEAS-SUBSLICE-STRICT` and *axiomatized*, to be
discharged once the aeneas primitive was fixed:

- **A1** `libcrux_iot_ml_dsa.Util.SliceSpecs.Slice.subslice_le_eq` — reading a
  sub-slice `s[a..b]` for `a ≤ b ≤ s.length` returns `s.val.slice a b`.
- **A2** `libcrux_iot_ml_dsa.Util.SliceSpecs.Array.update_subslice_le_eq` —
  writing back a sub-slice over `a ≤ b ≤ length` yields the expected
  `setSlice!`. (The slice-level `Slice.update_subslice_le_eq` is subsumed.)

As of aeneas nightly-2026.08.24 all three primitives guard on `start ≤ end`, so
the aeneas primitive **is** fixed and all three statements are now **theorems**
proved directly from the definitions (`if_pos`/`dif_pos` + `rfl`), kept verbatim
in [`Util/SliceSpecs.lean`](Util/SliceSpecs.lean) so no use site changed.

This also closes a **soundness** gap, not merely a bookkeeping one. While the old
model was strict, A1 asserted success exactly where the definition failed, so
`False` was derivable from it at `s = ⟨[], _⟩`, `r = ⟨0,0⟩`. Because the
`@[spec]`-tagged range-index specs are selected automatically by `hax_mvcgen` on
any slice-range subscript, that axiom could be inherited without a deliberate
citation. With A1/A2 discharged against the real definitions the exposure is gone:
there is no longer an inconsistent axiom in the development to inherit. (ML-KEM's
tree carried the same two axioms and closes them on the same fix.)

Only `to_i32_array` / `from_i32_array` use range-slice reads/writes (packing the
32×8 SIMD lanes into a flat 256-array and back), so only those two theorems ever
depended on A1/A2. The remaining ML-DSA opaque functions in
[`Extraction/FunsExternal.lean`](Extraction/FunsExternal.lean) (the
encoding/sample/decompose entry points outside the polynomial API's scope) are
`opaque` **definitions**, not axioms, so they do not appear in any theorem's
axiom set.

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
  - Lean 4 toolchain `leanprover/lean4:v4.31.0` (pinned in `lean-toolchain`).
  - The Hax Lean proof-lib `cryspen/hax-lean` tag `v0.3.12` (provides the
    `CoreModels` library; pulled in by the lakefile).
- For extraction:
  - Mainline Hax `cargo-hax-v0.4.0` (rev `f8fe6933`; the Lean/Aeneas backend
    lives in `cryspen/hax` main, the old `aeneas-lean` backend was renamed to
    `lean`), with the **prebuilt** charon/aeneas binaries pinned workspace-wide
    in `libcrux-iot/hax.toml`:
    - Charon `nightly-2026.09.02`
    - Aeneas `nightly-2026.09.03` (commit `6852e64`)
  - Easiest via the flake: `nix develop .#lean` from the repo root provides
    `cargo hax` @ `f8fe6933` + cargo; `cargo hax tools install` fetches the
    pinned charon/aeneas.

### Verifying the Lean proof

From `libcrux-iot/ml-dsa/proofs/lean/`:

```bash
lake exe cache get   # fetch the mathlib build cache
lake build
```

A clean build reports 1766 jobs and no errors. Each top-level `*_fc` theorem
carries a `#print axioms` guard (`#guard_msgs`) that fails the build if the
axiom set drifts from the one documented under [Axioms](#axioms).

### Extraction from Rust into Lean

The impl side is a plain hax scenario: `libcrux-iot/ml-dsa/hax.toml` declares
`[scenario.libcrux-iot-ml-dsa]` (Lean backend, `proofs/lean` output, and the
charon `--start-from`/`--opaque` scope), and needs no post-processing. Run it
inside the `nix develop .#lean` environment described above:

```bash
# Spec side (from a checkout of cryspen/libcrux):
cd specs/ml-dsa/
./hax_aeneas.py

# Impl side:
cd libcrux-iot/ml-dsa/
cargo hax extract
```