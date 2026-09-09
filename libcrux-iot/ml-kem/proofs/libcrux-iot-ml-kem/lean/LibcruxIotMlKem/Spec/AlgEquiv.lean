/-
  # `Spec/AlgEquiv.lean` — algebraic-equivalence lemmas for the
  easy `bit_<op>` cluster.

  Each lemma characterises `bit_<op>` pointwise on
  `MontPoly = Vector (ZMod 3329) 256` in closed form, so callers can
  unfold a single named theorem instead of inlining `Vector.getElem_ofFn`
  chains.

  | `bit_<op>`                              | Characterisation         | Shape  |
  | --------------------------------------- | ------------------------ | ------ |
  | `bit_add`                               | pointwise `+`            | rfl    |
  | `bit_sub`                               | pointwise `-`            | rfl    |
  | `bit_barrett_reduce`                    | identity                 | rfl    |
  | `bit_montgomery_multiply_by_constant`   | pointwise `· c`          | rfl    |
  | `bit_multiply_by_constant`              | pointwise `· c`          | rfl    |
  | `bit_to_unsigned_representative`        | identity                 | rfl    |
  | `bit_to_standard_domain`                | pointwise `· 2285`       | rfl    |
  | `bit_cond_subtract_3329`                | identity                 | rfl    |
  | `bit_add_to_ring_element`               | `bit_add`                | rfl    |
  | `bit_subtract_reduce`                   | pointwise `(q-p) · 512`  | rfl    |

  - The pointwise lemmas are `@[simp]`-eligible: each rewrites
    `(bit_<op> ...)[i]'h` to a closed form on the operand lanes.
  - The SpecPoly-bridge variants of the form
    `bit_<op> (SpecPoly.toMontPoly p) = SpecPoly.toMontPoly (Spec.<op>_pure p)`
    are deferred to the NTT-cluster pass because they require the
    pure-projection side lemmas of `parameters.FieldElement.{add,sub,mul}`.
    A locked target shape for the follow-up is captured inline at the end
    of this file.
  - Mathlib is imported for `ring`/`field_simp` on `ZMod 3329`.
-/
import LibcruxIotMlKem.Spec
import LibcruxIotMlKem.Spec.Pure
import Mathlib.Tactic.Ring

namespace libcrux_iot_ml_kem.Spec.AlgEquiv
open CoreModels Aeneas Aeneas.Std
open libcrux_iot_ml_kem.Spec

/-! ## §M.4 Easy #1 — `bit_add` pointwise. -/

/-- `(bit_add p q)[i] = p[i] + q[i]`. -/
@[scoped grind =]
theorem bit_add_getElem (p q : MontPoly) (i : Nat) (h : i < 256) :
    (bit_add p q)[i]'h = p[i]'h + q[i]'h := by
  unfold bit_add
  simp [Vector.getElem_ofFn]

/-! ## §M.4 Easy #2 — `bit_sub` pointwise. -/

/-- `(bit_sub p q)[i] = p[i] - q[i]`. -/
@[scoped grind =]
theorem bit_sub_getElem (p q : MontPoly) (i : Nat) (h : i < 256) :
    (bit_sub p q)[i]'h = p[i]'h - q[i]'h := by
  unfold bit_sub
  simp [Vector.getElem_ofFn]

/-! ## §M.4 Easy #3 — `bit_barrett_reduce` is identity. -/

/-- `bit_barrett_reduce p = p` (identity in `ZMod 3329`; the impl-side
    Barrett reduction picks a canonical residue mod q, which is the
    same `ZMod 3329` element). -/
@[scoped grind =]
theorem bit_barrett_reduce_eq (p : MontPoly) : bit_barrett_reduce p = p := rfl

/-! ## §M.4 Easy #4 — `bit_montgomery_multiply_by_constant` pointwise. -/

/-- `(bit_montgomery_multiply_by_constant p c)[i] = p[i] * c`. The
    Mont factor is already absorbed by the calling convention — the
    constant is in Mont domain (`c · R`), and Mont multiplication
    `· c · R · R⁻¹ = · c`, so the result is plain multiplication by `c`. -/
@[scoped grind =]
theorem bit_montgomery_multiply_by_constant_getElem
    (p : MontPoly) (c : ZMod 3329) (i : Nat) (h : i < 256) :
    (bit_montgomery_multiply_by_constant p c)[i]'h = p[i]'h * c := by
  unfold bit_montgomery_multiply_by_constant
  simp [Vector.getElem_ofFn]

/-! ## §M.4 Easy #5 — `bit_multiply_by_constant` pointwise. -/

/-- `(bit_multiply_by_constant p c)[i] = p[i] * c` (plain-domain
    multiplication). -/
@[scoped grind =]
theorem bit_multiply_by_constant_getElem
    (p : MontPoly) (c : ZMod 3329) (i : Nat) (h : i < 256) :
    (bit_multiply_by_constant p c)[i]'h = p[i]'h * c := by
  unfold bit_multiply_by_constant
  simp [Vector.getElem_ofFn]

/-! ## §M.4 Easy #6 — `bit_to_unsigned_representative` is identity. -/

/-- `bit_to_unsigned_representative p = p`. The impl-side picks the
    nonneg `[0, q)` representative; that is the same `ZMod 3329` element. -/
@[scoped grind =]
theorem bit_to_unsigned_representative_eq (p : MontPoly) :
    bit_to_unsigned_representative p = p := rfl

/-! ## §M.4 Easy #7 — `bit_to_standard_domain` pointwise. -/

/-- `(bit_to_standard_domain p)[i] = p[i] * 2285`. The constant `2285`
    is `R mod q` (B.3 keystone): the operation multiplies by `R²·R⁻¹`
    = `R` because the underlying impl composes
    `montgomery_multiply_fer_by_constant` with the constant `1353 =
    R² mod q`. After Mont absorption we end up with `· R`. -/
@[scoped grind =]
theorem bit_to_standard_domain_getElem
    (p : MontPoly) (i : Nat) (h : i < 256) :
    (bit_to_standard_domain p)[i]'h = p[i]'h * (2285 : ZMod 3329) := by
  unfold bit_to_standard_domain
  simp [Vector.getElem_ofFn]

/-! ## §M.4 Easy #8 — `bit_cond_subtract_3329` is identity. -/

/-- `bit_cond_subtract_3329 p = p`. The impl-side conditionally
    subtracts `q = 3329` to canonicalise the lane to `[0, q)`; in
    `ZMod 3329` this is a no-op modulo q. -/
@[scoped grind =]
theorem bit_cond_subtract_3329_eq (p : MontPoly) :
    bit_cond_subtract_3329 p = p := rfl

/-! ## §M.4 Easy #9 — `bit_add_to_ring_element` is `bit_add`. -/

/-- `bit_add_to_ring_element p q = bit_add p q`. The poly-level
    `add_to_ring_element` impl wrapper is just chunked pointwise
    addition, which lifts to `bit_add` exactly. -/
@[scoped grind =]
theorem bit_add_to_ring_element_eq (p q : MontPoly) :
    bit_add_to_ring_element p q = bit_add p q := rfl

/-- Corollary: `bit_add_to_ring_element` pointwise. -/
@[scoped grind =]
theorem bit_add_to_ring_element_getElem (p q : MontPoly) (i : Nat) (h : i < 256) :
    (bit_add_to_ring_element p q)[i]'h = p[i]'h + q[i]'h := by
  rw [bit_add_to_ring_element_eq]; exact bit_add_getElem p q i h

/-! ## §M.4 Easy #10 — `bit_subtract_reduce` pointwise. -/

/-- `(bit_subtract_reduce p q)[i] = (q[i] - p[i]) * 512`. The factor
    `512 = R · 128⁻¹ mod q = 1441 · 169 mod q` (B.1 keystone): the
    impl computes "subtract and finalize INTT" by multiplying by
    `R/128 mod q`. -/
@[scoped grind =]
theorem bit_subtract_reduce_getElem (p q : MontPoly) (i : Nat) (h : i < 256) :
    (bit_subtract_reduce p q)[i]'h = (q[i]'h - p[i]'h) * (512 : ZMod 3329) := by
  unfold bit_subtract_reduce
  simp [Vector.getElem_ofFn]

/-! ## §M.4 SpecPoly bridges — deferred to NTT cluster.

    The full set of bridges of the form
      `bit_<op> (SpecPoly.toMontPoly p) = SpecPoly.toMontPoly (Spec.<op>_pure p)`
    requires per-`bit_<op>` sub-lemmas `zmodOfFE_<op>_pure` that
    distribute `zmodOfFE` through the hacspec `_pure` projection. Each
    sub-lemma depends on the pure-projection side lemma for the
    underlying `parameters.FieldElement.<op>` (Open Question I.8 in
    arch plan §F.2), which is not in scope for this easy-cluster
    dispatch.

    The target shape (locked here for the follow-up dispatch):
    ```
    theorem bit_add_specpoly_alg_eq (p q : SpecPoly) :
        bit_add (SpecPoly.toMontPoly p) (SpecPoly.toMontPoly q) =
        SpecPoly.toMontPoly
          (Vector.ofFn fun i => Spec.Pure.FieldElement.add_pure (p[i]) (q[i])) := by
      apply Vector.ext; intro k hk
      rw [bit_add_getElem]
      unfold SpecPoly.toMontPoly
      simp only [Vector.getElem_map, Vector.getElem_ofFn]
      exact (zmodOfFE_add_pure (p[k]) (q[k])).symm
    ```
    -- closes once the deferred sub-lemma
    --   `zmodOfFE (FieldElement.add_pure a b) = zmodOfFE a + zmodOfFE b`
    -- lands (depends on `FieldElement.add_eq_ok` pure-projection).
-/

end libcrux_iot_ml_kem.Spec.AlgEquiv