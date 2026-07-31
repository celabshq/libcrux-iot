/-
  # `Polynomial/Ntt.lean` — polynomial-layer NTT FCs (ML-DSA)

  The polynomial-layer NTT API (`crate::ntt`) is generic over the
  `simd::traits::Operations` trait. Charon emits the concrete
  `Operations for Coefficients` instance
  (`…Coefficients.Insts.…Operations`, abbreviated `portable_ops_inst`). These FCs
  apply the generic fns to that extracted instance: each one unfolds the trivial
  wrapper (`do let a ← inst.<m> re.simd_units; ok {simd_units := a}`), reduces the
  instance method to the concrete per-unit master, and applies the proven master
  (`ntt_inner_fc` / `invert_ntt_inner_fc`), bridging `lift_poly = lift_units` on
  `.simd_units` (`Spec.Lift.lift_poly_eq_lift_units`, `rfl`).
-/
import LibcruxIotMlDsa.Vector.Portable.NttMaster
import LibcruxIotMlDsa.Vector.Portable.InvNttMaster

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_dsa.Polynomial.Ntt
open Aeneas Aeneas.Std Std.Do Result
open libcrux_iot_ml_dsa
open libcrux_iot_ml_dsa.Spec
open libcrux_iot_ml_dsa.Spec.Lift libcrux_iot_ml_dsa.Spec.Montgomery
  libcrux_iot_ml_dsa.Spec.Parameters

/-- The concrete portable `Operations Coefficients` instance emitted by aeneas.
    Generic poly-layer fns are applied at this instance. -/
abbrev portable_ops_inst :
    simd.traits.Operations simd.portable.vector_type.Coefficients :=
  simd.portable.vector_type.Coefficients.Insts.Libcrux_iot_ml_dsaSimdTraitsOperations

/-- Reflect a `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` Triple into an `.ok` witness plus the post
    (file-scoped copy of the §13.5 helper). -/
private theorem triple_exists_ok
    {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl,
      (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

/-- `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` closer for `x = .ok v` (file-scoped §13.5 copy). -/
private theorem triple_of_ok
    {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

/-! ## Forward NTT — `ntt.ntt` at `Coefficients`.

`ntt.ntt inst re = do let a ← inst.ntt re.simd_units; ok {simd_units := a}`; the
instance's `ntt` field forwards to `simd.portable.ntt.ntt`, so this is a one-step
corollary of `ntt_inner_fc`. -/
set_option maxHeartbeats 1000000 in
@[spec]
theorem ntt_fc
    (re : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (B : Nat)
    (hB : (B : Int) + 34 * 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.simd_units.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    ntt.ntt portable_ops_inst re
    ⦃ ⇓ r => ⌜ lift_poly r = Pure.ntt (lift_poly re)
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.simd_units.val[u]!).values.val[l]!.val.natAbs ≤ B + 34 * 2 ^ 24) ⌝ ⦄ := by
  obtain ⟨a, ha_eq, ha_lift, ha_bd⟩ :=
    triple_exists_ok (Vector.Portable.NttDriver.ntt_inner_fc re.simd_units B hB hin)
  apply triple_of_ok (v := { simd_units := a })
  · show (do
          let a ← simd.portable.ntt.ntt re.simd_units
          ok ({ simd_units := a } :
            polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients))
        = ok ({ simd_units := a } :
            polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    rw [ha_eq]; rfl
  · refine ⟨?_, ?_⟩
    · rw [lift_poly_eq_lift_units, lift_poly_eq_lift_units]; exact ha_lift
    · exact ha_bd

/-! ## Inverse NTT — `ntt.invert_ntt_montgomery` at `Coefficients`.

`ntt.invert_ntt_montgomery inst re = do let a ← inst.invert_ntt_montgomery re.simd_units;
ok {simd_units := a}`; corollary of `invert_ntt_inner_fc`. Output is mont-domain
(`·R`), matching the master. -/
set_option maxHeartbeats 1000000 in
@[spec]
theorem invert_ntt_montgomery_fc
    (re : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (B : Nat)
    (hB : (B : Int) ≤ 2 ^ 23 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.simd_units.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    ntt.invert_ntt_montgomery portable_ops_inst re
    ⦃ ⇓ r => ⌜ lift_poly r
                 = (Pure.intt (lift_poly re)).map (· * ((Montgomery.R : Nat) : Zq))
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.simd_units.val[u]!).values.val[l]!.val.natAbs ≤ 2 ^ 24) ⌝ ⦄ := by
  obtain ⟨a, ha_eq, ha_lift, ha_bd⟩ :=
    triple_exists_ok (Vector.Portable.InvNttDriver.invert_ntt_inner_fc re.simd_units B hB hin)
  apply triple_of_ok (v := { simd_units := a })
  · show (do
          let a ← simd.portable.invntt.invert_ntt_montgomery re.simd_units
          ok ({ simd_units := a } :
            polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients))
        = ok ({ simd_units := a } :
            polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    rw [ha_eq]; rfl
  · refine ⟨?_, ?_⟩
    · rw [lift_poly_eq_lift_units, lift_poly_eq_lift_units]; exact ha_lift
    · exact ha_bd

end libcrux_iot_ml_dsa.Polynomial.Ntt
