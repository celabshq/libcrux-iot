/-
  # `Polynomial/HacspecFC.lean` — `@[spec]` Triple corollaries with extracted-hacspec posts

  The impl poly-layer FCs (`Polynomial/Arithmetic.lean::{add_fc,subtract_fc}`,
  `Polynomial/NttArith.lean::ntt_multiply_montgomery_fc`) post the impl result equal
  (through `lift_poly`) to the HAND spec `Spec.Pure.{poly_add,poly_sub,poly_pointwise_mul}`.

  `Spec/HacspecBridge.lean` proves the hand spec equals the machine-EXTRACTED hacspec
  (`hacspec_ml_dsa.polynomial.*`), exposing the plain `*_hacspec_eq` lemmas. This file
  composes the two into `@[spec]` Triple corollaries over the GENERIC impl entry points
  (`PolynomialRingElement.{add,subtract}`, `ntt.ntt_multiply_montgomery` at
  `portable_ops_inst`), whose post is stated DIRECTLY against the extracted spec on the
  canonical re-encodings (`lift_poly_res`). These are the trusted-reference FCs.
-/
import LibcruxIotMlDsa.Spec.HacspecBridge
import LibcruxIotMlDsa.Polynomial.Arithmetic
import LibcruxIotMlDsa.Polynomial.NttArith

open CoreModels Aeneas Aeneas.Std Std.Do Result
open libcrux_iot_ml_dsa
open libcrux_iot_ml_dsa.Spec
open libcrux_iot_ml_dsa.Spec.Lift
open libcrux_iot_ml_dsa.Spec.HacspecBridge
open libcrux_iot_ml_dsa.Polynomial.Ntt

namespace libcrux_iot_ml_dsa.Polynomial.HacspecFC
set_option mvcgen.warning false
set_option linter.unusedVariables false

/-! ## Triple ↔ `Result.ok` reflection (file-scoped §13.5 copies). -/

private theorem triple_exists_ok
    {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl,
      (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

private theorem triple_of_ok
    {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

/-! ## `@[spec]` corollaries: extracted-hacspec posts. -/

/-- **`PolynomialRingElement.add` ↔ extracted `hacspec_ml_dsa.polynomial.poly_add`.**
    Composes the impl `add_fc` (functional post via `lift_poly` = hand spec) with the
    bridge `poly_add_hacspec_eq` (hand spec = extracted spec). -/
@[spec]
theorem poly_add_hacspec_fc
    (self rhs : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (hpre : ∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
      ((self.simd_units.val[u]!).values.val[j]!.val
        + (rhs.simd_units.val[u]!).values.val[j]!.val).natAbs ≤ 2 ^ 31 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    polynomial.PolynomialRingElement.add portable_ops_inst self rhs
    ⦃ ⇓ r => ⌜ hacspec_ml_dsa.polynomial.poly_add (lift_poly_res self) (lift_poly_res rhs)
                = .ok (lift_poly_res r) ⌝ ⦄ := by
  obtain ⟨r, hr_eq, hr_lift, _hr_bnd⟩ :=
    triple_exists_ok (Polynomial.Arithmetic.add_fc self rhs hpre)
  apply triple_of_ok hr_eq
  exact HacspecBridge.poly_add_hacspec_eq self rhs r hr_lift

/--
info: 'libcrux_iot_ml_dsa.Polynomial.HacspecFC.poly_add_hacspec_fc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms poly_add_hacspec_fc

/-- **`PolynomialRingElement.subtract` ↔ extracted `hacspec_ml_dsa.polynomial.poly_sub`.** -/
@[spec]
theorem poly_sub_hacspec_fc
    (self rhs : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (hpre : ∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
      ((self.simd_units.val[u]!).values.val[j]!.val
        - (rhs.simd_units.val[u]!).values.val[j]!.val).natAbs ≤ 2 ^ 31 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    polynomial.PolynomialRingElement.subtract portable_ops_inst self rhs
    ⦃ ⇓ r => ⌜ hacspec_ml_dsa.polynomial.poly_sub (lift_poly_res self) (lift_poly_res rhs)
                = .ok (lift_poly_res r) ⌝ ⦄ := by
  obtain ⟨r, hr_eq, hr_lift, _hr_bnd⟩ :=
    triple_exists_ok (Polynomial.Arithmetic.subtract_fc self rhs hpre)
  apply triple_of_ok hr_eq
  exact HacspecBridge.poly_sub_hacspec_eq self rhs r hr_lift

/--
info: 'libcrux_iot_ml_dsa.Polynomial.HacspecFC.poly_sub_hacspec_fc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms poly_sub_hacspec_fc

/-- **`ntt.ntt_multiply_montgomery` ↔ extracted `hacspec_ml_dsa.polynomial.poly_pointwise_mul`.** -/
@[spec]
theorem poly_pointwise_mul_hacspec_fc
    (lhs rhs : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (hpre : ∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
      (rhs.simd_units.val[u]!).values.val[j]!.val.natAbs ≤ 8380416) :
    ⦃ ⌜ True ⌝ ⦄
    ntt.ntt_multiply_montgomery portable_ops_inst lhs rhs
    ⦃ ⇓ r => ⌜ hacspec_ml_dsa.polynomial.poly_pointwise_mul (lift_poly_res lhs) (lift_poly_res rhs)
                = .ok (lift_poly_res r) ⌝ ⦄ := by
  obtain ⟨r, hr_eq, hr_lift, _hr_bnd⟩ :=
    triple_exists_ok (Polynomial.NttArith.ntt_multiply_montgomery_fc lhs rhs hpre)
  apply triple_of_ok hr_eq
  exact HacspecBridge.poly_pointwise_mul_hacspec_eq lhs rhs r hr_lift

/--
info: 'libcrux_iot_ml_dsa.Polynomial.HacspecFC.poly_pointwise_mul_hacspec_fc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms poly_pointwise_mul_hacspec_fc

end libcrux_iot_ml_dsa.Polynomial.HacspecFC
