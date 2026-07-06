/-
  # `Equivalence/L2_NTTSteps.lean` — Layer 2 intra-PortableVector NTT step Triples.

  L2.x Triples for the per-PortableVector NTT butterflies in
  `vector/portable/ntt.rs`. L2.1 `ntt_step_spec` is the single
  Cooley-Tukey butterfly inside a PortableVector at indices `(i, j)`
  with ζ; post is bound-only (unchanged lanes + 3·3328 → 4·3328
  propagation). The modular congruence content (`r[i] ≡ a + ζb`,
  `r[j] ≡ a - ζb` mod 3329) lives in `BitMlKem.Commute`.
-/
import LibcruxIotMlKem.Extraction.Funs
import LibcruxIotMlKem.Vector.Portable.Arithmetic.LoopHelper
import LibcruxIotMlKem.Vector.Portable.Arithmetic.PerElement
import LibcruxIotMlKem.Spec.Lift
import LibcruxIotMlKem.Vector.Portable.Arithmetic.Element

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_kem.Vector.Portable.Ntt
open libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper

/-! ## Local helpers — Triple ↔ Result.ok bridges. -/

/-- The Triple `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` closer for `x = .ok v`. -/
private theorem triple_of_ok_l2 {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

/-- Extract the `.ok` witness from a true-pre Triple. Used by L2.1 to
    consume L0.4's `@[spec]`. -/
private theorem triple_exists_ok_l2 {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl, (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

/-! ## L2.1 — `ntt_step_spec`

    The impl is a straight chain of 8 binds:
      1. read `vec[j]`
      2. classify ζ        (identity)
      3. L0.4 montgomery_multiply: `t = mont_mult(vec[j], ζ)`
      4. read `vec[i]`
      5. `a_minus_t = vec[i] - t`   (wrapping_sub)
      6. `a_plus_t  = vec[i] + t`   (wrapping_add)
      7. write `vec[j] := a_minus_t`
      8. write `vec[i] := a_plus_t`

    Under the L0.4 bound (`|t.val| ≤ 3328`), and `|vec[i]|, |vec[j]|
    ≤ 3·3328`, the two sums `vec[i] ± t` satisfy `| · | ≤ 4·3328 =
    13312 < 2^15 = 32768`, so the wrappings are the identity and
    `(vec[i] ± t).val = vec[i].val ± t.val`. -/

/-- Reduction of `core.num.I16.wrapping_sub` to the underlying
    Aeneas `Std.I16.wrapping_sub`. -/
private theorem cm_wrapping_sub_ok_eq (x y : Std.I16) :
    CoreModels.core.num.I16.wrapping_sub x y = .ok (Std.I16.wrapping_sub x y) := by
  unfold CoreModels.core.num.I16.wrapping_sub
  unfold rust_primitives.arithmetic.wrapping_sub_i16
  rfl

/-- Reduction of `core.num.I16.wrapping_add` to the underlying
    Aeneas `Std.I16.wrapping_add`. -/
private theorem cm_wrapping_add_ok_eq (x y : Std.I16) :
    CoreModels.core.num.I16.wrapping_add x y = .ok (Std.I16.wrapping_add x y) := by
  unfold CoreModels.core.num.I16.wrapping_add
  unfold rust_primitives.arithmetic.wrapping_add_i16
  rfl

/-- Reduction of `classify` to identity. -/
private theorem classify_ok_eq {T : Type} (x : T) :
    libcrux_secrets.traits.Classify.Blanket.classify x = .ok x := rfl

/-- Under `|a.val| ≤ B·3328`, `|t.val| ≤ 3328`, and `B ≤ 8`, the I16-wrapped
    sum `a + t` has `.val = a.val + t.val` and `.val.natAbs ≤ (B+1)·3328`. -/
private theorem add_no_overflow_value_B (a t : Std.I16) (B : Nat)
    (h_a : a.val.natAbs ≤ B * 3328) (h_t : t.val.natAbs ≤ 3328) (h_B : B ≤ 8) :
    (Std.I16.wrapping_add a t).val = a.val + t.val
      ∧ (Std.I16.wrapping_add a t).val.natAbs ≤ (B + 1) * 3328 := by
  -- |a + t| ≤ |a| + |t| ≤ B·3328 + 3328 = (B+1)·3328 ≤ 9·3328 = 29952 < 2^15 = 32768.
  have h_sum_abs : ((a.val + t.val : Int)).natAbs ≤ (B + 1) * 3328 := by
    have h_tri : (a.val + t.val).natAbs ≤ a.val.natAbs + t.val.natAbs := Int.natAbs_add_le _ _
    omega
  -- No-overflow ⇒ bmod is identity.
  have h_lb : -(2 ^ 15 : Int) ≤ a.val + t.val := by
    have h_natAbs : ((a.val + t.val : Int)).natAbs ≤ (B + 1) * 3328 := h_sum_abs
    have h_bound : (B + 1) * 3328 ≤ 9 * 3328 := by
      have : B + 1 ≤ 9 := by omega
      exact Nat.mul_le_mul_right _ this
    omega
  have h_ub : a.val + t.val < (2 ^ 15 : Int) := by
    have h_natAbs : ((a.val + t.val : Int)).natAbs ≤ (B + 1) * 3328 := h_sum_abs
    have h_bound : (B + 1) * 3328 ≤ 9 * 3328 := by
      have : B + 1 ≤ 9 := by omega
      exact Nat.mul_le_mul_right _ this
    omega
  have h_bmod : Int.bmod (a.val + t.val) (2 ^ 16) = a.val + t.val := by
    apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
    · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
      exact le_trans h_const h_lb
    · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
      exact lt_of_lt_of_le h_ub h_const
  have h_val := Std.I16.wrapping_add_val_eq a t
  refine ⟨?_, ?_⟩
  · rw [h_val, h_bmod]
  · rw [h_val, h_bmod]; exact h_sum_abs

/-- Under `|a.val| ≤ B·3328`, `|t.val| ≤ 3328`, and `B ≤ 8`, the I16-wrapped
    diff `a - t` has `.val = a.val - t.val` and `.val.natAbs ≤ (B+1)·3328`. -/
private theorem sub_no_overflow_value_B (a t : Std.I16) (B : Nat)
    (h_a : a.val.natAbs ≤ B * 3328) (h_t : t.val.natAbs ≤ 3328) (h_B : B ≤ 8) :
    (Std.I16.wrapping_sub a t).val = a.val - t.val
      ∧ (Std.I16.wrapping_sub a t).val.natAbs ≤ (B + 1) * 3328 := by
  have h_diff_abs : ((a.val - t.val : Int)).natAbs ≤ (B + 1) * 3328 := by
    have h_neg_natAbs : (-t.val).natAbs = t.val.natAbs := Int.natAbs_neg _
    have h_eq : a.val - t.val = a.val + (-t.val) := by ring
    rw [h_eq]
    have h_tri : (a.val + (-t.val)).natAbs ≤ a.val.natAbs + (-t.val).natAbs :=
      Int.natAbs_add_le _ _
    rw [h_neg_natAbs] at h_tri
    omega
  have h_lb : -(2 ^ 15 : Int) ≤ a.val - t.val := by
    have h_natAbs : ((a.val - t.val : Int)).natAbs ≤ (B + 1) * 3328 := h_diff_abs
    have h_bound : (B + 1) * 3328 ≤ 9 * 3328 := by
      have : B + 1 ≤ 9 := by omega
      exact Nat.mul_le_mul_right _ this
    omega
  have h_ub : a.val - t.val < (2 ^ 15 : Int) := by
    have h_natAbs : ((a.val - t.val : Int)).natAbs ≤ (B + 1) * 3328 := h_diff_abs
    have h_bound : (B + 1) * 3328 ≤ 9 * 3328 := by
      have : B + 1 ≤ 9 := by omega
      exact Nat.mul_le_mul_right _ this
    omega
  have h_bmod : Int.bmod (a.val - t.val) (2 ^ 16) = a.val - t.val := by
    apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
    · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
      exact le_trans h_const h_lb
    · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
      exact lt_of_lt_of_le h_ub h_const
  have h_val := Std.I16.wrapping_sub_val_eq a t
  refine ⟨?_, ?_⟩
  · rw [h_val, h_bmod]
  · rw [h_val, h_bmod]; exact h_diff_abs

/-- Specialised form (B = 3) — preserves the original signature for callers. -/
private theorem add_no_overflow_value (a t : Std.I16)
    (h_a : a.val.natAbs ≤ 3 * 3328) (h_t : t.val.natAbs ≤ 3328) :
    (Std.I16.wrapping_add a t).val = a.val + t.val
      ∧ (Std.I16.wrapping_add a t).val.natAbs ≤ 4 * 3328 :=
  add_no_overflow_value_B a t 3 h_a h_t (by decide)

/-- Specialised form (B = 3) — preserves the original signature for callers. -/
private theorem sub_no_overflow_value (a t : Std.I16)
    (h_a : a.val.natAbs ≤ 3 * 3328) (h_t : t.val.natAbs ≤ 3328) :
    (Std.I16.wrapping_sub a t).val = a.val - t.val
      ∧ (Std.I16.wrapping_sub a t).val.natAbs ≤ 4 * 3328 :=
  sub_no_overflow_value_B a t 3 h_a h_t (by decide)

/-! ### Truly bnd-parameterised no-overflow lemmas.

    `add_no_overflow_value_B` / `sub_no_overflow_value_B` are convenient when
    the lane bound has the multiplicative shape `B * 3328`. The L3.{1,2,3}_B
    parameterisation upstream needs an arbitrary `Nat` bound. The
    `_bnd` variants below replace `(B + 1) * 3328` with `bnd + 3328` and the
    `B + 1 ≤ 9` bridge with `bnd + 3328 ≤ 32767` directly (equivalent to
    `bnd ≤ 29439`). Numerically `29439 + 3328 = 32767 < 2^15`, so the I16
    wrapping is the identity. -/

/-- Under `|a.val| ≤ bnd`, `|t.val| ≤ 3328`, and `bnd ≤ 29439`, the I16-wrapped
    sum `a + t` has `.val = a.val + t.val` and `.val.natAbs ≤ bnd + 3328`. -/
private theorem add_no_overflow_value_bnd (a t : Std.I16) (bnd : Nat)
    (h_a : a.val.natAbs ≤ bnd) (h_t : t.val.natAbs ≤ 3328) (h_bnd : bnd ≤ 29439) :
    (Std.I16.wrapping_add a t).val = a.val + t.val
      ∧ (Std.I16.wrapping_add a t).val.natAbs ≤ bnd + 3328 := by
  -- |a + t| ≤ |a| + |t| ≤ bnd + 3328 ≤ 29439 + 3328 = 32767 < 2^15.
  have h_sum_abs : ((a.val + t.val : Int)).natAbs ≤ bnd + 3328 := by
    have h_tri : (a.val + t.val).natAbs ≤ a.val.natAbs + t.val.natAbs := Int.natAbs_add_le _ _
    omega
  -- No-overflow ⇒ bmod is identity.
  have h_lb : -(2 ^ 15 : Int) ≤ a.val + t.val := by
    have h_natAbs : ((a.val + t.val : Int)).natAbs ≤ bnd + 3328 := h_sum_abs
    have h_bound : bnd + 3328 ≤ 32767 := by omega
    omega
  have h_ub : a.val + t.val < (2 ^ 15 : Int) := by
    have h_natAbs : ((a.val + t.val : Int)).natAbs ≤ bnd + 3328 := h_sum_abs
    have h_bound : bnd + 3328 ≤ 32767 := by omega
    omega
  have h_bmod : Int.bmod (a.val + t.val) (2 ^ 16) = a.val + t.val := by
    apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
    · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
      exact le_trans h_const h_lb
    · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
      exact lt_of_lt_of_le h_ub h_const
  have h_val := Std.I16.wrapping_add_val_eq a t
  refine ⟨?_, ?_⟩
  · rw [h_val, h_bmod]
  · rw [h_val, h_bmod]; exact h_sum_abs

/-- Under `|a.val| ≤ bnd`, `|t.val| ≤ 3328`, and `bnd ≤ 29439`, the I16-wrapped
    diff `a - t` has `.val = a.val - t.val` and `.val.natAbs ≤ bnd + 3328`. -/
private theorem sub_no_overflow_value_bnd (a t : Std.I16) (bnd : Nat)
    (h_a : a.val.natAbs ≤ bnd) (h_t : t.val.natAbs ≤ 3328) (h_bnd : bnd ≤ 29439) :
    (Std.I16.wrapping_sub a t).val = a.val - t.val
      ∧ (Std.I16.wrapping_sub a t).val.natAbs ≤ bnd + 3328 := by
  have h_diff_abs : ((a.val - t.val : Int)).natAbs ≤ bnd + 3328 := by
    have h_neg_natAbs : (-t.val).natAbs = t.val.natAbs := Int.natAbs_neg _
    have h_eq : a.val - t.val = a.val + (-t.val) := by ring
    rw [h_eq]
    have h_tri : (a.val + (-t.val)).natAbs ≤ a.val.natAbs + (-t.val).natAbs :=
      Int.natAbs_add_le _ _
    rw [h_neg_natAbs] at h_tri
    omega
  have h_lb : -(2 ^ 15 : Int) ≤ a.val - t.val := by
    have h_natAbs : ((a.val - t.val : Int)).natAbs ≤ bnd + 3328 := h_diff_abs
    have h_bound : bnd + 3328 ≤ 32767 := by omega
    omega
  have h_ub : a.val - t.val < (2 ^ 15 : Int) := by
    have h_natAbs : ((a.val - t.val : Int)).natAbs ≤ bnd + 3328 := h_diff_abs
    have h_bound : bnd + 3328 ≤ 32767 := by omega
    omega
  have h_bmod : Int.bmod (a.val - t.val) (2 ^ 16) = a.val - t.val := by
    apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
    · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
      exact le_trans h_const h_lb
    · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
      exact lt_of_lt_of_le h_ub h_const
  have h_val := Std.I16.wrapping_sub_val_eq a t
  refine ⟨?_, ?_⟩
  · rw [h_val, h_bmod]
  · rw [h_val, h_bmod]; exact h_diff_abs

@[spec]
theorem ntt_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i j : Std.Usize)
    (h_i : i.val < 16) (h_j : j.val < 16) (h_ne : i.val ≠ j.val)
    (h_zeta : zeta.val.natAbs ≤ 1664)
    (h_a : (vec.elements.val[i.val]!).val.natAbs ≤ 3 * 3328)
    (h_b : (vec.elements.val[j.val]!).val.natAbs ≤ 3 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j
    ⦃ ⇓ r => ⌜ (∀ k : Nat, k < 16 → k ≠ i.val → k ≠ j.val →
                  r.elements.val[k]! = vec.elements.val[k]!)
              ∧ (r.elements.val[i.val]!).val.natAbs ≤ 4 * 3328
              ∧ (r.elements.val[j.val]!).val.natAbs ≤ 4 * 3328 ⌝ ⦄ := by
  have h_vec_len : vec.elements.length = 16 := PortableVector_elements_length vec
  -- Step 1: read vec[j].
  have h_idx_j :
      Aeneas.Std.Array.index_usize vec.elements j = .ok (vec.elements.val[j.val]!) :=
    array_index_usize_ok_eq vec.elements j (by rw [h_vec_len]; exact h_j)
  -- Step 2: classify ζ.
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify zeta = .ok zeta :=
    classify_ok_eq zeta
  -- Step 3: L0.4 montgomery_multiply on (vec[j], ζ).
  set b : Std.I16 := vec.elements.val[j.val]! with hb_def
  obtain ⟨t, h_t_eq_ok, h_t_bd, _h_t_mod⟩ :=
    triple_exists_ok_l2 (montgomery_multiply_fe_by_fer_spec b zeta h_zeta)
  -- Step 4: read vec[i].
  have h_idx_i :
      Aeneas.Std.Array.index_usize vec.elements i = .ok (vec.elements.val[i.val]!) :=
    array_index_usize_ok_eq vec.elements i (by rw [h_vec_len]; exact h_i)
  set a : Std.I16 := vec.elements.val[i.val]! with ha_def
  -- Step 5: wrapping_sub a t.
  have h_sub_eq : CoreModels.core.num.I16.wrapping_sub a t = .ok (Std.I16.wrapping_sub a t) :=
    cm_wrapping_sub_ok_eq a t
  -- Step 6: wrapping_add a t.
  have h_add_eq : CoreModels.core.num.I16.wrapping_add a t = .ok (Std.I16.wrapping_add a t) :=
    cm_wrapping_add_ok_eq a t
  set a_minus_t : Std.I16 := Std.I16.wrapping_sub a t with hamt_def
  set a_plus_t  : Std.I16 := Std.I16.wrapping_add a t with hapt_def
  -- Step 7: update vec at index j with a_minus_t.
  have h_upd_j :
      Aeneas.Std.Array.update vec.elements j a_minus_t
        = .ok (vec.elements.set j a_minus_t) :=
    array_update_ok_eq vec.elements j a_minus_t (by rw [h_vec_len]; exact h_j)
  -- Step 8: update at index i with a_plus_t.
  have h_upd_i :
      Aeneas.Std.Array.update (vec.elements.set j a_minus_t) i a_plus_t
        = .ok ((vec.elements.set j a_minus_t).set i a_plus_t) := by
    have h_len : (vec.elements.set j a_minus_t).length = 16 := by
      rw [Std.Array.set_length]; exact h_vec_len
    exact array_update_ok_eq _ i a_plus_t (by rw [h_len]; exact h_i)
  -- Compose the whole do-block into one `.ok` equation.
  set final_elements : Std.Array Std.I16 16#usize :=
    (vec.elements.set j a_minus_t).set i a_plus_t with hfe_def
  set final_vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    { elements := final_elements } with hfv_def
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j = .ok final_vec := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_step
    rw [h_idx_j]; simp only [bind_tc_ok]
    rw [h_classify]; simp only [bind_tc_ok]
    rw [h_t_eq_ok]; simp only [bind_tc_ok]
    rw [h_idx_i]; simp only [bind_tc_ok]
    rw [h_sub_eq]; simp only [bind_tc_ok]
    rw [h_add_eq]; simp only [bind_tc_ok]
    rw [h_upd_j]; simp only [bind_tc_ok]
    rw [h_upd_i]; simp only [bind_tc_ok]; rfl
  -- Bound facts on the two touched lanes.
  have h_add := add_no_overflow_value a t h_a h_t_bd
  have h_sub := sub_no_overflow_value a t h_a h_t_bd
  -- Close the Triple.
  apply triple_of_ok_l2 h_body
  refine ⟨?_, ?_, ?_⟩
  · -- Unchanged lanes: k ≠ i.val and k ≠ j.val.
    intro k hk_lt hk_ne_i hk_ne_j
    have h_set_i_ne :
        ((vec.elements.set j a_minus_t).set i a_plus_t)[k]!
          = (vec.elements.set j a_minus_t)[k]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ i k _ (Ne.symm hk_ne_i)
    have h_set_j_ne :
        (vec.elements.set j a_minus_t)[k]! = (vec.elements)[k]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ j k _ (Ne.symm hk_ne_j)
    show final_vec.elements.val[k]! = vec.elements.val[k]!
    show ((vec.elements.set j a_minus_t).set i a_plus_t).val[k]! = vec.elements.val[k]!
    -- Convert .val[k]! ↔ [k]! using getElem!_Nat_eq, then chain set_ne rewrites.
    rw [← Aeneas.Std.Array.getElem!_Nat_eq, ← Aeneas.Std.Array.getElem!_Nat_eq,
        h_set_i_ne, h_set_j_ne]
  · -- Bound on r.elements.val[i.val]!.
    show (final_vec.elements.val[i.val]!).val.natAbs ≤ 4 * 3328
    show (((vec.elements.set j a_minus_t).set i a_plus_t).val[i.val]!).val.natAbs ≤ 4 * 3328
    have h_eq1 :
        ((vec.elements.set j a_minus_t).set i a_plus_t).val[i.val]!
          = ((vec.elements.set j a_minus_t).set i a_plus_t)[i.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    have h_set_i_eq :
        ((vec.elements.set j a_minus_t).set i a_plus_t)[i.val]! = a_plus_t := by
      have h_len : (vec.elements.set j a_minus_t).length = 16 := by
        rw [Std.Array.set_length]; exact h_vec_len
      exact Aeneas.Std.Array.getElem!_Nat_set_eq _ i i.val _ ⟨rfl, by rw [h_len]; exact h_i⟩
    rw [h_eq1, h_set_i_eq]
    exact h_add.2
  · -- Bound on r.elements.val[j.val]!.
    show (final_vec.elements.val[j.val]!).val.natAbs ≤ 4 * 3328
    show (((vec.elements.set j a_minus_t).set i a_plus_t).val[j.val]!).val.natAbs ≤ 4 * 3328
    have h_eq1 :
        ((vec.elements.set j a_minus_t).set i a_plus_t).val[j.val]!
          = ((vec.elements.set j a_minus_t).set i a_plus_t)[j.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    have h_ne_ij : i.val ≠ j.val := h_ne
    have h_set_i_ne :
        ((vec.elements.set j a_minus_t).set i a_plus_t)[j.val]!
          = (vec.elements.set j a_minus_t)[j.val]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ i j.val _ h_ne_ij
    have h_set_j_eq :
        (vec.elements.set j a_minus_t)[j.val]! = a_minus_t := by
      exact Aeneas.Std.Array.getElem!_Nat_set_eq _ j j.val _ ⟨rfl, by rw [h_vec_len]; exact h_j⟩
    have h_eq2 :
        (vec.elements.set j a_minus_t)[j.val]!
          = (vec.elements.set j a_minus_t).val[j.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    rw [h_eq1, h_set_i_ne, h_set_j_eq]
    exact h_sub.2

/-! ## Parameterised L2.1 — `ntt_step_spec_B`

    Same shape as `ntt_step_spec` but with a configurable lane bound `B ≤ 8`.
    Each touched lane goes from `≤ B·3328` to `≤ (B+1)·3328`. Used by the
    L2.2/L2.3/L2.4 bundled-butterfly proofs which need different inbound
    bounds (7·3328 / 6·3328 / 5·3328 respectively).

    The proof body is identical to `ntt_step_spec` except that
    `add_no_overflow_value` / `sub_no_overflow_value` are replaced by their
    `_B` counterparts.

    `h_B : B ≤ 8` ensures no I16 overflow: `(B+1)·3328 ≤ 9·3328 = 29952 < 2^15`.
-/

@[spec]
theorem ntt_step_spec_B
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i j : Std.Usize) (B : Nat)
    (h_i : i.val < 16) (h_j : j.val < 16) (h_ne : i.val ≠ j.val)
    (h_zeta : zeta.val.natAbs ≤ 1664)
    (h_a : (vec.elements.val[i.val]!).val.natAbs ≤ B * 3328)
    (h_b : (vec.elements.val[j.val]!).val.natAbs ≤ B * 3328)
    (h_B : B ≤ 8) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j
    ⦃ ⇓ r => ⌜ (∀ k : Nat, k < 16 → k ≠ i.val → k ≠ j.val →
                  r.elements.val[k]! = vec.elements.val[k]!)
              ∧ (r.elements.val[i.val]!).val.natAbs ≤ (B + 1) * 3328
              ∧ (r.elements.val[j.val]!).val.natAbs ≤ (B + 1) * 3328 ⌝ ⦄ := by
  have h_vec_len : vec.elements.length = 16 := PortableVector_elements_length vec
  have h_idx_j :
      Aeneas.Std.Array.index_usize vec.elements j = .ok (vec.elements.val[j.val]!) :=
    array_index_usize_ok_eq vec.elements j (by rw [h_vec_len]; exact h_j)
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify zeta = .ok zeta :=
    classify_ok_eq zeta
  set b : Std.I16 := vec.elements.val[j.val]! with hb_def
  obtain ⟨t, h_t_eq_ok, h_t_bd, _h_t_mod⟩ :=
    triple_exists_ok_l2 (montgomery_multiply_fe_by_fer_spec b zeta h_zeta)
  have h_idx_i :
      Aeneas.Std.Array.index_usize vec.elements i = .ok (vec.elements.val[i.val]!) :=
    array_index_usize_ok_eq vec.elements i (by rw [h_vec_len]; exact h_i)
  set a : Std.I16 := vec.elements.val[i.val]! with ha_def
  have h_sub_eq : CoreModels.core.num.I16.wrapping_sub a t = .ok (Std.I16.wrapping_sub a t) :=
    cm_wrapping_sub_ok_eq a t
  have h_add_eq : CoreModels.core.num.I16.wrapping_add a t = .ok (Std.I16.wrapping_add a t) :=
    cm_wrapping_add_ok_eq a t
  set a_minus_t : Std.I16 := Std.I16.wrapping_sub a t with hamt_def
  set a_plus_t  : Std.I16 := Std.I16.wrapping_add a t with hapt_def
  have h_upd_j :
      Aeneas.Std.Array.update vec.elements j a_minus_t
        = .ok (vec.elements.set j a_minus_t) :=
    array_update_ok_eq vec.elements j a_minus_t (by rw [h_vec_len]; exact h_j)
  have h_upd_i :
      Aeneas.Std.Array.update (vec.elements.set j a_minus_t) i a_plus_t
        = .ok ((vec.elements.set j a_minus_t).set i a_plus_t) := by
    have h_len : (vec.elements.set j a_minus_t).length = 16 := by
      rw [Std.Array.set_length]; exact h_vec_len
    exact array_update_ok_eq _ i a_plus_t (by rw [h_len]; exact h_i)
  set final_elements : Std.Array Std.I16 16#usize :=
    (vec.elements.set j a_minus_t).set i a_plus_t with hfe_def
  set final_vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    { elements := final_elements } with hfv_def
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j = .ok final_vec := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_step
    rw [h_idx_j]; simp only [bind_tc_ok]
    rw [h_classify]; simp only [bind_tc_ok]
    rw [h_t_eq_ok]; simp only [bind_tc_ok]
    rw [h_idx_i]; simp only [bind_tc_ok]
    rw [h_sub_eq]; simp only [bind_tc_ok]
    rw [h_add_eq]; simp only [bind_tc_ok]
    rw [h_upd_j]; simp only [bind_tc_ok]
    rw [h_upd_i]; simp only [bind_tc_ok]; rfl
  have h_add := add_no_overflow_value_B a t B h_a h_t_bd h_B
  have h_sub := sub_no_overflow_value_B a t B h_a h_t_bd h_B
  apply triple_of_ok_l2 h_body
  refine ⟨?_, ?_, ?_⟩
  · intro k hk_lt hk_ne_i hk_ne_j
    have h_set_i_ne :
        ((vec.elements.set j a_minus_t).set i a_plus_t)[k]!
          = (vec.elements.set j a_minus_t)[k]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ i k _ (Ne.symm hk_ne_i)
    have h_set_j_ne :
        (vec.elements.set j a_minus_t)[k]! = (vec.elements)[k]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ j k _ (Ne.symm hk_ne_j)
    show final_vec.elements.val[k]! = vec.elements.val[k]!
    show ((vec.elements.set j a_minus_t).set i a_plus_t).val[k]! = vec.elements.val[k]!
    rw [← Aeneas.Std.Array.getElem!_Nat_eq, ← Aeneas.Std.Array.getElem!_Nat_eq,
        h_set_i_ne, h_set_j_ne]
  · show (final_vec.elements.val[i.val]!).val.natAbs ≤ (B + 1) * 3328
    show (((vec.elements.set j a_minus_t).set i a_plus_t).val[i.val]!).val.natAbs ≤ (B + 1) * 3328
    have h_eq1 :
        ((vec.elements.set j a_minus_t).set i a_plus_t).val[i.val]!
          = ((vec.elements.set j a_minus_t).set i a_plus_t)[i.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    have h_set_i_eq :
        ((vec.elements.set j a_minus_t).set i a_plus_t)[i.val]! = a_plus_t := by
      have h_len : (vec.elements.set j a_minus_t).length = 16 := by
        rw [Std.Array.set_length]; exact h_vec_len
      exact Aeneas.Std.Array.getElem!_Nat_set_eq _ i i.val _ ⟨rfl, by rw [h_len]; exact h_i⟩
    rw [h_eq1, h_set_i_eq]
    exact h_add.2
  · show (final_vec.elements.val[j.val]!).val.natAbs ≤ (B + 1) * 3328
    show (((vec.elements.set j a_minus_t).set i a_plus_t).val[j.val]!).val.natAbs ≤ (B + 1) * 3328
    have h_eq1 :
        ((vec.elements.set j a_minus_t).set i a_plus_t).val[j.val]!
          = ((vec.elements.set j a_minus_t).set i a_plus_t)[j.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    have h_ne_ij : i.val ≠ j.val := h_ne
    have h_set_i_ne :
        ((vec.elements.set j a_minus_t).set i a_plus_t)[j.val]!
          = (vec.elements.set j a_minus_t)[j.val]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ i j.val _ h_ne_ij
    have h_set_j_eq :
        (vec.elements.set j a_minus_t)[j.val]! = a_minus_t := by
      exact Aeneas.Std.Array.getElem!_Nat_set_eq _ j j.val _ ⟨rfl, by rw [h_vec_len]; exact h_j⟩
    have h_eq2 :
        (vec.elements.set j a_minus_t)[j.val]!
          = (vec.elements.set j a_minus_t).val[j.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    rw [h_eq1, h_set_i_ne, h_set_j_eq]
    exact h_sub.2

/-! ## Truly bnd-parameterised L2.1 — `ntt_step_spec_bnd`

    Same shape as `ntt_step_spec_B` but with the lane bound stated as a raw
    `Nat` `bnd` (instead of `B * 3328`). Used by the `L3.{1,2,3}_B`
    parameterisations which carry an `bnd : Nat` invariant rather than a
    multiplicative `B * 3328` shape.

    The proof body mirrors `ntt_step_spec_B` exactly, swapping the calls to
    `add_no_overflow_value_B` / `sub_no_overflow_value_B` for their `_bnd`
    counterparts and the `B ≤ 8` precondition for `bnd ≤ 29439`.

    The bound `29439 = 32767 - 3328` ensures `(bnd + 3328) ≤ 32767 < 2^15`,
    so the I16 wrapping is the identity for both `a + t` and `a - t`. -/

@[spec]
theorem ntt_step_spec_bnd
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i j : Std.Usize) (bnd : Nat)
    (h_i : i.val < 16) (h_j : j.val < 16) (h_ne : i.val ≠ j.val)
    (h_zeta : zeta.val.natAbs ≤ 1664)
    (h_a : (vec.elements.val[i.val]!).val.natAbs ≤ bnd)
    (h_b : (vec.elements.val[j.val]!).val.natAbs ≤ bnd)
    (h_bnd : bnd ≤ 29439) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j
    ⦃ ⇓ r => ⌜ (∀ k : Nat, k < 16 → k ≠ i.val → k ≠ j.val →
                  r.elements.val[k]! = vec.elements.val[k]!)
              ∧ (r.elements.val[i.val]!).val.natAbs ≤ bnd + 3328
              ∧ (r.elements.val[j.val]!).val.natAbs ≤ bnd + 3328 ⌝ ⦄ := by
  have h_vec_len : vec.elements.length = 16 := PortableVector_elements_length vec
  have h_idx_j :
      Aeneas.Std.Array.index_usize vec.elements j = .ok (vec.elements.val[j.val]!) :=
    array_index_usize_ok_eq vec.elements j (by rw [h_vec_len]; exact h_j)
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify zeta = .ok zeta :=
    classify_ok_eq zeta
  set b : Std.I16 := vec.elements.val[j.val]! with hb_def
  obtain ⟨t, h_t_eq_ok, h_t_bd, _h_t_mod⟩ :=
    triple_exists_ok_l2 (montgomery_multiply_fe_by_fer_spec b zeta h_zeta)
  have h_idx_i :
      Aeneas.Std.Array.index_usize vec.elements i = .ok (vec.elements.val[i.val]!) :=
    array_index_usize_ok_eq vec.elements i (by rw [h_vec_len]; exact h_i)
  set a : Std.I16 := vec.elements.val[i.val]! with ha_def
  have h_sub_eq : CoreModels.core.num.I16.wrapping_sub a t = .ok (Std.I16.wrapping_sub a t) :=
    cm_wrapping_sub_ok_eq a t
  have h_add_eq : CoreModels.core.num.I16.wrapping_add a t = .ok (Std.I16.wrapping_add a t) :=
    cm_wrapping_add_ok_eq a t
  set a_minus_t : Std.I16 := Std.I16.wrapping_sub a t with hamt_def
  set a_plus_t  : Std.I16 := Std.I16.wrapping_add a t with hapt_def
  have h_upd_j :
      Aeneas.Std.Array.update vec.elements j a_minus_t
        = .ok (vec.elements.set j a_minus_t) :=
    array_update_ok_eq vec.elements j a_minus_t (by rw [h_vec_len]; exact h_j)
  have h_upd_i :
      Aeneas.Std.Array.update (vec.elements.set j a_minus_t) i a_plus_t
        = .ok ((vec.elements.set j a_minus_t).set i a_plus_t) := by
    have h_len : (vec.elements.set j a_minus_t).length = 16 := by
      rw [Std.Array.set_length]; exact h_vec_len
    exact array_update_ok_eq _ i a_plus_t (by rw [h_len]; exact h_i)
  set final_elements : Std.Array Std.I16 16#usize :=
    (vec.elements.set j a_minus_t).set i a_plus_t with hfe_def
  set final_vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    { elements := final_elements } with hfv_def
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j = .ok final_vec := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_step
    rw [h_idx_j]; simp only [bind_tc_ok]
    rw [h_classify]; simp only [bind_tc_ok]
    rw [h_t_eq_ok]; simp only [bind_tc_ok]
    rw [h_idx_i]; simp only [bind_tc_ok]
    rw [h_sub_eq]; simp only [bind_tc_ok]
    rw [h_add_eq]; simp only [bind_tc_ok]
    rw [h_upd_j]; simp only [bind_tc_ok]
    rw [h_upd_i]; simp only [bind_tc_ok]; rfl
  have h_add := add_no_overflow_value_bnd a t bnd h_a h_t_bd h_bnd
  have h_sub := sub_no_overflow_value_bnd a t bnd h_a h_t_bd h_bnd
  apply triple_of_ok_l2 h_body
  refine ⟨?_, ?_, ?_⟩
  · intro k hk_lt hk_ne_i hk_ne_j
    have h_set_i_ne :
        ((vec.elements.set j a_minus_t).set i a_plus_t)[k]!
          = (vec.elements.set j a_minus_t)[k]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ i k _ (Ne.symm hk_ne_i)
    have h_set_j_ne :
        (vec.elements.set j a_minus_t)[k]! = (vec.elements)[k]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ j k _ (Ne.symm hk_ne_j)
    show final_vec.elements.val[k]! = vec.elements.val[k]!
    show ((vec.elements.set j a_minus_t).set i a_plus_t).val[k]! = vec.elements.val[k]!
    rw [← Aeneas.Std.Array.getElem!_Nat_eq, ← Aeneas.Std.Array.getElem!_Nat_eq,
        h_set_i_ne, h_set_j_ne]
  · show (final_vec.elements.val[i.val]!).val.natAbs ≤ bnd + 3328
    show (((vec.elements.set j a_minus_t).set i a_plus_t).val[i.val]!).val.natAbs ≤ bnd + 3328
    have h_eq1 :
        ((vec.elements.set j a_minus_t).set i a_plus_t).val[i.val]!
          = ((vec.elements.set j a_minus_t).set i a_plus_t)[i.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    have h_set_i_eq :
        ((vec.elements.set j a_minus_t).set i a_plus_t)[i.val]! = a_plus_t := by
      have h_len : (vec.elements.set j a_minus_t).length = 16 := by
        rw [Std.Array.set_length]; exact h_vec_len
      exact Aeneas.Std.Array.getElem!_Nat_set_eq _ i i.val _ ⟨rfl, by rw [h_len]; exact h_i⟩
    rw [h_eq1, h_set_i_eq]
    exact h_add.2
  · show (final_vec.elements.val[j.val]!).val.natAbs ≤ bnd + 3328
    show (((vec.elements.set j a_minus_t).set i a_plus_t).val[j.val]!).val.natAbs ≤ bnd + 3328
    have h_eq1 :
        ((vec.elements.set j a_minus_t).set i a_plus_t).val[j.val]!
          = ((vec.elements.set j a_minus_t).set i a_plus_t)[j.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    have h_ne_ij : i.val ≠ j.val := h_ne
    have h_set_i_ne :
        ((vec.elements.set j a_minus_t).set i a_plus_t)[j.val]!
          = (vec.elements.set j a_minus_t)[j.val]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ i j.val _ h_ne_ij
    have h_set_j_eq :
        (vec.elements.set j a_minus_t)[j.val]! = a_minus_t := by
      exact Aeneas.Std.Array.getElem!_Nat_set_eq _ j j.val _ ⟨rfl, by rw [h_vec_len]; exact h_j⟩
    have h_eq2 :
        (vec.elements.set j a_minus_t)[j.val]!
          = (vec.elements.set j a_minus_t).val[j.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    rw [h_eq1, h_set_i_ne, h_set_j_eq]
    exact h_sub.2

/-! ## L2.2 — `ntt_layer_1_step_spec`

    Eight disjoint butterflies on pairs `(0,2)ζ0`, `(1,3)ζ0`, `(4,6)ζ1`,
    `(5,7)ζ1`, `(8,10)ζ2`, `(9,11)ζ2`, `(12,14)ζ3`, `(13,15)ζ3`. Each call
    of `ntt_step_spec_B` with `B = 7` raises the two touched lanes from
    `≤ 7·3328` to `≤ 8·3328`; pairs are pairwise disjoint and cover all
    16 lanes, so every lane is touched exactly once.

    Bookkeeping idiom: we maintain, after the k-th call, the invariant
    "for every lane index ℓ ∈ [0,16), if ℓ is among the lanes touched
    so far, lane_k[ℓ] ≤ 8·3328; else lane_k[ℓ] = vec[ℓ] (and so
    ≤ 7·3328 ≤ 8·3328)". The post conjuncts of `ntt_step_spec_B`
    immediately give us each step's contribution.
-/

@[spec]
theorem ntt_layer_1_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta0 zeta1 zeta2 zeta3 : Std.I16)
    (hz0 : zeta0.val.natAbs ≤ 1664) (hz1 : zeta1.val.natAbs ≤ 1664)
    (hz2 : zeta2.val.natAbs ≤ 1664) (hz3 : zeta3.val.natAbs ≤ 1664)
    (hpre : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 7 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ 8 * 3328 ⌝ ⦄ := by
  -- Index abbreviations.
  have h0lt : (0#usize : Std.Usize).val < 16 := by decide
  have h1lt : (1#usize : Std.Usize).val < 16 := by decide
  have h2lt : (2#usize : Std.Usize).val < 16 := by decide
  have h3lt : (3#usize : Std.Usize).val < 16 := by decide
  have h4lt : (4#usize : Std.Usize).val < 16 := by decide
  have h5lt : (5#usize : Std.Usize).val < 16 := by decide
  have h6lt : (6#usize : Std.Usize).val < 16 := by decide
  have h7lt : (7#usize : Std.Usize).val < 16 := by decide
  have h8lt : (8#usize : Std.Usize).val < 16 := by decide
  have h9lt : (9#usize : Std.Usize).val < 16 := by decide
  have h10lt : (10#usize : Std.Usize).val < 16 := by decide
  have h11lt : (11#usize : Std.Usize).val < 16 := by decide
  have h12lt : (12#usize : Std.Usize).val < 16 := by decide
  have h13lt : (13#usize : Std.Usize).val < 16 := by decide
  have h14lt : (14#usize : Std.Usize).val < 16 := by decide
  have h15lt : (15#usize : Std.Usize).val < 16 := by decide
  -- Initial bounds: hpre gives ≤ 7·3328 on all lanes.
  have hb_init : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 7 * 3328 := hpre
  -- Step 1: (0, 2) ζ0. Pair untouched ⇒ both lanes ≤ 7·3328 from hpre.
  obtain ⟨v1, h_v1_eq, h_v1_unc, h_v1_i, h_v1_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B vec zeta0 0#usize 2#usize 7
      h0lt h2lt (by decide) hz0 (hb_init 0 h0lt) (hb_init 2 h2lt) (by decide))
  -- After step 1: lane 0 and lane 2 are ≤ 8·3328 (h_v1_i, h_v1_j); other lanes
  -- unchanged from vec (h_v1_unc), so still ≤ 7·3328 from hpre.
  -- Step 2: (1, 3) ζ0. Disjoint from {0, 2}, so lanes 1, 3 are still vec[1], vec[3] ≤ 7·3328.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v1_unc 1 h1lt (by decide) (by decide)]; exact hb_init 1 h1lt
  have h_v1_3 : (v1.elements.val[3]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v1_unc 3 h3lt (by decide) (by decide)]; exact hb_init 3 h3lt
  obtain ⟨v2, h_v2_eq, h_v2_unc, h_v2_i, h_v2_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v1 zeta0 1#usize 3#usize 7
      h1lt h3lt (by decide) hz0 h_v1_1 h_v1_3 (by decide))
  -- Step 3: (4, 6) ζ1. v2[4], v2[6] not touched in steps 1,2 ⇒ = vec[4], vec[6] ≤ 7·3328.
  have h_v2_4 : (v2.elements.val[4]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v2_unc 4 h4lt (by decide) (by decide), h_v1_unc 4 h4lt (by decide) (by decide)]
    exact hb_init 4 h4lt
  have h_v2_6 : (v2.elements.val[6]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v2_unc 6 h6lt (by decide) (by decide), h_v1_unc 6 h6lt (by decide) (by decide)]
    exact hb_init 6 h6lt
  obtain ⟨v3, h_v3_eq, h_v3_unc, h_v3_i, h_v3_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v2 zeta1 4#usize 6#usize 7
      h4lt h6lt (by decide) hz1 h_v2_4 h_v2_6 (by decide))
  -- Step 4: (5, 7) ζ1.
  have h_v3_5 : (v3.elements.val[5]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v3_unc 5 h5lt (by decide) (by decide),
        h_v2_unc 5 h5lt (by decide) (by decide),
        h_v1_unc 5 h5lt (by decide) (by decide)]
    exact hb_init 5 h5lt
  have h_v3_7 : (v3.elements.val[7]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v3_unc 7 h7lt (by decide) (by decide),
        h_v2_unc 7 h7lt (by decide) (by decide),
        h_v1_unc 7 h7lt (by decide) (by decide)]
    exact hb_init 7 h7lt
  obtain ⟨v4, h_v4_eq, h_v4_unc, h_v4_i, h_v4_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v3 zeta1 5#usize 7#usize 7
      h5lt h7lt (by decide) hz1 h_v3_5 h_v3_7 (by decide))
  -- Step 5: (8, 10) ζ2.
  have h_v4_8 : (v4.elements.val[8]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v4_unc 8 h8lt (by decide) (by decide),
        h_v3_unc 8 h8lt (by decide) (by decide),
        h_v2_unc 8 h8lt (by decide) (by decide),
        h_v1_unc 8 h8lt (by decide) (by decide)]
    exact hb_init 8 h8lt
  have h_v4_10 : (v4.elements.val[10]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v4_unc 10 h10lt (by decide) (by decide),
        h_v3_unc 10 h10lt (by decide) (by decide),
        h_v2_unc 10 h10lt (by decide) (by decide),
        h_v1_unc 10 h10lt (by decide) (by decide)]
    exact hb_init 10 h10lt
  obtain ⟨v5, h_v5_eq, h_v5_unc, h_v5_i, h_v5_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v4 zeta2 8#usize 10#usize 7
      h8lt h10lt (by decide) hz2 h_v4_8 h_v4_10 (by decide))
  -- Step 6: (9, 11) ζ2.
  have h_v5_9 : (v5.elements.val[9]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v5_unc 9 h9lt (by decide) (by decide),
        h_v4_unc 9 h9lt (by decide) (by decide),
        h_v3_unc 9 h9lt (by decide) (by decide),
        h_v2_unc 9 h9lt (by decide) (by decide),
        h_v1_unc 9 h9lt (by decide) (by decide)]
    exact hb_init 9 h9lt
  have h_v5_11 : (v5.elements.val[11]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v5_unc 11 h11lt (by decide) (by decide),
        h_v4_unc 11 h11lt (by decide) (by decide),
        h_v3_unc 11 h11lt (by decide) (by decide),
        h_v2_unc 11 h11lt (by decide) (by decide),
        h_v1_unc 11 h11lt (by decide) (by decide)]
    exact hb_init 11 h11lt
  obtain ⟨v6, h_v6_eq, h_v6_unc, h_v6_i, h_v6_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v5 zeta2 9#usize 11#usize 7
      h9lt h11lt (by decide) hz2 h_v5_9 h_v5_11 (by decide))
  -- Step 7: (12, 14) ζ3.
  have h_v6_12 : (v6.elements.val[12]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v6_unc 12 h12lt (by decide) (by decide),
        h_v5_unc 12 h12lt (by decide) (by decide),
        h_v4_unc 12 h12lt (by decide) (by decide),
        h_v3_unc 12 h12lt (by decide) (by decide),
        h_v2_unc 12 h12lt (by decide) (by decide),
        h_v1_unc 12 h12lt (by decide) (by decide)]
    exact hb_init 12 h12lt
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v6_unc 14 h14lt (by decide) (by decide),
        h_v5_unc 14 h14lt (by decide) (by decide),
        h_v4_unc 14 h14lt (by decide) (by decide),
        h_v3_unc 14 h14lt (by decide) (by decide),
        h_v2_unc 14 h14lt (by decide) (by decide),
        h_v1_unc 14 h14lt (by decide) (by decide)]
    exact hb_init 14 h14lt
  obtain ⟨v7, h_v7_eq, h_v7_unc, h_v7_i, h_v7_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v6 zeta3 12#usize 14#usize 7
      h12lt h14lt (by decide) hz3 h_v6_12 h_v6_14 (by decide))
  -- Step 8: (13, 15) ζ3.
  have h_v7_13 : (v7.elements.val[13]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v7_unc 13 h13lt (by decide) (by decide),
        h_v6_unc 13 h13lt (by decide) (by decide),
        h_v5_unc 13 h13lt (by decide) (by decide),
        h_v4_unc 13 h13lt (by decide) (by decide),
        h_v3_unc 13 h13lt (by decide) (by decide),
        h_v2_unc 13 h13lt (by decide) (by decide),
        h_v1_unc 13 h13lt (by decide) (by decide)]
    exact hb_init 13 h13lt
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 7 * 3328 := by
    rw [h_v7_unc 15 h15lt (by decide) (by decide),
        h_v6_unc 15 h15lt (by decide) (by decide),
        h_v5_unc 15 h15lt (by decide) (by decide),
        h_v4_unc 15 h15lt (by decide) (by decide),
        h_v3_unc 15 h15lt (by decide) (by decide),
        h_v2_unc 15 h15lt (by decide) (by decide),
        h_v1_unc 15 h15lt (by decide) (by decide)]
    exact hb_init 15 h15lt
  obtain ⟨v8, h_v8_eq, h_v8_unc, h_v8_i, h_v8_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v7 zeta3 13#usize 15#usize 7
      h13lt h15lt (by decide) hz3 h_v7_13 h_v7_15 (by decide))
  -- Compose the whole 8-step chain into one `.ok v8` equation.
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3
        = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step
    rw [h_v1_eq]; simp only [bind_tc_ok]
    rw [h_v2_eq]; simp only [bind_tc_ok]
    rw [h_v3_eq]; simp only [bind_tc_ok]
    rw [h_v4_eq]; simp only [bind_tc_ok]
    rw [h_v5_eq]; simp only [bind_tc_ok]
    rw [h_v6_eq]; simp only [bind_tc_ok]
    rw [h_v7_eq]; simp only [bind_tc_ok]
    exact h_v8_eq
  -- Close the Triple: prove every lane ≤ 8·3328 by case-split on which step touched it.
  -- Strategy: for each lane ℓ, identify the step that touched it (giving h_v{k}_i or h_v{k}_j
  -- with bound ≤ 8·3328), then propagate v_k[ℓ] = ... = v8[ℓ] via the later steps' h_v{m}_unc.
  apply triple_of_ok_l2 h_body
  intro i hi
  interval_cases i
  -- Lane 0: touched in step 1 as i-lane ⇒ v1[0] ≤ 8·3328. v8[0] = v1[0].
  · have h_eq : v8.elements.val[0]! = v1.elements.val[0]! := by
      rw [h_v8_unc 0 h0lt (by decide) (by decide),
          h_v7_unc 0 h0lt (by decide) (by decide),
          h_v6_unc 0 h0lt (by decide) (by decide),
          h_v5_unc 0 h0lt (by decide) (by decide),
          h_v4_unc 0 h0lt (by decide) (by decide),
          h_v3_unc 0 h0lt (by decide) (by decide),
          h_v2_unc 0 h0lt (by decide) (by decide)]
    rw [h_eq]; exact h_v1_i
  -- Lane 1: touched in step 2 as i-lane.
  · have h_eq : v8.elements.val[1]! = v2.elements.val[1]! := by
      rw [h_v8_unc 1 h1lt (by decide) (by decide),
          h_v7_unc 1 h1lt (by decide) (by decide),
          h_v6_unc 1 h1lt (by decide) (by decide),
          h_v5_unc 1 h1lt (by decide) (by decide),
          h_v4_unc 1 h1lt (by decide) (by decide),
          h_v3_unc 1 h1lt (by decide) (by decide)]
    rw [h_eq]; exact h_v2_i
  -- Lane 2: touched in step 1 as j-lane.
  · have h_eq : v8.elements.val[2]! = v1.elements.val[2]! := by
      rw [h_v8_unc 2 h2lt (by decide) (by decide),
          h_v7_unc 2 h2lt (by decide) (by decide),
          h_v6_unc 2 h2lt (by decide) (by decide),
          h_v5_unc 2 h2lt (by decide) (by decide),
          h_v4_unc 2 h2lt (by decide) (by decide),
          h_v3_unc 2 h2lt (by decide) (by decide),
          h_v2_unc 2 h2lt (by decide) (by decide)]
    rw [h_eq]; exact h_v1_j
  -- Lane 3: touched in step 2 as j-lane.
  · have h_eq : v8.elements.val[3]! = v2.elements.val[3]! := by
      rw [h_v8_unc 3 h3lt (by decide) (by decide),
          h_v7_unc 3 h3lt (by decide) (by decide),
          h_v6_unc 3 h3lt (by decide) (by decide),
          h_v5_unc 3 h3lt (by decide) (by decide),
          h_v4_unc 3 h3lt (by decide) (by decide),
          h_v3_unc 3 h3lt (by decide) (by decide)]
    rw [h_eq]; exact h_v2_j
  -- Lane 4: touched in step 3 as i-lane.
  · have h_eq : v8.elements.val[4]! = v3.elements.val[4]! := by
      rw [h_v8_unc 4 h4lt (by decide) (by decide),
          h_v7_unc 4 h4lt (by decide) (by decide),
          h_v6_unc 4 h4lt (by decide) (by decide),
          h_v5_unc 4 h4lt (by decide) (by decide),
          h_v4_unc 4 h4lt (by decide) (by decide)]
    rw [h_eq]; exact h_v3_i
  -- Lane 5: touched in step 4 as i-lane.
  · have h_eq : v8.elements.val[5]! = v4.elements.val[5]! := by
      rw [h_v8_unc 5 h5lt (by decide) (by decide),
          h_v7_unc 5 h5lt (by decide) (by decide),
          h_v6_unc 5 h5lt (by decide) (by decide),
          h_v5_unc 5 h5lt (by decide) (by decide)]
    rw [h_eq]; exact h_v4_i
  -- Lane 6: touched in step 3 as j-lane.
  · have h_eq : v8.elements.val[6]! = v3.elements.val[6]! := by
      rw [h_v8_unc 6 h6lt (by decide) (by decide),
          h_v7_unc 6 h6lt (by decide) (by decide),
          h_v6_unc 6 h6lt (by decide) (by decide),
          h_v5_unc 6 h6lt (by decide) (by decide),
          h_v4_unc 6 h6lt (by decide) (by decide)]
    rw [h_eq]; exact h_v3_j
  -- Lane 7: touched in step 4 as j-lane.
  · have h_eq : v8.elements.val[7]! = v4.elements.val[7]! := by
      rw [h_v8_unc 7 h7lt (by decide) (by decide),
          h_v7_unc 7 h7lt (by decide) (by decide),
          h_v6_unc 7 h7lt (by decide) (by decide),
          h_v5_unc 7 h7lt (by decide) (by decide)]
    rw [h_eq]; exact h_v4_j
  -- Lane 8: touched in step 5 as i-lane.
  · have h_eq : v8.elements.val[8]! = v5.elements.val[8]! := by
      rw [h_v8_unc 8 h8lt (by decide) (by decide),
          h_v7_unc 8 h8lt (by decide) (by decide),
          h_v6_unc 8 h8lt (by decide) (by decide)]
    rw [h_eq]; exact h_v5_i
  -- Lane 9: touched in step 6 as i-lane.
  · have h_eq : v8.elements.val[9]! = v6.elements.val[9]! := by
      rw [h_v8_unc 9 h9lt (by decide) (by decide),
          h_v7_unc 9 h9lt (by decide) (by decide)]
    rw [h_eq]; exact h_v6_i
  -- Lane 10: touched in step 5 as j-lane.
  · have h_eq : v8.elements.val[10]! = v5.elements.val[10]! := by
      rw [h_v8_unc 10 h10lt (by decide) (by decide),
          h_v7_unc 10 h10lt (by decide) (by decide),
          h_v6_unc 10 h10lt (by decide) (by decide)]
    rw [h_eq]; exact h_v5_j
  -- Lane 11: touched in step 6 as j-lane.
  · have h_eq : v8.elements.val[11]! = v6.elements.val[11]! := by
      rw [h_v8_unc 11 h11lt (by decide) (by decide),
          h_v7_unc 11 h11lt (by decide) (by decide)]
    rw [h_eq]; exact h_v6_j
  -- Lane 12: touched in step 7 as i-lane.
  · have h_eq : v8.elements.val[12]! = v7.elements.val[12]! := by
      rw [h_v8_unc 12 h12lt (by decide) (by decide)]
    rw [h_eq]; exact h_v7_i
  -- Lane 13: touched in step 8 as i-lane.
  · exact h_v8_i
  -- Lane 14: touched in step 7 as j-lane.
  · have h_eq : v8.elements.val[14]! = v7.elements.val[14]! := by
      rw [h_v8_unc 14 h14lt (by decide) (by decide)]
    rw [h_eq]; exact h_v7_j
  -- Lane 15: touched in step 8 as j-lane.
  · exact h_v8_j

/-! ## L2.2.bnd — `ntt_layer_1_step_spec_bnd`

    Nat-bnd parameterised mirror of `ntt_layer_1_step_spec` (L2.2): same eight
    disjoint butterflies on pairs `(0,2)ζ0`, `(1,3)ζ0`, `(4,6)ζ1`, `(5,7)ζ1`,
    `(8,10)ζ2`, `(9,11)ζ2`, `(12,14)ζ3`, `(13,15)ζ3`, dispatched via the
    `_bnd` form of the per-butterfly Triple. Each call raises the two touched
    lanes from `≤ bnd` to `≤ bnd + 3328`.

    Precondition `bnd ≤ 8 * 3328 = 26624` keeps the output bound
    `bnd + 3328 ≤ 9 * 3328 = 29952` within `ntt_step_spec_bnd`'s safe range
    (`bnd' ≤ 29439` for the I16 no-overflow argument); `26624 ≤ 29439`.
-/

@[spec]
theorem ntt_layer_1_step_spec_bnd
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta0 zeta1 zeta2 zeta3 : Std.I16)
    (bnd : Nat) (h_bnd : bnd ≤ 29439)
    (hz0 : zeta0.val.natAbs ≤ 1664) (hz1 : zeta1.val.natAbs ≤ 1664)
    (hz2 : zeta2.val.natAbs ≤ 1664) (hz3 : zeta3.val.natAbs ≤ 1664)
    (hpre : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ bnd) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ bnd + 3328 ⌝ ⦄ := by
  -- Index abbreviations.
  have h0lt : (0#usize : Std.Usize).val < 16 := by decide
  have h1lt : (1#usize : Std.Usize).val < 16 := by decide
  have h2lt : (2#usize : Std.Usize).val < 16 := by decide
  have h3lt : (3#usize : Std.Usize).val < 16 := by decide
  have h4lt : (4#usize : Std.Usize).val < 16 := by decide
  have h5lt : (5#usize : Std.Usize).val < 16 := by decide
  have h6lt : (6#usize : Std.Usize).val < 16 := by decide
  have h7lt : (7#usize : Std.Usize).val < 16 := by decide
  have h8lt : (8#usize : Std.Usize).val < 16 := by decide
  have h9lt : (9#usize : Std.Usize).val < 16 := by decide
  have h10lt : (10#usize : Std.Usize).val < 16 := by decide
  have h11lt : (11#usize : Std.Usize).val < 16 := by decide
  have h12lt : (12#usize : Std.Usize).val < 16 := by decide
  have h13lt : (13#usize : Std.Usize).val < 16 := by decide
  have h14lt : (14#usize : Std.Usize).val < 16 := by decide
  have h15lt : (15#usize : Std.Usize).val < 16 := by decide
  -- Bridge: bnd ≤ 8*3328 = 26624 ≤ 29439 (= ntt_step_spec_bnd's max input bound).
  have h_bnd29439 : bnd ≤ 29439 := by omega
  -- Initial bounds: hpre gives ≤ bnd on all lanes.
  have hb_init : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ bnd := hpre
  -- Step 1: (0, 2) ζ0. Pair untouched ⇒ both lanes ≤ bnd from hpre.
  obtain ⟨v1, h_v1_eq, h_v1_unc, h_v1_i, h_v1_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd vec zeta0 0#usize 2#usize bnd
      h0lt h2lt (by decide) hz0 (hb_init 0 h0lt) (hb_init 2 h2lt) h_bnd29439)
  -- After step 1: lane 0 and lane 2 are ≤ bnd + 3328 (h_v1_i, h_v1_j); other lanes
  -- unchanged from vec (h_v1_unc), so still ≤ bnd from hpre.
  -- Step 2: (1, 3) ζ0. Disjoint from {0, 2}, so lanes 1, 3 are still vec[1], vec[3] ≤ bnd.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ bnd := by
    rw [h_v1_unc 1 h1lt (by decide) (by decide)]; exact hb_init 1 h1lt
  have h_v1_3 : (v1.elements.val[3]!).val.natAbs ≤ bnd := by
    rw [h_v1_unc 3 h3lt (by decide) (by decide)]; exact hb_init 3 h3lt
  obtain ⟨v2, h_v2_eq, h_v2_unc, h_v2_i, h_v2_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v1 zeta0 1#usize 3#usize bnd
      h1lt h3lt (by decide) hz0 h_v1_1 h_v1_3 h_bnd29439)
  -- Step 3: (4, 6) ζ1. v2[4], v2[6] not touched in steps 1,2 ⇒ = vec[4], vec[6] ≤ bnd.
  have h_v2_4 : (v2.elements.val[4]!).val.natAbs ≤ bnd := by
    rw [h_v2_unc 4 h4lt (by decide) (by decide), h_v1_unc 4 h4lt (by decide) (by decide)]
    exact hb_init 4 h4lt
  have h_v2_6 : (v2.elements.val[6]!).val.natAbs ≤ bnd := by
    rw [h_v2_unc 6 h6lt (by decide) (by decide), h_v1_unc 6 h6lt (by decide) (by decide)]
    exact hb_init 6 h6lt
  obtain ⟨v3, h_v3_eq, h_v3_unc, h_v3_i, h_v3_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v2 zeta1 4#usize 6#usize bnd
      h4lt h6lt (by decide) hz1 h_v2_4 h_v2_6 h_bnd29439)
  -- Step 4: (5, 7) ζ1.
  have h_v3_5 : (v3.elements.val[5]!).val.natAbs ≤ bnd := by
    rw [h_v3_unc 5 h5lt (by decide) (by decide),
        h_v2_unc 5 h5lt (by decide) (by decide),
        h_v1_unc 5 h5lt (by decide) (by decide)]
    exact hb_init 5 h5lt
  have h_v3_7 : (v3.elements.val[7]!).val.natAbs ≤ bnd := by
    rw [h_v3_unc 7 h7lt (by decide) (by decide),
        h_v2_unc 7 h7lt (by decide) (by decide),
        h_v1_unc 7 h7lt (by decide) (by decide)]
    exact hb_init 7 h7lt
  obtain ⟨v4, h_v4_eq, h_v4_unc, h_v4_i, h_v4_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v3 zeta1 5#usize 7#usize bnd
      h5lt h7lt (by decide) hz1 h_v3_5 h_v3_7 h_bnd29439)
  -- Step 5: (8, 10) ζ2.
  have h_v4_8 : (v4.elements.val[8]!).val.natAbs ≤ bnd := by
    rw [h_v4_unc 8 h8lt (by decide) (by decide),
        h_v3_unc 8 h8lt (by decide) (by decide),
        h_v2_unc 8 h8lt (by decide) (by decide),
        h_v1_unc 8 h8lt (by decide) (by decide)]
    exact hb_init 8 h8lt
  have h_v4_10 : (v4.elements.val[10]!).val.natAbs ≤ bnd := by
    rw [h_v4_unc 10 h10lt (by decide) (by decide),
        h_v3_unc 10 h10lt (by decide) (by decide),
        h_v2_unc 10 h10lt (by decide) (by decide),
        h_v1_unc 10 h10lt (by decide) (by decide)]
    exact hb_init 10 h10lt
  obtain ⟨v5, h_v5_eq, h_v5_unc, h_v5_i, h_v5_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v4 zeta2 8#usize 10#usize bnd
      h8lt h10lt (by decide) hz2 h_v4_8 h_v4_10 h_bnd29439)
  -- Step 6: (9, 11) ζ2.
  have h_v5_9 : (v5.elements.val[9]!).val.natAbs ≤ bnd := by
    rw [h_v5_unc 9 h9lt (by decide) (by decide),
        h_v4_unc 9 h9lt (by decide) (by decide),
        h_v3_unc 9 h9lt (by decide) (by decide),
        h_v2_unc 9 h9lt (by decide) (by decide),
        h_v1_unc 9 h9lt (by decide) (by decide)]
    exact hb_init 9 h9lt
  have h_v5_11 : (v5.elements.val[11]!).val.natAbs ≤ bnd := by
    rw [h_v5_unc 11 h11lt (by decide) (by decide),
        h_v4_unc 11 h11lt (by decide) (by decide),
        h_v3_unc 11 h11lt (by decide) (by decide),
        h_v2_unc 11 h11lt (by decide) (by decide),
        h_v1_unc 11 h11lt (by decide) (by decide)]
    exact hb_init 11 h11lt
  obtain ⟨v6, h_v6_eq, h_v6_unc, h_v6_i, h_v6_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v5 zeta2 9#usize 11#usize bnd
      h9lt h11lt (by decide) hz2 h_v5_9 h_v5_11 h_bnd29439)
  -- Step 7: (12, 14) ζ3.
  have h_v6_12 : (v6.elements.val[12]!).val.natAbs ≤ bnd := by
    rw [h_v6_unc 12 h12lt (by decide) (by decide),
        h_v5_unc 12 h12lt (by decide) (by decide),
        h_v4_unc 12 h12lt (by decide) (by decide),
        h_v3_unc 12 h12lt (by decide) (by decide),
        h_v2_unc 12 h12lt (by decide) (by decide),
        h_v1_unc 12 h12lt (by decide) (by decide)]
    exact hb_init 12 h12lt
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ bnd := by
    rw [h_v6_unc 14 h14lt (by decide) (by decide),
        h_v5_unc 14 h14lt (by decide) (by decide),
        h_v4_unc 14 h14lt (by decide) (by decide),
        h_v3_unc 14 h14lt (by decide) (by decide),
        h_v2_unc 14 h14lt (by decide) (by decide),
        h_v1_unc 14 h14lt (by decide) (by decide)]
    exact hb_init 14 h14lt
  obtain ⟨v7, h_v7_eq, h_v7_unc, h_v7_i, h_v7_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v6 zeta3 12#usize 14#usize bnd
      h12lt h14lt (by decide) hz3 h_v6_12 h_v6_14 h_bnd29439)
  -- Step 8: (13, 15) ζ3.
  have h_v7_13 : (v7.elements.val[13]!).val.natAbs ≤ bnd := by
    rw [h_v7_unc 13 h13lt (by decide) (by decide),
        h_v6_unc 13 h13lt (by decide) (by decide),
        h_v5_unc 13 h13lt (by decide) (by decide),
        h_v4_unc 13 h13lt (by decide) (by decide),
        h_v3_unc 13 h13lt (by decide) (by decide),
        h_v2_unc 13 h13lt (by decide) (by decide),
        h_v1_unc 13 h13lt (by decide) (by decide)]
    exact hb_init 13 h13lt
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ bnd := by
    rw [h_v7_unc 15 h15lt (by decide) (by decide),
        h_v6_unc 15 h15lt (by decide) (by decide),
        h_v5_unc 15 h15lt (by decide) (by decide),
        h_v4_unc 15 h15lt (by decide) (by decide),
        h_v3_unc 15 h15lt (by decide) (by decide),
        h_v2_unc 15 h15lt (by decide) (by decide),
        h_v1_unc 15 h15lt (by decide) (by decide)]
    exact hb_init 15 h15lt
  obtain ⟨v8, h_v8_eq, h_v8_unc, h_v8_i, h_v8_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v7 zeta3 13#usize 15#usize bnd
      h13lt h15lt (by decide) hz3 h_v7_13 h_v7_15 h_bnd29439)
  -- Compose the whole 8-step chain into one `.ok v8` equation.
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3
        = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step
    rw [h_v1_eq]; simp only [bind_tc_ok]
    rw [h_v2_eq]; simp only [bind_tc_ok]
    rw [h_v3_eq]; simp only [bind_tc_ok]
    rw [h_v4_eq]; simp only [bind_tc_ok]
    rw [h_v5_eq]; simp only [bind_tc_ok]
    rw [h_v6_eq]; simp only [bind_tc_ok]
    rw [h_v7_eq]; simp only [bind_tc_ok]
    exact h_v8_eq
  -- Close the Triple: prove every lane ≤ bnd + 3328 by case-split on which step touched it.
  -- Strategy: for each lane ℓ, identify the step that touched it (giving h_v{k}_i or h_v{k}_j
  -- with bound ≤ bnd + 3328), then propagate v_k[ℓ] = ... = v8[ℓ] via the later steps' h_v{m}_unc.
  apply triple_of_ok_l2 h_body
  intro i hi
  interval_cases i
  -- Lane 0: touched in step 1 as i-lane ⇒ v1[0] ≤ bnd + 3328. v8[0] = v1[0].
  · have h_eq : v8.elements.val[0]! = v1.elements.val[0]! := by
      rw [h_v8_unc 0 h0lt (by decide) (by decide),
          h_v7_unc 0 h0lt (by decide) (by decide),
          h_v6_unc 0 h0lt (by decide) (by decide),
          h_v5_unc 0 h0lt (by decide) (by decide),
          h_v4_unc 0 h0lt (by decide) (by decide),
          h_v3_unc 0 h0lt (by decide) (by decide),
          h_v2_unc 0 h0lt (by decide) (by decide)]
    rw [h_eq]; exact h_v1_i
  -- Lane 1: touched in step 2 as i-lane.
  · have h_eq : v8.elements.val[1]! = v2.elements.val[1]! := by
      rw [h_v8_unc 1 h1lt (by decide) (by decide),
          h_v7_unc 1 h1lt (by decide) (by decide),
          h_v6_unc 1 h1lt (by decide) (by decide),
          h_v5_unc 1 h1lt (by decide) (by decide),
          h_v4_unc 1 h1lt (by decide) (by decide),
          h_v3_unc 1 h1lt (by decide) (by decide)]
    rw [h_eq]; exact h_v2_i
  -- Lane 2: touched in step 1 as j-lane.
  · have h_eq : v8.elements.val[2]! = v1.elements.val[2]! := by
      rw [h_v8_unc 2 h2lt (by decide) (by decide),
          h_v7_unc 2 h2lt (by decide) (by decide),
          h_v6_unc 2 h2lt (by decide) (by decide),
          h_v5_unc 2 h2lt (by decide) (by decide),
          h_v4_unc 2 h2lt (by decide) (by decide),
          h_v3_unc 2 h2lt (by decide) (by decide),
          h_v2_unc 2 h2lt (by decide) (by decide)]
    rw [h_eq]; exact h_v1_j
  -- Lane 3: touched in step 2 as j-lane.
  · have h_eq : v8.elements.val[3]! = v2.elements.val[3]! := by
      rw [h_v8_unc 3 h3lt (by decide) (by decide),
          h_v7_unc 3 h3lt (by decide) (by decide),
          h_v6_unc 3 h3lt (by decide) (by decide),
          h_v5_unc 3 h3lt (by decide) (by decide),
          h_v4_unc 3 h3lt (by decide) (by decide),
          h_v3_unc 3 h3lt (by decide) (by decide)]
    rw [h_eq]; exact h_v2_j
  -- Lane 4: touched in step 3 as i-lane.
  · have h_eq : v8.elements.val[4]! = v3.elements.val[4]! := by
      rw [h_v8_unc 4 h4lt (by decide) (by decide),
          h_v7_unc 4 h4lt (by decide) (by decide),
          h_v6_unc 4 h4lt (by decide) (by decide),
          h_v5_unc 4 h4lt (by decide) (by decide),
          h_v4_unc 4 h4lt (by decide) (by decide)]
    rw [h_eq]; exact h_v3_i
  -- Lane 5: touched in step 4 as i-lane.
  · have h_eq : v8.elements.val[5]! = v4.elements.val[5]! := by
      rw [h_v8_unc 5 h5lt (by decide) (by decide),
          h_v7_unc 5 h5lt (by decide) (by decide),
          h_v6_unc 5 h5lt (by decide) (by decide),
          h_v5_unc 5 h5lt (by decide) (by decide)]
    rw [h_eq]; exact h_v4_i
  -- Lane 6: touched in step 3 as j-lane.
  · have h_eq : v8.elements.val[6]! = v3.elements.val[6]! := by
      rw [h_v8_unc 6 h6lt (by decide) (by decide),
          h_v7_unc 6 h6lt (by decide) (by decide),
          h_v6_unc 6 h6lt (by decide) (by decide),
          h_v5_unc 6 h6lt (by decide) (by decide),
          h_v4_unc 6 h6lt (by decide) (by decide)]
    rw [h_eq]; exact h_v3_j
  -- Lane 7: touched in step 4 as j-lane.
  · have h_eq : v8.elements.val[7]! = v4.elements.val[7]! := by
      rw [h_v8_unc 7 h7lt (by decide) (by decide),
          h_v7_unc 7 h7lt (by decide) (by decide),
          h_v6_unc 7 h7lt (by decide) (by decide),
          h_v5_unc 7 h7lt (by decide) (by decide)]
    rw [h_eq]; exact h_v4_j
  -- Lane 8: touched in step 5 as i-lane.
  · have h_eq : v8.elements.val[8]! = v5.elements.val[8]! := by
      rw [h_v8_unc 8 h8lt (by decide) (by decide),
          h_v7_unc 8 h8lt (by decide) (by decide),
          h_v6_unc 8 h8lt (by decide) (by decide)]
    rw [h_eq]; exact h_v5_i
  -- Lane 9: touched in step 6 as i-lane.
  · have h_eq : v8.elements.val[9]! = v6.elements.val[9]! := by
      rw [h_v8_unc 9 h9lt (by decide) (by decide),
          h_v7_unc 9 h9lt (by decide) (by decide)]
    rw [h_eq]; exact h_v6_i
  -- Lane 10: touched in step 5 as j-lane.
  · have h_eq : v8.elements.val[10]! = v5.elements.val[10]! := by
      rw [h_v8_unc 10 h10lt (by decide) (by decide),
          h_v7_unc 10 h10lt (by decide) (by decide),
          h_v6_unc 10 h10lt (by decide) (by decide)]
    rw [h_eq]; exact h_v5_j
  -- Lane 11: touched in step 6 as j-lane.
  · have h_eq : v8.elements.val[11]! = v6.elements.val[11]! := by
      rw [h_v8_unc 11 h11lt (by decide) (by decide),
          h_v7_unc 11 h11lt (by decide) (by decide)]
    rw [h_eq]; exact h_v6_j
  -- Lane 12: touched in step 7 as i-lane.
  · have h_eq : v8.elements.val[12]! = v7.elements.val[12]! := by
      rw [h_v8_unc 12 h12lt (by decide) (by decide)]
    rw [h_eq]; exact h_v7_i
  -- Lane 13: touched in step 8 as i-lane.
  · exact h_v8_i
  -- Lane 14: touched in step 7 as j-lane.
  · have h_eq : v8.elements.val[14]! = v7.elements.val[14]! := by
      rw [h_v8_unc 14 h14lt (by decide) (by decide)]
    rw [h_eq]; exact h_v7_j
  -- Lane 15: touched in step 8 as j-lane.
  · exact h_v8_j

/-! ## L2.3 — `ntt_layer_2_step_spec`

    Eight disjoint butterflies on pairs `(0,4)ζ0`, `(1,5)ζ0`, `(2,6)ζ0`,
    `(3,7)ζ0`, `(8,12)ζ1`, `(9,13)ζ1`, `(10,14)ζ1`, `(11,15)ζ1`. Same
    bookkeeping pattern as L2.2 but with `B = 6`.
-/

@[spec]
theorem ntt_layer_2_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta0 zeta1 : Std.I16)
    (hz0 : zeta0.val.natAbs ≤ 1664) (hz1 : zeta1.val.natAbs ≤ 1664)
    (hpre : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 6 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step vec zeta0 zeta1
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ 7 * 3328 ⌝ ⦄ := by
  have h0lt : (0#usize : Std.Usize).val < 16 := by decide
  have h1lt : (1#usize : Std.Usize).val < 16 := by decide
  have h2lt : (2#usize : Std.Usize).val < 16 := by decide
  have h3lt : (3#usize : Std.Usize).val < 16 := by decide
  have h4lt : (4#usize : Std.Usize).val < 16 := by decide
  have h5lt : (5#usize : Std.Usize).val < 16 := by decide
  have h6lt : (6#usize : Std.Usize).val < 16 := by decide
  have h7lt : (7#usize : Std.Usize).val < 16 := by decide
  have h8lt : (8#usize : Std.Usize).val < 16 := by decide
  have h9lt : (9#usize : Std.Usize).val < 16 := by decide
  have h10lt : (10#usize : Std.Usize).val < 16 := by decide
  have h11lt : (11#usize : Std.Usize).val < 16 := by decide
  have h12lt : (12#usize : Std.Usize).val < 16 := by decide
  have h13lt : (13#usize : Std.Usize).val < 16 := by decide
  have h14lt : (14#usize : Std.Usize).val < 16 := by decide
  have h15lt : (15#usize : Std.Usize).val < 16 := by decide
  have hb_init : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 6 * 3328 := hpre
  -- Step 1: (0, 4) ζ0.
  obtain ⟨v1, h_v1_eq, h_v1_unc, h_v1_i, h_v1_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B vec zeta0 0#usize 4#usize 6
      h0lt h4lt (by decide) hz0 (hb_init 0 h0lt) (hb_init 4 h4lt) (by decide))
  -- Step 2: (1, 5) ζ0.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v1_unc 1 h1lt (by decide) (by decide)]; exact hb_init 1 h1lt
  have h_v1_5 : (v1.elements.val[5]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v1_unc 5 h5lt (by decide) (by decide)]; exact hb_init 5 h5lt
  obtain ⟨v2, h_v2_eq, h_v2_unc, h_v2_i, h_v2_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v1 zeta0 1#usize 5#usize 6
      h1lt h5lt (by decide) hz0 h_v1_1 h_v1_5 (by decide))
  -- Step 3: (2, 6) ζ0.
  have h_v2_2 : (v2.elements.val[2]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v2_unc 2 h2lt (by decide) (by decide), h_v1_unc 2 h2lt (by decide) (by decide)]
    exact hb_init 2 h2lt
  have h_v2_6 : (v2.elements.val[6]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v2_unc 6 h6lt (by decide) (by decide), h_v1_unc 6 h6lt (by decide) (by decide)]
    exact hb_init 6 h6lt
  obtain ⟨v3, h_v3_eq, h_v3_unc, h_v3_i, h_v3_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v2 zeta0 2#usize 6#usize 6
      h2lt h6lt (by decide) hz0 h_v2_2 h_v2_6 (by decide))
  -- Step 4: (3, 7) ζ0.
  have h_v3_3 : (v3.elements.val[3]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v3_unc 3 h3lt (by decide) (by decide),
        h_v2_unc 3 h3lt (by decide) (by decide),
        h_v1_unc 3 h3lt (by decide) (by decide)]
    exact hb_init 3 h3lt
  have h_v3_7 : (v3.elements.val[7]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v3_unc 7 h7lt (by decide) (by decide),
        h_v2_unc 7 h7lt (by decide) (by decide),
        h_v1_unc 7 h7lt (by decide) (by decide)]
    exact hb_init 7 h7lt
  obtain ⟨v4, h_v4_eq, h_v4_unc, h_v4_i, h_v4_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v3 zeta0 3#usize 7#usize 6
      h3lt h7lt (by decide) hz0 h_v3_3 h_v3_7 (by decide))
  -- Step 5: (8, 12) ζ1.
  have h_v4_8 : (v4.elements.val[8]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v4_unc 8 h8lt (by decide) (by decide),
        h_v3_unc 8 h8lt (by decide) (by decide),
        h_v2_unc 8 h8lt (by decide) (by decide),
        h_v1_unc 8 h8lt (by decide) (by decide)]
    exact hb_init 8 h8lt
  have h_v4_12 : (v4.elements.val[12]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v4_unc 12 h12lt (by decide) (by decide),
        h_v3_unc 12 h12lt (by decide) (by decide),
        h_v2_unc 12 h12lt (by decide) (by decide),
        h_v1_unc 12 h12lt (by decide) (by decide)]
    exact hb_init 12 h12lt
  obtain ⟨v5, h_v5_eq, h_v5_unc, h_v5_i, h_v5_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v4 zeta1 8#usize 12#usize 6
      h8lt h12lt (by decide) hz1 h_v4_8 h_v4_12 (by decide))
  -- Step 6: (9, 13) ζ1.
  have h_v5_9 : (v5.elements.val[9]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v5_unc 9 h9lt (by decide) (by decide),
        h_v4_unc 9 h9lt (by decide) (by decide),
        h_v3_unc 9 h9lt (by decide) (by decide),
        h_v2_unc 9 h9lt (by decide) (by decide),
        h_v1_unc 9 h9lt (by decide) (by decide)]
    exact hb_init 9 h9lt
  have h_v5_13 : (v5.elements.val[13]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v5_unc 13 h13lt (by decide) (by decide),
        h_v4_unc 13 h13lt (by decide) (by decide),
        h_v3_unc 13 h13lt (by decide) (by decide),
        h_v2_unc 13 h13lt (by decide) (by decide),
        h_v1_unc 13 h13lt (by decide) (by decide)]
    exact hb_init 13 h13lt
  obtain ⟨v6, h_v6_eq, h_v6_unc, h_v6_i, h_v6_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v5 zeta1 9#usize 13#usize 6
      h9lt h13lt (by decide) hz1 h_v5_9 h_v5_13 (by decide))
  -- Step 7: (10, 14) ζ1.
  have h_v6_10 : (v6.elements.val[10]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v6_unc 10 h10lt (by decide) (by decide),
        h_v5_unc 10 h10lt (by decide) (by decide),
        h_v4_unc 10 h10lt (by decide) (by decide),
        h_v3_unc 10 h10lt (by decide) (by decide),
        h_v2_unc 10 h10lt (by decide) (by decide),
        h_v1_unc 10 h10lt (by decide) (by decide)]
    exact hb_init 10 h10lt
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v6_unc 14 h14lt (by decide) (by decide),
        h_v5_unc 14 h14lt (by decide) (by decide),
        h_v4_unc 14 h14lt (by decide) (by decide),
        h_v3_unc 14 h14lt (by decide) (by decide),
        h_v2_unc 14 h14lt (by decide) (by decide),
        h_v1_unc 14 h14lt (by decide) (by decide)]
    exact hb_init 14 h14lt
  obtain ⟨v7, h_v7_eq, h_v7_unc, h_v7_i, h_v7_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v6 zeta1 10#usize 14#usize 6
      h10lt h14lt (by decide) hz1 h_v6_10 h_v6_14 (by decide))
  -- Step 8: (11, 15) ζ1.
  have h_v7_11 : (v7.elements.val[11]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v7_unc 11 h11lt (by decide) (by decide),
        h_v6_unc 11 h11lt (by decide) (by decide),
        h_v5_unc 11 h11lt (by decide) (by decide),
        h_v4_unc 11 h11lt (by decide) (by decide),
        h_v3_unc 11 h11lt (by decide) (by decide),
        h_v2_unc 11 h11lt (by decide) (by decide),
        h_v1_unc 11 h11lt (by decide) (by decide)]
    exact hb_init 11 h11lt
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 6 * 3328 := by
    rw [h_v7_unc 15 h15lt (by decide) (by decide),
        h_v6_unc 15 h15lt (by decide) (by decide),
        h_v5_unc 15 h15lt (by decide) (by decide),
        h_v4_unc 15 h15lt (by decide) (by decide),
        h_v3_unc 15 h15lt (by decide) (by decide),
        h_v2_unc 15 h15lt (by decide) (by decide),
        h_v1_unc 15 h15lt (by decide) (by decide)]
    exact hb_init 15 h15lt
  obtain ⟨v8, h_v8_eq, h_v8_unc, h_v8_i, h_v8_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v7 zeta1 11#usize 15#usize 6
      h11lt h15lt (by decide) hz1 h_v7_11 h_v7_15 (by decide))
  -- Compose into one `.ok v8` equation.
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step vec zeta0 zeta1
        = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step
    rw [h_v1_eq]; simp only [bind_tc_ok]
    rw [h_v2_eq]; simp only [bind_tc_ok]
    rw [h_v3_eq]; simp only [bind_tc_ok]
    rw [h_v4_eq]; simp only [bind_tc_ok]
    rw [h_v5_eq]; simp only [bind_tc_ok]
    rw [h_v6_eq]; simp only [bind_tc_ok]
    rw [h_v7_eq]; simp only [bind_tc_ok]
    exact h_v8_eq
  -- Close: per-lane case split.
  apply triple_of_ok_l2 h_body
  intro i hi
  interval_cases i
  -- Lane 0: step 1 i-lane.
  · have h_eq : v8.elements.val[0]! = v1.elements.val[0]! := by
      rw [h_v8_unc 0 h0lt (by decide) (by decide),
          h_v7_unc 0 h0lt (by decide) (by decide),
          h_v6_unc 0 h0lt (by decide) (by decide),
          h_v5_unc 0 h0lt (by decide) (by decide),
          h_v4_unc 0 h0lt (by decide) (by decide),
          h_v3_unc 0 h0lt (by decide) (by decide),
          h_v2_unc 0 h0lt (by decide) (by decide)]
    rw [h_eq]; exact h_v1_i
  -- Lane 1: step 2 i-lane.
  · have h_eq : v8.elements.val[1]! = v2.elements.val[1]! := by
      rw [h_v8_unc 1 h1lt (by decide) (by decide),
          h_v7_unc 1 h1lt (by decide) (by decide),
          h_v6_unc 1 h1lt (by decide) (by decide),
          h_v5_unc 1 h1lt (by decide) (by decide),
          h_v4_unc 1 h1lt (by decide) (by decide),
          h_v3_unc 1 h1lt (by decide) (by decide)]
    rw [h_eq]; exact h_v2_i
  -- Lane 2: step 3 i-lane.
  · have h_eq : v8.elements.val[2]! = v3.elements.val[2]! := by
      rw [h_v8_unc 2 h2lt (by decide) (by decide),
          h_v7_unc 2 h2lt (by decide) (by decide),
          h_v6_unc 2 h2lt (by decide) (by decide),
          h_v5_unc 2 h2lt (by decide) (by decide),
          h_v4_unc 2 h2lt (by decide) (by decide)]
    rw [h_eq]; exact h_v3_i
  -- Lane 3: step 4 i-lane.
  · have h_eq : v8.elements.val[3]! = v4.elements.val[3]! := by
      rw [h_v8_unc 3 h3lt (by decide) (by decide),
          h_v7_unc 3 h3lt (by decide) (by decide),
          h_v6_unc 3 h3lt (by decide) (by decide),
          h_v5_unc 3 h3lt (by decide) (by decide)]
    rw [h_eq]; exact h_v4_i
  -- Lane 4: step 1 j-lane.
  · have h_eq : v8.elements.val[4]! = v1.elements.val[4]! := by
      rw [h_v8_unc 4 h4lt (by decide) (by decide),
          h_v7_unc 4 h4lt (by decide) (by decide),
          h_v6_unc 4 h4lt (by decide) (by decide),
          h_v5_unc 4 h4lt (by decide) (by decide),
          h_v4_unc 4 h4lt (by decide) (by decide),
          h_v3_unc 4 h4lt (by decide) (by decide),
          h_v2_unc 4 h4lt (by decide) (by decide)]
    rw [h_eq]; exact h_v1_j
  -- Lane 5: step 2 j-lane.
  · have h_eq : v8.elements.val[5]! = v2.elements.val[5]! := by
      rw [h_v8_unc 5 h5lt (by decide) (by decide),
          h_v7_unc 5 h5lt (by decide) (by decide),
          h_v6_unc 5 h5lt (by decide) (by decide),
          h_v5_unc 5 h5lt (by decide) (by decide),
          h_v4_unc 5 h5lt (by decide) (by decide),
          h_v3_unc 5 h5lt (by decide) (by decide)]
    rw [h_eq]; exact h_v2_j
  -- Lane 6: step 3 j-lane.
  · have h_eq : v8.elements.val[6]! = v3.elements.val[6]! := by
      rw [h_v8_unc 6 h6lt (by decide) (by decide),
          h_v7_unc 6 h6lt (by decide) (by decide),
          h_v6_unc 6 h6lt (by decide) (by decide),
          h_v5_unc 6 h6lt (by decide) (by decide),
          h_v4_unc 6 h6lt (by decide) (by decide)]
    rw [h_eq]; exact h_v3_j
  -- Lane 7: step 4 j-lane.
  · have h_eq : v8.elements.val[7]! = v4.elements.val[7]! := by
      rw [h_v8_unc 7 h7lt (by decide) (by decide),
          h_v7_unc 7 h7lt (by decide) (by decide),
          h_v6_unc 7 h7lt (by decide) (by decide),
          h_v5_unc 7 h7lt (by decide) (by decide)]
    rw [h_eq]; exact h_v4_j
  -- Lane 8: step 5 i-lane.
  · have h_eq : v8.elements.val[8]! = v5.elements.val[8]! := by
      rw [h_v8_unc 8 h8lt (by decide) (by decide),
          h_v7_unc 8 h8lt (by decide) (by decide),
          h_v6_unc 8 h8lt (by decide) (by decide)]
    rw [h_eq]; exact h_v5_i
  -- Lane 9: step 6 i-lane.
  · have h_eq : v8.elements.val[9]! = v6.elements.val[9]! := by
      rw [h_v8_unc 9 h9lt (by decide) (by decide),
          h_v7_unc 9 h9lt (by decide) (by decide)]
    rw [h_eq]; exact h_v6_i
  -- Lane 10: step 7 i-lane.
  · have h_eq : v8.elements.val[10]! = v7.elements.val[10]! := by
      rw [h_v8_unc 10 h10lt (by decide) (by decide)]
    rw [h_eq]; exact h_v7_i
  -- Lane 11: step 8 i-lane.
  · exact h_v8_i
  -- Lane 12: step 5 j-lane.
  · have h_eq : v8.elements.val[12]! = v5.elements.val[12]! := by
      rw [h_v8_unc 12 h12lt (by decide) (by decide),
          h_v7_unc 12 h12lt (by decide) (by decide),
          h_v6_unc 12 h12lt (by decide) (by decide)]
    rw [h_eq]; exact h_v5_j
  -- Lane 13: step 6 j-lane.
  · have h_eq : v8.elements.val[13]! = v6.elements.val[13]! := by
      rw [h_v8_unc 13 h13lt (by decide) (by decide),
          h_v7_unc 13 h13lt (by decide) (by decide)]
    rw [h_eq]; exact h_v6_j
  -- Lane 14: step 7 j-lane.
  · have h_eq : v8.elements.val[14]! = v7.elements.val[14]! := by
      rw [h_v8_unc 14 h14lt (by decide) (by decide)]
    rw [h_eq]; exact h_v7_j
  -- Lane 15: step 8 j-lane.
  · exact h_v8_j

/-! ## L2.3.bnd — `ntt_layer_2_step_spec_bnd`

    Nat-bnd parameterised mirror of `ntt_layer_2_step_spec` (L2.3): same
    eight disjoint butterflies on pairs `(0,4)ζ0`, `(1,5)ζ0`, `(2,6)ζ0`,
    `(3,7)ζ0`, `(8,12)ζ1`, `(9,13)ζ1`, `(10,14)ζ1`, `(11,15)ζ1`, dispatched
    via the `_bnd` form. Same `bnd ≤ 8 * 3328` precondition as
    `ntt_layer_1_step_spec_bnd`. -/

@[spec]
theorem ntt_layer_2_step_spec_bnd
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta0 zeta1 : Std.I16)
    (bnd : Nat) (h_bnd : bnd ≤ 29439)
    (hz0 : zeta0.val.natAbs ≤ 1664) (hz1 : zeta1.val.natAbs ≤ 1664)
    (hpre : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ bnd) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step vec zeta0 zeta1
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ bnd + 3328 ⌝ ⦄ := by
  have h0lt : (0#usize : Std.Usize).val < 16 := by decide
  have h1lt : (1#usize : Std.Usize).val < 16 := by decide
  have h2lt : (2#usize : Std.Usize).val < 16 := by decide
  have h3lt : (3#usize : Std.Usize).val < 16 := by decide
  have h4lt : (4#usize : Std.Usize).val < 16 := by decide
  have h5lt : (5#usize : Std.Usize).val < 16 := by decide
  have h6lt : (6#usize : Std.Usize).val < 16 := by decide
  have h7lt : (7#usize : Std.Usize).val < 16 := by decide
  have h8lt : (8#usize : Std.Usize).val < 16 := by decide
  have h9lt : (9#usize : Std.Usize).val < 16 := by decide
  have h10lt : (10#usize : Std.Usize).val < 16 := by decide
  have h11lt : (11#usize : Std.Usize).val < 16 := by decide
  have h12lt : (12#usize : Std.Usize).val < 16 := by decide
  have h13lt : (13#usize : Std.Usize).val < 16 := by decide
  have h14lt : (14#usize : Std.Usize).val < 16 := by decide
  have h15lt : (15#usize : Std.Usize).val < 16 := by decide
  -- Bridge: bnd ≤ 8*3328 = 26624 ≤ 29439 (= ntt_step_spec_bnd's max input bound).
  have h_bnd29439 : bnd ≤ 29439 := by omega
  have hb_init : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ bnd := hpre
  -- Step 1: (0, 4) ζ0.
  obtain ⟨v1, h_v1_eq, h_v1_unc, h_v1_i, h_v1_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd vec zeta0 0#usize 4#usize bnd
      h0lt h4lt (by decide) hz0 (hb_init 0 h0lt) (hb_init 4 h4lt) h_bnd29439)
  -- Step 2: (1, 5) ζ0.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ bnd := by
    rw [h_v1_unc 1 h1lt (by decide) (by decide)]; exact hb_init 1 h1lt
  have h_v1_5 : (v1.elements.val[5]!).val.natAbs ≤ bnd := by
    rw [h_v1_unc 5 h5lt (by decide) (by decide)]; exact hb_init 5 h5lt
  obtain ⟨v2, h_v2_eq, h_v2_unc, h_v2_i, h_v2_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v1 zeta0 1#usize 5#usize bnd
      h1lt h5lt (by decide) hz0 h_v1_1 h_v1_5 h_bnd29439)
  -- Step 3: (2, 6) ζ0.
  have h_v2_2 : (v2.elements.val[2]!).val.natAbs ≤ bnd := by
    rw [h_v2_unc 2 h2lt (by decide) (by decide), h_v1_unc 2 h2lt (by decide) (by decide)]
    exact hb_init 2 h2lt
  have h_v2_6 : (v2.elements.val[6]!).val.natAbs ≤ bnd := by
    rw [h_v2_unc 6 h6lt (by decide) (by decide), h_v1_unc 6 h6lt (by decide) (by decide)]
    exact hb_init 6 h6lt
  obtain ⟨v3, h_v3_eq, h_v3_unc, h_v3_i, h_v3_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v2 zeta0 2#usize 6#usize bnd
      h2lt h6lt (by decide) hz0 h_v2_2 h_v2_6 h_bnd29439)
  -- Step 4: (3, 7) ζ0.
  have h_v3_3 : (v3.elements.val[3]!).val.natAbs ≤ bnd := by
    rw [h_v3_unc 3 h3lt (by decide) (by decide),
        h_v2_unc 3 h3lt (by decide) (by decide),
        h_v1_unc 3 h3lt (by decide) (by decide)]
    exact hb_init 3 h3lt
  have h_v3_7 : (v3.elements.val[7]!).val.natAbs ≤ bnd := by
    rw [h_v3_unc 7 h7lt (by decide) (by decide),
        h_v2_unc 7 h7lt (by decide) (by decide),
        h_v1_unc 7 h7lt (by decide) (by decide)]
    exact hb_init 7 h7lt
  obtain ⟨v4, h_v4_eq, h_v4_unc, h_v4_i, h_v4_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v3 zeta0 3#usize 7#usize bnd
      h3lt h7lt (by decide) hz0 h_v3_3 h_v3_7 h_bnd29439)
  -- Step 5: (8, 12) ζ1.
  have h_v4_8 : (v4.elements.val[8]!).val.natAbs ≤ bnd := by
    rw [h_v4_unc 8 h8lt (by decide) (by decide),
        h_v3_unc 8 h8lt (by decide) (by decide),
        h_v2_unc 8 h8lt (by decide) (by decide),
        h_v1_unc 8 h8lt (by decide) (by decide)]
    exact hb_init 8 h8lt
  have h_v4_12 : (v4.elements.val[12]!).val.natAbs ≤ bnd := by
    rw [h_v4_unc 12 h12lt (by decide) (by decide),
        h_v3_unc 12 h12lt (by decide) (by decide),
        h_v2_unc 12 h12lt (by decide) (by decide),
        h_v1_unc 12 h12lt (by decide) (by decide)]
    exact hb_init 12 h12lt
  obtain ⟨v5, h_v5_eq, h_v5_unc, h_v5_i, h_v5_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v4 zeta1 8#usize 12#usize bnd
      h8lt h12lt (by decide) hz1 h_v4_8 h_v4_12 h_bnd29439)
  -- Step 6: (9, 13) ζ1.
  have h_v5_9 : (v5.elements.val[9]!).val.natAbs ≤ bnd := by
    rw [h_v5_unc 9 h9lt (by decide) (by decide),
        h_v4_unc 9 h9lt (by decide) (by decide),
        h_v3_unc 9 h9lt (by decide) (by decide),
        h_v2_unc 9 h9lt (by decide) (by decide),
        h_v1_unc 9 h9lt (by decide) (by decide)]
    exact hb_init 9 h9lt
  have h_v5_13 : (v5.elements.val[13]!).val.natAbs ≤ bnd := by
    rw [h_v5_unc 13 h13lt (by decide) (by decide),
        h_v4_unc 13 h13lt (by decide) (by decide),
        h_v3_unc 13 h13lt (by decide) (by decide),
        h_v2_unc 13 h13lt (by decide) (by decide),
        h_v1_unc 13 h13lt (by decide) (by decide)]
    exact hb_init 13 h13lt
  obtain ⟨v6, h_v6_eq, h_v6_unc, h_v6_i, h_v6_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v5 zeta1 9#usize 13#usize bnd
      h9lt h13lt (by decide) hz1 h_v5_9 h_v5_13 h_bnd29439)
  -- Step 7: (10, 14) ζ1.
  have h_v6_10 : (v6.elements.val[10]!).val.natAbs ≤ bnd := by
    rw [h_v6_unc 10 h10lt (by decide) (by decide),
        h_v5_unc 10 h10lt (by decide) (by decide),
        h_v4_unc 10 h10lt (by decide) (by decide),
        h_v3_unc 10 h10lt (by decide) (by decide),
        h_v2_unc 10 h10lt (by decide) (by decide),
        h_v1_unc 10 h10lt (by decide) (by decide)]
    exact hb_init 10 h10lt
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ bnd := by
    rw [h_v6_unc 14 h14lt (by decide) (by decide),
        h_v5_unc 14 h14lt (by decide) (by decide),
        h_v4_unc 14 h14lt (by decide) (by decide),
        h_v3_unc 14 h14lt (by decide) (by decide),
        h_v2_unc 14 h14lt (by decide) (by decide),
        h_v1_unc 14 h14lt (by decide) (by decide)]
    exact hb_init 14 h14lt
  obtain ⟨v7, h_v7_eq, h_v7_unc, h_v7_i, h_v7_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v6 zeta1 10#usize 14#usize bnd
      h10lt h14lt (by decide) hz1 h_v6_10 h_v6_14 h_bnd29439)
  -- Step 8: (11, 15) ζ1.
  have h_v7_11 : (v7.elements.val[11]!).val.natAbs ≤ bnd := by
    rw [h_v7_unc 11 h11lt (by decide) (by decide),
        h_v6_unc 11 h11lt (by decide) (by decide),
        h_v5_unc 11 h11lt (by decide) (by decide),
        h_v4_unc 11 h11lt (by decide) (by decide),
        h_v3_unc 11 h11lt (by decide) (by decide),
        h_v2_unc 11 h11lt (by decide) (by decide),
        h_v1_unc 11 h11lt (by decide) (by decide)]
    exact hb_init 11 h11lt
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ bnd := by
    rw [h_v7_unc 15 h15lt (by decide) (by decide),
        h_v6_unc 15 h15lt (by decide) (by decide),
        h_v5_unc 15 h15lt (by decide) (by decide),
        h_v4_unc 15 h15lt (by decide) (by decide),
        h_v3_unc 15 h15lt (by decide) (by decide),
        h_v2_unc 15 h15lt (by decide) (by decide),
        h_v1_unc 15 h15lt (by decide) (by decide)]
    exact hb_init 15 h15lt
  obtain ⟨v8, h_v8_eq, h_v8_unc, h_v8_i, h_v8_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v7 zeta1 11#usize 15#usize bnd
      h11lt h15lt (by decide) hz1 h_v7_11 h_v7_15 h_bnd29439)
  -- Compose into one `.ok v8` equation.
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step vec zeta0 zeta1
        = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step
    rw [h_v1_eq]; simp only [bind_tc_ok]
    rw [h_v2_eq]; simp only [bind_tc_ok]
    rw [h_v3_eq]; simp only [bind_tc_ok]
    rw [h_v4_eq]; simp only [bind_tc_ok]
    rw [h_v5_eq]; simp only [bind_tc_ok]
    rw [h_v6_eq]; simp only [bind_tc_ok]
    rw [h_v7_eq]; simp only [bind_tc_ok]
    exact h_v8_eq
  -- Close: per-lane case split.
  apply triple_of_ok_l2 h_body
  intro i hi
  interval_cases i
  -- Lane 0: step 1 i-lane.
  · have h_eq : v8.elements.val[0]! = v1.elements.val[0]! := by
      rw [h_v8_unc 0 h0lt (by decide) (by decide),
          h_v7_unc 0 h0lt (by decide) (by decide),
          h_v6_unc 0 h0lt (by decide) (by decide),
          h_v5_unc 0 h0lt (by decide) (by decide),
          h_v4_unc 0 h0lt (by decide) (by decide),
          h_v3_unc 0 h0lt (by decide) (by decide),
          h_v2_unc 0 h0lt (by decide) (by decide)]
    rw [h_eq]; exact h_v1_i
  -- Lane 1: step 2 i-lane.
  · have h_eq : v8.elements.val[1]! = v2.elements.val[1]! := by
      rw [h_v8_unc 1 h1lt (by decide) (by decide),
          h_v7_unc 1 h1lt (by decide) (by decide),
          h_v6_unc 1 h1lt (by decide) (by decide),
          h_v5_unc 1 h1lt (by decide) (by decide),
          h_v4_unc 1 h1lt (by decide) (by decide),
          h_v3_unc 1 h1lt (by decide) (by decide)]
    rw [h_eq]; exact h_v2_i
  -- Lane 2: step 3 i-lane.
  · have h_eq : v8.elements.val[2]! = v3.elements.val[2]! := by
      rw [h_v8_unc 2 h2lt (by decide) (by decide),
          h_v7_unc 2 h2lt (by decide) (by decide),
          h_v6_unc 2 h2lt (by decide) (by decide),
          h_v5_unc 2 h2lt (by decide) (by decide),
          h_v4_unc 2 h2lt (by decide) (by decide)]
    rw [h_eq]; exact h_v3_i
  -- Lane 3: step 4 i-lane.
  · have h_eq : v8.elements.val[3]! = v4.elements.val[3]! := by
      rw [h_v8_unc 3 h3lt (by decide) (by decide),
          h_v7_unc 3 h3lt (by decide) (by decide),
          h_v6_unc 3 h3lt (by decide) (by decide),
          h_v5_unc 3 h3lt (by decide) (by decide)]
    rw [h_eq]; exact h_v4_i
  -- Lane 4: step 1 j-lane.
  · have h_eq : v8.elements.val[4]! = v1.elements.val[4]! := by
      rw [h_v8_unc 4 h4lt (by decide) (by decide),
          h_v7_unc 4 h4lt (by decide) (by decide),
          h_v6_unc 4 h4lt (by decide) (by decide),
          h_v5_unc 4 h4lt (by decide) (by decide),
          h_v4_unc 4 h4lt (by decide) (by decide),
          h_v3_unc 4 h4lt (by decide) (by decide),
          h_v2_unc 4 h4lt (by decide) (by decide)]
    rw [h_eq]; exact h_v1_j
  -- Lane 5: step 2 j-lane.
  · have h_eq : v8.elements.val[5]! = v2.elements.val[5]! := by
      rw [h_v8_unc 5 h5lt (by decide) (by decide),
          h_v7_unc 5 h5lt (by decide) (by decide),
          h_v6_unc 5 h5lt (by decide) (by decide),
          h_v5_unc 5 h5lt (by decide) (by decide),
          h_v4_unc 5 h5lt (by decide) (by decide),
          h_v3_unc 5 h5lt (by decide) (by decide)]
    rw [h_eq]; exact h_v2_j
  -- Lane 6: step 3 j-lane.
  · have h_eq : v8.elements.val[6]! = v3.elements.val[6]! := by
      rw [h_v8_unc 6 h6lt (by decide) (by decide),
          h_v7_unc 6 h6lt (by decide) (by decide),
          h_v6_unc 6 h6lt (by decide) (by decide),
          h_v5_unc 6 h6lt (by decide) (by decide),
          h_v4_unc 6 h6lt (by decide) (by decide)]
    rw [h_eq]; exact h_v3_j
  -- Lane 7: step 4 j-lane.
  · have h_eq : v8.elements.val[7]! = v4.elements.val[7]! := by
      rw [h_v8_unc 7 h7lt (by decide) (by decide),
          h_v7_unc 7 h7lt (by decide) (by decide),
          h_v6_unc 7 h7lt (by decide) (by decide),
          h_v5_unc 7 h7lt (by decide) (by decide)]
    rw [h_eq]; exact h_v4_j
  -- Lane 8: step 5 i-lane.
  · have h_eq : v8.elements.val[8]! = v5.elements.val[8]! := by
      rw [h_v8_unc 8 h8lt (by decide) (by decide),
          h_v7_unc 8 h8lt (by decide) (by decide),
          h_v6_unc 8 h8lt (by decide) (by decide)]
    rw [h_eq]; exact h_v5_i
  -- Lane 9: step 6 i-lane.
  · have h_eq : v8.elements.val[9]! = v6.elements.val[9]! := by
      rw [h_v8_unc 9 h9lt (by decide) (by decide),
          h_v7_unc 9 h9lt (by decide) (by decide)]
    rw [h_eq]; exact h_v6_i
  -- Lane 10: step 7 i-lane.
  · have h_eq : v8.elements.val[10]! = v7.elements.val[10]! := by
      rw [h_v8_unc 10 h10lt (by decide) (by decide)]
    rw [h_eq]; exact h_v7_i
  -- Lane 11: step 8 i-lane.
  · exact h_v8_i
  -- Lane 12: step 5 j-lane.
  · have h_eq : v8.elements.val[12]! = v5.elements.val[12]! := by
      rw [h_v8_unc 12 h12lt (by decide) (by decide),
          h_v7_unc 12 h12lt (by decide) (by decide),
          h_v6_unc 12 h12lt (by decide) (by decide)]
    rw [h_eq]; exact h_v5_j
  -- Lane 13: step 6 j-lane.
  · have h_eq : v8.elements.val[13]! = v6.elements.val[13]! := by
      rw [h_v8_unc 13 h13lt (by decide) (by decide),
          h_v7_unc 13 h13lt (by decide) (by decide)]
    rw [h_eq]; exact h_v6_j
  -- Lane 14: step 7 j-lane.
  · have h_eq : v8.elements.val[14]! = v7.elements.val[14]! := by
      rw [h_v8_unc 14 h14lt (by decide) (by decide)]
    rw [h_eq]; exact h_v7_j
  -- Lane 15: step 8 j-lane.
  · exact h_v8_j

/-! ## L2.4 — `ntt_layer_3_step_spec`

    Eight disjoint butterflies on pairs `(0,8)`, `(1,9)`, `(2,10)`, `(3,11)`,
    `(4,12)`, `(5,13)`, `(6,14)`, `(7,15)` — all with the single ζ. Same
    bookkeeping pattern as L2.2/L2.3 but with `B = 5`.
-/

@[spec]
theorem ntt_layer_3_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (hz : zeta.val.natAbs ≤ 1664)
    (hpre : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 5 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step vec zeta
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ 6 * 3328 ⌝ ⦄ := by
  have h0lt : (0#usize : Std.Usize).val < 16 := by decide
  have h1lt : (1#usize : Std.Usize).val < 16 := by decide
  have h2lt : (2#usize : Std.Usize).val < 16 := by decide
  have h3lt : (3#usize : Std.Usize).val < 16 := by decide
  have h4lt : (4#usize : Std.Usize).val < 16 := by decide
  have h5lt : (5#usize : Std.Usize).val < 16 := by decide
  have h6lt : (6#usize : Std.Usize).val < 16 := by decide
  have h7lt : (7#usize : Std.Usize).val < 16 := by decide
  have h8lt : (8#usize : Std.Usize).val < 16 := by decide
  have h9lt : (9#usize : Std.Usize).val < 16 := by decide
  have h10lt : (10#usize : Std.Usize).val < 16 := by decide
  have h11lt : (11#usize : Std.Usize).val < 16 := by decide
  have h12lt : (12#usize : Std.Usize).val < 16 := by decide
  have h13lt : (13#usize : Std.Usize).val < 16 := by decide
  have h14lt : (14#usize : Std.Usize).val < 16 := by decide
  have h15lt : (15#usize : Std.Usize).val < 16 := by decide
  have hb_init : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 5 * 3328 := hpre
  -- Step 1: (0, 8).
  obtain ⟨v1, h_v1_eq, h_v1_unc, h_v1_i, h_v1_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B vec zeta 0#usize 8#usize 5
      h0lt h8lt (by decide) hz (hb_init 0 h0lt) (hb_init 8 h8lt) (by decide))
  -- Step 2: (1, 9).
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v1_unc 1 h1lt (by decide) (by decide)]; exact hb_init 1 h1lt
  have h_v1_9 : (v1.elements.val[9]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v1_unc 9 h9lt (by decide) (by decide)]; exact hb_init 9 h9lt
  obtain ⟨v2, h_v2_eq, h_v2_unc, h_v2_i, h_v2_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v1 zeta 1#usize 9#usize 5
      h1lt h9lt (by decide) hz h_v1_1 h_v1_9 (by decide))
  -- Step 3: (2, 10).
  have h_v2_2 : (v2.elements.val[2]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v2_unc 2 h2lt (by decide) (by decide), h_v1_unc 2 h2lt (by decide) (by decide)]
    exact hb_init 2 h2lt
  have h_v2_10 : (v2.elements.val[10]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v2_unc 10 h10lt (by decide) (by decide), h_v1_unc 10 h10lt (by decide) (by decide)]
    exact hb_init 10 h10lt
  obtain ⟨v3, h_v3_eq, h_v3_unc, h_v3_i, h_v3_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v2 zeta 2#usize 10#usize 5
      h2lt h10lt (by decide) hz h_v2_2 h_v2_10 (by decide))
  -- Step 4: (3, 11).
  have h_v3_3 : (v3.elements.val[3]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v3_unc 3 h3lt (by decide) (by decide),
        h_v2_unc 3 h3lt (by decide) (by decide),
        h_v1_unc 3 h3lt (by decide) (by decide)]
    exact hb_init 3 h3lt
  have h_v3_11 : (v3.elements.val[11]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v3_unc 11 h11lt (by decide) (by decide),
        h_v2_unc 11 h11lt (by decide) (by decide),
        h_v1_unc 11 h11lt (by decide) (by decide)]
    exact hb_init 11 h11lt
  obtain ⟨v4, h_v4_eq, h_v4_unc, h_v4_i, h_v4_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v3 zeta 3#usize 11#usize 5
      h3lt h11lt (by decide) hz h_v3_3 h_v3_11 (by decide))
  -- Step 5: (4, 12).
  have h_v4_4 : (v4.elements.val[4]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v4_unc 4 h4lt (by decide) (by decide),
        h_v3_unc 4 h4lt (by decide) (by decide),
        h_v2_unc 4 h4lt (by decide) (by decide),
        h_v1_unc 4 h4lt (by decide) (by decide)]
    exact hb_init 4 h4lt
  have h_v4_12 : (v4.elements.val[12]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v4_unc 12 h12lt (by decide) (by decide),
        h_v3_unc 12 h12lt (by decide) (by decide),
        h_v2_unc 12 h12lt (by decide) (by decide),
        h_v1_unc 12 h12lt (by decide) (by decide)]
    exact hb_init 12 h12lt
  obtain ⟨v5, h_v5_eq, h_v5_unc, h_v5_i, h_v5_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v4 zeta 4#usize 12#usize 5
      h4lt h12lt (by decide) hz h_v4_4 h_v4_12 (by decide))
  -- Step 6: (5, 13).
  have h_v5_5 : (v5.elements.val[5]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v5_unc 5 h5lt (by decide) (by decide),
        h_v4_unc 5 h5lt (by decide) (by decide),
        h_v3_unc 5 h5lt (by decide) (by decide),
        h_v2_unc 5 h5lt (by decide) (by decide),
        h_v1_unc 5 h5lt (by decide) (by decide)]
    exact hb_init 5 h5lt
  have h_v5_13 : (v5.elements.val[13]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v5_unc 13 h13lt (by decide) (by decide),
        h_v4_unc 13 h13lt (by decide) (by decide),
        h_v3_unc 13 h13lt (by decide) (by decide),
        h_v2_unc 13 h13lt (by decide) (by decide),
        h_v1_unc 13 h13lt (by decide) (by decide)]
    exact hb_init 13 h13lt
  obtain ⟨v6, h_v6_eq, h_v6_unc, h_v6_i, h_v6_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v5 zeta 5#usize 13#usize 5
      h5lt h13lt (by decide) hz h_v5_5 h_v5_13 (by decide))
  -- Step 7: (6, 14).
  have h_v6_6 : (v6.elements.val[6]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v6_unc 6 h6lt (by decide) (by decide),
        h_v5_unc 6 h6lt (by decide) (by decide),
        h_v4_unc 6 h6lt (by decide) (by decide),
        h_v3_unc 6 h6lt (by decide) (by decide),
        h_v2_unc 6 h6lt (by decide) (by decide),
        h_v1_unc 6 h6lt (by decide) (by decide)]
    exact hb_init 6 h6lt
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v6_unc 14 h14lt (by decide) (by decide),
        h_v5_unc 14 h14lt (by decide) (by decide),
        h_v4_unc 14 h14lt (by decide) (by decide),
        h_v3_unc 14 h14lt (by decide) (by decide),
        h_v2_unc 14 h14lt (by decide) (by decide),
        h_v1_unc 14 h14lt (by decide) (by decide)]
    exact hb_init 14 h14lt
  obtain ⟨v7, h_v7_eq, h_v7_unc, h_v7_i, h_v7_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v6 zeta 6#usize 14#usize 5
      h6lt h14lt (by decide) hz h_v6_6 h_v6_14 (by decide))
  -- Step 8: (7, 15).
  have h_v7_7 : (v7.elements.val[7]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v7_unc 7 h7lt (by decide) (by decide),
        h_v6_unc 7 h7lt (by decide) (by decide),
        h_v5_unc 7 h7lt (by decide) (by decide),
        h_v4_unc 7 h7lt (by decide) (by decide),
        h_v3_unc 7 h7lt (by decide) (by decide),
        h_v2_unc 7 h7lt (by decide) (by decide),
        h_v1_unc 7 h7lt (by decide) (by decide)]
    exact hb_init 7 h7lt
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 5 * 3328 := by
    rw [h_v7_unc 15 h15lt (by decide) (by decide),
        h_v6_unc 15 h15lt (by decide) (by decide),
        h_v5_unc 15 h15lt (by decide) (by decide),
        h_v4_unc 15 h15lt (by decide) (by decide),
        h_v3_unc 15 h15lt (by decide) (by decide),
        h_v2_unc 15 h15lt (by decide) (by decide),
        h_v1_unc 15 h15lt (by decide) (by decide)]
    exact hb_init 15 h15lt
  obtain ⟨v8, h_v8_eq, h_v8_unc, h_v8_i, h_v8_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_B v7 zeta 7#usize 15#usize 5
      h7lt h15lt (by decide) hz h_v7_7 h_v7_15 (by decide))
  -- Compose into one `.ok v8` equation.
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step vec zeta = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step
    rw [h_v1_eq]; simp only [bind_tc_ok]
    rw [h_v2_eq]; simp only [bind_tc_ok]
    rw [h_v3_eq]; simp only [bind_tc_ok]
    rw [h_v4_eq]; simp only [bind_tc_ok]
    rw [h_v5_eq]; simp only [bind_tc_ok]
    rw [h_v6_eq]; simp only [bind_tc_ok]
    rw [h_v7_eq]; simp only [bind_tc_ok]
    exact h_v8_eq
  -- Close: per-lane case split.
  apply triple_of_ok_l2 h_body
  intro i hi
  interval_cases i
  -- Lane 0: step 1 i-lane.
  · have h_eq : v8.elements.val[0]! = v1.elements.val[0]! := by
      rw [h_v8_unc 0 h0lt (by decide) (by decide),
          h_v7_unc 0 h0lt (by decide) (by decide),
          h_v6_unc 0 h0lt (by decide) (by decide),
          h_v5_unc 0 h0lt (by decide) (by decide),
          h_v4_unc 0 h0lt (by decide) (by decide),
          h_v3_unc 0 h0lt (by decide) (by decide),
          h_v2_unc 0 h0lt (by decide) (by decide)]
    rw [h_eq]; exact h_v1_i
  -- Lane 1: step 2 i-lane.
  · have h_eq : v8.elements.val[1]! = v2.elements.val[1]! := by
      rw [h_v8_unc 1 h1lt (by decide) (by decide),
          h_v7_unc 1 h1lt (by decide) (by decide),
          h_v6_unc 1 h1lt (by decide) (by decide),
          h_v5_unc 1 h1lt (by decide) (by decide),
          h_v4_unc 1 h1lt (by decide) (by decide),
          h_v3_unc 1 h1lt (by decide) (by decide)]
    rw [h_eq]; exact h_v2_i
  -- Lane 2: step 3 i-lane.
  · have h_eq : v8.elements.val[2]! = v3.elements.val[2]! := by
      rw [h_v8_unc 2 h2lt (by decide) (by decide),
          h_v7_unc 2 h2lt (by decide) (by decide),
          h_v6_unc 2 h2lt (by decide) (by decide),
          h_v5_unc 2 h2lt (by decide) (by decide),
          h_v4_unc 2 h2lt (by decide) (by decide)]
    rw [h_eq]; exact h_v3_i
  -- Lane 3: step 4 i-lane.
  · have h_eq : v8.elements.val[3]! = v4.elements.val[3]! := by
      rw [h_v8_unc 3 h3lt (by decide) (by decide),
          h_v7_unc 3 h3lt (by decide) (by decide),
          h_v6_unc 3 h3lt (by decide) (by decide),
          h_v5_unc 3 h3lt (by decide) (by decide)]
    rw [h_eq]; exact h_v4_i
  -- Lane 4: step 5 i-lane.
  · have h_eq : v8.elements.val[4]! = v5.elements.val[4]! := by
      rw [h_v8_unc 4 h4lt (by decide) (by decide),
          h_v7_unc 4 h4lt (by decide) (by decide),
          h_v6_unc 4 h4lt (by decide) (by decide)]
    rw [h_eq]; exact h_v5_i
  -- Lane 5: step 6 i-lane.
  · have h_eq : v8.elements.val[5]! = v6.elements.val[5]! := by
      rw [h_v8_unc 5 h5lt (by decide) (by decide),
          h_v7_unc 5 h5lt (by decide) (by decide)]
    rw [h_eq]; exact h_v6_i
  -- Lane 6: step 7 i-lane.
  · have h_eq : v8.elements.val[6]! = v7.elements.val[6]! := by
      rw [h_v8_unc 6 h6lt (by decide) (by decide)]
    rw [h_eq]; exact h_v7_i
  -- Lane 7: step 8 i-lane.
  · exact h_v8_i
  -- Lane 8: step 1 j-lane.
  · have h_eq : v8.elements.val[8]! = v1.elements.val[8]! := by
      rw [h_v8_unc 8 h8lt (by decide) (by decide),
          h_v7_unc 8 h8lt (by decide) (by decide),
          h_v6_unc 8 h8lt (by decide) (by decide),
          h_v5_unc 8 h8lt (by decide) (by decide),
          h_v4_unc 8 h8lt (by decide) (by decide),
          h_v3_unc 8 h8lt (by decide) (by decide),
          h_v2_unc 8 h8lt (by decide) (by decide)]
    rw [h_eq]; exact h_v1_j
  -- Lane 9: step 2 j-lane.
  · have h_eq : v8.elements.val[9]! = v2.elements.val[9]! := by
      rw [h_v8_unc 9 h9lt (by decide) (by decide),
          h_v7_unc 9 h9lt (by decide) (by decide),
          h_v6_unc 9 h9lt (by decide) (by decide),
          h_v5_unc 9 h9lt (by decide) (by decide),
          h_v4_unc 9 h9lt (by decide) (by decide),
          h_v3_unc 9 h9lt (by decide) (by decide)]
    rw [h_eq]; exact h_v2_j
  -- Lane 10: step 3 j-lane.
  · have h_eq : v8.elements.val[10]! = v3.elements.val[10]! := by
      rw [h_v8_unc 10 h10lt (by decide) (by decide),
          h_v7_unc 10 h10lt (by decide) (by decide),
          h_v6_unc 10 h10lt (by decide) (by decide),
          h_v5_unc 10 h10lt (by decide) (by decide),
          h_v4_unc 10 h10lt (by decide) (by decide)]
    rw [h_eq]; exact h_v3_j
  -- Lane 11: step 4 j-lane.
  · have h_eq : v8.elements.val[11]! = v4.elements.val[11]! := by
      rw [h_v8_unc 11 h11lt (by decide) (by decide),
          h_v7_unc 11 h11lt (by decide) (by decide),
          h_v6_unc 11 h11lt (by decide) (by decide),
          h_v5_unc 11 h11lt (by decide) (by decide)]
    rw [h_eq]; exact h_v4_j
  -- Lane 12: step 5 j-lane.
  · have h_eq : v8.elements.val[12]! = v5.elements.val[12]! := by
      rw [h_v8_unc 12 h12lt (by decide) (by decide),
          h_v7_unc 12 h12lt (by decide) (by decide),
          h_v6_unc 12 h12lt (by decide) (by decide)]
    rw [h_eq]; exact h_v5_j
  -- Lane 13: step 6 j-lane.
  · have h_eq : v8.elements.val[13]! = v6.elements.val[13]! := by
      rw [h_v8_unc 13 h13lt (by decide) (by decide),
          h_v7_unc 13 h13lt (by decide) (by decide)]
    rw [h_eq]; exact h_v6_j
  -- Lane 14: step 7 j-lane.
  · have h_eq : v8.elements.val[14]! = v7.elements.val[14]! := by
      rw [h_v8_unc 14 h14lt (by decide) (by decide)]
    rw [h_eq]; exact h_v7_j
  -- Lane 15: step 8 j-lane.
  · exact h_v8_j

/-! ## L2.4.bnd — `ntt_layer_3_step_spec_bnd`

    Nat-bnd parameterised mirror of `ntt_layer_3_step_spec` (L2.4): same
    eight disjoint butterflies on pairs `(0,8)`, `(1,9)`, `(2,10)`, `(3,11)`,
    `(4,12)`, `(5,13)`, `(6,14)`, `(7,15)` — single ζ. Same
    `bnd ≤ 8 * 3328` precondition as `ntt_layer_{1,2}_step_spec_bnd`. -/

@[spec]
theorem ntt_layer_3_step_spec_bnd
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16)
    (bnd : Nat) (h_bnd : bnd ≤ 29439)
    (hz : zeta.val.natAbs ≤ 1664)
    (hpre : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ bnd) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step vec zeta
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ bnd + 3328 ⌝ ⦄ := by
  have h0lt : (0#usize : Std.Usize).val < 16 := by decide
  have h1lt : (1#usize : Std.Usize).val < 16 := by decide
  have h2lt : (2#usize : Std.Usize).val < 16 := by decide
  have h3lt : (3#usize : Std.Usize).val < 16 := by decide
  have h4lt : (4#usize : Std.Usize).val < 16 := by decide
  have h5lt : (5#usize : Std.Usize).val < 16 := by decide
  have h6lt : (6#usize : Std.Usize).val < 16 := by decide
  have h7lt : (7#usize : Std.Usize).val < 16 := by decide
  have h8lt : (8#usize : Std.Usize).val < 16 := by decide
  have h9lt : (9#usize : Std.Usize).val < 16 := by decide
  have h10lt : (10#usize : Std.Usize).val < 16 := by decide
  have h11lt : (11#usize : Std.Usize).val < 16 := by decide
  have h12lt : (12#usize : Std.Usize).val < 16 := by decide
  have h13lt : (13#usize : Std.Usize).val < 16 := by decide
  have h14lt : (14#usize : Std.Usize).val < 16 := by decide
  have h15lt : (15#usize : Std.Usize).val < 16 := by decide
  -- Bridge: bnd ≤ 8*3328 = 26624 ≤ 29439 (= ntt_step_spec_bnd's max input bound).
  have h_bnd29439 : bnd ≤ 29439 := by omega
  have hb_init : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ bnd := hpre
  -- Step 1: (0, 8).
  obtain ⟨v1, h_v1_eq, h_v1_unc, h_v1_i, h_v1_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd vec zeta 0#usize 8#usize bnd
      h0lt h8lt (by decide) hz (hb_init 0 h0lt) (hb_init 8 h8lt) h_bnd29439)
  -- Step 2: (1, 9).
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ bnd := by
    rw [h_v1_unc 1 h1lt (by decide) (by decide)]; exact hb_init 1 h1lt
  have h_v1_9 : (v1.elements.val[9]!).val.natAbs ≤ bnd := by
    rw [h_v1_unc 9 h9lt (by decide) (by decide)]; exact hb_init 9 h9lt
  obtain ⟨v2, h_v2_eq, h_v2_unc, h_v2_i, h_v2_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v1 zeta 1#usize 9#usize bnd
      h1lt h9lt (by decide) hz h_v1_1 h_v1_9 h_bnd29439)
  -- Step 3: (2, 10).
  have h_v2_2 : (v2.elements.val[2]!).val.natAbs ≤ bnd := by
    rw [h_v2_unc 2 h2lt (by decide) (by decide), h_v1_unc 2 h2lt (by decide) (by decide)]
    exact hb_init 2 h2lt
  have h_v2_10 : (v2.elements.val[10]!).val.natAbs ≤ bnd := by
    rw [h_v2_unc 10 h10lt (by decide) (by decide), h_v1_unc 10 h10lt (by decide) (by decide)]
    exact hb_init 10 h10lt
  obtain ⟨v3, h_v3_eq, h_v3_unc, h_v3_i, h_v3_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v2 zeta 2#usize 10#usize bnd
      h2lt h10lt (by decide) hz h_v2_2 h_v2_10 h_bnd29439)
  -- Step 4: (3, 11).
  have h_v3_3 : (v3.elements.val[3]!).val.natAbs ≤ bnd := by
    rw [h_v3_unc 3 h3lt (by decide) (by decide),
        h_v2_unc 3 h3lt (by decide) (by decide),
        h_v1_unc 3 h3lt (by decide) (by decide)]
    exact hb_init 3 h3lt
  have h_v3_11 : (v3.elements.val[11]!).val.natAbs ≤ bnd := by
    rw [h_v3_unc 11 h11lt (by decide) (by decide),
        h_v2_unc 11 h11lt (by decide) (by decide),
        h_v1_unc 11 h11lt (by decide) (by decide)]
    exact hb_init 11 h11lt
  obtain ⟨v4, h_v4_eq, h_v4_unc, h_v4_i, h_v4_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v3 zeta 3#usize 11#usize bnd
      h3lt h11lt (by decide) hz h_v3_3 h_v3_11 h_bnd29439)
  -- Step 5: (4, 12).
  have h_v4_4 : (v4.elements.val[4]!).val.natAbs ≤ bnd := by
    rw [h_v4_unc 4 h4lt (by decide) (by decide),
        h_v3_unc 4 h4lt (by decide) (by decide),
        h_v2_unc 4 h4lt (by decide) (by decide),
        h_v1_unc 4 h4lt (by decide) (by decide)]
    exact hb_init 4 h4lt
  have h_v4_12 : (v4.elements.val[12]!).val.natAbs ≤ bnd := by
    rw [h_v4_unc 12 h12lt (by decide) (by decide),
        h_v3_unc 12 h12lt (by decide) (by decide),
        h_v2_unc 12 h12lt (by decide) (by decide),
        h_v1_unc 12 h12lt (by decide) (by decide)]
    exact hb_init 12 h12lt
  obtain ⟨v5, h_v5_eq, h_v5_unc, h_v5_i, h_v5_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v4 zeta 4#usize 12#usize bnd
      h4lt h12lt (by decide) hz h_v4_4 h_v4_12 h_bnd29439)
  -- Step 6: (5, 13).
  have h_v5_5 : (v5.elements.val[5]!).val.natAbs ≤ bnd := by
    rw [h_v5_unc 5 h5lt (by decide) (by decide),
        h_v4_unc 5 h5lt (by decide) (by decide),
        h_v3_unc 5 h5lt (by decide) (by decide),
        h_v2_unc 5 h5lt (by decide) (by decide),
        h_v1_unc 5 h5lt (by decide) (by decide)]
    exact hb_init 5 h5lt
  have h_v5_13 : (v5.elements.val[13]!).val.natAbs ≤ bnd := by
    rw [h_v5_unc 13 h13lt (by decide) (by decide),
        h_v4_unc 13 h13lt (by decide) (by decide),
        h_v3_unc 13 h13lt (by decide) (by decide),
        h_v2_unc 13 h13lt (by decide) (by decide),
        h_v1_unc 13 h13lt (by decide) (by decide)]
    exact hb_init 13 h13lt
  obtain ⟨v6, h_v6_eq, h_v6_unc, h_v6_i, h_v6_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v5 zeta 5#usize 13#usize bnd
      h5lt h13lt (by decide) hz h_v5_5 h_v5_13 h_bnd29439)
  -- Step 7: (6, 14).
  have h_v6_6 : (v6.elements.val[6]!).val.natAbs ≤ bnd := by
    rw [h_v6_unc 6 h6lt (by decide) (by decide),
        h_v5_unc 6 h6lt (by decide) (by decide),
        h_v4_unc 6 h6lt (by decide) (by decide),
        h_v3_unc 6 h6lt (by decide) (by decide),
        h_v2_unc 6 h6lt (by decide) (by decide),
        h_v1_unc 6 h6lt (by decide) (by decide)]
    exact hb_init 6 h6lt
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ bnd := by
    rw [h_v6_unc 14 h14lt (by decide) (by decide),
        h_v5_unc 14 h14lt (by decide) (by decide),
        h_v4_unc 14 h14lt (by decide) (by decide),
        h_v3_unc 14 h14lt (by decide) (by decide),
        h_v2_unc 14 h14lt (by decide) (by decide),
        h_v1_unc 14 h14lt (by decide) (by decide)]
    exact hb_init 14 h14lt
  obtain ⟨v7, h_v7_eq, h_v7_unc, h_v7_i, h_v7_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v6 zeta 6#usize 14#usize bnd
      h6lt h14lt (by decide) hz h_v6_6 h_v6_14 h_bnd29439)
  -- Step 8: (7, 15).
  have h_v7_7 : (v7.elements.val[7]!).val.natAbs ≤ bnd := by
    rw [h_v7_unc 7 h7lt (by decide) (by decide),
        h_v6_unc 7 h7lt (by decide) (by decide),
        h_v5_unc 7 h7lt (by decide) (by decide),
        h_v4_unc 7 h7lt (by decide) (by decide),
        h_v3_unc 7 h7lt (by decide) (by decide),
        h_v2_unc 7 h7lt (by decide) (by decide),
        h_v1_unc 7 h7lt (by decide) (by decide)]
    exact hb_init 7 h7lt
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ bnd := by
    rw [h_v7_unc 15 h15lt (by decide) (by decide),
        h_v6_unc 15 h15lt (by decide) (by decide),
        h_v5_unc 15 h15lt (by decide) (by decide),
        h_v4_unc 15 h15lt (by decide) (by decide),
        h_v3_unc 15 h15lt (by decide) (by decide),
        h_v2_unc 15 h15lt (by decide) (by decide),
        h_v1_unc 15 h15lt (by decide) (by decide)]
    exact hb_init 15 h15lt
  obtain ⟨v8, h_v8_eq, h_v8_unc, h_v8_i, h_v8_j⟩ :=
    triple_exists_ok_l2 (ntt_step_spec_bnd v7 zeta 7#usize 15#usize bnd
      h7lt h15lt (by decide) hz h_v7_7 h_v7_15 h_bnd29439)
  -- Compose into one `.ok v8` equation.
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step vec zeta = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step
    rw [h_v1_eq]; simp only [bind_tc_ok]
    rw [h_v2_eq]; simp only [bind_tc_ok]
    rw [h_v3_eq]; simp only [bind_tc_ok]
    rw [h_v4_eq]; simp only [bind_tc_ok]
    rw [h_v5_eq]; simp only [bind_tc_ok]
    rw [h_v6_eq]; simp only [bind_tc_ok]
    rw [h_v7_eq]; simp only [bind_tc_ok]
    exact h_v8_eq
  -- Close: per-lane case split.
  apply triple_of_ok_l2 h_body
  intro i hi
  interval_cases i
  -- Lane 0: step 1 i-lane.
  · have h_eq : v8.elements.val[0]! = v1.elements.val[0]! := by
      rw [h_v8_unc 0 h0lt (by decide) (by decide),
          h_v7_unc 0 h0lt (by decide) (by decide),
          h_v6_unc 0 h0lt (by decide) (by decide),
          h_v5_unc 0 h0lt (by decide) (by decide),
          h_v4_unc 0 h0lt (by decide) (by decide),
          h_v3_unc 0 h0lt (by decide) (by decide),
          h_v2_unc 0 h0lt (by decide) (by decide)]
    rw [h_eq]; exact h_v1_i
  -- Lane 1: step 2 i-lane.
  · have h_eq : v8.elements.val[1]! = v2.elements.val[1]! := by
      rw [h_v8_unc 1 h1lt (by decide) (by decide),
          h_v7_unc 1 h1lt (by decide) (by decide),
          h_v6_unc 1 h1lt (by decide) (by decide),
          h_v5_unc 1 h1lt (by decide) (by decide),
          h_v4_unc 1 h1lt (by decide) (by decide),
          h_v3_unc 1 h1lt (by decide) (by decide)]
    rw [h_eq]; exact h_v2_i
  -- Lane 2: step 3 i-lane.
  · have h_eq : v8.elements.val[2]! = v3.elements.val[2]! := by
      rw [h_v8_unc 2 h2lt (by decide) (by decide),
          h_v7_unc 2 h2lt (by decide) (by decide),
          h_v6_unc 2 h2lt (by decide) (by decide),
          h_v5_unc 2 h2lt (by decide) (by decide),
          h_v4_unc 2 h2lt (by decide) (by decide)]
    rw [h_eq]; exact h_v3_i
  -- Lane 3: step 4 i-lane.
  · have h_eq : v8.elements.val[3]! = v4.elements.val[3]! := by
      rw [h_v8_unc 3 h3lt (by decide) (by decide),
          h_v7_unc 3 h3lt (by decide) (by decide),
          h_v6_unc 3 h3lt (by decide) (by decide),
          h_v5_unc 3 h3lt (by decide) (by decide)]
    rw [h_eq]; exact h_v4_i
  -- Lane 4: step 5 i-lane.
  · have h_eq : v8.elements.val[4]! = v5.elements.val[4]! := by
      rw [h_v8_unc 4 h4lt (by decide) (by decide),
          h_v7_unc 4 h4lt (by decide) (by decide),
          h_v6_unc 4 h4lt (by decide) (by decide)]
    rw [h_eq]; exact h_v5_i
  -- Lane 5: step 6 i-lane.
  · have h_eq : v8.elements.val[5]! = v6.elements.val[5]! := by
      rw [h_v8_unc 5 h5lt (by decide) (by decide),
          h_v7_unc 5 h5lt (by decide) (by decide)]
    rw [h_eq]; exact h_v6_i
  -- Lane 6: step 7 i-lane.
  · have h_eq : v8.elements.val[6]! = v7.elements.val[6]! := by
      rw [h_v8_unc 6 h6lt (by decide) (by decide)]
    rw [h_eq]; exact h_v7_i
  -- Lane 7: step 8 i-lane.
  · exact h_v8_i
  -- Lane 8: step 1 j-lane.
  · have h_eq : v8.elements.val[8]! = v1.elements.val[8]! := by
      rw [h_v8_unc 8 h8lt (by decide) (by decide),
          h_v7_unc 8 h8lt (by decide) (by decide),
          h_v6_unc 8 h8lt (by decide) (by decide),
          h_v5_unc 8 h8lt (by decide) (by decide),
          h_v4_unc 8 h8lt (by decide) (by decide),
          h_v3_unc 8 h8lt (by decide) (by decide),
          h_v2_unc 8 h8lt (by decide) (by decide)]
    rw [h_eq]; exact h_v1_j
  -- Lane 9: step 2 j-lane.
  · have h_eq : v8.elements.val[9]! = v2.elements.val[9]! := by
      rw [h_v8_unc 9 h9lt (by decide) (by decide),
          h_v7_unc 9 h9lt (by decide) (by decide),
          h_v6_unc 9 h9lt (by decide) (by decide),
          h_v5_unc 9 h9lt (by decide) (by decide),
          h_v4_unc 9 h9lt (by decide) (by decide),
          h_v3_unc 9 h9lt (by decide) (by decide)]
    rw [h_eq]; exact h_v2_j
  -- Lane 10: step 3 j-lane.
  · have h_eq : v8.elements.val[10]! = v3.elements.val[10]! := by
      rw [h_v8_unc 10 h10lt (by decide) (by decide),
          h_v7_unc 10 h10lt (by decide) (by decide),
          h_v6_unc 10 h10lt (by decide) (by decide),
          h_v5_unc 10 h10lt (by decide) (by decide),
          h_v4_unc 10 h10lt (by decide) (by decide)]
    rw [h_eq]; exact h_v3_j
  -- Lane 11: step 4 j-lane.
  · have h_eq : v8.elements.val[11]! = v4.elements.val[11]! := by
      rw [h_v8_unc 11 h11lt (by decide) (by decide),
          h_v7_unc 11 h11lt (by decide) (by decide),
          h_v6_unc 11 h11lt (by decide) (by decide),
          h_v5_unc 11 h11lt (by decide) (by decide)]
    rw [h_eq]; exact h_v4_j
  -- Lane 12: step 5 j-lane.
  · have h_eq : v8.elements.val[12]! = v5.elements.val[12]! := by
      rw [h_v8_unc 12 h12lt (by decide) (by decide),
          h_v7_unc 12 h12lt (by decide) (by decide),
          h_v6_unc 12 h12lt (by decide) (by decide)]
    rw [h_eq]; exact h_v5_j
  -- Lane 13: step 6 j-lane.
  · have h_eq : v8.elements.val[13]! = v6.elements.val[13]! := by
      rw [h_v8_unc 13 h13lt (by decide) (by decide),
          h_v7_unc 13 h13lt (by decide) (by decide)]
    rw [h_eq]; exact h_v6_j
  -- Lane 14: step 7 j-lane.
  · have h_eq : v8.elements.val[14]! = v7.elements.val[14]! := by
      rw [h_v8_unc 14 h14lt (by decide) (by decide)]
    rw [h_eq]; exact h_v7_j
  -- Lane 15: step 8 j-lane.
  · exact h_v8_j

/-! ## L2.5 — `inv_ntt_step_spec` (Gentleman–Sande inverse butterfly)

    The impl is a straight chain of 9 binds:
      1. read `vec[j]`             (= `i1`)
      2. read `vec[i]`             (= `i2`)
      3. `a_minus_b = vec[j] - vec[i]`   (wrapping_sub i1 i2)
      4. `a_plus_b  = vec[j] + vec[i]`   (wrapping_add i1 i2)
      5. `o0 = barrett_reduce_element a_plus_b`        (L0.2)
      6. classify ζ                  (identity)
      7. `o1 = montgomery_multiply_fe_by_fer a_minus_b ζ`  (L0.4)
      8. write `vec[i] := o0`        (barrett-reduced sum)
      9. write `vec[j] := o1`        (mont-mul diff by ζ)

    With pre `|vec[i]|, |vec[j]| ≤ B·3328` and `B ≤ 4`:
      `|a_plus_b|, |a_minus_b| ≤ 2·B·3328 ≤ 8·3328 = 26624 ≤ 28296` (L0.2 pre).
      L0.2 post: `|o0| ≤ 3328`.
      L0.4 post: `|o1| ≤ 3328`.
    So both touched lanes end ≤ 3328 (tight). Coarsenings (≤ 2·3328, ≤ 4·3328)
    are derived at the layer level.

    The shape of the parameterized post mirrors `ntt_step_spec_B`: explicit
    unchanged-lane equality + two tight bounds on the touched lanes.
-/

/-- Tight parameterized inverse butterfly Triple. `B` is the input lane bound;
    output bound on touched lanes is the tight `3328`. -/
@[spec]
theorem inv_ntt_step_spec_B
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i j : Std.Usize) (B : Nat)
    (h_i : i.val < 16) (h_j : j.val < 16) (h_ne : i.val ≠ j.val)
    (h_zeta : zeta.val.natAbs ≤ 1664)
    (h_a : (vec.elements.val[i.val]!).val.natAbs ≤ B * 3328)
    (h_b : (vec.elements.val[j.val]!).val.natAbs ≤ B * 3328)
    (h_B : B ≤ 4) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step vec zeta i j
    ⦃ ⇓ r => ⌜ (∀ k : Nat, k < 16 → k ≠ i.val → k ≠ j.val →
                  r.elements.val[k]! = vec.elements.val[k]!)
              ∧ (r.elements.val[i.val]!).val.natAbs ≤ 3328
              ∧ (r.elements.val[j.val]!).val.natAbs ≤ 3328 ⌝ ⦄ := by
  have h_vec_len : vec.elements.length = 16 := PortableVector_elements_length vec
  -- Step 1: read vec[j] (= i1 in impl).
  have h_idx_j :
      Aeneas.Std.Array.index_usize vec.elements j = .ok (vec.elements.val[j.val]!) :=
    array_index_usize_ok_eq vec.elements j (by rw [h_vec_len]; exact h_j)
  -- Step 2: read vec[i] (= i2 in impl).
  have h_idx_i :
      Aeneas.Std.Array.index_usize vec.elements i = .ok (vec.elements.val[i.val]!) :=
    array_index_usize_ok_eq vec.elements i (by rw [h_vec_len]; exact h_i)
  set a : Std.I16 := vec.elements.val[i.val]! with ha_def
  set b : Std.I16 := vec.elements.val[j.val]! with hb_def
  -- Step 3: wrapping_sub b a (= a_minus_b).
  have h_sub_eq : CoreModels.core.num.I16.wrapping_sub b a = .ok (Std.I16.wrapping_sub b a) :=
    cm_wrapping_sub_ok_eq b a
  -- Step 4: wrapping_add b a (= a_plus_b).
  have h_add_eq : CoreModels.core.num.I16.wrapping_add b a = .ok (Std.I16.wrapping_add b a) :=
    cm_wrapping_add_ok_eq b a
  set a_minus_b : Std.I16 := Std.I16.wrapping_sub b a with hamb_def
  set a_plus_b  : Std.I16 := Std.I16.wrapping_add b a with hapb_def
  -- Direct no-overflow proof for b ± a with |b|, |a| ≤ B·3328, B ≤ 4.
  -- (`add_no_overflow_value_B` requires |t| ≤ 3328 on the second arg; we have
  --  the stronger |a| ≤ B·3328, so we re-derive in this generality.)
  have h_add_eq_val : (Std.I16.wrapping_add b a).val = b.val + a.val
      ∧ (Std.I16.wrapping_add b a).val.natAbs ≤ 2 * B * 3328 := by
    have h_sum_abs : ((b.val + a.val : Int)).natAbs ≤ 2 * B * 3328 := by
      have h_tri : (b.val + a.val).natAbs ≤ b.val.natAbs + a.val.natAbs :=
        Int.natAbs_add_le _ _
      omega
    have h_lb : -(2 ^ 15 : Int) ≤ b.val + a.val := by
      have h_bound : 2 * B * 3328 ≤ 8 * 3328 := by
        have : 2 * B ≤ 8 := by omega
        exact Nat.mul_le_mul_right _ this
      omega
    have h_ub : b.val + a.val < (2 ^ 15 : Int) := by
      have h_bound : 2 * B * 3328 ≤ 8 * 3328 := by
        have : 2 * B ≤ 8 := by omega
        exact Nat.mul_le_mul_right _ this
      omega
    have h_bmod : Int.bmod (b.val + a.val) (2 ^ 16) = b.val + a.val := by
      apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
      · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
        exact le_trans h_const h_lb
      · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
        exact lt_of_lt_of_le h_ub h_const
    have h_val := Std.I16.wrapping_add_val_eq b a
    exact ⟨by rw [h_val, h_bmod], by rw [h_val, h_bmod]; exact h_sum_abs⟩
  have h_sub_eq_val : (Std.I16.wrapping_sub b a).val = b.val - a.val
      ∧ (Std.I16.wrapping_sub b a).val.natAbs ≤ 2 * B * 3328 := by
    have h_diff_abs : ((b.val - a.val : Int)).natAbs ≤ 2 * B * 3328 := by
      have h_neg_natAbs : (-a.val).natAbs = a.val.natAbs := Int.natAbs_neg _
      have h_eq : b.val - a.val = b.val + (-a.val) := by ring
      rw [h_eq]
      have h_tri : (b.val + (-a.val)).natAbs ≤ b.val.natAbs + (-a.val).natAbs :=
        Int.natAbs_add_le _ _
      rw [h_neg_natAbs] at h_tri
      omega
    have h_lb : -(2 ^ 15 : Int) ≤ b.val - a.val := by
      have h_bound : 2 * B * 3328 ≤ 8 * 3328 := by
        have : 2 * B ≤ 8 := by omega
        exact Nat.mul_le_mul_right _ this
      omega
    have h_ub : b.val - a.val < (2 ^ 15 : Int) := by
      have h_bound : 2 * B * 3328 ≤ 8 * 3328 := by
        have : 2 * B ≤ 8 := by omega
        exact Nat.mul_le_mul_right _ this
      omega
    have h_bmod : Int.bmod (b.val - a.val) (2 ^ 16) = b.val - a.val := by
      apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
      · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
        exact le_trans h_const h_lb
      · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
        exact lt_of_lt_of_le h_ub h_const
    have h_val := Std.I16.wrapping_sub_val_eq b a
    exact ⟨by rw [h_val, h_bmod], by rw [h_val, h_bmod]; exact h_diff_abs⟩
  -- Bound on a_plus_b for L0.2: 2·B·3328 ≤ 8·3328 = 26624 ≤ 28296.
  have h_apb_bd : a_plus_b.val.natAbs ≤ 28296 := by
    rw [hapb_def]
    have h_step : 2 * B * 3328 ≤ 8 * 3328 := by
      have : 2 * B ≤ 8 := by omega
      exact Nat.mul_le_mul_right _ this
    have h := h_add_eq_val.2
    omega
  -- Step 5: L0.2 barrett_reduce_element on a_plus_b.
  obtain ⟨o0, h_o0_eq_ok, _h_o0_mod, h_o0_bd_t⟩ :=
    triple_exists_ok_l2 (barrett_reduce_element_spec a_plus_b
      (Nat.le_trans h_apb_bd (by decide : 28296 ≤ 32767)))
  -- `barrett_reduce_element_spec` gives the centered `≤ 1664`; the NTT layer
  -- invariants only need the looser `≤ 3328`, so weaken here.
  have h_o0_bd : o0.val.natAbs ≤ 3328 := Nat.le_trans h_o0_bd_t (by decide)
  -- Step 6: classify ζ.
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify zeta = .ok zeta :=
    classify_ok_eq zeta
  -- Step 7: L0.4 montgomery_multiply on (a_minus_b, ζ).
  obtain ⟨o1, h_o1_eq_ok, h_o1_bd, _h_o1_mod⟩ :=
    triple_exists_ok_l2 (montgomery_multiply_fe_by_fer_spec a_minus_b zeta h_zeta)
  -- Step 8: update vec at index i with o0.
  have h_upd_i :
      Aeneas.Std.Array.update vec.elements i o0
        = .ok (vec.elements.set i o0) :=
    array_update_ok_eq vec.elements i o0 (by rw [h_vec_len]; exact h_i)
  -- Step 9: update at index j with o1.
  have h_upd_j :
      Aeneas.Std.Array.update (vec.elements.set i o0) j o1
        = .ok ((vec.elements.set i o0).set j o1) := by
    have h_len : (vec.elements.set i o0).length = 16 := by
      rw [Std.Array.set_length]; exact h_vec_len
    exact array_update_ok_eq _ j o1 (by rw [h_len]; exact h_j)
  -- Compose into one `.ok` equation.
  set final_elements : Std.Array Std.I16 16#usize :=
    (vec.elements.set i o0).set j o1 with hfe_def
  set final_vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    { elements := final_elements } with hfv_def
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step vec zeta i j = .ok final_vec := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step
    rw [h_idx_j]; simp only [bind_tc_ok]
    rw [h_idx_i]; simp only [bind_tc_ok]
    rw [h_sub_eq]; simp only [bind_tc_ok]
    rw [h_add_eq]; simp only [bind_tc_ok]
    rw [h_o0_eq_ok]; simp only [bind_tc_ok]
    rw [h_classify]; simp only [bind_tc_ok]
    rw [h_o1_eq_ok]; simp only [bind_tc_ok]
    rw [h_upd_i]; simp only [bind_tc_ok]
    rw [h_upd_j]; simp only [bind_tc_ok]; rfl
  -- Close the Triple.
  apply triple_of_ok_l2 h_body
  refine ⟨?_, ?_, ?_⟩
  · -- Unchanged lanes: k ≠ i.val and k ≠ j.val.
    intro k hk_lt hk_ne_i hk_ne_j
    have h_set_j_ne :
        ((vec.elements.set i o0).set j o1)[k]!
          = (vec.elements.set i o0)[k]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ j k _ (Ne.symm hk_ne_j)
    have h_set_i_ne :
        (vec.elements.set i o0)[k]! = (vec.elements)[k]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ i k _ (Ne.symm hk_ne_i)
    show final_vec.elements.val[k]! = vec.elements.val[k]!
    show ((vec.elements.set i o0).set j o1).val[k]! = vec.elements.val[k]!
    rw [← Aeneas.Std.Array.getElem!_Nat_eq, ← Aeneas.Std.Array.getElem!_Nat_eq,
        h_set_j_ne, h_set_i_ne]
  · -- Bound on r.elements.val[i.val]!. Lane i gets o0 (barrett-reduced sum).
    show (final_vec.elements.val[i.val]!).val.natAbs ≤ 3328
    show (((vec.elements.set i o0).set j o1).val[i.val]!).val.natAbs ≤ 3328
    have h_eq1 :
        ((vec.elements.set i o0).set j o1).val[i.val]!
          = ((vec.elements.set i o0).set j o1)[i.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    have h_ne_ji : j.val ≠ i.val := (Ne.symm h_ne)
    have h_set_j_ne :
        ((vec.elements.set i o0).set j o1)[i.val]!
          = (vec.elements.set i o0)[i.val]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne _ j i.val _ h_ne_ji
    have h_set_i_eq :
        (vec.elements.set i o0)[i.val]! = o0 :=
      Aeneas.Std.Array.getElem!_Nat_set_eq _ i i.val _ ⟨rfl, by rw [h_vec_len]; exact h_i⟩
    rw [h_eq1, h_set_j_ne, h_set_i_eq]
    exact h_o0_bd
  · -- Bound on r.elements.val[j.val]!. Lane j gets o1 (mont-mul diff).
    show (final_vec.elements.val[j.val]!).val.natAbs ≤ 3328
    show (((vec.elements.set i o0).set j o1).val[j.val]!).val.natAbs ≤ 3328
    have h_eq1 :
        ((vec.elements.set i o0).set j o1).val[j.val]!
          = ((vec.elements.set i o0).set j o1)[j.val]! := by
      simp [Std.Array.getElem!_Nat_eq]
    have h_set_j_eq :
        ((vec.elements.set i o0).set j o1)[j.val]! = o1 := by
      have h_len : (vec.elements.set i o0).length = 16 := by
        rw [Std.Array.set_length]; exact h_vec_len
      exact Aeneas.Std.Array.getElem!_Nat_set_eq _ j j.val _ ⟨rfl, by rw [h_len]; exact h_j⟩
    rw [h_eq1, h_set_j_eq]
    exact h_o1_bd

/-- Named (B = 4) form matching the brief: `≤ 4·3328 → ≤ 4·3328` on all lanes. -/
@[spec]
theorem inv_ntt_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i j : Std.Usize)
    (h_i : i.val < 16) (h_j : j.val < 16) (h_ne : i.val ≠ j.val)
    (h_zeta : zeta.val.natAbs ≤ 1664)
    (hpre : ∀ k : Nat, k < 16 → (vec.elements.val[k]!).val.natAbs ≤ 4 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step vec zeta i j
    ⦃ ⇓ r => ⌜ ∀ k : Nat, k < 16 → (r.elements.val[k]!).val.natAbs ≤ 4 * 3328 ⌝ ⦄ := by
  obtain ⟨r, h_eq, h_unc, h_i_bd, h_j_bd⟩ :=
    triple_exists_ok_l2
      (inv_ntt_step_spec_B vec zeta i j 4 h_i h_j h_ne h_zeta (hpre i.val h_i)
        (hpre j.val h_j) (by decide))
  apply triple_of_ok_l2 h_eq
  intro k hk
  by_cases h_ki : k = i.val
  · subst h_ki
    have h_3328_le : (3328 : Nat) ≤ 4 * 3328 := by decide
    exact le_trans h_i_bd h_3328_le
  · by_cases h_kj : k = j.val
    · subst h_kj
      have h_3328_le : (3328 : Nat) ≤ 4 * 3328 := by decide
      exact le_trans h_j_bd h_3328_le
    · rw [h_unc k hk h_ki h_kj]
      exact hpre k hk

/-! ## L2.6 — `inv_ntt_layer_1_step_spec`

    Eight disjoint inverse butterflies on pairs `(0,2)ζ0`, `(1,3)ζ0`, `(4,6)ζ1`,
    `(5,7)ζ1`, `(8,10)ζ2`, `(9,11)ζ2`, `(12,14)ζ3`, `(13,15)ζ3`. Input lanes
    `≤ 3328` (B=1); each touched lane lands at `≤ 3328`; pairs cover all 16
    lanes, so post is `≤ 3328 ≤ 2·3328`.
-/

@[spec]
theorem inv_ntt_layer_1_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta0 zeta1 zeta2 zeta3 : Std.I16)
    (hz0 : zeta0.val.natAbs ≤ 1664) (hz1 : zeta1.val.natAbs ≤ 1664)
    (hz2 : zeta2.val.natAbs ≤ 1664) (hz3 : zeta3.val.natAbs ≤ 1664)
    (hpre : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_1_step
      vec zeta0 zeta1 zeta2 zeta3
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ 2 * 3328 ⌝ ⦄ := by
  have h0lt : (0#usize : Std.Usize).val < 16 := by decide
  have h1lt : (1#usize : Std.Usize).val < 16 := by decide
  have h2lt : (2#usize : Std.Usize).val < 16 := by decide
  have h3lt : (3#usize : Std.Usize).val < 16 := by decide
  have h4lt : (4#usize : Std.Usize).val < 16 := by decide
  have h5lt : (5#usize : Std.Usize).val < 16 := by decide
  have h6lt : (6#usize : Std.Usize).val < 16 := by decide
  have h7lt : (7#usize : Std.Usize).val < 16 := by decide
  have h8lt : (8#usize : Std.Usize).val < 16 := by decide
  have h9lt : (9#usize : Std.Usize).val < 16 := by decide
  have h10lt : (10#usize : Std.Usize).val < 16 := by decide
  have h11lt : (11#usize : Std.Usize).val < 16 := by decide
  have h12lt : (12#usize : Std.Usize).val < 16 := by decide
  have h13lt : (13#usize : Std.Usize).val < 16 := by decide
  have h14lt : (14#usize : Std.Usize).val < 16 := by decide
  have h15lt : (15#usize : Std.Usize).val < 16 := by decide
  have hb_init : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 1 * 3328 := by
    intro i hi; have := hpre i hi; omega
  -- Step 1: (0, 2) ζ0.
  obtain ⟨v1, h_v1_eq, h_v1_unc, h_v1_i, h_v1_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B vec zeta0 0#usize 2#usize 1
      h0lt h2lt (by decide) hz0 (hb_init 0 h0lt) (hb_init 2 h2lt) (by decide))
  -- Step 2: (1, 3) ζ0.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v1_unc 1 h1lt (by decide) (by decide)]; exact hb_init 1 h1lt
  have h_v1_3 : (v1.elements.val[3]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v1_unc 3 h3lt (by decide) (by decide)]; exact hb_init 3 h3lt
  obtain ⟨v2, h_v2_eq, h_v2_unc, h_v2_i, h_v2_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v1 zeta0 1#usize 3#usize 1
      h1lt h3lt (by decide) hz0 h_v1_1 h_v1_3 (by decide))
  -- Step 3: (4, 6) ζ1.
  have h_v2_4 : (v2.elements.val[4]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v2_unc 4 h4lt (by decide) (by decide), h_v1_unc 4 h4lt (by decide) (by decide)]
    exact hb_init 4 h4lt
  have h_v2_6 : (v2.elements.val[6]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v2_unc 6 h6lt (by decide) (by decide), h_v1_unc 6 h6lt (by decide) (by decide)]
    exact hb_init 6 h6lt
  obtain ⟨v3, h_v3_eq, h_v3_unc, h_v3_i, h_v3_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v2 zeta1 4#usize 6#usize 1
      h4lt h6lt (by decide) hz1 h_v2_4 h_v2_6 (by decide))
  -- Step 4: (5, 7) ζ1.
  have h_v3_5 : (v3.elements.val[5]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v3_unc 5 h5lt (by decide) (by decide),
        h_v2_unc 5 h5lt (by decide) (by decide),
        h_v1_unc 5 h5lt (by decide) (by decide)]
    exact hb_init 5 h5lt
  have h_v3_7 : (v3.elements.val[7]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v3_unc 7 h7lt (by decide) (by decide),
        h_v2_unc 7 h7lt (by decide) (by decide),
        h_v1_unc 7 h7lt (by decide) (by decide)]
    exact hb_init 7 h7lt
  obtain ⟨v4, h_v4_eq, h_v4_unc, h_v4_i, h_v4_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v3 zeta1 5#usize 7#usize 1
      h5lt h7lt (by decide) hz1 h_v3_5 h_v3_7 (by decide))
  -- Step 5: (8, 10) ζ2.
  have h_v4_8 : (v4.elements.val[8]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v4_unc 8 h8lt (by decide) (by decide),
        h_v3_unc 8 h8lt (by decide) (by decide),
        h_v2_unc 8 h8lt (by decide) (by decide),
        h_v1_unc 8 h8lt (by decide) (by decide)]
    exact hb_init 8 h8lt
  have h_v4_10 : (v4.elements.val[10]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v4_unc 10 h10lt (by decide) (by decide),
        h_v3_unc 10 h10lt (by decide) (by decide),
        h_v2_unc 10 h10lt (by decide) (by decide),
        h_v1_unc 10 h10lt (by decide) (by decide)]
    exact hb_init 10 h10lt
  obtain ⟨v5, h_v5_eq, h_v5_unc, h_v5_i, h_v5_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v4 zeta2 8#usize 10#usize 1
      h8lt h10lt (by decide) hz2 h_v4_8 h_v4_10 (by decide))
  -- Step 6: (9, 11) ζ2.
  have h_v5_9 : (v5.elements.val[9]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v5_unc 9 h9lt (by decide) (by decide),
        h_v4_unc 9 h9lt (by decide) (by decide),
        h_v3_unc 9 h9lt (by decide) (by decide),
        h_v2_unc 9 h9lt (by decide) (by decide),
        h_v1_unc 9 h9lt (by decide) (by decide)]
    exact hb_init 9 h9lt
  have h_v5_11 : (v5.elements.val[11]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v5_unc 11 h11lt (by decide) (by decide),
        h_v4_unc 11 h11lt (by decide) (by decide),
        h_v3_unc 11 h11lt (by decide) (by decide),
        h_v2_unc 11 h11lt (by decide) (by decide),
        h_v1_unc 11 h11lt (by decide) (by decide)]
    exact hb_init 11 h11lt
  obtain ⟨v6, h_v6_eq, h_v6_unc, h_v6_i, h_v6_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v5 zeta2 9#usize 11#usize 1
      h9lt h11lt (by decide) hz2 h_v5_9 h_v5_11 (by decide))
  -- Step 7: (12, 14) ζ3.
  have h_v6_12 : (v6.elements.val[12]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v6_unc 12 h12lt (by decide) (by decide),
        h_v5_unc 12 h12lt (by decide) (by decide),
        h_v4_unc 12 h12lt (by decide) (by decide),
        h_v3_unc 12 h12lt (by decide) (by decide),
        h_v2_unc 12 h12lt (by decide) (by decide),
        h_v1_unc 12 h12lt (by decide) (by decide)]
    exact hb_init 12 h12lt
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v6_unc 14 h14lt (by decide) (by decide),
        h_v5_unc 14 h14lt (by decide) (by decide),
        h_v4_unc 14 h14lt (by decide) (by decide),
        h_v3_unc 14 h14lt (by decide) (by decide),
        h_v2_unc 14 h14lt (by decide) (by decide),
        h_v1_unc 14 h14lt (by decide) (by decide)]
    exact hb_init 14 h14lt
  obtain ⟨v7, h_v7_eq, h_v7_unc, h_v7_i, h_v7_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v6 zeta3 12#usize 14#usize 1
      h12lt h14lt (by decide) hz3 h_v6_12 h_v6_14 (by decide))
  -- Step 8: (13, 15) ζ3.
  have h_v7_13 : (v7.elements.val[13]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v7_unc 13 h13lt (by decide) (by decide),
        h_v6_unc 13 h13lt (by decide) (by decide),
        h_v5_unc 13 h13lt (by decide) (by decide),
        h_v4_unc 13 h13lt (by decide) (by decide),
        h_v3_unc 13 h13lt (by decide) (by decide),
        h_v2_unc 13 h13lt (by decide) (by decide),
        h_v1_unc 13 h13lt (by decide) (by decide)]
    exact hb_init 13 h13lt
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 1 * 3328 := by
    rw [h_v7_unc 15 h15lt (by decide) (by decide),
        h_v6_unc 15 h15lt (by decide) (by decide),
        h_v5_unc 15 h15lt (by decide) (by decide),
        h_v4_unc 15 h15lt (by decide) (by decide),
        h_v3_unc 15 h15lt (by decide) (by decide),
        h_v2_unc 15 h15lt (by decide) (by decide),
        h_v1_unc 15 h15lt (by decide) (by decide)]
    exact hb_init 15 h15lt
  obtain ⟨v8, h_v8_eq, h_v8_unc, h_v8_i, h_v8_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v7 zeta3 13#usize 15#usize 1
      h13lt h15lt (by decide) hz3 h_v7_13 h_v7_15 (by decide))
  -- Compose into one `.ok v8` equation.
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3
        = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_1_step
    rw [h_v1_eq]; simp only [bind_tc_ok]
    rw [h_v2_eq]; simp only [bind_tc_ok]
    rw [h_v3_eq]; simp only [bind_tc_ok]
    rw [h_v4_eq]; simp only [bind_tc_ok]
    rw [h_v5_eq]; simp only [bind_tc_ok]
    rw [h_v6_eq]; simp only [bind_tc_ok]
    rw [h_v7_eq]; simp only [bind_tc_ok]
    exact h_v8_eq
  apply triple_of_ok_l2 h_body
  intro i hi
  -- Each lane is touched exactly once and ends at ≤ 3328 ≤ 2·3328.
  have h_3328 : (3328 : Nat) ≤ 2 * 3328 := by decide
  interval_cases i
  -- Lane 0: step 1 i-lane.
  · have h_eq : v8.elements.val[0]! = v1.elements.val[0]! := by
      rw [h_v8_unc 0 h0lt (by decide) (by decide),
          h_v7_unc 0 h0lt (by decide) (by decide),
          h_v6_unc 0 h0lt (by decide) (by decide),
          h_v5_unc 0 h0lt (by decide) (by decide),
          h_v4_unc 0 h0lt (by decide) (by decide),
          h_v3_unc 0 h0lt (by decide) (by decide),
          h_v2_unc 0 h0lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v1_i h_3328
  -- Lane 1: step 2 i-lane.
  · have h_eq : v8.elements.val[1]! = v2.elements.val[1]! := by
      rw [h_v8_unc 1 h1lt (by decide) (by decide),
          h_v7_unc 1 h1lt (by decide) (by decide),
          h_v6_unc 1 h1lt (by decide) (by decide),
          h_v5_unc 1 h1lt (by decide) (by decide),
          h_v4_unc 1 h1lt (by decide) (by decide),
          h_v3_unc 1 h1lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v2_i h_3328
  -- Lane 2: step 1 j-lane.
  · have h_eq : v8.elements.val[2]! = v1.elements.val[2]! := by
      rw [h_v8_unc 2 h2lt (by decide) (by decide),
          h_v7_unc 2 h2lt (by decide) (by decide),
          h_v6_unc 2 h2lt (by decide) (by decide),
          h_v5_unc 2 h2lt (by decide) (by decide),
          h_v4_unc 2 h2lt (by decide) (by decide),
          h_v3_unc 2 h2lt (by decide) (by decide),
          h_v2_unc 2 h2lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v1_j h_3328
  -- Lane 3: step 2 j-lane.
  · have h_eq : v8.elements.val[3]! = v2.elements.val[3]! := by
      rw [h_v8_unc 3 h3lt (by decide) (by decide),
          h_v7_unc 3 h3lt (by decide) (by decide),
          h_v6_unc 3 h3lt (by decide) (by decide),
          h_v5_unc 3 h3lt (by decide) (by decide),
          h_v4_unc 3 h3lt (by decide) (by decide),
          h_v3_unc 3 h3lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v2_j h_3328
  -- Lane 4: step 3 i-lane.
  · have h_eq : v8.elements.val[4]! = v3.elements.val[4]! := by
      rw [h_v8_unc 4 h4lt (by decide) (by decide),
          h_v7_unc 4 h4lt (by decide) (by decide),
          h_v6_unc 4 h4lt (by decide) (by decide),
          h_v5_unc 4 h4lt (by decide) (by decide),
          h_v4_unc 4 h4lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v3_i h_3328
  -- Lane 5: step 4 i-lane.
  · have h_eq : v8.elements.val[5]! = v4.elements.val[5]! := by
      rw [h_v8_unc 5 h5lt (by decide) (by decide),
          h_v7_unc 5 h5lt (by decide) (by decide),
          h_v6_unc 5 h5lt (by decide) (by decide),
          h_v5_unc 5 h5lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v4_i h_3328
  -- Lane 6: step 3 j-lane.
  · have h_eq : v8.elements.val[6]! = v3.elements.val[6]! := by
      rw [h_v8_unc 6 h6lt (by decide) (by decide),
          h_v7_unc 6 h6lt (by decide) (by decide),
          h_v6_unc 6 h6lt (by decide) (by decide),
          h_v5_unc 6 h6lt (by decide) (by decide),
          h_v4_unc 6 h6lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v3_j h_3328
  -- Lane 7: step 4 j-lane.
  · have h_eq : v8.elements.val[7]! = v4.elements.val[7]! := by
      rw [h_v8_unc 7 h7lt (by decide) (by decide),
          h_v7_unc 7 h7lt (by decide) (by decide),
          h_v6_unc 7 h7lt (by decide) (by decide),
          h_v5_unc 7 h7lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v4_j h_3328
  -- Lane 8: step 5 i-lane.
  · have h_eq : v8.elements.val[8]! = v5.elements.val[8]! := by
      rw [h_v8_unc 8 h8lt (by decide) (by decide),
          h_v7_unc 8 h8lt (by decide) (by decide),
          h_v6_unc 8 h8lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v5_i h_3328
  -- Lane 9: step 6 i-lane.
  · have h_eq : v8.elements.val[9]! = v6.elements.val[9]! := by
      rw [h_v8_unc 9 h9lt (by decide) (by decide),
          h_v7_unc 9 h9lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v6_i h_3328
  -- Lane 10: step 5 j-lane.
  · have h_eq : v8.elements.val[10]! = v5.elements.val[10]! := by
      rw [h_v8_unc 10 h10lt (by decide) (by decide),
          h_v7_unc 10 h10lt (by decide) (by decide),
          h_v6_unc 10 h10lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v5_j h_3328
  -- Lane 11: step 6 j-lane.
  · have h_eq : v8.elements.val[11]! = v6.elements.val[11]! := by
      rw [h_v8_unc 11 h11lt (by decide) (by decide),
          h_v7_unc 11 h11lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v6_j h_3328
  -- Lane 12: step 7 i-lane.
  · have h_eq : v8.elements.val[12]! = v7.elements.val[12]! := by
      rw [h_v8_unc 12 h12lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v7_i h_3328
  -- Lane 13: step 8 i-lane.
  · exact le_trans h_v8_i h_3328
  -- Lane 14: step 7 j-lane.
  · have h_eq : v8.elements.val[14]! = v7.elements.val[14]! := by
      rw [h_v8_unc 14 h14lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v7_j h_3328
  -- Lane 15: step 8 j-lane.
  · exact le_trans h_v8_j h_3328

/-! ## L2.7a — `inv_ntt_layer_2_step_spec`

    Eight disjoint inverse butterflies on pairs `(0,4)ζ0`, `(1,5)ζ0`, `(2,6)ζ0`,
    `(3,7)ζ0`, `(8,12)ζ1`, `(9,13)ζ1`, `(10,14)ζ1`, `(11,15)ζ1`. Input bound
    `≤ 2·3328` (B=2); each touched lane lands at `≤ 3328 ≤ 4·3328`.
-/

@[spec]
theorem inv_ntt_layer_2_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta0 zeta1 : Std.I16)
    (hz0 : zeta0.val.natAbs ≤ 1664) (hz1 : zeta1.val.natAbs ≤ 1664)
    (hpre : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 2 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_2_step vec zeta0 zeta1
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ 4 * 3328 ⌝ ⦄ := by
  have h0lt : (0#usize : Std.Usize).val < 16 := by decide
  have h1lt : (1#usize : Std.Usize).val < 16 := by decide
  have h2lt : (2#usize : Std.Usize).val < 16 := by decide
  have h3lt : (3#usize : Std.Usize).val < 16 := by decide
  have h4lt : (4#usize : Std.Usize).val < 16 := by decide
  have h5lt : (5#usize : Std.Usize).val < 16 := by decide
  have h6lt : (6#usize : Std.Usize).val < 16 := by decide
  have h7lt : (7#usize : Std.Usize).val < 16 := by decide
  have h8lt : (8#usize : Std.Usize).val < 16 := by decide
  have h9lt : (9#usize : Std.Usize).val < 16 := by decide
  have h10lt : (10#usize : Std.Usize).val < 16 := by decide
  have h11lt : (11#usize : Std.Usize).val < 16 := by decide
  have h12lt : (12#usize : Std.Usize).val < 16 := by decide
  have h13lt : (13#usize : Std.Usize).val < 16 := by decide
  have h14lt : (14#usize : Std.Usize).val < 16 := by decide
  have h15lt : (15#usize : Std.Usize).val < 16 := by decide
  have hb_init : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 2 * 3328 := hpre
  -- Step 1: (0, 4) ζ0.
  obtain ⟨v1, h_v1_eq, h_v1_unc, h_v1_i, h_v1_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B vec zeta0 0#usize 4#usize 2
      h0lt h4lt (by decide) hz0 (hb_init 0 h0lt) (hb_init 4 h4lt) (by decide))
  -- Step 2: (1, 5) ζ0.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v1_unc 1 h1lt (by decide) (by decide)]; exact hb_init 1 h1lt
  have h_v1_5 : (v1.elements.val[5]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v1_unc 5 h5lt (by decide) (by decide)]; exact hb_init 5 h5lt
  obtain ⟨v2, h_v2_eq, h_v2_unc, h_v2_i, h_v2_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v1 zeta0 1#usize 5#usize 2
      h1lt h5lt (by decide) hz0 h_v1_1 h_v1_5 (by decide))
  -- Step 3: (2, 6) ζ0.
  have h_v2_2 : (v2.elements.val[2]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v2_unc 2 h2lt (by decide) (by decide), h_v1_unc 2 h2lt (by decide) (by decide)]
    exact hb_init 2 h2lt
  have h_v2_6 : (v2.elements.val[6]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v2_unc 6 h6lt (by decide) (by decide), h_v1_unc 6 h6lt (by decide) (by decide)]
    exact hb_init 6 h6lt
  obtain ⟨v3, h_v3_eq, h_v3_unc, h_v3_i, h_v3_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v2 zeta0 2#usize 6#usize 2
      h2lt h6lt (by decide) hz0 h_v2_2 h_v2_6 (by decide))
  -- Step 4: (3, 7) ζ0.
  have h_v3_3 : (v3.elements.val[3]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v3_unc 3 h3lt (by decide) (by decide),
        h_v2_unc 3 h3lt (by decide) (by decide),
        h_v1_unc 3 h3lt (by decide) (by decide)]
    exact hb_init 3 h3lt
  have h_v3_7 : (v3.elements.val[7]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v3_unc 7 h7lt (by decide) (by decide),
        h_v2_unc 7 h7lt (by decide) (by decide),
        h_v1_unc 7 h7lt (by decide) (by decide)]
    exact hb_init 7 h7lt
  obtain ⟨v4, h_v4_eq, h_v4_unc, h_v4_i, h_v4_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v3 zeta0 3#usize 7#usize 2
      h3lt h7lt (by decide) hz0 h_v3_3 h_v3_7 (by decide))
  -- Step 5: (8, 12) ζ1.
  have h_v4_8 : (v4.elements.val[8]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v4_unc 8 h8lt (by decide) (by decide),
        h_v3_unc 8 h8lt (by decide) (by decide),
        h_v2_unc 8 h8lt (by decide) (by decide),
        h_v1_unc 8 h8lt (by decide) (by decide)]
    exact hb_init 8 h8lt
  have h_v4_12 : (v4.elements.val[12]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v4_unc 12 h12lt (by decide) (by decide),
        h_v3_unc 12 h12lt (by decide) (by decide),
        h_v2_unc 12 h12lt (by decide) (by decide),
        h_v1_unc 12 h12lt (by decide) (by decide)]
    exact hb_init 12 h12lt
  obtain ⟨v5, h_v5_eq, h_v5_unc, h_v5_i, h_v5_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v4 zeta1 8#usize 12#usize 2
      h8lt h12lt (by decide) hz1 h_v4_8 h_v4_12 (by decide))
  -- Step 6: (9, 13) ζ1.
  have h_v5_9 : (v5.elements.val[9]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v5_unc 9 h9lt (by decide) (by decide),
        h_v4_unc 9 h9lt (by decide) (by decide),
        h_v3_unc 9 h9lt (by decide) (by decide),
        h_v2_unc 9 h9lt (by decide) (by decide),
        h_v1_unc 9 h9lt (by decide) (by decide)]
    exact hb_init 9 h9lt
  have h_v5_13 : (v5.elements.val[13]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v5_unc 13 h13lt (by decide) (by decide),
        h_v4_unc 13 h13lt (by decide) (by decide),
        h_v3_unc 13 h13lt (by decide) (by decide),
        h_v2_unc 13 h13lt (by decide) (by decide),
        h_v1_unc 13 h13lt (by decide) (by decide)]
    exact hb_init 13 h13lt
  obtain ⟨v6, h_v6_eq, h_v6_unc, h_v6_i, h_v6_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v5 zeta1 9#usize 13#usize 2
      h9lt h13lt (by decide) hz1 h_v5_9 h_v5_13 (by decide))
  -- Step 7: (10, 14) ζ1.
  have h_v6_10 : (v6.elements.val[10]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v6_unc 10 h10lt (by decide) (by decide),
        h_v5_unc 10 h10lt (by decide) (by decide),
        h_v4_unc 10 h10lt (by decide) (by decide),
        h_v3_unc 10 h10lt (by decide) (by decide),
        h_v2_unc 10 h10lt (by decide) (by decide),
        h_v1_unc 10 h10lt (by decide) (by decide)]
    exact hb_init 10 h10lt
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v6_unc 14 h14lt (by decide) (by decide),
        h_v5_unc 14 h14lt (by decide) (by decide),
        h_v4_unc 14 h14lt (by decide) (by decide),
        h_v3_unc 14 h14lt (by decide) (by decide),
        h_v2_unc 14 h14lt (by decide) (by decide),
        h_v1_unc 14 h14lt (by decide) (by decide)]
    exact hb_init 14 h14lt
  obtain ⟨v7, h_v7_eq, h_v7_unc, h_v7_i, h_v7_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v6 zeta1 10#usize 14#usize 2
      h10lt h14lt (by decide) hz1 h_v6_10 h_v6_14 (by decide))
  -- Step 8: (11, 15) ζ1.
  have h_v7_11 : (v7.elements.val[11]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v7_unc 11 h11lt (by decide) (by decide),
        h_v6_unc 11 h11lt (by decide) (by decide),
        h_v5_unc 11 h11lt (by decide) (by decide),
        h_v4_unc 11 h11lt (by decide) (by decide),
        h_v3_unc 11 h11lt (by decide) (by decide),
        h_v2_unc 11 h11lt (by decide) (by decide),
        h_v1_unc 11 h11lt (by decide) (by decide)]
    exact hb_init 11 h11lt
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v7_unc 15 h15lt (by decide) (by decide),
        h_v6_unc 15 h15lt (by decide) (by decide),
        h_v5_unc 15 h15lt (by decide) (by decide),
        h_v4_unc 15 h15lt (by decide) (by decide),
        h_v3_unc 15 h15lt (by decide) (by decide),
        h_v2_unc 15 h15lt (by decide) (by decide),
        h_v1_unc 15 h15lt (by decide) (by decide)]
    exact hb_init 15 h15lt
  obtain ⟨v8, h_v8_eq, h_v8_unc, h_v8_i, h_v8_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v7 zeta1 11#usize 15#usize 2
      h11lt h15lt (by decide) hz1 h_v7_11 h_v7_15 (by decide))
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_2_step vec zeta0 zeta1
        = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_2_step
    rw [h_v1_eq]; simp only [bind_tc_ok]
    rw [h_v2_eq]; simp only [bind_tc_ok]
    rw [h_v3_eq]; simp only [bind_tc_ok]
    rw [h_v4_eq]; simp only [bind_tc_ok]
    rw [h_v5_eq]; simp only [bind_tc_ok]
    rw [h_v6_eq]; simp only [bind_tc_ok]
    rw [h_v7_eq]; simp only [bind_tc_ok]
    exact h_v8_eq
  apply triple_of_ok_l2 h_body
  intro i hi
  have h_3328 : (3328 : Nat) ≤ 4 * 3328 := by decide
  interval_cases i
  -- Lane 0: step 1 i-lane.
  · have h_eq : v8.elements.val[0]! = v1.elements.val[0]! := by
      rw [h_v8_unc 0 h0lt (by decide) (by decide),
          h_v7_unc 0 h0lt (by decide) (by decide),
          h_v6_unc 0 h0lt (by decide) (by decide),
          h_v5_unc 0 h0lt (by decide) (by decide),
          h_v4_unc 0 h0lt (by decide) (by decide),
          h_v3_unc 0 h0lt (by decide) (by decide),
          h_v2_unc 0 h0lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v1_i h_3328
  -- Lane 1: step 2 i-lane.
  · have h_eq : v8.elements.val[1]! = v2.elements.val[1]! := by
      rw [h_v8_unc 1 h1lt (by decide) (by decide),
          h_v7_unc 1 h1lt (by decide) (by decide),
          h_v6_unc 1 h1lt (by decide) (by decide),
          h_v5_unc 1 h1lt (by decide) (by decide),
          h_v4_unc 1 h1lt (by decide) (by decide),
          h_v3_unc 1 h1lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v2_i h_3328
  -- Lane 2: step 3 i-lane.
  · have h_eq : v8.elements.val[2]! = v3.elements.val[2]! := by
      rw [h_v8_unc 2 h2lt (by decide) (by decide),
          h_v7_unc 2 h2lt (by decide) (by decide),
          h_v6_unc 2 h2lt (by decide) (by decide),
          h_v5_unc 2 h2lt (by decide) (by decide),
          h_v4_unc 2 h2lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v3_i h_3328
  -- Lane 3: step 4 i-lane.
  · have h_eq : v8.elements.val[3]! = v4.elements.val[3]! := by
      rw [h_v8_unc 3 h3lt (by decide) (by decide),
          h_v7_unc 3 h3lt (by decide) (by decide),
          h_v6_unc 3 h3lt (by decide) (by decide),
          h_v5_unc 3 h3lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v4_i h_3328
  -- Lane 4: step 1 j-lane.
  · have h_eq : v8.elements.val[4]! = v1.elements.val[4]! := by
      rw [h_v8_unc 4 h4lt (by decide) (by decide),
          h_v7_unc 4 h4lt (by decide) (by decide),
          h_v6_unc 4 h4lt (by decide) (by decide),
          h_v5_unc 4 h4lt (by decide) (by decide),
          h_v4_unc 4 h4lt (by decide) (by decide),
          h_v3_unc 4 h4lt (by decide) (by decide),
          h_v2_unc 4 h4lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v1_j h_3328
  -- Lane 5: step 2 j-lane.
  · have h_eq : v8.elements.val[5]! = v2.elements.val[5]! := by
      rw [h_v8_unc 5 h5lt (by decide) (by decide),
          h_v7_unc 5 h5lt (by decide) (by decide),
          h_v6_unc 5 h5lt (by decide) (by decide),
          h_v5_unc 5 h5lt (by decide) (by decide),
          h_v4_unc 5 h5lt (by decide) (by decide),
          h_v3_unc 5 h5lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v2_j h_3328
  -- Lane 6: step 3 j-lane.
  · have h_eq : v8.elements.val[6]! = v3.elements.val[6]! := by
      rw [h_v8_unc 6 h6lt (by decide) (by decide),
          h_v7_unc 6 h6lt (by decide) (by decide),
          h_v6_unc 6 h6lt (by decide) (by decide),
          h_v5_unc 6 h6lt (by decide) (by decide),
          h_v4_unc 6 h6lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v3_j h_3328
  -- Lane 7: step 4 j-lane.
  · have h_eq : v8.elements.val[7]! = v4.elements.val[7]! := by
      rw [h_v8_unc 7 h7lt (by decide) (by decide),
          h_v7_unc 7 h7lt (by decide) (by decide),
          h_v6_unc 7 h7lt (by decide) (by decide),
          h_v5_unc 7 h7lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v4_j h_3328
  -- Lane 8: step 5 i-lane.
  · have h_eq : v8.elements.val[8]! = v5.elements.val[8]! := by
      rw [h_v8_unc 8 h8lt (by decide) (by decide),
          h_v7_unc 8 h8lt (by decide) (by decide),
          h_v6_unc 8 h8lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v5_i h_3328
  -- Lane 9: step 6 i-lane.
  · have h_eq : v8.elements.val[9]! = v6.elements.val[9]! := by
      rw [h_v8_unc 9 h9lt (by decide) (by decide),
          h_v7_unc 9 h9lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v6_i h_3328
  -- Lane 10: step 7 i-lane.
  · have h_eq : v8.elements.val[10]! = v7.elements.val[10]! := by
      rw [h_v8_unc 10 h10lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v7_i h_3328
  -- Lane 11: step 8 i-lane.
  · exact le_trans h_v8_i h_3328
  -- Lane 12: step 5 j-lane.
  · have h_eq : v8.elements.val[12]! = v5.elements.val[12]! := by
      rw [h_v8_unc 12 h12lt (by decide) (by decide),
          h_v7_unc 12 h12lt (by decide) (by decide),
          h_v6_unc 12 h12lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v5_j h_3328
  -- Lane 13: step 6 j-lane.
  · have h_eq : v8.elements.val[13]! = v6.elements.val[13]! := by
      rw [h_v8_unc 13 h13lt (by decide) (by decide),
          h_v7_unc 13 h13lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v6_j h_3328
  -- Lane 14: step 7 j-lane.
  · have h_eq : v8.elements.val[14]! = v7.elements.val[14]! := by
      rw [h_v8_unc 14 h14lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v7_j h_3328
  -- Lane 15: step 8 j-lane.
  · exact le_trans h_v8_j h_3328

/-! ## L2.7b — `inv_ntt_layer_3_step_spec`

    Eight disjoint inverse butterflies on pairs `(0,8)`, `(1,9)`, …, `(7,15)`
    all with the single ζ. Input bound `≤ 2·3328` (B=2); each touched lane
    lands at `≤ 3328 ≤ 4·3328`.
-/

@[spec]
theorem inv_ntt_layer_3_step_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (hz : zeta.val.natAbs ≤ 1664)
    (hpre : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 2 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_3_step vec zeta
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ 4 * 3328 ⌝ ⦄ := by
  have h0lt : (0#usize : Std.Usize).val < 16 := by decide
  have h1lt : (1#usize : Std.Usize).val < 16 := by decide
  have h2lt : (2#usize : Std.Usize).val < 16 := by decide
  have h3lt : (3#usize : Std.Usize).val < 16 := by decide
  have h4lt : (4#usize : Std.Usize).val < 16 := by decide
  have h5lt : (5#usize : Std.Usize).val < 16 := by decide
  have h6lt : (6#usize : Std.Usize).val < 16 := by decide
  have h7lt : (7#usize : Std.Usize).val < 16 := by decide
  have h8lt : (8#usize : Std.Usize).val < 16 := by decide
  have h9lt : (9#usize : Std.Usize).val < 16 := by decide
  have h10lt : (10#usize : Std.Usize).val < 16 := by decide
  have h11lt : (11#usize : Std.Usize).val < 16 := by decide
  have h12lt : (12#usize : Std.Usize).val < 16 := by decide
  have h13lt : (13#usize : Std.Usize).val < 16 := by decide
  have h14lt : (14#usize : Std.Usize).val < 16 := by decide
  have h15lt : (15#usize : Std.Usize).val < 16 := by decide
  have hb_init : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 2 * 3328 := hpre
  -- Step 1: (0, 8).
  obtain ⟨v1, h_v1_eq, h_v1_unc, h_v1_i, h_v1_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B vec zeta 0#usize 8#usize 2
      h0lt h8lt (by decide) hz (hb_init 0 h0lt) (hb_init 8 h8lt) (by decide))
  -- Step 2: (1, 9).
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v1_unc 1 h1lt (by decide) (by decide)]; exact hb_init 1 h1lt
  have h_v1_9 : (v1.elements.val[9]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v1_unc 9 h9lt (by decide) (by decide)]; exact hb_init 9 h9lt
  obtain ⟨v2, h_v2_eq, h_v2_unc, h_v2_i, h_v2_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v1 zeta 1#usize 9#usize 2
      h1lt h9lt (by decide) hz h_v1_1 h_v1_9 (by decide))
  -- Step 3: (2, 10).
  have h_v2_2 : (v2.elements.val[2]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v2_unc 2 h2lt (by decide) (by decide), h_v1_unc 2 h2lt (by decide) (by decide)]
    exact hb_init 2 h2lt
  have h_v2_10 : (v2.elements.val[10]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v2_unc 10 h10lt (by decide) (by decide), h_v1_unc 10 h10lt (by decide) (by decide)]
    exact hb_init 10 h10lt
  obtain ⟨v3, h_v3_eq, h_v3_unc, h_v3_i, h_v3_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v2 zeta 2#usize 10#usize 2
      h2lt h10lt (by decide) hz h_v2_2 h_v2_10 (by decide))
  -- Step 4: (3, 11).
  have h_v3_3 : (v3.elements.val[3]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v3_unc 3 h3lt (by decide) (by decide),
        h_v2_unc 3 h3lt (by decide) (by decide),
        h_v1_unc 3 h3lt (by decide) (by decide)]
    exact hb_init 3 h3lt
  have h_v3_11 : (v3.elements.val[11]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v3_unc 11 h11lt (by decide) (by decide),
        h_v2_unc 11 h11lt (by decide) (by decide),
        h_v1_unc 11 h11lt (by decide) (by decide)]
    exact hb_init 11 h11lt
  obtain ⟨v4, h_v4_eq, h_v4_unc, h_v4_i, h_v4_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v3 zeta 3#usize 11#usize 2
      h3lt h11lt (by decide) hz h_v3_3 h_v3_11 (by decide))
  -- Step 5: (4, 12).
  have h_v4_4 : (v4.elements.val[4]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v4_unc 4 h4lt (by decide) (by decide),
        h_v3_unc 4 h4lt (by decide) (by decide),
        h_v2_unc 4 h4lt (by decide) (by decide),
        h_v1_unc 4 h4lt (by decide) (by decide)]
    exact hb_init 4 h4lt
  have h_v4_12 : (v4.elements.val[12]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v4_unc 12 h12lt (by decide) (by decide),
        h_v3_unc 12 h12lt (by decide) (by decide),
        h_v2_unc 12 h12lt (by decide) (by decide),
        h_v1_unc 12 h12lt (by decide) (by decide)]
    exact hb_init 12 h12lt
  obtain ⟨v5, h_v5_eq, h_v5_unc, h_v5_i, h_v5_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v4 zeta 4#usize 12#usize 2
      h4lt h12lt (by decide) hz h_v4_4 h_v4_12 (by decide))
  -- Step 6: (5, 13).
  have h_v5_5 : (v5.elements.val[5]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v5_unc 5 h5lt (by decide) (by decide),
        h_v4_unc 5 h5lt (by decide) (by decide),
        h_v3_unc 5 h5lt (by decide) (by decide),
        h_v2_unc 5 h5lt (by decide) (by decide),
        h_v1_unc 5 h5lt (by decide) (by decide)]
    exact hb_init 5 h5lt
  have h_v5_13 : (v5.elements.val[13]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v5_unc 13 h13lt (by decide) (by decide),
        h_v4_unc 13 h13lt (by decide) (by decide),
        h_v3_unc 13 h13lt (by decide) (by decide),
        h_v2_unc 13 h13lt (by decide) (by decide),
        h_v1_unc 13 h13lt (by decide) (by decide)]
    exact hb_init 13 h13lt
  obtain ⟨v6, h_v6_eq, h_v6_unc, h_v6_i, h_v6_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v5 zeta 5#usize 13#usize 2
      h5lt h13lt (by decide) hz h_v5_5 h_v5_13 (by decide))
  -- Step 7: (6, 14).
  have h_v6_6 : (v6.elements.val[6]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v6_unc 6 h6lt (by decide) (by decide),
        h_v5_unc 6 h6lt (by decide) (by decide),
        h_v4_unc 6 h6lt (by decide) (by decide),
        h_v3_unc 6 h6lt (by decide) (by decide),
        h_v2_unc 6 h6lt (by decide) (by decide),
        h_v1_unc 6 h6lt (by decide) (by decide)]
    exact hb_init 6 h6lt
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v6_unc 14 h14lt (by decide) (by decide),
        h_v5_unc 14 h14lt (by decide) (by decide),
        h_v4_unc 14 h14lt (by decide) (by decide),
        h_v3_unc 14 h14lt (by decide) (by decide),
        h_v2_unc 14 h14lt (by decide) (by decide),
        h_v1_unc 14 h14lt (by decide) (by decide)]
    exact hb_init 14 h14lt
  obtain ⟨v7, h_v7_eq, h_v7_unc, h_v7_i, h_v7_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v6 zeta 6#usize 14#usize 2
      h6lt h14lt (by decide) hz h_v6_6 h_v6_14 (by decide))
  -- Step 8: (7, 15).
  have h_v7_7 : (v7.elements.val[7]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v7_unc 7 h7lt (by decide) (by decide),
        h_v6_unc 7 h7lt (by decide) (by decide),
        h_v5_unc 7 h7lt (by decide) (by decide),
        h_v4_unc 7 h7lt (by decide) (by decide),
        h_v3_unc 7 h7lt (by decide) (by decide),
        h_v2_unc 7 h7lt (by decide) (by decide),
        h_v1_unc 7 h7lt (by decide) (by decide)]
    exact hb_init 7 h7lt
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 2 * 3328 := by
    rw [h_v7_unc 15 h15lt (by decide) (by decide),
        h_v6_unc 15 h15lt (by decide) (by decide),
        h_v5_unc 15 h15lt (by decide) (by decide),
        h_v4_unc 15 h15lt (by decide) (by decide),
        h_v3_unc 15 h15lt (by decide) (by decide),
        h_v2_unc 15 h15lt (by decide) (by decide),
        h_v1_unc 15 h15lt (by decide) (by decide)]
    exact hb_init 15 h15lt
  obtain ⟨v8, h_v8_eq, h_v8_unc, h_v8_i, h_v8_j⟩ :=
    triple_exists_ok_l2 (inv_ntt_step_spec_B v7 zeta 7#usize 15#usize 2
      h7lt h15lt (by decide) hz h_v7_7 h_v7_15 (by decide))
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_3_step vec zeta = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_3_step
    rw [h_v1_eq]; simp only [bind_tc_ok]
    rw [h_v2_eq]; simp only [bind_tc_ok]
    rw [h_v3_eq]; simp only [bind_tc_ok]
    rw [h_v4_eq]; simp only [bind_tc_ok]
    rw [h_v5_eq]; simp only [bind_tc_ok]
    rw [h_v6_eq]; simp only [bind_tc_ok]
    rw [h_v7_eq]; simp only [bind_tc_ok]
    exact h_v8_eq
  apply triple_of_ok_l2 h_body
  intro i hi
  have h_3328 : (3328 : Nat) ≤ 4 * 3328 := by decide
  interval_cases i
  -- Lane 0: step 1 i-lane.
  · have h_eq : v8.elements.val[0]! = v1.elements.val[0]! := by
      rw [h_v8_unc 0 h0lt (by decide) (by decide),
          h_v7_unc 0 h0lt (by decide) (by decide),
          h_v6_unc 0 h0lt (by decide) (by decide),
          h_v5_unc 0 h0lt (by decide) (by decide),
          h_v4_unc 0 h0lt (by decide) (by decide),
          h_v3_unc 0 h0lt (by decide) (by decide),
          h_v2_unc 0 h0lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v1_i h_3328
  -- Lane 1: step 2 i-lane.
  · have h_eq : v8.elements.val[1]! = v2.elements.val[1]! := by
      rw [h_v8_unc 1 h1lt (by decide) (by decide),
          h_v7_unc 1 h1lt (by decide) (by decide),
          h_v6_unc 1 h1lt (by decide) (by decide),
          h_v5_unc 1 h1lt (by decide) (by decide),
          h_v4_unc 1 h1lt (by decide) (by decide),
          h_v3_unc 1 h1lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v2_i h_3328
  -- Lane 2: step 3 i-lane.
  · have h_eq : v8.elements.val[2]! = v3.elements.val[2]! := by
      rw [h_v8_unc 2 h2lt (by decide) (by decide),
          h_v7_unc 2 h2lt (by decide) (by decide),
          h_v6_unc 2 h2lt (by decide) (by decide),
          h_v5_unc 2 h2lt (by decide) (by decide),
          h_v4_unc 2 h2lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v3_i h_3328
  -- Lane 3: step 4 i-lane.
  · have h_eq : v8.elements.val[3]! = v4.elements.val[3]! := by
      rw [h_v8_unc 3 h3lt (by decide) (by decide),
          h_v7_unc 3 h3lt (by decide) (by decide),
          h_v6_unc 3 h3lt (by decide) (by decide),
          h_v5_unc 3 h3lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v4_i h_3328
  -- Lane 4: step 5 i-lane.
  · have h_eq : v8.elements.val[4]! = v5.elements.val[4]! := by
      rw [h_v8_unc 4 h4lt (by decide) (by decide),
          h_v7_unc 4 h4lt (by decide) (by decide),
          h_v6_unc 4 h4lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v5_i h_3328
  -- Lane 5: step 6 i-lane.
  · have h_eq : v8.elements.val[5]! = v6.elements.val[5]! := by
      rw [h_v8_unc 5 h5lt (by decide) (by decide),
          h_v7_unc 5 h5lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v6_i h_3328
  -- Lane 6: step 7 i-lane.
  · have h_eq : v8.elements.val[6]! = v7.elements.val[6]! := by
      rw [h_v8_unc 6 h6lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v7_i h_3328
  -- Lane 7: step 8 i-lane.
  · exact le_trans h_v8_i h_3328
  -- Lane 8: step 1 j-lane.
  · have h_eq : v8.elements.val[8]! = v1.elements.val[8]! := by
      rw [h_v8_unc 8 h8lt (by decide) (by decide),
          h_v7_unc 8 h8lt (by decide) (by decide),
          h_v6_unc 8 h8lt (by decide) (by decide),
          h_v5_unc 8 h8lt (by decide) (by decide),
          h_v4_unc 8 h8lt (by decide) (by decide),
          h_v3_unc 8 h8lt (by decide) (by decide),
          h_v2_unc 8 h8lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v1_j h_3328
  -- Lane 9: step 2 j-lane.
  · have h_eq : v8.elements.val[9]! = v2.elements.val[9]! := by
      rw [h_v8_unc 9 h9lt (by decide) (by decide),
          h_v7_unc 9 h9lt (by decide) (by decide),
          h_v6_unc 9 h9lt (by decide) (by decide),
          h_v5_unc 9 h9lt (by decide) (by decide),
          h_v4_unc 9 h9lt (by decide) (by decide),
          h_v3_unc 9 h9lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v2_j h_3328
  -- Lane 10: step 3 j-lane.
  · have h_eq : v8.elements.val[10]! = v3.elements.val[10]! := by
      rw [h_v8_unc 10 h10lt (by decide) (by decide),
          h_v7_unc 10 h10lt (by decide) (by decide),
          h_v6_unc 10 h10lt (by decide) (by decide),
          h_v5_unc 10 h10lt (by decide) (by decide),
          h_v4_unc 10 h10lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v3_j h_3328
  -- Lane 11: step 4 j-lane.
  · have h_eq : v8.elements.val[11]! = v4.elements.val[11]! := by
      rw [h_v8_unc 11 h11lt (by decide) (by decide),
          h_v7_unc 11 h11lt (by decide) (by decide),
          h_v6_unc 11 h11lt (by decide) (by decide),
          h_v5_unc 11 h11lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v4_j h_3328
  -- Lane 12: step 5 j-lane.
  · have h_eq : v8.elements.val[12]! = v5.elements.val[12]! := by
      rw [h_v8_unc 12 h12lt (by decide) (by decide),
          h_v7_unc 12 h12lt (by decide) (by decide),
          h_v6_unc 12 h12lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v5_j h_3328
  -- Lane 13: step 6 j-lane.
  · have h_eq : v8.elements.val[13]! = v6.elements.val[13]! := by
      rw [h_v8_unc 13 h13lt (by decide) (by decide),
          h_v7_unc 13 h13lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v6_j h_3328
  -- Lane 14: step 7 j-lane.
  · have h_eq : v8.elements.val[14]! = v7.elements.val[14]! := by
      rw [h_v8_unc 14 h14lt (by decide) (by decide)]
    rw [h_eq]; exact le_trans h_v7_j h_3328
  -- Lane 15: step 8 j-lane.
  · exact le_trans h_v8_j h_3328

end libcrux_iot_ml_kem.Vector.Portable.Ntt
/-! ### Extracted from FCTargets.lean (§vector_ntt). -/

namespace libcrux_iot_ml_kem.Vector.Portable.Ntt
open libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec

/-! ## §L2 — NTT step ops (5 theorems). -/

/-! ### L2.1 — `ntt_step` private helpers. -/

/-- Reduction of `core.num.I16.wrapping_sub` to the underlying
    Aeneas `Std.I16.wrapping_sub`. Mirror of L2's helper, scoped to FCTargets. -/
theorem ntt_step_fc.cm_wrapping_sub_ok_eq (x y : Std.I16) :
    CoreModels.core.num.I16.wrapping_sub x y = .ok (Std.I16.wrapping_sub x y) := by
  unfold CoreModels.core.num.I16.wrapping_sub
  unfold rust_primitives.arithmetic.wrapping_sub_i16
  rfl

/-- Reduction of `core.num.I16.wrapping_add` to the underlying
    Aeneas `Std.I16.wrapping_add`. Mirror of L2's helper. -/
theorem ntt_step_fc.cm_wrapping_add_ok_eq (x y : Std.I16) :
    CoreModels.core.num.I16.wrapping_add x y = .ok (Std.I16.wrapping_add x y) := by
  unfold CoreModels.core.num.I16.wrapping_add
  unfold rust_primitives.arithmetic.wrapping_add_i16
  rfl

/-- Reduction of `classify` to identity. Mirror of L2's helper. -/
theorem ntt_step_fc.classify_ok_eq {T : Type} (x : T) :
    libcrux_secrets.traits.Classify.Blanket.classify x = .ok x := rfl

/-- Under `|a.val| ≤ bnd`, `|t.val| ≤ 3328`, and `bnd ≤ 29439`, the I16-wrapped
    sum `a + t` has `.val = a.val + t.val` (no overflow). Mirror of L2's
    `add_no_overflow_value_bnd`, scoped to FCTargets — only the value
    equation is exposed (bound conjunct dropped, not needed here). -/
theorem ntt_step_fc.add_no_overflow_value (a t : Std.I16) (bnd : Nat)
    (h_a : a.val.natAbs ≤ bnd) (h_t : t.val.natAbs ≤ 3328) (h_bnd : bnd ≤ 29439) :
    (Std.I16.wrapping_add a t).val = a.val + t.val := by
  have h_sum_abs : ((a.val + t.val : Int)).natAbs ≤ bnd + 3328 := by
    have h_tri : (a.val + t.val).natAbs ≤ a.val.natAbs + t.val.natAbs := Int.natAbs_add_le _ _
    omega
  have h_lb : -(2 ^ 15 : Int) ≤ a.val + t.val := by
    have h_bound : bnd + 3328 ≤ 32767 := by omega
    omega
  have h_ub : a.val + t.val < (2 ^ 15 : Int) := by
    have h_bound : bnd + 3328 ≤ 32767 := by omega
    omega
  have h_bmod : Int.bmod (a.val + t.val) (2 ^ 16) = a.val + t.val := by
    apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
    · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
      exact le_trans h_const h_lb
    · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
      exact lt_of_lt_of_le h_ub h_const
  have h_val := Std.I16.wrapping_add_val_eq a t
  rw [h_val, h_bmod]

/-- Diff variant of `add_no_overflow_value`. -/
theorem ntt_step_fc.sub_no_overflow_value (a t : Std.I16) (bnd : Nat)
    (h_a : a.val.natAbs ≤ bnd) (h_t : t.val.natAbs ≤ 3328) (h_bnd : bnd ≤ 29439) :
    (Std.I16.wrapping_sub a t).val = a.val - t.val := by
  have h_diff_abs : ((a.val - t.val : Int)).natAbs ≤ bnd + 3328 := by
    have h_neg_natAbs : (-t.val).natAbs = t.val.natAbs := Int.natAbs_neg _
    have h_eq : a.val - t.val = a.val + (-t.val) := by ring
    rw [h_eq]
    have h_tri : (a.val + (-t.val)).natAbs ≤ a.val.natAbs + (-t.val).natAbs :=
      Int.natAbs_add_le _ _
    rw [h_neg_natAbs] at h_tri
    omega
  have h_lb : -(2 ^ 15 : Int) ≤ a.val - t.val := by
    have h_bound : bnd + 3328 ≤ 32767 := by omega
    omega
  have h_ub : a.val - t.val < (2 ^ 15 : Int) := by
    have h_bound : bnd + 3328 ≤ 32767 := by omega
    omega
  have h_bmod : Int.bmod (a.val - t.val) (2 ^ 16) = a.val - t.val := by
    apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
    · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
      exact le_trans h_const h_lb
    · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
      exact lt_of_lt_of_le h_ub h_const
  have h_val := Std.I16.wrapping_sub_val_eq a t
  rw [h_val, h_bmod]

/-- Helper: `(lift_fe_mont x).val.val = (i16_to_spec_fe_mont x).val`. -/
theorem lift_fe_mont_val_val (x : Std.I16) :
    (lift_fe_mont x).val.val = (i16_to_spec_fe_mont x).val := by
  unfold lift_fe_mont feOfZMod
  show (BitVec.ofNat 16 (i16_to_spec_fe_mont x).val).toNat = (i16_to_spec_fe_mont x).val
  rw [BitVec.toNat_ofNat]
  have h_lt : (i16_to_spec_fe_mont x).val < 2 ^ 16 :=
    Nat.lt_of_lt_of_le (ZMod.val_lt _) (by decide)
  exact Nat.mod_eq_of_lt h_lt

/-- Bridge lemma for the L0.4 Mont-domain output: from the legacy modq
    form `r.val ≡ b.val * zeta.val * 169 (mod 3329)`, derive the FE-level
    `lift_fe r = mul_pure (lift_fe b) (lift_fe_mont zeta)`.

    Algebra: both sides are canonical FEs (left by `Canonical_lift_fe`,
    right by `Canonical_mul_pure`). Equality reduces (via the canonical
    round-trip `feOfZMod_zmodOfFE_of_canonical`) to a `ZMod 3329` equation
    on their `zmodOfFE`-projections, closed by the legacy modq cast
    `modq_eq_cast_zmod` plus `ring`. -/
theorem lift_fe_mul_pure_mont_eq
    (b zeta r : Std.I16)
    (h : libcrux_iot_ml_kem.Spec.ModularArith.modq_eq r.val (b.val * zeta.val * 169) 3329) :
    lift_fe r
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe b) (lift_fe_mont zeta) := by
  -- LHS: lift_fe r = feOfZMod ((r.val : Int) : ZMod 3329).
  have h_lhs : lift_fe r = feOfZMod (((r.val : Int)) : ZMod 3329) := by
    unfold lift_fe i16_to_spec_fe_plain
    rfl
  -- RHS: mul_pure is canonical; reduce via round-trip.
  set s : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
      (lift_fe b) (lift_fe_mont zeta) with hs_def
  have h_canon : s.val.val < 3329 := by
    have h_cs := libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure
      (lift_fe b) (lift_fe_mont zeta)
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at h_cs
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cs
    exact h_cs
  have h_round_trip : feOfZMod (zmodOfFE s) = s :=
    feOfZMod_zmodOfFE_of_canonical s h_canon
  -- zmodOfFE s = (b.val * zeta.val * 169 : ZMod 3329).
  have h_zmod_s : zmodOfFE s = (((b.val * zeta.val * 169 : Int)) : ZMod 3329) := by
    unfold zmodOfFE
    rw [mul_pure_val_eq]
    rw [ZMod.natCast_mod]
    push_cast
    have h_lb : ((lift_fe b).val.val : ZMod 3329) = (((b.val : Int)) : ZMod 3329) := by
      rw [lift_fe_val_val b]; exact ZMod.natCast_zmod_val _
    have h_lz : ((lift_fe_mont zeta).val.val : ZMod 3329)
                  = (((zeta.val : Int)) : ZMod 3329) * 169 := by
      rw [lift_fe_mont_val_val zeta, ZMod.natCast_zmod_val]
      rw [i16_to_spec_fe_mont_unfold]
    rw [h_lb, h_lz]
    ring
  -- Cast the modq hypothesis to a ZMod equality.
  have h_zmod_eq : (((r.val : Int)) : ZMod 3329)
                    = (((b.val * zeta.val * 169 : Int)) : ZMod 3329) :=
    modq_eq_cast_zmod _ _ h
  rw [h_lhs, ← h_round_trip, h_zmod_s, h_zmod_eq]

/-- L2.1 — `ntt_step`: per-pair butterfly.

    **Preconditions beyond locked statement**:
    - `hne : i.val ≠ j.val` — mirrors L2 legacy `ntt_step_spec`. Without
      this, the impl's two writes (`a[j] := a-t` then `a[i] := a+t`) at
      the same index yield `a+t` while the spec would also yield `a+t`
      (via `(a.set j (a-t)).set i (a+t)` with `i = j` → same), but the
      lift-level reasoning bifurcates messily. Real callers in L2.2/3/4
      all use distinct `i, j`.
    - `hvec : ∀ k, k < 16 → (vec.elements.val[k]!).val.natAbs ≤ 29439` —
      ensures the I16 wrapping_{add,sub} at indices `i, j` do not overflow.
      The bound `29439 = 32767 - 3328` is the tightest that keeps
      `|vec[i] ± t| ≤ 32767` when `|t| ≤ 3328` (L0.4 output bound).
      Universal form (not just at `i, j`) for callers' convenience —
      they typically carry a per-lane bound. -/
@[spec high]
theorem ntt_step_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i j : Std.Usize)
    (hi : i.val < 16) (hj : j.val < 16)
    (hne : i.val ≠ j.val)
    (hzeta : zeta.val.natAbs ≤ 1664)
    (hvec : ∀ k : Nat, k < 16 →
      (vec.elements.val[k]!).val.natAbs ≤ 29439) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_ntt_step_pure (lift_chunk vec) (lift_fe_mont zeta) i j ⌝ ⦄ := by
  -- Step 0: vector length facts.
  have h_vec_len : vec.elements.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length vec
  have h_vec_val_len : vec.elements.val.length = 16 := h_vec_len
  -- Step 1: read vec[j].
  have h_idx_j :
      Aeneas.Std.Array.index_usize vec.elements j = .ok (vec.elements.val[j.val]!) :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq vec.elements j
      (by rw [h_vec_len]; exact hj)
  -- Step 2: classify ζ.
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify zeta = .ok zeta :=
    ntt_step_fc.classify_ok_eq zeta
  -- Step 3: L0.4 keystone on (vec[j], ζ).
  set b : Std.I16 := vec.elements.val[j.val]! with hb_def
  have h_b_bnd_29439 : b.val.natAbs ≤ 29439 := hvec j.val hj
  have h_b_bnd : b.val.natAbs ≤ 32767 := by
    have := h_b_bnd_29439
    omega
  obtain ⟨t, h_t_eq_ok, h_t_bd, h_t_lift⟩ :=
    triple_exists_ok_fc (montgomery_multiply_fe_by_fer_fc b zeta h_b_bnd hzeta)
  -- Recover the modq form via the legacy spec (needed for `lift_fe_mul_pure_mont_eq`).
  obtain ⟨t', h_t'_eq, h_t'_bnd_tight, h_t_modq⟩ :=
    triple_exists_ok_fc
      (libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.montgomery_multiply_fe_by_fer_spec b zeta hzeta)
  -- t' = t (same impl call, both `.ok`).
  have h_tt' : t = t' := by
    have : (Result.ok t : Result _) = Result.ok t' := by rw [← h_t_eq_ok, h_t'_eq]
    cases this; rfl
  -- Step 4: read vec[i].
  have h_idx_i :
      Aeneas.Std.Array.index_usize vec.elements i = .ok (vec.elements.val[i.val]!) :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq vec.elements i
      (by rw [h_vec_len]; exact hi)
  set a : Std.I16 := vec.elements.val[i.val]! with ha_def
  have h_a_bnd : a.val.natAbs ≤ 29439 := hvec i.val hi
  -- Step 5,6: wrapping_sub / wrapping_add.
  have h_sub_eq :
      CoreModels.core.num.I16.wrapping_sub a t = .ok (Std.I16.wrapping_sub a t) :=
    ntt_step_fc.cm_wrapping_sub_ok_eq a t
  have h_add_eq :
      CoreModels.core.num.I16.wrapping_add a t = .ok (Std.I16.wrapping_add a t) :=
    ntt_step_fc.cm_wrapping_add_ok_eq a t
  set a_minus_t : Std.I16 := Std.I16.wrapping_sub a t with hamt_def
  set a_plus_t  : Std.I16 := Std.I16.wrapping_add a t with hapt_def
  have h_t_bd' : t.val.natAbs ≤ 3328 := by
    -- L0.4-FC's locked-post bound is ≤ 3328 + 1665 = 4993; the legacy
    -- is the tighter ≤ 3328 (from `montgomery_multiply_fe_by_fer_spec`).
    rw [h_tt']; exact h_t'_bnd_tight
  have h_amt_val : a_minus_t.val = a.val - t.val :=
    ntt_step_fc.sub_no_overflow_value a t 29439 h_a_bnd h_t_bd' (by decide)
  have h_apt_val : a_plus_t.val = a.val + t.val :=
    ntt_step_fc.add_no_overflow_value a t 29439 h_a_bnd h_t_bd' (by decide)
  -- Step 7,8: writes.
  have h_upd_j :
      Aeneas.Std.Array.update vec.elements j a_minus_t
        = .ok (vec.elements.set j a_minus_t) :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_update_ok_eq vec.elements j a_minus_t
      (by rw [h_vec_len]; exact hj)
  have h_upd_i :
      Aeneas.Std.Array.update (vec.elements.set j a_minus_t) i a_plus_t
        = .ok ((vec.elements.set j a_minus_t).set i a_plus_t) := by
    have h_len : (vec.elements.set j a_minus_t).length = 16 := by
      rw [Std.Array.set_length]; exact h_vec_len
    exact libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_update_ok_eq _ i a_plus_t
      (by rw [h_len]; exact hi)
  -- Compose: derive `.ok final_vec` form.
  set final_elements : Std.Array Std.I16 16#usize :=
    (vec.elements.set j a_minus_t).set i a_plus_t with hfe_def
  set final_vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    { elements := final_elements } with hfv_def
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j = .ok final_vec := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_step
    rw [h_idx_j]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_classify]; simp only [Aeneas.Std.bind_tc_ok]
    rw [← h_tt'] at h_t'_eq
    rw [h_t'_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_idx_i]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_sub_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_add_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_upd_j]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_upd_i]; simp only [Aeneas.Std.bind_tc_ok]; rfl
  apply triple_of_ok_fc h_body
  -- Now: prove the FC chunk equation.
  -- Set up the abbreviations.
  set s_t_fe : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
      (lift_fe b) (lift_fe_mont zeta) with hs_t_fe_def
  set s_minus : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
      (lift_fe a) s_t_fe with hs_minus_def
  set s_plus : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
      (lift_fe a) s_t_fe with hs_plus_def
  -- Reduce both sides to underlying lists via Subtype.ext.
  unfold lift_chunk Spec.chunk_ntt_step_pure
  apply Subtype.ext
  -- Both `lift_chunk` and `Spec.chunk_ntt_step_pure` produce Std.Array FE 16.
  -- After Subtype.ext the goal is on `.val : List FE`.
  -- Reduce: `(Std.Array.make 16 L _).val = L` and `Std.Array.set v i x .val = v.val.set i.val x`.
  simp only [Std.Array.set_val_eq]
  -- The Std.Array.make .val reduces by rfl (it's `⟨L, _⟩.val = L`).
  -- And `.val[k]!` on a `Std.Array.make _ L _` equals `L[k]!`.
  -- LHS: final_vec.elements.val.map lift_fe (final_vec.elements is set-set).
  show ((vec.elements.val.set j.val a_minus_t).set i.val a_plus_t).map lift_fe
      = ((vec.elements.val.map lift_fe).set j.val
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
            ((vec.elements.val.map lift_fe)[i.val]!)
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              ((vec.elements.val.map lift_fe)[j.val]!) (lift_fe_mont zeta)))).set i.val
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          ((vec.elements.val.map lift_fe)[i.val]!)
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            ((vec.elements.val.map lift_fe)[j.val]!) (lift_fe_mont zeta)))
  -- Bridge: `(vec.elements.val.map lift_fe)[k]! = lift_fe (vec.elements.val[k]!)` when k < 16.
  have h_map_lift_at (k : Nat) (hk : k < 16) :
      (vec.elements.val.map lift_fe)[k]! = lift_fe (vec.elements.val[k]!) := by
    have hk_lhs : k < (vec.elements.val.map lift_fe).length := by
      simp [List.length_map, h_vec_val_len]; exact hk
    rw [getElem!_pos (vec.elements.val.map lift_fe) k hk_lhs]
    rw [List.getElem_map]
    have hk_vec : k < vec.elements.val.length := by rw [h_vec_val_len]; exact hk
    rw [getElem!_pos vec.elements.val k hk_vec]
  rw [h_map_lift_at i.val hi, h_map_lift_at j.val hj]
  -- The RHS s_t_fe / s_plus / s_minus values match:
  --   sub_pure (lift_fe a) (mul_pure (lift_fe b) (lift_fe_mont zeta)) = s_minus
  --   add_pure (lift_fe a) (mul_pure (lift_fe b) (lift_fe_mont zeta)) = s_plus
  change ((vec.elements.val.set j.val a_minus_t).set i.val a_plus_t).map lift_fe
      = ((vec.elements.val.map lift_fe).set j.val s_minus).set i.val s_plus
  -- Per-index proof.
  apply List.ext_getElem
  · simp [List.length_map, List.length_set]
  · intro k hk1 hk2
    have hk : k < 16 := by
      have hk' : k < (((vec.elements.val.set j.val a_minus_t).set i.val a_plus_t).map lift_fe).length := hk1
      simp [List.length_map, List.length_set, h_vec_val_len] at hk'
      exact hk'
    rw [List.getElem_map]
    by_cases h_eq_i : k = i.val
    · -- k = i.val: r[i] = a_plus_t, RHS = s_plus.
      subst h_eq_i
      rw [List.getElem_set_self]
      rw [List.getElem_set_self]
      -- Goal: lift_fe a_plus_t = s_plus
      show lift_fe a_plus_t = s_plus
      have h_step1 :
          lift_fe a_plus_t
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (lift_fe a) (lift_fe t) :=
        lift_fe_add_pure_eq a t a_plus_t h_apt_val
      rw [h_step1]
      show libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              (lift_fe a) (lift_fe t) = s_plus
      simp only [hs_plus_def, hs_t_fe_def]
      congr 1
      rw [h_tt']
      exact lift_fe_mul_pure_mont_eq b zeta t' h_t_modq
    · -- k ≠ i.val.
      rw [List.getElem_set_ne (Ne.symm h_eq_i)]
      rw [List.getElem_set_ne (Ne.symm h_eq_i)]
      by_cases h_eq_j : k = j.val
      · -- k = j.val.
        subst h_eq_j
        rw [List.getElem_set_self]
        rw [List.getElem_set_self]
        show lift_fe a_minus_t = s_minus
        have h_step1 :
            lift_fe a_minus_t
              = libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
                  (lift_fe a) (lift_fe t) :=
          lift_fe_sub_pure_eq a t a_minus_t h_amt_val
        rw [h_step1]
        show libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
                (lift_fe a) (lift_fe t) = s_minus
        simp only [hs_minus_def, hs_t_fe_def]
        congr 1
        rw [h_tt']
        exact lift_fe_mul_pure_mont_eq b zeta t' h_t_modq
      · -- k ≠ i.val, k ≠ j.val: r[k] = vec[k] under lift_fe.
        rw [List.getElem_set_ne (Ne.symm h_eq_j)]
        rw [List.getElem_set_ne (Ne.symm h_eq_j)]
        rw [List.getElem_map]

/-- Per-lane variant of `ntt_step_fc` for layer composition. Same body
    as the keystone, but the precondition is split into the two lanes
    actually read (`i`, `j`). This is needed for layer-N proofs where
    after each ntt_step the touched lanes exceed the universal `≤ 29439`
    bound; the pairs within a layer are disjoint, so only the
    untouched-pair lanes need to satisfy `≤ 29439` at each step.

    Also exposes the per-lane output bound `≤ 32767` (i.e. all lanes
    remain valid `I16`s), used to chain across steps. -/
theorem ntt_step_pair_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i j : Std.Usize)
    (hi : i.val < 16) (hj : j.val < 16)
    (hne : i.val ≠ j.val)
    (hzeta : zeta.val.natAbs ≤ 1664)
    (h_a_bnd : (vec.elements.val[i.val]!).val.natAbs ≤ 29439)
    (h_b_bnd : (vec.elements.val[j.val]!).val.natAbs ≤ 29439) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_ntt_step_pure (lift_chunk vec) (lift_fe_mont zeta) i j
              ∧ (∀ k : Nat, k < 16 → k ≠ i.val → k ≠ j.val →
                  (r.elements.val[k]!) = (vec.elements.val[k]!))
              ∧ (r.elements.val[i.val]!).val.natAbs ≤ 32767
              ∧ (r.elements.val[j.val]!).val.natAbs ≤ 32767 ⌝ ⦄ := by
  -- Step 0: vector length facts.
  have h_vec_len : vec.elements.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length vec
  have h_vec_val_len : vec.elements.val.length = 16 := h_vec_len
  -- Step 1: read vec[j].
  have h_idx_j :
      Aeneas.Std.Array.index_usize vec.elements j = .ok (vec.elements.val[j.val]!) :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq vec.elements j
      (by rw [h_vec_len]; exact hj)
  -- Step 2: classify ζ.
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify zeta = .ok zeta :=
    ntt_step_fc.classify_ok_eq zeta
  -- Step 3: L0.4 keystone on (vec[j], ζ).
  set b : Std.I16 := vec.elements.val[j.val]! with hb_def
  have h_b_bnd_29439 : b.val.natAbs ≤ 29439 := h_b_bnd
  have h_b_bnd_max : b.val.natAbs ≤ 32767 := by
    have := h_b_bnd_29439; omega
  obtain ⟨t, h_t_eq_ok, h_t_bd, h_t_lift⟩ :=
    triple_exists_ok_fc (montgomery_multiply_fe_by_fer_fc b zeta h_b_bnd_max hzeta)
  obtain ⟨t', h_t'_eq, h_t'_bnd_tight, h_t_modq⟩ :=
    triple_exists_ok_fc
      (libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.montgomery_multiply_fe_by_fer_spec b zeta hzeta)
  have h_tt' : t = t' := by
    have : (Result.ok t : Result _) = Result.ok t' := by rw [← h_t_eq_ok, h_t'_eq]
    cases this; rfl
  -- Step 4: read vec[i].
  have h_idx_i :
      Aeneas.Std.Array.index_usize vec.elements i = .ok (vec.elements.val[i.val]!) :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq vec.elements i
      (by rw [h_vec_len]; exact hi)
  set a : Std.I16 := vec.elements.val[i.val]! with ha_def
  have h_a_bnd_29439 : a.val.natAbs ≤ 29439 := h_a_bnd
  -- Step 5,6: wrapping_sub / wrapping_add.
  have h_sub_eq :
      CoreModels.core.num.I16.wrapping_sub a t = .ok (Std.I16.wrapping_sub a t) :=
    ntt_step_fc.cm_wrapping_sub_ok_eq a t
  have h_add_eq :
      CoreModels.core.num.I16.wrapping_add a t = .ok (Std.I16.wrapping_add a t) :=
    ntt_step_fc.cm_wrapping_add_ok_eq a t
  set a_minus_t : Std.I16 := Std.I16.wrapping_sub a t with hamt_def
  set a_plus_t  : Std.I16 := Std.I16.wrapping_add a t with hapt_def
  have h_t_bd' : t.val.natAbs ≤ 3328 := by
    rw [h_tt']; exact h_t'_bnd_tight
  have h_amt_val : a_minus_t.val = a.val - t.val :=
    ntt_step_fc.sub_no_overflow_value a t 29439 h_a_bnd_29439 h_t_bd' (by decide)
  have h_apt_val : a_plus_t.val = a.val + t.val :=
    ntt_step_fc.add_no_overflow_value a t 29439 h_a_bnd_29439 h_t_bd' (by decide)
  -- Step 7,8: writes.
  have h_upd_j :
      Aeneas.Std.Array.update vec.elements j a_minus_t
        = .ok (vec.elements.set j a_minus_t) :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_update_ok_eq vec.elements j a_minus_t
      (by rw [h_vec_len]; exact hj)
  have h_upd_i :
      Aeneas.Std.Array.update (vec.elements.set j a_minus_t) i a_plus_t
        = .ok ((vec.elements.set j a_minus_t).set i a_plus_t) := by
    have h_len : (vec.elements.set j a_minus_t).length = 16 := by
      rw [Std.Array.set_length]; exact h_vec_len
    exact libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_update_ok_eq _ i a_plus_t
      (by rw [h_len]; exact hi)
  -- Compose.
  set final_elements : Std.Array Std.I16 16#usize :=
    (vec.elements.set j a_minus_t).set i a_plus_t with hfe_def
  set final_vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    { elements := final_elements } with hfv_def
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_step vec zeta i j = .ok final_vec := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_step
    rw [h_idx_j]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_classify]; simp only [Aeneas.Std.bind_tc_ok]
    rw [← h_tt'] at h_t'_eq
    rw [h_t'_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_idx_i]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_sub_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_add_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_upd_j]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_upd_i]; simp only [Aeneas.Std.bind_tc_ok]; rfl
  apply triple_of_ok_fc h_body
  -- Now: 4 conjuncts.
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- lift_chunk equation: identical to keystone proof.
    set s_t_fe : hacspec_ml_kem.parameters.FieldElement :=
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
        (lift_fe b) (lift_fe_mont zeta) with hs_t_fe_def
    set s_minus : hacspec_ml_kem.parameters.FieldElement :=
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
        (lift_fe a) s_t_fe with hs_minus_def
    set s_plus : hacspec_ml_kem.parameters.FieldElement :=
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
        (lift_fe a) s_t_fe with hs_plus_def
    unfold lift_chunk Spec.chunk_ntt_step_pure
    apply Subtype.ext
    simp only [Std.Array.set_val_eq]
    show ((vec.elements.val.set j.val a_minus_t).set i.val a_plus_t).map lift_fe
        = ((vec.elements.val.map lift_fe).set j.val
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
              ((vec.elements.val.map lift_fe)[i.val]!)
              (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                ((vec.elements.val.map lift_fe)[j.val]!) (lift_fe_mont zeta)))).set i.val
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            ((vec.elements.val.map lift_fe)[i.val]!)
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              ((vec.elements.val.map lift_fe)[j.val]!) (lift_fe_mont zeta)))
    have h_map_lift_at (k : Nat) (hk : k < 16) :
        (vec.elements.val.map lift_fe)[k]! = lift_fe (vec.elements.val[k]!) := by
      have hk_lhs : k < (vec.elements.val.map lift_fe).length := by
        simp [List.length_map, h_vec_val_len]; exact hk
      rw [getElem!_pos (vec.elements.val.map lift_fe) k hk_lhs]
      rw [List.getElem_map]
      have hk_vec : k < vec.elements.val.length := by rw [h_vec_val_len]; exact hk
      rw [getElem!_pos vec.elements.val k hk_vec]
    rw [h_map_lift_at i.val hi, h_map_lift_at j.val hj]
    change ((vec.elements.val.set j.val a_minus_t).set i.val a_plus_t).map lift_fe
        = ((vec.elements.val.map lift_fe).set j.val s_minus).set i.val s_plus
    apply List.ext_getElem
    · simp [List.length_map, List.length_set]
    · intro k hk1 hk2
      have hk : k < 16 := by
        have hk' : k < (((vec.elements.val.set j.val a_minus_t).set i.val a_plus_t).map lift_fe).length := hk1
        simp [List.length_map, List.length_set, h_vec_val_len] at hk'
        exact hk'
      rw [List.getElem_map]
      by_cases h_eq_i : k = i.val
      · subst h_eq_i
        rw [List.getElem_set_self]
        rw [List.getElem_set_self]
        show lift_fe a_plus_t = s_plus
        have h_step1 :
            lift_fe a_plus_t
              = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                  (lift_fe a) (lift_fe t) :=
          lift_fe_add_pure_eq a t a_plus_t h_apt_val
        rw [h_step1]
        show libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (lift_fe a) (lift_fe t) = s_plus
        simp only [hs_plus_def, hs_t_fe_def]
        congr 1
        rw [h_tt']
        exact lift_fe_mul_pure_mont_eq b zeta t' h_t_modq
      · rw [List.getElem_set_ne (Ne.symm h_eq_i)]
        rw [List.getElem_set_ne (Ne.symm h_eq_i)]
        by_cases h_eq_j : k = j.val
        · subst h_eq_j
          rw [List.getElem_set_self]
          rw [List.getElem_set_self]
          show lift_fe a_minus_t = s_minus
          have h_step1 :
              lift_fe a_minus_t
                = libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
                    (lift_fe a) (lift_fe t) :=
            lift_fe_sub_pure_eq a t a_minus_t h_amt_val
          rw [h_step1]
          show libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
                  (lift_fe a) (lift_fe t) = s_minus
          simp only [hs_minus_def, hs_t_fe_def]
          congr 1
          rw [h_tt']
          exact lift_fe_mul_pure_mont_eq b zeta t' h_t_modq
        · rw [List.getElem_set_ne (Ne.symm h_eq_j)]
          rw [List.getElem_set_ne (Ne.symm h_eq_j)]
          rw [List.getElem_map]
  · -- Untouched-lane preservation: r[k] = vec[k] for k ≠ i, j.
    intro k hk hki hkj
    show ((vec.elements.set j a_minus_t).set i a_plus_t).val[k]!
      = vec.elements.val[k]!
    have h_set_val_eq : ((vec.elements.set j a_minus_t).set i a_plus_t).val
        = (vec.elements.val.set j.val a_minus_t).set i.val a_plus_t := by
      simp [Std.Array.set_val_eq]
    rw [h_set_val_eq]
    -- (list.set j _).set i _ at index k (k ≠ i, k ≠ j) = original list at k.
    have hk_set_i : k < (vec.elements.val.set j.val a_minus_t).length := by
      simp [List.length_set, h_vec_val_len]; exact hk
    rw [getElem!_pos _ k (by simp [List.length_set, h_vec_val_len]; exact hk)]
    rw [List.getElem_set_ne (Ne.symm hki)]
    rw [List.getElem_set_ne (Ne.symm hkj)]
    rw [getElem!_pos vec.elements.val k (by rw [h_vec_val_len]; exact hk)]
  · -- Bound at i: r[i] = a_plus_t = a + t (no-overflow), |a| ≤ 29439, |t| ≤ 3328.
    show ((vec.elements.set j a_minus_t).set i a_plus_t).val[i.val]!.val.natAbs ≤ 32767
    have h_set_val_eq : ((vec.elements.set j a_minus_t).set i a_plus_t).val
        = (vec.elements.val.set j.val a_minus_t).set i.val a_plus_t := by
      simp [Std.Array.set_val_eq]
    rw [h_set_val_eq]
    rw [getElem!_pos _ i.val (by simp [List.length_set, h_vec_val_len]; exact hi)]
    rw [List.getElem_set_self]
    -- a_plus_t.val = a.val + t.val, |a| ≤ 29439, |t| ≤ 3328 ⇒ |sum| ≤ 32767.
    have h_sum_abs : ((a.val + t.val : Int)).natAbs ≤ 29439 + 3328 := by
      have h_tri : (a.val + t.val).natAbs ≤ a.val.natAbs + t.val.natAbs := Int.natAbs_add_le _ _
      omega
    rw [h_apt_val]; omega
  · -- Bound at j: r[j] = a_minus_t = a - t (no-overflow), similar.
    show ((vec.elements.set j a_minus_t).set i a_plus_t).val[j.val]!.val.natAbs ≤ 32767
    have h_set_val_eq : ((vec.elements.set j a_minus_t).set i a_plus_t).val
        = (vec.elements.val.set j.val a_minus_t).set i.val a_plus_t := by
      simp [Std.Array.set_val_eq]
    rw [h_set_val_eq]
    rw [getElem!_pos _ j.val (by simp [List.length_set, h_vec_val_len]; exact hj)]
    rw [List.getElem_set_ne hne]
    rw [List.getElem_set_self]
    have h_diff_abs : ((a.val - t.val : Int)).natAbs ≤ 29439 + 3328 := by
      have h_neg : (-t.val).natAbs = t.val.natAbs := Int.natAbs_neg _
      have h_eq : a.val - t.val = a.val + (-t.val) := by ring
      rw [h_eq]
      have h_tri : (a.val + (-t.val)).natAbs ≤ a.val.natAbs + (-t.val).natAbs :=
        Int.natAbs_add_le _ _
      rw [h_neg] at h_tri
      omega
    rw [h_amt_val]; omega

/-- L2.2 — `ntt_layer_1_step`: 8 butterfly pairs (0,2)(1,3) with z0,
    (4,6)(5,7) with z1, (8,10)(9,11) with z2, (12,14)(13,15) with z3.

    **Precondition adjustment** (beyond locked statement):
    - `hvec : ∀ k < 16, |vec[k]| ≤ 29439` — same as layer_2/3 (disjoint pairs). -/
@[spec]
theorem ntt_layer_1_step_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (z0 z1 z2 z3 : Std.I16)
    (hz : z0.val.natAbs ≤ 1664 ∧ z1.val.natAbs ≤ 1664
        ∧ z2.val.natAbs ≤ 1664 ∧ z3.val.natAbs ≤ 1664)
    (hvec : ∀ k : Nat, k < 16 →
      (vec.elements.val[k]!).val.natAbs ≤ 29439) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step vec z0 z1 z2 z3
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_ntt_layer_1_step_pure (lift_chunk vec)
                    (lift_fe_mont z0) (lift_fe_mont z1)
                    (lift_fe_mont z2) (lift_fe_mont z3) ⌝ ⦄ := by
  obtain ⟨hz0, hz1, hz2, hz3⟩ := hz
  have hi0 : (0 : Nat) < 16 := by decide
  have hi1 : (1 : Nat) < 16 := by decide
  have hi2 : (2 : Nat) < 16 := by decide
  have hi3 : (3 : Nat) < 16 := by decide
  have hi4 : (4 : Nat) < 16 := by decide
  have hi5 : (5 : Nat) < 16 := by decide
  have hi6 : (6 : Nat) < 16 := by decide
  have hi7 : (7 : Nat) < 16 := by decide
  have hi8 : (8 : Nat) < 16 := by decide
  have hi9 : (9 : Nat) < 16 := by decide
  have hi10 : (10 : Nat) < 16 := by decide
  have hi11 : (11 : Nat) < 16 := by decide
  have hi12 : (12 : Nat) < 16 := by decide
  have hi13 : (13 : Nat) < 16 := by decide
  have hi14 : (14 : Nat) < 16 := by decide
  have hi15 : (15 : Nat) < 16 := by decide
  -- Step 1: ntt_step vec z0 0 2.
  obtain ⟨v1, h_v1_eq, h_v1_lift, h_v1_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc vec z0 0#usize 2#usize hi0 hi2
      (by decide) hz0 (hvec 0 hi0) (hvec 2 hi2))
  -- Step 2: ntt_step v1 z0 1 3.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 29439 := by
    rw [h_v1_unc 1 hi1 (by decide) (by decide)]; exact hvec 1 hi1
  have h_v1_3 : (v1.elements.val[3]!).val.natAbs ≤ 29439 := by
    rw [h_v1_unc 3 hi3 (by decide) (by decide)]; exact hvec 3 hi3
  obtain ⟨v2, h_v2_eq, h_v2_lift, h_v2_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v1 z0 1#usize 3#usize hi1 hi3
      (by decide) hz0 h_v1_1 h_v1_3)
  -- Step 3: ntt_step v2 z1 4 6.
  have h_v2_4 : (v2.elements.val[4]!).val.natAbs ≤ 29439 := by
    rw [h_v2_unc 4 hi4 (by decide) (by decide),
        h_v1_unc 4 hi4 (by decide) (by decide)]; exact hvec 4 hi4
  have h_v2_6 : (v2.elements.val[6]!).val.natAbs ≤ 29439 := by
    rw [h_v2_unc 6 hi6 (by decide) (by decide),
        h_v1_unc 6 hi6 (by decide) (by decide)]; exact hvec 6 hi6
  obtain ⟨v3, h_v3_eq, h_v3_lift, h_v3_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v2 z1 4#usize 6#usize hi4 hi6
      (by decide) hz1 h_v2_4 h_v2_6)
  -- Step 4: ntt_step v3 z1 5 7.
  have h_v3_5 : (v3.elements.val[5]!).val.natAbs ≤ 29439 := by
    rw [h_v3_unc 5 hi5 (by decide) (by decide),
        h_v2_unc 5 hi5 (by decide) (by decide),
        h_v1_unc 5 hi5 (by decide) (by decide)]; exact hvec 5 hi5
  have h_v3_7 : (v3.elements.val[7]!).val.natAbs ≤ 29439 := by
    rw [h_v3_unc 7 hi7 (by decide) (by decide),
        h_v2_unc 7 hi7 (by decide) (by decide),
        h_v1_unc 7 hi7 (by decide) (by decide)]; exact hvec 7 hi7
  obtain ⟨v4, h_v4_eq, h_v4_lift, h_v4_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v3 z1 5#usize 7#usize hi5 hi7
      (by decide) hz1 h_v3_5 h_v3_7)
  -- Step 5: ntt_step v4 z2 8 10.
  have h_v4_8 : (v4.elements.val[8]!).val.natAbs ≤ 29439 := by
    rw [h_v4_unc 8 hi8 (by decide) (by decide),
        h_v3_unc 8 hi8 (by decide) (by decide),
        h_v2_unc 8 hi8 (by decide) (by decide),
        h_v1_unc 8 hi8 (by decide) (by decide)]; exact hvec 8 hi8
  have h_v4_10 : (v4.elements.val[10]!).val.natAbs ≤ 29439 := by
    rw [h_v4_unc 10 hi10 (by decide) (by decide),
        h_v3_unc 10 hi10 (by decide) (by decide),
        h_v2_unc 10 hi10 (by decide) (by decide),
        h_v1_unc 10 hi10 (by decide) (by decide)]; exact hvec 10 hi10
  obtain ⟨v5, h_v5_eq, h_v5_lift, h_v5_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v4 z2 8#usize 10#usize hi8 hi10
      (by decide) hz2 h_v4_8 h_v4_10)
  -- Step 6: ntt_step v5 z2 9 11.
  have h_v5_9 : (v5.elements.val[9]!).val.natAbs ≤ 29439 := by
    rw [h_v5_unc 9 hi9 (by decide) (by decide),
        h_v4_unc 9 hi9 (by decide) (by decide),
        h_v3_unc 9 hi9 (by decide) (by decide),
        h_v2_unc 9 hi9 (by decide) (by decide),
        h_v1_unc 9 hi9 (by decide) (by decide)]; exact hvec 9 hi9
  have h_v5_11 : (v5.elements.val[11]!).val.natAbs ≤ 29439 := by
    rw [h_v5_unc 11 hi11 (by decide) (by decide),
        h_v4_unc 11 hi11 (by decide) (by decide),
        h_v3_unc 11 hi11 (by decide) (by decide),
        h_v2_unc 11 hi11 (by decide) (by decide),
        h_v1_unc 11 hi11 (by decide) (by decide)]; exact hvec 11 hi11
  obtain ⟨v6, h_v6_eq, h_v6_lift, h_v6_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v5 z2 9#usize 11#usize hi9 hi11
      (by decide) hz2 h_v5_9 h_v5_11)
  -- Step 7: ntt_step v6 z3 12 14.
  have h_v6_12 : (v6.elements.val[12]!).val.natAbs ≤ 29439 := by
    rw [h_v6_unc 12 hi12 (by decide) (by decide),
        h_v5_unc 12 hi12 (by decide) (by decide),
        h_v4_unc 12 hi12 (by decide) (by decide),
        h_v3_unc 12 hi12 (by decide) (by decide),
        h_v2_unc 12 hi12 (by decide) (by decide),
        h_v1_unc 12 hi12 (by decide) (by decide)]; exact hvec 12 hi12
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 29439 := by
    rw [h_v6_unc 14 hi14 (by decide) (by decide),
        h_v5_unc 14 hi14 (by decide) (by decide),
        h_v4_unc 14 hi14 (by decide) (by decide),
        h_v3_unc 14 hi14 (by decide) (by decide),
        h_v2_unc 14 hi14 (by decide) (by decide),
        h_v1_unc 14 hi14 (by decide) (by decide)]; exact hvec 14 hi14
  obtain ⟨v7, h_v7_eq, h_v7_lift, h_v7_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v6 z3 12#usize 14#usize hi12 hi14
      (by decide) hz3 h_v6_12 h_v6_14)
  -- Step 8: ntt_step v7 z3 13 15.
  have h_v7_13 : (v7.elements.val[13]!).val.natAbs ≤ 29439 := by
    rw [h_v7_unc 13 hi13 (by decide) (by decide),
        h_v6_unc 13 hi13 (by decide) (by decide),
        h_v5_unc 13 hi13 (by decide) (by decide),
        h_v4_unc 13 hi13 (by decide) (by decide),
        h_v3_unc 13 hi13 (by decide) (by decide),
        h_v2_unc 13 hi13 (by decide) (by decide),
        h_v1_unc 13 hi13 (by decide) (by decide)]; exact hvec 13 hi13
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 29439 := by
    rw [h_v7_unc 15 hi15 (by decide) (by decide),
        h_v6_unc 15 hi15 (by decide) (by decide),
        h_v5_unc 15 hi15 (by decide) (by decide),
        h_v4_unc 15 hi15 (by decide) (by decide),
        h_v3_unc 15 hi15 (by decide) (by decide),
        h_v2_unc 15 hi15 (by decide) (by decide),
        h_v1_unc 15 hi15 (by decide) (by decide)]; exact hvec 15 hi15
  obtain ⟨v8, h_v8_eq, h_v8_lift, _, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v7 z3 13#usize 15#usize hi13 hi15
      (by decide) hz3 h_v7_13 h_v7_15)
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step vec z0 z1 z2 z3
        = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step
    rw [h_v1_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v2_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v3_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v4_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v5_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v6_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v7_eq]; simp only [Aeneas.Std.bind_tc_ok]
    exact h_v8_eq
  apply triple_of_ok_fc h_body
  unfold Spec.chunk_ntt_layer_1_step_pure
  rw [h_v8_lift, h_v7_lift, h_v6_lift, h_v5_lift, h_v4_lift, h_v3_lift, h_v2_lift, h_v1_lift]

/-- L2.3 — `ntt_layer_2_step`: 8 butterfly pairs (0,4)…(3,7) with z0 then
    (8,12)…(11,15) with z1.

    **Precondition adjustment** (beyond locked statement):
    - `hvec : ∀ k < 16, |vec[k]| ≤ 29439` — same as layer_3 (disjoint pairs). -/
@[spec]
theorem ntt_layer_2_step_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (z0 z1 : Std.I16)
    (hz : z0.val.natAbs ≤ 1664 ∧ z1.val.natAbs ≤ 1664)
    (hvec : ∀ k : Nat, k < 16 →
      (vec.elements.val[k]!).val.natAbs ≤ 29439) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step vec z0 z1
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_ntt_layer_2_step_pure (lift_chunk vec)
                    (lift_fe_mont z0) (lift_fe_mont z1) ⌝ ⦄ := by
  obtain ⟨hz0, hz1⟩ := hz
  have hi0 : (0 : Nat) < 16 := by decide
  have hi1 : (1 : Nat) < 16 := by decide
  have hi2 : (2 : Nat) < 16 := by decide
  have hi3 : (3 : Nat) < 16 := by decide
  have hi4 : (4 : Nat) < 16 := by decide
  have hi5 : (5 : Nat) < 16 := by decide
  have hi6 : (6 : Nat) < 16 := by decide
  have hi7 : (7 : Nat) < 16 := by decide
  have hi8 : (8 : Nat) < 16 := by decide
  have hi9 : (9 : Nat) < 16 := by decide
  have hi10 : (10 : Nat) < 16 := by decide
  have hi11 : (11 : Nat) < 16 := by decide
  have hi12 : (12 : Nat) < 16 := by decide
  have hi13 : (13 : Nat) < 16 := by decide
  have hi14 : (14 : Nat) < 16 := by decide
  have hi15 : (15 : Nat) < 16 := by decide
  -- Step 1: ntt_step vec z0 0 4.
  obtain ⟨v1, h_v1_eq, h_v1_lift, h_v1_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc vec z0 0#usize 4#usize hi0 hi4
      (by decide) hz0 (hvec 0 hi0) (hvec 4 hi4))
  -- Step 2: ntt_step v1 z0 1 5.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 29439 := by
    rw [h_v1_unc 1 hi1 (by decide) (by decide)]; exact hvec 1 hi1
  have h_v1_5 : (v1.elements.val[5]!).val.natAbs ≤ 29439 := by
    rw [h_v1_unc 5 hi5 (by decide) (by decide)]; exact hvec 5 hi5
  obtain ⟨v2, h_v2_eq, h_v2_lift, h_v2_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v1 z0 1#usize 5#usize hi1 hi5
      (by decide) hz0 h_v1_1 h_v1_5)
  -- Step 3: ntt_step v2 z0 2 6.
  have h_v2_2 : (v2.elements.val[2]!).val.natAbs ≤ 29439 := by
    rw [h_v2_unc 2 hi2 (by decide) (by decide),
        h_v1_unc 2 hi2 (by decide) (by decide)]; exact hvec 2 hi2
  have h_v2_6 : (v2.elements.val[6]!).val.natAbs ≤ 29439 := by
    rw [h_v2_unc 6 hi6 (by decide) (by decide),
        h_v1_unc 6 hi6 (by decide) (by decide)]; exact hvec 6 hi6
  obtain ⟨v3, h_v3_eq, h_v3_lift, h_v3_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v2 z0 2#usize 6#usize hi2 hi6
      (by decide) hz0 h_v2_2 h_v2_6)
  -- Step 4: ntt_step v3 z0 3 7.
  have h_v3_3 : (v3.elements.val[3]!).val.natAbs ≤ 29439 := by
    rw [h_v3_unc 3 hi3 (by decide) (by decide),
        h_v2_unc 3 hi3 (by decide) (by decide),
        h_v1_unc 3 hi3 (by decide) (by decide)]; exact hvec 3 hi3
  have h_v3_7 : (v3.elements.val[7]!).val.natAbs ≤ 29439 := by
    rw [h_v3_unc 7 hi7 (by decide) (by decide),
        h_v2_unc 7 hi7 (by decide) (by decide),
        h_v1_unc 7 hi7 (by decide) (by decide)]; exact hvec 7 hi7
  obtain ⟨v4, h_v4_eq, h_v4_lift, h_v4_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v3 z0 3#usize 7#usize hi3 hi7
      (by decide) hz0 h_v3_3 h_v3_7)
  -- Step 5: ntt_step v4 z1 8 12.
  have h_v4_8 : (v4.elements.val[8]!).val.natAbs ≤ 29439 := by
    rw [h_v4_unc 8 hi8 (by decide) (by decide),
        h_v3_unc 8 hi8 (by decide) (by decide),
        h_v2_unc 8 hi8 (by decide) (by decide),
        h_v1_unc 8 hi8 (by decide) (by decide)]; exact hvec 8 hi8
  have h_v4_12 : (v4.elements.val[12]!).val.natAbs ≤ 29439 := by
    rw [h_v4_unc 12 hi12 (by decide) (by decide),
        h_v3_unc 12 hi12 (by decide) (by decide),
        h_v2_unc 12 hi12 (by decide) (by decide),
        h_v1_unc 12 hi12 (by decide) (by decide)]; exact hvec 12 hi12
  obtain ⟨v5, h_v5_eq, h_v5_lift, h_v5_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v4 z1 8#usize 12#usize hi8 hi12
      (by decide) hz1 h_v4_8 h_v4_12)
  -- Step 6: ntt_step v5 z1 9 13.
  have h_v5_9 : (v5.elements.val[9]!).val.natAbs ≤ 29439 := by
    rw [h_v5_unc 9 hi9 (by decide) (by decide),
        h_v4_unc 9 hi9 (by decide) (by decide),
        h_v3_unc 9 hi9 (by decide) (by decide),
        h_v2_unc 9 hi9 (by decide) (by decide),
        h_v1_unc 9 hi9 (by decide) (by decide)]; exact hvec 9 hi9
  have h_v5_13 : (v5.elements.val[13]!).val.natAbs ≤ 29439 := by
    rw [h_v5_unc 13 hi13 (by decide) (by decide),
        h_v4_unc 13 hi13 (by decide) (by decide),
        h_v3_unc 13 hi13 (by decide) (by decide),
        h_v2_unc 13 hi13 (by decide) (by decide),
        h_v1_unc 13 hi13 (by decide) (by decide)]; exact hvec 13 hi13
  obtain ⟨v6, h_v6_eq, h_v6_lift, h_v6_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v5 z1 9#usize 13#usize hi9 hi13
      (by decide) hz1 h_v5_9 h_v5_13)
  -- Step 7: ntt_step v6 z1 10 14.
  have h_v6_10 : (v6.elements.val[10]!).val.natAbs ≤ 29439 := by
    rw [h_v6_unc 10 hi10 (by decide) (by decide),
        h_v5_unc 10 hi10 (by decide) (by decide),
        h_v4_unc 10 hi10 (by decide) (by decide),
        h_v3_unc 10 hi10 (by decide) (by decide),
        h_v2_unc 10 hi10 (by decide) (by decide),
        h_v1_unc 10 hi10 (by decide) (by decide)]; exact hvec 10 hi10
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 29439 := by
    rw [h_v6_unc 14 hi14 (by decide) (by decide),
        h_v5_unc 14 hi14 (by decide) (by decide),
        h_v4_unc 14 hi14 (by decide) (by decide),
        h_v3_unc 14 hi14 (by decide) (by decide),
        h_v2_unc 14 hi14 (by decide) (by decide),
        h_v1_unc 14 hi14 (by decide) (by decide)]; exact hvec 14 hi14
  obtain ⟨v7, h_v7_eq, h_v7_lift, h_v7_unc, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v6 z1 10#usize 14#usize hi10 hi14
      (by decide) hz1 h_v6_10 h_v6_14)
  -- Step 8: ntt_step v7 z1 11 15.
  have h_v7_11 : (v7.elements.val[11]!).val.natAbs ≤ 29439 := by
    rw [h_v7_unc 11 hi11 (by decide) (by decide),
        h_v6_unc 11 hi11 (by decide) (by decide),
        h_v5_unc 11 hi11 (by decide) (by decide),
        h_v4_unc 11 hi11 (by decide) (by decide),
        h_v3_unc 11 hi11 (by decide) (by decide),
        h_v2_unc 11 hi11 (by decide) (by decide),
        h_v1_unc 11 hi11 (by decide) (by decide)]; exact hvec 11 hi11
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 29439 := by
    rw [h_v7_unc 15 hi15 (by decide) (by decide),
        h_v6_unc 15 hi15 (by decide) (by decide),
        h_v5_unc 15 hi15 (by decide) (by decide),
        h_v4_unc 15 hi15 (by decide) (by decide),
        h_v3_unc 15 hi15 (by decide) (by decide),
        h_v2_unc 15 hi15 (by decide) (by decide),
        h_v1_unc 15 hi15 (by decide) (by decide)]; exact hvec 15 hi15
  obtain ⟨v8, h_v8_eq, h_v8_lift, _, _, _⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v7 z1 11#usize 15#usize hi11 hi15
      (by decide) hz1 h_v7_11 h_v7_15)
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step vec z0 z1 = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step
    rw [h_v1_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v2_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v3_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v4_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v5_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v6_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v7_eq]; simp only [Aeneas.Std.bind_tc_ok]
    exact h_v8_eq
  apply triple_of_ok_fc h_body
  unfold Spec.chunk_ntt_layer_2_step_pure
  rw [h_v8_lift, h_v7_lift, h_v6_lift, h_v5_lift, h_v4_lift, h_v3_lift, h_v2_lift, h_v1_lift]

/-- L2.4 — `ntt_layer_3_step`: 8 butterfly pairs (0,8)…(7,15) with one zeta.

    **Precondition adjustment** (beyond locked statement):
    - `hvec : ∀ k < 16, |vec[k]| ≤ 29439` — chained through the 8
      ntt_step calls. Pairs are disjoint (each lane touched exactly
      once), so the keystone's `≤ 29439` precondition holds at each
      step on the unchanged lanes. -/
@[spec]
theorem ntt_layer_3_step_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (z : Std.I16) (hz : z.val.natAbs ≤ 1664)
    (hvec : ∀ k : Nat, k < 16 →
      (vec.elements.val[k]!).val.natAbs ≤ 29439) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step vec z
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_ntt_layer_3_step_pure (lift_chunk vec) (lift_fe_mont z) ⌝ ⦄ := by
  -- Initial-lane bounds (specialised from hvec).
  have hi0 : (0 : Nat) < 16 := by decide
  have hi1 : (1 : Nat) < 16 := by decide
  have hi2 : (2 : Nat) < 16 := by decide
  have hi3 : (3 : Nat) < 16 := by decide
  have hi4 : (4 : Nat) < 16 := by decide
  have hi5 : (5 : Nat) < 16 := by decide
  have hi6 : (6 : Nat) < 16 := by decide
  have hi7 : (7 : Nat) < 16 := by decide
  have hi8 : (8 : Nat) < 16 := by decide
  have hi9 : (9 : Nat) < 16 := by decide
  have hi10 : (10 : Nat) < 16 := by decide
  have hi11 : (11 : Nat) < 16 := by decide
  have hi12 : (12 : Nat) < 16 := by decide
  have hi13 : (13 : Nat) < 16 := by decide
  have hi14 : (14 : Nat) < 16 := by decide
  have hi15 : (15 : Nat) < 16 := by decide
  -- Step 1: ntt_step vec z 0 8.
  obtain ⟨v1, h_v1_eq, h_v1_lift, h_v1_unc, _h_v1_i_bd, _h_v1_j_bd⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc vec z 0#usize 8#usize hi0 hi8
      (by decide) hz (hvec 0 hi0) (hvec 8 hi8))
  -- Step 2: ntt_step v1 z 1 9 — needs v1[1], v1[9] ≤ 29439. Both via h_v1_unc.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 29439 := by
    rw [h_v1_unc 1 hi1 (by decide) (by decide)]; exact hvec 1 hi1
  have h_v1_9 : (v1.elements.val[9]!).val.natAbs ≤ 29439 := by
    rw [h_v1_unc 9 hi9 (by decide) (by decide)]; exact hvec 9 hi9
  obtain ⟨v2, h_v2_eq, h_v2_lift, h_v2_unc, _h_v2_i_bd, _h_v2_j_bd⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v1 z 1#usize 9#usize hi1 hi9
      (by decide) hz h_v1_1 h_v1_9)
  -- Step 3: ntt_step v2 z 2 10.
  have h_v2_2 : (v2.elements.val[2]!).val.natAbs ≤ 29439 := by
    rw [h_v2_unc 2 hi2 (by decide) (by decide),
        h_v1_unc 2 hi2 (by decide) (by decide)]; exact hvec 2 hi2
  have h_v2_10 : (v2.elements.val[10]!).val.natAbs ≤ 29439 := by
    rw [h_v2_unc 10 hi10 (by decide) (by decide),
        h_v1_unc 10 hi10 (by decide) (by decide)]; exact hvec 10 hi10
  obtain ⟨v3, h_v3_eq, h_v3_lift, h_v3_unc, _h_v3_i_bd, _h_v3_j_bd⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v2 z 2#usize 10#usize hi2 hi10
      (by decide) hz h_v2_2 h_v2_10)
  -- Step 4: ntt_step v3 z 3 11.
  have h_v3_3 : (v3.elements.val[3]!).val.natAbs ≤ 29439 := by
    rw [h_v3_unc 3 hi3 (by decide) (by decide),
        h_v2_unc 3 hi3 (by decide) (by decide),
        h_v1_unc 3 hi3 (by decide) (by decide)]; exact hvec 3 hi3
  have h_v3_11 : (v3.elements.val[11]!).val.natAbs ≤ 29439 := by
    rw [h_v3_unc 11 hi11 (by decide) (by decide),
        h_v2_unc 11 hi11 (by decide) (by decide),
        h_v1_unc 11 hi11 (by decide) (by decide)]; exact hvec 11 hi11
  obtain ⟨v4, h_v4_eq, h_v4_lift, h_v4_unc, _h_v4_i_bd, _h_v4_j_bd⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v3 z 3#usize 11#usize hi3 hi11
      (by decide) hz h_v3_3 h_v3_11)
  -- Step 5: ntt_step v4 z 4 12.
  have h_v4_4 : (v4.elements.val[4]!).val.natAbs ≤ 29439 := by
    rw [h_v4_unc 4 hi4 (by decide) (by decide),
        h_v3_unc 4 hi4 (by decide) (by decide),
        h_v2_unc 4 hi4 (by decide) (by decide),
        h_v1_unc 4 hi4 (by decide) (by decide)]; exact hvec 4 hi4
  have h_v4_12 : (v4.elements.val[12]!).val.natAbs ≤ 29439 := by
    rw [h_v4_unc 12 hi12 (by decide) (by decide),
        h_v3_unc 12 hi12 (by decide) (by decide),
        h_v2_unc 12 hi12 (by decide) (by decide),
        h_v1_unc 12 hi12 (by decide) (by decide)]; exact hvec 12 hi12
  obtain ⟨v5, h_v5_eq, h_v5_lift, h_v5_unc, _h_v5_i_bd, _h_v5_j_bd⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v4 z 4#usize 12#usize hi4 hi12
      (by decide) hz h_v4_4 h_v4_12)
  -- Step 6: ntt_step v5 z 5 13.
  have h_v5_5 : (v5.elements.val[5]!).val.natAbs ≤ 29439 := by
    rw [h_v5_unc 5 hi5 (by decide) (by decide),
        h_v4_unc 5 hi5 (by decide) (by decide),
        h_v3_unc 5 hi5 (by decide) (by decide),
        h_v2_unc 5 hi5 (by decide) (by decide),
        h_v1_unc 5 hi5 (by decide) (by decide)]; exact hvec 5 hi5
  have h_v5_13 : (v5.elements.val[13]!).val.natAbs ≤ 29439 := by
    rw [h_v5_unc 13 hi13 (by decide) (by decide),
        h_v4_unc 13 hi13 (by decide) (by decide),
        h_v3_unc 13 hi13 (by decide) (by decide),
        h_v2_unc 13 hi13 (by decide) (by decide),
        h_v1_unc 13 hi13 (by decide) (by decide)]; exact hvec 13 hi13
  obtain ⟨v6, h_v6_eq, h_v6_lift, h_v6_unc, _h_v6_i_bd, _h_v6_j_bd⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v5 z 5#usize 13#usize hi5 hi13
      (by decide) hz h_v5_5 h_v5_13)
  -- Step 7: ntt_step v6 z 6 14.
  have h_v6_6 : (v6.elements.val[6]!).val.natAbs ≤ 29439 := by
    rw [h_v6_unc 6 hi6 (by decide) (by decide),
        h_v5_unc 6 hi6 (by decide) (by decide),
        h_v4_unc 6 hi6 (by decide) (by decide),
        h_v3_unc 6 hi6 (by decide) (by decide),
        h_v2_unc 6 hi6 (by decide) (by decide),
        h_v1_unc 6 hi6 (by decide) (by decide)]; exact hvec 6 hi6
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 29439 := by
    rw [h_v6_unc 14 hi14 (by decide) (by decide),
        h_v5_unc 14 hi14 (by decide) (by decide),
        h_v4_unc 14 hi14 (by decide) (by decide),
        h_v3_unc 14 hi14 (by decide) (by decide),
        h_v2_unc 14 hi14 (by decide) (by decide),
        h_v1_unc 14 hi14 (by decide) (by decide)]; exact hvec 14 hi14
  obtain ⟨v7, h_v7_eq, h_v7_lift, h_v7_unc, _h_v7_i_bd, _h_v7_j_bd⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v6 z 6#usize 14#usize hi6 hi14
      (by decide) hz h_v6_6 h_v6_14)
  -- Step 8: ntt_step v7 z 7 15.
  have h_v7_7 : (v7.elements.val[7]!).val.natAbs ≤ 29439 := by
    rw [h_v7_unc 7 hi7 (by decide) (by decide),
        h_v6_unc 7 hi7 (by decide) (by decide),
        h_v5_unc 7 hi7 (by decide) (by decide),
        h_v4_unc 7 hi7 (by decide) (by decide),
        h_v3_unc 7 hi7 (by decide) (by decide),
        h_v2_unc 7 hi7 (by decide) (by decide),
        h_v1_unc 7 hi7 (by decide) (by decide)]; exact hvec 7 hi7
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 29439 := by
    rw [h_v7_unc 15 hi15 (by decide) (by decide),
        h_v6_unc 15 hi15 (by decide) (by decide),
        h_v5_unc 15 hi15 (by decide) (by decide),
        h_v4_unc 15 hi15 (by decide) (by decide),
        h_v3_unc 15 hi15 (by decide) (by decide),
        h_v2_unc 15 hi15 (by decide) (by decide),
        h_v1_unc 15 hi15 (by decide) (by decide)]; exact hvec 15 hi15
  obtain ⟨v8, h_v8_eq, h_v8_lift, _h_v8_unc, _h_v8_i_bd, _h_v8_j_bd⟩ :=
    triple_exists_ok_fc (ntt_step_pair_fc v7 z 7#usize 15#usize hi7 hi15
      (by decide) hz h_v7_7 h_v7_15)
  -- Compose into a single `.ok v8` for the layer body.
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step vec z = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step
    rw [h_v1_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v2_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v3_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v4_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v5_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v6_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v7_eq]; simp only [Aeneas.Std.bind_tc_ok]
    exact h_v8_eq
  apply triple_of_ok_fc h_body
  -- Chain the 8 lift equations into the spec composition.
  unfold Spec.chunk_ntt_layer_3_step_pure
  rw [h_v8_lift, h_v7_lift, h_v6_lift, h_v5_lift, h_v4_lift, h_v3_lift, h_v2_lift, h_v1_lift]

/-- L2.5 — `inv_ntt_step`: per-pair inverse butterfly.

    **Preconditions beyond locked statement** (precondition adjustment):
    - `hne : i.val ≠ j.val` — without this the impl's two writes
      (`vec[i] := o0` then `vec[j] := o1`) at the same index yield `o1`
      while the spec's `(a.set i new_i).set j new_j` with `i = j` also
      yields `new_j`, but the lift-level proof bifurcates messily. Real
      callers (inv_ntt_layer_{1,2,3}_step) all use distinct `i, j`.
    - `hvec : ∀ k < 16, |vec[k]| ≤ 13312` (= 4·3328) — needed so that
      `wrapping_add (vec[j], vec[i])` and `wrapping_sub (vec[j], vec[i])`
      don't overflow at the I16 level. Since `|vec[j]| + |vec[i]| ≤
      26624 < 32768`, both ops have `.val = b + a` and `b - a` exactly.
      This mirrors the legacy `inv_ntt_step_spec_B` with `B = 4`. -/
@[spec]
theorem inv_ntt_step_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i j : Std.Usize)
    (hi : i.val < 16) (hj : j.val < 16)
    (hne : i.val ≠ j.val)
    (hzeta : zeta.val.natAbs ≤ 1664)
    (hvec : ∀ k : Nat, k < 16 →
      (vec.elements.val[k]!).val.natAbs ≤ 13312) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step vec zeta i j
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_inv_ntt_step_pure (lift_chunk vec) (lift_fe_mont zeta) i j ⌝ ⦄ := by
  -- Step 0: vector length facts.
  have h_vec_len : vec.elements.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length vec
  have h_vec_val_len : vec.elements.val.length = 16 := h_vec_len
  -- Step 1: read vec[j] (= i1 in impl, called "b").
  have h_idx_j :
      Aeneas.Std.Array.index_usize vec.elements j = .ok (vec.elements.val[j.val]!) :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq vec.elements j
      (by rw [h_vec_len]; exact hj)
  -- Step 2: read vec[i] (= i2 in impl, called "a").
  have h_idx_i :
      Aeneas.Std.Array.index_usize vec.elements i = .ok (vec.elements.val[i.val]!) :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq vec.elements i
      (by rw [h_vec_len]; exact hi)
  set a : Std.I16 := vec.elements.val[i.val]! with ha_def
  set b : Std.I16 := vec.elements.val[j.val]! with hb_def
  have h_a_bnd : a.val.natAbs ≤ 13312 := hvec i.val hi
  have h_b_bnd : b.val.natAbs ≤ 13312 := hvec j.val hj
  -- Step 3,4: wrapping_sub b a and wrapping_add b a.
  have h_sub_eq :
      CoreModels.core.num.I16.wrapping_sub b a = .ok (Std.I16.wrapping_sub b a) :=
    ntt_step_fc.cm_wrapping_sub_ok_eq b a
  have h_add_eq :
      CoreModels.core.num.I16.wrapping_add b a = .ok (Std.I16.wrapping_add b a) :=
    ntt_step_fc.cm_wrapping_add_ok_eq b a
  set a_minus_b : Std.I16 := Std.I16.wrapping_sub b a with hamb_def
  set a_plus_b  : Std.I16 := Std.I16.wrapping_add b a with hapb_def
  -- No-overflow for wrapping_add b a: |b.val + a.val| ≤ 2·13312 = 26624 < 32768.
  have h_apb_val : a_plus_b.val = b.val + a.val := by
    have h_sum_abs : ((b.val + a.val : Int)).natAbs ≤ 26624 := by
      have h_tri : (b.val + a.val).natAbs ≤ b.val.natAbs + a.val.natAbs :=
        Int.natAbs_add_le _ _
      omega
    have h_lb : -(2 ^ 15 : Int) ≤ b.val + a.val := by omega
    have h_ub : b.val + a.val < (2 ^ 15 : Int) := by omega
    have h_bmod : Int.bmod (b.val + a.val) (2 ^ 16) = b.val + a.val := by
      apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
      · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
        exact le_trans h_const h_lb
      · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
        exact lt_of_lt_of_le h_ub h_const
    have h_val := Std.I16.wrapping_add_val_eq b a
    rw [hapb_def, h_val, h_bmod]
  have h_amb_val : a_minus_b.val = b.val - a.val := by
    have h_diff_abs : ((b.val - a.val : Int)).natAbs ≤ 26624 := by
      have h_neg_natAbs : (-a.val).natAbs = a.val.natAbs := Int.natAbs_neg _
      have h_eq : b.val - a.val = b.val + (-a.val) := by ring
      rw [h_eq]
      have h_tri : (b.val + (-a.val)).natAbs ≤ b.val.natAbs + (-a.val).natAbs :=
        Int.natAbs_add_le _ _
      rw [h_neg_natAbs] at h_tri
      omega
    have h_lb : -(2 ^ 15 : Int) ≤ b.val - a.val := by omega
    have h_ub : b.val - a.val < (2 ^ 15 : Int) := by omega
    have h_bmod : Int.bmod (b.val - a.val) (2 ^ 16) = b.val - a.val := by
      apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
      · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
        exact le_trans h_const h_lb
      · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
        exact lt_of_lt_of_le h_ub h_const
    have h_val := Std.I16.wrapping_sub_val_eq b a
    rw [hamb_def, h_val, h_bmod]
  -- Bound on a_plus_b for L0.2 (≤ 26624 ≤ 32767).
  have h_apb_bd : a_plus_b.val.natAbs ≤ 32767 := by
    rw [h_apb_val]
    have h_tri : (b.val + a.val).natAbs ≤ b.val.natAbs + a.val.natAbs :=
      Int.natAbs_add_le _ _
    omega
  -- Step 5: L0.2 barrett_reduce_element on a_plus_b.
  obtain ⟨o0, h_o0_eq_ok, h_o0_bd, h_o0_lift⟩ :=
    triple_exists_ok_fc (barrett_reduce_element_fc a_plus_b h_apb_bd)
  -- Recover modq form via legacy (needed since L0.2-FC delivers `lift_fe o0 =
  -- barrett_pure (lift_fe a_plus_b)` but we need `lift_fe o0 = add_pure (lift_fe b)
  -- (lift_fe a)`; the bridge needs the modq equation on `.val`s).
  obtain ⟨o0', h_o0'_eq, h_o0'_modq, _h_o0'_bd⟩ :=
    triple_exists_ok_fc
      (libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.barrett_reduce_element_spec a_plus_b h_apb_bd)
  have h_oo' : o0 = o0' := by
    have : (Result.ok o0 : Result _) = Result.ok o0' := by
      rw [← h_o0_eq_ok, h_o0'_eq]
    cases this; rfl
  -- Step 6: classify zeta = zeta.
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify zeta = .ok zeta :=
    ntt_step_fc.classify_ok_eq zeta
  -- Step 7: L0.4 montgomery_multiply on (a_minus_b, zeta).
  obtain ⟨o1, h_o1_eq_ok, h_o1_bd, h_o1_lift⟩ :=
    triple_exists_ok_fc (montgomery_multiply_fe_by_fer_fc a_minus_b zeta
      (by have := a_minus_b.hBounds; omega) hzeta)
  obtain ⟨o1', h_o1'_eq, h_o1'_bd_tight, h_o1'_modq⟩ :=
    triple_exists_ok_fc
      (libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.montgomery_multiply_fe_by_fer_spec a_minus_b zeta hzeta)
  have h_oo1' : o1 = o1' := by
    have : (Result.ok o1 : Result _) = Result.ok o1' := by
      rw [← h_o1_eq_ok, h_o1'_eq]
    cases this; rfl
  -- Step 8: write vec[i] := o0.
  have h_upd_i :
      Aeneas.Std.Array.update vec.elements i o0
        = .ok (vec.elements.set i o0) :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_update_ok_eq vec.elements i o0
      (by rw [h_vec_len]; exact hi)
  -- Step 9: write vec[j] := o1.
  have h_upd_j :
      Aeneas.Std.Array.update (vec.elements.set i o0) j o1
        = .ok ((vec.elements.set i o0).set j o1) := by
    have h_len : (vec.elements.set i o0).length = 16 := by
      rw [Std.Array.set_length]; exact h_vec_len
    exact libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_update_ok_eq _ j o1
      (by rw [h_len]; exact hj)
  -- Compose into `.ok final_vec`.
  set final_elements : Std.Array Std.I16 16#usize :=
    (vec.elements.set i o0).set j o1 with hfe_def
  set final_vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    { elements := final_elements } with hfv_def
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step vec zeta i j
        = .ok final_vec := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step
    rw [h_idx_j]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_idx_i]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_sub_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_add_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [← h_oo'] at h_o0'_eq
    rw [h_o0_eq_ok]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_classify]; simp only [Aeneas.Std.bind_tc_ok]
    rw [← h_oo1'] at h_o1'_eq
    rw [h_o1_eq_ok]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_upd_i]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_upd_j]; simp only [Aeneas.Std.bind_tc_ok]; rfl
  apply triple_of_ok_fc h_body
  -- Now: prove the FC chunk equation.
  -- spec new_i := add_pure (lift_fe b) (lift_fe a)
  -- spec new_j := mul_pure (sub_pure (lift_fe b) (lift_fe a)) (lift_fe_mont zeta)
  set s_new_i : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
      (lift_fe b) (lift_fe a) with hs_new_i_def
  set s_diff : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
      (lift_fe b) (lift_fe a) with hs_diff_def
  set s_new_j : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
      s_diff (lift_fe_mont zeta) with hs_new_j_def
  unfold lift_chunk Spec.chunk_inv_ntt_step_pure
  apply Subtype.ext
  simp only [Std.Array.set_val_eq]
  -- Bridge: (vec.elements.val.map lift_fe)[k]! = lift_fe (vec.elements.val[k]!) when k < 16.
  have h_map_lift_at (k : Nat) (hk : k < 16) :
      (vec.elements.val.map lift_fe)[k]! = lift_fe (vec.elements.val[k]!) := by
    have hk_lhs : k < (vec.elements.val.map lift_fe).length := by
      simp [List.length_map, h_vec_val_len]; exact hk
    rw [getElem!_pos (vec.elements.val.map lift_fe) k hk_lhs]
    rw [List.getElem_map]
    have hk_vec : k < vec.elements.val.length := by rw [h_vec_val_len]; exact hk
    rw [getElem!_pos vec.elements.val k hk_vec]
  show ((vec.elements.val.set i.val o0).set j.val o1).map lift_fe
      = ((vec.elements.val.map lift_fe).set i.val
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            ((vec.elements.val.map lift_fe)[j.val]!)
            ((vec.elements.val.map lift_fe)[i.val]!))).set j.val
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
            ((vec.elements.val.map lift_fe)[j.val]!)
            ((vec.elements.val.map lift_fe)[i.val]!))
          (lift_fe_mont zeta))
  rw [h_map_lift_at i.val hi, h_map_lift_at j.val hj]
  change ((vec.elements.val.set i.val o0).set j.val o1).map lift_fe
      = ((vec.elements.val.map lift_fe).set i.val s_new_i).set j.val s_new_j
  apply List.ext_getElem
  · simp [List.length_map, List.length_set]
  · intro k hk1 hk2
    have hk : k < 16 := by
      have hk' : k < (((vec.elements.val.set i.val o0).set j.val o1).map lift_fe).length := hk1
      simp [List.length_map, List.length_set, h_vec_val_len] at hk'
      exact hk'
    rw [List.getElem_map]
    by_cases h_eq_j : k = j.val
    · -- k = j.val: r[j] = o1 = mont_mul(b-a, zeta).
      subst h_eq_j
      rw [List.getElem_set_self]
      rw [List.getElem_set_self]
      show lift_fe o1 = s_new_j
      -- mont_mul a_minus_b zeta produced o1. We have h_o1'_modq:
      -- modq_eq o1'.val (a_minus_b.val * zeta.val * 169) 3329.
      -- lift_fe o1 = lift_fe o1' (h_oo1') = mul_pure (lift_fe a_minus_b) (lift_fe_mont zeta).
      have h_step1 :
          lift_fe o1 = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (lift_fe a_minus_b) (lift_fe_mont zeta) := by
        rw [h_oo1']
        exact lift_fe_mul_pure_mont_eq a_minus_b zeta o1' h_o1'_modq
      rw [h_step1]
      -- Now: mul_pure (lift_fe a_minus_b) (lift_fe_mont zeta) = s_new_j
      --    = mul_pure s_diff (lift_fe_mont zeta) where s_diff = sub_pure (lift_fe b) (lift_fe a).
      -- Reduce by congr 1 to: lift_fe a_minus_b = s_diff.
      simp only [hs_new_j_def]
      congr 1
      -- lift_fe a_minus_b = sub_pure (lift_fe b) (lift_fe a).
      exact lift_fe_sub_pure_eq b a a_minus_b h_amb_val
    · rw [List.getElem_set_ne (Ne.symm h_eq_j)]
      rw [List.getElem_set_ne (Ne.symm h_eq_j)]
      by_cases h_eq_i : k = i.val
      · -- k = i.val: r[i] = o0 = barrett(b+a).
        subst h_eq_i
        rw [List.getElem_set_self]
        rw [List.getElem_set_self]
        show lift_fe o0 = s_new_i
        -- lift_fe o0 = lift_fe o0' (h_oo') from h_o0'_modq:
        --   modq_eq o0'.val a_plus_b.val 3329.
        -- Then lift_fe o0' = lift_fe a_plus_b = add_pure (lift_fe b) (lift_fe a).
        have h_step1 : lift_fe o0 = lift_fe a_plus_b := by
          rw [h_oo']
          exact lift_fe_eq_of_modq o0' a_plus_b h_o0'_modq
        rw [h_step1]
        -- lift_fe a_plus_b = add_pure (lift_fe b) (lift_fe a) via h_apb_val.
        simp only [hs_new_i_def]
        exact lift_fe_add_pure_eq b a a_plus_b h_apb_val
      · -- k ≠ i.val, k ≠ j.val.
        rw [List.getElem_set_ne (Ne.symm h_eq_i)]
        rw [List.getElem_set_ne (Ne.symm h_eq_i)]
        rw [List.getElem_map]

/-! ### L2.9 — `inv_ntt_layer_1_step` (FC).

    layer-1 vector-level step. Mirrors `ntt_layer_1_step_fc` on the same lane-pair sequence
    `(0,2)(1,3)(4,6)(5,7)(8,10)(9,11)(12,14)(13,15)` with zetas
    `z0,z0,z1,z1,z2,z2,z3,z3` — only the butterfly direction differs.
    Chains 8 `inv_ntt_step` calls via the private `inv_ntt_step_pair_fc`
    helper (mirror of `ntt_step_pair_fc`) which exposes
    both the `lift_chunk` equation AND the unchanged-lane preservation,
    plus the tight per-output bound `≤ 3328` so the bound is preserved
    across the 8-step chain on disjoint lane pairs. -/

/-- Per-lane variant of `inv_ntt_step_fc` for layer composition. Splits
    the universal precondition into per-lane bounds on `i` and `j` (only
    the two lanes actually read), and exposes:
    1. The `lift_chunk` equation (the spec-bridge).
    2. **Unchanged-lane preservation**: `r[k] = vec[k]` for `k ≠ i, j`.
    3. **Tight per-output bound `≤ 3328`** at both `i` and `j`. `r[i]` is
       `barrett(vec[j] + vec[i])` (post-barrett bound is `≤ 3328`); `r[j]`
       is `montgomery_multiply(vec[j] - vec[i], zeta)` whose Equivalence
       spec also gives the tight `≤ 3328` bound. -/
theorem inv_ntt_step_pair_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i j : Std.Usize)
    (hi : i.val < 16) (hj : j.val < 16)
    (hne : i.val ≠ j.val)
    (hzeta : zeta.val.natAbs ≤ 1664)
    (h_a_bnd : (vec.elements.val[i.val]!).val.natAbs ≤ 13312)
    (h_b_bnd : (vec.elements.val[j.val]!).val.natAbs ≤ 13312) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step vec zeta i j
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_inv_ntt_step_pure (lift_chunk vec) (lift_fe_mont zeta) i j
              ∧ (∀ k : Nat, k < 16 → k ≠ i.val → k ≠ j.val →
                  (r.elements.val[k]!) = (vec.elements.val[k]!))
              ∧ (r.elements.val[i.val]!).val.natAbs ≤ 3328
              ∧ (r.elements.val[j.val]!).val.natAbs ≤ 3328 ⌝ ⦄ := by
  -- Step 0: vector length facts.
  have h_vec_len : vec.elements.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length vec
  have h_vec_val_len : vec.elements.val.length = 16 := h_vec_len
  -- Step 1: read vec[j] (= i1 in impl, called "b").
  have h_idx_j :
      Aeneas.Std.Array.index_usize vec.elements j = .ok (vec.elements.val[j.val]!) :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq vec.elements j
      (by rw [h_vec_len]; exact hj)
  -- Step 2: read vec[i] (= i2 in impl, called "a").
  have h_idx_i :
      Aeneas.Std.Array.index_usize vec.elements i = .ok (vec.elements.val[i.val]!) :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq vec.elements i
      (by rw [h_vec_len]; exact hi)
  set a : Std.I16 := vec.elements.val[i.val]! with ha_def
  set b : Std.I16 := vec.elements.val[j.val]! with hb_def
  -- Step 3,4: wrapping_sub b a and wrapping_add b a.
  have h_sub_eq :
      CoreModels.core.num.I16.wrapping_sub b a = .ok (Std.I16.wrapping_sub b a) :=
    ntt_step_fc.cm_wrapping_sub_ok_eq b a
  have h_add_eq :
      CoreModels.core.num.I16.wrapping_add b a = .ok (Std.I16.wrapping_add b a) :=
    ntt_step_fc.cm_wrapping_add_ok_eq b a
  set a_minus_b : Std.I16 := Std.I16.wrapping_sub b a with hamb_def
  set a_plus_b  : Std.I16 := Std.I16.wrapping_add b a with hapb_def
  -- No-overflow for wrapping_add b a: |b.val + a.val| ≤ 2·13312 = 26624 < 32768.
  have h_apb_val : a_plus_b.val = b.val + a.val := by
    have h_sum_abs : ((b.val + a.val : Int)).natAbs ≤ 26624 := by
      have h_tri : (b.val + a.val).natAbs ≤ b.val.natAbs + a.val.natAbs :=
        Int.natAbs_add_le _ _
      omega
    have h_lb : -(2 ^ 15 : Int) ≤ b.val + a.val := by omega
    have h_ub : b.val + a.val < (2 ^ 15 : Int) := by omega
    have h_bmod : Int.bmod (b.val + a.val) (2 ^ 16) = b.val + a.val := by
      apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
      · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
        exact le_trans h_const h_lb
      · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
        exact lt_of_lt_of_le h_ub h_const
    have h_val := Std.I16.wrapping_add_val_eq b a
    rw [hapb_def, h_val, h_bmod]
  have h_amb_val : a_minus_b.val = b.val - a.val := by
    have h_diff_abs : ((b.val - a.val : Int)).natAbs ≤ 26624 := by
      have h_neg_natAbs : (-a.val).natAbs = a.val.natAbs := Int.natAbs_neg _
      have h_eq : b.val - a.val = b.val + (-a.val) := by ring
      rw [h_eq]
      have h_tri : (b.val + (-a.val)).natAbs ≤ b.val.natAbs + (-a.val).natAbs :=
        Int.natAbs_add_le _ _
      rw [h_neg_natAbs] at h_tri
      omega
    have h_lb : -(2 ^ 15 : Int) ≤ b.val - a.val := by omega
    have h_ub : b.val - a.val < (2 ^ 15 : Int) := by omega
    have h_bmod : Int.bmod (b.val - a.val) (2 ^ 16) = b.val - a.val := by
      apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
      · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
        exact le_trans h_const h_lb
      · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
        exact lt_of_lt_of_le h_ub h_const
    have h_val := Std.I16.wrapping_sub_val_eq b a
    rw [hamb_def, h_val, h_bmod]
  -- Bound on a_plus_b for L0.2 (≤ 26624 ≤ 32767).
  have h_apb_bd : a_plus_b.val.natAbs ≤ 32767 := by
    rw [h_apb_val]
    have h_tri : (b.val + a.val).natAbs ≤ b.val.natAbs + a.val.natAbs :=
      Int.natAbs_add_le _ _
    omega
  -- Step 5: L0.2 barrett_reduce_element on a_plus_b. Bound: |o0| ≤ 3328.
  obtain ⟨o0, h_o0_eq_ok, h_o0_bd, _h_o0_lift⟩ :=
    triple_exists_ok_fc (barrett_reduce_element_fc a_plus_b h_apb_bd)
  obtain ⟨o0', h_o0'_eq, h_o0'_modq, _h_o0'_bd⟩ :=
    triple_exists_ok_fc
      (libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.barrett_reduce_element_spec a_plus_b h_apb_bd)
  have h_oo' : o0 = o0' := by
    have : (Result.ok o0 : Result _) = Result.ok o0' := by
      rw [← h_o0_eq_ok, h_o0'_eq]
    cases this; rfl
  -- Step 6: classify zeta = zeta.
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify zeta = .ok zeta :=
    ntt_step_fc.classify_ok_eq zeta
  -- Step 7: L0.4 montgomery_multiply on (a_minus_b, zeta). Bound: |o1| ≤ 3328+1665 = 4993.
  obtain ⟨o1, h_o1_eq_ok, h_o1_bd, _h_o1_lift⟩ :=
    triple_exists_ok_fc (montgomery_multiply_fe_by_fer_fc a_minus_b zeta
      (by have := a_minus_b.hBounds; omega) hzeta)
  obtain ⟨o1', h_o1'_eq, h_o1'_bd_tight, h_o1'_modq⟩ :=
    triple_exists_ok_fc
      (libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.montgomery_multiply_fe_by_fer_spec a_minus_b zeta hzeta)
  have h_oo1' : o1 = o1' := by
    have : (Result.ok o1 : Result _) = Result.ok o1' := by
      rw [← h_o1_eq_ok, h_o1'_eq]
    cases this; rfl
  -- Step 8: write vec[i] := o0.
  have h_upd_i :
      Aeneas.Std.Array.update vec.elements i o0
        = .ok (vec.elements.set i o0) :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_update_ok_eq vec.elements i o0
      (by rw [h_vec_len]; exact hi)
  -- Step 9: write vec[j] := o1.
  have h_upd_j :
      Aeneas.Std.Array.update (vec.elements.set i o0) j o1
        = .ok ((vec.elements.set i o0).set j o1) := by
    have h_len : (vec.elements.set i o0).length = 16 := by
      rw [Std.Array.set_length]; exact h_vec_len
    exact libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_update_ok_eq _ j o1
      (by rw [h_len]; exact hj)
  -- Compose into `.ok final_vec`.
  set final_elements : Std.Array Std.I16 16#usize :=
    (vec.elements.set i o0).set j o1 with hfe_def
  set final_vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    { elements := final_elements } with hfv_def
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step vec zeta i j
        = .ok final_vec := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_step
    rw [h_idx_j]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_idx_i]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_sub_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_add_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [← h_oo'] at h_o0'_eq
    rw [h_o0_eq_ok]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_classify]; simp only [Aeneas.Std.bind_tc_ok]
    rw [← h_oo1'] at h_o1'_eq
    rw [h_o1_eq_ok]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_upd_i]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_upd_j]; simp only [Aeneas.Std.bind_tc_ok]; rfl
  apply triple_of_ok_fc h_body
  -- Helper: bridge for `(vec.elements.val.map lift_fe)[k]! = lift_fe (vec.elements.val[k]!)`.
  have h_map_lift_at (k : Nat) (hk : k < 16) :
      (vec.elements.val.map lift_fe)[k]! = lift_fe (vec.elements.val[k]!) := by
    have hk_lhs : k < (vec.elements.val.map lift_fe).length := by
      simp [List.length_map, h_vec_val_len]; exact hk
    rw [getElem!_pos (vec.elements.val.map lift_fe) k hk_lhs]
    rw [List.getElem_map]
    have hk_vec : k < vec.elements.val.length := by rw [h_vec_val_len]; exact hk
    rw [getElem!_pos vec.elements.val k hk_vec]
  -- Now: 4 conjuncts.
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- lift_chunk equation: same as keystone proof.
    set s_new_i : hacspec_ml_kem.parameters.FieldElement :=
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
        (lift_fe b) (lift_fe a) with hs_new_i_def
    set s_diff : hacspec_ml_kem.parameters.FieldElement :=
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
        (lift_fe b) (lift_fe a) with hs_diff_def
    set s_new_j : hacspec_ml_kem.parameters.FieldElement :=
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
        s_diff (lift_fe_mont zeta) with hs_new_j_def
    unfold lift_chunk Spec.chunk_inv_ntt_step_pure
    apply Subtype.ext
    simp only [Std.Array.set_val_eq]
    show ((vec.elements.val.set i.val o0).set j.val o1).map lift_fe
        = ((vec.elements.val.map lift_fe).set i.val
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              ((vec.elements.val.map lift_fe)[j.val]!)
              ((vec.elements.val.map lift_fe)[i.val]!))).set j.val
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
              ((vec.elements.val.map lift_fe)[j.val]!)
              ((vec.elements.val.map lift_fe)[i.val]!))
            (lift_fe_mont zeta))
    rw [h_map_lift_at i.val hi, h_map_lift_at j.val hj]
    change ((vec.elements.val.set i.val o0).set j.val o1).map lift_fe
        = ((vec.elements.val.map lift_fe).set i.val s_new_i).set j.val s_new_j
    apply List.ext_getElem
    · simp [List.length_map, List.length_set]
    · intro k hk1 hk2
      have hk : k < 16 := by
        have hk' : k < (((vec.elements.val.set i.val o0).set j.val o1).map lift_fe).length := hk1
        simp [List.length_map, List.length_set, h_vec_val_len] at hk'
        exact hk'
      rw [List.getElem_map]
      by_cases h_eq_j : k = j.val
      · subst h_eq_j
        rw [List.getElem_set_self]
        rw [List.getElem_set_self]
        show lift_fe o1 = s_new_j
        have h_step1 :
            lift_fe o1 = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (lift_fe a_minus_b) (lift_fe_mont zeta) := by
          rw [h_oo1']
          exact lift_fe_mul_pure_mont_eq a_minus_b zeta o1' h_o1'_modq
        rw [h_step1]
        simp only [hs_new_j_def]
        congr 1
        exact lift_fe_sub_pure_eq b a a_minus_b h_amb_val
      · rw [List.getElem_set_ne (Ne.symm h_eq_j)]
        rw [List.getElem_set_ne (Ne.symm h_eq_j)]
        by_cases h_eq_i : k = i.val
        · subst h_eq_i
          rw [List.getElem_set_self]
          rw [List.getElem_set_self]
          show lift_fe o0 = s_new_i
          have h_step1 : lift_fe o0 = lift_fe a_plus_b := by
            rw [h_oo']
            exact lift_fe_eq_of_modq o0' a_plus_b h_o0'_modq
          rw [h_step1]
          simp only [hs_new_i_def]
          exact lift_fe_add_pure_eq b a a_plus_b h_apb_val
        · rw [List.getElem_set_ne (Ne.symm h_eq_i)]
          rw [List.getElem_set_ne (Ne.symm h_eq_i)]
          rw [List.getElem_map]
  · -- Untouched-lane preservation: r[k] = vec[k] for k ≠ i, j.
    -- final_vec.elements.val = (vec.elements.set i o0).set j o1 .val
    intro k hk hki hkj
    show ((vec.elements.set i o0).set j o1).val[k]!
      = vec.elements.val[k]!
    have h_set_val_eq : ((vec.elements.set i o0).set j o1).val
        = (vec.elements.val.set i.val o0).set j.val o1 := by
      simp [Std.Array.set_val_eq]
    rw [h_set_val_eq]
    rw [getElem!_pos _ k (by simp [List.length_set, h_vec_val_len]; exact hk)]
    rw [List.getElem_set_ne (Ne.symm hkj)]
    rw [List.getElem_set_ne (Ne.symm hki)]
    rw [getElem!_pos vec.elements.val k (by rw [h_vec_val_len]; exact hk)]
  · -- Bound at i: r[i] = o0 (set last) — since i ≠ j (hne), second set doesn't touch i,
    -- so r[i] = (set i o0)[i] = o0. |o0| ≤ 3328 (tight, from barrett_reduce).
    show ((vec.elements.set i o0).set j o1).val[i.val]!.val.natAbs ≤ 3328
    have h_set_val_eq : ((vec.elements.set i o0).set j o1).val
        = (vec.elements.val.set i.val o0).set j.val o1 := by
      simp [Std.Array.set_val_eq]
    rw [h_set_val_eq]
    rw [getElem!_pos _ i.val (by simp [List.length_set, h_vec_val_len]; exact hi)]
    rw [List.getElem_set_ne (Ne.symm hne)]
    rw [List.getElem_set_self]
    -- now goal: o0.val.natAbs ≤ 3328. h_o0_bd : o0.val.natAbs ≤ 3328.
    exact h_o0_bd
  · -- Bound at j: r[j] = o1 (second set wins). |o1| ≤ 3328 (tight, via
    -- `montgomery_multiply_fe_by_fer_spec`).
    show ((vec.elements.set i o0).set j o1).val[j.val]!.val.natAbs ≤ 3328
    have h_set_val_eq : ((vec.elements.set i o0).set j o1).val
        = (vec.elements.val.set i.val o0).set j.val o1 := by
      simp [Std.Array.set_val_eq]
    rw [h_set_val_eq]
    rw [getElem!_pos _ j.val (by simp [List.length_set, h_vec_val_len]; exact hj)]
    rw [List.getElem_set_self]
    -- goal: o1.val.natAbs ≤ 3328. h_o1'_bd_tight : o1'.val.natAbs ≤ 3328 with o1 = o1'.
    rw [h_oo1']; exact h_o1'_bd_tight

/-- L2.9 — `inv_ntt_layer_1_step`: vector-level layer-1 inverse step.
    Maps `lift_chunk` of the impl output to `Spec.chunk_inv_ntt_layer_1_step_pure`
    applied to `lift_chunk` of the input and the canonical-domain zetas.

    **Precondition adjustment** (beyond locked statement):
    - `hz : |z_k| ≤ 1664` for each zeta — Mont-domain zeta from `polynomial.zeta`.
    - `hvec : ∀ k < 16, |vec[k]| ≤ 13312` — preserved across 8 sequential
      `inv_ntt_step` invocations on disjoint pairs (each lane after a step is
      either ≤ 3328 from barrett, ≤ 4993 from mont-mul, or unchanged ≤ 13312). -/
@[spec]
theorem inv_ntt_layer_1_step_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (z0 z1 z2 z3 : Std.I16)
    (hz : z0.val.natAbs ≤ 1664 ∧ z1.val.natAbs ≤ 1664
        ∧ z2.val.natAbs ≤ 1664 ∧ z3.val.natAbs ≤ 1664)
    (hvec : ∀ k : Nat, k < 16 →
      (vec.elements.val[k]!).val.natAbs ≤ 13312) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_1_step vec z0 z1 z2 z3
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_inv_ntt_layer_1_step_pure (lift_chunk vec)
                    (lift_fe_mont z0) (lift_fe_mont z1)
                    (lift_fe_mont z2) (lift_fe_mont z3)
              ∧ (∀ k : Nat, k < 16 →
                  (r.elements.val[k]!).val.natAbs ≤ 3328) ⌝ ⦄ := by
  obtain ⟨hz0, hz1, hz2, hz3⟩ := hz
  have hi0 : (0 : Nat) < 16 := by decide
  have hi1 : (1 : Nat) < 16 := by decide
  have hi2 : (2 : Nat) < 16 := by decide
  have hi3 : (3 : Nat) < 16 := by decide
  have hi4 : (4 : Nat) < 16 := by decide
  have hi5 : (5 : Nat) < 16 := by decide
  have hi6 : (6 : Nat) < 16 := by decide
  have hi7 : (7 : Nat) < 16 := by decide
  have hi8 : (8 : Nat) < 16 := by decide
  have hi9 : (9 : Nat) < 16 := by decide
  have hi10 : (10 : Nat) < 16 := by decide
  have hi11 : (11 : Nat) < 16 := by decide
  have hi12 : (12 : Nat) < 16 := by decide
  have hi13 : (13 : Nat) < 16 := by decide
  have hi14 : (14 : Nat) < 16 := by decide
  have hi15 : (15 : Nat) < 16 := by decide
  -- Step 1: inv_ntt_step vec z0 0 2.
  obtain ⟨v1, h_v1_eq, h_v1_lift, h_v1_unc, h_v1_bnd_0, h_v1_bnd_2⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc vec z0 0#usize 2#usize hi0 hi2
      (by decide) hz0 (hvec 0 hi0) (hvec 2 hi2))
  -- Step 2: inv_ntt_step v1 z0 1 3.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 13312 := by
    rw [h_v1_unc 1 hi1 (by decide) (by decide)]; exact hvec 1 hi1
  have h_v1_3 : (v1.elements.val[3]!).val.natAbs ≤ 13312 := by
    rw [h_v1_unc 3 hi3 (by decide) (by decide)]; exact hvec 3 hi3
  obtain ⟨v2, h_v2_eq, h_v2_lift, h_v2_unc, h_v2_bnd_1, h_v2_bnd_3⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v1 z0 1#usize 3#usize hi1 hi3
      (by decide) hz0 h_v1_1 h_v1_3)
  -- Step 3: inv_ntt_step v2 z1 4 6.
  have h_v2_4 : (v2.elements.val[4]!).val.natAbs ≤ 13312 := by
    rw [h_v2_unc 4 hi4 (by decide) (by decide),
        h_v1_unc 4 hi4 (by decide) (by decide)]; exact hvec 4 hi4
  have h_v2_6 : (v2.elements.val[6]!).val.natAbs ≤ 13312 := by
    rw [h_v2_unc 6 hi6 (by decide) (by decide),
        h_v1_unc 6 hi6 (by decide) (by decide)]; exact hvec 6 hi6
  obtain ⟨v3, h_v3_eq, h_v3_lift, h_v3_unc, h_v3_bnd_4, h_v3_bnd_6⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v2 z1 4#usize 6#usize hi4 hi6
      (by decide) hz1 h_v2_4 h_v2_6)
  -- Step 4: inv_ntt_step v3 z1 5 7.
  have h_v3_5 : (v3.elements.val[5]!).val.natAbs ≤ 13312 := by
    rw [h_v3_unc 5 hi5 (by decide) (by decide),
        h_v2_unc 5 hi5 (by decide) (by decide),
        h_v1_unc 5 hi5 (by decide) (by decide)]; exact hvec 5 hi5
  have h_v3_7 : (v3.elements.val[7]!).val.natAbs ≤ 13312 := by
    rw [h_v3_unc 7 hi7 (by decide) (by decide),
        h_v2_unc 7 hi7 (by decide) (by decide),
        h_v1_unc 7 hi7 (by decide) (by decide)]; exact hvec 7 hi7
  obtain ⟨v4, h_v4_eq, h_v4_lift, h_v4_unc, h_v4_bnd_5, h_v4_bnd_7⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v3 z1 5#usize 7#usize hi5 hi7
      (by decide) hz1 h_v3_5 h_v3_7)
  -- Step 5: inv_ntt_step v4 z2 8 10.
  have h_v4_8 : (v4.elements.val[8]!).val.natAbs ≤ 13312 := by
    rw [h_v4_unc 8 hi8 (by decide) (by decide),
        h_v3_unc 8 hi8 (by decide) (by decide),
        h_v2_unc 8 hi8 (by decide) (by decide),
        h_v1_unc 8 hi8 (by decide) (by decide)]; exact hvec 8 hi8
  have h_v4_10 : (v4.elements.val[10]!).val.natAbs ≤ 13312 := by
    rw [h_v4_unc 10 hi10 (by decide) (by decide),
        h_v3_unc 10 hi10 (by decide) (by decide),
        h_v2_unc 10 hi10 (by decide) (by decide),
        h_v1_unc 10 hi10 (by decide) (by decide)]; exact hvec 10 hi10
  obtain ⟨v5, h_v5_eq, h_v5_lift, h_v5_unc, h_v5_bnd_8, h_v5_bnd_10⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v4 z2 8#usize 10#usize hi8 hi10
      (by decide) hz2 h_v4_8 h_v4_10)
  -- Step 6: inv_ntt_step v5 z2 9 11.
  have h_v5_9 : (v5.elements.val[9]!).val.natAbs ≤ 13312 := by
    rw [h_v5_unc 9 hi9 (by decide) (by decide),
        h_v4_unc 9 hi9 (by decide) (by decide),
        h_v3_unc 9 hi9 (by decide) (by decide),
        h_v2_unc 9 hi9 (by decide) (by decide),
        h_v1_unc 9 hi9 (by decide) (by decide)]; exact hvec 9 hi9
  have h_v5_11 : (v5.elements.val[11]!).val.natAbs ≤ 13312 := by
    rw [h_v5_unc 11 hi11 (by decide) (by decide),
        h_v4_unc 11 hi11 (by decide) (by decide),
        h_v3_unc 11 hi11 (by decide) (by decide),
        h_v2_unc 11 hi11 (by decide) (by decide),
        h_v1_unc 11 hi11 (by decide) (by decide)]; exact hvec 11 hi11
  obtain ⟨v6, h_v6_eq, h_v6_lift, h_v6_unc, h_v6_bnd_9, h_v6_bnd_11⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v5 z2 9#usize 11#usize hi9 hi11
      (by decide) hz2 h_v5_9 h_v5_11)
  -- Step 7: inv_ntt_step v6 z3 12 14.
  have h_v6_12 : (v6.elements.val[12]!).val.natAbs ≤ 13312 := by
    rw [h_v6_unc 12 hi12 (by decide) (by decide),
        h_v5_unc 12 hi12 (by decide) (by decide),
        h_v4_unc 12 hi12 (by decide) (by decide),
        h_v3_unc 12 hi12 (by decide) (by decide),
        h_v2_unc 12 hi12 (by decide) (by decide),
        h_v1_unc 12 hi12 (by decide) (by decide)]; exact hvec 12 hi12
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 13312 := by
    rw [h_v6_unc 14 hi14 (by decide) (by decide),
        h_v5_unc 14 hi14 (by decide) (by decide),
        h_v4_unc 14 hi14 (by decide) (by decide),
        h_v3_unc 14 hi14 (by decide) (by decide),
        h_v2_unc 14 hi14 (by decide) (by decide),
        h_v1_unc 14 hi14 (by decide) (by decide)]; exact hvec 14 hi14
  obtain ⟨v7, h_v7_eq, h_v7_lift, h_v7_unc, h_v7_bnd_12, h_v7_bnd_14⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v6 z3 12#usize 14#usize hi12 hi14
      (by decide) hz3 h_v6_12 h_v6_14)
  -- Step 8: inv_ntt_step v7 z3 13 15.
  have h_v7_13 : (v7.elements.val[13]!).val.natAbs ≤ 13312 := by
    rw [h_v7_unc 13 hi13 (by decide) (by decide),
        h_v6_unc 13 hi13 (by decide) (by decide),
        h_v5_unc 13 hi13 (by decide) (by decide),
        h_v4_unc 13 hi13 (by decide) (by decide),
        h_v3_unc 13 hi13 (by decide) (by decide),
        h_v2_unc 13 hi13 (by decide) (by decide),
        h_v1_unc 13 hi13 (by decide) (by decide)]; exact hvec 13 hi13
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 13312 := by
    rw [h_v7_unc 15 hi15 (by decide) (by decide),
        h_v6_unc 15 hi15 (by decide) (by decide),
        h_v5_unc 15 hi15 (by decide) (by decide),
        h_v4_unc 15 hi15 (by decide) (by decide),
        h_v3_unc 15 hi15 (by decide) (by decide),
        h_v2_unc 15 hi15 (by decide) (by decide),
        h_v1_unc 15 hi15 (by decide) (by decide)]; exact hvec 15 hi15
  obtain ⟨v8, h_v8_eq, h_v8_lift, h_v8_unc, h_v8_bnd_13, h_v8_bnd_15⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v7 z3 13#usize 15#usize hi13 hi15
      (by decide) hz3 h_v7_13 h_v7_15)
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_1_step vec z0 z1 z2 z3
        = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_1_step
    rw [h_v1_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v2_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v3_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v4_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v5_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v6_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v7_eq]; simp only [Aeneas.Std.bind_tc_ok]
    exact h_v8_eq
  apply triple_of_ok_fc h_body
  refine ⟨?_, ?_⟩
  · -- Spec equation.
    unfold Spec.chunk_inv_ntt_layer_1_step_pure
    rw [h_v8_lift, h_v7_lift, h_v6_lift, h_v5_lift, h_v4_lift, h_v3_lift, h_v2_lift, h_v1_lift]
  · -- Per-lane output bound ≤ 3328.
    -- Each lane is touched by exactly one of the 8 steps. After that step,
    -- the lane's natAbs is ≤ 3328 (per inv_ntt_step_pair_fc's strengthened
    -- POST). Later steps don't touch it, so v8.elements.val[k]! preserves
    -- that value via the unchanged-lane chain.
    intro k hk
    -- Lane → touching step: 0,2→1; 1,3→2; 4,6→3; 5,7→4; 8,10→5; 9,11→6;
    -- 12,14→7; 13,15→8.
    interval_cases k
    · -- k=0: touched at step 1. Unchanged in steps 2..8.
      rw [h_v8_unc 0 hi0 (by decide) (by decide),
          h_v7_unc 0 hi0 (by decide) (by decide),
          h_v6_unc 0 hi0 (by decide) (by decide),
          h_v5_unc 0 hi0 (by decide) (by decide),
          h_v4_unc 0 hi0 (by decide) (by decide),
          h_v3_unc 0 hi0 (by decide) (by decide),
          h_v2_unc 0 hi0 (by decide) (by decide)]
      exact h_v1_bnd_0
    · -- k=1: touched at step 2.
      rw [h_v8_unc 1 hi1 (by decide) (by decide),
          h_v7_unc 1 hi1 (by decide) (by decide),
          h_v6_unc 1 hi1 (by decide) (by decide),
          h_v5_unc 1 hi1 (by decide) (by decide),
          h_v4_unc 1 hi1 (by decide) (by decide),
          h_v3_unc 1 hi1 (by decide) (by decide)]
      exact h_v2_bnd_1
    · -- k=2: touched at step 1.
      rw [h_v8_unc 2 hi2 (by decide) (by decide),
          h_v7_unc 2 hi2 (by decide) (by decide),
          h_v6_unc 2 hi2 (by decide) (by decide),
          h_v5_unc 2 hi2 (by decide) (by decide),
          h_v4_unc 2 hi2 (by decide) (by decide),
          h_v3_unc 2 hi2 (by decide) (by decide),
          h_v2_unc 2 hi2 (by decide) (by decide)]
      exact h_v1_bnd_2
    · -- k=3: touched at step 2.
      rw [h_v8_unc 3 hi3 (by decide) (by decide),
          h_v7_unc 3 hi3 (by decide) (by decide),
          h_v6_unc 3 hi3 (by decide) (by decide),
          h_v5_unc 3 hi3 (by decide) (by decide),
          h_v4_unc 3 hi3 (by decide) (by decide),
          h_v3_unc 3 hi3 (by decide) (by decide)]
      exact h_v2_bnd_3
    · -- k=4: touched at step 3.
      rw [h_v8_unc 4 hi4 (by decide) (by decide),
          h_v7_unc 4 hi4 (by decide) (by decide),
          h_v6_unc 4 hi4 (by decide) (by decide),
          h_v5_unc 4 hi4 (by decide) (by decide),
          h_v4_unc 4 hi4 (by decide) (by decide)]
      exact h_v3_bnd_4
    · -- k=5: touched at step 4.
      rw [h_v8_unc 5 hi5 (by decide) (by decide),
          h_v7_unc 5 hi5 (by decide) (by decide),
          h_v6_unc 5 hi5 (by decide) (by decide),
          h_v5_unc 5 hi5 (by decide) (by decide)]
      exact h_v4_bnd_5
    · -- k=6: touched at step 3.
      rw [h_v8_unc 6 hi6 (by decide) (by decide),
          h_v7_unc 6 hi6 (by decide) (by decide),
          h_v6_unc 6 hi6 (by decide) (by decide),
          h_v5_unc 6 hi6 (by decide) (by decide),
          h_v4_unc 6 hi6 (by decide) (by decide)]
      exact h_v3_bnd_6
    · -- k=7: touched at step 4.
      rw [h_v8_unc 7 hi7 (by decide) (by decide),
          h_v7_unc 7 hi7 (by decide) (by decide),
          h_v6_unc 7 hi7 (by decide) (by decide),
          h_v5_unc 7 hi7 (by decide) (by decide)]
      exact h_v4_bnd_7
    · -- k=8: touched at step 5.
      rw [h_v8_unc 8 hi8 (by decide) (by decide),
          h_v7_unc 8 hi8 (by decide) (by decide),
          h_v6_unc 8 hi8 (by decide) (by decide)]
      exact h_v5_bnd_8
    · -- k=9: touched at step 6.
      rw [h_v8_unc 9 hi9 (by decide) (by decide),
          h_v7_unc 9 hi9 (by decide) (by decide)]
      exact h_v6_bnd_9
    · -- k=10: touched at step 5.
      rw [h_v8_unc 10 hi10 (by decide) (by decide),
          h_v7_unc 10 hi10 (by decide) (by decide),
          h_v6_unc 10 hi10 (by decide) (by decide)]
      exact h_v5_bnd_10
    · -- k=11: touched at step 6.
      rw [h_v8_unc 11 hi11 (by decide) (by decide),
          h_v7_unc 11 hi11 (by decide) (by decide)]
      exact h_v6_bnd_11
    · -- k=12: touched at step 7.
      rw [h_v8_unc 12 hi12 (by decide) (by decide)]
      exact h_v7_bnd_12
    · -- k=13: touched at step 8.
      exact h_v8_bnd_13
    · -- k=14: touched at step 7.
      rw [h_v8_unc 14 hi14 (by decide) (by decide)]
      exact h_v7_bnd_14
    · -- k=15: touched at step 8.
      exact h_v8_bnd_15

/-- L2.10 — `inv_ntt_layer_2_step`: 8 inverse butterfly pairs (0,4)…(3,7)
    with z0 then (8,12)…(11,15) with z1. Mirror of `ntt_layer_2_step_fc` on the same lane-pair sequence.

    **Precondition adjustment** (beyond locked statement):
    - `hvec : ∀ k < 16, |vec[k]| ≤ 13312` — preserved across 8 sequential
      `inv_ntt_step_pair_fc` invocations on disjoint pairs (post-barrett
      ≤ 3328, post-mont-mul ≤ 4993, untouched lanes preserve input). -/
@[spec]
theorem inv_ntt_layer_2_step_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (z0 z1 : Std.I16)
    (hz : z0.val.natAbs ≤ 1664 ∧ z1.val.natAbs ≤ 1664)
    (hvec : ∀ k : Nat, k < 16 →
      (vec.elements.val[k]!).val.natAbs ≤ 13312) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_2_step vec z0 z1
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_inv_ntt_layer_2_step_pure (lift_chunk vec)
                    (lift_fe_mont z0) (lift_fe_mont z1)
              ∧ (∀ k : Nat, k < 16 →
                  (r.elements.val[k]!).val.natAbs ≤ 3328) ⌝ ⦄ := by
  obtain ⟨hz0, hz1⟩ := hz
  have hi0 : (0 : Nat) < 16 := by decide
  have hi1 : (1 : Nat) < 16 := by decide
  have hi2 : (2 : Nat) < 16 := by decide
  have hi3 : (3 : Nat) < 16 := by decide
  have hi4 : (4 : Nat) < 16 := by decide
  have hi5 : (5 : Nat) < 16 := by decide
  have hi6 : (6 : Nat) < 16 := by decide
  have hi7 : (7 : Nat) < 16 := by decide
  have hi8 : (8 : Nat) < 16 := by decide
  have hi9 : (9 : Nat) < 16 := by decide
  have hi10 : (10 : Nat) < 16 := by decide
  have hi11 : (11 : Nat) < 16 := by decide
  have hi12 : (12 : Nat) < 16 := by decide
  have hi13 : (13 : Nat) < 16 := by decide
  have hi14 : (14 : Nat) < 16 := by decide
  have hi15 : (15 : Nat) < 16 := by decide
  -- Step 1: inv_ntt_step vec z0 0 4.
  obtain ⟨v1, h_v1_eq, h_v1_lift, h_v1_unc, h_v1_bnd_0, h_v1_bnd_4⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc vec z0 0#usize 4#usize hi0 hi4
      (by decide) hz0 (hvec 0 hi0) (hvec 4 hi4))
  -- Step 2: inv_ntt_step v1 z0 1 5.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 13312 := by
    rw [h_v1_unc 1 hi1 (by decide) (by decide)]; exact hvec 1 hi1
  have h_v1_5 : (v1.elements.val[5]!).val.natAbs ≤ 13312 := by
    rw [h_v1_unc 5 hi5 (by decide) (by decide)]; exact hvec 5 hi5
  obtain ⟨v2, h_v2_eq, h_v2_lift, h_v2_unc, h_v2_bnd_1, h_v2_bnd_5⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v1 z0 1#usize 5#usize hi1 hi5
      (by decide) hz0 h_v1_1 h_v1_5)
  -- Step 3: inv_ntt_step v2 z0 2 6.
  have h_v2_2 : (v2.elements.val[2]!).val.natAbs ≤ 13312 := by
    rw [h_v2_unc 2 hi2 (by decide) (by decide),
        h_v1_unc 2 hi2 (by decide) (by decide)]; exact hvec 2 hi2
  have h_v2_6 : (v2.elements.val[6]!).val.natAbs ≤ 13312 := by
    rw [h_v2_unc 6 hi6 (by decide) (by decide),
        h_v1_unc 6 hi6 (by decide) (by decide)]; exact hvec 6 hi6
  obtain ⟨v3, h_v3_eq, h_v3_lift, h_v3_unc, h_v3_bnd_2, h_v3_bnd_6⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v2 z0 2#usize 6#usize hi2 hi6
      (by decide) hz0 h_v2_2 h_v2_6)
  -- Step 4: inv_ntt_step v3 z0 3 7.
  have h_v3_3 : (v3.elements.val[3]!).val.natAbs ≤ 13312 := by
    rw [h_v3_unc 3 hi3 (by decide) (by decide),
        h_v2_unc 3 hi3 (by decide) (by decide),
        h_v1_unc 3 hi3 (by decide) (by decide)]; exact hvec 3 hi3
  have h_v3_7 : (v3.elements.val[7]!).val.natAbs ≤ 13312 := by
    rw [h_v3_unc 7 hi7 (by decide) (by decide),
        h_v2_unc 7 hi7 (by decide) (by decide),
        h_v1_unc 7 hi7 (by decide) (by decide)]; exact hvec 7 hi7
  obtain ⟨v4, h_v4_eq, h_v4_lift, h_v4_unc, h_v4_bnd_3, h_v4_bnd_7⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v3 z0 3#usize 7#usize hi3 hi7
      (by decide) hz0 h_v3_3 h_v3_7)
  -- Step 5: inv_ntt_step v4 z1 8 12.
  have h_v4_8 : (v4.elements.val[8]!).val.natAbs ≤ 13312 := by
    rw [h_v4_unc 8 hi8 (by decide) (by decide),
        h_v3_unc 8 hi8 (by decide) (by decide),
        h_v2_unc 8 hi8 (by decide) (by decide),
        h_v1_unc 8 hi8 (by decide) (by decide)]; exact hvec 8 hi8
  have h_v4_12 : (v4.elements.val[12]!).val.natAbs ≤ 13312 := by
    rw [h_v4_unc 12 hi12 (by decide) (by decide),
        h_v3_unc 12 hi12 (by decide) (by decide),
        h_v2_unc 12 hi12 (by decide) (by decide),
        h_v1_unc 12 hi12 (by decide) (by decide)]; exact hvec 12 hi12
  obtain ⟨v5, h_v5_eq, h_v5_lift, h_v5_unc, h_v5_bnd_8, h_v5_bnd_12⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v4 z1 8#usize 12#usize hi8 hi12
      (by decide) hz1 h_v4_8 h_v4_12)
  -- Step 6: inv_ntt_step v5 z1 9 13.
  have h_v5_9 : (v5.elements.val[9]!).val.natAbs ≤ 13312 := by
    rw [h_v5_unc 9 hi9 (by decide) (by decide),
        h_v4_unc 9 hi9 (by decide) (by decide),
        h_v3_unc 9 hi9 (by decide) (by decide),
        h_v2_unc 9 hi9 (by decide) (by decide),
        h_v1_unc 9 hi9 (by decide) (by decide)]; exact hvec 9 hi9
  have h_v5_13 : (v5.elements.val[13]!).val.natAbs ≤ 13312 := by
    rw [h_v5_unc 13 hi13 (by decide) (by decide),
        h_v4_unc 13 hi13 (by decide) (by decide),
        h_v3_unc 13 hi13 (by decide) (by decide),
        h_v2_unc 13 hi13 (by decide) (by decide),
        h_v1_unc 13 hi13 (by decide) (by decide)]; exact hvec 13 hi13
  obtain ⟨v6, h_v6_eq, h_v6_lift, h_v6_unc, h_v6_bnd_9, h_v6_bnd_13⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v5 z1 9#usize 13#usize hi9 hi13
      (by decide) hz1 h_v5_9 h_v5_13)
  -- Step 7: inv_ntt_step v6 z1 10 14.
  have h_v6_10 : (v6.elements.val[10]!).val.natAbs ≤ 13312 := by
    rw [h_v6_unc 10 hi10 (by decide) (by decide),
        h_v5_unc 10 hi10 (by decide) (by decide),
        h_v4_unc 10 hi10 (by decide) (by decide),
        h_v3_unc 10 hi10 (by decide) (by decide),
        h_v2_unc 10 hi10 (by decide) (by decide),
        h_v1_unc 10 hi10 (by decide) (by decide)]; exact hvec 10 hi10
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 13312 := by
    rw [h_v6_unc 14 hi14 (by decide) (by decide),
        h_v5_unc 14 hi14 (by decide) (by decide),
        h_v4_unc 14 hi14 (by decide) (by decide),
        h_v3_unc 14 hi14 (by decide) (by decide),
        h_v2_unc 14 hi14 (by decide) (by decide),
        h_v1_unc 14 hi14 (by decide) (by decide)]; exact hvec 14 hi14
  obtain ⟨v7, h_v7_eq, h_v7_lift, h_v7_unc, h_v7_bnd_10, h_v7_bnd_14⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v6 z1 10#usize 14#usize hi10 hi14
      (by decide) hz1 h_v6_10 h_v6_14)
  -- Step 8: inv_ntt_step v7 z1 11 15.
  have h_v7_11 : (v7.elements.val[11]!).val.natAbs ≤ 13312 := by
    rw [h_v7_unc 11 hi11 (by decide) (by decide),
        h_v6_unc 11 hi11 (by decide) (by decide),
        h_v5_unc 11 hi11 (by decide) (by decide),
        h_v4_unc 11 hi11 (by decide) (by decide),
        h_v3_unc 11 hi11 (by decide) (by decide),
        h_v2_unc 11 hi11 (by decide) (by decide),
        h_v1_unc 11 hi11 (by decide) (by decide)]; exact hvec 11 hi11
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 13312 := by
    rw [h_v7_unc 15 hi15 (by decide) (by decide),
        h_v6_unc 15 hi15 (by decide) (by decide),
        h_v5_unc 15 hi15 (by decide) (by decide),
        h_v4_unc 15 hi15 (by decide) (by decide),
        h_v3_unc 15 hi15 (by decide) (by decide),
        h_v2_unc 15 hi15 (by decide) (by decide),
        h_v1_unc 15 hi15 (by decide) (by decide)]; exact hvec 15 hi15
  obtain ⟨v8, h_v8_eq, h_v8_lift, h_v8_unc, h_v8_bnd_11, h_v8_bnd_15⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v7 z1 11#usize 15#usize hi11 hi15
      (by decide) hz1 h_v7_11 h_v7_15)
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_2_step vec z0 z1
        = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_2_step
    rw [h_v1_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v2_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v3_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v4_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v5_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v6_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v7_eq]; simp only [Aeneas.Std.bind_tc_ok]
    exact h_v8_eq
  apply triple_of_ok_fc h_body
  refine ⟨?_, ?_⟩
  · -- Spec equation.
    unfold Spec.chunk_inv_ntt_layer_2_step_pure
    rw [h_v8_lift, h_v7_lift, h_v6_lift, h_v5_lift, h_v4_lift, h_v3_lift, h_v2_lift, h_v1_lift]
  · -- Per-lane output bound ≤ 3328.
    -- Step touches: 1:(0,4), 2:(1,5), 3:(2,6), 4:(3,7), 5:(8,12), 6:(9,13),
    -- 7:(10,14), 8:(11,15). All 16 lanes touched exactly once.
    intro k hk
    interval_cases k
    · -- k=0: touched at step 1.
      rw [h_v8_unc 0 hi0 (by decide) (by decide),
          h_v7_unc 0 hi0 (by decide) (by decide),
          h_v6_unc 0 hi0 (by decide) (by decide),
          h_v5_unc 0 hi0 (by decide) (by decide),
          h_v4_unc 0 hi0 (by decide) (by decide),
          h_v3_unc 0 hi0 (by decide) (by decide),
          h_v2_unc 0 hi0 (by decide) (by decide)]
      exact h_v1_bnd_0
    · -- k=1: touched at step 2.
      rw [h_v8_unc 1 hi1 (by decide) (by decide),
          h_v7_unc 1 hi1 (by decide) (by decide),
          h_v6_unc 1 hi1 (by decide) (by decide),
          h_v5_unc 1 hi1 (by decide) (by decide),
          h_v4_unc 1 hi1 (by decide) (by decide),
          h_v3_unc 1 hi1 (by decide) (by decide)]
      exact h_v2_bnd_1
    · -- k=2: touched at step 3.
      rw [h_v8_unc 2 hi2 (by decide) (by decide),
          h_v7_unc 2 hi2 (by decide) (by decide),
          h_v6_unc 2 hi2 (by decide) (by decide),
          h_v5_unc 2 hi2 (by decide) (by decide),
          h_v4_unc 2 hi2 (by decide) (by decide)]
      exact h_v3_bnd_2
    · -- k=3: touched at step 4.
      rw [h_v8_unc 3 hi3 (by decide) (by decide),
          h_v7_unc 3 hi3 (by decide) (by decide),
          h_v6_unc 3 hi3 (by decide) (by decide),
          h_v5_unc 3 hi3 (by decide) (by decide)]
      exact h_v4_bnd_3
    · -- k=4: touched at step 1.
      rw [h_v8_unc 4 hi4 (by decide) (by decide),
          h_v7_unc 4 hi4 (by decide) (by decide),
          h_v6_unc 4 hi4 (by decide) (by decide),
          h_v5_unc 4 hi4 (by decide) (by decide),
          h_v4_unc 4 hi4 (by decide) (by decide),
          h_v3_unc 4 hi4 (by decide) (by decide),
          h_v2_unc 4 hi4 (by decide) (by decide)]
      exact h_v1_bnd_4
    · -- k=5: touched at step 2.
      rw [h_v8_unc 5 hi5 (by decide) (by decide),
          h_v7_unc 5 hi5 (by decide) (by decide),
          h_v6_unc 5 hi5 (by decide) (by decide),
          h_v5_unc 5 hi5 (by decide) (by decide),
          h_v4_unc 5 hi5 (by decide) (by decide),
          h_v3_unc 5 hi5 (by decide) (by decide)]
      exact h_v2_bnd_5
    · -- k=6: touched at step 3.
      rw [h_v8_unc 6 hi6 (by decide) (by decide),
          h_v7_unc 6 hi6 (by decide) (by decide),
          h_v6_unc 6 hi6 (by decide) (by decide),
          h_v5_unc 6 hi6 (by decide) (by decide),
          h_v4_unc 6 hi6 (by decide) (by decide)]
      exact h_v3_bnd_6
    · -- k=7: touched at step 4.
      rw [h_v8_unc 7 hi7 (by decide) (by decide),
          h_v7_unc 7 hi7 (by decide) (by decide),
          h_v6_unc 7 hi7 (by decide) (by decide),
          h_v5_unc 7 hi7 (by decide) (by decide)]
      exact h_v4_bnd_7
    · -- k=8: touched at step 5.
      rw [h_v8_unc 8 hi8 (by decide) (by decide),
          h_v7_unc 8 hi8 (by decide) (by decide),
          h_v6_unc 8 hi8 (by decide) (by decide)]
      exact h_v5_bnd_8
    · -- k=9: touched at step 6.
      rw [h_v8_unc 9 hi9 (by decide) (by decide),
          h_v7_unc 9 hi9 (by decide) (by decide)]
      exact h_v6_bnd_9
    · -- k=10: touched at step 7.
      rw [h_v8_unc 10 hi10 (by decide) (by decide)]
      exact h_v7_bnd_10
    · -- k=11: touched at step 8.
      exact h_v8_bnd_11
    · -- k=12: touched at step 5.
      rw [h_v8_unc 12 hi12 (by decide) (by decide),
          h_v7_unc 12 hi12 (by decide) (by decide),
          h_v6_unc 12 hi12 (by decide) (by decide)]
      exact h_v5_bnd_12
    · -- k=13: touched at step 6.
      rw [h_v8_unc 13 hi13 (by decide) (by decide),
          h_v7_unc 13 hi13 (by decide) (by decide)]
      exact h_v6_bnd_13
    · -- k=14: touched at step 7.
      rw [h_v8_unc 14 hi14 (by decide) (by decide)]
      exact h_v7_bnd_14
    · -- k=15: touched at step 8.
      exact h_v8_bnd_15

/-- L2.11 — `inv_ntt_layer_3_step`: 8 inverse butterfly pairs
    (0,8)…(7,15) with one zeta. Mirror of `ntt_layer_3_step_fc` on the same lane-pair sequence.

    **Precondition adjustment** (beyond locked statement):
    - `hvec : ∀ k < 16, |vec[k]| ≤ 13312` — chained through the 8
      inv_ntt_step calls. Pairs are disjoint (each lane touched exactly
      once), so the per-lane bound holds at each step on the unchanged
      lanes (touched lanes themselves stay ≤ 13312 by inv_ntt_step's
      post-output bounds). -/
@[spec]
theorem inv_ntt_layer_3_step_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (z : Std.I16) (hz : z.val.natAbs ≤ 1664)
    (hvec : ∀ k : Nat, k < 16 →
      (vec.elements.val[k]!).val.natAbs ≤ 13312) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_3_step vec z
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_inv_ntt_layer_3_step_pure (lift_chunk vec) (lift_fe_mont z)
              ∧ (∀ k : Nat, k < 16 →
                  (r.elements.val[k]!).val.natAbs ≤ 3328) ⌝ ⦄ := by
  have hi0 : (0 : Nat) < 16 := by decide
  have hi1 : (1 : Nat) < 16 := by decide
  have hi2 : (2 : Nat) < 16 := by decide
  have hi3 : (3 : Nat) < 16 := by decide
  have hi4 : (4 : Nat) < 16 := by decide
  have hi5 : (5 : Nat) < 16 := by decide
  have hi6 : (6 : Nat) < 16 := by decide
  have hi7 : (7 : Nat) < 16 := by decide
  have hi8 : (8 : Nat) < 16 := by decide
  have hi9 : (9 : Nat) < 16 := by decide
  have hi10 : (10 : Nat) < 16 := by decide
  have hi11 : (11 : Nat) < 16 := by decide
  have hi12 : (12 : Nat) < 16 := by decide
  have hi13 : (13 : Nat) < 16 := by decide
  have hi14 : (14 : Nat) < 16 := by decide
  have hi15 : (15 : Nat) < 16 := by decide
  -- Step 1: inv_ntt_step vec z 0 8.
  obtain ⟨v1, h_v1_eq, h_v1_lift, h_v1_unc, h_v1_bnd_0, h_v1_bnd_8⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc vec z 0#usize 8#usize hi0 hi8
      (by decide) hz (hvec 0 hi0) (hvec 8 hi8))
  -- Step 2: inv_ntt_step v1 z 1 9.
  have h_v1_1 : (v1.elements.val[1]!).val.natAbs ≤ 13312 := by
    rw [h_v1_unc 1 hi1 (by decide) (by decide)]; exact hvec 1 hi1
  have h_v1_9 : (v1.elements.val[9]!).val.natAbs ≤ 13312 := by
    rw [h_v1_unc 9 hi9 (by decide) (by decide)]; exact hvec 9 hi9
  obtain ⟨v2, h_v2_eq, h_v2_lift, h_v2_unc, h_v2_bnd_1, h_v2_bnd_9⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v1 z 1#usize 9#usize hi1 hi9
      (by decide) hz h_v1_1 h_v1_9)
  -- Step 3: inv_ntt_step v2 z 2 10.
  have h_v2_2 : (v2.elements.val[2]!).val.natAbs ≤ 13312 := by
    rw [h_v2_unc 2 hi2 (by decide) (by decide),
        h_v1_unc 2 hi2 (by decide) (by decide)]; exact hvec 2 hi2
  have h_v2_10 : (v2.elements.val[10]!).val.natAbs ≤ 13312 := by
    rw [h_v2_unc 10 hi10 (by decide) (by decide),
        h_v1_unc 10 hi10 (by decide) (by decide)]; exact hvec 10 hi10
  obtain ⟨v3, h_v3_eq, h_v3_lift, h_v3_unc, h_v3_bnd_2, h_v3_bnd_10⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v2 z 2#usize 10#usize hi2 hi10
      (by decide) hz h_v2_2 h_v2_10)
  -- Step 4: inv_ntt_step v3 z 3 11.
  have h_v3_3 : (v3.elements.val[3]!).val.natAbs ≤ 13312 := by
    rw [h_v3_unc 3 hi3 (by decide) (by decide),
        h_v2_unc 3 hi3 (by decide) (by decide),
        h_v1_unc 3 hi3 (by decide) (by decide)]; exact hvec 3 hi3
  have h_v3_11 : (v3.elements.val[11]!).val.natAbs ≤ 13312 := by
    rw [h_v3_unc 11 hi11 (by decide) (by decide),
        h_v2_unc 11 hi11 (by decide) (by decide),
        h_v1_unc 11 hi11 (by decide) (by decide)]; exact hvec 11 hi11
  obtain ⟨v4, h_v4_eq, h_v4_lift, h_v4_unc, h_v4_bnd_3, h_v4_bnd_11⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v3 z 3#usize 11#usize hi3 hi11
      (by decide) hz h_v3_3 h_v3_11)
  -- Step 5: inv_ntt_step v4 z 4 12.
  have h_v4_4 : (v4.elements.val[4]!).val.natAbs ≤ 13312 := by
    rw [h_v4_unc 4 hi4 (by decide) (by decide),
        h_v3_unc 4 hi4 (by decide) (by decide),
        h_v2_unc 4 hi4 (by decide) (by decide),
        h_v1_unc 4 hi4 (by decide) (by decide)]; exact hvec 4 hi4
  have h_v4_12 : (v4.elements.val[12]!).val.natAbs ≤ 13312 := by
    rw [h_v4_unc 12 hi12 (by decide) (by decide),
        h_v3_unc 12 hi12 (by decide) (by decide),
        h_v2_unc 12 hi12 (by decide) (by decide),
        h_v1_unc 12 hi12 (by decide) (by decide)]; exact hvec 12 hi12
  obtain ⟨v5, h_v5_eq, h_v5_lift, h_v5_unc, h_v5_bnd_4, h_v5_bnd_12⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v4 z 4#usize 12#usize hi4 hi12
      (by decide) hz h_v4_4 h_v4_12)
  -- Step 6: inv_ntt_step v5 z 5 13.
  have h_v5_5 : (v5.elements.val[5]!).val.natAbs ≤ 13312 := by
    rw [h_v5_unc 5 hi5 (by decide) (by decide),
        h_v4_unc 5 hi5 (by decide) (by decide),
        h_v3_unc 5 hi5 (by decide) (by decide),
        h_v2_unc 5 hi5 (by decide) (by decide),
        h_v1_unc 5 hi5 (by decide) (by decide)]; exact hvec 5 hi5
  have h_v5_13 : (v5.elements.val[13]!).val.natAbs ≤ 13312 := by
    rw [h_v5_unc 13 hi13 (by decide) (by decide),
        h_v4_unc 13 hi13 (by decide) (by decide),
        h_v3_unc 13 hi13 (by decide) (by decide),
        h_v2_unc 13 hi13 (by decide) (by decide),
        h_v1_unc 13 hi13 (by decide) (by decide)]; exact hvec 13 hi13
  obtain ⟨v6, h_v6_eq, h_v6_lift, h_v6_unc, h_v6_bnd_5, h_v6_bnd_13⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v5 z 5#usize 13#usize hi5 hi13
      (by decide) hz h_v5_5 h_v5_13)
  -- Step 7: inv_ntt_step v6 z 6 14.
  have h_v6_6 : (v6.elements.val[6]!).val.natAbs ≤ 13312 := by
    rw [h_v6_unc 6 hi6 (by decide) (by decide),
        h_v5_unc 6 hi6 (by decide) (by decide),
        h_v4_unc 6 hi6 (by decide) (by decide),
        h_v3_unc 6 hi6 (by decide) (by decide),
        h_v2_unc 6 hi6 (by decide) (by decide),
        h_v1_unc 6 hi6 (by decide) (by decide)]; exact hvec 6 hi6
  have h_v6_14 : (v6.elements.val[14]!).val.natAbs ≤ 13312 := by
    rw [h_v6_unc 14 hi14 (by decide) (by decide),
        h_v5_unc 14 hi14 (by decide) (by decide),
        h_v4_unc 14 hi14 (by decide) (by decide),
        h_v3_unc 14 hi14 (by decide) (by decide),
        h_v2_unc 14 hi14 (by decide) (by decide),
        h_v1_unc 14 hi14 (by decide) (by decide)]; exact hvec 14 hi14
  obtain ⟨v7, h_v7_eq, h_v7_lift, h_v7_unc, h_v7_bnd_6, h_v7_bnd_14⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v6 z 6#usize 14#usize hi6 hi14
      (by decide) hz h_v6_6 h_v6_14)
  -- Step 8: inv_ntt_step v7 z 7 15.
  have h_v7_7 : (v7.elements.val[7]!).val.natAbs ≤ 13312 := by
    rw [h_v7_unc 7 hi7 (by decide) (by decide),
        h_v6_unc 7 hi7 (by decide) (by decide),
        h_v5_unc 7 hi7 (by decide) (by decide),
        h_v4_unc 7 hi7 (by decide) (by decide),
        h_v3_unc 7 hi7 (by decide) (by decide),
        h_v2_unc 7 hi7 (by decide) (by decide),
        h_v1_unc 7 hi7 (by decide) (by decide)]; exact hvec 7 hi7
  have h_v7_15 : (v7.elements.val[15]!).val.natAbs ≤ 13312 := by
    rw [h_v7_unc 15 hi15 (by decide) (by decide),
        h_v6_unc 15 hi15 (by decide) (by decide),
        h_v5_unc 15 hi15 (by decide) (by decide),
        h_v4_unc 15 hi15 (by decide) (by decide),
        h_v3_unc 15 hi15 (by decide) (by decide),
        h_v2_unc 15 hi15 (by decide) (by decide),
        h_v1_unc 15 hi15 (by decide) (by decide)]; exact hvec 15 hi15
  obtain ⟨v8, h_v8_eq, h_v8_lift, h_v8_unc, h_v8_bnd_7, h_v8_bnd_15⟩ :=
    triple_exists_ok_fc (inv_ntt_step_pair_fc v7 z 7#usize 15#usize hi7 hi15
      (by decide) hz h_v7_7 h_v7_15)
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_3_step vec z = .ok v8 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_3_step
    rw [h_v1_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v2_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v3_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v4_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v5_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v6_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_v7_eq]; simp only [Aeneas.Std.bind_tc_ok]
    exact h_v8_eq
  apply triple_of_ok_fc h_body
  refine ⟨?_, ?_⟩
  · -- Spec equation.
    unfold Spec.chunk_inv_ntt_layer_3_step_pure
    rw [h_v8_lift, h_v7_lift, h_v6_lift, h_v5_lift, h_v4_lift, h_v3_lift, h_v2_lift, h_v1_lift]
  · -- Per-lane output bound ≤ 3328.
    -- Step touches: 1:(0,8), 2:(1,9), 3:(2,10), 4:(3,11), 5:(4,12), 6:(5,13),
    -- 7:(6,14), 8:(7,15). All 16 lanes touched exactly once.
    intro k hk
    interval_cases k
    · -- k=0: touched at step 1.
      rw [h_v8_unc 0 hi0 (by decide) (by decide),
          h_v7_unc 0 hi0 (by decide) (by decide),
          h_v6_unc 0 hi0 (by decide) (by decide),
          h_v5_unc 0 hi0 (by decide) (by decide),
          h_v4_unc 0 hi0 (by decide) (by decide),
          h_v3_unc 0 hi0 (by decide) (by decide),
          h_v2_unc 0 hi0 (by decide) (by decide)]
      exact h_v1_bnd_0
    · -- k=1: touched at step 2.
      rw [h_v8_unc 1 hi1 (by decide) (by decide),
          h_v7_unc 1 hi1 (by decide) (by decide),
          h_v6_unc 1 hi1 (by decide) (by decide),
          h_v5_unc 1 hi1 (by decide) (by decide),
          h_v4_unc 1 hi1 (by decide) (by decide),
          h_v3_unc 1 hi1 (by decide) (by decide)]
      exact h_v2_bnd_1
    · -- k=2: touched at step 3.
      rw [h_v8_unc 2 hi2 (by decide) (by decide),
          h_v7_unc 2 hi2 (by decide) (by decide),
          h_v6_unc 2 hi2 (by decide) (by decide),
          h_v5_unc 2 hi2 (by decide) (by decide),
          h_v4_unc 2 hi2 (by decide) (by decide)]
      exact h_v3_bnd_2
    · -- k=3: touched at step 4.
      rw [h_v8_unc 3 hi3 (by decide) (by decide),
          h_v7_unc 3 hi3 (by decide) (by decide),
          h_v6_unc 3 hi3 (by decide) (by decide),
          h_v5_unc 3 hi3 (by decide) (by decide)]
      exact h_v4_bnd_3
    · -- k=4: touched at step 5.
      rw [h_v8_unc 4 hi4 (by decide) (by decide),
          h_v7_unc 4 hi4 (by decide) (by decide),
          h_v6_unc 4 hi4 (by decide) (by decide)]
      exact h_v5_bnd_4
    · -- k=5: touched at step 6.
      rw [h_v8_unc 5 hi5 (by decide) (by decide),
          h_v7_unc 5 hi5 (by decide) (by decide)]
      exact h_v6_bnd_5
    · -- k=6: touched at step 7.
      rw [h_v8_unc 6 hi6 (by decide) (by decide)]
      exact h_v7_bnd_6
    · -- k=7: touched at step 8.
      exact h_v8_bnd_7
    · -- k=8: touched at step 1.
      rw [h_v8_unc 8 hi8 (by decide) (by decide),
          h_v7_unc 8 hi8 (by decide) (by decide),
          h_v6_unc 8 hi8 (by decide) (by decide),
          h_v5_unc 8 hi8 (by decide) (by decide),
          h_v4_unc 8 hi8 (by decide) (by decide),
          h_v3_unc 8 hi8 (by decide) (by decide),
          h_v2_unc 8 hi8 (by decide) (by decide)]
      exact h_v1_bnd_8
    · -- k=9: touched at step 2.
      rw [h_v8_unc 9 hi9 (by decide) (by decide),
          h_v7_unc 9 hi9 (by decide) (by decide),
          h_v6_unc 9 hi9 (by decide) (by decide),
          h_v5_unc 9 hi9 (by decide) (by decide),
          h_v4_unc 9 hi9 (by decide) (by decide),
          h_v3_unc 9 hi9 (by decide) (by decide)]
      exact h_v2_bnd_9
    · -- k=10: touched at step 3.
      rw [h_v8_unc 10 hi10 (by decide) (by decide),
          h_v7_unc 10 hi10 (by decide) (by decide),
          h_v6_unc 10 hi10 (by decide) (by decide),
          h_v5_unc 10 hi10 (by decide) (by decide),
          h_v4_unc 10 hi10 (by decide) (by decide)]
      exact h_v3_bnd_10
    · -- k=11: touched at step 4.
      rw [h_v8_unc 11 hi11 (by decide) (by decide),
          h_v7_unc 11 hi11 (by decide) (by decide),
          h_v6_unc 11 hi11 (by decide) (by decide),
          h_v5_unc 11 hi11 (by decide) (by decide)]
      exact h_v4_bnd_11
    · -- k=12: touched at step 5.
      rw [h_v8_unc 12 hi12 (by decide) (by decide),
          h_v7_unc 12 hi12 (by decide) (by decide),
          h_v6_unc 12 hi12 (by decide) (by decide)]
      exact h_v5_bnd_12
    · -- k=13: touched at step 6.
      rw [h_v8_unc 13 hi13 (by decide) (by decide),
          h_v7_unc 13 hi13 (by decide) (by decide)]
      exact h_v6_bnd_13
    · -- k=14: touched at step 7.
      rw [h_v8_unc 14 hi14 (by decide) (by decide)]
      exact h_v7_bnd_14
    · -- k=15: touched at step 8.
      exact h_v8_bnd_15



/-- Chunk projection identity: `Spec.chunk_at (lift_poly re) k = lift_chunk re.coefs[k]`.

    Pointwise equality at each lane: `lift_fe ((re.coefs[k]).elems[j])` on both sides. -/
theorem chunk_at_lift_poly_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Nat) (hk : k < 16) :
    Spec.chunk_at (lift_poly re) k = lift_chunk (re.coefficients.val[k]!) := by
  unfold Spec.chunk_at lift_poly lift_chunk
  apply Subtype.ext
  have h_chunk_len : (re.coefficients.val[k]!).elements.val.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length _
  -- Both sides .val unfold definitionally to a list; show list equality.
  show (List.range 16).map
        (fun j => ((List.range 256).map
          (fun j' => lift_fe (re.coefficients.val[j' / 16]!).elements.val[j' % 16]!))[16 * k + j]!)
      = (re.coefficients.val[k]!).elements.val.map lift_fe
  apply List.ext_getElem
  · simp
  · intro i hi1 _hi2
    have hi : i < 16 := by
      have : i < ((List.range 16).map _).length := hi1
      simpa using this
    have h_idx_lt : 16 * k + i < 256 := by
      have hk' : k ≤ 15 := by omega
      have : 16 * k ≤ 16 * 15 := Nat.mul_le_mul_left _ hk'
      omega
    have h_list_len : ((List.range 256).map (fun j =>
          lift_fe ((re.coefficients.val[j / 16]!).elements.val[j % 16]!))).length = 256 := by
      simp
    have h_div : (16 * k + i) / 16 = k := by
      have h_i_div : i / 16 = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hi)
      have := Nat.add_mul_div_left i k (by decide : 0 < 16)
      omega
    have h_mod : (16 * k + i) % 16 = i := by
      have := Nat.add_mul_mod_self_left i k 16
      have h_i_mod : i % 16 = i := Nat.mod_eq_of_lt hi
      omega
    -- LHS chain: List.getElem_map (outer), List.getElem_range (outer),
    --            getElem!_pos (big-list lookup), List.getElem_map (big-list),
    --            List.getElem_range (big-list), h_div + h_mod.
    rw [List.getElem_map, List.getElem_range,
        getElem!_pos _ (16 * k + i) (by rw [h_list_len]; exact h_idx_lt),
        List.getElem_map, List.getElem_range, h_div, h_mod]
    -- Goal: lift_fe (val[i]!) = ((val).map lift_fe)[i]'_.
    have h_getElem_pos :
        (re.coefficients.val[k]!).elements.val[i]!
          = (re.coefficients.val[k]!).elements.val[i]'(by rw [h_chunk_len]; exact hi) :=
      getElem!_pos (re.coefficients.val[k]!).elements.val i
        (by rw [h_chunk_len]; exact hi)
    rw [h_getElem_pos]
    -- Goal: lift_fe (val[i]'_) = (val.map lift_fe)[i]'_.
    exact (List.getElem_map (f := lift_fe) (l := (re.coefficients.val[k]!).elements.val)).symm

/-- Flatten-chunks identity (the chunked image of a poly under `lift_poly`).
    Mathematically: if `chunks[k] = lift_chunk re.coefs[k]` for all k < 16,
    then `flatten_chunks chunks = lift_poly re`.

    Uses `getElem` (with proof) rather than `getElem!` in the hypothesis to
    avoid a Lean elaborator issue with `Inhabited (Std.Array FE 16)`
    synthesis in `∀` binders. -/
theorem flatten_chunks_eq_lift_poly_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (chunks : Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
                16#usize)
    (h_chunks_len : chunks.val.length = 16)
    (h_chunks : ∀ k : Nat, (hk : k < 16) →
      chunks.val[k]'(by rw [h_chunks_len]; exact hk)
        = lift_chunk (re.coefficients.val[k]!)) :
    Spec.flatten_chunks chunks = lift_poly re := by
  unfold Spec.flatten_chunks lift_poly
  apply Subtype.ext
  show (List.range 256).map (fun j => (chunks.val[j / 16]!).val[j % 16]!)
       = (List.range 256).map (fun j =>
          lift_fe ((re.coefficients.val[j / 16]!).elements.val[j % 16]!))
  apply List.ext_getElem
  · simp
  · intro j hj1 _hj2
    have hj : j < 256 := by
      have : j < ((List.range 256).map (fun j' => (chunks.val[j' / 16]!).val[j' % 16]!)).length := hj1
      simpa using this
    have h_div_lt : j / 16 < 16 := Nat.div_lt_iff_lt_mul (by decide : 0 < 16) |>.mpr hj
    have h_mod_lt : j % 16 < 16 := Nat.mod_lt _ (by decide : 0 < 16)
    have h_chunk_len : (re.coefficients.val[j / 16]!).elements.val.length = 16 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length _
    have h_map_len : ((re.coefficients.val[j / 16]!).elements.val.map lift_fe).length = 16 := by
      rw [List.length_map]; exact h_chunk_len
    -- Pull `chunks.val[j/16]!` through `h_chunks` using `getElem!_pos`.
    have h_chunks_getElem :
        chunks.val[j / 16]! = lift_chunk (re.coefficients.val[j / 16]!) := by
      rw [getElem!_pos chunks.val (j / 16) (by rw [h_chunks_len]; exact h_div_lt)]
      exact h_chunks (j / 16) h_div_lt
    rw [List.getElem_map, List.getElem_map, List.getElem_range, h_chunks_getElem]
    -- Goal: (lift_chunk re.coefficients[j/16]).val[j % 16]! = lift_fe ((...).val[j % 16]!).
    -- LHS unfolds to ((re.coefs[j/16]).elements.val.map lift_fe)[j % 16]!.
    show ((re.coefficients.val[j / 16]!).elements.val.map lift_fe)[j % 16]!
        = lift_fe ((re.coefficients.val[j / 16]!).elements.val[j % 16]!)
    rw [getElem!_pos ((re.coefficients.val[j / 16]!).elements.val.map lift_fe) (j % 16)
          (by rw [h_map_len]; exact h_mod_lt),
        getElem!_pos (re.coefficients.val[j / 16]!).elements.val (j % 16)
          (by rw [h_chunk_len]; exact h_mod_lt)]
    exact List.getElem_map (f := lift_fe)
      (l := (re.coefficients.val[j / 16]!).elements.val)

end libcrux_iot_ml_kem.Vector.Portable.Ntt
