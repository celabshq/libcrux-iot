/-
  # `Polynomial/InfinityNorm.lean` — polynomial-layer `infinity_norm_exceeds` FC (ML-DSA)

  The security-critical signing rejection check (`polynomial.rs::infinity_norm_exceeds`),
  at the bug-fixed site (commit `cb9df99`). The generic poly-layer fn is a 32-unit
  short-circuiting OR-loop over `self.simd_units`, calling the per-unit
  `inst.infinity_norm_exceeds` (forwarding to `simd.portable.arithmetic.infinity_norm_exceeds`,
  whose per-lane spec `infinity_norm_exceeds_unit_spec` proves `normalized = |coefficient|`
  — the impl-bug-#2 site — and returns `decide (∃ j < 8, bound ≤ |unit.values[j]|)`).

  This FC lives at a DISTINCT altitude from the rest of the layer: it is about RAW
  signed integer coefficient magnitudes (`.val`), NOT the `Z_q` `lift_poly`. The post
  is EQUALITY-form, tied to `Spec.Pure.infinity_norm_exceeds`:

      r = decide (Spec.Pure.infinity_norm_exceeds
                    (fun k => (self.simd_units[k/8]).values[k%8].val) bound.val)

  i.e. `r = true` iff some coefficient's absolute value `≥ bound`. The loop invariant
  carries `result = decide (∃ u < k, ∃ j < 8, bound ≤ |self[u].values[j]|)`; the final
  bridge identifies the `(u, j)` double-existential (u<32, j<8) with the flat
  `∃ i < 256` of the spec via `i = 8·u + j`.

  Per-lane no-overflow precond: `|self[u].values[j]| ≤ 2^30` (consumed by the per-unit FC).
-/
import LibcruxIotMlDsa.Polynomial.Ntt
import LibcruxIotMlDsa.Vector.Portable.Arithmetic
import LibcruxIotMlDsa.Spec.Pure

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_dsa.Polynomial.InfinityNorm
open CoreModels Aeneas Aeneas.Std Std.Do Result ControlFlow
open libcrux_iot_ml_dsa
open libcrux_iot_ml_dsa.Polynomial.Ntt
open libcrux_iot_ml_dsa.Util.LoopHelper

/-! ## Local Triple ↔ Result.ok bridges. -/

private theorem triple_of_ok_in
    {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

private theorem triple_exists_ok_in
    {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl,
      (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

private theorem pure_prop_holds_in {P : Prop} (h : P) : (pure P : Result Prop).holds := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp]; intro _; exact h

private theorem of_pure_prop_holds_in {P : Prop}
    (h : (pure P : Result Prop).holds) : P := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp] at h; exact h trivial

/-! ## Carrier + length bridges. -/

/-- The 32-unit ring-element array. -/
abbrev UnitArr := Std.Array simd.portable.vector_type.Coefficients 32#usize

@[simp]
theorem UnitArr_length (a : UnitArr) : a.length = 32 := by
  have := a.property; show a.val.length = 32; exact this

private theorem units_slice_len_eq (a : UnitArr) :
    Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice a) = (32#usize : Std.Usize) := by
  apply Std.UScalar.eq_of_val_eq
  show (Aeneas.Std.Array.to_slice a).length = (32#usize : Std.Usize).val
  simp [Aeneas.Std.Array.to_slice]

/-! ## The poly Bool-accumulator OR-loop.

The poly loop body (`infinity_norm_exceeds_loop.body` at `portable_ops_inst`) short-circuits
BEFORE indexing: `if result then ok (cont true) else (let t ← a[i]; let r1 ← inst.inf t bound;
ok (cont r1))`. -/

/-- The per-unit predicate at unit `u`: some lane `j < 8` has `bound ≤ |self[u].values[j]|`. -/
private def unit_exceeds (a : UnitArr) (bound : Std.I32) (u : Nat) : Prop :=
  ∃ j : Nat, j < 8 ∧ (bound.val : Int) ≤ |((a.val[u]!).values.val[j]!).val|

instance (a : UnitArr) (bound : Std.I32) (u : Nat) : Decidable (unit_exceeds a bound u) := by
  unfold unit_exceeds; infer_instance

/-- The poly loop body (the `infinity_norm_exceeds_loop.body … portable_ops_inst` shape). -/
def poly_inf_body (a : UnitArr) (bound : Std.I32)
    (iter : CoreModels.core.ops.range.Range Std.Usize) (result : Bool) :
    Result (ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) × Bool) Bool) := do
  let (o, iter1) ←
    CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      CoreModels.core.Usize.Insts.CoreIterRangeStep iter
  match o with
  | CoreModels.core.option.Option.None => ok (ControlFlow.done result)
  | CoreModels.core.option.Option.Some i =>
    if result
    then ok (ControlFlow.cont (iter1, true))
    else
      let t ← Aeneas.Std.Array.index_usize a i
      let result1 ← portable_ops_inst.infinity_norm_exceeds t bound
      ok (ControlFlow.cont (iter1, result1))

/-- The poly loop invariant: `result = decide(∃ u < k, unit_exceeds u)`. -/
def poly_inf_inv (a : UnitArr) (bound : Std.I32) :
    Std.Usize → Bool → Result Prop :=
  fun k result => pure
    (result = decide (∃ u : Nat, u < k.val ∧ unit_exceeds a bound u))

/-- Per-iteration step post for the poly loop. -/
def poly_inf_step_post (a : UnitArr) (bound : Std.I32) (k : Std.Usize)
    (r : ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) × Bool) Bool) : Prop :=
  match r with
  | .cont (iter', result') =>
      k.val < (32#usize : Std.Usize).val ∧ iter'.«end» = 32#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (poly_inf_inv a bound iter'.start result').holds
  | .done y => (poly_inf_inv a bound 32#usize y).holds

/-- Invariant extension at the `Some` step. -/
private theorem poly_inf_extend (a : UnitArr) (bound : Std.I32)
    (k : Nat) (hk : k < 32) (result : Bool)
    (h_res : result = decide (∃ u : Nat, u < k ∧ unit_exceeds a bound u))
    (test : Bool) (h_test : test = decide (unit_exceeds a bound k)) :
    (if result then true else test)
      = decide (∃ u : Nat, u < k + 1 ∧ unit_exceeds a bound u) := by
  rw [h_test, h_res]
  rw [show ∀ (P Q : Prop) [Decidable P] [Decidable Q],
        (if decide P then true else decide Q) = decide (P ∨ Q) from by
        intro P Q _ _; by_cases h : P <;> simp [h]]
  rw [decide_eq_decide]
  constructor
  · rintro (⟨u, hu, hue⟩ | hk')
    · exact ⟨u, by omega, hue⟩
    · exact ⟨k, by omega, hk'⟩
  · rintro ⟨u, hu, hue⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hu with h | h
    · exact Or.inl ⟨u, h, hue⟩
    · subst h; exact Or.inr hue

set_option maxHeartbeats 4000000 in
/-- Per-iteration step lemma for the poly OR-loop. -/
theorem poly_inf_step_lemma
    (a : UnitArr) (bound : Std.I32)
    (hpre : ∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 → (a.val[u]!).values.val[j]!.val.natAbs ≤ 2^30)
    (result : Bool) (k : Std.Usize)
    (h_le : k.val ≤ (32#usize : Std.Usize).val)
    (h_inv : (poly_inf_inv a bound k result).holds) :
    ⦃ ⌜ True ⌝ ⦄
    poly_inf_body a bound { start := k, «end» := 32#usize } result
    ⦃ ⇓ r => ⌜ poly_inf_step_post a bound k r ⌝ ⦄ := by
  have h_32 : (32#usize : Std.Usize).val = 32 := rfl
  have h_a_len : a.length = 32 := UnitArr_length a
  have h_res : result = decide (∃ u : Nat, u < k.val ∧ unit_exceeds a bound u) :=
    of_pure_prop_holds_in h_inv
  unfold poly_inf_body
  by_cases h_lt : k.val < (32#usize : Std.Usize).val
  · -- `Some k` branch.
    have hk_32 : k.val < 32 := by rw [h_32] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k 32#usize h_lt
    set t : simd.portable.vector_type.Coefficients := a.val[k.val]! with ht_def
    have h_idx : Aeneas.Std.Array.index_usize a k = .ok t :=
      array_index_usize_ok_eq a k (by rw [h_a_len]; exact hk_32)
    -- Per-unit FC at chunk k.
    have hpre_k : ∀ j : Nat, j < 8 → (t.values.val[j]!).val.natAbs ≤ 2^30 := by
      intro j hj; rw [ht_def]; exact hpre k.val hk_32 j hj
    obtain ⟨ru, hru_eq, hru_P⟩ :=
      triple_exists_ok_in
        (Vector.Portable.Arithmetic.infinity_norm_exceeds_unit_spec t bound hpre_k)
    -- ru = decide (∃ j < 8, bound ≤ |t.values[j]|) = decide (unit_exceeds a bound k).
    have hru_test : ru = decide (unit_exceeds a bound k.val) := by
      rw [hru_P]
      show decide (∃ j : Nat, j < 8 ∧ (bound.val : Int) ≤ |(t.values.val[j]!).val|)
        = decide (unit_exceeds a bound k.val)
      rw [decide_eq_decide]
      show (∃ j : Nat, j < 8 ∧ (bound.val : Int) ≤ |(t.values.val[j]!).val|) ↔ unit_exceeds a bound k.val
      unfold unit_exceeds; rw [ht_def]
    set new_res : Bool := if result then true else ru with hnr_def
    have h_body :
        (do
          let (o, iter1) ←
            CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              CoreModels.core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 32#usize } : CoreModels.core.ops.range.Range Std.Usize)
          match o with
          | CoreModels.core.option.Option.None =>
              (Result.ok (ControlFlow.done result) :
                Result (ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) × Bool) Bool))
          | CoreModels.core.option.Option.Some i =>
            if result
            then ok (ControlFlow.cont (iter1, true))
            else
              let t ← Aeneas.Std.Array.index_usize a i
              let result1 ← portable_ops_inst.infinity_norm_exceeds t bound
              ok (ControlFlow.cont (iter1, result1)))
        = .ok (ControlFlow.cont
            (({ start := s, «end» := 32#usize }
                : CoreModels.core.ops.range.Range Std.Usize), new_res)) := by
      conv_lhs =>
        rw [show
          (CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              CoreModels.core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 32#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                CoreModels.core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 32#usize } : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [hnr_def]
      by_cases hr : result = true
      · -- result = true: short-circuit to `true`.
        rw [hr]; simp only [if_true]
      · -- result = false: take the `else` branch, reduce the per-unit call.
        simp only [hr, Bool.false_eq_true, if_false]
        rw [h_idx]
        simp only [Aeneas.Std.bind_tc_ok]
        rw [show simd.portable.vector_type.Coefficients.Insts.Libcrux_iot_ml_dsaSimdTraitsOperations.infinity_norm_exceeds t bound
              = simd.portable.arithmetic.infinity_norm_exceeds t bound from rfl, hru_eq]
        simp only [Aeneas.Std.bind_tc_ok]
    apply triple_of_ok_in h_body
    show poly_inf_step_post a bound k
      (.cont (({ start := s, «end» := 32#usize }
                : CoreModels.core.ops.range.Range Std.Usize), new_res))
    unfold poly_inf_step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (poly_inf_inv a bound s new_res).holds
    apply pure_prop_holds_in
    show new_res = decide (∃ u : Nat, u < s.val ∧ unit_exceeds a bound u)
    rw [hs_val, hnr_def]
    exact poly_inf_extend a bound k.val hk_32 result h_res ru hru_test
  · -- `None` branch.
    have hk_ge : k.val ≥ (32#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 32 := by rw [h_32] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k 32#usize hk_ge
    have h_body :
        (do
          let (o, iter1) ←
            CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              CoreModels.core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 32#usize } : CoreModels.core.ops.range.Range Std.Usize)
          match o with
          | CoreModels.core.option.Option.None =>
              (Result.ok (ControlFlow.done result) :
                Result (ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) × Bool) Bool))
          | CoreModels.core.option.Option.Some i =>
            if result
            then ok (ControlFlow.cont (iter1, true))
            else
              let t ← Aeneas.Std.Array.index_usize a i
              let result1 ← portable_ops_inst.infinity_norm_exceeds t bound
              ok (ControlFlow.cont (iter1, result1)))
        = .ok (ControlFlow.done result) := by
      conv_lhs =>
        rw [show
          (CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              CoreModels.core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 32#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                CoreModels.core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 32#usize } : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    apply triple_of_ok_in h_body
    show poly_inf_step_post a bound k (.done result)
    unfold poly_inf_step_post
    show (poly_inf_inv a bound 32#usize result).holds
    apply pure_prop_holds_in
    show result = decide (∃ u : Nat, u < 32 ∧ unit_exceeds a bound u)
    rw [h_res, hk_eq]

/-! ## The bridge: double-existential ↔ the flat `Spec.Pure.infinity_norm_exceeds`. -/

/-- `(∃ u < 32, ∃ j < 8, bound ≤ |self[u].values[j]|) ↔ Spec.Pure.infinity_norm_exceeds`,
    via the bijection `i = 8·u + j` on `[0,256)`. -/
private theorem double_exists_iff_spec
    (self : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (bound : Std.I32) :
    (∃ u : Nat, u < 32 ∧ unit_exceeds self.simd_units bound u)
      ↔ Spec.Pure.infinity_norm_exceeds
          (fun k => ((self.simd_units.val[k / 8]!).values.val[k % 8]!).val) bound.val := by
  unfold Spec.Pure.infinity_norm_exceeds unit_exceeds
  constructor
  · rintro ⟨u, hu, j, hj, hb⟩
    refine ⟨8 * u + j, by omega, ?_⟩
    simp only [show (8 * u + j) / 8 = u from by omega, show (8 * u + j) % 8 = j from by omega]
    exact hb
  · rintro ⟨i, hi, hb⟩
    refine ⟨i / 8, by omega, i % 8, Nat.mod_lt i (by decide), ?_⟩
    simpa only [] using hb

/-! ## Top-level poly FC. -/

set_option maxHeartbeats 2000000 in
/-- **`PolynomialRingElement.infinity_norm_exceeds` at `portable_ops_inst`.** The
    32-unit short-circuiting OR-loop; each unit calls the per-unit
    `infinity_norm_exceeds_unit_spec` (the bug-fixed site). Post is EQUALITY-form, tied
    to `Spec.Pure.infinity_norm_exceeds`: `r = true` iff some coefficient's absolute
    value `≥ bound`. Per-lane no-overflow precond: `|self[u].values[j]| ≤ 2^30`. -/
@[spec]
theorem infinity_norm_exceeds_fc
    (self : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (bound : Std.I32)
    (hpre : ∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
        (self.simd_units.val[u]!).values.val[j]!.val.natAbs ≤ 2^30) :
    ⦃ ⌜ True ⌝ ⦄
    polynomial.PolynomialRingElement.infinity_norm_exceeds portable_ops_inst self bound
    ⦃ ⇓ r => ⌜ r = decide (Spec.Pure.infinity_norm_exceeds
                  (fun k => ((self.simd_units.val[k / 8]!).values.val[k % 8]!).val)
                  bound.val) ⌝ ⦄ := by
  unfold polynomial.PolynomialRingElement.infinity_norm_exceeds
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice self.simd_units)
        = .ok (Aeneas.Std.Array.to_slice self.simd_units) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show CoreModels.core.slice.Slice.len (Aeneas.Std.Array.to_slice self.simd_units)
        = .ok (Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice self.simd_units)) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [units_slice_len_eq self.simd_units]
  unfold polynomial.PolynomialRingElement.infinity_norm_exceeds_loop
  -- Bridge the extracted body to `poly_inf_body`.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × Bool) =>
        polynomial.PolynomialRingElement.infinity_norm_exceeds_loop.body
          portable_ops_inst self.simd_units bound p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × Bool) =>
        poly_inf_body self.simd_units bound p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, result1⟩
    unfold polynomial.PolynomialRingElement.infinity_norm_exceeds_loop.body poly_inf_body
    rfl
  rw [h_body_eq]
  obtain ⟨out, h_out_eq, h_out_holds⟩ :=
    triple_exists_ok_in
      (Util.LoopSpecs.loop_range_spec_usize
        (fun p => poly_inf_body self.simd_units bound p.1 p.2)
        false 0#usize 32#usize
        (poly_inf_inv self.simd_units bound)
        (by decide : (0#usize : Std.Usize).val ≤ (32#usize : Std.Usize).val)
        (by
          apply pure_prop_holds_in
          show (false : Bool)
            = decide (∃ u : Nat, u < 0 ∧ unit_exceeds self.simd_units bound u)
          symm; rw [decide_eq_false_iff_not]; rintro ⟨u, hu, _⟩; exact absurd hu (Nat.not_lt_zero u))
        (by
          intro acc k _h_ge h_le hinv
          have h_step := poly_inf_step_lemma self.simd_units bound hpre acc k h_le hinv
          apply Std.Do.Triple.of_entails_right _ h_step
          rw [PostCond.entails_noThrow]
          intro r hh
          rcases r with ⟨iter', acc'⟩ | y
          · have hP : poly_inf_step_post self.simd_units bound k (.cont (iter', acc')) := by
              simpa [Std.Do.SPred.down_pure] using hh
            simpa [poly_inf_step_post] using hP
          · have hP : poly_inf_step_post self.simd_units bound k (.done y) := by
              simpa [Std.Do.SPred.down_pure] using hh
            simpa [poly_inf_step_post] using hP))
  rw [h_out_eq]
  apply triple_of_ok_in (v := out) rfl
  have h_final : out = decide (∃ u : Nat, u < 32 ∧ unit_exceeds self.simd_units bound u) :=
    of_pure_prop_holds_in h_out_holds
  rw [h_final, decide_eq_decide]
  exact double_exists_iff_spec self bound

end libcrux_iot_ml_dsa.Polynomial.InfinityNorm
