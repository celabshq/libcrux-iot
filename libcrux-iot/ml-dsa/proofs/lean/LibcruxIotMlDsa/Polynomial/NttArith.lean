/-
  # `Polynomial/NttArith.lean` — poly-layer `ntt_multiply_montgomery` / `reduce` FCs (ML-DSA)

  Two more 32-unit poly-loops over `self.simd_units`, applied to the concrete
  portable `Operations Coefficients` instance (`portable_ops_inst`, from
  `Ntt.lean`). Structurally these mirror `Polynomial/Arithmetic.lean`'s
  `add`/`subtract` keystone, but the per-unit posts are **`liftZ_std`-valued**
  (not raw-integer value equations), so we carry a `liftZ_std` invariant:

  * `ntt_multiply_montgomery`: each unit calls `inst.montgomery_multiply lhs[i]
    rhs[i]` (→ `simd.portable.arithmetic.montgomery_multiply`, per-unit
    `montgomery_multiply_spec`). Post per lane: `liftZ_std r[ℓ] = lhs[ℓ]·rhs[ℓ]·RINV`,
    bound `2^24`. The `lift_poly`-level pointwise product reconciles via `RINV²`:
    `lift_poly r[i] = liftZ r.val = liftZ_std r.val · RINV = lhs·rhs·RINV²`, while
    `lift_poly lhs[i] · lift_poly rhs[i] = (lhs·RINV)(rhs·RINV) = lhs·rhs·RINV²`.

  * `reduce`: `ntt.reduce inst re = do let a ← inst.reduce re.simd_units; ok {…}`.
    `inst.reduce` reduces to `…Operations.reduce`, a 32-unit loop calling
    `shift_left_then_reduce 0#i32 c` per unit (per-unit
    `shift_left_then_reduce_spec` at `SHIFT_BY = 0`: `liftZ_std r[ℓ] =
    liftZ_std x[ℓ]·2^0 = liftZ_std x[ℓ]`, bound `6283009`). Hence `liftZ r[ℓ] =
    liftZ x[ℓ]`, so `lift_poly r = lift_poly re` (identity in `Z_q`).
-/
import LibcruxIotMlDsa.Polynomial.Ntt
import LibcruxIotMlDsa.Polynomial.Arithmetic
import LibcruxIotMlDsa.Vector.Portable.Element
import LibcruxIotMlDsa.Vector.Portable.Arithmetic
import LibcruxIotMlDsa.Util.LoopHelper
import LibcruxIotMlDsa.Util.LoopSpecs
import LibcruxIotMlDsa.Spec.Lift
import LibcruxIotMlDsa.Spec.Pure

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_dsa.Polynomial.NttArith
open Aeneas Aeneas.Std Std.Do Result ControlFlow CoreModels
open libcrux_iot_ml_dsa
open libcrux_iot_ml_dsa.Spec
open libcrux_iot_ml_dsa.Spec.Lift libcrux_iot_ml_dsa.Spec.Montgomery
  libcrux_iot_ml_dsa.Spec.Parameters
open libcrux_iot_ml_dsa.Polynomial.Ntt
open libcrux_iot_ml_dsa.Polynomial.Arithmetic
open libcrux_iot_ml_dsa.Util.LoopHelper

/-! ## Local helpers — Triple ↔ Result.ok bridges, pure-prop holds. -/

private theorem triple_of_ok_na
    {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

private theorem triple_exists_ok_na
    {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl,
      (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

private theorem pure_prop_holds_na {P : Prop} (h : P) : (pure P : Result Prop).holds := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp]; intro _; exact h

private theorem of_pure_prop_holds_na {P : Prop}
    (h : (pure P : Result Prop).holds) : P := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp] at h; exact h trivial

/-! ## Length bridge (shared with `Arithmetic.lean`'s `UnitArray`). -/

/-- `Slice.len (Array.to_slice (a : UnitArray)) = 32#usize`. -/
private theorem units_slice_len_eq_na (a : UnitArray) :
    Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice a) = (32#usize : Std.Usize) := by
  apply Std.UScalar.eq_of_val_eq
  show (Aeneas.Std.Array.to_slice a).length = (32#usize : Std.Usize).val
  simp [Aeneas.Std.Array.to_slice]

/-! ## `ntt_multiply_montgomery` — binary mul-loop core.

The loop body matches `ntt_multiply_montgomery_loop.body … portable_ops_inst rhs`
verbatim (binary: read `acc[i]` and `rhs[i]`, write `inst.montgomery_multiply`).
The invariant carries, for each done unit `j < k` and lane `ℓ`, the per-lane
**`liftZ_std` value equation** `liftZ_std acc[j][ℓ] = lhs[j][ℓ]·rhs[j][ℓ]·RINV`
(in `Z_q`) plus the output bound `≤ 2^24`; for undone units `acc[j] = lhs[j]`. -/

section MulCore

/-- The mul loop body, matching the extracted
    `ntt_multiply_montgomery_loop.body … portable_ops_inst rhs`. -/
def mmBody
    (rhs : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (iter : CoreModels.core.ops.range.Range Std.Usize) (a : UnitArray) :
    Result (ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × UnitArray) UnitArray) := do
  let (o, iter1) ←
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep iter
  match o with
  | core.option.Option.None => ok (done a)
  | core.option.Option.Some i =>
    let (t, index_mut_back) ← Array.index_mut_usize a i
    let t1 ← Array.index_usize rhs.simd_units i
    let t2 ← portable_ops_inst.montgomery_multiply t t1
    let a1 := index_mut_back t2
    ok (cont (iter1, a1))

/-- Loop invariant: for done units `j < k`, the per-lane `liftZ_std` mont-product
    equation + the `≤ 2^24` bound; for undone units, `acc[j] = lhs[j]`. -/
def mmInv
    (lhs rhs : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients) :
    Std.Usize → UnitArray → Result Prop :=
  fun k acc => pure (
    (∀ j : Nat, j < k.val →
      (∀ ℓ : Nat, ℓ < 8 →
        liftZ_std ((acc.val[j]!).values.val[ℓ]!).val
          = ((lhs.simd_units.val[j]!).values.val[ℓ]!).val
              * ((rhs.simd_units.val[j]!).values.val[ℓ]!).val * (RINV : Zq)
        ∧ ((acc.val[j]!).values.val[ℓ]!).val.natAbs ≤ 2 ^ 24))
    ∧ (∀ j : Nat, k.val ≤ j → j < 32 →
        acc.val[j]! = lhs.simd_units.val[j]!))

/-- Step post for `loop_range_spec_usize`. -/
def mmStepPost
    (lhs rhs : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × UnitArray) UnitArray) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (32#usize : Std.Usize).val ∧ iter'.«end» = 32#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (mmInv lhs rhs iter'.start acc').holds
  | .done y => (mmInv lhs rhs 32#usize y).holds

set_option maxHeartbeats 4000000 in
/-- Per-iteration step lemma: applies `montgomery_multiply_spec` to chunk `k`. -/
theorem mmStep
    (lhs rhs : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (hpre : ∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
      (rhs.simd_units.val[u]!).values.val[j]!.val.natAbs ≤ 8380416)
    (acc : UnitArray)
    (k : Std.Usize) (h_le : k.val ≤ (32#usize : Std.Usize).val)
    (h_inv : (mmInv lhs rhs k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    mmBody rhs { start := k, «end» := 32#usize } acc
    ⦃ ⇓ r => ⌜ mmStepPost lhs rhs k r ⌝ ⦄ := by
  have h32 : (32#usize : Std.Usize).val = 32 := rfl
  have h_acc_len : acc.length = 32 := UnitArray_length acc
  have h_rhs_len : rhs.simd_units.length = 32 := UnitArray_length rhs.simd_units
  obtain ⟨h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_na h_inv
  unfold mmBody
  by_cases h_lt : k.val < (32#usize : Std.Usize).val
  · -- `Some i = k` branch.
    have hk_32 : k.val < 32 := by rw [h32] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k 32#usize h_lt
    set t : simd.portable.vector_type.Coefficients := acc.val[k.val]! with ht_def
    have h_idx_t : Aeneas.Std.Array.index_usize acc k = .ok t :=
      array_index_usize_ok_eq acc k (by rw [h_acc_len]; exact hk_32)
    have h_imt_t : Aeneas.Std.Array.index_mut_usize acc k = .ok (t, acc.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_t]; rfl
    have h_t_eq : t = lhs.simd_units.val[k.val]! := by
      show acc.val[k.val]! = lhs.simd_units.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_32
    set t1 : simd.portable.vector_type.Coefficients := rhs.simd_units.val[k.val]! with ht1_def
    have h_idx_t1 : Aeneas.Std.Array.index_usize rhs.simd_units k = .ok t1 :=
      array_index_usize_ok_eq rhs.simd_units k (by rw [h_rhs_len]; exact hk_32)
    -- per-unit precondition: rhs lanes ≤ q-1.
    have h_t1_pre : ∀ j : Nat, j < 8 → (t1.values.val[j]!).val.natAbs ≤ 8380416 := by
      intro j hj; rw [ht1_def]; exact hpre k.val hk_32 j hj
    obtain ⟨t2, h_t2_eq, h_t2_P⟩ :=
      triple_exists_ok_na
        (Vector.Portable.Element.montgomery_multiply_spec t t1 h_t1_pre)
    -- Compose the whole body into one `.ok` equation.
    have h_body :
        (do
          let (o, iter1) ←
            core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 32#usize } : CoreModels.core.ops.range.Range Std.Usize)
          match o with
          | core.option.Option.None =>
              (Result.ok (ControlFlow.done acc) :
                Result (ControlFlow
                  ((CoreModels.core.ops.range.Range Std.Usize) × UnitArray) UnitArray))
          | core.option.Option.Some i =>
            let (t', index_mut_back) ← Array.index_mut_usize acc i
            let t1' ← Array.index_usize rhs.simd_units i
            let t2' ← portable_ops_inst.montgomery_multiply t' t1'
            let a1 := index_mut_back t2'
            ok (cont (iter1, a1)))
        = .ok (cont (({ start := s, «end» := 32#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                     acc.set k t2)) := by
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 32#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 32#usize }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_t]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_t1]; simp only [Aeneas.Std.bind_tc_ok]
      -- the instance method is the wrapper `do simd.portable.arithmetic.montgomery_multiply …`,
      -- definitionally equal to the bare arithmetic call the per-unit spec speaks.
      rw [show
        simd.portable.vector_type.Coefficients.Insts.Libcrux_iot_ml_dsaSimdTraitsOperations.montgomery_multiply
          t t1 = simd.portable.arithmetic.montgomery_multiply t t1 from rfl]
      rw [h_t2_eq]
      rfl
    apply triple_of_ok_na h_body
    show mmStepPost lhs rhs k
      (.cont (({ start := s, «end» := 32#usize }
                : CoreModels.core.ops.range.Range Std.Usize), acc.set k t2))
    unfold mmStepPost
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (mmInv lhs rhs s (acc.set k t2)).holds
    apply pure_prop_holds_na
    refine ⟨?_, ?_⟩
    · -- Done units `j < s.val`.
      intro j hj
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_set_ne : (acc.set k t2).val[j]! = acc.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne acc k j t2 h_ne
        intro ℓ hℓ
        rw [h_set_ne]
        exact h_acc_done j hj_lt_k ℓ hℓ
      · subst hj_eq_k
        have h_set_eq : (acc.set k t2).val[k.val]! = t2 := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_eq acc k k.val t2
              ⟨rfl, by rw [h_acc_len]; exact hk_32⟩
        intro ℓ hℓ
        rw [h_set_eq]
        obtain ⟨h_val, h_bd⟩ := h_t2_P ℓ hℓ
        refine ⟨?_, h_bd⟩
        rw [h_val, h_t_eq, ht1_def]
    · -- Undone units `j ≥ s.val`.
      intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_ne : k.val ≠ j := by omega
      have h_ge' : k.val ≤ j := by omega
      have h_set_ne : (acc.set k t2).val[j]! = acc.val[j]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
          Aeneas.Std.Array.getElem!_Nat_set_ne acc k j t2 h_ne
      rw [h_set_ne]
      exact h_acc_undone j h_ge' hj_lt
  · -- `None` branch: k ≥ 32, done.
    have hk_ge : k.val ≥ (32#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 32 := by rw [h32] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k 32#usize hk_ge
    have h_body :
        (do
          let (o, iter1) ←
            core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 32#usize } : CoreModels.core.ops.range.Range Std.Usize)
          match o with
          | core.option.Option.None =>
              (Result.ok (ControlFlow.done acc) :
                Result (ControlFlow
                  ((CoreModels.core.ops.range.Range Std.Usize) × UnitArray) UnitArray))
          | core.option.Option.Some i =>
            let (t', index_mut_back) ← Array.index_mut_usize acc i
            let t1' ← Array.index_usize rhs.simd_units i
            let t2' ← portable_ops_inst.montgomery_multiply t' t1'
            let a1 := index_mut_back t2'
            ok (cont (iter1, a1)))
        = .ok (done acc) := by
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 32#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 32#usize }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    apply triple_of_ok_na h_body
    show mmStepPost lhs rhs k (.done acc)
    unfold mmStepPost
    show (mmInv lhs rhs 32#usize acc).holds
    apply pure_prop_holds_na
    refine ⟨?_, ?_⟩
    · intro j hj; rw [h32] at hj
      apply h_acc_done j; rw [hk_eq]; exact hj
    · intro j hj_ge hj_lt; rw [h32] at hj_ge
      apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge

end MulCore

/-! ## Mul lift bridge: invariant at `k=32` ⟹ the `poly_pointwise_mul` equality.

The done-half at `k=32` gives, for every unit `j` and lane `ℓ`, the `Z_q`
equation `liftZ_std out[j][ℓ] = lhs[j][ℓ]·rhs[j][ℓ]·RINV`. We turn this into
`lift_poly {simd_units := out} = build (fun i => (lift_poly lhs)[i]·(lift_poly
rhs)[i])` via the RINV²-reconciliation: `liftZ x = liftZ_std x · RINV`, so
`liftZ out = lhs·rhs·RINV² = (lhs·RINV)(rhs·RINV) = liftZ lhs · liftZ rhs`. -/

private theorem mm_lift_bridge
    (lhs rhs : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (out : UnitArray)
    (h_done : ∀ j : Nat, j < 32 → ∀ ℓ : Nat, ℓ < 8 →
        liftZ_std ((out.val[j]!).values.val[ℓ]!).val
          = ((lhs.simd_units.val[j]!).values.val[ℓ]!).val
              * ((rhs.simd_units.val[j]!).values.val[ℓ]!).val * (RINV : Zq)) :
    lift_poly ({ simd_units := out } :
        polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
      = Pure.poly_pointwise_mul (lift_poly lhs) (lift_poly rhs) := by
  rw [lift_poly_eq_lift_units]
  unfold lift_units Pure.poly_pointwise_mul
  apply Pure.build_congr
  intro i hi
  have hdiv : i / 8 < 32 := by omega
  have hmod : i % 8 < 8 := Nat.mod_lt i (by decide)
  show liftZ ((out.val[i / 8]!).values.val[i % 8]!).val = _
  -- The per-lane mont post (`liftZ_std out = lhs·rhs·RINV`, i.e. `(out:Zq) =
  -- (lhs:Zq)·(rhs:Zq)·RINV`) is exactly the `liftZ_of_mont` hypothesis, which
  -- strips one more `R` from each side: `liftZ out = liftZ lhs · liftZ rhs`.
  have h_mont : (((out.val[i / 8]!).values.val[i % 8]!).val : Zq)
      = (((lhs.simd_units.val[i / 8]!).values.val[i % 8]!).val : Zq)
          * (((rhs.simd_units.val[i / 8]!).values.val[i % 8]!).val : Zq) * (RINV : Zq) := by
    have := h_done (i / 8) hdiv (i % 8) hmod
    unfold liftZ_std at this
    exact this
  rw [liftZ_of_mont _ _ _ h_mont]
  -- RHS: identify `(lift_poly lhs)[i]` / `(lift_poly rhs)[i]` with their lanes.
  congr 1
  · rw [lift_poly_eq_lift_units]; unfold lift_units; rw [Pure.build_getElem _ i hi]
  · rw [lift_poly_eq_lift_units]; unfold lift_units; rw [Pure.build_getElem _ i hi]

set_option maxHeartbeats 8000000 in
/-- **`ntt.ntt_multiply_montgomery` at `portable_ops_inst`.** 32-unit loop; each
    unit calls `inst.montgomery_multiply lhs[i] rhs[i]`. Functional post is
    EQUALITY-form via `lift_poly` = `Pure.poly_pointwise_mul`. -/
@[spec]
theorem ntt_multiply_montgomery_fc
    (lhs rhs : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (hpre : ∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
      (rhs.simd_units.val[u]!).values.val[j]!.val.natAbs ≤ 8380416) :
    ⦃ ⌜ True ⌝ ⦄
    ntt.ntt_multiply_montgomery portable_ops_inst lhs rhs
    ⦃ ⇓ r => ⌜ lift_poly r = Pure.poly_pointwise_mul (lift_poly lhs) (lift_poly rhs)
             ∧ (∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
                  (r.simd_units.val[u]!).values.val[j]!.val.natAbs ≤ 2 ^ 24) ⌝ ⦄ := by
  unfold ntt.ntt_multiply_montgomery
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice lhs.simd_units)
        = .ok (Aeneas.Std.Array.to_slice lhs.simd_units) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show CoreModels.core.slice.Slice.len (Aeneas.Std.Array.to_slice lhs.simd_units)
        = .ok (Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice lhs.simd_units)) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [units_slice_len_eq_na lhs.simd_units]
  unfold ntt.ntt_multiply_montgomery_loop
  -- Bridge the extracted body to the generic `mmBody`.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × UnitArray) =>
        ntt.ntt_multiply_montgomery_loop.body portable_ops_inst rhs p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × UnitArray) =>
        mmBody rhs p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, a1⟩
    unfold ntt.ntt_multiply_montgomery_loop.body mmBody
    rfl
  rw [h_body_eq]
  obtain ⟨out, h_out_eq, h_out_holds⟩ :=
    triple_exists_ok_na
      (Util.LoopSpecs.loop_range_spec_usize
        (fun p => mmBody rhs p.1 p.2)
        lhs.simd_units 0#usize 32#usize
        (mmInv lhs rhs)
        (by decide : (0#usize : Std.Usize).val ≤ (32#usize : Std.Usize).val)
        (by
          apply pure_prop_holds_na
          refine ⟨fun j hj => absurd hj (Nat.not_lt_zero j), fun _ _ _ => rfl⟩)
        (by
          intro acc k _h_ge h_le hinv
          have h_step := mmStep lhs rhs hpre acc k h_le hinv
          apply Std.Do.Triple.of_entails_right _ h_step
          rw [PostCond.entails_noThrow]
          intro r hh
          rcases r with ⟨iter', acc'⟩ | y
          · have hP : mmStepPost lhs rhs k (.cont (iter', acc')) := by
              simpa [Std.Do.SPred.down_pure] using hh
            simpa [mmStepPost] using hP
          · have hP : mmStepPost lhs rhs k (.done y) := by
              simpa [Std.Do.SPred.down_pure] using hh
            simpa [mmStepPost] using hP))
  rw [h_out_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  obtain ⟨h_done, _h_undone⟩ := of_pure_prop_holds_na h_out_holds
  refine triple_of_ok_na (v := { simd_units := out }) rfl ?_
  refine ⟨?_, ?_⟩
  · -- Equality conjunct via the mul lift bridge.
    have h_bridge := mm_lift_bridge lhs rhs out
      (fun j hj ℓ hℓ =>
        (h_done j (by rw [show (32#usize : Std.Usize).val = 32 from rfl]; exact hj) ℓ hℓ).1)
    show lift_poly ({ simd_units := out } :
        polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients) = _
    exact h_bridge
  · -- Bound conjunct.
    intro u hu j hj
    show (out.val[u]!).values.val[j]!.val.natAbs ≤ _
    exact (h_done u (by rw [show (32#usize : Std.Usize).val = 32 from rfl]; exact hu) j hj).2

/-! ## `reduce` — unary 32-unit reduce-loop core.

`ntt.reduce inst re = do let a ← inst.reduce re.simd_units; ok {simd_units := a}`,
where `inst.reduce` reduces to `…Operations.reduce`, a 32-unit loop calling
`shift_left_then_reduce 0#i32 c` per unit. We first prove an FC for the
instance method `…Operations.reduce` as a unary 32-unit loop, then wrap it.

At `SHIFT_BY = 0#i32`, the per-unit `shift_left_then_reduce_spec` gives
`liftZ_std r[ℓ] = liftZ_std x[ℓ] · 2^0 = liftZ_std x[ℓ]`, bound `6283009`. The
invariant carries, for done units `j < k`, `liftZ_std acc[j][ℓ] =
liftZ_std re[j][ℓ]` + the bound; undone units `acc[j] = re[j]`. -/

section RedCore

/-- The reduce loop body, matching the extracted
    `…Operations.reduce_loop.body` (unary: read `acc[i]`, write
    `shift_left_then_reduce 0#i32 c`). -/
def redBody
    (iter : CoreModels.core.ops.range.Range Std.Usize) (a : UnitArray) :
    Result (ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × UnitArray) UnitArray) := do
  let (o, iter1) ←
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep iter
  match o with
  | core.option.Option.None => ok (done a)
  | core.option.Option.Some i =>
    let (c, index_mut_back) ← Array.index_mut_usize a i
    let c1 ←
      simd.portable.vector_type.Coefficients.Insts.Libcrux_iot_ml_dsaSimdTraitsOperations.shift_left_then_reduce
        0#i32 c
    let a1 := index_mut_back c1
    ok (cont (iter1, a1))

/-- Loop invariant: for done units `j < k`, the per-lane `liftZ_std` identity
    equation + the `≤ 6283009` bound; for undone units, `acc[j] = re[j]`. -/
def redInv
    (re : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients) :
    Std.Usize → UnitArray → Result Prop :=
  fun k acc => pure (
    (∀ j : Nat, j < k.val →
      (∀ ℓ : Nat, ℓ < 8 →
        liftZ_std ((acc.val[j]!).values.val[ℓ]!).val
          = liftZ_std ((re.simd_units.val[j]!).values.val[ℓ]!).val
        ∧ ((acc.val[j]!).values.val[ℓ]!).val.natAbs ≤ 6283009))
    ∧ (∀ j : Nat, k.val ≤ j → j < 32 →
        acc.val[j]! = re.simd_units.val[j]!))

/-- Step post for `loop_range_spec_usize`. -/
def redStepPost
    (re : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × UnitArray) UnitArray) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (32#usize : Std.Usize).val ∧ iter'.«end» = 32#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (redInv re iter'.start acc').holds
  | .done y => (redInv re 32#usize y).holds

set_option maxHeartbeats 4000000 in
/-- Per-iteration step lemma: applies `shift_left_then_reduce_spec` at
    `SHIFT_BY = 0#i32` to chunk `k`. -/
theorem redStep
    (re : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (hpre : ∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
      (re.simd_units.val[u]!).values.val[j]!.val.natAbs ≤ 2 ^ 31 - 2 ^ 23)
    (acc : UnitArray)
    (k : Std.Usize) (h_le : k.val ≤ (32#usize : Std.Usize).val)
    (h_inv : (redInv re k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    redBody { start := k, «end» := 32#usize } acc
    ⦃ ⇓ r => ⌜ redStepPost re k r ⌝ ⦄ := by
  have h32 : (32#usize : Std.Usize).val = 32 := rfl
  have h_acc_len : acc.length = 32 := UnitArray_length acc
  obtain ⟨h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_na h_inv
  unfold redBody
  by_cases h_lt : k.val < (32#usize : Std.Usize).val
  · -- `Some i = k` branch.
    have hk_32 : k.val < 32 := by rw [h32] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k 32#usize h_lt
    set c : simd.portable.vector_type.Coefficients := acc.val[k.val]! with hc_def
    have h_idx_c : Aeneas.Std.Array.index_usize acc k = .ok c :=
      array_index_usize_ok_eq acc k (by rw [h_acc_len]; exact hk_32)
    have h_imt_c : Aeneas.Std.Array.index_mut_usize acc k = .ok (c, acc.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_c]; rfl
    have h_c_eq : c = re.simd_units.val[k.val]! := by
      show acc.val[k.val]! = re.simd_units.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_32
    -- per-unit `shift_left_then_reduce_spec` at SHIFT_BY = 0.
    have h_shift : (0 : Int) ≤ (0#i32 : Std.I32).val ∧ (0#i32 : Std.I32).val < 32 := by
      refine ⟨by decide, by decide⟩
    have h_c_bound : ∀ j, j < 8 →
        (c.values.val[j]!).val.natAbs * 2 ^ (0#i32 : Std.I32).toNat ≤ 2 ^ 31 - 2 ^ 23 := by
      intro j hj
      rw [show (0#i32 : Std.I32).toNat = 0 from rfl, pow_zero, Nat.mul_one, h_c_eq]
      exact hpre k.val hk_32 j hj
    obtain ⟨c1, h_c1_eq, h_c1_P⟩ :=
      triple_exists_ok_na
        (Vector.Portable.Arithmetic.shift_left_then_reduce_spec 0#i32 c h_shift h_c_bound)
    have h_body :
        (do
          let (o, iter1) ←
            core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 32#usize } : CoreModels.core.ops.range.Range Std.Usize)
          match o with
          | core.option.Option.None =>
              (Result.ok (ControlFlow.done acc) :
                Result (ControlFlow
                  ((CoreModels.core.ops.range.Range Std.Usize) × UnitArray) UnitArray))
          | core.option.Option.Some i =>
            let (c', index_mut_back) ← Array.index_mut_usize acc i
            let c1' ←
              simd.portable.vector_type.Coefficients.Insts.Libcrux_iot_ml_dsaSimdTraitsOperations.shift_left_then_reduce
                0#i32 c'
            let a1 := index_mut_back c1'
            ok (cont (iter1, a1)))
        = .ok (cont (({ start := s, «end» := 32#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                     acc.set k c1)) := by
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 32#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 32#usize }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_c]; simp only [Aeneas.Std.bind_tc_ok]
      -- the instance method is the wrapper `do shift_left_then_reduce …`.
      rw [show
        simd.portable.vector_type.Coefficients.Insts.Libcrux_iot_ml_dsaSimdTraitsOperations.shift_left_then_reduce
          0#i32 c = simd.portable.arithmetic.shift_left_then_reduce 0#i32 c from rfl]
      rw [h_c1_eq]
      rfl
    apply triple_of_ok_na h_body
    show redStepPost re k
      (.cont (({ start := s, «end» := 32#usize }
                : CoreModels.core.ops.range.Range Std.Usize), acc.set k c1))
    unfold redStepPost
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (redInv re s (acc.set k c1)).holds
    apply pure_prop_holds_na
    refine ⟨?_, ?_⟩
    · -- Done units `j < s.val`.
      intro j hj
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_set_ne : (acc.set k c1).val[j]! = acc.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne acc k j c1 h_ne
        intro ℓ hℓ
        rw [h_set_ne]
        exact h_acc_done j hj_lt_k ℓ hℓ
      · subst hj_eq_k
        have h_set_eq : (acc.set k c1).val[k.val]! = c1 := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_eq acc k k.val c1
              ⟨rfl, by rw [h_acc_len]; exact hk_32⟩
        intro ℓ hℓ
        rw [h_set_eq]
        obtain ⟨h_val, h_bd⟩ := h_c1_P ℓ hℓ
        refine ⟨?_, h_bd⟩
        -- `liftZ_std c1[ℓ] = liftZ_std c[ℓ] · 2^0 = liftZ_std c[ℓ] = liftZ_std re[k][ℓ]`.
        have h_toNat0 : (2 : Zq) ^ Std.I32.toNat 0#i32 = 1 := by
          rw [show Std.I32.toNat 0#i32 = 0 from rfl, pow_zero]
        rw [h_val, h_toNat0, mul_one, h_c_eq]
    · -- Undone units `j ≥ s.val`.
      intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_ne : k.val ≠ j := by omega
      have h_ge' : k.val ≤ j := by omega
      have h_set_ne : (acc.set k c1).val[j]! = acc.val[j]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
          Aeneas.Std.Array.getElem!_Nat_set_ne acc k j c1 h_ne
      rw [h_set_ne]
      exact h_acc_undone j h_ge' hj_lt
  · -- `None` branch: k ≥ 32, done.
    have hk_ge : k.val ≥ (32#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 32 := by rw [h32] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k 32#usize hk_ge
    have h_body :
        (do
          let (o, iter1) ←
            core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 32#usize } : CoreModels.core.ops.range.Range Std.Usize)
          match o with
          | core.option.Option.None =>
              (Result.ok (ControlFlow.done acc) :
                Result (ControlFlow
                  ((CoreModels.core.ops.range.Range Std.Usize) × UnitArray) UnitArray))
          | core.option.Option.Some i =>
            let (c', index_mut_back) ← Array.index_mut_usize acc i
            let c1' ←
              simd.portable.vector_type.Coefficients.Insts.Libcrux_iot_ml_dsaSimdTraitsOperations.shift_left_then_reduce
                0#i32 c'
            let a1 := index_mut_back c1'
            ok (cont (iter1, a1)))
        = .ok (done acc) := by
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 32#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 32#usize }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    apply triple_of_ok_na h_body
    show redStepPost re k (.done acc)
    unfold redStepPost
    show (redInv re 32#usize acc).holds
    apply pure_prop_holds_na
    refine ⟨?_, ?_⟩
    · intro j hj; rw [h32] at hj
      apply h_acc_done j; rw [hk_eq]; exact hj
    · intro j hj_ge hj_lt; rw [h32] at hj_ge
      apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge

end RedCore

/-! ## Reduce lift bridge + instance-method FC, then the `ntt.reduce` wrapper. -/

set_option maxHeartbeats 8000000 in
/-- `…Operations.reduce` as a 32-unit reduce-loop: `liftZ_std`-identity post +
    output bound. The functional half says lane residues are unchanged in `Z_q`. -/
private theorem operations_reduce_fc
    (re : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (hpre : ∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
      (re.simd_units.val[u]!).values.val[j]!.val.natAbs ≤ 2 ^ 31 - 2 ^ 23) :
    ∃ out : UnitArray,
      simd.portable.vector_type.Coefficients.Insts.Libcrux_iot_ml_dsaSimdTraitsOperations.reduce
          re.simd_units = .ok out
      ∧ (∀ j : Nat, j < 32 → ∀ ℓ : Nat, ℓ < 8 →
          liftZ_std ((out.val[j]!).values.val[ℓ]!).val
            = liftZ_std ((re.simd_units.val[j]!).values.val[ℓ]!).val)
      ∧ (∀ j : Nat, j < 32 → ∀ ℓ : Nat, ℓ < 8 →
          ((out.val[j]!).values.val[ℓ]!).val.natAbs ≤ 6283009) := by
  apply triple_exists_ok_na
  unfold simd.portable.vector_type.Coefficients.Insts.Libcrux_iot_ml_dsaSimdTraitsOperations.reduce
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice re.simd_units)
        = .ok (Aeneas.Std.Array.to_slice re.simd_units) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show CoreModels.core.slice.Slice.len (Aeneas.Std.Array.to_slice re.simd_units)
        = .ok (Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice re.simd_units)) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [units_slice_len_eq_na re.simd_units]
  unfold simd.portable.vector_type.Coefficients.Insts.Libcrux_iot_ml_dsaSimdTraitsOperations.reduce_loop
  -- Bridge the extracted body to the generic `redBody`.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × UnitArray) =>
        simd.portable.vector_type.Coefficients.Insts.Libcrux_iot_ml_dsaSimdTraitsOperations.reduce_loop.body
          p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × UnitArray) =>
        redBody p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, a1⟩
    unfold simd.portable.vector_type.Coefficients.Insts.Libcrux_iot_ml_dsaSimdTraitsOperations.reduce_loop.body
      redBody
    rfl
  rw [h_body_eq]
  obtain ⟨out, h_out_eq, h_out_holds⟩ :=
    triple_exists_ok_na
      (Util.LoopSpecs.loop_range_spec_usize
        (fun p => redBody p.1 p.2)
        re.simd_units 0#usize 32#usize
        (redInv re)
        (by decide : (0#usize : Std.Usize).val ≤ (32#usize : Std.Usize).val)
        (by
          apply pure_prop_holds_na
          refine ⟨fun j hj => absurd hj (Nat.not_lt_zero j), fun _ _ _ => rfl⟩)
        (by
          intro acc k _h_ge h_le hinv
          have h_step := redStep re hpre acc k h_le hinv
          apply Std.Do.Triple.of_entails_right _ h_step
          rw [PostCond.entails_noThrow]
          intro r hh
          rcases r with ⟨iter', acc'⟩ | y
          · have hP : redStepPost re k (.cont (iter', acc')) := by
              simpa [Std.Do.SPred.down_pure] using hh
            simpa [redStepPost] using hP
          · have hP : redStepPost re k (.done y) := by
              simpa [Std.Do.SPred.down_pure] using hh
            simpa [redStepPost] using hP))
  rw [h_out_eq]
  apply triple_of_ok_na (v := out) rfl
  obtain ⟨h_done, _h_undone⟩ := of_pure_prop_holds_na h_out_holds
  refine ⟨?_, ?_⟩
  · intro j hj ℓ hℓ
    exact (h_done j (by rw [show (32#usize : Std.Usize).val = 32 from rfl]; exact hj) ℓ hℓ).1
  · intro j hj ℓ hℓ
    exact (h_done j (by rw [show (32#usize : Std.Usize).val = 32 from rfl]; exact hj) ℓ hℓ).2

set_option maxHeartbeats 8000000 in
/-- **`ntt.reduce` at `portable_ops_inst`.** Trivial wrapper around
    `…Operations.reduce` (corollary idiom). Each lane's residue is unchanged in
    `Z_q` (`lift_poly r = lift_poly re`); the output is barrett-reduced. -/
@[spec]
theorem reduce_fc
    (re : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (hpre : ∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
      (re.simd_units.val[u]!).values.val[j]!.val.natAbs ≤ 2 ^ 31 - 2 ^ 23) :
    ⦃ ⌜ True ⌝ ⦄
    ntt.reduce portable_ops_inst re
    ⦃ ⇓ r => ⌜ lift_poly r = lift_poly re
             ∧ (∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
                  (r.simd_units.val[u]!).values.val[j]!.val.natAbs ≤ 6283009) ⌝ ⦄ := by
  obtain ⟨out, h_out_eq, h_lift, h_bd⟩ := operations_reduce_fc re hpre
  apply triple_of_ok_na (v := { simd_units := out })
  · show (do
          let a ←
            simd.portable.vector_type.Coefficients.Insts.Libcrux_iot_ml_dsaSimdTraitsOperations.reduce
              re.simd_units
          ok ({ simd_units := a } :
            polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients))
        = ok ({ simd_units := out } :
            polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    rw [h_out_eq]; rfl
  · refine ⟨?_, ?_⟩
    · -- Equality conjunct: `lift_poly out = lift_poly re` lane-by-lane.
      rw [lift_poly_eq_lift_units, lift_poly_eq_lift_units]
      unfold lift_units
      apply Pure.build_congr
      intro i hi
      have hdiv : i / 8 < 32 := by omega
      have hmod : i % 8 < 8 := Nat.mod_lt i (by decide)
      show liftZ ((out.val[i / 8]!).values.val[i % 8]!).val
            = liftZ ((re.simd_units.val[i / 8]!).values.val[i % 8]!).val
      -- `liftZ x = liftZ_std x · RINV`; the `liftZ_std` residues agree.
      have h_liftZ_def : ∀ x : Int, liftZ x = liftZ_std x * (RINV : Zq) := by
        intro x; unfold liftZ liftZ_std; rfl
      rw [h_liftZ_def, h_liftZ_def, h_lift (i / 8) hdiv (i % 8) hmod]
    · -- Bound conjunct.
      intro u hu j hj
      show (out.val[u]!).values.val[j]!.val.natAbs ≤ _
      exact h_bd u hu j hj

/--
info: 'libcrux_iot_ml_dsa.Polynomial.NttArith.reduce_fc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reduce_fc

end libcrux_iot_ml_dsa.Polynomial.NttArith
