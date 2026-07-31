/-
  # `Polynomial/Arithmetic.lean` — polynomial-layer `add`/`subtract` FCs (ML-DSA)

  The polynomial-layer arithmetic API (`crate::polynomial`) is generic over the
  `simd::traits::Operations` trait. These FCs apply the generic
  `PolynomialRingElement.{add,subtract}` to the concrete portable
  `Operations Coefficients` instance (`portable_ops_inst`, from `Ntt.lean`).

  Each is a 32-unit loop over `self.simd_units` (the loop accumulator `a` starts
  as `self.simd_units`; the partner `rhs` is read fresh): every iteration calls
  `inst.<op> a[i] rhs.simd_units[i]`. The instance's `add`/`subtract` fields are
  `@[reducible]` forwarders to `simd.portable.arithmetic.{add,subtract}`, to which
  the proven per-unit `add_spec`/`subtract_spec` (`Vector/Portable/Element.lean`)
  apply.

  The functional post is EQUALITY-form via `lift_poly`: the `liftZ_add`/`liftZ_sub`
  seam turns the per-unit integer `±` into the `Z_q`-level `±` of `Pure.poly_add`/
  `Pure.poly_sub`. The loop invariant carries, for each done unit, the per-lane
  value equation `acc[j].values[ℓ] = self[j].values[ℓ] ± rhs[j].values[ℓ]`
  (alongside the output bound), which is exactly what the lift equation needs.
-/
import LibcruxIotMlDsa.Polynomial.Ntt
import LibcruxIotMlDsa.Vector.Portable.Element
import LibcruxIotMlDsa.Util.LoopHelper
import LibcruxIotMlDsa.Spec.Lift
import LibcruxIotMlDsa.Spec.Pure

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_dsa.Polynomial.Arithmetic
open Aeneas Aeneas.Std Std.Do Result ControlFlow CoreModels
open libcrux_iot_ml_dsa
open libcrux_iot_ml_dsa.Spec
open libcrux_iot_ml_dsa.Spec.Lift
open libcrux_iot_ml_dsa.Polynomial.Ntt
open libcrux_iot_ml_dsa.Util.LoopHelper

/-! ## Local helpers — Triple ↔ Result.ok bridges, pure-prop holds. -/

private theorem triple_of_ok_ar
    {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

private theorem triple_exists_ok_ar
    {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl,
      (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

private theorem pure_prop_holds_ar {P : Prop} (h : P) : (pure P : Result Prop).holds := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp]; intro _; exact h

private theorem of_pure_prop_holds_ar {P : Prop}
    (h : (pure P : Result Prop).holds) : P := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp] at h; exact h trivial

/-! ## Carrier abbreviations and length bridges. -/

/-- The poly-layer loop accumulator: the raw 32-unit array. -/
abbrev UnitArray := Std.Array simd.portable.vector_type.Coefficients 32#usize

@[simp]
theorem UnitArray_length (a : UnitArray) : a.length = 32 := by
  have := a.property
  show a.val.length = 32
  exact this

/-- `Slice.len (Array.to_slice (a : UnitArray)) = 32#usize`. -/
private theorem units_slice_len_eq (a : UnitArray) :
    Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice a) = (32#usize : Std.Usize) := by
  apply Std.UScalar.eq_of_val_eq
  show (Aeneas.Std.Array.to_slice a).length = (32#usize : Std.Usize).val
  simp [Aeneas.Std.Array.to_slice]

/-! ## Generic 32-unit binary poly-loop core.

`self`/`rhs` are the two ring elements; `op : Int → Int → Int` is the lane
combinator (`(· + ·)` / `(· - ·)`); `inst_op` is the per-unit instance method
(`portable_ops_inst.add` / `.subtract`); `per_unit_spec` is the proven per-unit
spec for `inst_op` (an `add_spec`/`subtract_spec` wrapper). The loop body shape
matches `add_loop.body`/`subtract_loop.body` verbatim. -/

section Core

variable
    (op : Int → Int → Int)
    (inst_op : simd.portable.vector_type.Coefficients →
      simd.portable.vector_type.Coefficients →
      Result simd.portable.vector_type.Coefficients)

/-- The loop body (parametrized by the per-unit op `inst_op`), matching the
    extracted `{add,subtract}_loop.body … portable_ops_inst rhs`. -/
def body
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
    let t2 ← inst_op t t1
    let a1 := index_mut_back t2
    ok (cont (iter1, a1))

/-- Loop invariant: for done units `j < k`, the lane-wise value equation holds
    (`acc[j].values[ℓ] = op (self[j].values[ℓ]) (rhs[j].values[ℓ])`) and the
    output bound; for undone units `j ≥ k`, `acc[j] = self[j]`. -/
def inv
    (self rhs : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients) :
    Std.Usize → UnitArray → Result Prop :=
  fun k acc => pure (
    (∀ j : Nat, j < k.val →
      (∀ ℓ : Nat, ℓ < 8 →
        ((acc.val[j]!).values.val[ℓ]!).val
          = op ((self.simd_units.val[j]!).values.val[ℓ]!).val
                ((rhs.simd_units.val[j]!).values.val[ℓ]!).val
        ∧ ((acc.val[j]!).values.val[ℓ]!).val.natAbs ≤ 2 ^ 31 - 1))
    ∧ (∀ j : Nat, k.val ≤ j → j < 32 →
        acc.val[j]! = self.simd_units.val[j]!))

/-- Step post for `loop_range_spec_usize`. -/
def step_post
    (self rhs : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × UnitArray) UnitArray) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (32#usize : Std.Usize).val ∧ iter'.«end» = 32#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv op self rhs iter'.start acc').holds
  | .done y => (inv op self rhs 32#usize y).holds

set_option maxHeartbeats 4000000 in
/-- Per-iteration step lemma. Given the loop state `(acc, k)` with the invariant
    and the global precondition `hpre` (every lane of `op self[u][ℓ] rhs[u][ℓ]`
    is in range), applies `per_unit_spec` to chunk `k` of `acc`, recording the
    per-lane value equation while preserving units `j ≠ k`. -/
theorem step_lemma
    (self rhs : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (per_unit_spec : ∀ (lhs r : simd.portable.vector_type.Coefficients),
      (∀ ℓ : Nat, ℓ < 8 →
        (op (lhs.values.val[ℓ]!).val (r.values.val[ℓ]!).val : Int).natAbs ≤ 2 ^ 31 - 1) →
      ⦃ ⌜ True ⌝ ⦄
      inst_op lhs r
      ⦃ ⇓ out => ⌜ ∀ ℓ : Nat, ℓ < 8 →
                    (out.values.val[ℓ]!).val
                      = op (lhs.values.val[ℓ]!).val (r.values.val[ℓ]!).val
                    ∧ (out.values.val[ℓ]!).val.natAbs ≤ 2 ^ 31 - 1 ⌝ ⦄)
    (hpre : ∀ u : Nat, u < 32 → ∀ ℓ : Nat, ℓ < 8 →
      (op ((self.simd_units.val[u]!).values.val[ℓ]!).val
          ((rhs.simd_units.val[u]!).values.val[ℓ]!).val : Int).natAbs ≤ 2 ^ 31 - 1)
    (acc : UnitArray)
    (k : Std.Usize) (h_le : k.val ≤ (32#usize : Std.Usize).val)
    (h_inv : (inv op self rhs k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    body inst_op rhs { start := k, «end» := 32#usize } acc
    ⦃ ⇓ r => ⌜ step_post op self rhs k r ⌝ ⦄ := by
  have h32 : (32#usize : Std.Usize).val = 32 := rfl
  have h_acc_len : acc.length = 32 := UnitArray_length acc
  have h_rhs_len : rhs.simd_units.length = 32 := UnitArray_length rhs.simd_units
  obtain ⟨h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_ar h_inv
  unfold body
  by_cases h_lt : k.val < (32#usize : Std.Usize).val
  · -- `Some i = k` branch.
    have hk_32 : k.val < 32 := by rw [h32] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k 32#usize h_lt
    -- (1) `index_mut_usize acc k` → `(t, set_back)`.
    set t : simd.portable.vector_type.Coefficients := acc.val[k.val]! with ht_def
    have h_idx_t : Aeneas.Std.Array.index_usize acc k = .ok t :=
      array_index_usize_ok_eq acc k (by rw [h_acc_len]; exact hk_32)
    have h_imt_t : Aeneas.Std.Array.index_mut_usize acc k = .ok (t, acc.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_t]; rfl
    -- (1a) `t = self.simd_units[k]` (via h_acc_undone at j=k).
    have h_t_eq : t = self.simd_units.val[k.val]! := by
      show acc.val[k.val]! = self.simd_units.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_32
    -- (2) `t1 = rhs.simd_units[k]`.
    set t1 : simd.portable.vector_type.Coefficients := rhs.simd_units.val[k.val]! with ht1_def
    have h_idx_t1 : Aeneas.Std.Array.index_usize rhs.simd_units k = .ok t1 :=
      array_index_usize_ok_eq rhs.simd_units k (by rw [h_rhs_len]; exact hk_32)
    -- (3) `inst_op t t1` → `t2`, with per-lane value eq + bound.
    have h_op_bnd : ∀ ℓ : Nat, ℓ < 8 →
        (op (t.values.val[ℓ]!).val (t1.values.val[ℓ]!).val : Int).natAbs ≤ 2 ^ 31 - 1 := by
      intro ℓ hℓ
      rw [h_t_eq, ht1_def]
      exact hpre k.val hk_32 ℓ hℓ
    obtain ⟨t2, h_t2_eq, h_t2_P⟩ :=
      triple_exists_ok_ar (per_unit_spec t t1 h_op_bnd)
    -- (4) Compose the whole body into one `.ok` equation.
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
            let t2' ← inst_op t' t1'
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
      rw [h_t2_eq]
      rfl
    apply triple_of_ok_ar h_body
    show step_post op self rhs k
      (.cont (({ start := s, «end» := 32#usize }
                : CoreModels.core.ops.range.Range Std.Usize), acc.set k t2))
    unfold step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (inv op self rhs s (acc.set k t2)).holds
    apply pure_prop_holds_ar
    refine ⟨?_, ?_⟩
    · -- Done units `j < s.val`.
      intro j hj
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · -- j < k.val: unchanged by the set.
        have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_set_ne : (acc.set k t2).val[j]! = acc.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne acc k j t2 h_ne
        intro ℓ hℓ
        rw [h_set_ne]
        exact h_acc_done j hj_lt_k ℓ hℓ
      · -- j = k.val: it's t2.
        subst hj_eq_k
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
            let t2' ← inst_op t' t1'
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
    apply triple_of_ok_ar h_body
    show step_post op self rhs k (.done acc)
    unfold step_post
    show (inv op self rhs 32#usize acc).holds
    apply pure_prop_holds_ar
    refine ⟨?_, ?_⟩
    · intro j hj; rw [h32] at hj
      apply h_acc_done j; rw [hk_eq]; exact hj
    · intro j hj_ge hj_lt; rw [h32] at hj_ge
      apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge

end Core

/-! ## Lift bridge: the loop invariant at `k=32` ⟹ the `lift_poly` equality.

The done-half of the invariant at `k=32` says, for every unit `j<32` and lane
`ℓ<8`, `out[j].values[ℓ].val = op self[j].values[ℓ].val rhs[j].values[ℓ].val`.
We turn this into `lift_poly {simd_units := out} = build (fun i => liftZ-of-self ±
liftZ-of-rhs)`, then identify the RHS with `Pure.poly_{add,sub} (lift_poly self)
(lift_poly rhs)` via `liftZ_{add,sub}` and `Pure.build_getElem`. -/

/-- Generic lift bridge, parametrized by the integer combinator `op` and the
    matching `Z_q` combinator `zop` related by `liftZ (op x y) = zop (liftZ x)
    (liftZ y)`. -/
private theorem lift_bridge
    (op : Int → Int → Int) (zop : Parameters.Zq → Parameters.Zq → Parameters.Zq)
    (h_liftZ : ∀ x y : Int, liftZ (op x y) = zop (liftZ x) (liftZ y))
    (self rhs : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (out : UnitArray)
    (h_done : ∀ j : Nat, j < 32 → ∀ ℓ : Nat, ℓ < 8 →
        (out.val[j]!).values.val[ℓ]!.val
          = op ((self.simd_units.val[j]!).values.val[ℓ]!).val
                ((rhs.simd_units.val[j]!).values.val[ℓ]!).val) :
    lift_poly ({ simd_units := out } :
        polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
      = Pure.build (fun i =>
          zop ((lift_poly self)[i]!) ((lift_poly rhs)[i]!)) := by
  rw [lift_poly_eq_lift_units]
  unfold lift_units
  apply Pure.build_congr
  intro i hi
  -- `i/8 < 32` and `i%8 < 8`.
  have hdiv : i / 8 < 32 := by omega
  have hmod : i % 8 < 8 := Nat.mod_lt i (by decide)
  show liftZ ((out.val[i / 8]!).values.val[i % 8]!).val = _
  rw [h_done (i / 8) hdiv (i % 8) hmod, h_liftZ]
  -- Now: zop (liftZ self[i/8][i%8]) (liftZ rhs[i/8][i%8])
  --        = zop ((lift_poly self)[i]!) ((lift_poly rhs)[i]!).
  rw [show (lift_poly self)[i]!
        = liftZ ((self.simd_units.val[i / 8]!).values.val[i % 8]!).val from by
        rw [lift_poly_eq_lift_units]; unfold lift_units; rw [Pure.build_getElem _ i hi],
      show (lift_poly rhs)[i]!
        = liftZ ((rhs.simd_units.val[i / 8]!).values.val[i % 8]!).val from by
        rw [lift_poly_eq_lift_units]; unfold lift_units; rw [Pure.build_getElem _ i hi]]

/-! ## Top-level FCs. -/

set_option maxHeartbeats 8000000 in
/-- **`PolynomialRingElement.add` at `portable_ops_inst`.** 32-unit loop;
    each unit calls the per-unit `add` (forwarding to
    `simd.portable.arithmetic.add`). Functional post is EQUALITY-form via
    `lift_poly`. The precond `hpre` is the per-lane no-overflow bound on
    `self[u][ℓ] + rhs[u][ℓ]` consumed by the per-unit `add_spec`. -/
@[spec]
theorem add_fc
    (self rhs : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (hpre : ∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
      ((self.simd_units.val[u]!).values.val[j]!.val
        + (rhs.simd_units.val[u]!).values.val[j]!.val).natAbs ≤ 2 ^ 31 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    polynomial.PolynomialRingElement.add portable_ops_inst self rhs
    ⦃ ⇓ r => ⌜ lift_poly r = Pure.poly_add (lift_poly self) (lift_poly rhs)
             ∧ (∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
                  (r.simd_units.val[u]!).values.val[j]!.val.natAbs ≤ 2 ^ 31 - 1) ⌝ ⦄ := by
  unfold polynomial.PolynomialRingElement.add
  -- `lift (Array.to_slice self.simd_units) = .ok (Array.to_slice self.simd_units)`.
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice self.simd_units)
        = .ok (Aeneas.Std.Array.to_slice self.simd_units) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  -- `core.slice.Slice.len s = .ok (Slice.len s)`.
  rw [show CoreModels.core.slice.Slice.len (Aeneas.Std.Array.to_slice self.simd_units)
        = .ok (Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice self.simd_units)) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  -- `Slice.len (to_slice self.simd_units) = 32#usize`.
  rw [units_slice_len_eq self.simd_units]
  unfold polynomial.PolynomialRingElement.add_loop
  -- Bridge the extracted body to the generic `body`.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × UnitArray) =>
        polynomial.PolynomialRingElement.add_loop.body portable_ops_inst rhs p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × UnitArray) =>
        body portable_ops_inst.add rhs p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, a1⟩
    unfold polynomial.PolynomialRingElement.add_loop.body body
    rfl
  rw [h_body_eq]
  -- Run the loop via `loop_range_spec_usize`, with the per-lane `add` invariant.
  obtain ⟨out, h_out_eq, h_out_holds⟩ :=
    triple_exists_ok_ar
      (Util.LoopSpecs.loop_range_spec_usize
        (fun p => body portable_ops_inst.add rhs p.1 p.2)
        self.simd_units 0#usize 32#usize
        (inv (· + ·) self rhs)
        (by decide : (0#usize : Std.Usize).val ≤ (32#usize : Std.Usize).val)
        (by
          apply pure_prop_holds_ar
          refine ⟨fun j hj => absurd hj (Nat.not_lt_zero j), fun _ _ _ => rfl⟩)
        (by
          intro acc k _h_ge h_le hinv
          have h_step :=
            step_lemma (· + ·) portable_ops_inst.add self rhs
              (fun lhs r hb => by
                show ⦃ ⌜ True ⌝ ⦄ simd.portable.arithmetic.add lhs r ⦃ _ ⦄
                exact Vector.Portable.Element.add_spec lhs r hb)
              hpre acc k h_le hinv
          apply Std.Do.Triple.of_entails_right _ h_step
          rw [PostCond.entails_noThrow]
          intro r hh
          rcases r with ⟨iter', acc'⟩ | y
          · have hP : step_post (· + ·) self rhs k (.cont (iter', acc')) := by
              simpa [Std.Do.SPred.down_pure] using hh
            simpa [step_post] using hP
          · have hP : step_post (· + ·) self rhs k (.done y) := by
              simpa [Std.Do.SPred.down_pure] using hh
            simpa [step_post] using hP))
  rw [h_out_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  -- `h_out_holds : (inv (·+·) self rhs 32#usize out).holds`.
  obtain ⟨h_done, _h_undone⟩ := of_pure_prop_holds_ar h_out_holds
  refine triple_of_ok_ar (v := { simd_units := out }) rfl ?_
  refine ⟨?_, ?_⟩
  · -- Equality conjunct via the lift bridge.
    have h_bridge := lift_bridge (· + ·) (· + ·)
      (fun x y => liftZ_add x y) self rhs out
      (fun j hj ℓ hℓ => (h_done j (by rw [show (32#usize : Std.Usize).val = 32 from rfl]; exact hj) ℓ hℓ).1)
    show lift_poly ({ simd_units := out } :
        polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients) = _
    rw [h_bridge]
    unfold Pure.poly_add
    rfl
  · -- Bound conjunct.
    intro u hu j hj
    show (out.val[u]!).values.val[j]!.val.natAbs ≤ _
    exact (h_done u (by rw [show (32#usize : Std.Usize).val = 32 from rfl]; exact hu) j hj).2

set_option maxHeartbeats 8000000 in
/-- **`PolynomialRingElement.subtract` at `portable_ops_inst`.** Clone of
    `add_fc` with `-`/`Pure.poly_sub`/`subtract_spec`. -/
@[spec]
theorem subtract_fc
    (self rhs : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (hpre : ∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
      ((self.simd_units.val[u]!).values.val[j]!.val
        - (rhs.simd_units.val[u]!).values.val[j]!.val).natAbs ≤ 2 ^ 31 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    polynomial.PolynomialRingElement.subtract portable_ops_inst self rhs
    ⦃ ⇓ r => ⌜ lift_poly r = Pure.poly_sub (lift_poly self) (lift_poly rhs)
             ∧ (∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
                  (r.simd_units.val[u]!).values.val[j]!.val.natAbs ≤ 2 ^ 31 - 1) ⌝ ⦄ := by
  unfold polynomial.PolynomialRingElement.subtract
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice self.simd_units)
        = .ok (Aeneas.Std.Array.to_slice self.simd_units) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show CoreModels.core.slice.Slice.len (Aeneas.Std.Array.to_slice self.simd_units)
        = .ok (Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice self.simd_units)) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [units_slice_len_eq self.simd_units]
  unfold polynomial.PolynomialRingElement.subtract_loop
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × UnitArray) =>
        polynomial.PolynomialRingElement.subtract_loop.body portable_ops_inst rhs p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × UnitArray) =>
        body portable_ops_inst.subtract rhs p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, a1⟩
    unfold polynomial.PolynomialRingElement.subtract_loop.body body
    rfl
  rw [h_body_eq]
  obtain ⟨out, h_out_eq, h_out_holds⟩ :=
    triple_exists_ok_ar
      (Util.LoopSpecs.loop_range_spec_usize
        (fun p => body portable_ops_inst.subtract rhs p.1 p.2)
        self.simd_units 0#usize 32#usize
        (inv (· - ·) self rhs)
        (by decide : (0#usize : Std.Usize).val ≤ (32#usize : Std.Usize).val)
        (by
          apply pure_prop_holds_ar
          refine ⟨fun j hj => absurd hj (Nat.not_lt_zero j), fun _ _ _ => rfl⟩)
        (by
          intro acc k _h_ge h_le hinv
          have h_step :=
            step_lemma (· - ·) portable_ops_inst.subtract self rhs
              (fun lhs r hb => by
                show ⦃ ⌜ True ⌝ ⦄ simd.portable.arithmetic.subtract lhs r ⦃ _ ⦄
                exact Vector.Portable.Element.subtract_spec lhs r hb)
              hpre acc k h_le hinv
          apply Std.Do.Triple.of_entails_right _ h_step
          rw [PostCond.entails_noThrow]
          intro r hh
          rcases r with ⟨iter', acc'⟩ | y
          · have hP : step_post (· - ·) self rhs k (.cont (iter', acc')) := by
              simpa [Std.Do.SPred.down_pure] using hh
            simpa [step_post] using hP
          · have hP : step_post (· - ·) self rhs k (.done y) := by
              simpa [Std.Do.SPred.down_pure] using hh
            simpa [step_post] using hP))
  rw [h_out_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  obtain ⟨h_done, _h_undone⟩ := of_pure_prop_holds_ar h_out_holds
  refine triple_of_ok_ar (v := { simd_units := out }) rfl ?_
  refine ⟨?_, ?_⟩
  · have h_bridge := lift_bridge (· - ·) (· - ·)
      (fun x y => liftZ_sub x y) self rhs out
      (fun j hj ℓ hℓ => (h_done j (by rw [show (32#usize : Std.Usize).val = 32 from rfl]; exact hj) ℓ hℓ).1)
    show lift_poly ({ simd_units := out } :
        polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients) = _
    rw [h_bridge]
    unfold Pure.poly_sub
    rfl
  · intro u hu j hj
    show (out.val[u]!).values.val[j]!.val.natAbs ≤ _
    exact (h_done u (by rw [show (32#usize : Std.Usize).val = 32 from rfl]; exact hu) j hj).2

end libcrux_iot_ml_dsa.Polynomial.Arithmetic
