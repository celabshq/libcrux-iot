/-
  # `Polynomial/Convert.lean` — polynomial-layer convert FCs (ML-DSA)

  The polynomial-layer convert API (`crate::polynomial`) is generic over the
  `simd::traits::Operations` trait. These FCs apply the generic
  `PolynomialRingElement.{zero, to_i32_array, from_i32_array}` to the concrete
  portable `Operations Coefficients` instance (`portable_ops_inst`, from
  `Ntt.lean`), reducing the per-unit instance methods to the proven per-unit
  convert FCs (`Vector/Portable/Element.lean`).

  - **`zero_fc`** — `do let t ← inst.zero; ok {simd_units := repeat 32 t}`; the
    instance's `zero` returns the all-zero unit, so every lane is `0` and
    `lift_poly r = Pure.zero_poly` (`liftZ 0 = 0`).
  - **`to_i32_array_fc`** — an `enumerate`-iterator loop over the 32 units,
    writing each unit's 8 declassified coeffs into window `[i*8 .. i*8+8)` of a
    256-array via the per-unit `to_coefficient_array`. Raw-value extraction post.
  - **`from_i32_array_fc`** — a `Range`-iterator loop building each unit from the
    `array[i*8 .. i*8+8)` window via the per-unit `from_coefficient_array`.
    Raw-value (and `lift_poly`-form) post.
-/
import LibcruxIotMlDsa.Polynomial.Ntt
import LibcruxIotMlDsa.Vector.Portable.Element
import LibcruxIotMlDsa.Util.LoopHelper
import LibcruxIotMlDsa.Util.LoopSpecs
import LibcruxIotMlDsa.Util.SliceSpecs
import LibcruxIotMlDsa.Spec.Lift
import LibcruxIotMlDsa.Spec.Pure

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_dsa.Polynomial.Convert
open Aeneas Aeneas.Std Std.Do Result ControlFlow CoreModels
open libcrux_iot_ml_dsa
open libcrux_iot_ml_dsa.Spec
open libcrux_iot_ml_dsa.Spec.Lift
open libcrux_iot_ml_dsa.Polynomial.Ntt
open libcrux_iot_ml_dsa.Util.LoopHelper

/-! ## Local helpers — Triple ↔ Result.ok bridges. -/

private theorem triple_of_ok_cv
    {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

private theorem triple_exists_ok_cv
    {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl,
      (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

private theorem pure_prop_holds_cv {P : Prop} (h : P) : (pure P : Result Prop).holds := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp]; intro _; exact h

private theorem of_pure_prop_holds_cv {P : Prop}
    (h : (pure P : Result Prop).holds) : P := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp] at h; exact h trivial

/-- `.val`-preserving `Std.Usize` mul helper. -/
private theorem usize_mul_ok_eq (x y : Std.Usize) (h : x.val * y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x * y : Result Std.Usize) = .ok z ∧ z.val = x.val * y.val := by
  obtain ⟨z, h_eq, h_v⟩ := Std.WP.spec_imp_exists (Std.Usize.mul_spec h); exact ⟨z, h_eq, h_v⟩

/-- `.val`-preserving `Std.Usize` add helper. -/
private theorem usize_add_ok_eq (x y : Std.Usize) (h : x.val + y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x + y : Result Std.Usize) = .ok z ∧ z.val = x.val + y.val := by
  obtain ⟨z, h_eq, h_v⟩ := Std.WP.spec_imp_exists (Std.Usize.add_spec h); exact ⟨z, h_eq, h_v⟩

/-- Sub-slice extraction `.ok`-form, from `core_models_Slice_Insts_index_RangeUsize_spec`. -/
private theorem slice_index_range_ok_eq
    {T : Type} (a : Slice T) (r : CoreModels.core.ops.range.Range Std.Usize)
    (h0 : r.start.val ≤ r.end.val) (h1 : r.end.val ≤ a.val.length) :
    ∃ s : Slice T,
      core.Slice.Insts.CoreOpsIndexIndex.index
        (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) a r = .ok s
      ∧ s.val = a.val.slice r.start.val r.end.val
      ∧ s.val.length = r.end.val - r.start.val := by
  obtain ⟨s, h_eq, h_post⟩ :=
    triple_exists_ok_cv (Util.SliceSpecs.core_models_Slice_Insts_index_RangeUsize_spec
      (T := T) a r h0 h1)
  exact ⟨s, h_eq, h_post.1, h_post.2⟩

/-- `(Array.repeat n x).val[i]! = x` for `i < n` (used by `zero_fc`). -/
private theorem repeat_getElem {α : Type} [Inhabited α] (n : Std.Usize) (x : α)
    (i : Nat) (hi : i < n.val) :
    (Array.repeat n x).val[i]! = x := by
  rw [Array.repeat_val, List.getElem!_eq_getElem?_getD, List.getElem?_replicate]
  simp [hi]

/-- The poly-layer convert-loop accumulator carrier (the whole ring element). -/
abbrev PRE := polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients

/-! ## `zero` — `PolynomialRingElement.zero` at `portable_ops_inst`.

`zero inst = do let t ← inst.zero; ok {simd_units := repeat 32 t}`; the instance's
`zero` field reduces to `simd.portable.vector_type.zero`, an all-zero unit, so the
whole ring element is all-zero. -/

@[spec]
theorem zero_fc :
    ⦃ ⌜ True ⌝ ⦄
    polynomial.PolynomialRingElement.zero portable_ops_inst
    ⦃ ⇓ r => ⌜ lift_poly r = Pure.zero_poly
             ∧ (∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
                  (r.simd_units.val[u]!).values.val[j]!.val = 0) ⌝ ⦄ := by
  -- The all-zero SIMD unit (`classify` is identity).
  set zu : simd.portable.vector_type.Coefficients :=
    { values := Array.repeat 8#usize (0#i32 : Std.I32) } with hzu_def
  have h_ok : polynomial.PolynomialRingElement.zero portable_ops_inst
      = .ok { simd_units := Array.repeat 32#usize zu } := by
    unfold polynomial.PolynomialRingElement.zero
    show (do
      let t ← simd.portable.vector_type.zero
      Result.ok ({ simd_units := Array.repeat 32#usize t }
        : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)) = _
    rw [show simd.portable.vector_type.zero = .ok zu from by
        rw [hzu_def]
        unfold simd.portable.vector_type.zero
        unfold libcrux_secrets.traits.Classify.Blanket.classify
        rfl]
    rfl
  refine triple_of_ok_cv (v := { simd_units := Array.repeat 32#usize zu }) h_ok ?_
  -- Raw lane values are all `0`.
  have h_lane : ∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
      ((Array.repeat 32#usize zu).val[u]!).values.val[j]!.val = 0 := by
    intro u hu j hj
    rw [repeat_getElem 32#usize zu u (by exact hu), hzu_def]
    show ((Array.repeat 8#usize (0#i32 : Std.I32)).val[j]!).val = 0
    rw [repeat_getElem 8#usize (0#i32 : Std.I32) j (by exact hj)]
    decide
  refine ⟨?_, h_lane⟩
  -- `lift_poly r = zero_poly` via per-index `liftZ 0 = 0`.
  unfold lift_poly Pure.zero_poly
  apply Pure.build_congr
  intro i hi
  have hdiv : i / 8 < 32 := by omega
  have hmod : i % 8 < 8 := Nat.mod_lt i (by decide)
  show liftZ _ = 0
  rw [h_lane (i / 8) hdiv (i % 8) hmod]
  show liftZ 0 = 0
  unfold liftZ
  simp

/--
info: 'libcrux_iot_ml_dsa.Polynomial.Convert.zero_fc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms zero_fc

/-! ## `from_i32_array` — `PolynomialRingElement.from_i32_array` at `portable_ops_inst`.

A `Range`-iterator loop `0..32`; the accumulator is the whole `result : PRE`. Each
iteration extracts `array[i*8 .. i*8+8)`, indexes (and overwrites) `result.simd_units[i]`
via the per-unit `from_coefficient_array` (which discards the read value), so unit `i`'s
8 lanes become the `i*8 .. i*8+8` window of `array`. The invariant carries the done-units
value equation `acc[j].values[ℓ] = array[8*j + ℓ]` and the unit-array length. -/

section FromI32

/-- The loop body (matching `from_i32_array_loop.body … portable_ops_inst array`). -/
def from_body (array : Slice Std.I32)
    (iter : CoreModels.core.ops.range.Range Std.Usize) (result : PRE) :
    Result (ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) × PRE) PRE) := do
  let (o, iter1) ←
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep iter
  match o with
  | core.option.Option.None => ok (done result)
  | core.option.Option.Some i =>
    let i1 ← i * simd.traits.COEFFICIENTS_IN_SIMD_UNIT
    let i2 ← i + 1#usize
    let i3 ← i2 * simd.traits.COEFFICIENTS_IN_SIMD_UNIT
    let s ←
      core.Slice.Insts.CoreOpsIndexIndex.index
        (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I32) array
        { start := i1, «end» := i3 }
    let (t, index_mut_back) ← Array.index_mut_usize result.simd_units i
    let t1 ← portable_ops_inst.from_coefficient_array s t
    let a := index_mut_back t1
    ok (cont (iter1, { simd_units := a }))

/-- Loop invariant: the unit-array has 32 units, and for done units `j < k` the
    lane-wise value equation `acc[j].values[ℓ] = array[8*j + ℓ]` holds. -/
def from_inv (array : Slice Std.I32) : Std.Usize → PRE → Result Prop :=
  fun k acc => pure (
    acc.simd_units.val.length = 32 ∧
    (∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 8 →
      ((acc.simd_units.val[j]!).values.val[ℓ]!).val = (array.val[8 * j + ℓ]!).val))

/-- Step post for `loop_range_spec_usize`. -/
def from_step_post (array : Slice Std.I32) (k : Std.Usize)
    (r : ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) × PRE) PRE) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (32#usize : Std.Usize).val ∧ iter'.«end» = 32#usize
        ∧ iter'.start.val = k.val + 1 ∧ (from_inv array iter'.start acc').holds
  | .done y => (from_inv array 32#usize y).holds

set_option maxHeartbeats 4000000 in
/-- Per-iteration step lemma. Given the loop state `(acc, k)` with the invariant
    and the length precondition `hlen` (`array` length 256), applies the per-unit
    `from_coefficient_array_spec` to chunk `k`, recording the per-lane value
    equation while preserving units `j ≠ k`. -/
theorem from_step_lemma (array : Slice Std.I32) (hlen : array.val.length = 256)
    (acc : PRE) (k : Std.Usize) (h_le : k.val ≤ (32#usize : Std.Usize).val)
    (h_inv : (from_inv array k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    from_body array { start := k, «end» := 32#usize } acc
    ⦃ ⇓ r => ⌜ from_step_post array k r ⌝ ⦄ := by
  have h32 : (32#usize : Std.Usize).val = 32 := rfl
  obtain ⟨h_acc_len, h_acc_done⟩ := of_pure_prop_holds_cv h_inv
  unfold from_body
  by_cases h_lt : k.val < (32#usize : Std.Usize).val
  · have hk_32 : k.val < 32 := by rw [h32] at h_lt; exact h_lt
    obtain ⟨s_it, hs_it_val, h_iter_some⟩ := iter_next_some_eq k 32#usize h_lt
    rw [show simd.traits.COEFFICIENTS_IN_SIMD_UNIT = 8#usize by
          simp [simd.traits.COEFFICIENTS_IN_SIMD_UNIT]]
    -- i1 = k*8.
    have hmax8 : k.val * (8#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [show (8#usize : Std.Usize).val = 8 from rfl]
      have h1 : k.val * 8 ≤ 31 * 8 := Nat.mul_le_mul_right 8 (by omega)
      have h2 : (31 * 8 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i1, hi1_eq, hi1_v⟩ := usize_mul_ok_eq k 8#usize hmax8
    have hi1_val : i1.val = 8 * k.val := by
      rw [hi1_v, show (8#usize : Std.Usize).val = 8 from rfl]; omega
    -- i2 = k+1.
    have hmaxa : k.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [show (1#usize : Std.Usize).val = 1 from rfl]
      have : (32 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i2, hi2_eq, hi2_v⟩ := usize_add_ok_eq k 1#usize hmaxa
    have hi2_val : i2.val = k.val + 1 := by
      rw [hi2_v, show (1#usize : Std.Usize).val = 1 from rfl]
    -- i3 = i2*8.
    have hmax3 : i2.val * (8#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [show (8#usize : Std.Usize).val = 8 from rfl, hi2_val]
      have h1 : (k.val + 1) * 8 ≤ 32 * 8 := Nat.mul_le_mul_right 8 (by omega)
      have h2 : (32 * 8 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i3, hi3_eq, hi3_v⟩ := usize_mul_ok_eq i2 8#usize hmax3
    have hi3_val : i3.val = 8 * (k.val + 1) := by
      rw [hi3_v, hi2_val, show (8#usize : Std.Usize).val = 8 from rfl]; omega
    -- s = array[i1..i3].
    have h0_le : i1.val ≤ i3.val := by rw [hi1_val, hi3_val]; omega
    have hi3_le : i3.val ≤ array.val.length := by
      rw [hlen, hi3_val]
      have : (k.val + 1) * 8 ≤ 32 * 8 := Nat.mul_le_mul_right 8 (by omega)
      omega
    obtain ⟨s, hs_eq, hs_slice, hs_len⟩ :=
      slice_index_range_ok_eq array { start := i1, «end» := i3 } h0_le hi3_le
    have hs_len8 : 8 ≤ s.val.length := by
      rw [hs_len]; show 8 ≤ i3.val - i1.val; rw [hi1_val, hi3_val]; omega
    -- index_mut acc.simd_units k.
    set t : simd.portable.vector_type.Coefficients := acc.simd_units.val[k.val]! with ht_def
    have h_idx_t : Aeneas.Std.Array.index_usize acc.simd_units k = .ok t :=
      array_index_usize_ok_eq acc.simd_units k
        (by rw [show acc.simd_units.length = acc.simd_units.val.length from rfl, h_acc_len];
            exact hk_32)
    have h_imt_t : Aeneas.Std.Array.index_mut_usize acc.simd_units k
        = .ok (t, acc.simd_units.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize; rw [h_idx_t]; rfl
    -- from_coefficient_array s t → t1, with the per-lane value eq.
    obtain ⟨t1, ht1_eq, ht1_P⟩ :=
      triple_exists_ok_cv (Vector.Portable.Element.from_coefficient_array_spec s t hs_len8)
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
                  ((CoreModels.core.ops.range.Range Std.Usize) × PRE) PRE))
          | core.option.Option.Some i =>
            let i1 ← i * 8#usize
            let i2 ← i + 1#usize
            let i3 ← i2 * 8#usize
            let s ←
              core.Slice.Insts.CoreOpsIndexIndex.index
                (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I32) array
                { start := i1, «end» := i3 }
            let (t', index_mut_back) ← Array.index_mut_usize acc.simd_units i
            let t1' ← portable_ops_inst.from_coefficient_array s t'
            let a := index_mut_back t1'
            ok (cont (iter1, ({ simd_units := a } : PRE))))
        = .ok (cont (({ start := s_it, «end» := 32#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                     ({ simd_units := acc.simd_units.set k t1 } : PRE))) := by
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
      rw [hi1_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi2_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi3_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hs_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_t]; simp only [Aeneas.Std.bind_tc_ok]
      rw [show
        simd.portable.vector_type.Coefficients.Insts.Libcrux_iot_ml_dsaSimdTraitsOperations.from_coefficient_array
            s t
          = simd.portable.vector_type.from_coefficient_array s t from rfl]
      rw [ht1_eq]
      rfl
    apply triple_of_ok_cv h_body
    show from_step_post array k
      (.cont (({ start := s_it, «end» := 32#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
              ({ simd_units := acc.simd_units.set k t1 } : PRE)))
    unfold from_step_post
    refine ⟨h_lt, rfl, hs_it_val, ?_⟩
    show (from_inv array s_it { simd_units := acc.simd_units.set k t1 }).holds
    apply pure_prop_holds_cv
    refine ⟨?_, ?_⟩
    · show (acc.simd_units.set k t1).val.length = 32
      rw [show (acc.simd_units.set k t1).val.length = acc.simd_units.val.length from by
            simp [Aeneas.Std.Array.set]]
      exact h_acc_len
    · intro j hj ℓ hℓ
      rw [hs_it_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt | hj_eq
      · -- j < k: unchanged by the set.
        have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt
        have h_set_ne : (acc.simd_units.set k t1).val[j]! = acc.simd_units.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.simd_units k j t1 h_ne
        rw [h_set_ne]
        exact h_acc_done j hj_lt ℓ hℓ
      · -- j = k: it's t1.
        subst hj_eq
        have h_set_eq : (acc.simd_units.set k t1).val[k.val]! = t1 := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_eq acc.simd_units k k.val t1
              ⟨rfl, by rw [show acc.simd_units.length = acc.simd_units.val.length from rfl,
                          h_acc_len]; exact hk_32⟩
        rw [h_set_eq]
        -- t1.values[ℓ] = s[ℓ] = array[i1 + ℓ] = array[8*k + ℓ].
        rw [ht1_P ℓ hℓ, hs_slice]
        rw [List.getElem!_slice i1.val i3.val ℓ array.val
              ⟨hi3_le, by rw [hi1_val, hi3_val]; omega⟩]
        rw [hi1_val]
  · -- None branch: k ≥ 32, done.
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
                  ((CoreModels.core.ops.range.Range Std.Usize) × PRE) PRE))
          | core.option.Option.Some i =>
            let i1 ← i * simd.traits.COEFFICIENTS_IN_SIMD_UNIT
            let i2 ← i + 1#usize
            let i3 ← i2 * simd.traits.COEFFICIENTS_IN_SIMD_UNIT
            let s ←
              core.Slice.Insts.CoreOpsIndexIndex.index
                (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I32) array
                { start := i1, «end» := i3 }
            let (t', index_mut_back) ← Array.index_mut_usize acc.simd_units i
            let t1' ← portable_ops_inst.from_coefficient_array s t'
            let a := index_mut_back t1'
            ok (cont (iter1, ({ simd_units := a } : PRE))))
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
    apply triple_of_ok_cv h_body
    show from_step_post array k (.done acc)
    unfold from_step_post
    show (from_inv array 32#usize acc).holds
    apply pure_prop_holds_cv
    refine ⟨h_acc_len, ?_⟩
    intro j hj ℓ hℓ; rw [h32] at hj
    exact h_acc_done j (by rw [hk_eq]; exact hj) ℓ hℓ

end FromI32

set_option maxHeartbeats 8000000 in
/-- **`PolynomialRingElement.from_i32_array` at `portable_ops_inst`.** 32-unit
    `Range` loop; each unit reads `array[i*8 .. i*8+8)` via the per-unit
    `from_coefficient_array`. Raw-value equality post, plus the `lift_poly`-form
    corollary. The precond `hlen` (`array` length 256) is the impl's `massert`
    bound + the in-bounds requirement of the per-window index. -/
@[spec]
theorem from_i32_array_fc
    (array : Slice Std.I32) (result : PRE) (hlen : array.val.length = 256) :
    ⦃ ⌜ True ⌝ ⦄
    polynomial.PolynomialRingElement.from_i32_array portable_ops_inst array result
    ⦃ ⇓ r => ⌜ ∀ k : Nat, k < 256 →
                (r.simd_units.val[k / 8]!).values.val[k % 8]!.val = (array.val[k]!).val ⌝ ⦄ := by
  -- Reduce the top-level `from_i32_array` to the `0..32` loop.
  unfold polynomial.PolynomialRingElement.from_i32_array
  rw [show CoreModels.core.slice.Slice.len array = .ok (Aeneas.Std.Slice.len array) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show (massert (Aeneas.Std.Slice.len array >= 256#usize) : Result Unit) = .ok () from by
        have h : (Aeneas.Std.Slice.len array >= 256#usize) := by
          have hv : (Aeneas.Std.Slice.len array).val = 256 := by
            simp [hlen]
          show (256#usize : Std.Usize).val ≤ (Aeneas.Std.Slice.len array).val
          rw [hv]; decide
        unfold massert; simp [h]]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show simd.traits.SIMD_UNITS_IN_RING_ELEMENT = .ok 32#usize from by
        simp only [simd.traits.SIMD_UNITS_IN_RING_ELEMENT,
          constants.COEFFICIENTS_IN_RING_ELEMENT, simd.traits.COEFFICIENTS_IN_SIMD_UNIT]
        rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  unfold polynomial.PolynomialRingElement.from_i32_array_loop
  -- Bridge the extracted body to `from_body`.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × PRE) =>
        polynomial.PolynomialRingElement.from_i32_array_loop.body portable_ops_inst array p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × PRE) =>
        from_body array p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, a1⟩
    unfold polynomial.PolynomialRingElement.from_i32_array_loop.body from_body
    rfl
  rw [h_body_eq]
  -- Run the loop via `loop_range_spec_usize`.
  obtain ⟨out, h_out_eq, h_out_holds⟩ :=
    triple_exists_ok_cv
      (Util.LoopSpecs.loop_range_spec_usize
        (fun p => from_body array p.1 p.2)
        result 0#usize 32#usize
        (from_inv array)
        (by decide : (0#usize : Std.Usize).val ≤ (32#usize : Std.Usize).val)
        (by
          apply pure_prop_holds_cv
          exact ⟨result.simd_units.property, fun j hj => absurd hj (Nat.not_lt_zero j)⟩)
        (by
          intro acc k _h_ge h_le hinv
          have h_step := from_step_lemma array hlen acc k h_le hinv
          apply Std.Do.Triple.of_entails_right _ h_step
          rw [PostCond.entails_noThrow]
          intro r hh
          rcases r with ⟨iter', acc'⟩ | y
          · have hP : from_step_post array k (.cont (iter', acc')) := by
              simpa [Std.Do.SPred.down_pure] using hh
            simpa [from_step_post] using hP
          · have hP : from_step_post array k (.done y) := by
              simpa [Std.Do.SPred.down_pure] using hh
            simpa [from_step_post] using hP))
  rw [h_out_eq]
  -- `h_out_holds : (from_inv array 32#usize out).holds`.
  obtain ⟨_h_len, h_done⟩ := of_pure_prop_holds_cv h_out_holds
  refine triple_of_ok_cv (v := out) rfl ?_
  intro k hk
  have hdiv : k / 8 < 32 := by omega
  have hmod : k % 8 < 8 := Nat.mod_lt k (by decide)
  have h := h_done (k / 8) (by rw [show (32#usize : Std.Usize).val = 32 from rfl]; exact hdiv)
              (k % 8) hmod
  rw [h]
  -- `8 * (k/8) + k%8 = k`.
  rw [show 8 * (k / 8) + k % 8 = k from by omega]

/--
info: 'libcrux_iot_ml_dsa.Polynomial.Convert.from_i32_array_fc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms from_i32_array_fc

/-- **`lift_poly`-form corollary of `from_i32_array_fc`.** The lifted ring element
    is the clean spec built from the (mont-stripped) input lanes. -/
theorem from_i32_array_lift_fc
    (array : Slice Std.I32) (result : PRE) (hlen : array.val.length = 256) :
    ⦃ ⌜ True ⌝ ⦄
    polynomial.PolynomialRingElement.from_i32_array portable_ops_inst array result
    ⦃ ⇓ r => ⌜ lift_poly r = Pure.build (fun k => liftZ (array.val[k]!).val) ⌝ ⦄ := by
  obtain ⟨out, h_out_eq, h_raw⟩ := triple_exists_ok_cv (from_i32_array_fc array result hlen)
  refine triple_of_ok_cv h_out_eq ?_
  unfold lift_poly
  apply Pure.build_congr
  intro i hi
  show liftZ ((out.simd_units.val[i / 8]!).values.val[i % 8]!).val = liftZ (array.val[i]!).val
  rw [h_raw i hi]

/-! ## `to_i32_array` — `PolynomialRingElement.to_i32_array` at `portable_ops_inst`.

An `enumerate`-iterator loop over `self.simd_units` (a 32-unit slice). The
accumulator is the 256-array `result`. Each iteration writes the `i`-th unit's 8
declassified lanes into window `[i*8 .. i*8+8)` via the per-unit
`to_coefficient_array`. We prove the loop by induction on the remaining-suffix
length, with an invariant that the consumed-prefix windows of `result` already
hold the corresponding units' lanes. -/

section ToI32

abbrev SU := simd.portable.vector_type.Coefficients
abbrev Arr256 := Std.Array Std.I32 256#usize
abbrev EnumIter := CoreModels.core.iter.adapters.enumerate.Enumerate
  (CoreModels.core.slice.iter.Iter SU)

/-- The inner `slice.iter.Iter` `next` on a nonempty suffix pops the head and
    returns the `drop 1` tail. -/
private theorem inner_next_some (suffix : Slice SU) (hne : 0 < suffix.val.length) :
    ∃ tl : Slice SU, tl.val = suffix.val.drop 1 ∧
      CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
        (T := SU) suffix
      = .ok (CoreModels.core.option.Option.Some (suffix.val[0]!), tl) := by
  have hlen0 : ¬ (Aeneas.Std.Slice.len suffix = 0#usize) := by
    intro h
    have hv : suffix.val.length = 0 := by
      have hh : (Aeneas.Std.Slice.len suffix).val = (0#usize : Std.Usize).val := by rw [h]
      rwa [Aeneas.Std.Slice.len_val, show (0#usize : Std.Usize).val = 0 from rfl] at hh
    omega
  refine ⟨⟨suffix.val.drop 1, by have := suffix.property; simp; omega⟩, rfl, ?_⟩
  unfold CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
  unfold rust_primitives.sequence.seq_len
  simp only [Aeneas.Std.bind_tc_ok]
  rw [if_neg hlen0]
  unfold rust_primitives.sequence.seq_remove
  rw [dif_pos (by show (0#usize : Std.Usize).val < suffix.val.length; simpa using hne)]
  have hget : (suffix.val.get ⟨(0#usize : Std.Usize).val, by simpa using hne⟩)
      = suffix.val[0]! := by
    rw [List.getElem!_eq_getElem?_getD, List.get_eq_getElem,
        List.getElem?_eq_getElem (by simpa using hne)]; rfl
  have hsl : suffix.val.take (0#usize : Std.Usize).val
      ++ suffix.val.drop ((0#usize : Std.Usize).val + 1) = suffix.val.drop 1 := by simp
  simp only [Aeneas.Std.bind_tc_ok, hget, hsl]
  rfl

/-- The inner `slice.iter.Iter` `next` on an empty suffix returns `None`. -/
private theorem inner_next_none (suffix : Slice SU) (he : suffix.val.length = 0) :
    CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
      (T := SU) suffix
    = .ok (CoreModels.core.option.Option.None, suffix) := by
  unfold CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
  unfold rust_primitives.sequence.seq_len
  simp only [Aeneas.Std.bind_tc_ok]
  have hlen0 : (Aeneas.Std.Slice.len suffix = 0#usize) := by
    apply Std.UScalar.eq_of_val_eq
    rw [Aeneas.Std.Slice.len_val]
    simp only [show (0#usize : Std.Usize).val = 0 from rfl, he]
  rw [if_pos hlen0]

/-- The `Enumerate` `next` on a nonempty suffix at count `c`. -/
private theorem enum_next_some (suffix : Slice SU) (c : Std.Usize)
    (hne : 0 < suffix.val.length) (hc : c.val + 1 ≤ Std.Usize.max) :
    ∃ (tl : Slice SU) (c' : Std.Usize), tl.val = suffix.val.drop 1 ∧ c'.val = c.val + 1 ∧
      CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
        (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT SU)
        { iter := suffix, count := c }
      = .ok (CoreModels.core.option.Option.Some (c, suffix.val[0]!),
          { iter := tl, count := c' }) := by
  unfold CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
  obtain ⟨tl, htl_val, htl_eq⟩ := inner_next_some suffix hne
  rw [show (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT SU).next
            suffix
        = CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
            (T := SU) suffix from rfl]
  rw [htl_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  obtain ⟨c', hc'_eq, hc'_val⟩ :=
    usize_add_ok_eq c 1#usize (by rw [show (1#usize : Std.Usize).val = 1 from rfl]; exact hc)
  rw [hc'_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  exact ⟨tl, c', htl_val, by rw [hc'_val, show (1#usize : Std.Usize).val = 1 from rfl], rfl⟩

/-- The `Enumerate` `next` on an empty suffix returns `None`. -/
private theorem enum_next_none (suffix : Slice SU) (c : Std.Usize)
    (he : suffix.val.length = 0) :
    CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
      (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT SU)
      { iter := suffix, count := c }
    = .ok (CoreModels.core.option.Option.None, { iter := suffix, count := c }) := by
  unfold CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
  rw [show (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT SU).next
            suffix
        = CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
            (T := SU) suffix from rfl]
  rw [inner_next_none suffix he]; rfl

/-- Mutable sub-slice index of the 256-array over a `Range`: returns the sub-slice
    `result.val[i1..i3]` (length 8) and a write-back that overwrites window
    `[i1, i1+|s'|)`. -/
private theorem arr_index_mut (result : Arr256) (i1 i3 : Std.Usize)
    (h0 : i1.val ≤ i3.val) (h1 : i3.val ≤ 256) (hwin : i3.val - i1.val = 8) :
    ∃ (s : Slice Std.I32) (back : Slice Std.I32 → Arr256),
      CoreModels.core.Array.Insts.CoreOpsIndexIndexMut.index_mut
        (CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut
          (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I32))
        result { start := i1, «end» := i3 } = .ok (s, back)
      ∧ s.val = result.val.slice i1.val i3.val
      ∧ (∀ s' : Slice Std.I32, s'.val.length = 8 →
          (back s').val = result.val.setSlice! i1.val s'.val) := by
  have hslen : i3.val ≤ (Aeneas.Std.Array.to_slice_mut result).1.val.length := by
    rw [show (Aeneas.Std.Array.to_slice_mut result).1.val = result.val from rfl,
        show result.val.length = 256 from result.property]; exact h1
  obtain ⟨⟨sout, sback⟩, hslice_eq, hsout_val, hsout_len, hsback⟩ :=
    triple_exists_ok_cv (Util.SliceSpecs.core_models_Slice_Insts_index_mut_RangeUsize_spec
      (Aeneas.Std.Array.to_slice_mut result).1 { start := i1, «end» := i3 } h0 hslen)
  have hinner : Aeneas.Std.core.slice.index.Slice.index_mut
      (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I32)
      (Aeneas.Std.Array.to_slice_mut result).1 { start := i1, «end» := i3 }
      = .ok (sout, sback) := hslice_eq
  unfold CoreModels.core.Array.Insts.CoreOpsIndexIndexMut.index_mut
  -- Surface the inner `Slice.index_mut` with `.1`/`.2` explicit (the `CoreOpsIndexIndexMut`
  -- instance reduces to the `RangeUsize` one).
  show ∃ s back, (do
      let (out, to_slice) ← Aeneas.Std.core.slice.index.Slice.index_mut
          (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I32)
          (Aeneas.Std.Array.to_slice_mut result).1 { start := i1, «end» := i3 }
      Result.ok (out, fun o => (Aeneas.Std.Array.to_slice_mut result).2 (to_slice o)))
      = .ok (s, back) ∧ _ ∧ _
  rw [hinner]
  simp only [Aeneas.Std.bind_tc_ok]
  refine ⟨sout, _, rfl, ?_, ?_⟩
  · rw [hsout_val]; rfl
  · intro s' hs'_len
    show ((Aeneas.Std.Array.to_slice_mut result).2 (sback s')).val = _
    rw [show (Aeneas.Std.Array.to_slice_mut result).2 = result.from_slice from rfl]
    have hsback_val : (sback s').val = result.val.setSlice! i1.val s'.val := by
      rw [hsback s']; rfl
    have hlen256 : (sback s').val.length = 256 := by
      rw [hsback_val, List.setSlice!]
      have hrl : result.val.length = 256 := result.property
      simp only [List.length_append, List.length_take, List.length_drop, hrl]
      omega
    rw [Aeneas.Std.Array.from_slice_val result (sback s') (by rw [hlen256]; rfl)]
    exact hsback_val

/-- `to_coefficient_array value out` (at the instance) reduces to the declassified
    `to_slice value.values` (when `out` has length 8). -/
private theorem to_coefficient_array_eq (value : SU) (out : Slice Std.I32)
    (hout : out.val.length = 8) :
    simd.portable.vector_type.Coefficients.Insts.Libcrux_iot_ml_dsaSimdTraitsOperations.to_coefficient_array
        value out
      = .ok (Aeneas.Std.Array.to_slice value.values) := by
  show simd.portable.vector_type.to_coefficient_array value out = _
  unfold simd.portable.vector_type.to_coefficient_array
  unfold libcrux_secrets.SharedAT.Insts.Libcrux_secretsTraitsDeclassifyRefSharedAT.declassify_ref
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice value.values)
        = .ok (Aeneas.Std.Array.to_slice value.values) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  unfold CoreModels.core.slice.Slice.copy_from_slice
  rw [if_pos (by
        apply Std.UScalar.eq_of_val_eq
        rw [Aeneas.Std.Slice.len_val, Aeneas.Std.Slice.len_val,
            Aeneas.Std.Array.length_to_slice]
        show out.val.length = 8; rw [hout])]

/-- The body — defined as the extracted `to_i32_array_loop.body` at the instance,
    so the top-level FC needs no body bridge. The `to_body_{some,none}` lemmas
    `unfold` it to the do-block. -/
def to_body (iter : EnumIter) (result : Arr256) :
    Result (ControlFlow (EnumIter × Arr256) Arr256) :=
  polynomial.PolynomialRingElement.to_i32_array_loop.body portable_ops_inst iter result

/-- `to_body` on a nonempty suffix at count `c` pops the head unit, writes its
    8 declassified lanes into window `[8c, 8c+8)`, and continues with `tl`/`c+1`. -/
theorem to_body_some (suf : Slice SU) (c : Std.Usize) (result : Arr256)
    (hc_lt : c.val < 32) (hne : 0 < suf.val.length) :
    ∃ (tl : Slice SU) (c' : Std.Usize) (new_result : Arr256),
      tl.val = suf.val.drop 1 ∧ c'.val = c.val + 1 ∧
      new_result.val = result.val.setSlice! (8 * c.val) (suf.val[0]!).values.val ∧
      to_body { iter := suf, count := c } result
        = .ok (cont ({ iter := tl, count := c' }, new_result)) := by
  obtain ⟨tl, c', htl_val, hc'_val, hnext⟩ := enum_next_some suf c hne (by
    have : (32 : Nat) ≤ Std.Usize.max := by scalar_tac
    omega)
  -- Index arithmetic + the mutable-window index, computed upfront.
  have hmax8 : c.val * (8#usize : Std.Usize).val ≤ Std.Usize.max := by
    rw [show (8#usize : Std.Usize).val = 8 from rfl]
    have h1 : c.val * 8 ≤ 31 * 8 := Nat.mul_le_mul_right 8 (by omega)
    have h2 : (31 * 8 : Nat) ≤ Std.Usize.max := by scalar_tac
    omega
  obtain ⟨i1, hi1_eq, hi1_v⟩ := usize_mul_ok_eq c 8#usize hmax8
  have hi1_val : i1.val = 8 * c.val := by
    rw [hi1_v, show (8#usize : Std.Usize).val = 8 from rfl]; omega
  have hmaxa : c.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
    rw [show (1#usize : Std.Usize).val = 1 from rfl]
    have : (32 : Nat) ≤ Std.Usize.max := by scalar_tac
    omega
  obtain ⟨i2, hi2_eq, hi2_v⟩ := usize_add_ok_eq c 1#usize hmaxa
  have hi2_val : i2.val = c.val + 1 := by
    rw [hi2_v, show (1#usize : Std.Usize).val = 1 from rfl]
  have hmax3 : i2.val * (8#usize : Std.Usize).val ≤ Std.Usize.max := by
    rw [show (8#usize : Std.Usize).val = 8 from rfl, hi2_val]
    have h1 : (c.val + 1) * 8 ≤ 32 * 8 := Nat.mul_le_mul_right 8 (by omega)
    have h2 : (32 * 8 : Nat) ≤ Std.Usize.max := by scalar_tac
    omega
  obtain ⟨i3, hi3_eq, hi3_v⟩ := usize_mul_ok_eq i2 8#usize hmax3
  have hi3_val : i3.val = 8 * (c.val + 1) := by
    rw [hi3_v, hi2_val, show (8#usize : Std.Usize).val = 8 from rfl]; omega
  have h0_le : i1.val ≤ i3.val := by rw [hi1_val, hi3_val]; omega
  have hi3_le : i3.val ≤ 256 := by
    rw [hi3_val]; have : (c.val + 1) * 8 ≤ 32 * 8 := Nat.mul_le_mul_right 8 (by omega); omega
  have hwin : i3.val - i1.val = 8 := by rw [hi1_val, hi3_val]; omega
  obtain ⟨s, back, him_eq, hs_val, hback⟩ := arr_index_mut result i1 i3 h0_le hi3_le hwin
  have hs_len8 : s.val.length = 8 := by
    rw [hs_val, List.slice_length]
    have : result.val.length = 256 := result.property
    omega
  -- Provide the witnesses; new_result is the window-overwrite of `result`.
  refine ⟨tl, c', back (Aeneas.Std.Array.to_slice (suf.val[0]!).values),
    htl_val, hc'_val, ?_, ?_⟩
  · rw [hback (Aeneas.Std.Array.to_slice (suf.val[0]!).values) (suf.val[0]!).values.property,
        hi1_val]
    rfl
  · -- The body equation. After `rw [hnext]`, the literal pair-let `Some`-branch is
    -- defeq to the reduced body (with `i := c`, `simd_unit := suf[0]`); state it via `show`.
    unfold to_body polynomial.PolynomialRingElement.to_i32_array_loop.body
    rw [hnext]
    show (do
        let i1' ← c * simd.traits.COEFFICIENTS_IN_SIMD_UNIT
        let i2' ← c + 1#usize
        let i3' ← i2' * simd.traits.COEFFICIENTS_IN_SIMD_UNIT
        let (s', index_mut_back) ←
          core.Array.Insts.CoreOpsIndexIndexMut.index_mut
            (core.Slice.Insts.CoreOpsIndexIndexMut
            (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I32))
            result { start := i1', «end» := i3' }
        let s1 ← portable_ops_inst.to_coefficient_array (suf.val[0]!) s'
        Result.ok (cont (({ iter := tl, count := c' } : EnumIter), index_mut_back s1)))
        = .ok (cont ({ iter := tl, count := c' },
                     back (Aeneas.Std.Array.to_slice (suf.val[0]!).values)))
    rw [show simd.traits.COEFFICIENTS_IN_SIMD_UNIT = 8#usize by
          simp [simd.traits.COEFFICIENTS_IN_SIMD_UNIT]]
    rw [hi1_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [hi2_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [hi3_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [him_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [to_coefficient_array_eq (suf.val[0]!) s hs_len8]
    simp only [Aeneas.Std.bind_tc_ok]

/-- `to_body` on an empty suffix returns `done result`. -/
theorem to_body_none (suf : Slice SU) (c : Std.Usize) (result : Arr256)
    (he : suf.val.length = 0) :
    to_body { iter := suf, count := c } result = .ok (done result) := by
  unfold to_body polynomial.PolynomialRingElement.to_i32_array_loop.body
  rw [enum_next_none suf c he]
  rfl

set_option maxHeartbeats 4000000 in
/-- The `to_i32_array` loop, by induction on the remaining-suffix length `n`.
    Invariant: the consumed-prefix windows `[0, c)` of `result` already equal the
    corresponding units' lanes; the suffix is `units.val.drop c`. -/
theorem to_loop_spec (units : Std.Array SU 32#usize) :
    ∀ (n : Nat) (c : Std.Usize) (suf : Slice SU) (result : Arr256),
      suf.val.length = n →
      result.val.length = 256 →
      suf.val = units.val.drop c.val →
      c.val + n = 32 →
      (∀ j : Nat, j < c.val → ∀ ℓ : Nat, ℓ < 8 →
        (result.val[8 * j + ℓ]!).val = ((units.val[j]!).values.val[ℓ]!).val) →
      ⦃ ⌜ True ⌝ ⦄
      loop (fun (p : EnumIter × Arr256) => to_body p.1 p.2)
        (({ iter := suf, count := c } : EnumIter), result)
      ⦃ ⇓ r => ⌜ ∀ k : Nat, k < 256 →
                 (r.val[k]!).val = ((units.val[k / 8]!).values.val[k % 8]!).val ⌝ ⦄ := by
  intro n
  induction n with
  | zero =>
    intro c suf result hsuf_len hres_len hsuf_eq hcn hdone
    have hc_eq : c.val = 32 := by omega
    rw [loop.eq_def, to_body_none suf c result (by omega)]
    refine triple_of_ok_cv (v := result) rfl ?_
    intro k hk
    have hk8 : k / 8 < 32 := by omega
    have h := hdone (k / 8) (by rw [hc_eq]; exact hk8) (k % 8) (Nat.mod_lt k (by decide))
    rw [show 8 * (k / 8) + k % 8 = k from by omega] at h
    exact h
  | succ n ih =>
    intro c suf result hsuf_len hres_len hsuf_eq hcn hdone
    have hc_lt : c.val < 32 := by omega
    have hne : 0 < suf.val.length := by omega
    obtain ⟨tl, c', new_result, htl_val, hc'_val, hnr_val, hbody⟩ :=
      to_body_some suf c result hc_lt hne
    rw [loop.eq_def, hbody]
    -- the head unit = units[c].
    have hhead : suf.val[0]! = units.val[c.val]! := by
      rw [hsuf_eq, List.getElem!_eq_getElem?_getD, List.getElem?_drop,
          List.getElem!_eq_getElem?_getD]; simp
    -- New invariant: windows `[0, c+1)` correct.
    have hnew_done : ∀ j : Nat, j < c'.val → ∀ ℓ : Nat, ℓ < 8 →
        (new_result.val[8 * j + ℓ]!).val = ((units.val[j]!).values.val[ℓ]!).val := by
      intro j hj ℓ hℓ
      rw [hc'_val] at hj
      rw [hnr_val]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt | hj_eq
      · rw [List.getElem!_setSlice!_prefix result.val (suf.val[0]!).values.val
              (8 * c.val) (8 * j + ℓ) (by omega)]
        exact hdone j hj_lt ℓ hℓ
      · subst hj_eq
        rw [List.getElem!_setSlice!_middle result.val (suf.val[0]!).values.val
              (8 * c.val) (8 * c.val + ℓ)
              ⟨by omega,
               by rw [show (suf.val[0]!).values.val.length = 8 from (suf.val[0]!).values.property];
                  omega,
               by rw [hres_len]; omega⟩]
        rw [show 8 * c.val + ℓ - 8 * c.val = ℓ from by omega, hhead]
    -- Apply the IH at count c', suffix tl, accumulator new_result.
    exact ih c' tl new_result
      (by rw [htl_val, List.length_drop]; omega)
      (by
        rw [hnr_val, List.setSlice!]
        simp only [List.length_append, List.length_take, List.length_drop, hres_len]
        omega)
      (by
        rw [htl_val, hsuf_eq, List.drop_drop, hc'_val, show c.val + 1 = 1 + c.val from by omega])
      (by omega)
      hnew_done

end ToI32

set_option maxHeartbeats 8000000 in
/-- **`PolynomialRingElement.to_i32_array` at `portable_ops_inst`.** 32-unit
    `enumerate` loop; each unit's 8 declassified lanes are written into window
    `[i*8 .. i*8+8)` of the 256-array via the per-unit `to_coefficient_array`.
    Raw-value extraction post (equality-form). -/
@[spec]
theorem to_i32_array_fc (self : PRE) :
    ⦃ ⌜ True ⌝ ⦄
    polynomial.PolynomialRingElement.to_i32_array portable_ops_inst self
    ⦃ ⇓ r => ⌜ ∀ k : Nat, k < 256 →
                (r.val[k]!).val = (self.simd_units.val[k / 8]!).values.val[k % 8]!.val ⌝ ⦄ := by
  unfold polynomial.PolynomialRingElement.to_i32_array
  -- `lift (to_slice self.simd_units) = .ok (to_slice self.simd_units)`.
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice self.simd_units)
        = .ok (Aeneas.Std.Array.to_slice self.simd_units) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  -- `Slice.iter s = seq_from_slice s = .ok s`.
  rw [show CoreModels.core.slice.Slice.iter (Aeneas.Std.Array.to_slice self.simd_units)
        = .ok (Aeneas.Std.Array.to_slice self.simd_units) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  -- `enumerate i = .ok { iter := i, count := 0 }`.
  rw [show CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.enumerate
            (Aeneas.Std.Array.to_slice self.simd_units)
        = .ok { iter := Aeneas.Std.Array.to_slice self.simd_units, count := 0#usize } from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  unfold polynomial.PolynomialRingElement.to_i32_array_loop
  -- Bridge the extracted body to `to_body` (defeq: `to_body` IS the extracted body).
  have h_body_eq :
      (fun (p : EnumIter × Arr256) =>
        polynomial.PolynomialRingElement.to_i32_array_loop.body portable_ops_inst p.1 p.2)
      = (fun (p : EnumIter × Arr256) => to_body p.1 p.2) := rfl
  rw [h_body_eq]
  -- Run the loop induction from count 0, full suffix, all-zero `result`.
  apply to_loop_spec self.simd_units 32 0#usize
    (Aeneas.Std.Array.to_slice self.simd_units)
    (Array.repeat 256#usize (0#i32 : Std.I32))
  · show (Aeneas.Std.Array.to_slice self.simd_units).val.length = 32
    rw [show (Aeneas.Std.Array.to_slice self.simd_units).val = self.simd_units.val from rfl]
    exact self.simd_units.property
  · show (Array.repeat 256#usize (0#i32 : Std.I32)).val.length = 256
    rw [Array.repeat_val, List.length_replicate]
    rfl
  · show (Aeneas.Std.Array.to_slice self.simd_units).val = self.simd_units.val.drop 0
    rw [List.drop_zero]; rfl
  · rfl
  · intro j hj; exact absurd hj (Nat.not_lt_zero j)

/--
info: 'libcrux_iot_ml_dsa.Polynomial.Convert.to_i32_array_fc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms to_i32_array_fc

end libcrux_iot_ml_dsa.Polynomial.Convert
