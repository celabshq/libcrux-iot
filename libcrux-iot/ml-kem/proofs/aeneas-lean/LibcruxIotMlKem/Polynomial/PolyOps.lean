/-
  # `Equivalence/L6_PolyOps.lean` — Layer 6 polynomial-composite Triples.

  L6.1: `PolynomialRingElement_poly_barrett_reduce_spec` — wraps L1.3
  `barrett_reduce_spec` across the 16 PortableVectors of a
  `PolynomialRingElement`. The impl is a 16-iter loop over
  `self.coefficients` that dispatches the trait method
  `Vector::barrett_reduce` on each lane.

  Specialised to `Vector := PortableVector` with the concrete
  `Libcrux_iot_ml_kemVectorTraitsOperations` instance. The instance's
  `barrett_reduce` field (`@[reducible]`) reduces to
  `vector.portable.arithmetic.barrett_reduce`, which is L1.3's target.
-/
import LibcruxIotMlKem.Extraction.Funs
import LibcruxIotMlKem.Util.LoopSpecs
import LibcruxIotMlKem.Vector.Portable.Arithmetic.LoopHelper
import LibcruxIotMlKem.Vector.Portable.Arithmetic.Element

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_kem.Polynomial.PolyOps
open libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement
open CoreModels Aeneas Aeneas.Std Result ControlFlow Std.Do
open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper

/-! ## Inhabited instances — needed for `.val[j]!` projections on
    `Array PortableVector 16`. Mirror the locally-registered instances
    in `L3_NTTDrivers.lean`. Declared `local` to avoid colliding with
    L3's identically-named auto-generated instance constants when both
    files are imported by the project root. -/

local instance instInhabitedPortableVector_l6 :
    Inhabited libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
  ⟨{ elements := Std.Array.make 16#usize (List.replicate 16 (0#i16 : Std.I16))
        (by simp) }⟩

local instance instInhabitedPolynomialRingElement_l6 {Vector : Type} [Inhabited Vector] :
    Inhabited (libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector) :=
  ⟨{ coefficients := Std.Array.make 16#usize (List.replicate 16 default) (by simp) }⟩

/-! ## Local helpers — Triple ↔ Result.ok bridges, pure-prop holds.

Mirror the `triple_of_ok_l3` / `triple_exists_ok_l3` / `pure_prop_holds_l3`
family used by `L3_NTTDrivers.lean`. Each phase file carries its own copy
with a phase-local suffix to avoid cross-file shadowing. -/

private theorem triple_of_ok_l6 {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

private theorem triple_exists_ok_l6 {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl, (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

private theorem pure_prop_holds_l6 {P : Prop} (h : P) : (pure P : Result Prop).holds := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp]; intro _; exact h

private theorem of_pure_prop_holds_l6 {P : Prop}
    (h : (pure P : Result Prop).holds) : P := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp] at h; exact h trivial

/-! ## L6.1 — `PolynomialRingElement_poly_barrett_reduce_spec`

Driver loop: 16 iterations over `self.coefficients`. Each iteration reads
`self.coefficients[k]` (a `PortableVector`), dispatches
`OpsInst.barrett_reduce` (reduces via `@[reducible]` to
`vector.portable.arithmetic.barrett_reduce`, to which L1.3 applies), and
writes the reduced vector back.

Per-vector bound `≤ 32767` (L1.3 input) → `≤ 3328` (L1.3 output).

Loop invariant after `k` iterations (`k.val ∈ [0, 16]`), state `acc`:
  - For `j < k.val`, all 16 elements of `acc.coefficients[j]` are
    bounded by `3328`.
  - For `j ≥ k.val`, `acc.coefficients[j] = re.coefficients[j]` (so the
    L1.3 precondition `≤ 32767` is inherited from `h_pre`). -/

namespace BarrettReduce

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Result ControlFlow

/-- Step-local accumulator type. -/
abbrev Acc :=
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- Loop invariant. -/
def inv
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    (∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 3328)
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.coefficients.val[j]! = re.coefficients.val[j]!))

/-- Step post (named to keep the `match` constant canonical across sites). -/
def step_post
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv re iter'.start acc').holds
  | .done y => (inv re 16#usize y).holds

end BarrettReduce

/-- Per-iteration step lemma: each body call transforms
    `acc.coefficients[k]` from a `≤ 32767` PortableVector (via h_pre +
    h_acc_undone) to a `≤ 3328` one, leaves other indices untouched. -/
private theorem poly_barrett_reduce_step_lemma
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 32767)
    (acc : BarrettReduce.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_acc_done : ∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 3328)
    (h_acc_undone : ∀ j : Nat, k.val ≤ j → j < 16 →
        acc.coefficients.val[j]! = re.coefficients.val[j]!) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce_loop.body
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      { start := k, «end» := 16#usize } acc
    ⦃ ⇓ r => ⌜ BarrettReduce.step_post re k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.coefficients.length = 16 :=
    Std.Array.length_eq _
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- Some round = k branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k h_lt
    -- 1) `Array.index_mut_usize acc.coefficients k`.
    have h_idx :
        Aeneas.Std.Array.index_usize acc.coefficients k
          = .ok (acc.coefficients.val[k.val]!) :=
      array_index_usize_ok_eq acc.coefficients k (by rw [h_coef_len]; exact hk_16)
    have h_imt_ok :
        Aeneas.Std.Array.index_mut_usize acc.coefficients k
          = .ok (acc.coefficients.val[k.val]!, acc.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx]
      rfl
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.coefficients.val[k.val]! with ht_def
    -- 2) `OpsInst.barrett_reduce t`. The instance's `@[reducible]` field
    -- forwards to `vector.portable.arithmetic.barrett_reduce`, to which
    -- L1.3 applies. Pre: t's elements ≤ 32767 (it's
    -- `re.coefficients[k]` via h_acc_undone + h_pre).
    have h_t_eq : t = re.coefficients.val[k.val]! := by
      show acc.coefficients.val[k.val]! = re.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 32767 := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_pre k.val hk_16 ℓ hℓ
    obtain ⟨t1, h_t1_eq, h_t1_P⟩ :=
      triple_exists_ok_l6 (barrett_reduce_spec t h_t_bd)
    -- h_t1_P : ∀ i : Nat, i < 16 → modq_eq … ∧ (t1.elements[i]).val.natAbs ≤ 1664
    -- (centered); this L6.1 wrapper keeps the looser `≤ 3328`, so weaken.
    have h_t1_bd : ∀ ℓ : Nat, ℓ < 16 →
        (t1.elements.val[ℓ]!).val.natAbs ≤ 3328 :=
      fun ℓ hℓ => Nat.le_trans (h_t1_P ℓ hℓ).2 (by decide)
    -- Set the next-state accumulator.
    set a : Std.Array
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.coefficients.set k t1 with ha_def
    set acc' : BarrettReduce.Acc := ({ coefficients := a } : BarrettReduce.Acc) with hacc'_def
    -- Compose the whole body into one `.ok` equation.
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc
        = .ok (cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                     acc')) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce_loop.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp [bind_tc_ok, h_imt_ok]
      -- After simp, only the barrett_reduce call remains. The trait
      -- instance's field is `@[reducible]` and forwards to
      -- `vector.portable.arithmetic.barrett_reduce`; force-reduce via
      -- `show`, then close via `h_t1_eq`.
      show (do
            let t1' ←
              libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce t
            ok (cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                      ({ coefficients := acc.coefficients.set k t1' }
                        : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            = _
      rw [h_t1_eq]
      rfl
    apply triple_of_ok_l6 h_body
    show BarrettReduce.step_post re k
      (.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
              acc'))
    unfold BarrettReduce.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    -- Now: invariant at (s, acc').
    apply pure_prop_holds_l6
    -- Two conjuncts of BarrettReduce.inv at (s, acc').
    refine ⟨?_, ?_⟩
    · -- All j < s.val are bounded by 3328.
      intro j hj ℓ hℓ
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · -- j < k.val: unchanged by the set, use h_acc_done.
        have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_set_ne :
            (acc.coefficients.set k t1)[j]! = (acc.coefficients)[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc.coefficients k j t1 h_ne
        have h_set_ne_val :
            (acc.coefficients.set k t1).val[j]! = acc.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
        show ((acc.coefficients.set k t1).val[j]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_ne_val]
        exact h_acc_done j hj_lt_k ℓ hℓ
      · -- j = k.val: it's t1.
        subst hj_eq_k
        have h_lt' : k.val < acc.coefficients.length := by
          rw [h_coef_len]; exact hk_16
        have h_set_eq :
            (acc.coefficients.set k t1)[k.val]! = t1 :=
          Aeneas.Std.Array.getElem!_Nat_set_eq acc.coefficients k k.val t1
            ⟨rfl, h_lt'⟩
        have h_set_eq_val :
            (acc.coefficients.set k t1).val[k.val]! = t1 := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
        show ((acc.coefficients.set k t1).val[k.val]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_eq_val]
        exact h_t1_bd ℓ hℓ
    · -- All j ≥ s.val are unchanged.
      intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_ne : k.val ≠ j := by omega
      have h_ge' : k.val ≤ j := by omega
      have h_set_ne :
          (acc.coefficients.set k t1)[j]! = (acc.coefficients)[j]! :=
        Aeneas.Std.Array.getElem!_Nat_set_ne acc.coefficients k j t1 h_ne
      have h_set_ne_val :
          (acc.coefficients.set k t1).val[j]! = acc.coefficients.val[j]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
      show (acc.coefficients.set k t1).val[j]! = re.coefficients.val[j]!
      rw [h_set_ne_val]
      exact h_acc_undone j h_ge' hj_lt
  · -- None branch (k ≥ 16).
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc
        = .ok (done acc) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce_loop.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    apply triple_of_ok_l6 h_body
    show BarrettReduce.step_post re k (.done acc)
    unfold BarrettReduce.step_post
    show (BarrettReduce.inv re 16#usize acc).holds
    apply pure_prop_holds_l6
    refine ⟨?_, ?_⟩
    · intro j hj ℓ hℓ; rw [h16] at hj
      apply h_acc_done j _ ℓ hℓ; rw [hk_eq]; exact hj
    · intro j hj_ge hj_lt; rw [h16] at hj_ge
      apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge

set_option maxHeartbeats 16000000 in
@[spec]
theorem PolynomialRingElement_poly_barrett_reduce_spec
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 32767) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      re
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                ((r.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3328 ⌝ ⦄ := by
  -- Reduce the top wrapper to the inner loop.
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce
  -- `VECTORS_IN_RING_ELEMENT` reduces to `.ok 16#usize`.
  have h_vire : libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
                  = .ok (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
    rfl
  rw [h_vire]
  simp only [bind_tc_ok]
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          iter1 acc1)
      (β := BarrettReduce.Acc)
      re
      0#usize 16#usize
      (BarrettReduce.inv re)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (pure_prop_holds_l6 ⟨
        fun j hj _ _ => absurd hj (Nat.not_lt_zero j),
        fun _ _ _ => rfl⟩)
      ?_)
  · -- Post entailment.
    rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_done, _h_undone⟩ := of_pure_prop_holds_l6 h
    intro i hi j hj
    apply h_done i (by rw [show (16#usize : Std.Usize).val = 16 from rfl]; exact hi) j hj
  · -- Step lemma application.
    intro acc k h_ge h_le hinv
    obtain ⟨h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_l6 hinv
    have h_step := poly_barrett_reduce_step_lemma re h_pre acc k h_le
        h_acc_done h_acc_undone
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : BarrettReduce.step_post re k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [BarrettReduce.step_post] using hP
    · have hP : BarrettReduce.step_post re k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [BarrettReduce.step_post] using hP

end libcrux_iot_ml_kem.Polynomial.PolyOps