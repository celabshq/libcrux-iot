/-
  # `Util/LoopSpecs.lean` — Generic Aeneas `loop` + iterator-range Triples

  Generic loop combinators:

  - `result_eq_of_triple` (re-exported from `Util.SliceSpecs`).
  - `IteratorRange_next_spec_i32` + `loop_range_spec_i32`.
  - `IteratorRange_next_spec_usize` + `loop_range_spec_usize`.
  - `array_from_fn_eq_unfold5` + the `bv_ofNat_eq_usize_lit_{0..4}` helpers.
-/
import LibcruxIotMlKem.Util.SliceSpecs
import Hax

open CoreModels Aeneas Aeneas.Std Result ControlFlow Std.Do

namespace libcrux_iot_ml_kem.Util.LoopSpecs
open libcrux_iot_ml_kem.Util.SliceSpecs
set_option mvcgen.warning false
set_option linter.unusedVariables false

/-! ## Re-export `result_eq_of_triple`

`Util.SliceSpecs` already proves this; we re-export the name into this
module's namespace so downstream `import Util.LoopSpecs` callers
automatically see it. -/

-- (`libcrux_iot_ml_kem.Util.SliceSpecs.result_eq_of_triple` is in scope via `Util.SliceSpecs`.)

/-! ## `Usize.val` conversion for small-Nat constants

The `array.from_fn` extraction uses raw `BitVec.ofNat _ n` for iteration
indices; we need to convert these to the standard `n#usize` form. -/

private theorem bv_ofNat_val_eq (n : Nat) (hn : n < 2^32) :
    (⟨BitVec.ofNat System.Platform.numBits n⟩ : Std.Usize).val = n := by
  show (BitVec.ofNat _ n).toNat = n
  simp only [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have h32 : (32 : Nat) ≤ System.Platform.numBits := by
    have := System.Platform.numBits_eq; omega
  calc n < 2^32 := hn
    _ ≤ 2^System.Platform.numBits := Nat.pow_le_pow_right (by decide) h32

private theorem bv_ofNat_eq_usize_lit_0 :
    (⟨BitVec.ofNat _ 0⟩ : Std.Usize) = 0#usize := by
  apply Std.UScalar.eq_of_val_eq; exact bv_ofNat_val_eq 0 (by omega)
private theorem bv_ofNat_eq_usize_lit_1 :
    (⟨BitVec.ofNat _ 1⟩ : Std.Usize) = 1#usize := by
  apply Std.UScalar.eq_of_val_eq; exact bv_ofNat_val_eq 1 (by omega)
private theorem bv_ofNat_eq_usize_lit_2 :
    (⟨BitVec.ofNat _ 2⟩ : Std.Usize) = 2#usize := by
  apply Std.UScalar.eq_of_val_eq; exact bv_ofNat_val_eq 2 (by omega)
private theorem bv_ofNat_eq_usize_lit_3 :
    (⟨BitVec.ofNat _ 3⟩ : Std.Usize) = 3#usize := by
  apply Std.UScalar.eq_of_val_eq; exact bv_ofNat_val_eq 3 (by omega)
private theorem bv_ofNat_eq_usize_lit_4 :
    (⟨BitVec.ofNat _ 4⟩ : Std.Usize) = 4#usize := by
  apply Std.UScalar.eq_of_val_eq; exact bv_ofNat_val_eq 4 (by omega)

/-! ## `array.from_fn 5` unfolding lemma

`rust_primitives.slice.array_from_fn 5#usize inst f0` unfolds to a chain
of 5 `inst.call_mut` calls building an `Array.make 5 [v0,v1,v2,v3,v4]`. -/

set_option maxHeartbeats 400000000 in
theorem array_from_fn_eq_unfold5
    {T F : Type} (inst : CoreModels.core.ops.function.FnMut F Std.Usize T) (f0 : F)
    (v0 v1 v2 v3 v4 : T) (f1 f2 f3 f4 f5 : F)
    (h0 : inst.call_mut f0 0#usize = .ok (v0, f1))
    (h1 : inst.call_mut f1 1#usize = .ok (v1, f2))
    (h2 : inst.call_mut f2 2#usize = .ok (v2, f3))
    (h3 : inst.call_mut f3 3#usize = .ok (v3, f4))
    (h4 : inst.call_mut f4 4#usize = .ok (v4, f5)) :
    rust_primitives.slice.array_from_fn 5#usize inst f0 =
      .ok (Std.Array.make 5#usize [v0, v1, v2, v3, v4]) := by
  have h_fold :
      List.foldlM
        (fun (s : List T × F) (i : Nat) => do
          let __discr ← inst.call_mut s.2 ⟨BitVec.ofNat _ i⟩
          match __discr with
          | (v, f') => Result.ok (s.1 ++ [v], f'))
        ([], f0) (List.range (5#usize).val)
      = .ok ([v0, v1, v2, v3, v4], f5) := by
    show List.foldlM _ ([], f0) (List.range 5) = _
    rw [show (List.range 5) = [0, 1, 2, 3, 4] from by decide]
    simp only [List.foldlM_cons, List.foldlM_nil,
               bv_ofNat_eq_usize_lit_0, bv_ofNat_eq_usize_lit_1,
               bv_ofNat_eq_usize_lit_2, bv_ofNat_eq_usize_lit_3,
               bv_ofNat_eq_usize_lit_4, h0, h1, h2, h3, h4, bind_tc_ok]
    rfl
  unfold rust_primitives.slice.array_from_fn
  split
  · rename_i e heq_match
    rw [h_fold] at heq_match
    exact absurd heq_match (by simp)
  · rename_i heq_match
    rw [h_fold] at heq_match
    exact absurd heq_match (by simp)
  · rename_i result heq_match
    rw [h_fold] at heq_match
    have hres : result = ([v0, v1, v2, v3, v4], f5) := (Result.ok.inj heq_match).symm
    subst hres
    rfl

/-! ## `Usize` iterator-next spec

The `Usize.Insts.CoreIterRangeStep` instance is an abbrev for
`core.iter.range.StepUsize` (see Aeneas-Std `FunsPrologue.lean`).

Splits on `i.val < e.val`: if so, returns `some i` plus the incremented
range; otherwise returns `none`. -/

theorem IteratorRange_next_spec_usize (i e : Std.Usize) {Q}
    (h_lt : (h : i.val < e.val) →
      ∀ (s : Std.Usize), s.val = i.val + 1 →
        (Q.1 (some i, { start := s, «end» := e })).down)
    (h_ge : i.val ≥ e.val →
      (Q.1 (none, { start := i, «end» := e })).down) :
    ⦃ ⌜ True ⌝ ⦄
    core.iter.range.IteratorRange.next
      core.Usize.Insts.CoreIterRangeStep
      { start := i, «end» := e }
    ⦃ Q ⦄ := by
  rcases lt_or_ge i.val e.val with hlt | hge
  · -- i < e: forward_checked succeeds with no overflow, start advances by 1.
    have hUB : i.val + 1 < 2 ^ System.Platform.numBits := by
      have he := e.hBounds
      rcases System.Platform.numBits_eq with hN | hN <;>
        simp only [Std.UScalarTy.Usize_numBits_eq, hN] at he <;>
        rw [hN] <;> omega
    have hno_ovf : BitVec.uaddOverflow i.bv (1#System.Platform.numBits) = false := by
      have h1 : (1#System.Platform.numBits : BitVec _).toNat = 1 := by
        rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> rfl
      simp [BitVec.uaddOverflow, h1, hUB]
    have h_eq :
        CoreModels.core.iter.range.IteratorRange.next
          CoreModels.core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e }
        = .ok (CoreModels.core.option.Option.Some i,
               { start := ⟨i.bv + 1#System.Platform.numBits⟩, «end» := e }) := by
      unfold CoreModels.core.iter.range.IteratorRange.next
      simp only [                 CoreModels.core.Usize.Insts.CoreCmpPartialOrdUsize,
                 CoreModels.core.mkUPartialOrd,
                                  CoreModels.core.Usize.Insts.CoreCloneClone.clone,
                 CoreModels.core.Usize.Insts.CoreIterRangeStep.forward_checked,
                 CoreModels.core.convert.TryFromUTInfallible.Blanket.try_from,
                                  CoreModels.core.convert.From.Blanket.from,
                 CoreModels.core.num.Usize.checked_add,
                 CoreModels.core.num.Usize.overflowing_add,
                 CoreModels.rust_primitives.arithmetic.overflowing_add_usize,
                 Std.UScalar.overflowing_add]
      have hcmp : compare i.val e.val = Ordering.lt := by
        rw [Nat.compare_eq_lt]; exact hlt
      simp [hcmp, hno_ovf]
    rw [h_eq]
    have h_step : (⟨i.bv + 1#System.Platform.numBits⟩ : Std.Usize).val = i.val + 1 := by
      show (i.bv + 1#System.Platform.numBits).toNat = i.val + 1
      rw [BitVec.toNat_add]
      have h1 : (1#System.Platform.numBits : BitVec _).toNat = 1 := by
        rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> rfl
      rw [h1]
      show (i.bv.toNat + 1) % _ = i.val + 1
      exact Nat.mod_eq_of_lt hUB
    simp [Triple, WP.wp, PredTrans.apply]
    exact h_lt hlt _ h_step
  · -- i ≥ e: next returns none.
    have h_eq :
        CoreModels.core.iter.range.IteratorRange.next
          CoreModels.core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e }
        = .ok (CoreModels.core.option.Option.None, { start := i, «end» := e }) := by
      unfold CoreModels.core.iter.range.IteratorRange.next
      simp only [                 CoreModels.core.Usize.Insts.CoreCmpPartialOrdUsize,
                 CoreModels.core.mkUPartialOrd]
      have hcmp : compare i.val e.val ≠ Ordering.lt := by
        intro h; rw [Nat.compare_eq_lt] at h; omega
      cases h : compare i.val e.val <;> simp_all
    rw [h_eq]
    simp [Triple, WP.wp, PredTrans.apply]
    exact h_ge hge

/-! ## `Usize` loop-over-range spec

Specialized to `loop` over `core.ops.range.Range Usize`. An invariant
`inv : Usize → β → Result Prop` is preserved by each step. Induction on
`(e.val - start.val)`. -/

section loop_range_usize_helpers

private abbrev ResultPSU := PostShape.except Error (PostShape.except PUnit PostShape.pure)

private theorem triple_noThrow_elim_usize {α : Type} {x : Result α} {Q : α → Assertion ResultPSU}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) {v : α} (hv : x = ok v) :
    (Q v).down := by
  subst hv; simpa [Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h

private theorem triple_noThrow_exists_ok_usize {α : Type} {x : Result α}
    {Q : α → Assertion ResultPSU}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) : ∃ v, x = ok v := by
  match x, h with
  | .ok v, _ => exact ⟨v, rfl⟩
  | .fail _, h => exact absurd h (by simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div, h => exact absurd h (by simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

private theorem triple_of_ok_usize {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = ok v) (hp : P v) :
    (⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) := by
  subst hx; simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

end loop_range_usize_helpers

set_option maxHeartbeats 2000000 in
theorem loop_range_spec_usize {β : Type}
    (body : (CoreModels.core.ops.range.Range Std.Usize × β) →
      Result (ControlFlow (CoreModels.core.ops.range.Range Std.Usize × β) β))
    (init : β) (s e : Std.Usize) (inv : Std.Usize → β → Result Prop)
    (h_le : s.val ≤ e.val)
    (h_init : (inv s init).holds)
    (h_step : ∀ acc (i : Std.Usize), s.val ≤ i.val → i.val ≤ e.val →
      (inv i acc).holds →
      ⦃ ⌜ True ⌝ ⦄
      body ({ start := i, «end» := e }, acc)
      ⦃ ⇓ r => match r with
        | .cont (iter', acc') =>
          ⌜ i.val < e.val ∧ iter'.«end» = e ∧ iter'.start.val = i.val + 1
            ∧ (inv iter'.start acc').holds ⌝
        | .done y => ⌜ (inv e y).holds ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    loop body ({ start := s, «end» := e }, init)
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ := by
  suffices gen : ∀ (n : Nat) (acc : β) (start : Std.Usize),
    e.val - start.val = n →
    s.val ≤ start.val → start.val ≤ e.val →
    (inv start acc).holds →
    ⦃ ⌜ True ⌝ ⦄ loop body ({ start := start, «end» := e }, acc)
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ by
    exact gen _ init s rfl (Nat.le_refl _) h_le h_init
  intro n
  induction n with
  | zero =>
    intro acc start hn hs_le hse_le hinv
    have hs := h_step acc start hs_le hse_le hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok_usize hs
    have hpost := triple_noThrow_elim_usize hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .cont (iter', acc') =>
      simp at hpost; exact absurd hpost.1 (by omega)
    | .done y =>
      simp at hpost; exact triple_of_ok_usize rfl hpost
  | succ n ih =>
    intro acc start hn hs_le hse_le hinv
    have hs := h_step acc start hs_le hse_le hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok_usize hs
    have hpost := triple_noThrow_elim_usize hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .done y =>
      simp at hpost; exact triple_of_ok_usize rfl hpost
    | .cont (iter', acc') =>
      simp at hpost
      obtain ⟨hlt, hend, hstart, hinv'⟩ := hpost
      have hiter : iter' = { start := iter'.start, «end» := e } := by
        cases iter'; cases hend; rfl
      rw [hiter]
      exact ih acc' iter'.start
        (by rw [hstart]; omega) (by rw [hstart]; omega) (by rw [hstart]; omega) hinv'

/-! ## `I32` iterator-next spec

The `core.I32.Insts.CoreIterRangeStep` instance uses
`IScalar.tryMk .I32 (start.val + 1)` for `forward_checked`. For ranges
within `[-2^31, 2^31)` this always succeeds. -/

theorem IteratorRange_next_spec_i32 (i e : Std.I32)
    (h_e_lt_max : e.val < 2^31) {Q}
    (h_lt : (h : i.val < e.val) →
      ∀ (s : Std.I32), s.val = i.val + 1 →
        (Q.1 (some i, { start := s, «end» := e })).down)
    (h_ge : i.val ≥ e.val →
      (Q.1 (none, { start := i, «end» := e })).down) :
    ⦃ ⌜ True ⌝ ⦄
    core.iter.range.IteratorRange.next core.I32.Insts.CoreIterRangeStep
      { start := i, «end» := e }
    ⦃ Q ⦄ := by
  rcases lt_or_ge i.val e.val with hlt | hge
  · -- i < e: forward_checked succeeds with no overflow, start advances by 1.
    have hcmp : compare i.val e.val = Ordering.lt := Int.compare_eq_lt.mpr hlt
    have hmin : (-2147483648 : Int) ≤ i.val := by scalar_tac
    have h1val : (Std.UScalar.hcast Std.IScalarTy.I32
                    (Std.UScalar.cast Std.UScalarTy.U32 1#usize)).val = 1 := by
      simp only [Std.UScalar.hcast, Std.UScalar.cast, Std.IScalarTy.I32_numBits_eq,
                 Std.UScalarTy.U32_numBits_eq]
      simp; decide
    have hwval : (Std.I32.wrapping_add i
        (Std.UScalar.hcast Std.IScalarTy.I32
          (Std.UScalar.cast Std.UScalarTy.U32 1#usize))).val = i.val + 1 := by
      rw [Std.I32.wrapping_add_val_eq, h1val, Int.bmod_eq_emod]
      simp only [Nat.reducePow]
      split <;> omega
    have hbmod : ((i.val : Int) + 1).bmod 4294967296 = i.val + 1 := by
      rw [Int.bmod_eq_emod]; split <;> omega
    have htry : CoreModels.core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from 1#usize
        = .ok (CoreModels.core.result.Result.Ok
                 (Std.UScalar.cast Std.UScalarTy.U32 1#usize)) := by
      unfold CoreModels.core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
      simp [Aeneas.Std.lift, Std.U32.rMax]
    have h_eq : CoreModels.core.iter.range.IteratorRange.next
        CoreModels.core.I32.Insts.CoreIterRangeStep { start := i, «end» := e }
      = .ok (CoreModels.core.option.Option.Some i,
             { start := Std.I32.wrapping_add i
                 (Std.UScalar.hcast Std.IScalarTy.I32
                   (Std.UScalar.cast Std.UScalarTy.U32 1#usize)),
               «end» := e }) := by
      unfold CoreModels.core.iter.range.IteratorRange.next
      simp [CoreModels.core.I32.Insts.CoreCmpPartialOrdI32,
            CoreModels.core.mkIPartialOrd,
            CoreModels.core.I32.Insts.CoreCloneClone.clone,
            CoreModels.core.I32.Insts.CoreIterRangeStep.forward_checked,
            CoreModels.core.num.I32.wrapping_add,
            CoreModels.rust_primitives.arithmetic.wrapping_add_i32,
            Aeneas.Std.lift, hcmp, htry, h1val, hbmod]
    rw [h_eq]
    simp [Triple, WP.wp, PredTrans.apply]
    exact h_lt hlt _ hwval
  · -- i ≥ e: next returns none.
    have h_eq : CoreModels.core.iter.range.IteratorRange.next
        CoreModels.core.I32.Insts.CoreIterRangeStep { start := i, «end» := e }
      = .ok (CoreModels.core.option.Option.None, { start := i, «end» := e }) := by
      unfold CoreModels.core.iter.range.IteratorRange.next
      simp only [CoreModels.core.I32.Insts.CoreCmpPartialOrdI32,
                 CoreModels.core.mkIPartialOrd]
      have hcmp : compare i.val e.val ≠ Ordering.lt := Int.compare_ne_lt.mpr hge
      cases h : compare i.val e.val <;> simp_all
    rw [h_eq]
    simp [Triple, WP.wp, PredTrans.apply]
    exact h_ge hge

/-! ## `I32` loop-over-range spec

Specialized to `loop` over `core.ops.range.Range I32`. Same shape as the
`Usize` version. -/

section loop_range_i32_helpers

private abbrev ResultPS := PostShape.except Error (PostShape.except PUnit PostShape.pure)

private theorem triple_noThrow_elim_i32 {α : Type} {x : Result α} {Q : α → Assertion ResultPS}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) {v : α} (hv : x = ok v) :
    (Q v).down := by
  subst hv; simpa [Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h

private theorem triple_noThrow_exists_ok_i32 {α : Type} {x : Result α}
    {Q : α → Assertion ResultPS}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) : ∃ v, x = ok v := by
  match x, h with
  | .ok v, _ => exact ⟨v, rfl⟩
  | .fail _, h => exact absurd h (by simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div, h => exact absurd h (by simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

private theorem triple_of_ok_i32 {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = ok v) (hp : P v) :
    (⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) := by
  subst hx; simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

end loop_range_i32_helpers

set_option maxHeartbeats 2000000 in
theorem loop_range_spec_i32 {β : Type}
    (body : (CoreModels.core.ops.range.Range Std.I32 × β) →
      Result (ControlFlow (CoreModels.core.ops.range.Range Std.I32 × β) β))
    (init : β) (s e : Std.I32) (inv : Std.I32 → β → Result Prop)
    (h_le : s.val ≤ e.val)
    (h_init : (inv s init).holds)
    (h_step : ∀ acc (i : Std.I32), s.val ≤ i.val → i.val ≤ e.val →
      (inv i acc).holds →
      ⦃ ⌜ True ⌝ ⦄
      body ({ start := i, «end» := e }, acc)
      ⦃ ⇓ r => match r with
        | .cont (iter', acc') =>
          ⌜ i.val < e.val ∧ iter'.«end» = e ∧ iter'.start.val = i.val + 1
            ∧ (inv iter'.start acc').holds ⌝
        | .done y => ⌜ (inv e y).holds ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    loop body ({ start := s, «end» := e }, init)
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ := by
  -- Generalize over the current iteration's `start` and induct on the number
  -- of remaining steps `n = (e.val - start.val).toNat`.
  suffices gen : ∀ (n : Nat) (acc : β) (start : Std.I32),
    (e.val - start.val).toNat = n →
    s.val ≤ start.val → start.val ≤ e.val →
    (inv start acc).holds →
    ⦃ ⌜ True ⌝ ⦄ loop body ({ start := start, «end» := e }, acc)
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ by
    exact gen _ init s rfl (Int.le_refl _) h_le h_init
  intro n
  induction n with
  | zero =>
    intro acc start hn hs_le hse_le hinv
    have hs := h_step acc start hs_le hse_le hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok_i32 hs
    have hpost := triple_noThrow_elim_i32 hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .cont (iter', acc') =>
      simp at hpost; exact absurd hpost.1 (by omega)
    | .done y =>
      simp at hpost; exact triple_of_ok_i32 rfl hpost
  | succ n ih =>
    intro acc start hn hs_le hse_le hinv
    have hs := h_step acc start hs_le hse_le hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok_i32 hs
    have hpost := triple_noThrow_elim_i32 hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .done y =>
      simp at hpost; exact triple_of_ok_i32 rfl hpost
    | .cont (iter', acc') =>
      simp at hpost
      obtain ⟨hlt, hend, hstart, hinv'⟩ := hpost
      have hiter : iter' = { start := iter'.start, «end» := e } := by
        cases iter'; cases hend; rfl
      rw [hiter]
      exact ih acc' iter'.start
        (by rw [hstart]; omega) (by rw [hstart]; omega) (by rw [hstart]; omega) hinv'

end libcrux_iot_ml_kem.Util.LoopSpecs