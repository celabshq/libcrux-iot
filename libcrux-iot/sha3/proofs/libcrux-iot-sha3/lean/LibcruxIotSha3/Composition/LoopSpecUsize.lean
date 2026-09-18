/-
  Loop-spec infrastructure for `Usize` ranges, plus a structural-unfolding
  helper for `array.from_fn` over small `N`.

  The implementation's `keccakf1600` iterates over an `I32` range (handled by
  `Foundation/I32LoopSpec.lean`); the round chain and the sponge loops iterate
  over `Usize` ranges.  This file is the `Usize` half: the iterator-`next`
  equations and the `loop`-over-range Hoare rule everything above reuses.
-/
import LibcruxIotSha3.Composition.ViaBit
import LibcruxIotSha3.Foundation.I32LoopSpec

open Aeneas Aeneas.Std RustM ControlFlow Std.Do libcrux_iot_sha3
open libcrux_iot_sha3.Foundation

namespace libcrux_iot_sha3.Composition

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-! ## Helper: `Usize.val` conversion for small-Nat constants

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

`CoreModels.rust_primitives.slice.array_from_fn 5#usize inst f0` unfolds to a chain
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
    CoreModels.rust_primitives.slice.array_from_fn 5#usize inst f0 =
      .ok (Std.Array.make 5#usize [v0, v1, v2, v3, v4]) := by
  -- CoreModels v0.3.12 implements `array_from_fn` as a structural recursion
  -- (`array_from_fn_go`) followed by a length-guarded `if`, where it used to be a
  -- `List.foldlM`; the characterization below is phrased over the new shape.
  have h_go :
      CoreModels.rust_primitives.slice.array_from_fn_go inst f0 (5#usize).val
        = .ok ([v0, v1, v2, v3, v4], f5) := by
    show CoreModels.rust_primitives.slice.array_from_fn_go inst f0 5 = _
    simp only [CoreModels.rust_primitives.slice.array_from_fn_go,
               bv_ofNat_eq_usize_lit_0, bv_ofNat_eq_usize_lit_1,
               bv_ofNat_eq_usize_lit_2, bv_ofNat_eq_usize_lit_3,
               bv_ofNat_eq_usize_lit_4, h0, h1, h2, h3, h4, bind_tc_ok]
    -- `array_from_fn_go` accumulates with `++`, so the list arrives as
    -- `[] ++ [v0] ++ .. ++ [v4]`.
    simp
  unfold CoreModels.rust_primitives.slice.array_from_fn
  rw [h_go]
  simp only [bind_tc_ok]
  rw [dif_pos (by simp : ([v0, v1, v2, v3, v4] : List T).length = (5#usize).val)]
  rfl

/-! ## `Usize` iterator-next spec (analog of `IteratorRange_next_spec_i32`)

The round chain and the sponge loops iterate `Usize` indices over a range.
The `Usize.Insts.CoreIterRangeStep` instance is an
abbrev for `CoreModels.core.iter.range.StepUsize` (see `FunsPrologue.lean`). -/

theorem IteratorRange_next_spec_usize (i e : Std.Usize) {Q}
    (h_lt : (h : i.val < e.val) →
      ∀ (s : Std.Usize), s.val = i.val + 1 →
        (Q.1 (some i, { start := s, «end» := e })).down)
    (h_ge : i.val ≥ e.val →
      (Q.1 (none, { start := i, «end» := e })).down) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.iter.range.IteratorRange.next
      CoreModels.core.Usize.Insts.CoreIterRangeStep
      { start := i, «end» := e }
    ⦃ Q ⦄ := by
  rcases lt_or_ge i.val e.val with hlt | hge
  · -- i < e case: derive an `ok` form, then close
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
      -- `iter.range.IteratorRange.next` is only an `abbrev` for
      -- `CoreModels.core.IteratorRange.next` as of CoreModels v0.3.12, so
      -- unfolding the alias alone leaves the body untouched.
      unfold CoreModels.core.iter.range.IteratorRange.next
             CoreModels.core.IteratorRange.next
      simp only [CoreModels.core.Usize.Insts.CoreCmpPartialOrdUsize,
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
  · -- i ≥ e case
    have h_eq :
        CoreModels.core.iter.range.IteratorRange.next
          CoreModels.core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e }
        = .ok (CoreModels.core.option.Option.None, { start := i, «end» := e }) := by
      -- `iter.range.IteratorRange.next` is only an `abbrev` for
      -- `CoreModels.core.IteratorRange.next` as of CoreModels v0.3.12, so
      -- unfolding the alias alone leaves the body untouched.
      unfold CoreModels.core.iter.range.IteratorRange.next
             CoreModels.core.IteratorRange.next
      simp only [CoreModels.core.Usize.Insts.CoreCmpPartialOrdUsize,
                 CoreModels.core.mkUPartialOrd]
      have hcmp : compare i.val e.val ≠ Ordering.lt := by
        intro h; rw [Nat.compare_eq_lt] at h; omega
      cases h : compare i.val e.val <;> simp_all
    rw [h_eq]
    simp [Triple, WP.wp, PredTrans.apply]
    exact h_ge hge
/-! ## `Usize` loop-over-range spec (analog of `loop_range_spec_i32`)

Specialized to `loop` over `core.ops.range.Range Usize`. Same shape as the
`I32` version: an invariant `inv : Usize → β → RustM Prop` is preserved by
each step. Induction on `(e.val - start.val).toNat`. -/

section loop_range_usize_helpers

private abbrev ResultPSU := PostShape.except Error (PostShape.except PUnit PostShape.pure)

private theorem triple_noThrow_elim_usize {α : Type} {x : RustM α} {Q : α → Assertion ResultPSU}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) {v : α} (hv : x = ok v) :
    (Q v).down := by
  subst hv; simpa [Triple, WP.wp, PredTrans.apply] using h

private theorem triple_noThrow_exists_ok_usize {α : Type} {x : RustM α}
    {Q : α → Assertion ResultPSU}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) : ∃ v, x = ok v := by
  match x, h with
  | .ok v, _ => exact ⟨v, rfl⟩
  | .fail _, h => exact absurd h (by simp [Triple, WP.wp, PredTrans.apply])
  | .div, h => exact absurd h (by simp [Triple, WP.wp, PredTrans.apply])

private theorem triple_of_ok_usize {α : Type} {x : RustM α} {v : α} {P : α → Prop}
    (hx : x = ok v) (hp : P v) :
    (⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) := by
  subst hx; simp [Triple, WP.wp, PredTrans.apply, hp]

end loop_range_usize_helpers

set_option maxHeartbeats 2000000 in
theorem loop_range_spec_usize {β : Type}
    (body : (CoreModels.core.ops.range.Range Std.Usize × β) →
      RustM (ControlFlow (CoreModels.core.ops.range.Range Std.Usize × β) β))
    (init : β) (s e : Std.Usize) (inv : Std.Usize → β → RustM Prop)
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


end libcrux_iot_sha3.Composition
