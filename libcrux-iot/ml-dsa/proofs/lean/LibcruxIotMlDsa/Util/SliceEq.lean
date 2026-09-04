/-
  # `Util/SliceEq.lean` — a spec for `core::cmp::PartialEq for [T]`

  Port of sha3's `Composition/SliceEq.lean` (verbatim proof, ml-dsa's
  `Util/LoopSpecs` supplies the identical `loop_range_spec_usize` /
  `IteratorRange_next_spec_usize`): CoreModels implements slice equality as an
  actual loop and ships no spec lemma for it, so anything that writes `a == b`
  on slices extracts to something no tactic can see through. ml-dsa hits it in
  `from_i32_array`'s generated post (`&raw_gather(future(result))[..] ==
  array.declassify_ref()`).

  This is a CoreModels-level fact, not a libcrux-iot one — it belongs upstream
  next to the definition. It lives here until then (in TWO trees now; one more
  reason to move it).
-/
import LibcruxIotMlDsa.Util.LoopSpecs

open Aeneas Aeneas.Std RustM ControlFlow Std.Do
open CoreModels

namespace libcrux_iot_ml_dsa.Util.SliceEq

open libcrux_iot_ml_dsa.Util.LoopSpecs

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Bridges (file-local copies of the sha3 Foundation helpers) -/

private theorem pure_prop_holds {P : Prop} (h : P) : (pure P : RustM Prop).holds := by
  simp only [Aeneas.Std.RustM.holds, Std.Do.Triple, WP.wp]
  intro _
  exact h

private theorem of_pure_prop_holds {P : Prop} (h : (pure P : RustM Prop).holds) : P := by
  simp only [Aeneas.Std.RustM.holds, Std.Do.Triple, WP.wp] at h
  exact h trivial

private theorem triple_imp_intro {α} {e : Aeneas.Std.RustM α} {P : Prop} {Q : α → Prop}
    (h : P → ⦃⌜True⌝⦄ e ⦃⇓ r => ⌜Q r⌝⦄) :
    ⦃⌜P⌝⦄ e ⦃⇓ r => ⌜Q r⌝⦄ := by
  cases e
  · simp_all [Std.Do.Triple, WP.wp, PredTrans.apply]
  · simp_all [Std.Do.Triple, WP.wp, PredTrans.apply]
  · simp_all [Std.Do.Triple, WP.wp, PredTrans.apply]

/-- Local copy of the `triple_of_ok` pattern used throughout this tree. -/
private theorem triple_of_ok_seq {alpha : Type} {x : RustM alpha} {v : alpha}
    {P : alpha → Prop} (hx : x = ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Triple, WP.wp, PredTrans.apply, hp]

/-- An in-range `Slice.index_usize` as a plain equation. -/
private theorem slice_index_ok {T : Type} [Inhabited T] (s : Slice T) (i : Std.Usize)
    (h : i.val < s.val.length) : Slice.index_usize s i = .ok (s.val[i.val]!) := by
  unfold Aeneas.Std.Slice.index_usize
  rw [Aeneas.Std.Slice.getElem?_Usize_eq, List.getElem?_eq_getElem h,
    List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- What it means for a `PartialEq` instance to decide real equality: it is `==`.
    Combined with `LawfulBEq` that pins it to actual equality. -/
def LawfulPartialEq {T : Type} [BEq T] (inst : CoreModels.core.cmp.PartialEq T T) : Prop :=
  ∀ x y : T, inst.eq x y = .ok (x == y)

/-- `core.I32.Insts.CoreCmpPartialEqI32` is literally `fun x y => ok (x == y)`. -/
theorem lawful_partialEq_i32 :
    LawfulPartialEq (CoreModels.core.I32.Insts.CoreCmpPartialEqI32) :=
  fun _ _ => rfl

/-! ## The loop

    Invariant at index `i`: the accumulator is `true` exactly when the first `i`
    elements agree. The extraction never breaks early — once the accumulator is
    `false` it stays `false` and the walk runs to the end — which is what makes
    this invariant an iff rather than a one-way implication. -/

private theorem eq_loop_spec {T : Type} [Inhabited T] [BEq T] [LawfulBEq T]
    (inst : CoreModels.core.cmp.PartialEq T T) (hinst : LawfulPartialEq inst)
    (a b : Slice T) (n : Std.Usize)
    (ha : n.val ≤ a.val.length) (hb : n.val ≤ b.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.Slice.Insts.CoreCmpPartialEqSlice.eq_loop inst
      { start := 0#usize, «end» := n } a b true
    ⦃ ⇓ r => ⌜ r = true ↔ ∀ k : Nat, k < n.val → a.val[k]! = b.val[k]! ⌝ ⦄ := by
  unfold CoreModels.core.Slice.Insts.CoreCmpPartialEqSlice.eq_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, res1) => CoreModels.core.Slice.Insts.CoreCmpPartialEqSlice.eq_loop.body
        inst a b iter1 res1)
      true 0#usize n
      (fun i acc => pure (acc = true ↔ ∀ k : Nat, k < i.val → a.val[k]! = b.val[k]!))
      (by simp)
      (pure_prop_holds (by simp))
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    exact of_pure_prop_holds h
  · intro acc i _h_ge h_le hinv
    have hinv' := of_pure_prop_holds hinv
    unfold CoreModels.core.Slice.Insts.CoreCmpPartialEqSlice.eq_loop.body
    apply Std.Do.Triple.bind _ _
      (IteratorRange_next_spec_usize i n
        (Q := PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
          match oi.1 with
          | none => i.val ≥ n.val ∧ oi.2 = { start := i, «end» := n }
          | some m => m = i ∧ i.val < n.val ∧
                      oi.2.«end» = n ∧ oi.2.start.val = i.val + 1
        ⌝)
        (fun hlt s' hs' => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          exact ⟨rfl, hlt, rfl, hs'⟩)
        (fun hge => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          exact ⟨hge, rfl⟩))
    intro ⟨o, iter1⟩
    apply triple_imp_intro
    intro hnext
    match o with
    | none =>
        -- the walk is over: `i.val = n.val`, so the invariant at `i` IS the goal
        obtain ⟨hge, -⟩ := hnext
        have hin : i.val = n.val := Nat.le_antisymm h_le hge
        refine triple_of_ok_seq rfl (pure_prop_holds ?_)
        rw [← hin]; exact hinv'
    | some m =>
        obtain ⟨hmi, hlt, hend, hstart⟩ := hnext
        subst m
        have hia : i.val < a.val.length := Nat.lt_of_lt_of_le hlt ha
        have hib : i.val < b.val.length := Nat.lt_of_lt_of_le hlt hb
        dsimp only at hend hstart ⊢
        cases acc with
        | true =>
            -- The goal still carries an unreduced `let (o, iter1) := (some i, _)`
            -- and `match`, so `rw` cannot see the body. State the body's value as
            -- an equation instead and let `refine` close the gap by defeq.
            have hval :
                ((do let t ← Slice.index_usize a i
                     let t1 ← Slice.index_usize b i
                     let bb ← inst.eq t t1
                     if bb = true then ok (ControlFlow.cont (iter1, true))
                     else ok (ControlFlow.cont (iter1, false))) :
                  RustM (ControlFlow
                    (CoreModels.core.ops.range.Range Std.Usize × Bool) Bool))
                  = ok (ControlFlow.cont (iter1, (a.val[i.val]! == b.val[i.val]!))) := by
              rw [slice_index_ok a i hia, bind_tc_ok, slice_index_ok b i hib,
                bind_tc_ok, hinst, bind_tc_ok]
              cases h : (a.val[i.val]! == b.val[i.val]!) <;> simp
            refine triple_of_ok_seq hval ⟨hlt, hend, hstart, pure_prop_holds ?_⟩
            constructor
            · intro hbeq k hk
              rw [hstart] at hk
              rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
              · exact (hinv'.mp rfl) k hk'
              · subst hk'; exact eq_of_beq hbeq
            · intro hall
              exact beq_iff_eq.mpr (hall i.val (by rw [hstart]; omega))
        | false =>
            refine triple_of_ok_seq rfl ⟨hlt, hend, hstart, pure_prop_holds ?_⟩
            simp only [Bool.false_eq_true, false_iff]
            intro hall
            have hshort : ¬ (∀ k : Nat, k < i.val → a.val[k]! = b.val[k]!) := by
              intro h
              exact absurd (hinv'.mpr h) (by simp)
            exact hshort (fun k hk => hall k (by rw [hstart]; omega))

/-! ## The closed form -/

/-- **Slice equality, in closed form.** `a == b` on slices returns `true` exactly
    when the underlying lists are equal. -/
theorem slice_eq_spec {T : Type} [Inhabited T] [BEq T] [LawfulBEq T]
    (inst : CoreModels.core.cmp.PartialEq T T) (hinst : LawfulPartialEq inst)
    (a b : Slice T) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.Slice.Insts.CoreCmpPartialEqSlice.eq inst a b
    ⦃ ⇓ r => ⌜ r = true ↔ a.val = b.val ⌝ ⦄ := by
  unfold CoreModels.core.Slice.Insts.CoreCmpPartialEqSlice.eq
  have hlen : ∀ s : Slice T, CoreModels.core.slice.Slice.len s = .ok (Std.Slice.len s) := by
    intro s
    simp [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  rw [hlen a, hlen b, bind_tc_ok, bind_tc_ok]
  by_cases hne : Std.Slice.len a != Std.Slice.len b
  · rw [if_pos hne]
    refine triple_of_ok_seq rfl ?_
    simp only [Bool.false_eq_true, false_iff]
    intro hab
    have hlenab : Std.Slice.len a = Std.Slice.len b := by
      apply Aeneas.Std.UScalar.eq_of_val_eq
      simp [hab]
    simp [hlenab] at hne
  · rw [if_neg hne]
    have heqlen : a.val.length = b.val.length := by simpa using hne
    have hla : (Std.Slice.len a).val ≤ a.val.length := by simp
    have hlb : (Std.Slice.len a).val ≤ b.val.length := by
      simp [heqlen]
    apply Std.Do.Triple.of_entails_right _
      (eq_loop_spec inst hinst a b (Std.Slice.len a) hla hlb)
    rw [PostCond.entails_noThrow]
    intro r h
    dsimp only [Std.Do.SPred.down_pure] at h ⊢
    rw [h, Aeneas.Std.Slice.len_val]
    constructor
    · intro hall
      apply List.ext_getElem heqlen
      intro k h1 _h2
      have hk := hall k h1
      rwa [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem h1, List.getElem?_eq_getElem (heqlen ▸ h1)] at hk
    · intro hab k _hk
      rw [hab]

/-- Corollary in `.ok`-form for the common discharge direction: equal underlying
    lists make the extracted slice `==` return `ok true`. -/
theorem slice_eq_true {T : Type} [Inhabited T] [BEq T] [LawfulBEq T]
    (inst : CoreModels.core.cmp.PartialEq T T) (hinst : LawfulPartialEq inst)
    {a b : Slice T} (h : a.val = b.val) :
    CoreModels.core.Slice.Insts.CoreCmpPartialEqSlice.eq inst a b = .ok true := by
  have hs := slice_eq_spec inst hinst a b
  match hx : CoreModels.core.Slice.Insts.CoreCmpPartialEqSlice.eq inst a b, hs with
  | .ok r, hs =>
      have hr : r = true := by
        have hiff : r = true ↔ a.val = b.val := by
          simpa [Triple, WP.wp, PredTrans.apply] using hs
        exact hiff.mpr h
      rw [hr]
  | .fail _, hs =>
      exact absurd hs (by simp [Triple, WP.wp, PredTrans.apply])
  | .div, hs =>
      exact absurd hs (by simp [Triple, WP.wp, PredTrans.apply])

end libcrux_iot_ml_dsa.Util.SliceEq
