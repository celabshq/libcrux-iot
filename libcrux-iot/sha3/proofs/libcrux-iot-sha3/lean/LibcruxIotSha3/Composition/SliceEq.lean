/-
  # `Composition/SliceEq.lean` — a spec for `core::cmp::PartialEq for [T]`

  CoreModels implements slice equality as an actual loop
  (`core.Slice.Insts.CoreCmpPartialEqSlice.eq_loop`, a `Range` walk carrying a
  `Bool` accumulator) and ships no spec lemma for it. Anything that writes
  `a == b` on slices therefore extracts to something no tactic can see through.

  That shows up as soon as a `#[hax_lib::ensures]` compares a digest against a
  hacspec: the generated `post` ends in
  `core.Slice.Insts.CoreCmpPartialEqSlice.eq inst digest_future spec_out[..]`,
  and discharging it needs exactly the closed form proved here.

  This is a CoreModels-level fact, not a libcrux-iot one -- it belongs upstream
  next to the definition. It lives here until then.
-/
import LibcruxIotSha3.Composition.HacspecBridge

open Aeneas Aeneas.Std RustM ControlFlow Std.Do
open CoreModels

namespace libcrux_iot_sha3.Composition

open libcrux_iot_sha3.Foundation (triple_imp_intro pure_prop_holds of_pure_prop_holds)

set_option maxHeartbeats 1000000

/-! ## Bridges -/

/-- Local copy of the `triple_of_ok` pattern used throughout this tree: an
    `.ok v` equation plus the post fact gives the Triple. -/
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

/-- `core.U8.Insts.CoreCmpPartialEqU8` is literally `fun x y => ok (x == y)`, and
    `Std.U8 = UScalar .U8` carries `LawfulBEq`. -/
theorem lawful_partialEq_u8 :
    LawfulPartialEq (CoreModels.core.U8.Insts.CoreCmpPartialEqU8) :=
  fun _ _ => rfl

/-! ## The loop

    Invariant at index `i`: the accumulator is `true` exactly when the first `i`
    elements agree. Note the extraction never breaks early -- once the
    accumulator is `false` it stays `false` and the walk runs to the end -- which
    is what makes this invariant an iff rather than a one-way implication. -/

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
        -- reduce the `let (o, iter1) := (some i, iter1)` and the outer `match`
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
            -- the invariant already said the shorter prefix disagrees
            have hshort : ¬ (∀ k : Nat, k < i.val → a.val[k]! = b.val[k]!) := by
              intro h
              exact absurd (hinv'.mpr h) (by simp)
            exact hshort (fun k hk => hall k (by rw [hstart]; omega))

/-! ## The closed form -/

/-- **Slice equality, in closed form.** `a == b` on slices returns `true` exactly
    when the underlying lists are equal.

    The extraction compares lengths first and short-circuits to `false` when they
    differ, so the length case never enters the loop. -/
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
  · -- lengths differ: `ok false`, and the lists cannot be equal
    rw [if_pos hne]
    refine triple_of_ok_seq rfl ?_
    simp only [Bool.false_eq_true, false_iff]
    intro hab
    have hlenab : Std.Slice.len a = Std.Slice.len b := by
      apply Aeneas.Std.UScalar.eq_of_val_eq
      simp [hab]
    simp [hlenab] at hne
  · -- lengths agree: run the loop over `len a`
    rw [if_neg hne]
    -- `simp` reduces `¬(len a != len b)` straight to equality of the lengths
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

end libcrux_iot_sha3.Composition
