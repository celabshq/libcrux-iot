import LibcruxIotSha3.Composition.Pedantic.StateMap
/-!
# Equational loop-over-range lemma

The pedantic step mappings are nests of `for x in 0..5 { for y in 0..5 { for z
in 0..w { .. } } }`, and hax extracts each `for` into an Aeneas `loop` fixpoint
over a `Range Usize` iterator.  The hax library ships Hoare-triple lemmas for
those (`Hax.loop_range_spec_unsigned`), but they require the loop's accumulator
and its result to have the same type, and these loops return a *pair* (the
unchanged input state array alongside the output one) while accumulating only
the output.  They are also total and deterministic, which makes an equation more
useful downstream than a triple: the step-mapping characterisations are
equations, and equations compose by `rw`.

`loop_range_eq` is that equation.  Read it as a backwards induction: `P i acc r`
says "running the loop from index `i` with accumulator `acc` yields `r`", the
step hypothesis says one iteration turns the goal at `i` into the goal at
`i + 1`, and the conclusion is the run from any `i` with `e - i` iterations
left.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

theorem loop_range_eq {β γ : Type}
    (body : (core.ops.range.Range Std.Usize × β) →
      RustM (ControlFlow (core.ops.range.Range Std.Usize × β) γ))
    (e : Std.Usize) (P : Std.Usize → β → γ → Prop)
    (hstep : ∀ (i : Std.Usize) (acc : β), i.val < e.val →
      ∃ (s : Std.Usize) (acc' : β), s.val = i.val + 1 ∧
        body ({ start := i, «end» := e }, acc)
          = ok (.cont ({ start := s, «end» := e }, acc')) ∧
        ∀ r, P s acc' r → P i acc r)
    (hdone : ∀ (acc : β),
      ∃ r, body ({ start := e, «end» := e }, acc) = ok (.done r) ∧ P e acc r) :
    ∀ (k : Nat) (i : Std.Usize) (acc : β), i.val + k = e.val →
      ∃ r, loop body ({ start := i, «end» := e }, acc) = ok r ∧ P i acc r := by
  intro k
  induction k with
  | zero =>
    intro i acc hik
    have hie : i = e := by
      apply (Std.UScalar.eq_equiv i e).mpr
      omega
    subst hie
    obtain ⟨r, hb, hP⟩ := hdone acc
    exact ⟨r, by rw [loop.eq_def, hb], hP⟩
  | succ k ih =>
    intro i acc hik
    obtain ⟨s, acc', hs, hb, hP⟩ := hstep i acc (by omega)
    obtain ⟨r, hr, hPr⟩ := ih s acc' (by omega)
    exact ⟨r, by rw [loop.eq_def, hb]; exact hr, hP r hPr⟩


/-! ## `Iterator::next` on a `Range Usize`, as equations

`Hax.IteratorRange_next_spec_usize` states this as a Hoare triple; the loops
below need it as an equation, which the triple gives up via
`Hax.triple_noThrow_exists_ok` (the call cannot fail) plus
`Hax.triple_noThrow_elim` (its value is the one the post describes). -/

theorem range_next_lt (i e : Std.Usize) (h : i.val < e.val) :
    ∃ s : Std.Usize, s.val = i.val + 1 ∧
      core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
        core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e }
        = ok (some i, { start := s, «end» := e }) := by
  have ht := Hax.IteratorRange_next_spec_usize (Q := PostCond.noThrow fun p =>
      ⌜ ∃ s : Std.Usize, s.val = i.val + 1 ∧ p = (some i, { start := s, «end» := e }) ⌝)
    i e (fun _ s hs => ⟨s, hs, rfl⟩) (fun hge => absurd h (by omega))
  obtain ⟨v, hv⟩ := Hax.triple_noThrow_exists_ok ht
  obtain ⟨s, hs, hveq⟩ := Hax.triple_noThrow_elim ht hv
  refine ⟨s, hs, ?_⟩
  show core.IteratorRange.next _ _ = _
  rw [hv, hveq]

theorem range_next_ge (i e : Std.Usize) (h : e.val ≤ i.val) :
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e }
      = ok (none, { start := i, «end» := e }) := by
  have ht := Hax.IteratorRange_next_spec_usize (Q := PostCond.noThrow fun p =>
      ⌜ p = (none, { start := i, «end» := e }) ⌝)
    i e (fun hlt _ _ => absurd hlt (by omega)) (fun _ => rfl)
  obtain ⟨v, hv⟩ := Hax.triple_noThrow_exists_ok ht
  have hveq := Hax.triple_noThrow_elim ht hv
  show core.IteratorRange.next _ _ = _
  rw [hv, hveq]


/-! ## Reads and index arithmetic, as equations

The loop bodies read the state array with `Array.index_usize` and compute
neighbour indices with the checked `Usize` addition.  Both are `RustM` actions
that cannot fail here (the indices are in range, the sums are tiny), and both
are needed as equations for the same reason `loop_range_eq` is. -/

theorem index_usize_eq {α : Type} [Inhabited α] {n : Std.Usize}
    (v : Std.Array α n) (i : Std.Usize) (h : i.val < n.val) :
    v.index_usize i = ok v.val[i.val]! := by
  have hlen : v.val.length = n.val := v.property
  unfold Std.Array.index_usize
  rw [Std.Array.getElem?_Usize_eq, List.getElem?_eq_getElem (by omega),
    getElem!_pos v.val i.val (by omega)]

theorem usize_add_eq (x y : Std.Usize) (h : x.val + y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, x + y = ok z ∧ z.val = x.val + y.val := by
  have he := Std.UScalar.add_equiv x y
  cases hxy : (x + y : RustM Std.Usize) with
  | ok z => rw [hxy] at he; exact ⟨z, rfl, he.2.1⟩
  | fail e =>
    rw [hxy] at he
    exact absurd he.2 (by simp only [Std.UScalar.inBounds, not_not]; scalar_tac)
  | div => rw [hxy] at he; exact he.elim

theorem usize_rem_eq (x y : Std.Usize) (h : y.val ≠ 0) :
    ∃ z : Std.Usize, x % y = ok z ∧ z.val = x.val % y.val := by
  have hs := Std.Usize.rem_spec (x := x) (y := y)
  unfold WP.partialSpec at hs
  cases hxy : (x % y : RustM Std.Usize) with
  | ok z => rw [hxy] at hs; exact ⟨z, rfl, hs⟩
  | fail e => rw [hxy] at hs; cases e <;> simp_all
  | div => rw [hxy] at hs; exact hs.elim

theorem array_update_eq {α : Type} {n : Std.Usize}
    (v : Std.Array α n) (i : Std.Usize) (x : α) (h : i.val < n.val) :
    v.update i x = ok (v.set i x) := by
  have hlen : v.val.length = n.val := v.property
  unfold Std.Array.update
  rw [Std.Array.getElem?_Usize_eq, List.getElem?_eq_getElem (by omega)]
  rfl

end LibcruxIotSha3.Composition.Pedantic
