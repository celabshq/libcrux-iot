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

-- `scalar_tac` normalises the `i64` bounds through `2 ^ 63`, which overruns the
-- default recursion limit in the `imod` proof.
set_option maxRecDepth 8000

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

theorem usize_mul_eq (x y : Std.Usize) (h : x.val * y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, x * y = ok z ∧ z.val = x.val * y.val := by
  have he := Std.UScalar.mul_equiv x y
  have hdef : (x * y : RustM Std.Usize) = Std.UScalar.mul x y := rfl
  rw [hdef]
  cases hm : Std.UScalar.mul x y with
  | ok z => rw [hm] at he; exact ⟨z, rfl, he.2.1⟩
  | fail e => rw [hm] at he; exact absurd he.2 (by scalar_tac)
  | div => rw [hm] at he; exact he.elim

/-! ## The signed side: `imod`

`theta`'s D loop indexes with `x - 1` and `z - 1`, which FIPS 202 reads modulo 5
and modulo `w`.  Rust's `%` truncates towards zero, so the spec spells the
mathematical modulus out as `imod a b = ((a % b) + b) % b` over `i64`, casting
the result back to an index.  `imod_eq` says that is the mathematical modulus
whenever `|a| < b`, which is all the spec ever uses it at. -/

theorem usize_to_i64 (x : Std.Usize) (h : (x.val : Int) ≤ Std.IScalar.max .I64) :
    ∃ i : Std.I64, lift (Std.UScalar.hcast .I64 x) = ok i ∧ i.val = (x.val : Int) :=
  WP.spec_imp_exists (Std.UScalar.hcast_inBounds_spec .I64 x h)

theorem i64_to_usize_val (i : Std.I64)
    (h0 : 0 ≤ i.val) (h1 : i.val ≤ Std.UScalar.max .Usize) :
    ((Std.IScalar.hcast Std.UScalarTy.Usize i).val : Int) = i.val := by
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (Std.IScalar.hcast_inBounds_spec .Usize i ⟨h0, h1⟩)
  have hlift : lift (Std.IScalar.hcast Std.UScalarTy.Usize i)
      = ok (Std.IScalar.hcast Std.UScalarTy.Usize i) := rfl
  rw [hlift] at hy
  cases hy
  exact hyv

theorem i64_add_eq (x y : Std.I64)
    (h0 : Std.IScalar.min .I64 ≤ x.val + y.val) (h1 : x.val + y.val ≤ Std.IScalar.max .I64) :
    ∃ z : Std.I64, x + y = ok z ∧ z.val = x.val + y.val := by
  have he := Std.IScalar.add_equiv x y
  cases hxy : (x + y : RustM Std.I64) with
  | ok z => rw [hxy] at he; exact ⟨z, rfl, he.2.1⟩
  | fail e => rw [hxy] at he; exact absurd he.2 (by simp only [Std.IScalar.inBounds, not_not]; constructor <;> scalar_tac)
  | div => rw [hxy] at he; exact he.elim

theorem i64_sub_eq (x y : Std.I64)
    (h0 : Std.IScalar.min .I64 ≤ x.val - y.val) (h1 : x.val - y.val ≤ Std.IScalar.max .I64) :
    ∃ z : Std.I64, x - y = ok z ∧ z.val = x.val - y.val := by
  have he := Std.IScalar.sub_equiv x y
  cases hxy : (x - y : RustM Std.I64) with
  | ok z => rw [hxy] at he; exact ⟨z, rfl, he.2.1⟩
  | fail e => rw [hxy] at he; exact absurd he.2 (by simp only [Std.IScalar.inBounds, not_not]; constructor <;> scalar_tac)
  | div => rw [hxy] at he; exact he.elim

theorem i64_rem_eq (x y : Std.I64) (hy : y.val ≠ 0) (hmin : x.val ≠ Std.I64.min) :
    ∃ z : Std.I64, x % y = ok z ∧ z.val = Int.tmod x.val y.val := by
  have hs := Std.I64.rem_spec (x := x) (y := y)
  unfold WP.partialSpec at hs
  cases hxy : (x % y : RustM Std.I64) with
  | ok z => rw [hxy] at hs; exact ⟨z, rfl, hs⟩
  | fail e => rw [hxy] at hs; cases e <;> simp_all
  | div => rw [hxy] at hs; exact hs.elim

set_option maxRecDepth 8000 in
/-- With `|a| < b` -- the only way the spec calls it -- `imod` is the mathematical
    modulus, `Int.emod`. -/
theorem imod_eq (a b : Std.I64) (hb : 0 < b.val) (hlo : -b.val < a.val) (hhi : a.val < b.val)
    (hmax : a.val + b.val ≤ Std.IScalar.max .I64)
    (hbu : b.val ≤ Std.UScalar.max Std.UScalarTy.Usize) :
    ∃ m : Std.Usize, hacspec_sha3_pedantic.step_mappings.imod a b = ok m
      ∧ (m.val : Int) = a.val % b.val := by
  have hminval : Std.I64.min = -9223372036854775808 := Std.I64.min_eq
  have hminI : Std.IScalar.min Std.IScalarTy.I64 = -9223372036854775808 := by
    rw [Std.IScalar.min_IScalarTy_I64_eq, Std.I64.min_eq]
  have hmaxI : Std.IScalar.max Std.IScalarTy.I64 = 9223372036854775807 := by
    rw [Std.IScalar.max_IScalarTy_I64_eq, Std.I64.max_eq]
  have hpow : (2:Int) ^ (Std.IScalarTy.I64.numBits - 1) = 9223372036854775808 := by
    norm_num [Std.IScalarTy.numBits]
  have hbb := b.hBounds
  have hab := a.hBounds
  rw [hpow] at hbb hab
  have hamin : a.val ≠ Std.I64.min := by omega
  obtain ⟨i, hi, hiv⟩ := i64_rem_eq a b (by omega) hamin
  -- `a % b` truncates towards zero, and with `|a| < b` that leaves `a` alone.
  have hia : i.val = a.val := by
    rw [hiv, Int.tmod_eq_emod]
    by_cases hpos : 0 ≤ a.val
    · rw [if_pos (Or.inl hpos), Int.emod_eq_of_lt hpos hhi]; ring
    · have hnd : ¬ (b.val ∣ a.val) := by
        intro hdvd
        have : b.val ≤ -a.val := Int.le_of_dvd (by omega) ((dvd_neg).mpr hdvd)
        omega
      rw [if_neg (by tauto)]
      have hb' : (b.val.natAbs : Int) = b.val := by omega
      have : a.val % b.val = a.val + b.val := by
        have h1 : (a.val + b.val) % b.val = a.val % b.val := by
          simp
        rw [← h1, Int.emod_eq_of_lt (by omega) (by omega)]
      rw [this, hb']
      ring
  obtain ⟨i1, hi1, hi1v⟩ := i64_add_eq i b (by rw [hia]; omega) (by rw [hia]; omega)
  obtain ⟨i2, hi2, hi2v⟩ := i64_rem_eq i1 b (by omega) (by rw [hi1v, hia]; omega)
  have hi2a : i2.val = a.val % b.val := by
    rw [hi2v, hi1v, hia, Int.tmod_eq_emod, if_pos (Or.inl (by omega))]
    have : (a.val + b.val) % b.val = a.val % b.val := by
      simp
    rw [this]
    ring
  refine ⟨Std.IScalar.hcast Std.UScalarTy.Usize i2, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.step_mappings.imod
    rw [hi, bind_tc_ok, hi1, bind_tc_ok, hi2, bind_tc_ok]
  · rw [i64_to_usize_val i2 (by rw [hi2a]; exact Int.emod_nonneg _ (by omega)) (by
      rw [hi2a]
      have : a.val % b.val < b.val := Int.emod_lt_of_pos _ hb
      omega), hi2a]

end LibcruxIotSha3.Composition.Pedantic
