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

set_option mvcgen.warning false

-- `scalar_tac` normalises the `i64` bounds through `2 ^ 63`, which overruns the
-- default recursion limit in the `imod` proof.
set_option maxRecDepth 8000

/-- The induction itself, over any index type: `val` reads an index as an
    integer, `Inv` is whatever the accumulator has to satisfy for the body to
    behave (ρ needs it -- its accumulator carries the lane the walk has reached),
    and `P i acc r` says "running from `i` with `acc` yields `r`". -/
theorem loop_range_eq_inv {ι β γ : Type} (val : ι → Int)
    (hinj : ∀ i j : ι, val i = val j → i = j)
    (body : (core.ops.range.Range ι × β) →
      RustM (ControlFlow (core.ops.range.Range ι × β) γ))
    (e : ι) (Inv : ι → β → Prop) (P : ι → β → γ → Prop)
    (hstep : ∀ (i : ι) (acc : β), val i < val e → Inv i acc →
      ∃ (s : ι) (acc' : β), val s = val i + 1 ∧ Inv s acc' ∧
        body ({ start := i, «end» := e }, acc)
          = ok (.cont ({ start := s, «end» := e }, acc')) ∧
        ∀ r, P s acc' r → P i acc r)
    (hdone : ∀ (acc : β), Inv e acc →
      ∃ r, body ({ start := e, «end» := e }, acc) = ok (.done r) ∧ P e acc r) :
    ∀ (k : Nat) (i : ι) (acc : β), val i + k = val e → Inv i acc →
      ∃ r, loop body ({ start := i, «end» := e }, acc) = ok r ∧ P i acc r := by
  intro k
  induction k with
  | zero =>
    intro i acc hik hinv
    have hie : i = e := hinj i e (by omega)
    subst hie
    obtain ⟨r, hb, hP⟩ := hdone acc hinv
    exact ⟨r, by rw [loop.eq_def, hb], hP⟩
  | succ k ih =>
    intro i acc hik hinv
    obtain ⟨s, acc', hs, hinv', hb, hP⟩ := hstep i acc (by omega) hinv
    obtain ⟨r, hr, hPr⟩ := ih s acc' (by omega) hinv'
    exact ⟨r, by rw [loop.eq_def, hb]; exact hr, hP r hPr⟩

/-- The invariant-free version, for the loops whose bodies behave on any
    accumulator. -/
theorem loop_range_eq_gen {ι β γ : Type} (val : ι → Int)
    (hinj : ∀ i j : ι, val i = val j → i = j)
    (body : (core.ops.range.Range ι × β) →
      RustM (ControlFlow (core.ops.range.Range ι × β) γ))
    (e : ι) (P : ι → β → γ → Prop)
    (hstep : ∀ (i : ι) (acc : β), val i < val e →
      ∃ (s : ι) (acc' : β), val s = val i + 1 ∧
        body ({ start := i, «end» := e }, acc)
          = ok (.cont ({ start := s, «end» := e }, acc')) ∧
        ∀ r, P s acc' r → P i acc r)
    (hdone : ∀ (acc : β),
      ∃ r, body ({ start := e, «end» := e }, acc) = ok (.done r) ∧ P e acc r) :
    ∀ (k : Nat) (i : ι) (acc : β), val i + k = val e →
      ∃ r, loop body ({ start := i, «end» := e }, acc) = ok r ∧ P i acc r := by
  intro k i acc hik
  refine loop_range_eq_inv val hinj body e (fun _ _ => True) P ?_ (fun acc _ => hdone acc)
    k i acc hik trivial
  intro j acc' hj _
  obtain ⟨s, acc'', hs, hb, hP⟩ := hstep j acc' hj
  exact ⟨s, acc'', hs, trivial, hb, hP⟩

/-- The `Usize` instance, the one the `for x in 0..5` nests use. -/
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
  intro k i acc hik
  refine loop_range_eq_gen (fun x : Std.Usize => (x.val : Int))
    (fun i j h => (Std.UScalar.eq_equiv i j).mpr (by omega)) body e P ?_ hdone k i acc (by omega)
  intro j acc' hj
  obtain ⟨s, acc'', hs, hb, hP⟩ := hstep j acc' (by omega)
  exact ⟨s, acc'', by omega, hb, hP⟩

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

theorem i64_mul_eq (x y : Std.I64)
    (h0 : Std.IScalar.min .I64 ≤ x.val * y.val) (h1 : x.val * y.val ≤ Std.IScalar.max .I64) :
    ∃ z : Std.I64, x * y = ok z ∧ z.val = x.val * y.val := by
  have he := Std.IScalar.mul_equiv x y
  have hdef : (x * y : RustM Std.I64) = Std.IScalar.mul x y := rfl
  rw [hdef]
  cases hm : Std.IScalar.mul x y with
  | ok z => rw [hm] at he; exact ⟨z, rfl, he.2.2.1⟩
  | fail e => rw [hm] at he; exact absurd he.2 (by simp only [not_and, not_le]; omega)
  | div => rw [hm] at he; exact he.elim

theorem i64_div_eq (x y : Std.I64) (hy : y.val ≠ 0) (hmin : x.val ≠ Std.I64.min) :
    ∃ z : Std.I64, x / y = ok z ∧ z.val = Int.tdiv x.val y.val := by
  have hs := Std.I64.div_spec (x := x) (y := y)
  unfold WP.partialSpec at hs
  cases hxy : (x / y : RustM Std.I64) with
  | ok z => rw [hxy] at hs; exact ⟨z, rfl, hs⟩
  | fail e => rw [hxy] at hs; cases e <;> simp_all
  | div => rw [hxy] at hs; exact hs.elim

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
/-- `imod a b` is the mathematical modulus, `Int.emod`, for every positive `b`
    that leaves the intermediate `a % b + b` in range.  Rust's `%` truncates
    towards zero, which is why the spec needs the `+ b` and the second `%` at
    all; `Int.tmod_eq_emod` is what connects the two. -/
theorem imod_eq (a b : Std.I64) (hb : 0 < b.val)
    (hamin : a.val ≠ Std.I64.min) (hmax : 2 * b.val ≤ Std.IScalar.max .I64)
    (hbu : b.val ≤ Std.UScalar.max Std.UScalarTy.Usize) :
    ∃ m : Std.Usize, hacspec_sha3_pedantic.step_mappings.imod a b = ok m
      ∧ (m.val : Int) = a.val % b.val := by
  have hminI : Std.IScalar.min Std.IScalarTy.I64 = -9223372036854775808 := by
    rw [Std.IScalar.min_IScalarTy_I64_eq, Std.I64.min_eq]
  have hmaxI : Std.IScalar.max Std.IScalarTy.I64 = 9223372036854775807 := by
    rw [Std.IScalar.max_IScalarTy_I64_eq, Std.I64.max_eq]
  have hminN : Std.I64.min = -9223372036854775808 := Std.I64.min_eq
  have hpow : (2:Int) ^ (Std.IScalarTy.I64.numBits - 1) = 9223372036854775808 := by
    norm_num [Std.IScalarTy.numBits]
  have hab := a.hBounds
  have hbb := b.hBounds
  rw [hpow] at hab hbb
  have hem0 : 0 ≤ a.val % b.val := Int.emod_nonneg _ (by omega)
  have hem1 : a.val % b.val < b.val := Int.emod_lt_of_pos _ hb
  obtain ⟨i, hi, hiv⟩ := i64_rem_eq a b (by omega) hamin
  -- the truncating remainder differs from `emod` by at most one `b`
  have hib : i.val = a.val % b.val ∨ i.val = a.val % b.val - b.val := by
    rw [hiv, Int.tmod_eq_emod]
    by_cases hc : 0 ≤ a.val ∨ b.val ∣ a.val
    · rw [if_pos hc]; left; ring
    · rw [if_neg hc]
      right
      have : (b.val.natAbs : Int) = b.val := by omega
      rw [this]
  have hirange : -b.val ≤ i.val ∧ i.val < b.val := by omega
  have hi_lb : 0 ≤ i.val + b.val := by omega
  have hi_ub : i.val + b.val < 2 * b.val := by omega
  obtain ⟨i1, hi1, hi1v⟩ := i64_add_eq i b (by omega) (by omega)
  obtain ⟨i2, hi2, hi2v⟩ := i64_rem_eq i1 b (by omega) (by omega)
  have hi2a : i2.val = a.val % b.val := by
    have hi1nn : 0 ≤ i1.val := by omega
    rw [hi2v, Int.tmod_eq_emod, if_pos (Or.inl hi1nn), hi1v]
    have hsub : (i.val + b.val) % b.val = i.val % b.val := by simp
    rw [hsub]
    rcases hib with h | h
    · rw [h]
      simp
    · rw [h]
      have hstep : (a.val % b.val - b.val) % b.val = (a.val % b.val) % b.val := by
        simp
      rw [hstep]
      simp
  refine ⟨Std.IScalar.hcast Std.UScalarTy.Usize i2, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.step_mappings.imod
    rw [hi, bind_tc_ok, hi1, bind_tc_ok, hi2, bind_tc_ok]
  · rw [i64_to_usize_val i2 (by omega) (by omega), hi2a]

/-! ## `Iterator::next` on a `Range I64`

ρ walks `for t in 0..24` over `i64`, and the round loop of `keccak_p` does the
same, so the signed iterator needs the two equations too.  hax ships the triple
for `I32` and `Usize` only; this is the `I64` twin of its `I32` proof, from
which the equations follow as above. -/

private theorem hcast_cast_one_val_i64 :
    (Std.UScalar.hcast Std.IScalarTy.I64
      (Std.UScalar.cast Std.UScalarTy.U64 (1#usize))).val = 1 := by
  simp only [Std.UScalar.hcast, Std.IScalar.val, BitVec.toInt_setWidth]; grind

private theorem i64_wrapping_add_one_val (i : Std.I64)
    (h1 : -9223372036854775808 ≤ i.val) (h2 : i.val ≤ 9223372036854775806) :
    (i.wrapping_add (Std.UScalar.hcast Std.IScalarTy.I64
        (Std.UScalar.cast Std.UScalarTy.U64 1#usize))).val = i.val + 1 := by
  simp only [Std.I64.wrapping_add_val_eq, hcast_cast_one_val_i64, Nat.reducePow]
  grind

theorem IteratorRange_next_spec_i64 (i e : Std.I64) {Q}
    (h_lt : (h : i.val < e.val) →
      ∀ (s : Std.I64), s.val = i.val + 1 →
        (Q.1 (some i, { start := s, «end» := e })).down)
    (h_ge : i.val ≥ e.val →
      (Q.1 (none, { start := i, «end» := e })).down) :
    ⦃ ⌜ True ⌝ ⦄
    core.IteratorRange.next core.I64.Insts.CoreIterRangeStep
      { start := i, «end» := e }
    ⦃ Q ⦄ := by
  unfold core.IteratorRange.next core.I64.Insts.CoreIterRangeStep
  by_cases h : i.val < e.val
  · have h_lt' := h_lt h
    simp_all [compare, compareOfLessAndEq,
      core.I64.Insts.CoreCmpPartialOrdI64, core.mkIPartialOrd,
      core.I64.Insts.CoreCloneClone.clone,
      core.I64.Insts.CoreIterRangeStep.forward_checked,
      core.U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from,
      core.num.U64.MAX, core.num.U64.MIN,
      core.num.I64.wrapping_add, rust_primitives.arithmetic.wrapping_add_i64]
    mvcgen
    all_goals first
      | refine h_lt' _ ?_
        subst_vars
        exact i64_wrapping_add_one_val i (by scalar_tac) (by scalar_tac)
      | simp_all only [Std.U64.rMax, hcast_cast_one_val_i64,
          Std.UScalar.cast_val_eq, Std.UScalar.ofNatCore_val_eq]
        first
          | scalar_tac
          | (rcases System.Platform.numBits_eq with hN | hN <;> simp [hN] at * <;> omega)
          | grind
  · have h_ge' := h_ge (by omega)
    simp only [compare, compareOfLessAndEq,
      core.I64.Insts.CoreCmpPartialOrdI64, core.mkIPartialOrd]
    mvcgen
    have hlt : ¬ (i.val < e.val) := by omega
    by_cases hie : i.val = e.val <;> simp_all

theorem range_next_lt_i64 (i e : Std.I64) (h : i.val < e.val) :
    ∃ s : Std.I64, s.val = i.val + 1 ∧
      core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
        core.I64.Insts.CoreIterRangeStep { start := i, «end» := e }
        = ok (some i, { start := s, «end» := e }) := by
  have ht := IteratorRange_next_spec_i64 (Q := PostCond.noThrow fun p =>
      ⌜ ∃ s : Std.I64, s.val = i.val + 1 ∧ p = (some i, { start := s, «end» := e }) ⌝)
    i e (fun _ s hs => ⟨s, hs, rfl⟩) (fun hge => absurd h (by omega))
  obtain ⟨v, hv⟩ := Hax.triple_noThrow_exists_ok ht
  obtain ⟨s, hs, hveq⟩ := Hax.triple_noThrow_elim ht hv
  refine ⟨s, hs, ?_⟩
  show core.IteratorRange.next _ _ = _
  rw [hv, hveq]

theorem range_next_ge_i64 (i e : Std.I64) (h : e.val ≤ i.val) :
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.I64.Insts.CoreIterRangeStep { start := i, «end» := e }
      = ok (none, { start := i, «end» := e }) := by
  have ht := IteratorRange_next_spec_i64 (Q := PostCond.noThrow fun p =>
      ⌜ p = (none, { start := i, «end» := e }) ⌝)
    i e (fun hlt _ _ => absurd hlt (by omega)) (fun _ => rfl)
  obtain ⟨v, hv⟩ := Hax.triple_noThrow_exists_ok ht
  have hveq := Hax.triple_noThrow_elim ht hv
  show core.IteratorRange.next _ _ = _
  rw [hv, hveq]

/-- The `I64` instance of `loop_range_eq_gen`. -/
theorem loop_range_eq_i64 {β γ : Type}
    (body : (core.ops.range.Range Std.I64 × β) →
      RustM (ControlFlow (core.ops.range.Range Std.I64 × β) γ))
    (e : Std.I64) (P : Std.I64 → β → γ → Prop)
    (hstep : ∀ (i : Std.I64) (acc : β), i.val < e.val →
      ∃ (s : Std.I64) (acc' : β), s.val = i.val + 1 ∧
        body ({ start := i, «end» := e }, acc)
          = ok (.cont ({ start := s, «end» := e }, acc')) ∧
        ∀ r, P s acc' r → P i acc r)
    (hdone : ∀ (acc : β),
      ∃ r, body ({ start := e, «end» := e }, acc) = ok (.done r) ∧ P e acc r) :
    ∀ (k : Nat) (i : Std.I64) (acc : β), i.val + k = e.val →
      ∃ r, loop body ({ start := i, «end» := e }, acc) = ok r ∧ P i acc r :=
  loop_range_eq_gen (fun x : Std.I64 => x.val)
    (fun i j h => (Std.IScalar.eq_equiv i j).mpr h) body e P hstep hdone


/-- The `I64` instance of `loop_range_eq_inv`, for ρ's walk. -/
theorem loop_range_eq_inv_i64 {β γ : Type}
    (body : (core.ops.range.Range Std.I64 × β) →
      RustM (ControlFlow (core.ops.range.Range Std.I64 × β) γ))
    (e : Std.I64) (Inv : Std.I64 → β → Prop) (P : Std.I64 → β → γ → Prop)
    (hstep : ∀ (i : Std.I64) (acc : β), i.val < e.val → Inv i acc →
      ∃ (s : Std.I64) (acc' : β), s.val = i.val + 1 ∧ Inv s acc' ∧
        body ({ start := i, «end» := e }, acc)
          = ok (.cont ({ start := s, «end» := e }, acc')) ∧
        ∀ r, P s acc' r → P i acc r)
    (hdone : ∀ (acc : β), Inv e acc →
      ∃ r, body ({ start := e, «end» := e }, acc) = ok (.done r) ∧ P e acc r) :
    ∀ (k : Nat) (i : Std.I64) (acc : β), i.val + k = e.val → Inv i acc →
      ∃ r, loop body ({ start := i, «end» := e }, acc) = ok r ∧ P i acc r :=
  loop_range_eq_inv (fun x : Std.I64 => x.val)
    (fun i j h => (Std.IScalar.eq_equiv i j).mpr h) body e Inv P hstep hdone

/-! ## `Iterator::next` on a `RangeInclusive Usize`

`core-models` ships no `Iterator` instance for `RangeInclusive`, so the spec
package supplies one itself (`Assumptions/FunsExternal.lean`): the same body as
the half-open `Range`, with `≤` in place of `<`.  ι iterates `0..=l` and the
round-constant LFSR iterates `1..=t`, so the bridge needs its equations too.

The model has no `exhausted` flag, so it panics where Rust would yield the
largest value of the type and stop; `hsafe` below is exactly the hypothesis that
keeps us away from that corner, and every inclusive range in the spec is small. -/

theorem RangeInclusive_next_spec_usize (i e : Std.Usize) {Q}
    (hsafe : i.val + 1 ≤ Std.UScalar.max Std.UScalarTy.Usize)
    (h_le : (h : i.val ≤ e.val) →
      ∀ (s : Std.Usize), s.val = i.val + 1 →
        (Q.1 (some i, { start := s, «end» := e })).down)
    (h_gt : e.val < i.val →
      (Q.1 (none, { start := i, «end» := e })).down) :
    ⦃ ⌜ True ⌝ ⦄
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e }
    ⦃ Q ⦄ := by
  unfold core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
    core.Usize.Insts.CoreIterRangeStep
  by_cases h : i.val ≤ e.val
  · simp_all [compare, compareOfLessAndEq,
      core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd,
      core.Usize.Insts.CoreCloneClone.clone,
      core.Usize.Insts.CoreIterRangeStep.forward_checked,
      core.convert.TryFromUTInfallible.Blanket.try_from,
      core.convert.From.Blanket.from,
      core.num.Usize.checked_add, core.num.Usize.overflowing_add,
      rust_primitives.arithmetic.overflowing_add_usize]
    mvcgen [uncurry]
      <;> grind [Std.UScalar.overflowing_add_eq i (1#usize)]
  · have h_gt' := h_gt (by omega)
    simp_all [core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd]
    mvcgen; grind

theorem range_incl_next_le (i e : Std.Usize) (h : i.val ≤ e.val)
    (hsafe : i.val + 1 ≤ Std.UScalar.max Std.UScalarTy.Usize) :
    ∃ s : Std.Usize, s.val = i.val + 1 ∧
      core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
        core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e }
        = ok (some i, { start := s, «end» := e }) := by
  have ht := RangeInclusive_next_spec_usize (Q := PostCond.noThrow fun p =>
      ⌜ ∃ s : Std.Usize, s.val = i.val + 1 ∧ p = (some i, { start := s, «end» := e }) ⌝)
    i e hsafe (fun _ s hs => ⟨s, hs, rfl⟩) (fun hgt => absurd h (by omega))
  obtain ⟨v, hv⟩ := Hax.triple_noThrow_exists_ok ht
  obtain ⟨s, hs, hveq⟩ := Hax.triple_noThrow_elim ht hv
  exact ⟨s, hs, by rw [hv, hveq]⟩

theorem range_incl_next_gt (i e : Std.Usize) (h : e.val < i.val)
    (hsafe : i.val + 1 ≤ Std.UScalar.max Std.UScalarTy.Usize) :
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e }
      = ok (none, { start := i, «end» := e }) := by
  have ht := RangeInclusive_next_spec_usize (Q := PostCond.noThrow fun p =>
      ⌜ p = (none, { start := i, «end» := e }) ⌝)
    i e hsafe (fun hle _ _ => absurd hle (by omega)) (fun _ => rfl)
  obtain ⟨v, hv⟩ := Hax.triple_noThrow_exists_ok ht
  have hveq := Hax.triple_noThrow_elim ht hv
  rw [hv, hveq]

/-- The loop induction for an inclusive range: one more iteration than the
    half-open one, and the exit test is `start > end`. -/
theorem loop_range_incl_eq {β γ : Type}
    (body : (core.ops.range.RangeInclusive Std.Usize × β) →
      RustM (ControlFlow (core.ops.range.RangeInclusive Std.Usize × β) γ))
    (e : Std.Usize) (P : Std.Usize → β → γ → Prop)
    (hstep : ∀ (i : Std.Usize) (acc : β), i.val ≤ e.val →
      ∃ (s : Std.Usize) (acc' : β), s.val = i.val + 1 ∧
        body ({ start := i, «end» := e }, acc)
          = ok (.cont ({ start := s, «end» := e }, acc')) ∧
        ∀ r, P s acc' r → P i acc r)
    (hdone : ∀ (i : Std.Usize) (acc : β), e.val < i.val →
      ∃ r, body ({ start := i, «end» := e }, acc) = ok (.done r) ∧ P i acc r) :
    ∀ (k : Nat) (i : Std.Usize) (acc : β), i.val + k = e.val + 1 →
      ∃ r, loop body ({ start := i, «end» := e }, acc) = ok r ∧ P i acc r := by
  intro k
  induction k with
  | zero =>
    intro i acc hik
    obtain ⟨r, hb, hP⟩ := hdone i acc (by omega)
    exact ⟨r, by rw [loop.eq_def, hb], hP⟩
  | succ k ih =>
    intro i acc hik
    obtain ⟨s, acc', hs, hb, hP⟩ := hstep i acc (by omega)
    obtain ⟨r, hr, hPr⟩ := ih s acc' (by omega)
    exact ⟨r, by rw [loop.eq_def, hb]; exact hr, hP r hPr⟩

end LibcruxIotSha3.Composition.Pedantic
