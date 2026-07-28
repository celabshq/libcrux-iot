/-
  Bridge between the impl-level `keccak.keccakf1600` and the hacspec
  top-level `keccak_f.keccak_f`.

  ## Architecture

  The impl's `keccak.keccakf1600` iterates `keccakf1600_4rounds` 6 times
  over an `I32` range `[0, 6)`. The hacspec's `keccak_f.keccak_f` iterates
  the body `theta ; rho ; pi ; chi ; iota round` 24 times over a `Usize`
  range `[0, 24)`. Our `Composition.keccakf1600_equiv_via_bit` proves that
  the impl's output equals a 24-fold spec chain (`spec_chain (lift s) 24`).

  This file provides the loop-spec infrastructure for the `Usize` range,
  the structural-unfolding helper for `array.from_fn` / `createi` over
  small `N`, and the spec-side definitions in terms of the hacspec
  round body (θ; ρ; π; χ; ι) that mirrors `keccak_f.keccak_f`'s body.

  These bridge the iteration-structure gap between our proof
  infrastructure (using `Nat.fold 24` over `spec_round_step`) and the
  hacspec function (using a `Usize` range loop over a single-round body).
-/
import LibcruxIotSha3.Composition.ViaBit
import LibcruxIotSha3.Foundation.I32LoopSpec

open Aeneas Aeneas.Std Result ControlFlow Std.Do libcrux_iot_sha3 hacspec_sha3
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
  unfold CoreModels.rust_primitives.slice.array_from_fn
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

/-! ## Spec-side single-round step (hacspec round body)

Mirrors `keccak_f.keccak_f_loop.body` (the `Some round` branch). -/

def spec_round_step_hacspec (state : Std.Array Std.U64 25#usize) (round : Std.Usize) :
    Result (Std.Array Std.U64 25#usize) := do
  let a ← keccak_f.theta state
  let a1 ← keccak_f.rho a
  let a2 ← keccak_f.pi a1
  let a3 ← keccak_f.chi a2
  keccak_f.iota a3 round

/-! ## `Usize` iterator-next spec (analog of `IteratorRange_next_spec_i32`)

The hacspec loop in `keccak_f.keccak_f_loop` iterates `Usize` indices over
`[0, 24)`. The `Usize.Insts.CoreIterRangeStep` instance is an
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
      unfold CoreModels.core.iter.range.IteratorRange.next
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
      unfold CoreModels.core.iter.range.IteratorRange.next
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
`I32` version: an invariant `inv : Usize → β → Result Prop` is preserved by
each step. Induction on `(e.val - start.val).toNat`. -/

section loop_range_usize_helpers

private abbrev ResultPSU := PostShape.except Error (PostShape.except PUnit PostShape.pure)

private theorem triple_noThrow_elim_usize {α : Type} {x : Result α} {Q : α → Assertion ResultPSU}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) {v : α} (hv : x = ok v) :
    (Q v).down := by
  subst hv; simpa [Triple, WP.wp, PredTrans.apply] using h

private theorem triple_noThrow_exists_ok_usize {α : Type} {x : Result α}
    {Q : α → Assertion ResultPSU}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) : ∃ v, x = ok v := by
  match x, h with
  | .ok v, _ => exact ⟨v, rfl⟩
  | .fail _, h => exact absurd h (by simp [Triple, WP.wp, PredTrans.apply])
  | .div, h => exact absurd h (by simp [Triple, WP.wp, PredTrans.apply])

private theorem triple_of_ok_usize {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = ok v) (hp : P v) :
    (⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) := by
  subst hx; simp [Triple, WP.wp, PredTrans.apply, hp]

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

/-! ## Spec-chain via the hacspec round body

Mirrors `spec_chain` (from `SpecChain.lean`) but uses `spec_round_step_hacspec`. -/

def spec_round_step_hacspec_at (round_idx : Nat) (st : Std.Array Std.U64 25#usize) :
    Result (Std.Array Std.U64 25#usize) :=
  if h : round_idx < 24 then spec_round_step_hacspec st (roundOfNat round_idx (by omega))
  else .fail .panic

def spec_chain_hacspec (s : Std.Array Std.U64 25#usize) (n : Nat) :
    Result (Std.Array Std.U64 25#usize) :=
  Nat.fold n (fun i _ acc => acc >>= fun st => spec_round_step_hacspec_at i st) (pure s)

theorem spec_chain_hacspec_zero (s : Std.Array Std.U64 25#usize) :
    spec_chain_hacspec s 0 = .ok s := by rfl

theorem spec_chain_hacspec_succ (s : Std.Array Std.U64 25#usize) (n : Nat) :
    spec_chain_hacspec s (n + 1) =
      spec_chain_hacspec s n >>= fun st => spec_round_step_hacspec_at n st := by
  unfold spec_chain_hacspec
  rw [Nat.fold_succ]

/-! ## Components

This file provides the infrastructure that bridges the impl-level
`keccak.keccakf1600` to the hacspec-level `keccak_f.keccak_f`:

- `IteratorRange_next_spec_usize` and `loop_range_spec_usize` — the
  `Usize` analogs of `I32LoopSpec`'s `*_i32` lemmas.
- `array_from_fn_eq_unfold{5,25}` — `CoreModels.rust_primitives.slice.array_from_fn`
  unfolds to a chain of sequential `call_mut` calls (handles the
  dependent-typed `match h : foldlM ... with | ok r => ⟨r.1, _proof_1⟩`
  via a `split` + `subst` approach).
- `spec_round_step_hacspec` / `spec_chain_hacspec` — spec-side
  definitions mirroring the hacspec loop body (θ/ρ/π/χ/ι). Includes
  `_zero` and `_succ` recurrence lemmas.
- `keccak_f_loop_eq_spec_chain_hacspec` — `loop_range_spec_usize` with
  the invariant "after k iterations, the state equals
  `spec_chain_hacspec s k`".
- `keccakf1600_equiv_hacspec` — top-level theorem composing
  `keccakf1600_equiv_via_bit` with the above bridges to couple
  `keccak.keccakf1600` to `keccak_f.keccak_f` directly. -/

/-! ## Loop bridge: `keccak_f.keccak_f` equals `spec_chain_hacspec ... 24`

Direct induction on the number of remaining loop iterations. We pair the
loop's `start` index with a `Nat`-level counter `k`, and a proof that the
spec chain to `k` succeeds with `acc`. At each step:

- Iterator at `{kU, 24}` with `kU.val = k`: if `k < 24` returns
  `Some kU, iter1` with `iter1.start.val = k + 1`; if `k = 24` returns
  `None`.
- Loop body's θ;ρ;π;χ;ι chain is precisely `spec_round_step_hacspec acc kU`.
- By `spec_chain_hacspec_succ`, `spec_chain_hacspec s (k+1) =
  spec_chain_hacspec s k >>= spec_round_step_hacspec_at k =
  spec_round_step_hacspec_at k acc =
  spec_round_step_hacspec acc (roundOfNat k _)`. Since `kU.val = k`,
  `roundOfNat k _ = kU`, so this equals `spec_round_step_hacspec acc kU`.
- Failure in `spec_round_step_hacspec acc kU` propagates identically on
  both sides (loop fails, spec_chain fails and propagates to 24). -/

/-- Direct equality form of `IteratorRange.next` over a `Usize` range
    `{kU, 24}` when `kU.val < 24`: returns `Some kU` and increments the
    start by 1. Companion to `IteratorRange_next_spec_usize` (Triple form). -/
private theorem IteratorRange_next_eq_some_usize
    (kU : Std.Usize) (hkU : kU.val < 24) :
    ∃ kU' : Std.Usize, kU'.val = kU.val + 1 ∧
      CoreModels.core.iter.range.IteratorRange.next
        CoreModels.core.Usize.Insts.CoreIterRangeStep
        ({ start := kU, «end» := 24#usize } :
          CoreModels.core.ops.range.Range Std.Usize) =
        .ok (CoreModels.core.option.Option.Some kU,
             { start := kU', «end» := 24#usize }) := by
  have hUB : kU.val + 1 < 2 ^ System.Platform.numBits := by
    have h := kU.hBounds
    rcases System.Platform.numBits_eq with hN | hN <;>
      simp only [Std.UScalarTy.Usize_numBits_eq, hN] at h <;>
      rw [hN] <;> omega
  refine ⟨⟨kU.bv + 1#usize.bv⟩, ?_, ?_⟩
  · show (kU.bv + (1#usize).bv).toNat = kU.val + 1
    rw [BitVec.toNat_add]
    have h1 : (1#usize).bv.toNat = 1 := by decide
    rw [h1]
    show (kU.bv.toNat + 1) % _ = kU.val + 1
    apply Nat.mod_eq_of_lt
    exact hUB
  unfold CoreModels.core.iter.range.IteratorRange.next
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
  have hcmp : compare kU.val 24 = Ordering.lt := by
    rw [Nat.compare_eq_lt]; exact hkU
  have h24 : (24#usize : Std.Usize).val = 24 := rfl
  simp only [h24, hcmp]
  have hno_ovf : BitVec.uaddOverflow kU.bv (1#System.Platform.numBits) = false := by
    have h1 : (1#System.Platform.numBits : BitVec _).toNat = 1 := by
      rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> rfl
    simp [BitVec.uaddOverflow, h1, hUB]
  simp [hno_ovf]

/-- Direct equality form of `IteratorRange.next` when `kU.val ≥ 24`:
    returns `None`. -/
private theorem IteratorRange_next_eq_none_usize
    (kU : Std.Usize) (hkU : kU.val ≥ 24) :
    CoreModels.core.iter.range.IteratorRange.next
      CoreModels.core.Usize.Insts.CoreIterRangeStep
      ({ start := kU, «end» := 24#usize } :
        CoreModels.core.ops.range.Range Std.Usize) =
      .ok (CoreModels.core.option.Option.None,
           { start := kU, «end» := 24#usize }) := by
  unfold CoreModels.core.iter.range.IteratorRange.next
  simp only [CoreModels.core.Usize.Insts.CoreCmpPartialOrdUsize,
             CoreModels.core.mkUPartialOrd]
  have hkU' : (24#usize : Std.Usize).val = 24 := rfl
  have hcmp : compare kU.val 24 ≠ Ordering.lt := by
    intro h; rw [Nat.compare_eq_lt] at h; omega
  cases h : compare kU.val 24 <;> simp_all

/-- `roundOfNat k.val ... = kU` when `kU.val = k.val`: a `Std.Usize`
    constructed from its `.val` round-trips through `roundOfNat`. -/
private theorem roundOfNat_val_eq (kU : Std.Usize) (hk : kU.val < 24) :
    roundOfNat kU.val (by omega) = kU := by
  apply Std.UScalar.eq_of_val_eq
  unfold roundOfNat
  rw [Std.UScalar.ofNatCore_val_eq]

/-- Failure propagation: if `spec_chain_hacspec s k = .fail e`, then for
    all `n ≥ k`, `spec_chain_hacspec s n = .fail e`. -/
private theorem spec_chain_hacspec_fail_mono
    (s : Std.Array Std.U64 25#usize) (k : Nat) (e : Error)
    (h : spec_chain_hacspec s k = .fail e) :
    ∀ n, spec_chain_hacspec s (k + n) = .fail e := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [show k + (n + 1) = (k + n) + 1 from rfl, spec_chain_hacspec_succ, ih]
    rfl

/-- Divergence propagation: if `spec_chain_hacspec s k = .div`, then for
    all `n ≥ k`, `spec_chain_hacspec s n = .div`. -/
private theorem spec_chain_hacspec_div_mono
    (s : Std.Array Std.U64 25#usize) (k : Nat)
    (h : spec_chain_hacspec s k = .div) :
    ∀ n, spec_chain_hacspec s (k + n) = .div := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [show k + (n + 1) = (k + n) + 1 from rfl, spec_chain_hacspec_succ, ih]
    rfl

/-- Body of the loop after the iterator step in the Some branch: the
    `θ;ρ;π;χ;ι` chain wrapped with `ok (cont ...)`. Equals
    `spec_round_step_hacspec acc kU >>= (ok (cont (iter1, ·)))` by
    definitional unfolding of `spec_round_step_hacspec`. -/
private theorem loop_body_some_eq
    (acc : Std.Array Std.U64 25#usize) (kU : Std.Usize)
    (iter1 : CoreModels.core.ops.range.Range Std.Usize) :
    (do
      let a ← keccak_f.theta acc
      let a1 ← keccak_f.rho a
      let a2 ← keccak_f.pi a1
      let a3 ← keccak_f.chi a2
      let state1 ← keccak_f.iota a3 kU
      Aeneas.Std.Result.ok
        (cont (iter1, state1) :
          ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) ×
            (Std.Array Std.U64 25#usize)) (Std.Array Std.U64 25#usize))) =
    (do
      let state1 ← spec_round_step_hacspec acc kU
      Aeneas.Std.Result.ok (cont (iter1, state1))) := by
  unfold spec_round_step_hacspec
  simp only [bind_assoc]

/-- Inductive helper: induct on `n = 24 - k`, the number of remaining
    iterations. At `n = 0` (`k = 24`), the iterator returns `None` and the
    loop yields `.ok acc`, which by hypothesis equals `spec_chain_hacspec
    s 24`. At `n + 1` (`k < 24`), the body's θ;ρ;π;χ;ι chain matches
    `spec_round_step_hacspec acc kU`; success recurses via IH on
    `(n, k+1, kU+1, acc')`, failure/div propagates to round 24 via the
    `_mono` lemmas. -/
private theorem keccak_f_loop_eq_aux (s : Std.Array Std.U64 25#usize) :
    ∀ (n k : Nat) (kU : Std.Usize) (acc : Std.Array Std.U64 25#usize),
      kU.val = k → k + n = 24 →
      spec_chain_hacspec s k = .ok acc →
      keccak_f.keccak_f_loop { start := kU, «end» := 24#usize } acc =
        spec_chain_hacspec s 24 := by
  intro n
  induction n with
  | zero =>
    intro k kU acc h_kU h_kn h_chain
    have hk : k = 24 := by omega
    subst hk
    have h_kU_ge : kU.val ≥ 24 := by rw [h_kU]
    unfold keccak_f.keccak_f_loop
    rw [loop.eq_def]
    unfold keccak_f.keccak_f_loop.body
    dsimp only
    rw [show (CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              CoreModels.core.Usize.Insts.CoreIterRangeStep
              ({ start := kU, «end» := 24#usize } :
                CoreModels.core.ops.range.Range Std.Usize)) =
          CoreModels.core.iter.range.IteratorRange.next
            CoreModels.core.Usize.Insts.CoreIterRangeStep
            { start := kU, «end» := 24#usize } from rfl]
    rw [IteratorRange_next_eq_none_usize kU h_kU_ge]
    simp
    exact h_chain.symm
  | succ n ih =>
    intro k kU acc h_kU h_kn h_chain
    have h_k_lt : k < 24 := by omega
    have h_kU_lt : kU.val < 24 := by rw [h_kU]; exact h_k_lt
    obtain ⟨kU', h_kU'_val, h_iter⟩ := IteratorRange_next_eq_some_usize kU h_kU_lt
    -- Use `spec_chain_hacspec_succ` to connect to `spec_chain_hacspec s (k+1)`.
    have h_succ := spec_chain_hacspec_succ s k
    rw [h_chain] at h_succ
    simp [spec_round_step_hacspec_at, h_k_lt] at h_succ
    have h_round : roundOfNat k (by omega) = kU := by
      subst h_kU
      exact roundOfNat_val_eq kU h_kU_lt
    rw [h_round] at h_succ
    -- Case split on `spec_round_step_hacspec acc kU`.
    cases h_step : spec_round_step_hacspec acc kU with
    | ok acc' =>
      rw [h_step] at h_succ
      -- The body chain evaluates to `ok (cont (iter', acc'))`.
      have hbody_ok :
          keccak_f.keccak_f_loop.body { start := kU, «end» := 24#usize } acc =
          .ok (.cont ({ start := kU', «end» := 24#usize }, acc')) := by
        unfold keccak_f.keccak_f_loop.body
        rw [show (CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                  CoreModels.core.Usize.Insts.CoreIterRangeStep
                  ({ start := kU, «end» := 24#usize } :
                    CoreModels.core.ops.range.Range Std.Usize)) =
              CoreModels.core.iter.range.IteratorRange.next
                CoreModels.core.Usize.Insts.CoreIterRangeStep
                { start := kU, «end» := 24#usize } from rfl]
        rw [h_iter]
        have h_body_eq := loop_body_some_eq acc kU { start := kU', «end» := 24#usize }
        change (do
                  let a ← keccak_f.theta acc
                  let a1 ← keccak_f.rho a
                  let a2 ← keccak_f.pi a1
                  let a3 ← keccak_f.chi a2
                  let state1 ← keccak_f.iota a3 kU
                  Aeneas.Std.Result.ok
                    (cont ({ start := kU', «end» := 24#usize }, state1) :
                      ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) ×
                        (Std.Array Std.U64 25#usize)) (Std.Array Std.U64 25#usize)))
                = _
        rw [h_body_eq, h_step]; rfl
      have ih' := ih (k + 1) kU' acc'
                     (by rw [h_kU'_val, h_kU]) (by omega) h_succ
      -- Unfold loop once and use hbody_ok + IH.
      unfold keccak_f.keccak_f_loop
      rw [loop.eq_def]
      dsimp only
      rw [hbody_ok]
      simp only [keccak_f.keccak_f_loop] at ih'
      exact ih'
    | fail e =>
      rw [h_step] at h_succ
      have hbody_fail :
          keccak_f.keccak_f_loop.body { start := kU, «end» := 24#usize } acc =
          .fail e := by
        unfold keccak_f.keccak_f_loop.body
        rw [show (CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                  CoreModels.core.Usize.Insts.CoreIterRangeStep
                  ({ start := kU, «end» := 24#usize } :
                    CoreModels.core.ops.range.Range Std.Usize)) =
              CoreModels.core.iter.range.IteratorRange.next
                CoreModels.core.Usize.Insts.CoreIterRangeStep
                { start := kU, «end» := 24#usize } from rfl]
        rw [h_iter]
        have h_body_eq := loop_body_some_eq acc kU { start := kU', «end» := 24#usize }
        change (do
                  let a ← keccak_f.theta acc
                  let a1 ← keccak_f.rho a
                  let a2 ← keccak_f.pi a1
                  let a3 ← keccak_f.chi a2
                  let state1 ← keccak_f.iota a3 kU
                  Aeneas.Std.Result.ok
                    (cont ({ start := kU', «end» := 24#usize }, state1) :
                      ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) ×
                        (Std.Array Std.U64 25#usize)) (Std.Array Std.U64 25#usize)))
                = _
        rw [h_body_eq, h_step]; rfl
      unfold keccak_f.keccak_f_loop
      rw [loop.eq_def]
      dsimp only
      rw [hbody_fail]
      have h_fail24 := spec_chain_hacspec_fail_mono s (k + 1) e h_succ (24 - (k + 1))
      rw [show k + 1 + (24 - (k + 1)) = 24 from by omega] at h_fail24
      exact h_fail24.symm
    | div =>
      rw [h_step] at h_succ
      have hbody_div :
          keccak_f.keccak_f_loop.body { start := kU, «end» := 24#usize } acc =
          .div := by
        unfold keccak_f.keccak_f_loop.body
        rw [show (CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                  CoreModels.core.Usize.Insts.CoreIterRangeStep
                  ({ start := kU, «end» := 24#usize } :
                    CoreModels.core.ops.range.Range Std.Usize)) =
              CoreModels.core.iter.range.IteratorRange.next
                CoreModels.core.Usize.Insts.CoreIterRangeStep
                { start := kU, «end» := 24#usize } from rfl]
        rw [h_iter]
        have h_body_eq := loop_body_some_eq acc kU { start := kU', «end» := 24#usize }
        change (do
                  let a ← keccak_f.theta acc
                  let a1 ← keccak_f.rho a
                  let a2 ← keccak_f.pi a1
                  let a3 ← keccak_f.chi a2
                  let state1 ← keccak_f.iota a3 kU
                  Aeneas.Std.Result.ok
                    (cont ({ start := kU', «end» := 24#usize }, state1) :
                      ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) ×
                        (Std.Array Std.U64 25#usize)) (Std.Array Std.U64 25#usize)))
                = _
        rw [h_body_eq, h_step]; rfl
      unfold keccak_f.keccak_f_loop
      rw [loop.eq_def]
      dsimp only
      rw [hbody_div]
      have h_div24 := spec_chain_hacspec_div_mono s (k + 1) h_succ (24 - (k + 1))
      rw [show k + 1 + (24 - (k + 1)) = 24 from by omega] at h_div24
      exact h_div24.symm

/-- **Loop bridge**: the hacspec `keccak_f.keccak_f` function equals the
    `Nat.fold 24` chain `spec_chain_hacspec s 24`.

    Instantiates `keccak_f_loop_eq_aux` at `n = 24`, `k = 0`, `kU =
    0#usize`, `acc = s`. The initial spec_chain hypothesis is
    `spec_chain_hacspec s 0 = .ok s` (by `spec_chain_hacspec_zero`). -/
theorem keccak_f_loop_eq_spec_chain_hacspec
    (s : Std.Array Std.U64 25#usize) :
    keccak_f.keccak_f s = spec_chain_hacspec s 24 := by
  unfold keccak_f.keccak_f
  exact keccak_f_loop_eq_aux s 24 0 0#usize s rfl rfl (spec_chain_hacspec_zero s)


/-! ## Bridge 1 closure: spec_round_step / spec_chain equality

`spec_round_step_hacspec` and `spec_round_step` are identical (both go
through `keccak_f.theta / rho / pi / chi`), so the equality is
definitional. -/

theorem spec_round_step_hacspec_eq_spec_round_step
    (state : Std.Array Std.U64 25#usize) (round : Std.Usize) :
    spec_round_step_hacspec state round = spec_round_step state round := by
  unfold spec_round_step_hacspec spec_round_step
  rfl

theorem spec_chain_hacspec_eq_spec_chain
    (s : Std.Array Std.U64 25#usize) (n : Nat) :
    spec_chain_hacspec s n = spec_chain s n := by
  induction n with
  | zero => rw [spec_chain_hacspec_zero, spec_chain_zero]
  | succ k ih =>
    rw [spec_chain_hacspec_succ, spec_chain_succ, ih]
    -- `spec_round_step_hacspec_at` and `spec_round_step_at` are
    -- definitionally equal — `congr 1` closes.
    congr 1

/-! ## Top-level theorem: impl ↔ hacspec

`keccak.keccakf1600 s` succeeds and produces `r_impl` such that the
hacspec `keccak_f.keccak_f` applied to `lift s` succeeds with
`lift r_impl`. Composes `keccakf1600_equiv_via_bit` (the structural + algebraic equivalences
canonical post) with `spec_chain_hacspec ↔ spec_chain` (Bridge 1) and
`keccak_f_loop_eq_spec_chain_hacspec` (loop bridge). -/

theorem keccakf1600_equiv_hacspec (s : state.KeccakState)
    (h_i : s.i = 0#usize) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600 s
    ⦃ ⇓ r_impl => ⌜ keccak_f.keccak_f (lift s) = .ok (lift r_impl) ⌝ ⦄ := by
  -- Start from `keccakf1600_equiv_via_bit`'s canonical post.
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_equiv_via_bit s h_i)
  rw [PostCond.entails_noThrow]
  intro r h_post
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_post ⊢
  -- `h_post : keccakf1600_post_canonical s r`.
  -- Unfold the canonical post to get the spec_chain equation.
  unfold keccakf1600_post_canonical at h_post
  -- Convert the `Nat.fold` form to `spec_chain`.
  have h_chain :
      (do let lifted_final ← spec_chain (Foundation.lift s) 24
          pure (lifted_final = Foundation.lift r)).holds := by
    have h_eq :
        (do let lifted_final ← Nat.fold 24
              (fun i h acc => acc >>= fun st => spec_round_step st (roundOfNat i (by omega)))
              (pure (Foundation.lift s))
            pure (lifted_final = Foundation.lift r)).holds
        = (do let lifted_final ← spec_chain (Foundation.lift s) 24
              pure (lifted_final = Foundation.lift r)).holds := by
      unfold spec_chain spec_round_step_at
      congr 1
    rw [h_eq] at h_post
    exact h_post
  -- Extract spec_chain (lift s) 24 = .ok (lift r).
  have h_spec_chain : spec_chain (Foundation.lift s) 24 = .ok (Foundation.lift r) :=
    holds_chain_eq_ok h_chain
  -- Bridge via spec_chain_hacspec and keccak_f_loop_eq_spec_chain_hacspec.
  rw [keccak_f_loop_eq_spec_chain_hacspec, spec_chain_hacspec_eq_spec_chain]
  exact h_spec_chain

end libcrux_iot_sha3.Composition
