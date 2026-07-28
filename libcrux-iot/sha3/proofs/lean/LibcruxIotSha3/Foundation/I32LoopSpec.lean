/-
  I32 iterator + range-loop spec helpers.

  Provides:
  - `IteratorRange_next_spec_i32` — Hoare spec for one `IteratorRange.next`
    step over an `I32` range, splitting on `i.val < e.val`.
  - `loop_range_spec_i32` — induction principle for `loop` over
    `core.ops.range.Range I32`, parameterised by an invariant `inv`.

  Used by `StructuralEquiv.lean` to verify the 6-iteration
  `keccakf1600` round-bundle loop.
-/
import LibcruxIotSha3.Foundation.SpecStep

open Aeneas Aeneas.Std Result ControlFlow Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Foundation

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-! ### Triple → Result-equation converter

When each call_mut's purity is stated as a Triple (natural for
`hax_mvcgen`-driven proofs), the Result equation needed by
`createi_pure_eq` follows directly. Used both here (in this file's
loop-spec helpers) and externally (in `HacspecBridge.lean`). -/

-- `result_eq_of_triple` is now defined in `Lift.lean` (lower in the import
-- chain). Re-exported here only via transitive import.

/-! ## I32 iterator-next spec

The `CoreModels.core.I32.Insts.CoreIterRangeStep` instance (defined
in `Extraction/Missing.lean:25`) uses `IScalar.tryMk .I32 (start.val +
1)` for `forward_checked`. For our use case (range `[0, 6)`), the
bounds are well within I32 and `tryMk` succeeds. -/

theorem IteratorRange_next_spec_i32 (i e : Std.I32)
    (h_e_lt_max : e.val < 2^31) {Q}
    (h_lt : (h : i.val < e.val) →
      ∀ (s : Std.I32), s.val = i.val + 1 →
        (Q.1 (some i, { start := s, «end» := e })).down)
    (h_ge : i.val ≥ e.val →
      (Q.1 (none, { start := i, «end» := e })).down) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.iter.range.IteratorRange.next CoreModels.core.I32.Insts.CoreIterRangeStep
      { start := i, «end» := e }
    ⦃ Q ⦄ := by
  rcases lt_or_ge i.val e.val with hlt | hge
  · -- i < e: `forward_checked` succeeds with no overflow, start advances by 1.
    have hcmp : compare i.val e.val = Ordering.lt := Int.compare_eq_lt.mpr hlt
    have hmin : (-2147483648 : Int) ≤ i.val := by scalar_tac
    -- the `1#usize`, cast through u32 then hcast to i32, has value 1
    have h1val : (UScalar.hcast IScalarTy.I32 (UScalar.cast UScalarTy.U32 1#usize)).val = 1 := by
      simp only [UScalar.hcast, UScalar.cast, IScalarTy.I32_numBits_eq, UScalarTy.U32_numBits_eq]
      simp; decide
    -- the wrapping_add does not overflow: i.val + 1 ∈ [-2^31, 2^31)
    have hwval : (Std.I32.wrapping_add i
        (UScalar.hcast IScalarTy.I32 (UScalar.cast UScalarTy.U32 1#usize))).val = i.val + 1 := by
      rw [Std.I32.wrapping_add_val_eq, h1val, Int.bmod_eq_emod]
      simp only [Nat.reducePow]
      split <;> omega
    -- the same no-overflow fact, in the `bmod` form `simp` exposes
    have hbmod : ((i.val : Int) + 1).bmod 4294967296 = i.val + 1 := by
      rw [Int.bmod_eq_emod]; split <;> omega
    -- `try_from 1#usize` succeeds (1 is in range for u32).
    have htry : CoreModels.core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from 1#usize
        = .ok (CoreModels.core.result.Result.Ok (UScalar.cast UScalarTy.U32 1#usize)) := by
      unfold CoreModels.core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
      simp [Aeneas.Std.lift, U32.rMax]
    have h_eq : CoreModels.core.iter.range.IteratorRange.next
        CoreModels.core.I32.Insts.CoreIterRangeStep { start := i, «end» := e }
      = .ok (CoreModels.core.option.Option.Some i,
             { start := Std.I32.wrapping_add i
                 (UScalar.hcast IScalarTy.I32 (UScalar.cast UScalarTy.U32 1#usize)),
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
  · -- i ≥ e: `next` returns `none`.
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

/-! ## I32 loop-over-range spec

Specialized to `loop` over `core.ops.range.Range I32`. -/

section loop_range_i32_helpers

private abbrev ResultPS := PostShape.except Error (PostShape.except PUnit PostShape.pure)

private theorem triple_noThrow_elim_i32 {α : Type} {x : Result α} {Q : α → Assertion ResultPS}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) {v : α} (hv : x = ok v) :
    (Q v).down := by
  subst hv; simpa [Triple, WP.wp, PredTrans.apply] using h

private theorem triple_noThrow_exists_ok_i32 {α : Type} {x : Result α}
    {Q : α → Assertion ResultPS}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) : ∃ v, x = ok v := by
  match x, h with
  | .ok v, _ => exact ⟨v, rfl⟩
  | .fail _, h => exact absurd h (by simp [Triple, WP.wp, PredTrans.apply])
  | .div, h => exact absurd h (by simp [Triple, WP.wp, PredTrans.apply])

private theorem triple_of_ok_i32 {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = ok v) (hp : P v) :
    (⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) := by
  subst hx; simp [Triple, WP.wp, PredTrans.apply, hp]

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

end libcrux_iot_sha3.Foundation
