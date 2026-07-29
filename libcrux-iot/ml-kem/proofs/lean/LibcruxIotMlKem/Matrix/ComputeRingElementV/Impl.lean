/-
  # `Matrix/ComputeRingElementV/Impl.lean` — L7.3 chunks-exact loop keystone.

  Domain-free iterator infrastructure for the `loop` in
  `matrix.compute_ring_element_v_loop`, which iterates over a
  `Enumerate (ChunksExact U8)` via the `loop` combinator. There is no Mathlib,
  no ZMod, no mont reasoning here — purely Slice / Usize / iterator facts.

  Mirrors the EXISTING range-loop keystone `loop_range_spec_usize`: same induction skeleton, with `e.val - start.val`
  replaced by `numChunks - k` (k = enumerate count).

  Deliverables:
  * `enumerate_chunks_next_cont` / `enumerate_chunks_next_done` — equational
    characterization of `Enumerate.next` over `ChunksExact`.
  * `loop_chunks_exact_enumerate_spec` — the loop Hoare spec (keystone).
-/
import LibcruxIotMlKem.Spec.Lift
import LibcruxIotMlKem.Vector.Portable.Arithmetic.PerElement
import LibcruxIotMlKem.Vector.Portable.Arithmetic.Element
import LibcruxIotMlKem.Vector.Portable.Ntt
import LibcruxIotMlKem.Ntt
import LibcruxIotMlKem.InvertNtt
import LibcruxIotMlKem.Polynomial.NttDrivers
import LibcruxIotMlKem.Polynomial.PolyOps
import LibcruxIotMlKem.Polynomial.PolyOpsFcBarrett
import LibcruxIotMlKem.Polynomial.PolyOpsFc
import LibcruxIotMlKem.Polynomial.NttMultiply
import LibcruxIotMlKem.Matrix.Common
import LibcruxIotMlKem.Matrix.ComputeAsPlusE
import LibcruxIotMlKem.Sampling
import LibcruxIotMlKem.Serialize
import LibcruxIotMlKem.Matrix.ComputeMessage.Impl
import LibcruxIotMlKem.Matrix.ComputeMessage.Hacspec

namespace libcrux_iot_ml_kem.Matrix.ComputeRingElementV.Impl
open libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeMessage.Bridges libcrux_iot_ml_kem.Matrix.ComputeMessage.Hacspec libcrux_iot_ml_kem.Matrix.ComputeMessage.Impl
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec
open Result ControlFlow

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-- Local copy of FCTargets' `private triple_exists_ok_fc`. -/
private theorem triple_exists_ok_fc {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl, (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

/-- The concrete `Enumerate (ChunksExact U8)` iterator state type. -/
abbrev EnumCE :=
  CoreModels.core.iter.adapters.enumerate.Enumerate
    (CoreModels.core.slice.iter.ChunksExact Std.U8)

/-- The fully-applied `Enumerate.next` function for our iterator. -/
noncomputable abbrev enumCENext (it : EnumCE) :
    Result ((CoreModels.core.option.Option (Std.Usize × Slice Std.U8)) × EnumCE) :=
  CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
    (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice
      Std.U8) it

/-! ## Deliverable 1 — `Enumerate.next` characterization -/

/-- Enumerate-over-ChunksExact `next` when at least `cs` bytes remain:
    yields the current count paired with the first `cs` bytes, advances. -/
theorem enumerate_chunks_next_cont
    (rest : Slice Std.U8) (cs cnt : Std.Usize)
    (h_le : cs.val ≤ rest.length) (h_cnt : cnt.val + 1 ≤ Std.Usize.max) :
    ∃ (chunk drop : Slice Std.U8) (cnt' : Std.Usize),
      enumCENext { iter := { cs := cs, elements := rest }, count := cnt }
        = .ok (CoreModels.core.option.Option.Some (cnt, chunk),
               { iter := { cs := cs, elements := drop }, count := cnt' })
      ∧ cnt'.val = cnt.val + 1
      ∧ chunk.length = cs.val
      ∧ drop.length = rest.length - cs.val
      ∧ (∀ ℓ : Nat, ℓ < cs.val → chunk.val[ℓ]! = rest.val[ℓ]!) := by
  -- `split_at` succeeds since `cs ≤ rest.length`.
  have hsa := core.slice.Slice.split_at.spec rest cs (by simpa using h_le)
  obtain ⟨⟨s0, s1⟩, hsa_eq, hs0len, hs1len, hs0val, hs1val⟩ := WP.spec_imp_exists hsa
  -- `cnt + 1#usize` succeeds.
  have hadd := Std.Usize.add_spec (x := cnt) (y := 1#usize)
    (by have : (1#usize : Std.Usize).val = 1 := rfl; omega)
  obtain ⟨cnt', hcnt'_eq, hcnt'_post⟩ := WP.spec_imp_exists hadd
  have hcnt'_val : cnt'.val = cnt.val + 1 := by
    have h1 : (1#usize : Std.Usize).val = 1 := rfl
    simp only [h1] at hcnt'_post; omega
  refine ⟨s0, s1, cnt', ?_, hcnt'_val, hs0len, hs1len, ?_⟩
  · -- compute the `next`
    simp only [enumCENext,
      CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next,
      CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next]
    have h_le' : cs.val ≤ rest.val.length := by simpa [Slice.length] using h_le
    rw [hsa_eq]
    simp only [h_le', ↓reduceIte, bind_assoc]
    rw [hcnt'_eq]
    rfl
  · -- the element relation
    intro ℓ hℓ
    rw [hs0val, List.getElem!_take_of_lt _ _ _ hℓ]

/-- Enumerate-over-ChunksExact `next` when fewer than `cs` bytes remain:
    terminates. -/
theorem enumerate_chunks_next_done
    (rest : Slice Std.U8) (cs cnt : Std.Usize) (h_lt : rest.length < cs.val) :
    enumCENext { iter := { cs := cs, elements := rest }, count := cnt }
      = .ok (CoreModels.core.option.Option.None,
             { iter := { cs := cs, elements := rest }, count := cnt }) := by
  simp only [enumCENext,
    CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next,
    CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next]
  have hng : ¬ (cs.val ≤ rest.val.length) := by
    simp only [Slice.length] at h_lt; omega
  simp only [hng, ↓reduceIte]
  rfl

/-! ## Deliverable 2 — the loop Hoare spec keystone

Mirrors `loop_range_spec_usize`: same induction
skeleton with `e.val - start.val` replaced by `numChunks - k`. The three
`triple_noThrow_*_chunks` helpers below are verbatim copies of the
`triple_noThrow_*_usize` machinery, renamed to avoid clashes. -/

section loop_chunks_helpers

private abbrev ResultPSU := PostShape.except Error (PostShape.except PUnit PostShape.pure)

private theorem triple_noThrow_elim_chunks {α : Type} {x : Result α}
    {Q : α → Assertion ResultPSU}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) {v : α} (hv : x = ok v) :
    (Q v).down := by
  subst hv; simpa [Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h

private theorem triple_noThrow_exists_ok_chunks {α : Type} {x : Result α}
    {Q : α → Assertion ResultPSU}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) : ∃ v, x = ok v := by
  match x, h with
  | .ok v, _ => exact ⟨v, rfl⟩
  | .fail _, h => exact absurd h (by simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div, h => exact absurd h (by simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

private theorem triple_of_ok_chunks {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = ok v) (hp : P v) :
    (⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) := by
  subst hx; simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

end loop_chunks_helpers

set_option maxHeartbeats 2000000 in
/-- Loop-over-`Enumerate (ChunksExact U8)` spec. An invariant `inv : Nat → β →
    Result Prop`, indexed by the enumerate count `k`, is preserved by each step.
    Induction on `numChunks - k`. -/
theorem loop_chunks_exact_enumerate_spec {β : Type}
    (body : (EnumCE × β) → Result (ControlFlow (EnumCE × β) β))
    (init : β) (fullSlice : Slice Std.U8) (cs : Std.Usize) (numChunks : Nat)
    (inv : Nat → β → Result Prop)
    (h_cs_pos : 0 < cs.val)
    (h_len : fullSlice.length = numChunks * cs.val)
    (h_init : (inv 0 init).holds)
    (h_step : ∀ (acc : β) (k : Nat) (rest : Slice Std.U8) (cnt : Std.Usize),
        k ≤ numChunks → cnt.val = k → rest.length = (numChunks - k) * cs.val →
        (inv k acc).holds →
        ⦃ ⌜ True ⌝ ⦄
        body ({ iter := { cs := cs, elements := rest }, count := cnt }, acc)
        ⦃ ⇓ r => match r with
          | .cont (iter', acc') =>
              ⌜ k < numChunks ∧ iter'.iter.cs = cs ∧ iter'.count.val = k + 1
                ∧ iter'.iter.elements.length = (numChunks - (k + 1)) * cs.val
                ∧ (inv (k + 1) acc').holds ⌝
          | .done y => ⌜ (inv numChunks y).holds ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    loop body ({ iter := { cs := cs, elements := fullSlice }, count := 0#usize }, init)
    ⦃ ⇓ r => ⌜ (inv numChunks r).holds ⌝ ⦄ := by
  suffices gen : ∀ (n : Nat) (acc : β) (rest : Slice Std.U8) (cnt : Std.Usize),
      numChunks - cnt.val = n → cnt.val ≤ numChunks →
      rest.length = (numChunks - cnt.val) * cs.val →
      (inv cnt.val acc).holds →
      ⦃ ⌜ True ⌝ ⦄
      loop body ({ iter := { cs := cs, elements := rest }, count := cnt }, acc)
      ⦃ ⇓ r => ⌜ (inv numChunks r).holds ⌝ ⦄ by
    have h0 : (0#usize : Std.Usize).val = 0 := rfl
    refine gen _ init fullSlice 0#usize rfl (by rw [h0]; exact Nat.zero_le _) ?_ ?_
    · rw [h0]; simpa using h_len
    · rw [h0]; exact h_init
  intro n
  induction n with
  | zero =>
    intro acc rest cnt hn hcnt_le hlen hinv
    -- numChunks - cnt.val = 0 with cnt.val ≤ numChunks ⟹ cnt.val = numChunks
    have hcnt_eq : cnt.val = numChunks := by omega
    have hs := h_step acc cnt.val rest cnt hcnt_le rfl hlen hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok_chunks hs
    have hpost := triple_noThrow_elim_chunks hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .cont (iter', acc') =>
      simp only at hpost
      exact absurd hpost.1 (by rw [hcnt_eq]; exact Nat.lt_irrefl _)
    | .done y =>
      simp only at hpost
      exact triple_of_ok_chunks rfl hpost
  | succ n ih =>
    intro acc rest cnt hn hcnt_le hlen hinv
    have hcnt_lt : cnt.val < numChunks := by omega
    have hs := h_step acc cnt.val rest cnt hcnt_le rfl hlen hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok_chunks hs
    have hpost := triple_noThrow_elim_chunks hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .done y =>
      simp only at hpost
      exact triple_of_ok_chunks rfl hpost
    | .cont (iter', acc') =>
      simp only at hpost
      obtain ⟨hlt, hcs, hcnt', hlen', hinv'⟩ := hpost
      -- reconstruct iter' from its fields
      have hiter : iter'
          = { iter := { cs := cs, elements := iter'.iter.elements },
              count := iter'.count } := by
        cases iter' with
        | mk it ct => cases it with | mk csv el => cases hcs; rfl
      rw [hiter]
      refine ih acc' iter'.iter.elements iter'.count ?_ ?_ ?_ ?_
      · rw [hcnt']; omega
      · rw [hcnt']; omega
      · rw [hcnt']; exact hlen'
      · rw [hcnt']; exact hinv'

/-! ## Deliverable 1b — public-key-suffix-aware loop spec (L7.3 keystone)

The generic `loop_chunks_exact_enumerate_spec` exposes `rest` in `h_step` with
only a length hypothesis, NOT the byte-content relation needed to apply the A2
axiom `deserialize_to_reduced_ring_element_fc` (which requires
`chunk_bytes.val[ℓ]! = public_key.val[i*cs+ℓ]!`). This specialized keystone
threads the suffix relation `rest.val[ℓ]! = fullSlice.val[k*cs+ℓ]!` through the
induction, so `h_step` receives it at each `k`. -/

/-- Enumerate-over-ChunksExact `next` `drop`-suffix companion: in the `.cont`
    case the advanced slice `drop` is the `cs`-tail of `rest`, i.e.
    `drop.val[ℓ]! = rest.val[cs + ℓ]!`. Proven from `split_at.spec`'s
    `s1.val = s.val.drop cs`. -/
theorem enumerate_chunks_next_cont_drop
    (rest : Slice Std.U8) (cs cnt : Std.Usize)
    (h_le : cs.val ≤ rest.length) (h_cnt : cnt.val + 1 ≤ Std.Usize.max) :
    ∃ (chunk drop : Slice Std.U8) (cnt' : Std.Usize),
      enumCENext { iter := { cs := cs, elements := rest }, count := cnt }
        = .ok (CoreModels.core.option.Option.Some (cnt, chunk),
               { iter := { cs := cs, elements := drop }, count := cnt' })
      ∧ cnt'.val = cnt.val + 1
      ∧ chunk.length = cs.val
      ∧ drop.length = rest.length - cs.val
      ∧ (∀ ℓ : Nat, ℓ < cs.val → chunk.val[ℓ]! = rest.val[ℓ]!)
      ∧ (∀ ℓ : Nat, drop.val[ℓ]! = rest.val[cs.val + ℓ]!) := by
  have hsa := core.slice.Slice.split_at.spec rest cs (by simpa using h_le)
  obtain ⟨⟨s0, s1⟩, hsa_eq, hs0len, hs1len, hs0val, hs1val⟩ := WP.spec_imp_exists hsa
  have hadd := Std.Usize.add_spec (x := cnt) (y := 1#usize)
    (by have : (1#usize : Std.Usize).val = 1 := rfl; omega)
  obtain ⟨cnt', hcnt'_eq, hcnt'_post⟩ := WP.spec_imp_exists hadd
  have hcnt'_val : cnt'.val = cnt.val + 1 := by
    have h1 : (1#usize : Std.Usize).val = 1 := rfl
    simp only [h1] at hcnt'_post; omega
  refine ⟨s0, s1, cnt', ?_, hcnt'_val, hs0len, hs1len, ?_, ?_⟩
  · simp only [enumCENext,
      CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next,
      CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next]
    have h_le' : cs.val ≤ rest.val.length := by simpa [Slice.length] using h_le
    rw [hsa_eq]
    simp only [h_le', ↓reduceIte, bind_assoc]
    rw [hcnt'_eq]
    rfl
  · intro ℓ hℓ
    rw [hs0val, List.getElem!_take_of_lt _ _ _ hℓ]
  · intro ℓ
    rw [hs1val]
    by_cases hℓ : ℓ < (List.drop cs.val rest.val).length
    · rw [getElem!_pos (List.drop cs.val rest.val) ℓ hℓ]
      have hℓ' : cs.val + ℓ < rest.val.length := by
        rw [List.length_drop] at hℓ; omega
      rw [getElem!_pos rest.val (cs.val + ℓ) hℓ']
      rw [List.getElem_drop]
    · -- out-of-range: both default.
      have hℓr : ¬ (cs.val + ℓ < rest.val.length) := by
        rw [List.length_drop] at hℓ; omega
      rw [getElem!_neg (List.drop cs.val rest.val) ℓ hℓ,
          getElem!_neg rest.val (cs.val + ℓ) hℓr]

set_option maxHeartbeats 2000000 in
/-- Public-key-suffix-aware loop spec: like `loop_chunks_exact_enumerate_spec`,
    but additionally threads the byte-content suffix relation
    `rest.val[ℓ]! = fullSlice.val[k*cs+ℓ]!` to `h_step` at each `k`. The body
    receives, at count `k`, the slice `rest` positioned at byte-offset `k*cs`
    in `fullSlice`. Induction on `numChunks - k`, carrying the suffix relation
    `∀ ℓ, rest.val[ℓ]! = fullSlice.val[cnt.val*cs.val + ℓ]!`. -/
theorem loop_chunks_exact_pk_spec {β : Type}
    (body : (EnumCE × β) → Result (ControlFlow (EnumCE × β) β))
    (init : β) (fullSlice : Slice Std.U8) (cs : Std.Usize) (numChunks : Nat)
    (inv : Nat → β → Result Prop)
    (h_cs_pos : 0 < cs.val)
    (h_len : fullSlice.length = numChunks * cs.val)
    (h_init : (inv 0 init).holds)
    (h_step : ∀ (acc : β) (k : Nat) (rest : Slice Std.U8) (cnt : Std.Usize),
        k ≤ numChunks → cnt.val = k → rest.length = (numChunks - k) * cs.val →
        (∀ ℓ : Nat, rest.val[ℓ]! = fullSlice.val[k * cs.val + ℓ]!) →
        (inv k acc).holds →
        ⦃ ⌜ True ⌝ ⦄
        body ({ iter := { cs := cs, elements := rest }, count := cnt }, acc)
        ⦃ ⇓ r => match r with
          | .cont (iter', acc') =>
              ⌜ k < numChunks ∧ iter'.iter.cs = cs ∧ iter'.count.val = k + 1
                ∧ iter'.iter.elements.length = (numChunks - (k + 1)) * cs.val
                ∧ (∀ ℓ : Nat, iter'.iter.elements.val[ℓ]!
                      = fullSlice.val[(k + 1) * cs.val + ℓ]!)
                ∧ (inv (k + 1) acc').holds ⌝
          | .done y => ⌜ (inv numChunks y).holds ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    loop body ({ iter := { cs := cs, elements := fullSlice }, count := 0#usize }, init)
    ⦃ ⇓ r => ⌜ (inv numChunks r).holds ⌝ ⦄ := by
  suffices gen : ∀ (n : Nat) (acc : β) (rest : Slice Std.U8) (cnt : Std.Usize),
      numChunks - cnt.val = n → cnt.val ≤ numChunks →
      rest.length = (numChunks - cnt.val) * cs.val →
      (∀ ℓ : Nat, rest.val[ℓ]! = fullSlice.val[cnt.val * cs.val + ℓ]!) →
      (inv cnt.val acc).holds →
      ⦃ ⌜ True ⌝ ⦄
      loop body ({ iter := { cs := cs, elements := rest }, count := cnt }, acc)
      ⦃ ⇓ r => ⌜ (inv numChunks r).holds ⌝ ⦄ by
    have h0 : (0#usize : Std.Usize).val = 0 := rfl
    refine gen _ init fullSlice 0#usize rfl (by rw [h0]; exact Nat.zero_le _) ?_ ?_ ?_
    · rw [h0]; simpa using h_len
    · rw [h0]; intro ℓ; simp
    · rw [h0]; exact h_init
  intro n
  induction n with
  | zero =>
    intro acc rest cnt hn hcnt_le hlen hsuf hinv
    have hcnt_eq : cnt.val = numChunks := by omega
    have hs := h_step acc cnt.val rest cnt hcnt_le rfl hlen
      (by rw [hcnt_eq] at hsuf ⊢; exact hsuf) hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok_chunks hs
    have hpost := triple_noThrow_elim_chunks hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .cont (iter', acc') =>
      simp only at hpost
      exact absurd hpost.1 (by rw [hcnt_eq]; exact Nat.lt_irrefl _)
    | .done y =>
      simp only at hpost
      exact triple_of_ok_chunks rfl hpost
  | succ n ih =>
    intro acc rest cnt hn hcnt_le hlen hsuf hinv
    have hcnt_lt : cnt.val < numChunks := by omega
    have hs := h_step acc cnt.val rest cnt hcnt_le rfl hlen hsuf hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok_chunks hs
    have hpost := triple_noThrow_elim_chunks hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .done y =>
      simp only at hpost
      exact triple_of_ok_chunks rfl hpost
    | .cont (iter', acc') =>
      simp only at hpost
      obtain ⟨hlt, hcs, hcnt', hlen', hsuf', hinv'⟩ := hpost
      have hiter : iter'
          = { iter := { cs := cs, elements := iter'.iter.elements },
              count := iter'.count } := by
        cases iter' with
        | mk it ct => cases it with | mk csv el => cases hcs; rfl
      rw [hiter]
      refine ih acc' iter'.iter.elements iter'.count ?_ ?_ ?_ ?_ ?_
      · rw [hcnt']; omega
      · rw [hcnt']; omega
      · rw [hcnt']; exact hlen'
      · rw [hcnt']; exact hsuf'
      · rw [hcnt']; exact hinv'

/-! ## §L7.3-loop — chunks-exact USE-CACHE column loop (namespace `ChunkLoopFC`).

    The `matrix.compute_ring_element_v_loop` body, per enumerate count `i`:
    * classify_ref the chunk (identity cast),
    * `deserialize_to_reduced_ring_element` → `t̂[i]` (A2 axiom, the discarded
      poly is captured in the existential witness `mp`),
    * read `r_as_ntt[i]`, `cache[i]` (read-only),
    * `accumulating_ntt_multiply_use_cache` → acc += t̂[i]·r[i].

    Structurally `RowIFillFC.row_i_inv` (USE-CACHE, 2-conjunct existential-mp) with
    the matrix factor pinned to `(lift_t_as_ntt_from_public_key public_key K)`
    (the deserialize axiom) instead of `(lift_matrix_from_seed seed K).val[i]`.
    The loop carries `(t_as_ntt_entry, acc)`. -/

namespace ChunkLoopFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow
open libcrux_iot_ml_kem.InvertNtt libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeAsPlusE libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.NttMultiply libcrux_iot_ml_kem.Polynomial.PolyOpsFc libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Sampling libcrux_iot_ml_kem.Serialize libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt

abbrev Acc := UseCacheFC.Acc
abbrev Poly := UseCacheFC.Poly

/-- 2-conjunct invariant for the chunks-exact USE-CACHE column loop, in the
    RESOLVED all-mont/existential form. `t̂rows` is the canonical deserialized
    t-as-ntt rows `lift_t_as_ntt_from_public_key public_key K`. The impl
    DISCARDS each deserialized poly (only `t_as_ntt_entry` = the last one and
    the I32 accumulator survive), so we existentially quantify over the ACTUAL
    deserialized polys `mp : Array Poly K`, tie them to the canonical rows via
    the axiom (`lift_poly (mp[c]) = t̂rows[c]`), and characterize the
    accumulator in the all-mont form. β = `Poly × Acc` (the carried
    `t_as_ntt_entry` is ignored by the invariant). -/
def loop_inv {K : Std.Usize}
    (trows : Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K)
    (r_arr : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init : Acc) :
    Nat → (Poly × Acc) → Result Prop :=
  fun k p => pure (
    (∃ mp : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K,
       (∀ c : Nat, c < k →
          lift_poly (mp.val[c]!) = trows.val[c]!
          ∧ (∀ a : Fin 16, ∀ b : Fin 16,
               ((mp.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328))
       ∧ (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
           Spec.mont_reduce_pure (lift_fe_int (p.2.val[16 * j + ℓ]!).val)
             = (List.range k).foldl
                 (fun s c =>
                   libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                     ((Spec.ntt_multiply_pure_no_acc
                         (lift_chunk_mont (mp.val[c]!.coefficients.val[j]!))
                         (lift_chunk_mont (r_arr.val[c]!.coefficients.val[j]!))
                         (Spec.zeta_at (64 + 4 * j))
                         (Spec.zeta_at (64 + 4 * j + 1))
                         (Spec.zeta_at (64 + 4 * j + 2))
                         (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                 (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))))
    ∧ (∀ n : Nat, n < 256 →
        (p.2.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + k * 2^25))

end ChunkLoopFC

-- Memory hygiene (rule 1). Mirrors `L7_2b_irreducible`. We do NOT mark
-- `ChunkLoopFC.loop_inv` irreducible (preserve `simpa`-based destructure).
section L7_3_irreducible
open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow
open libcrux_iot_ml_kem.InvertNtt libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeAsPlusE libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.NttMultiply libcrux_iot_ml_kem.Polynomial.PolyOpsFc libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Sampling libcrux_iot_ml_kem.Serialize libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt

attribute [local irreducible] accumulating_ntt_multiply_poly_post
attribute [local irreducible] accumulating_ntt_multiply_poly_cache_post
attribute [local irreducible] Spec.ntt_multiply_pure_no_acc
attribute [local irreducible] Spec.mont_reduce_pure

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for the chunks-exact USE-CACHE column loop of
    `compute_ring_element_v`. Dispatches: `Enumerate.next` (cont) →
    `classify_ref` (identity) → `deserialize_to_reduced_ring_element` (A2 axiom,
    fed the public-key-suffix relation) → `accumulating_ntt_multiply_use_cache`.
    Re-establishes `loop_inv` at `k+1`.

    Mirrors `compute_vector_u_loop1_loop0_step_lemma_fc` (the SAMPLED USE-CACHE
    row-i loop) with the range-iterator `.next` replaced by the enumerate-chunks
    `.next` (via `enumerate_chunks_next_cont`) and `sample_matrix_entry_fc`
    replaced by `deserialize_to_reduced_ring_element_fc`. -/
private theorem compute_ring_element_v_loop_step_lemma_fc
    {K : Std.Usize}
    (public_key : Slice Std.U8) (h_pk_len : public_key.length = K.val * 384)
    (r_as_ntt cache : Slice
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (r_arr : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init : ChunkLoopFC.Acc)
    (h_r_len : r_as_ntt.length = K.val)
    (h_cache_len : cache.length = K.val)
    (h_r_arr : ∀ c : Nat, c < K.val → r_arr.val[c]! = r_as_ntt.val[c]!)
    (h_r_bnd : ∀ c : Nat, c < K.val → ∀ a : Fin 16, ∀ b : Fin 16,
        ((r_as_ntt.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_acc_bnd : ∀ n : Fin 256,
        (acc_init.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30)
    (h_cache_char : ∀ c : Nat, c < K.val →
        accumulating_ntt_multiply_poly_cache_post (r_as_ntt.val[c]!) (cache.val[c]!))
    (t_as_ntt_entry : ChunkLoopFC.Poly)
    (acc : ChunkLoopFC.Acc)
    (k : Nat) (h_le : k ≤ K.val)
    (rest : Slice Std.U8) (cnt : Std.Usize)
    (h_cnt : cnt.val = k)
    (h_rest_len : rest.length = (K.val - k) * 384)
    (h_suf : ∀ ℓ : Nat, rest.val[ℓ]! = public_key.val[k * 384 + ℓ]!)
    (h_inv : (ChunkLoopFC.loop_inv (lift_t_as_ntt_from_public_key public_key K) r_arr acc_init
                k (t_as_ntt_entry, acc)).holds) :
    ⦃ ⌜ True ⌝ ⦄
    matrix.compute_ring_element_v_loop.body
      (vectortraitsOperationsInst := portable_ops_inst) r_as_ntt cache
      { iter := { cs := 384#usize, elements := rest }, count := cnt } t_as_ntt_entry acc
    ⦃ ⇓ r => match r with
        | .cont (iter', acc') =>
            ⌜ k < K.val ∧ iter'.iter.cs = 384#usize ∧ iter'.count.val = k + 1
              ∧ iter'.iter.elements.length = (K.val - (k + 1)) * 384
              ∧ (∀ ℓ : Nat, iter'.iter.elements.val[ℓ]!
                    = public_key.val[(k + 1) * 384 + ℓ]!)
              ∧ (ChunkLoopFC.loop_inv (lift_t_as_ntt_from_public_key public_key K) r_arr acc_init
                    (k + 1) acc').holds ⌝
        | .done y => ⌜ (ChunkLoopFC.loop_inv (lift_t_as_ntt_from_public_key public_key K) r_arr
                          acc_init K.val y).holds ⌝ ⦄ := by
  set trows : Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K :=
    lift_t_as_ntt_from_public_key public_key K with htrows_def
  have h_acc_len : acc.length = 256 := Std.Array.length_eq acc
  have h_acc_init_len : acc_init.length = 256 := Std.Array.length_eq acc_init
  -- Destructure the 2-conjunct invariant (`.2` of the carried pair reduces to `acc`).
  obtain ⟨⟨mp, h_mp_agree, h_inv_acc⟩, h_inv_acc_bnd⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  dsimp only at h_inv_acc h_inv_acc_bnd
  unfold matrix.compute_ring_element_v_loop.body
  by_cases h_lt : k < K.val
  · -- `Some (cnt, chunk)` branch.
    -- (1) Enumerate.next reduces to .ok (Some (cnt, chunk), advanced).
    have h_cs_le : (384#usize : Std.Usize).val ≤ rest.length := by
      rw [h_rest_len]
      have : 1 ≤ K.val - k := by omega
      have : (384#usize : Std.Usize).val = 384 := rfl
      calc (384#usize : Std.Usize).val = 1 * 384 := by simp
        _ ≤ (K.val - k) * 384 := by
            apply Nat.mul_le_mul_right; omega
    have hcnt_lt : cnt.val < K.val := by rw [h_cnt]; exact h_lt
    have h_cnt_max : cnt.val + 1 ≤ Std.Usize.max := by
      have hKmax : K.val ≤ Std.Usize.max := by
        have h2 : public_key.length ≤ Std.Usize.max := public_key.property
        rw [h_pk_len] at h2
        have : K.val ≤ K.val * 384 := Nat.le_mul_of_pos_right _ (by omega)
        omega
      omega
    obtain ⟨chunk, drop, cnt', h_next_eq, h_cnt'_val, h_chunk_len, h_drop_len,
            h_chunk_eq, h_drop_eq⟩ :=
      enumerate_chunks_next_cont_drop rest 384#usize cnt h_cs_le h_cnt_max
    -- (3) deserialize via A2 axiom at index cnt (cnt.val = k).
    have h_chunk_pk : ∀ ℓ : Nat, ℓ < 384 →
        chunk.val[ℓ]! = public_key.val[cnt.val * 384 + ℓ]! := by
      intro ℓ hℓ
      have := h_chunk_eq ℓ (by have : (384#usize : Std.Usize).val = 384 := rfl; omega)
      rw [this, h_suf ℓ, h_cnt]
    obtain ⟨te1, h_te_eq, h_te_lift, h_te_bnd⟩ :=
      triple_exists_ok_fc
        (deserialize_to_reduced_ring_element_fc public_key K t_as_ntt_entry
          cnt h_pk_len hcnt_lt chunk h_chunk_len h_chunk_pk)
    have h_te_lift' : lift_poly te1 = trows.val[k]! := by
      rw [htrows_def, ← h_cnt]; exact h_te_lift
    have h_te_bnd' : ∀ a : Fin 16, ∀ b : Fin 16,
        ((te1.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328 :=
      fun a b => h_te_bnd a.val a.isLt b.val b.isLt
    -- (4) Slice.index_usize r_as_ntt cnt → r_as_ntt[k]!.
    set t_r : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      r_as_ntt.val[k]! with ht_r_def
    have h_idx_r : Aeneas.Std.Slice.index_usize r_as_ntt cnt = .ok t_r := by
      rw [ht_r_def, ← h_cnt]
      exact libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq r_as_ntt cnt
        (by show cnt.val < r_as_ntt.length; rw [h_r_len, h_cnt]; exact h_lt)
    -- (5) Slice.index_usize cache cnt → cache[k]!.
    set t_cache : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      cache.val[k]! with ht_cache_def
    have h_idx_cache : Aeneas.Std.Slice.index_usize cache cnt = .ok t_cache := by
      rw [ht_cache_def, ← h_cnt]
      exact libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq cache cnt
        (by show cnt.val < cache.length; rw [h_cache_len, h_cnt]; exact h_lt)
    -- (6) per-column use-cache forward dep at column k.
    have h_t_r_bnd : ∀ a : Fin 16, ∀ b : Fin 16,
        ((t_r.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328 :=
      fun a b => h_r_bnd k h_lt a b
    have h_cache_at_k : accumulating_ntt_multiply_poly_cache_post t_r t_cache := by
      rw [ht_r_def, ht_cache_def]; exact h_cache_char k h_lt
    have h_acc_cur_bnd : ∀ n : Fin 256, (acc.val[n.val]!).val.natAbs ≤ 2^30 := by
      intro n
      have hb := h_inv_acc_bnd n.val n.isLt
      have hp := h_acc_bnd n
      have hk_le : k * 2^25 ≤ K.val * 2^25 := Nat.mul_le_mul_right _ h_le
      omega
    obtain ⟨acc1, h_acc1_eq, h_acc1_bnd_rel, h_acc1_post⟩ :=
      triple_exists_ok_fc
        (accumulating_ntt_multiply_use_cache_poly_fc te1 t_r t_cache acc
          h_te_bnd' h_t_r_bnd h_acc_cur_bnd h_cache_at_k)
    -- (7) Body equation.
    have h_body :
        matrix.compute_ring_element_v_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) r_as_ntt cache
          { iter := { cs := 384#usize, elements := rest }, count := cnt } t_as_ntt_entry acc
        = .ok (ControlFlow.cont
            ({ iter := { cs := 384#usize, elements := drop }, count := cnt' }, te1, acc1)) := by
      unfold matrix.compute_ring_element_v_loop.body
      rw [show
        (CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
            (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice
              Std.U8)
            { iter := { cs := 384#usize, elements := rest }, count := cnt })
          = enumCENext { iter := { cs := 384#usize, elements := rest }, count := cnt }
        from rfl]
      rw [h_next_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      show ((do
              let t_as_ntt_entry1 ←
                libcrux_iot_ml_kem.serialize.deserialize_to_reduced_ring_element portable_ops_inst
                  chunk t_as_ntt_entry
              let pre ← Aeneas.Std.Slice.index_usize r_as_ntt cnt
              let pre1 ← Aeneas.Std.Slice.index_usize cache cnt
              let accumulator1 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_use_cache
                  portable_ops_inst t_as_ntt_entry1 pre acc pre1
              .ok (ControlFlow.cont
                (({ iter := { cs := 384#usize, elements := drop }, count := cnt' } : EnumCE),
                  t_as_ntt_entry1, accumulator1)))
            : Result (ControlFlow (EnumCE × (ChunkLoopFC.Poly × ChunkLoopFC.Acc))
                        (ChunkLoopFC.Poly × ChunkLoopFC.Acc))) = _
      rw [h_te_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_r]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_cache]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_acc1_eq]
      rfl
    apply triple_of_ok_chunks h_body
    -- (8) Discharge the step_post `.cont`.
    show k < K.val ∧ (384#usize : Std.Usize) = 384#usize ∧ cnt'.val = k + 1
      ∧ drop.length = (K.val - (k + 1)) * 384
      ∧ (∀ ℓ : Nat, drop.val[ℓ]! = public_key.val[(k + 1) * 384 + ℓ]!)
      ∧ (ChunkLoopFC.loop_inv trows r_arr acc_init (k + 1) (te1, acc1)).holds
    refine ⟨h_lt, rfl, by rw [h_cnt'_val, h_cnt], ?_, ?_, ?_⟩
    · -- drop length.
      have h384 : (384#usize : Std.Usize).val = 384 := rfl
      rw [h_drop_len, h_rest_len, h384]
      have hexp : (K.val - (k + 1)) * 384 = (K.val - k) * 384 - 384 := by
        rw [Nat.sub_mul]; ring_nf; omega
      rw [hexp, Nat.sub_mul]
    · -- drop suffix relation at offset (k+1)*384.
      intro ℓ
      rw [h_drop_eq ℓ, h_suf]
      have h384 : (384#usize : Std.Usize).val = 384 := rfl
      rw [h384]
      have hidx : k * 384 + (384 + ℓ) = (k + 1) * 384 + ℓ := by ring
      rw [hidx]
    · -- re-establish loop_inv at k+1.
      set mp1 : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K :=
        mp.set cnt te1 with hmp1_def
      have h_mp_len : mp.length = K.val := Std.Array.length_eq mp
      have h_mp1_at : mp1.val[k]! = te1 := by
        rw [hmp1_def, ← h_cnt]
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
          Aeneas.Std.Array.getElem!_Nat_set_eq mp cnt cnt.val te1
            ⟨rfl, by rw [h_mp_len]; rw [h_cnt]; exact h_lt⟩
      have h_mp1_ne : ∀ j : Nat, j ≠ k → mp1.val[j]! = mp.val[j]! := by
        intro j hj
        rw [hmp1_def]
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
          Aeneas.Std.Array.getElem!_Nat_set_ne mp cnt j te1 (fun h => hj (by rw [← h_cnt]; exact h.symm))
      have h_r_arr_k : r_arr.val[k]! = t_r := by
        rw [ht_r_def]; exact h_r_arr k h_lt
      have h_inv_pure :
          (∃ mp' : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K,
             (∀ c : Nat, c < k + 1 →
                lift_poly (mp'.val[c]!) = trows.val[c]!
                ∧ (∀ a : Fin 16, ∀ b : Fin 16,
                     ((mp'.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328))
             ∧ (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
                 Spec.mont_reduce_pure (lift_fe_int (acc1.val[16 * j + ℓ]!).val)
                   = (List.range (k + 1)).foldl
                       (fun s c =>
                         libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                           ((Spec.ntt_multiply_pure_no_acc
                               (lift_chunk_mont (mp'.val[c]!.coefficients.val[j]!))
                               (lift_chunk_mont (r_arr.val[c]!.coefficients.val[j]!))
                               (Spec.zeta_at (64 + 4 * j))
                               (Spec.zeta_at (64 + 4 * j + 1))
                               (Spec.zeta_at (64 + 4 * j + 2))
                               (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                       (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))))
          ∧ (∀ n : Nat, n < 256 →
              (acc1.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + (k + 1) * 2^25) := by
        refine ⟨⟨mp1, ?_, ?_⟩, ?_⟩
        · intro c hc
          rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc_lt | hc_eq
          · have hc_ne : c ≠ k := by omega
            rw [h_mp1_ne c hc_ne]; exact h_mp_agree c hc_lt
          · subst hc_eq
            rw [h_mp1_at]
            exact ⟨h_te_lift', h_te_bnd'⟩
        · intro j hj ℓ hℓ
          have h_step_acc :
              Spec.mont_reduce_pure (lift_fe_int (acc1.val[16 * j + ℓ]!).val)
                = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                    (Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val))
                    ((Spec.ntt_multiply_pure_no_acc
                        (lift_chunk_mont (te1.coefficients.val[j]!))
                        (lift_chunk_mont (t_r.coefficients.val[j]!))
                        (Spec.zeta_at (64 + 4 * j))
                        (Spec.zeta_at (64 + 4 * j + 1))
                        (Spec.zeta_at (64 + 4 * j + 2))
                        (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!) := by
            have := h_acc1_post
            unfold accumulating_ntt_multiply_poly_post at this
            exact this j hj ℓ hℓ
          have h_ih := h_inv_acc j hj ℓ hℓ
          rw [h_step_acc, h_ih]
          rw [List.range_succ, List.foldl_append]
          have h_foldl_congr : ∀ (L : List Nat) (init : hacspec_ml_kem.parameters.FieldElement),
              (∀ c ∈ L, c < k) →
              L.foldl
                  (fun s c =>
                    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                      ((Spec.ntt_multiply_pure_no_acc
                          (lift_chunk_mont (mp1.val[c]!.coefficients.val[j]!))
                          (lift_chunk_mont (r_arr.val[c]!.coefficients.val[j]!))
                          (Spec.zeta_at (64 + 4 * j))
                          (Spec.zeta_at (64 + 4 * j + 1))
                          (Spec.zeta_at (64 + 4 * j + 2))
                          (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                  init
                = L.foldl
                  (fun s c =>
                    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                      ((Spec.ntt_multiply_pure_no_acc
                          (lift_chunk_mont (mp.val[c]!.coefficients.val[j]!))
                          (lift_chunk_mont (r_arr.val[c]!.coefficients.val[j]!))
                          (Spec.zeta_at (64 + 4 * j))
                          (Spec.zeta_at (64 + 4 * j + 1))
                          (Spec.zeta_at (64 + 4 * j + 2))
                          (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                  init := by
            intro L
            induction L with
            | nil => intro init _; rfl
            | cons hd tl ih =>
              intro init hmem
              have hhd : hd < k := hmem hd (List.mem_cons_self)
              have htl : ∀ c ∈ tl, c < k := fun c hc => hmem c (List.mem_cons_of_mem hd hc)
              have hhd_ne : hd ≠ k := by omega
              simp only [List.foldl_cons]
              rw [h_mp1_ne hd hhd_ne]
              exact ih _ htl
          rw [h_foldl_congr (List.range k)
                (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))
                (fun c hc => by simpa using hc)]
          show libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                ((List.range k).foldl _ _) _
              = (List.foldl _ ((List.range k).foldl _ _) [k])
          rw [List.foldl_cons, List.foldl_nil]
          rw [h_mp1_at, h_r_arr_k]
        · intro n hn
          have h_acc1_bnd_n := h_acc1_bnd_rel ⟨n, hn⟩
          have h_acc1_bnd_n' : (acc1.val[n]!).val.natAbs ≤ (acc.val[n]!).val.natAbs + 2^25 :=
            h_acc1_bnd_n
          have h_inv_n := h_inv_acc_bnd n hn
          have h_arith : (k + 1) * 2^25 = k * 2^25 + 2^25 := by ring
          rw [h_arith]
          linarith [h_acc1_bnd_n', h_inv_n]
      show (pure _ : Result Prop).holds
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: rest.length < 384, k = K, done.
    have hk_ge : ¬ k < K.val := h_lt
    have hk_eq : k = K.val := by omega
    have h_rest_lt : rest.length < (384#usize : Std.Usize).val := by
      rw [h_rest_len, hk_eq]
      have h384 : (384#usize : Std.Usize).val = 384 := rfl
      simp [h384]
    have h_next_eq := enumerate_chunks_next_done rest 384#usize cnt h_rest_lt
    have h_body :
        matrix.compute_ring_element_v_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) r_as_ntt cache
          { iter := { cs := 384#usize, elements := rest }, count := cnt } t_as_ntt_entry acc
        = .ok (ControlFlow.done (t_as_ntt_entry, acc)) := by
      unfold matrix.compute_ring_element_v_loop.body
      rw [show
        (CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
            (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice
              Std.U8)
            { iter := { cs := 384#usize, elements := rest }, count := cnt })
          = enumCENext { iter := { cs := 384#usize, elements := rest }, count := cnt }
        from rfl]
      rw [h_next_eq]
      rfl
    apply triple_of_ok_chunks h_body
    show (ChunkLoopFC.loop_inv trows r_arr acc_init K.val (t_as_ntt_entry, acc)).holds
    have h_inv_pure :
        (∃ mp' : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K,
           (∀ c : Nat, c < K.val →
              lift_poly (mp'.val[c]!) = trows.val[c]!
              ∧ (∀ a : Fin 16, ∀ b : Fin 16,
                   ((mp'.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328))
           ∧ (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
               Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val)
                 = (List.range K.val).foldl
                     (fun s c =>
                       libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                         ((Spec.ntt_multiply_pure_no_acc
                             (lift_chunk_mont (mp'.val[c]!.coefficients.val[j]!))
                             (lift_chunk_mont (r_arr.val[c]!.coefficients.val[j]!))
                             (Spec.zeta_at (64 + 4 * j))
                             (Spec.zeta_at (64 + 4 * j + 1))
                             (Spec.zeta_at (64 + 4 * j + 2))
                             (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                     (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))))
        ∧ (∀ n : Nat, n < 256 →
            (acc.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + K.val * 2^25) := by
      refine ⟨⟨mp, ?_, ?_⟩, ?_⟩
      · intro c hc; exact h_mp_agree c (by rw [hk_eq]; exact hc)
      · intro j hj ℓ hℓ
        have h_eq := h_inv_acc j hj ℓ hℓ
        rw [show (List.range k) = (List.range K.val) by rw [hk_eq]] at h_eq
        exact h_eq
      · intro n hn
        have h_b := h_inv_acc_bnd n hn
        rw [show k * 2^25 = K.val * 2^25 by rw [hk_eq]] at h_b
        exact h_b
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 4000000 in
/-- **L7.3 loop FC.** `matrix.compute_ring_element_v_loop`: the chunks-exact
    USE-CACHE column loop. Iterates over `Enumerate (ChunksExact U8)` of the
    public key; each chunk `i` deserializes `t̂[i]` (A2 axiom), reads
    `r_as_ntt[i]` and `cache[i]` (read-only), and runs
    `accumulating_ntt_multiply_use_cache` to add `t̂[i]·r[i]` to the I32
    accumulator.

    POST: the RESOLVED all-mont/existential `loop_inv` holds at k = K — there
    exists a `K`-array `mp` of deserialized polys with `lift_poly mp[c] =
    (lift_t_as_ntt_from_public_key public_key K).val[c]` (axiom-pinned) such
    that for all (j,ℓ) ∈ [0,16)², `mont_reduce_pure (lift_fe_int acc[16j+ℓ])`
    equals the K-column all-mont sum, plus the bound.

    Applies `loop_chunks_exact_pk_spec` (numChunks = K, cs = 384) with the
    step lemma as `h_step`. -/
theorem compute_ring_element_v_loop_fc (K : Std.Usize) (hK : K.val ≤ 4)
    (public_key : Slice Std.U8) (h_pk_len : public_key.length = K.val * 384)
    (t_as_ntt_entry : ChunkLoopFC.Poly)
    (r_as_ntt cache : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (r_arr : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (h_r_len : r_as_ntt.length = K.val) (h_cache_len : cache.length = K.val)
    (h_r_arr : ∀ c : Nat, c < K.val → r_arr.val[c]! = r_as_ntt.val[c]!)
    (h_r_bnd : ∀ c : Nat, c < K.val → ∀ a : Fin 16, ∀ b : Fin 16,
       ((r_as_ntt.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_cache_char : ∀ c : Nat, c < K.val →
       accumulating_ntt_multiply_poly_cache_post (r_as_ntt.val[c]!) (cache.val[c]!))
    (accumulator : Std.Array Std.I32 256#usize)
    (h_acc_zero : ∀ n : Nat, n < 256 → (accumulator.val[n]!).val = 0)
    (iter0 : EnumCE)
    (h_iter0 : iter0 = { iter := { cs := 384#usize, elements := public_key }, count := 0#usize }) :
    ⦃ ⌜ True ⌝ ⦄
    matrix.compute_ring_element_v_loop
      (vectortraitsOperationsInst := portable_ops_inst) iter0
      t_as_ntt_entry r_as_ntt cache accumulator
    ⦃ ⇓ p => ⌜ (ChunkLoopFC.loop_inv (lift_t_as_ntt_from_public_key public_key K) r_arr accumulator
                  K.val p).holds ⌝ ⦄ := by
  set trows : Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K :=
    lift_t_as_ntt_from_public_key public_key K with htrows_def
  -- accumulator budget: zero init + K·2^25 ≤ 2^30 (K ≤ 4).
  have h_acc_bnd : ∀ n : Fin 256,
      (accumulator.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30 := by
    intro n
    have hz := h_acc_zero n.val n.isLt
    have : (accumulator.val[n.val]!).val.natAbs = 0 := by rw [hz]; rfl
    rw [this]
    have hk4 : K.val * 2^25 ≤ 4 * 2^25 := Nat.mul_le_mul_right _ hK
    omega
  subst h_iter0
  unfold matrix.compute_ring_element_v_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_chunks_exact_pk_spec
      (fun (iter1, p) =>
        matrix.compute_ring_element_v_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) r_as_ntt cache iter1 p.1 p.2)
      (β := ChunkLoopFC.Poly × ChunkLoopFC.Acc)
      (t_as_ntt_entry, accumulator)
      public_key 384#usize K.val
      (fun k p => ChunkLoopFC.loop_inv trows r_arr accumulator k p)
      (by decide : 0 < (384#usize : Std.Usize).val)
      (by rw [h_pk_len]; rfl)
      (by
        -- Base case at k = 0.
        show (ChunkLoopFC.loop_inv trows r_arr accumulator 0 (t_as_ntt_entry, accumulator)).holds
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨⟨Std.Array.repeat K t_as_ntt_entry, ?_, ?_⟩, ?_⟩
        · intro c hc; exact absurd hc (Nat.not_lt_zero c)
        · intro j hj ℓ hℓ
          show Spec.mont_reduce_pure _ = (List.range 0).foldl _ _
          simp [List.range_zero, List.foldl_nil]
        · intro n _; omega)
      ?_)
  · -- Post entailment at K.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_holds : (ChunkLoopFC.loop_inv trows r_arr accumulator K.val r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    show (ChunkLoopFC.loop_inv trows r_arr accumulator K.val r).holds
    exact h_holds
  · -- Step entailment: apply the step lemma.
    intro p k rest cnt hk_le hcnt hrest_len hsuf hinv
    have h_step := compute_ring_element_v_loop_step_lemma_fc
      public_key h_pk_len r_as_ntt cache r_arr accumulator
      h_r_len h_cache_len h_r_arr h_r_bnd h_acc_bnd h_cache_char
      p.1 p.2 k hk_le rest cnt hcnt hrest_len hsuf hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    have h384 : (384#usize : Std.Usize).val = 384 := rfl
    rcases r with ⟨iter', acc'⟩ | y
    · have hh' : k < K.val ∧ iter'.iter.cs = 384#usize ∧ iter'.count.val = k + 1
              ∧ iter'.iter.elements.length = (K.val - (k + 1)) * 384
              ∧ (∀ ℓ : Nat, iter'.iter.elements.val[ℓ]!
                    = public_key.val[(k + 1) * 384 + ℓ]!)
              ∧ (ChunkLoopFC.loop_inv trows r_arr accumulator (k + 1) acc').holds := by
        have := hh
        simp only [Std.Do.SPred.down_pure] at this
        exact this
      obtain ⟨h_klt, h_cs, h_cnt', h_len', h_suf', h_inv'⟩ := hh'
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
      refine ⟨h_klt, h_cs, h_cnt', ?_, ?_, h_inv'⟩
      · rw [h384]; exact h_len'
      · intro ℓ; rw [h384]; exact h_suf' ℓ
    · have h_done : (ChunkLoopFC.loop_inv trows r_arr accumulator K.val y).holds := by
        have := hh
        simp only [Std.Do.SPred.down_pure] at this
        exact this
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
      exact h_done

end L7_3_irreducible

/-! ## §L7.3 — acc-bridge (REUSES L7.4 `compute_message_acc_bridge`). -/

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do
open libcrux_iot_ml_kem.InvertNtt libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeAsPlusE libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.NttMultiply libcrux_iot_ml_kem.Polynomial.PolyOpsFc libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Sampling libcrux_iot_ml_kem.Serialize libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt

/-- Local single-256-lane field-element poly abbrev (keeps `256#usize` out of
    statement signatures — SKILL §7.7). -/
private abbrev FEPoly := Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize

/-- Local re-derivation of ComputeVectorU's private `lift_vec_mp_eq`: the
    `lift_vec` of the existential witness `mp` collapses to the canonical rows
    `trows`, given per-column agreement. -/
private theorem lift_vec_mp_eq {K : Std.Usize}
    (mp : Std.Array
            (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (trows : Std.Array FEPoly K)
    (h_agree : ∀ c : Nat, c < K.val → lift_poly (mp.val[c]!) = trows.val[c]!) :
    lift_vec mp = trows := by
  apply Subtype.ext
  show mp.val.map lift_poly = trows.val
  have h_mp_len : mp.val.length = K.val := Std.Array.length_eq mp
  have h_tr_len : trows.val.length = K.val := Std.Array.length_eq trows
  apply List.ext_getElem
  · rw [List.length_map, h_mp_len, h_tr_len]
  · intro i hi1 _hi2
    have hi : i < K.val := by
      have : i < (mp.val.map lift_poly).length := hi1
      rw [List.length_map, h_mp_len] at this; exact this
    rw [List.getElem_map]
    have h_lhs : lift_poly (mp.val[i]) = lift_poly (mp.val[i]!) := by
      rw [getElem!_pos mp.val i (by rw [h_mp_len]; exact hi)]
    have h_rhs : trows.val[i] = trows.val[i]! := by
      rw [getElem!_pos trows.val i (by rw [h_tr_len]; exact hi)]
    rw [h_lhs, h_rhs]; exact h_agree i hi

/-- Local re-derivation of ComputeVectorU's private `lift_vec_r_arr_eq`. -/
private theorem lift_vec_r_arr_eq {K : Std.Usize}
    (r_as_ntt : Slice
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (r_arr : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (h_r_arr : ∀ c : Nat, c < K.val → r_arr.val[c]! = r_as_ntt.val[c]!) :
    lift_vec r_arr = lift_vec_slice r_as_ntt K := by
  apply Subtype.ext
  show r_arr.val.map lift_poly = (List.range K.val).map (fun i => lift_poly r_as_ntt.val[i]!)
  have h_r_len : r_arr.val.length = K.val := Std.Array.length_eq r_arr
  apply List.ext_getElem
  · rw [List.length_map, h_r_len, List.length_map, List.length_range]
  · intro i hi1 _hi2
    have hi : i < K.val := by
      have : i < (r_arr.val.map lift_poly).length := hi1
      rw [List.length_map, h_r_len] at this; exact this
    rw [List.getElem_map, List.getElem_map, List.getElem_range]
    have h_lhs : lift_poly (r_arr.val[i]) = lift_poly (r_arr.val[i]!) := by
      rw [getElem!_pos r_arr.val i (by rw [h_r_len]; exact hi)]
    rw [h_lhs, h_r_arr i hi]

set_option maxHeartbeats 1000000 in
/-- **L7.3 acc-bridge.** Reconciles the hacspec `multiply_vectors` of the
    axiom-pinned deserialized t-as-ntt rows against the loop accumulator scaled
    by `R = 2285`. A thin wrapper REUSING L7.4 `compute_message_acc_bridge`: the
    existential witness `mp` of `loop_inv` supplies the t-as-ntt array, `r_arr`
    the r-as-ntt array, and `loop_inv`'s two conjuncts are exactly
    `S1LoopFC.loop_inv mp r_arr`'s two conjuncts. The two vector args are
    rewritten via `lift_vec_mp_eq` / `lift_vec_r_arr_eq`. Mirrors
    `compute_vector_u_rowi_acc_bridge`. -/
theorem compute_ring_element_v_acc_bridge {K : Std.Usize} (hK : K.val ≤ 4)
    (public_key : Slice Std.U8)
    (r_as_ntt : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (r_arr : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init acc2 : Std.Array Std.I32 256#usize)
    (h_acc_init_zero : ∀ n : Nat, n < 256 → (acc_init.val[n]!).val = 0)
    (h_r_arr : ∀ c : Nat, c < K.val → r_arr.val[c]! = r_as_ntt.val[c]!)
    (h_r_bnd : ∀ c : Nat, c < K.val → ∀ a : Fin 16, ∀ b : Fin 16,
        ((r_as_ntt.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (t_ent : ChunkLoopFC.Poly)
    (h_char : (ChunkLoopFC.loop_inv (lift_t_as_ntt_from_public_key public_key K) r_arr acc_init
                K.val (t_ent, acc2)).holds) :
    hacspec_ml_kem.matrix.multiply_vectors
        (lift_t_as_ntt_from_public_key public_key K) (lift_vec_slice r_as_ntt K)
      = .ok (scaleZ 2285 (Impl.mont_strip_pure
               (Spec.poly_reducing_from_i32_array_pure (Aeneas.Std.Array.to_slice acc2)))) := by
  set trows : Std.Array FEPoly K := lift_t_as_ntt_from_public_key public_key K with htrows_def
  -- Destructure `loop_inv`'s 2 conjuncts; the first is the ∃-witness pack.
  obtain ⟨⟨mp, h_mp_agree, h_inv_acc⟩, h_inv_bnd⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_char
  dsimp only at h_inv_acc h_inv_bnd
  -- `h_inv_acc` (mont foldl) and `h_inv_bnd` (bound) are exactly
  -- `S1LoopFC.loop_inv mp r_arr acc_init K acc2`'s two conjuncts.
  have h_char4 : (S1LoopFC.loop_inv mp r_arr acc_init K acc2).holds := by
    show (pure
        ((∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
            Spec.mont_reduce_pure (lift_fe_int (acc2.val[16 * j + ℓ]!).val)
              = (List.range K.val).foldl
                  (fun s c =>
                    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                      ((Spec.ntt_multiply_pure_no_acc
                          (lift_chunk_mont (mp.val[c]!.coefficients.val[j]!))
                          (lift_chunk_mont (r_arr.val[c]!.coefficients.val[j]!))
                          (Spec.zeta_at (64 + 4 * j))
                          (Spec.zeta_at (64 + 4 * j + 1))
                          (Spec.zeta_at (64 + 4 * j + 2))
                          (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                  (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val)))
          ∧ (∀ n : Nat, n < 256 →
              (acc2.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + K.val * 2^25))
        : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using
      (⟨h_inv_acc, h_inv_bnd⟩ : _ ∧ _)
  -- t-side bounds from the ∃-witness `mp`'s per-lane bound (conjunct 1.2).
  have h_secret_bnd : ∀ k : Fin K.val, ∀ i j : Fin 16,
      ((mp.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328 := by
    intro k i j; exact (h_mp_agree k.val k.isLt).2 i j
  -- r-side bounds from `h_r_bnd` rewritten through `h_r_arr`.
  have h_u_bnd : ∀ k : Fin K.val, ∀ i j : Fin 16,
      ((r_arr.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328 := by
    intro k i j; rw [h_r_arr k.val k.isLt]; exact h_r_bnd k.val k.isLt i j
  -- Apply the L7.4 bridge on `(mp, r_arr)`.
  have h_bridge :=
    compute_message_acc_bridge mp r_arr acc_init acc2 h_acc_init_zero h_secret_bnd h_u_bnd h_char4
  have h_mp_vec : lift_vec mp = trows :=
    lift_vec_mp_eq mp trows (fun c hc => (h_mp_agree c hc).1)
  have h_r_vec : lift_vec r_arr = lift_vec_slice r_as_ntt K :=
    lift_vec_r_arr_eq r_as_ntt r_arr h_r_arr
  rw [h_mp_vec, h_r_vec] at h_bridge
  rw [htrows_def]
  exact h_bridge

end libcrux_iot_ml_kem.Matrix.ComputeRingElementV.Impl