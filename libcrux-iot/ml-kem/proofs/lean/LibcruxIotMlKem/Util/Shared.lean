/-
  # `Util/Shared.lean` — generic plumbing lemmas shared across obligation files.

  ## Why this file exists
  These were `private` in `SerializeFc.lean`. Lean `private` is FILE-scoped, so the next
  obligation in a new file cannot cite them and copies them instead: `IndCpaFc.lean`'s first
  obligation re-stated 18 of them verbatim, ~330 of its 616 added lines, and
  `triple_exists_ok_fc`/`holds_ok` had reached their FOURTH copy in this tree
  (Matrix/ComputeVectorU/FC.lean, Matrix/ComputeVectorU/Impl.lean, SerializeFc.lean,
  IndCpaFc.lean). A copied lemma is also invisible to the exemplar dependency walk, so reuse
  that really happened cannot be measured.

  ## Two rules for anything added here
  1. **NO `@[simp]` / `@[spec]` / simp-set attributes.** Attributes are global to every
     module that transitively imports this one, so an attributed lemma here silently widens
     what `mvcgen`/`simp` see in every downstream file and can change proof search in files
     that currently build green. All twelve below were CHECKED to carry no attributes before
     being moved (as does every private lemma in SerializeFc.lean — measured, not assumed).
  2. **Generic only.** `RustM` / `Usize` / `Slice` plumbing. Anything mentioning a
     ring element, a modulus, 384, or a compression factor stays in its obligation file.
-/
import Hax                                              -- RustM.holds (Hax/MissingAeneas.lean)
import LibcruxIotMlKem.Extraction.Funs
import LibcruxIotMlKem.Vector.Portable.Arithmetic.LoopHelper  -- slice_index_usize_ok_eq
import LibcruxIotMlKem.Util.LoopSpecs                        -- IteratorRange_next_spec_usize

open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Util.LoopSpecs   -- IteratorRange_next_spec_usize, used by the iter_*_gen pair

namespace libcrux_iot_ml_kem.Util.Shared

theorem triple_exists_ok_fc {α : Type} {x : RustM α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) : ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl, (by subst hx; simpa [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PostCond.noThrow, Std.Do.PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PostCond.noThrow, Std.Do.PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PostCond.noThrow, Std.Do.PredTrans.apply])

theorem holds_ok (P : Prop) : (Aeneas.Std.RustM.ok P).holds ↔ P := by
  constructor
  · intro h
    simpa [Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp, Std.Do.PostCond.noThrow,
      Std.Do.PredTrans.apply] using h
  · intro h
    simp [Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp, Std.Do.PostCond.noThrow,
      Std.Do.PredTrans.apply, h]

theorem usize_mul_lit (x y z : Std.Usize) (h : x.val * y.val = z.val)
    (hb : x.val * y.val ≤ Std.Usize.max) :
    (x * y : Aeneas.Std.RustM Std.Usize) = .ok z := by
  obtain ⟨m, hm_eq, hm_v⟩ := Std.WP.spec_imp_exists
    (Std.WP.spec_of_partialSpec (@Std.Usize.mul_spec x y)
      (fun e => by cases e <;> scalar_tac) (by simp))
  have hm : m = z := by
    apply Aeneas.Std.UScalar.eq_of_val_eq
    rw [hm_v, h]
  rw [hm_eq, hm]

theorem usize_mul_ok_e (x y : Std.Usize) (hb : x.val * y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x * y : RustM Std.Usize) = .ok z ∧ z.val = x.val * y.val := by
  obtain ⟨z, hz, hv, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.mul_bv_spec (x := x) (y := y) (by scalar_tac))
  exact ⟨z, hz, hv⟩

theorem usize_add_ok_e (x y : Std.Usize) (hb : x.val + y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x + y : RustM Std.Usize) = .ok z ∧ z.val = x.val + y.val := by
  obtain ⟨z, hz, hv, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.add_bv_spec (x := x) (y := y) (by scalar_tac))
  exact ⟨z, hz, hv⟩

/-- `⟨BitVec.ofNat _ k⟩.val = k` for any in-range `k`. The `L57Bank2` companion
    `usize_ofNat_val` is pinned at the platform-independent `2 ^ 32`; here `k`
    ranges over `< K` with only `K * 384 ≤ Usize.max` known, so the bound has to
    be the machine one. -/
theorem usize_ofNat_val_le (k : Nat) (h : k ≤ Std.Usize.max) :
    ((⟨BitVec.ofNat _ k⟩ : Std.Usize)).val = k := by
  show (BitVec.ofNat _ k).toNat = k
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by scalar_tac)

/-- Literal `Usize` division, in the shape the two `BYTES_PER_RING_ELEMENT`
    constants (impl and hacspec) need. The L5.6 bank has this inline; hoisted
    here because both sides of this obligation want it. -/
theorem usize_div_lit (x y z : Std.Usize) (hy : y.val ≠ 0)
    (hz : x.val / y.val = z.val) : (x / y : RustM Std.Usize) = .ok z := by
  obtain ⟨q, hq_eq, hq_val⟩ := Std.UScalar.div_spec x (y := y) hy
  rw [hq_eq]
  congr 1
  exact Std.UScalar.eq_of_val_eq (by rw [hq_val, hz])

/-- Generic `core.slice.Slice.len` bridge (the file's `slice_len_384` is pinned at 384). -/
theorem slice_len_gen {T : Type} (sl : Slice T) :
    CoreModels.core.slice.Slice.len sl = .ok (Aeneas.Std.Slice.len sl) := rfl

/-- The shared-range index `s[a..b]` on a slice, in the shape the `vector_decode_12`
    closure uses (goes through `SliceIndex.get`, not `.index`). -/
theorem slice_range_index_ok {T : Type} [Inhabited T]
    (s : Slice T) (a b : Std.Usize) (h0 : a.val < b.val) (h1 : b.val ≤ s.val.length) :
    CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
        (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) s
        { start := a, «end» := b }
      = .ok ⟨List.slice a.val b.val s.val, by
          have := s.val.slice_length_le a.val b.val; scalar_tac⟩ := by
  have hle : (a ≤ b) := by scalar_tac
  have hb : (b ≤ Aeneas.Std.Slice.len s) := by
    have : (Aeneas.Std.Slice.len s).val = s.val.length := Aeneas.Std.Slice.len_val s
    scalar_tac
  unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
  simp only [CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
    CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get]
  rw [if_pos hle]
  unfold CoreModels.rust_primitives.slice.slice_length
  simp only [Aeneas.Std.bind_tc_ok]
  rw [if_pos hb]
  unfold CoreModels.rust_primitives.slice.slice_slice
  rw [show (Aeneas.Std.Slice.subslice s ⟨a, b⟩)
      = .ok ⟨List.slice a.val b.val s.val, by
          have := s.val.slice_length_le a.val b.val; scalar_tac⟩ from by
    unfold Aeneas.Std.Slice.subslice
    split
    · rfl
    · rename_i hcon
      exact absurd ⟨h0, h1⟩ hcon]
  rfl

/-- `Slice.index_mut_usize` in closed form (the `Slice` analogue of the file's
    `array_index_mut16`). -/
theorem slice_index_mut_ok {α : Type} [Inhabited α] (v : Slice α) (i : Std.Usize)
    (h : i.val < v.val.length) :
    Aeneas.Std.Slice.index_mut_usize v i = .ok (v.val[i.val]!, Aeneas.Std.Slice.set v i) := by
  simp only [Aeneas.Std.Slice.index_mut_usize,
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq v i h,
    Aeneas.Std.bind_tc_ok]

theorem slice_set_length {α : Type} (v : Slice α) (i : Std.Usize) (x : α) :
    (Aeneas.Std.Slice.set v i x).length = v.length := by
  show ((v.val.set i.val x).length) = v.val.length
  rw [List.length_set]

theorem slice_set_get {α : Type} [Inhabited α] (v : Slice α) (i : Std.Usize) (x : α)
    (j : Nat) (hj : j < v.val.length) :
    (Aeneas.Std.Slice.set v i x).val[j]! = if j = i.val then x else v.val[j]! := by
  by_cases h : j = i.val
  · rw [if_pos h]
    have hs := Aeneas.Std.Slice.getElem!_Nat_set_eq v i j x ⟨h.symm, hj⟩
    simpa [Aeneas.Std.Slice.getElem!_Nat_eq] using hs
  · rw [if_neg h]
    have hs := Aeneas.Std.Slice.getElem!_Nat_set_ne v i j x (fun hc => h hc.symm)
    simpa [Aeneas.Std.Slice.getElem!_Nat_eq] using hs

theorem triple_of_ok_fc {α : Type} {x : RustM α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    (⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) := by
  subst hx; simp [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PostCond.noThrow,
    Std.Do.PredTrans.apply, hp]

theorem slice_index_mut_range_strict {T : Type} [Inhabited T]
    (s : Slice T) (a b : Std.Usize) (h0 : a.val < b.val) (h1 : b.val ≤ s.val.length) :
    ∃ (ns : Slice T) (wb : Slice T → Slice T),
      CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
        (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) s
        ⟨a, b⟩ = .ok (ns, wb)
      ∧ ns.val.length = b.val - a.val
      ∧ (∀ s' : Slice T, s'.val.length = b.val - a.val →
            (wb s').val = s.val.setSlice! a.val s'.val) := by
  obtain ⟨ns, hns_eq, hns_val, hns_get⟩ :=
    Std.WP.spec_imp_exists (Aeneas.Std.Slice.subslice_spec s ⟨a, b⟩ h0 h1)
  have hlen : ns.val.length = b.val - a.val := by
    rw [hns_val]
    show (List.slice a.val b.val s.val).length = b.val - a.val
    rw [List.slice_length]; omega
  have hTR : HaxToRange.toRange ({ start := a, «end» := b }
        : CoreModels.core.ops.range.Range Std.Usize) (Aeneas.Std.Slice.len s)
      = ({ start := a, «end» := b } : Aeneas.Std.core.ops.range.Range Std.Usize) := rfl
  refine ⟨ns, (fun sub' =>
      match Aeneas.Std.Slice.update_subslice s
          (HaxToRange.toRange
            ({ start := a, «end» := b } : CoreModels.core.ops.range.Range Std.Usize)
            (Aeneas.Std.Slice.len s)) sub' with
      | .ok s'' => s''
      | _ => s), ?_, hlen, ?_⟩
  · unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
    simp only [CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
      CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
      CoreModels.rust_primitives.slice.slice_slice, hns_eq, Aeneas.Std.bind_tc_ok]
    rfl
  · intro s' hs'
    have hupd : Aeneas.Std.Slice.update_subslice s
        (HaxToRange.toRange ({ start := a, «end» := b }
            : CoreModels.core.ops.range.Range Std.Usize) (Aeneas.Std.Slice.len s)) s'
        = .ok ⟨s.val.setSlice! a.val s'.val, by scalar_tac⟩ := by
      rw [hTR]
      unfold Aeneas.Std.Slice.update_subslice
      rw [dif_pos ⟨h0, by simpa [Aeneas.Std.Slice.length] using h1, by
        simpa [Aeneas.Std.Slice.length] using hs'⟩]
    simp only [hupd]

/-- Generic-bound analogue of `LoopHelper.iter_next_some_eq`. -/
theorem iter_some_gen (i e : Std.Usize) (h_lt : i.val < e.val) :
    ∃ s : Std.Usize, s.val = i.val + 1 ∧
      CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
          CoreModels.core.Usize.Insts.CoreIterRangeStep
          ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)
        = .ok (some i,
            ({ start := s, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)) := by
  have hT := IteratorRange_next_spec_usize i e
    (Q := Std.Do.PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
      ∃ s : Std.Usize, s.val = i.val + 1
        ∧ oi = (some i,
            ({ start := s, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)) ⌝)
    (fun _ s hs => by
      dsimp only [Std.Do.PostCond.noThrow, Std.Do.SPred.down_pure]
      exact ⟨s, hs, rfl⟩)
    (fun hge => absurd h_lt (Nat.not_lt.mpr hge))
  obtain ⟨v, hveq, s, hs, hpair⟩ := triple_exists_ok_fc hT
  refine ⟨s, hs, ?_⟩
  show CoreModels.core.iter.range.IteratorRange.next
      CoreModels.core.Usize.Insts.CoreIterRangeStep
      ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize) = _
  rw [hveq, hpair]

/-- Generic-bound analogue of `LoopHelper.iter_next_none_eq`. -/
theorem iter_none_gen (i e : Std.Usize) (h_ge : e.val ≤ i.val) :
    CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
        CoreModels.core.Usize.Insts.CoreIterRangeStep
        ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)
      = .ok ((none : Option Std.Usize),
          ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)) := by
  have hT := IteratorRange_next_spec_usize i e
    (Q := Std.Do.PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
      oi = ((none : Option Std.Usize),
        ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)) ⌝)
    (fun hlt => absurd hlt (Nat.not_lt.mpr h_ge))
    (fun _ => by dsimp only [Std.Do.PostCond.noThrow, Std.Do.SPred.down_pure])
  obtain ⟨v, hveq, hP⟩ := triple_exists_ok_fc hT
  show CoreModels.core.iter.range.IteratorRange.next
      CoreModels.core.Usize.Insts.CoreIterRangeStep
      ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize) = _
  rw [hveq, hP]

end libcrux_iot_ml_kem.Util.Shared
