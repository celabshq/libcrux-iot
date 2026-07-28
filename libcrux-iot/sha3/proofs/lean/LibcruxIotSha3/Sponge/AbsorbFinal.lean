/-
  # `keccak.absorb_final` ↔ `sponge.absorb_final`

  Main Triple `keccak.absorb_final_spec` with the full equality-form post:

  * termination of `keccak.absorb_final`;
  * `r.i.val = 0` on the result (consumed by the top-level `keccak` proof's
    squeeze-first-block precondition);
  * the spec equation
    `sponge.absorb_final (lift s) last start len RATE DELIM = .ok (lift r)`.

  Both impl and spec follow the same 4-step buffer recipe (zero-init,
  copy `last[start..start+len]` into buf[0..len], `buf[len] := DELIM`,
  OR `0x80` into `buf[RATE-1]`), then load and permute. The impl uses
  `if len > 0` to skip the `copy_from_slice` of an empty slice; the
  spec always takes the index_mut path, which is identity when
  `len = 0` (empty slice + `setSlice! 0 []` = no-op). Both yield the
  *same* `buf3`.

  Impl and spec sides are walked as independent `.ok`-equation chains and
  composed at the end:

  1. `h_impl_eq : keccak.absorb_final ... = .ok r`
  2. `h_pad_eq  : sponge.pad_last_block ... = .ok buf3`
  3. `h_block_idx_eq` — the spec's `block[0..rate]` indexing.
  4. Compose via `h_r_spec` from `keccak.absorb_block_spec`.
-/
import LibcruxIotSha3.Sponge.AbsorbBlock

open Aeneas Aeneas.Std Result Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

open libcrux_iot_sha3.Foundation

-- Defensive seal re-issue: no proof in this file may unfold either side
-- of Bridge 1.
set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ## `keccak.absorb_final` ↔ `sponge.absorb_final`. -/

/-- Local triple-of-ok helper. -/
private theorem triple_of_ok_af {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PredTrans.apply, hp]

/-- Local existence extractor. -/
private theorem triple_exists_ok_af {α : Type} {x : Result α}
    {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v =>
      refine ⟨v, rfl, ?_⟩
      have := h; simp [Std.Do.Triple, WP.wp, PredTrans.apply] at this; exact this
  | .fail _ =>
      exfalso; have := h; simp [Std.Do.Triple, WP.wp, PredTrans.apply] at this
  | .div =>
      exfalso; have := h; simp [Std.Do.Triple, WP.wp, PredTrans.apply] at this

/-! ### Array index_mut Triple over `Range Usize`.

The Array variant of `core_models_Slice_Insts_index_mut_RangeUsize_spec`
(SliceSpecs.lean). Routes through `Array.to_slice_mut`. -/
@[spec]
theorem core_models_Array_Insts_index_mut_RangeUsize_spec
    {T : Type} {N : Std.Usize} (arr : Std.Array T N)
    (r : CoreModels.core.ops.range.Range Std.Usize)
    (h0 : r.start.val ≤ r.end.val) (h1 : r.end.val ≤ N.val) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.Array.Insts.CoreOpsIndexIndexMut.index_mut
      (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) arr r
    ⦃ ⇓ p => ⌜ p.1.val = arr.val.slice r.start.val r.end.val ∧
                p.1.val.length = r.end.val - r.start.val ∧
                ∀ s' : Slice T, s'.val.length = r.end.val - r.start.val →
                  (p.2 s').val = arr.val.setSlice! r.start.val s'.val ⌝ ⦄ := by
  unfold CoreModels.core.Array.Insts.CoreOpsIndexIndexMut.index_mut
  have h_to_slice_mut : Std.Array.to_slice_mut arr
      = (Std.Array.to_slice arr, Std.Array.from_slice arr) := rfl
  have h_val_to_slice : (Std.Array.to_slice arr).val = arr.val := Std.Array.val_to_slice arr
  have h_len_to_slice : (Std.Array.to_slice arr).val.length = N.val := by
    rw [h_val_to_slice]; exact arr.property
  have h1' : r.end.val ≤ (Std.Array.to_slice arr).val.length := by rw [h_len_to_slice]; exact h1
  have h_slice :=
    core_models_Slice_Insts_index_mut_RangeUsize_spec (Std.Array.to_slice arr) r h0 h1'
  obtain ⟨p_slice, hp_eq, hp_val, hp_len, hp_back⟩ := triple_exists_ok_af h_slice
  have h_slice_eq_core :
      (core.slice.index.Slice.index_mut
        (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T)
        (Std.Array.to_slice arr) r) = .ok p_slice := by
    have := hp_eq
    unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut at this
    exact this
  set out_val := p_slice.1
  set to_slice_back := p_slice.2
  refine triple_of_ok_af (v := (out_val, fun o => Std.Array.from_slice arr (to_slice_back o))) ?_ ?_
  · show (do
      let (s, to_arr) := Std.Array.to_slice_mut arr
      let (out, ts) ← core.slice.index.Slice.index_mut
        (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T)
        s r
      ok (out, fun o => to_arr (ts o))) = .ok _
    rw [h_to_slice_mut]
    simp only
    rw [h_slice_eq_core]; simp only [bind_tc_ok]
    rfl
  · refine ⟨?_, ?_, ?_⟩
    · show p_slice.1.val = arr.val.slice r.start.val r.end.val
      rw [hp_val, h_val_to_slice]
    · show p_slice.1.val.length = r.end.val - r.start.val
      exact hp_len
    · intro s' h_s'_len
      show (Std.Array.from_slice arr (to_slice_back s')).val = arr.val.setSlice! r.start.val s'.val
      have h_back_len : (to_slice_back s').val.length = N.val := by
        rw [hp_back s']
        rw [List.length_setSlice!]; exact h_len_to_slice
      rw [Std.Array.from_slice_val _ _ h_back_len]
      rw [hp_back s']
      rw [h_val_to_slice]

/-! ### `padded_buf` — the shared 4-step buffer value.

Both the impl's manual buffer construction and the spec's
`sponge.pad_last_block` produce this `Array U8 200` value. The follow-up
that lands the full textbook post will prove the impl/spec chains both
reduce to `.ok (padded_buf last start len i_r1 DELIM)`. -/
def padded_buf
    (last : Slice Std.U8) (start len i_r1 : Std.Usize) (DELIM : Std.U8) :
    Std.Array Std.U8 200#usize :=
  let buf0 : Std.Array Std.U8 200#usize := Std.Array.repeat 200#usize 0#u8
  let buf1_val : List Std.U8 :=
    if 0 < len.val then
      buf0.val.setSlice! 0 (last.val.slice start.val (start.val + len.val))
    else buf0.val
  let buf1 : Std.Array Std.U8 200#usize := ⟨buf1_val, by
    show (if 0 < len.val then buf0.val.setSlice! 0 (last.val.slice start.val (start.val + len.val))
          else buf0.val).length = (200#usize : Std.Usize).val
    split <;> simp [List.length_setSlice!, buf0.property]⟩
  let buf2 : Std.Array Std.U8 200#usize := buf1.set len DELIM
  buf2.set i_r1 (buf2.val[i_r1.val]! ||| 128#u8)

/-! ### Main Triple. -/

/-- `keccak.absorb_final RATE DELIM s last start len`:
    build a 200-byte padded buffer (zero-init, copy `last[start..start+len]`,
    write `DELIM` at offset `len`, OR `0x80` into byte `RATE-1`), then
    load-and-permute the rate-window.

    **Textbook post** (full equality form): termination, `r.i.val = 0`,
    plus the spec equation
    `sponge.absorb_final (lift s) last start len RATE DELIM = .ok (lift r)`.

    Strategy: walk impl and spec side independently as explicit
    `.ok`-equations, then compose. Both sides produce the *same* shared
    buffer `buf3` (the impl's manual 4-step chain and the spec's
    `sponge.pad_last_block` chain match step-for-step).

    Preconditions match the impl's `massert (len < RATE)` plus the
    standard `RATE.val % 8 = 0`, `1 ≤ RATE.val ≤ 200`, and bounds for the
    byte-window inside `last`. -/
@[spec]
theorem keccak.absorb_final_spec
    (RATE : Std.Usize) (DELIM : Std.U8) (s : state.KeccakState)
    (last : Slice Std.U8) (start : Std.Usize) (len : Std.Usize)
    (h_i : s.i.val = 0)
    (h_len_lt_RATE : len.val < RATE.val)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_ge_1 : 1 ≤ RATE.val)
    (h_RATE_le_200 : RATE.val ≤ 200)
    (h_last_len : start.val + len.val ≤ last.val.length)
    (h_off : start.val + len.val ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.absorb_final RATE DELIM s last start len
    ⦃ ⇓ r => ⌜ r.i.val = 0
              ∧ sponge.absorb_final (Foundation.lift s) last start len RATE DELIM
                  = .ok (Foundation.lift r) ⌝ ⦄ := by
  -- Common: RATE.val ≤ Std.Usize.max.
  have h_RATE_max : RATE.val ≤ Std.Usize.max := by
    have h200 : (200 : Nat) ≤ Std.Usize.max := by scalar_tac
    omega
  -- RATE - 1#usize = .ok i_r1, i_r1.val = RATE.val - 1.
  obtain ⟨i_r1, h_i_r1_eq, h_i_r1_val_eq, _⟩ :=
    Std.WP.spec_imp_exists
      (Std.UScalar.sub_bv_spec (x := RATE) (y := 1#usize) (by
        have h1 : (1#usize : Std.Usize).val = 1 := by decide
        rw [h1]; exact h_RATE_ge_1))
  have h_i_r1_val : i_r1.val = RATE.val - 1 := by
    rw [h_i_r1_val_eq]
    show RATE.val - (1#usize : Std.Usize).val = RATE.val - 1
    have h1 : (1#usize : Std.Usize).val = 1 := by decide
    rw [h1]
  have h_i_r1_lt_200 : i_r1.val < 200 := by rw [h_i_r1_val]; omega
  -- Show existence: ∃ r, keccak.absorb_final = .ok r ∧ r.i.val = 0 ∧
  -- sponge.absorb_final (lift s) ... = .ok (lift r).
  suffices h_exists :
      ∃ (r : state.KeccakState),
        keccak.absorb_final RATE DELIM s last start len = .ok r ∧
        r.i.val = 0 ∧
        sponge.absorb_final (Foundation.lift s) last start len RATE DELIM
          = .ok (Foundation.lift r) by
    obtain ⟨r, h_r_eq, h_r_i, h_r_spec⟩ := h_exists
    exact triple_of_ok_af (v := r) h_r_eq ⟨h_r_i, h_r_spec⟩
  -- Compute the buffer chain's `.ok` value.
  -- Step values shared across branches.
  set buf0 : Std.Array Std.U8 200#usize := Std.Array.repeat 200#usize 0#u8 with hbuf0_def
  have h_classify_buf0 : libcrux_secrets.traits.Classify.Blanket.classify buf0
                        = (Result.ok buf0 : Result _) := rfl
  have h_classify_DELIM : libcrux_secrets.traits.Classify.Blanket.classify DELIM
                        = (Result.ok DELIM : Result _) := rfl
  have h_buf0_len : buf0.val.length = 200 := buf0.property
  have h_lift_or_eq : ∀ x : Std.U8, (Std.lift (x ||| 128#u8) : Result Std.U8) = .ok (x ||| 128#u8) := by
    intro x; rfl
  have h_ma : massert (len < RATE) = .ok () := by
    unfold massert
    rw [if_pos (by show len < RATE; exact (Std.UScalar.lt_equiv len RATE).mpr h_len_lt_RATE)]
  -- The buffer chain produces a `buf1` (the `if`-branch result) and from
  -- there to `buf3`. We unify via case analysis on `len > 0`.
  -- Build `buf1` directly as an `Array U8 200` whose `.val` matches the
  -- if-branch's value.
  set buf1_val : List Std.U8 :=
    if 0 < len.val then
      buf0.val.setSlice! 0 (last.val.slice start.val (start.val + len.val))
    else buf0.val with hbuf1_val_def
  have h_buf1_val_len : buf1_val.length = 200 := by
    rw [hbuf1_val_def]; split <;> simp [List.length_setSlice!, h_buf0_len]
  set buf1 : Std.Array Std.U8 200#usize := ⟨buf1_val, by
    show buf1_val.length = (200#usize : Std.Usize).val
    rw [h_buf1_val_len]; rfl⟩ with hbuf1_def
  -- update buf1 len DELIM = .ok buf2.
  have h_len_lt_buf1 : len.val < buf1.val.length := by
    have : buf1.val.length = 200 := h_buf1_val_len
    omega
  obtain ⟨buf2, h_buf2_eq, h_buf2_set⟩ :=
    Std.WP.spec_imp_exists (Std.Array.update_spec buf1 len DELIM h_len_lt_buf1)
  -- index_usize buf2 i_r1 = .ok delim_byte.
  have h_i_r1_lt_buf2 : i_r1.val < buf2.val.length := by
    have hlen : buf2.val.length = (200#usize : Std.Usize).val := buf2.property
    show i_r1.val < buf2.val.length
    rw [hlen]; show i_r1.val < 200; omega
  obtain ⟨delim_byte, h_idx_eq, h_idx_val⟩ :=
    Std.WP.spec_imp_exists (Std.Array.index_usize_spec buf2 i_r1 h_i_r1_lt_buf2)
  -- update buf2 i_r1 (delim_byte ||| 0x80) = .ok buf3.
  obtain ⟨buf3, h_buf3_eq, h_buf3_set⟩ :=
    Std.WP.spec_imp_exists
      (Std.Array.update_spec buf2 i_r1 (delim_byte ||| 128#u8) h_i_r1_lt_buf2)
  -- absorb_block_spec on (to_slice buf3, 0).
  have h_blk : (0#usize : Std.Usize).val + RATE.val ≤ (Std.Array.to_slice buf3).val.length := by
    have hlen : (Std.Array.to_slice buf3).val.length = 200 := by
      rw [Std.Array.val_to_slice]; exact buf3.property
    rw [hlen]; show 0 + RATE.val ≤ 200; omega
  have h_off' : (0#usize : Std.Usize).val + RATE.val ≤ Std.Usize.max := by
    show 0 + RATE.val ≤ Std.Usize.max; omega
  obtain ⟨r, h_r_eq, h_r_post⟩ :=
    triple_exists_ok_af
      (keccak.absorb_block_spec RATE s (Std.Array.to_slice buf3) 0#usize
        h_i h_RATE_mod h_RATE_le_200 h_blk h_off')
  obtain ⟨h_r_i, h_r_spec⟩ := h_r_post
  -- absorb_block = load_block_full + keccakf1600 (after to_slice).
  have h_absorb_eq :
      (do
        let s1 ← state.KeccakState.load_block_full RATE s buf3 0#usize
        keccak.keccakf1600 s1)
      = keccak.absorb_block RATE s (Std.Array.to_slice buf3) 0#usize := by
    unfold keccak.absorb_block
    unfold state.KeccakState.load_block_full state.load_block_full_2u32
    unfold state.KeccakState.load_block
    show (do
            let s1 ← (do
                        let s2 ← Std.lift (α := Slice Std.U8) (Std.Array.to_slice buf3)
                        state.load_block_2u32 RATE s s2 0#usize)
            keccak.keccakf1600 s1) = (do
            let s1 ← state.load_block_2u32 RATE s (Std.Array.to_slice buf3) 0#usize
            keccak.keccakf1600 s1)
    unfold Std.lift
    show (do
            let s1 ← (do
                        let s2 ← (Result.ok (Std.Array.to_slice buf3) : Result (Slice Std.U8))
                        state.load_block_2u32 RATE s s2 0#usize)
            keccak.keccakf1600 s1) = _
    simp only [bind_tc_ok]
  -- The if-branch produces `.ok buf1`. We prove this via case analysis.
  have h_if_eq :
      (if len > 0#usize
        then
          (do
            let (s, index_mut_back) ←
              CoreModels.core.Array.Insts.CoreOpsIndexIndexMut.index_mut
                (CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut
                  (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                    Std.U8)) buf0 { start := 0#usize, «end» := len }
            let i ← start + len
            let s2 ←
              CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
                (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                  Std.U8) last { start, «end» := i }
            let s3 ←
              CoreModels.core.slice.Slice.copy_from_slice
                CoreModels.core.U8.Insts.CoreMarkerCopy s s2
            ok (index_mut_back s3))
        else (ok buf0 : Result (Std.Array Std.U8 200#usize)))
        = .ok buf1 := by
    by_cases hlen : (len > 0#usize)
    · rw [if_pos hlen]
      have h_len_val_pos : 0 < len.val := by
        have := (Std.UScalar.lt_equiv 0#usize len).mp hlen
        show 0 < len.val; omega
      have h_im_le : ((0#usize : Std.Usize).val) ≤ len.val := by show 0 ≤ len.val; omega
      have h_im_bnd : len.val ≤ (200#usize : Std.Usize).val := by show len.val ≤ 200; omega
      have h_wrap_eq_im :
          CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut
            (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
          = CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8 := rfl
      rw [h_wrap_eq_im]
      obtain ⟨p_im, h_pim_eq, h_pim_val, h_pim_len, h_pim_back⟩ :=
        triple_exists_ok_af
          (core_models_Array_Insts_index_mut_RangeUsize_spec
            buf0 { start := 0#usize, «end» := len } h_im_le h_im_bnd)
      rw [h_pim_eq]; simp only [bind_tc_ok]
      obtain ⟨s_im, write_back⟩ := p_im
      simp only at h_pim_val h_pim_len h_pim_back ⊢
      -- The destructure pattern `let (s, im_back) := (s_im, write_back)` doesn't auto-reduce.
      -- Use `show` to manually beta-reduce.
      show (do
              let i ← start + len
              let s2 ← CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
                (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                  Std.U8) last { start, «end» := i }
              let s3 ← CoreModels.core.slice.Slice.copy_from_slice
                CoreModels.core.U8.Insts.CoreMarkerCopy s_im s2
              ok (write_back s3)) = _
      obtain ⟨i_sl, h_i_sl_eq, h_i_sl_val_eq, _⟩ :=
        Std.WP.spec_imp_exists
          (Std.UScalar.add_bv_spec (x := start) (y := len) (by scalar_tac))
      have h_i_sl_val : i_sl.val = start.val + len.val := h_i_sl_val_eq
      rw [h_i_sl_eq]; simp only [bind_tc_ok]
      have h_idx_le : start.val ≤ i_sl.val := by rw [h_i_sl_val]; omega
      have h_idx_bnd : i_sl.val ≤ last.val.length := by rw [h_i_sl_val]; omega
      obtain ⟨q, hq_eq, hq_val, hq_len⟩ :=
        triple_exists_ok_af
          (core_models_Slice_Insts_index_RangeUsize_spec
            last { start, «end» := i_sl } h_idx_le h_idx_bnd)
      rw [hq_eq]; simp only [bind_tc_ok]
      have h_p_q_len : s_im.val.length = q.val.length := by
        rw [h_pim_len, hq_len]
        show len.val - (0#usize : Std.Usize).val = i_sl.val - start.val
        rw [show ((0#usize : Std.Usize).val : Nat) = 0 from rfl, Nat.sub_zero, h_i_sl_val]
        omega
      obtain ⟨w, hw_eq, hw_val⟩ :=
        triple_exists_ok_af
          (core_models_slice_Slice_copy_from_slice_spec
            CoreModels.core.U8.Insts.CoreMarkerCopy s_im q h_p_q_len)
      rw [hw_eq]; simp only [bind_tc_ok]
      -- Conclude write_back w = buf1.
      have h_w_val_len : w.val.length = len.val - (0#usize : Std.Usize).val := by
        rw [hw_val, hq_len]
        rw [show ((0#usize : Std.Usize).val : Nat) = 0 from rfl]
        rw [show i_sl.val - start.val = len.val from by rw [h_i_sl_val]; omega]
        rw [show len.val - 0 = len.val from by omega]
      have h_pback := h_pim_back w h_w_val_len
      have h_q_val_eq : q.val = last.val.slice start.val (start.val + len.val) := by
        rw [hq_val]
        show last.val.slice start.val i_sl.val = _
        rw [show i_sl.val = start.val + len.val from h_i_sl_val]
      apply Eq.symm
      show (Result.ok buf1 : Result (Std.Array Std.U8 200#usize)) = Result.ok (write_back w)
      congr 1
      apply Subtype.ext
      show buf1.val = (write_back w).val
      rw [h_pback, hw_val, h_q_val_eq]
      rw [hbuf1_def]
      show buf1_val = _
      rw [hbuf1_val_def, if_pos h_len_val_pos]
      show _ = buf0.val.setSlice! ((0#usize : Std.Usize).val) _
      rfl
    · rw [if_neg hlen]
      have h_len_val_zero : len.val = 0 := by
        have hle : ¬ (0 < len.val) := fun h => hlen ((Std.UScalar.lt_equiv 0#usize len).mpr (by show 0 < len.val; exact h))
        omega
      apply Eq.symm
      show (Result.ok buf1 : Result (Std.Array Std.U8 200#usize)) = Result.ok buf0
      congr 1
      apply Subtype.ext
      show buf1.val = buf0.val
      rw [hbuf1_def]; show buf1_val = buf0.val
      rw [hbuf1_val_def, if_neg (by omega : ¬ 0 < len.val)]
  -- Spec-side: `sponge.pad_last_block ... = .ok buf3`.
  -- The spec has no `if len > 0` — it always takes the index_mut path.
  -- When len = 0, the path's slice is empty and the write_back is identity,
  -- which still produces `buf1` (= buf0 in that case).
  -- `sponge.pad_last_block last start len RATE DELIM = .ok buf3`.
  have h_pad_eq :
      sponge.pad_last_block last start len RATE DELIM = .ok buf3 := by
    unfold sponge.pad_last_block
    -- Reduce `let buffer := Array.repeat 200 0` to `buf0`.
    simp only [hbuf0_def.symm]
    -- Compute the index_mut/copy prefix to `.ok buf1` via `h_spec_chain_eq`.
    -- First reform the prefix to match h_spec_chain_eq's exact shape. Note
    -- the spec's chain is `... ; let buffer1 := index_mut_back s2; ...`,
    -- which Lean's `do`-notation desugars as a pure let. We turn it into
    -- `let buffer1 ← ok (...)` so it joins the monadic chain, then split.
    show (do
            let (s, index_mut_back) ←
              CoreModels.core.Array.Insts.CoreOpsIndexIndexMut.index_mut
                (CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut
                  (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                    Std.U8)) buf0 { start := 0#usize, «end» := len }
            let i ← start + len
            let s1 ← CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
              (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                Std.U8) last { start := start, «end» := i }
            let s2 ← CoreModels.core.slice.Slice.copy_from_slice
              CoreModels.core.U8.Insts.CoreMarkerCopy s s1
            let buffer1 := index_mut_back s2
            let buffer2 ← Std.Array.update buffer1 len DELIM
            let i1 ← RATE - 1#usize
            let i2 ← Std.Array.index_usize buffer2 i1
            let i3 ← Std.lift (i2 ||| 128#u8)
            Std.Array.update buffer2 i1 i3) = .ok buf3
    -- Use the unwrapped form of the IndexMut instance.
    have h_wrap_eq_im :
        CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut
          (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
        = CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8 := rfl
    rw [h_wrap_eq_im]
    -- Build the unfolded prefix result.
    have h_im_le : ((0#usize : Std.Usize).val) ≤ len.val := by show 0 ≤ len.val; omega
    have h_im_bnd : len.val ≤ (200#usize : Std.Usize).val := by show len.val ≤ 200; omega
    obtain ⟨p_im, h_pim_eq, h_pim_val, h_pim_len, h_pim_back⟩ :=
      triple_exists_ok_af
        (core_models_Array_Insts_index_mut_RangeUsize_spec
          buf0 { start := 0#usize, «end» := len } h_im_le h_im_bnd)
    rw [h_pim_eq]; simp only [bind_tc_ok]
    obtain ⟨s_im, write_back⟩ := p_im
    simp only at h_pim_val h_pim_len h_pim_back ⊢
    show (do
            let i ← start + len
            let s1 ← CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
              (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                Std.U8) last { start := start, «end» := i }
            let s2 ← CoreModels.core.slice.Slice.copy_from_slice
              CoreModels.core.U8.Insts.CoreMarkerCopy s_im s1
            let buffer1 := write_back s2
            let buffer2 ← Std.Array.update buffer1 len DELIM
            let i1 ← RATE - 1#usize
            let i2 ← Std.Array.index_usize buffer2 i1
            let i3 ← Std.lift (i2 ||| 128#u8)
            Std.Array.update buffer2 i1 i3) = .ok buf3
    obtain ⟨i_sl, h_i_sl_eq, h_i_sl_val_eq, _⟩ :=
      Std.WP.spec_imp_exists
        (Std.UScalar.add_bv_spec (x := start) (y := len) (by scalar_tac))
    have h_i_sl_val : i_sl.val = start.val + len.val := h_i_sl_val_eq
    rw [h_i_sl_eq]; simp only [bind_tc_ok]
    have h_idx_le : start.val ≤ i_sl.val := by rw [h_i_sl_val]; omega
    have h_idx_bnd : i_sl.val ≤ last.val.length := by rw [h_i_sl_val]; omega
    obtain ⟨q, hq_eq, hq_val, hq_len⟩ :=
      triple_exists_ok_af
        (core_models_Slice_Insts_index_RangeUsize_spec
          last { start := start, «end» := i_sl } h_idx_le h_idx_bnd)
    rw [hq_eq]; simp only [bind_tc_ok]
    have h_p_q_len : s_im.val.length = q.val.length := by
      rw [h_pim_len, hq_len]
      show len.val - (0#usize : Std.Usize).val = i_sl.val - start.val
      rw [show ((0#usize : Std.Usize).val : Nat) = 0 from rfl, Nat.sub_zero, h_i_sl_val]
      omega
    obtain ⟨w, hw_eq, hw_val⟩ :=
      triple_exists_ok_af
        (core_models_slice_Slice_copy_from_slice_spec
          CoreModels.core.U8.Insts.CoreMarkerCopy s_im q h_p_q_len)
    rw [hw_eq]; simp only [bind_tc_ok]
    have h_w_val_len : w.val.length = len.val - (0#usize : Std.Usize).val := by
      rw [hw_val, hq_len]
      rw [show ((0#usize : Std.Usize).val : Nat) = 0 from rfl]
      rw [show i_sl.val - start.val = len.val from by rw [h_i_sl_val]; omega]
      rw [show len.val - 0 = len.val from by omega]
    have h_pback := h_pim_back w h_w_val_len
    have h_q_val_eq : q.val = last.val.slice start.val (start.val + len.val) := by
      rw [hq_val]
      show last.val.slice start.val i_sl.val = _
      rw [show i_sl.val = start.val + len.val from h_i_sl_val]
    -- Now `write_back w = buf1`.
    have h_wb_buf1 : write_back w = buf1 := by
      apply Subtype.ext
      show (write_back w).val = buf1.val
      rw [h_pback, hw_val, h_q_val_eq]
      rw [hbuf1_def]
      show _ = buf1_val
      rw [hbuf1_val_def]
      by_cases hlen0 : 0 < len.val
      · rw [if_pos hlen0]
        show buf0.val.setSlice! ((0#usize : Std.Usize).val) _ = _
        rfl
      · rw [if_neg hlen0]
        have hlen_zero : len.val = 0 := by omega
        have h_q_empty : last.val.slice start.val (start.val + len.val) = [] := by
          rw [hlen_zero]
          show last.val.slice start.val (start.val + 0) = []
          rw [Nat.add_zero]
          unfold List.slice
          rw [show start.val - start.val = 0 from by omega, List.take_zero]
        show buf0.val.setSlice! ((0#usize : Std.Usize).val) _ = buf0.val
        rw [h_q_empty]
        show buf0.val.setSlice! 0 [] = buf0.val
        unfold List.setSlice!
        simp
    -- Continue: write_back w = buf1, then update buf1 len DELIM = .ok buf2, etc.
    rw [h_wb_buf1]
    rw [h_buf2_eq]; simp only [bind_tc_ok]
    rw [h_i_r1_eq]; simp only [bind_tc_ok]
    rw [h_idx_eq]; simp only [bind_tc_ok]
    rw [h_lift_or_eq delim_byte]; simp only [bind_tc_ok]
    exact h_buf3_eq
  -- Spec-side: `block[0..rate]` (Array index on buf3) = .ok (block_of_blocks (to_slice buf3) 0 RATE _).
  have h_block_idx_eq :
      CoreModels.core.Array.Insts.CoreOpsIndexIndex.index
        (CoreModels.core.Slice.Insts.CoreOpsIndexIndex
          (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
            Std.U8)) buf3 { start := 0#usize, «end» := RATE }
        = .ok (block_of_blocks (Std.Array.to_slice buf3) 0#usize RATE h_blk) := by
    -- Unfold Array index → slice index over to_slice.
    unfold CoreModels.core.Array.Insts.CoreOpsIndexIndex.index
    -- The body is `core.slice.index.Slice.index inst (to_slice buf3) r`.
    -- This is the same as `CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index`
    -- after the wrapper is collapsed.
    have h_wrap_eq :
        CoreModels.core.Slice.Insts.CoreOpsIndexIndex
          (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
        = CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8 := rfl
    rw [h_wrap_eq]
    have h0' : ((0#usize : Std.Usize).val) ≤ RATE.val := by show 0 ≤ RATE.val; omega
    have h1' : RATE.val ≤ (Std.Array.to_slice buf3).val.length := by
      have hlen : (Std.Array.to_slice buf3).val.length = 200 := by
        rw [Std.Array.val_to_slice]; exact buf3.property
      rw [hlen]; exact h_RATE_le_200
    obtain ⟨q, hq_eq, hq_val, hq_len⟩ :=
      triple_exists_ok_af
        (core_models_Slice_Insts_index_RangeUsize_spec
          (Std.Array.to_slice buf3) { start := 0#usize, «end» := RATE } h0' h1')
    have h_slice_eq :
        core.slice.index.Slice.index
          (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
          (Std.Array.to_slice buf3) { start := 0#usize, «end» := RATE } = .ok q := by
      have := hq_eq
      unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index at this
      exact this
    rw [h_slice_eq]
    apply congrArg
    apply Subtype.ext
    show q.val = (block_of_blocks (Std.Array.to_slice buf3) 0#usize RATE h_blk).val
    rw [hq_val]
    show (Std.Array.to_slice buf3).val.slice (0#usize : Std.Usize).val RATE.val
        = (Std.Array.to_slice buf3).val.slice 0 (0 + RATE.val)
    rw [show ((0#usize : Std.Usize).val : Nat) = 0 from rfl, Nat.zero_add]
  -- Compose spec sides.
  have h_spec_eq :
      sponge.absorb_final (Foundation.lift s) last start len RATE DELIM
        = .ok (Foundation.lift r) := by
    unfold sponge.absorb_final
    rw [h_pad_eq]; simp only [bind_tc_ok]
    rw [h_block_idx_eq]; simp only [bind_tc_ok]
    exact h_r_spec
  -- Assemble the impl-side equation.
  refine ⟨r, ?_, h_r_i, h_spec_eq⟩
  unfold keccak.absorb_final
  -- Skip the `show` — work directly with the desugared form.
  rw [h_ma]; simp only [bind_tc_ok]
  -- `Array.repeat 200#usize 0#u8` is definitionally `buf0`, so `classify
  -- (Array.repeat ...)` reduces. We apply `rw` directly on `classify`.
  -- The let-bind for `a` is a `have` after simp.
  simp only [hbuf0_def.symm]
  rw [h_classify_buf0]; simp only [bind_tc_ok]
  -- The `if-let-bind` desugars with __do_jp. Rewrite the if-branch's
  -- value to `.ok buf1` directly using h_if_eq, by manipulating the
  -- desugared form.
  rw [h_if_eq]
  -- Now blocks1 := buf1; continue.
  simp only [bind_tc_ok]
  rw [h_classify_DELIM]; simp only [bind_tc_ok]
  rw [h_buf2_eq]; simp only [bind_tc_ok]
  rw [h_i_r1_eq]; simp only [bind_tc_ok]
  rw [h_idx_eq]; simp only [bind_tc_ok]
  rw [h_lift_or_eq delim_byte]; simp only [bind_tc_ok]
  rw [h_buf3_eq]; simp only [bind_tc_ok]
  rw [h_absorb_eq]
  exact h_r_eq

end libcrux_iot_sha3.Sponge
