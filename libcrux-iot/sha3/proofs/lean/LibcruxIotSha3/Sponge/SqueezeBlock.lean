/-
  # Squeeze block-level Triples.

  Bridges the impl-side squeeze block functions to the underlying byte
  projection of the sponge state, optionally preceded by a
  `keccakf1600` permutation.

  Four `@[spec]` Triples:

  - `keccak.squeeze_first_block_spec` — direct delegation to
    `store_block_spec` (no permutation).
  - `keccak.squeeze_next_block_spec`  — `keccakf1600` then `store_block`,
    returning the new state and output buffer.
  - `keccak.squeeze_last_spec`        — `keccakf1600`, `store_block_full`
    into a 200-byte buffer, then copy first `out.length` bytes.
  - `keccak.squeeze_first_and_last_spec` — no permutation, partial
    output via `store_block_full` + copy.

-/
import LibcruxIotSha3.Sponge.AbsorbBlock

open Aeneas Aeneas.Std Result Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

open libcrux_iot_sha3.Foundation

-- Defensive seal re-issue: no proof in this file may unfold either side
-- of Bridge 1.
set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ## Squeeze block-level Triples. -/

/-- Local triple-of-ok helper. -/
private theorem triple_of_ok_sb {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PredTrans.apply, hp]

/-- Local existence extractor: a Triple yields `∃ v, x = .ok v ∧ P v`. -/
private theorem triple_exists_ok_sb {α : Type} {x : Result α}
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

/-! ### Triple 1: `keccak.squeeze_first_block`. -/

/-- `keccak.squeeze_first_block RATE s out` — extract first output block
    by directly applying `store_block` (no `keccakf1600`).

    Post: matches `store_block_spec` exactly. -/
@[spec]
theorem keccak.squeeze_first_block_spec
    (RATE : Std.Usize) (s : state.KeccakState) (out : Slice Std.U8)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_bnd : RATE.val ≤ 200)
    (h_out : RATE.val ≤ out.val.length)
    (h_off : RATE.val ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.squeeze_first_block RATE s out
    ⦃ ⇓ r => ⌜
        r.val.length = out.val.length
        ∧ ∀ k : Nat, k < RATE.val →
            r.val[k]! = ⟨(BitVec.toLEBytes
              ((Foundation.lift s).val[k / 8]!).bv)[k % 8]!⟩
    ⌝ ⦄ := by
  -- Delegate to `store_block_spec`.
  obtain ⟨r, h_r_eq, h_r_len, h_r_bytes⟩ :=
    triple_exists_ok_sb
      (state.KeccakState.store_block_spec RATE s out
        h_RATE_mod h_RATE_bnd h_out h_off)
  apply triple_of_ok_sb (v := r) _ ⟨h_r_len, h_r_bytes⟩
  show keccak.squeeze_first_block RATE s out = .ok r
  unfold keccak.squeeze_first_block
  exact h_r_eq

/-! ### Triple 2: `keccak.squeeze_next_block`. -/

/-- `keccak.squeeze_next_block RATE s out` —
    `keccakf1600 s ; store_block`. Returns the tuple `(s_new, out_new)`.

    Post:
    - `r.1.i.val = 0` (impl-side `keccakf1600` resets `i`).
    - `r.2.val.length = out.val.length`.
    - There exists `s_spec` with `keccak_f.keccak_f (lift s) = .ok s_spec`,
      `s_spec = lift r.1`, and for every `k < RATE.val`,
      `r.2.val[k]! = (s_spec.val[k/8]!).bv.toLEBytes[k%8]!`. -/
@[spec]
theorem keccak.squeeze_next_block_spec
    (RATE : Std.Usize) (s : state.KeccakState) (out : Slice Std.U8)
    (h_i : s.i.val = 0)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_bnd : RATE.val ≤ 200)
    (h_out : RATE.val ≤ out.val.length)
    (h_off : RATE.val ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.squeeze_next_block RATE s out
    ⦃ ⇓ r => ⌜
        r.1.i.val = 0
        ∧ r.2.val.length = out.val.length
        ∧ ∃ s_spec : Std.Array Std.U64 25#usize,
            keccak_f.keccak_f (Foundation.lift s) = .ok s_spec
            ∧ s_spec = Foundation.lift r.1
            ∧ ∀ k : Nat, k < RATE.val →
                r.2.val[k]! = ⟨(BitVec.toLEBytes
                  (s_spec.val[k / 8]!).bv)[k % 8]!⟩
    ⌝ ⦄ := by
  -- Step 1: discharge `keccakf1600` via the Opaque seal.
  obtain ⟨s1, h_s1_eq, h_s1_spec, h_s1_i⟩ :=
    triple_exists_ok_sb (keccakf1600_seal_spec s h_i)
  -- Step 2: discharge `store_block` on `s1`.
  obtain ⟨out1, h_out1_eq, h_out1_len, h_out1_bytes⟩ :=
    triple_exists_ok_sb
      (state.KeccakState.store_block_spec RATE s1 out
        h_RATE_mod h_RATE_bnd h_out h_off)
  -- Step 3: assemble impl-side equality
  -- `keccak.squeeze_next_block ... = .ok (s1, out1)`.
  have h_impl_eq :
      keccak.squeeze_next_block RATE s out = .ok (s1, out1) := by
    unfold keccak.squeeze_next_block
    rw [h_s1_eq]; simp only [bind_tc_ok]
    rw [h_out1_eq]; simp only [bind_tc_ok]
  -- Step 4: package the post.
  apply triple_of_ok_sb (v := (s1, out1)) h_impl_eq
  refine ⟨h_s1_i, h_out1_len, Foundation.lift s1, h_s1_spec, rfl, ?_⟩
  intro k hk
  exact h_out1_bytes k hk

/-! ### Helper: `state.KeccakState.store_block_full` Triple.

The full-array variant delegates to `state.store_block_2u32` after the
`Array.to_slice_mut` coercion. The resulting array has the same per-byte
characterization as `store_block_spec` for the first `RATE.val` bytes;
later bytes are unconstrained (the wrapper's `Array.from_slice` writes
back the modified slice as the entire array). -/

/-- `state.KeccakState.store_block_full RATE s out` succeeds and the
    resulting array's first `RATE.val` bytes match the `store_block_spec`
    per-byte formula on `lift s`. -/
theorem state.KeccakState.store_block_full_spec
    (RATE : Std.Usize) (s : state.KeccakState)
    (out : Std.Array Std.U8 200#usize)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_bnd : RATE.val ≤ 200) :
    ⦃ ⌜ True ⌝ ⦄
    state.KeccakState.store_block_full RATE s out
    ⦃ ⇓ r => ⌜
        r.val.length = 200
        ∧ ∀ k : Nat, k < RATE.val →
            r.val[k]! = ⟨(BitVec.toLEBytes
              ((Foundation.lift s).val[k / 8]!).bv)[k % 8]!⟩
    ⌝ ⦄ := by
  -- `Array.to_slice out` has `.val = out.val` (length 200).
  have h_to_slice_val : (Std.Array.to_slice out).val = out.val := rfl
  have h_to_slice_len : (Std.Array.to_slice out).val.length = 200 := by
    rw [h_to_slice_val]; exact out.property
  have h_out_len : RATE.val ≤ (Std.Array.to_slice out).val.length := by
    rw [h_to_slice_len]; exact h_RATE_bnd
  have h_off : RATE.val ≤ Std.Usize.max := by
    have : (200 : Nat) ≤ Std.Usize.max := by scalar_tac
    omega
  -- Apply `store_block_spec` on the slice.
  obtain ⟨s_inner, h_s_inner_eq, h_s_inner_len, h_s_inner_bytes⟩ :=
    triple_exists_ok_sb
      (state.KeccakState.store_block_spec RATE s
        (Std.Array.to_slice out) h_RATE_mod h_RATE_bnd h_out_len h_off)
  -- `s_inner.val.length = 200` from `store_block_spec`'s length post.
  have h_s_inner_len_200 : s_inner.val.length = 200 := by
    rw [h_s_inner_len]; exact h_to_slice_len
  -- The wrapper's `Array.from_slice` writes back the slice as the array.
  -- Compute `r = Array.from_slice out s_inner`. Its `.val = s_inner.val`.
  set r_arr : Std.Array Std.U8 200#usize := Std.Array.from_slice out s_inner with hr_def
  have hr_val_eq : r_arr.val = s_inner.val := by
    rw [hr_def]
    apply Std.Array.from_slice_val
    rw [h_s_inner_len_200]; rfl
  have hr_len : r_arr.val.length = 200 := by
    rw [hr_val_eq]; exact h_s_inner_len_200
  have hr_bytes : ∀ k : Nat, k < RATE.val →
      r_arr.val[k]! = ⟨(BitVec.toLEBytes
        ((Foundation.lift s).val[k / 8]!).bv)[k % 8]!⟩ := by
    intro k hk
    rw [hr_val_eq]
    exact h_s_inner_bytes k hk
  -- Now assemble the impl-side equality.
  have h_impl_eq :
      state.KeccakState.store_block_full RATE s out = .ok r_arr := by
    unfold state.KeccakState.store_block_full state.store_block_full_2u32
    -- Body: do
    --   let (s1, back) ← lift (Array.to_slice_mut out)
    --   let s2 ← state.store_block_2u32 RATE s s1
    --   ok (back s2)
    show (do
        let (s1, back) ← Std.lift (α := Slice Std.U8 × (Slice Std.U8 → _))
                                  (Std.Array.to_slice_mut out)
        let s2 ← state.store_block_2u32 RATE s s1
        Result.ok (back s2)) = .ok r_arr
    unfold Std.lift
    -- `lift (to_slice_mut out)` reduces to `.ok (to_slice out, from_slice out)`.
    show (do
        let (s1, back) ← (Result.ok (Std.Array.to_slice_mut out) :
                            Result (Slice Std.U8 × (Slice Std.U8 → _)))
        let s2 ← state.store_block_2u32 RATE s s1
        Result.ok (back s2)) = .ok r_arr
    simp only [bind_tc_ok]
    -- Now: `let (s1, back) := Array.to_slice_mut out` destructures.
    show (do
        let s2 ← state.store_block_2u32 RATE s (Std.Array.to_slice out)
        Result.ok (Std.Array.from_slice out s2)) = .ok r_arr
    -- `state.store_block_2u32` unfolds to `state.KeccakState.store_block`.
    have h_inner_unfold :
        state.store_block_2u32 RATE s (Std.Array.to_slice out) = .ok s_inner := by
      have := h_s_inner_eq
      unfold state.KeccakState.store_block at this
      exact this
    rw [h_inner_unfold]; simp only [bind_tc_ok]
    rw [hr_def]
  apply triple_of_ok_sb (v := r_arr) h_impl_eq ⟨hr_len, hr_bytes⟩

/-! ### Helper Triple: Array index by `Range Usize`.

Array variant of `core_models_Slice_Insts_index_RangeUsize_spec`
(SliceSpecs.lean). The Array index reduces to the Slice index via
`Array.to_slice`. -/

@[spec]
theorem core_models_Array_Insts_index_RangeUsize_spec
    {T : Type} {N : Std.Usize} (arr : Std.Array T N)
    (r : CoreModels.core.ops.range.Range Std.Usize)
    (h0 : r.start.val ≤ r.end.val) (h1 : r.end.val ≤ N.val) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.Array.Insts.CoreOpsIndexIndex.index
      (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) arr r
    ⦃ ⇓ r' => ⌜ r'.val = arr.val.slice r.start.val r.end.val ∧
                r'.val.length = r.end.val - r.start.val ⌝ ⦄ := by
  -- Reduce to the slice version via `Array.to_slice`.
  unfold CoreModels.core.Array.Insts.CoreOpsIndexIndex.index
  -- Body: `core.slice.index.Slice.index inst (Array.to_slice arr) i`.
  have h1' : r.end.val ≤ (Std.Array.to_slice arr).val.length := by
    rw [Std.Array.val_to_slice]
    have : arr.val.length = N.val := arr.property
    omega
  have h_slice_val : (Std.Array.to_slice arr).val = arr.val :=
    Std.Array.val_to_slice arr
  -- Use the existing slice spec.
  have h_slice :=
    core_models_Slice_Insts_index_RangeUsize_spec (Std.Array.to_slice arr) r h0 h1'
  -- The slice version uses `CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index`,
  -- which unfolds to the same `core.slice.index.Slice.index` we need here.
  -- Convert the slice spec's post (in terms of `arr.to_slice.val`) into one
  -- in terms of `arr.val`.
  obtain ⟨v, hv_eq, hv_val, hv_len⟩ := triple_exists_ok_sb h_slice
  refine triple_of_ok_sb (v := v) ?_ ?_
  · -- Equality: `core.slice.index.Slice.index inst (Array.to_slice arr) r = .ok v`.
    have := hv_eq
    unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index at this
    exact this
  · refine ⟨?_, ?_⟩
    · rw [hv_val, h_slice_val]
    · rw [hv_len]

/-! ### Triple 3: `keccak.squeeze_last`. -/

/-- `keccak.squeeze_last RATE s out` —
    `keccakf1600 s ; store_block_full into 200-byte buf ;
     copy first out.length bytes`.

    Post: state side gives `∃ s_spec, keccak_f (lift s) = .ok s_spec`,
    output side characterizes every byte `k < out.val.length` via the
    same `toLEBytes`-of-spec-state formula (after permutation).

    Side condition: `out.val.length ≤ RATE.val` (only the first RATE
    bytes of the 200-byte buffer are characterized by `store_block_full_spec`). -/
@[spec]
theorem keccak.squeeze_last_spec
    (RATE : Std.Usize) (s : state.KeccakState) (out : Slice Std.U8)
    (h_i : s.i.val = 0)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_bnd : RATE.val ≤ 200)
    (h_out_le_RATE : out.val.length ≤ RATE.val) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.squeeze_last RATE s out
    ⦃ ⇓ r => ⌜
        r.val.length = out.val.length
        ∧ ∃ s_spec : Std.Array Std.U64 25#usize,
            keccak_f.keccak_f (Foundation.lift s) = .ok s_spec
            ∧ ∀ k : Nat, k < out.val.length →
                r.val[k]! = ⟨(BitVec.toLEBytes
                  (s_spec.val[k / 8]!).bv)[k % 8]!⟩
    ⌝ ⦄ := by
  -- Step 1: discharge `keccakf1600` via the Opaque seal.
  obtain ⟨s1, h_s1_eq, h_s1_spec, h_s1_i⟩ :=
    triple_exists_ok_sb (keccakf1600_seal_spec s h_i)
  -- The 200-byte buffer (all zeros) — `classify a = .ok a`.
  set buf : Std.Array Std.U8 200#usize := Std.Array.repeat 200#usize 0#u8 with hbuf
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify buf = .ok buf := rfl
  -- Step 2: discharge `store_block_full` on `s1`.
  obtain ⟨b1, h_b1_eq, h_b1_len, h_b1_bytes⟩ :=
    triple_exists_ok_sb
      (state.KeccakState.store_block_full_spec RATE s1 buf
        h_RATE_mod h_RATE_bnd)
  -- Step 3: discharge `Slice.len out`.
  have h_len : CoreModels.core.slice.Slice.len out = .ok (Std.Slice.len out) := by
    unfold CoreModels.core.slice.Slice.len; rfl
  set i := Std.Slice.len out
  have h_i_val : i.val = out.val.length := by
    simp [i, Std.Slice.len]
  -- Step 4: index `b1` by `[0, i)`. We use the helper above.
  have h_i_le : (0#usize : Std.Usize).val ≤ i.val := by
    show 0 ≤ i.val; omega
  have h_i_le_N : i.val ≤ (200#usize : Std.Usize).val := by
    rw [h_i_val]
    have hb1len : b1.val.length = 200 := h_b1_len
    have hb1_prop : b1.val.length = (200#usize : Std.Usize).val := by
      rw [hb1len]; rfl
    show i.val ≤ 200
    -- Need out.val.length ≤ 200.
    rw [h_i_val]
    omega
  obtain ⟨s2, h_s2_eq, h_s2_val, h_s2_len⟩ :=
    triple_exists_ok_sb
      (core_models_Array_Insts_index_RangeUsize_spec
        b1 { start := 0#usize, «end» := i } h_i_le h_i_le_N)
  -- s2.val = b1.val.slice 0 i.val = (b1.val.drop 0).take i.val.
  -- We need: s2.val.length = out.val.length, and for k < out.val.length, s2.val[k]! = b1.val[k]!.
  have h_s2_len' : s2.val.length = out.val.length := by
    rw [h_s2_len]
    show i.val - 0 = out.val.length
    omega
  have h_s2_bytes : ∀ k : Nat, k < out.val.length → s2.val[k]! = b1.val[k]! := by
    intro k hk
    rw [h_s2_val]
    -- `b1.val.slice 0 i.val = (b1.val.drop 0).take i.val = b1.val.take i.val`.
    show (List.slice ((0#usize : Std.Usize).val) i.val b1.val)[k]! = _
    have h_zero : ((0#usize : Std.Usize).val : Nat) = 0 := rfl
    rw [h_zero]
    unfold List.slice
    rw [List.drop_zero]
    have hk_i : k < i.val := by rw [h_i_val]; exact hk
    exact List.getElem!_take_of_lt _ k _ hk_i
  -- Step 5: discharge `copy_from_slice out s2`. Length check: out.val.length = s2.val.length.
  have h_copy : CoreModels.core.slice.Slice.copy_from_slice
        CoreModels.core.U8.Insts.CoreMarkerCopy out s2 = .ok s2 := by
    unfold CoreModels.core.slice.Slice.copy_from_slice
    have h_len_eq : Std.Slice.len out = Std.Slice.len s2 := by
      apply Std.UScalar.eq_of_val_eq
      simp [Std.Slice.len, h_s2_len']
    simp [h_len_eq]
  -- Wrapper-identity: `Slice.Insts.CoreOpsIndexIndex inst = inst`.
  have h_wrap_eq :
      CoreModels.core.Slice.Insts.CoreOpsIndexIndex
        (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
      = CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8 := by
    unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndex
    rfl
  -- Step 6: assemble impl-side equality.
  have h_impl_eq :
      keccak.squeeze_last RATE s out = .ok s2 := by
    unfold keccak.squeeze_last
    rw [h_s1_eq]; simp only [bind_tc_ok]
    rw [h_classify]; simp only [bind_tc_ok]
    rw [h_b1_eq]; simp only [bind_tc_ok]
    rw [h_len]; simp only [bind_tc_ok]
    rw [h_wrap_eq]
    rw [h_s2_eq]; simp only [bind_tc_ok]
    exact h_copy
  -- Step 7: build the per-byte post.
  -- For k < out.val.length ≤ RATE.val, s2.val[k]! = b1.val[k]! = the toLEBytes-of-lift formula on s1.
  -- And `Foundation.lift s1 = s_spec` where keccak_f (lift s) = .ok s_spec.
  refine triple_of_ok_sb (v := s2) h_impl_eq ?_
  refine ⟨h_s2_len', Foundation.lift s1, h_s1_spec, ?_⟩
  intro k hk
  rw [h_s2_bytes k hk]
  have hk_RATE : k < RATE.val := lt_of_lt_of_le hk h_out_le_RATE
  exact h_b1_bytes k hk_RATE

/-! ### Triple 4: `keccak.squeeze_first_and_last`. -/

/-- `keccak.squeeze_first_and_last RATE s out` — no permutation, partial
    output via `store_block_full` + copy first `out.length` bytes.

    Post: every byte `k < out.val.length` matches the `toLEBytes` of
    `lift s` (no permutation applied). -/
@[spec]
theorem keccak.squeeze_first_and_last_spec
    (RATE : Std.Usize) (s : state.KeccakState) (out : Slice Std.U8)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_bnd : RATE.val ≤ 200)
    (h_out_le_RATE : out.val.length ≤ RATE.val) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.squeeze_first_and_last RATE s out
    ⦃ ⇓ r => ⌜
        r.val.length = out.val.length
        ∧ ∀ k : Nat, k < out.val.length →
            r.val[k]! = ⟨(BitVec.toLEBytes
              ((Foundation.lift s).val[k / 8]!).bv)[k % 8]!⟩
    ⌝ ⦄ := by
  -- The 200-byte buffer (all zeros).
  set buf : Std.Array Std.U8 200#usize := Std.Array.repeat 200#usize 0#u8 with hbuf
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify buf = .ok buf := rfl
  -- Step 1: discharge `store_block_full` on `s`.
  obtain ⟨b1, h_b1_eq, h_b1_len, h_b1_bytes⟩ :=
    triple_exists_ok_sb
      (state.KeccakState.store_block_full_spec RATE s buf
        h_RATE_mod h_RATE_bnd)
  -- Step 2: discharge `Slice.len out`.
  have h_len : CoreModels.core.slice.Slice.len out = .ok (Std.Slice.len out) := by
    unfold CoreModels.core.slice.Slice.len; rfl
  set i := Std.Slice.len out
  have h_i_val : i.val = out.val.length := by
    simp [i, Std.Slice.len]
  -- Step 3: index `b1` by `[0, i)`.
  have h_i_le : (0#usize : Std.Usize).val ≤ i.val := by
    show 0 ≤ i.val; omega
  have h_i_le_N : i.val ≤ (200#usize : Std.Usize).val := by
    rw [h_i_val]
    show out.val.length ≤ 200
    omega
  obtain ⟨s2, h_s2_eq, h_s2_val, h_s2_len⟩ :=
    triple_exists_ok_sb
      (core_models_Array_Insts_index_RangeUsize_spec
        b1 { start := 0#usize, «end» := i } h_i_le h_i_le_N)
  have h_s2_len' : s2.val.length = out.val.length := by
    rw [h_s2_len]
    show i.val - 0 = out.val.length
    omega
  have h_s2_bytes : ∀ k : Nat, k < out.val.length → s2.val[k]! = b1.val[k]! := by
    intro k hk
    rw [h_s2_val]
    show (List.slice ((0#usize : Std.Usize).val) i.val b1.val)[k]! = _
    have h_zero : ((0#usize : Std.Usize).val : Nat) = 0 := rfl
    rw [h_zero]
    unfold List.slice
    rw [List.drop_zero]
    have hk_i : k < i.val := by rw [h_i_val]; exact hk
    exact List.getElem!_take_of_lt _ k _ hk_i
  -- Step 4: discharge `copy_from_slice out s2`.
  have h_copy : CoreModels.core.slice.Slice.copy_from_slice
        CoreModels.core.U8.Insts.CoreMarkerCopy out s2 = .ok s2 := by
    unfold CoreModels.core.slice.Slice.copy_from_slice
    have h_len_eq : Std.Slice.len out = Std.Slice.len s2 := by
      apply Std.UScalar.eq_of_val_eq
      simp [Std.Slice.len, h_s2_len']
    simp [h_len_eq]
  -- Wrapper-identity: `Slice.Insts.CoreOpsIndexIndex inst = inst`.
  have h_wrap_eq :
      CoreModels.core.Slice.Insts.CoreOpsIndexIndex
        (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
      = CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8 := by
    unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndex
    rfl
  -- Step 5: assemble impl-side equality.
  have h_impl_eq :
      keccak.squeeze_first_and_last RATE s out = .ok s2 := by
    unfold keccak.squeeze_first_and_last
    -- Normalize the inner `have a := Array.repeat ...` binder to `buf`.
    show (do
        let b ← libcrux_secrets.traits.Classify.Blanket.classify buf
        let b1 ← state.KeccakState.store_block_full RATE s b
        let i ← CoreModels.core.slice.Slice.len out
        let s1 ← CoreModels.core.Array.Insts.CoreOpsIndexIndex.index
                  (CoreModels.core.Slice.Insts.CoreOpsIndexIndex
                    (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                      Std.U8)) b1 { start := 0#usize, «end» := i }
        CoreModels.core.slice.Slice.copy_from_slice
          CoreModels.core.U8.Insts.CoreMarkerCopy out s1) = .ok s2
    rw [h_classify]; simp only [bind_tc_ok]
    rw [h_b1_eq]; simp only [bind_tc_ok]
    rw [h_len]; simp only [bind_tc_ok]
    rw [h_wrap_eq]
    rw [h_s2_eq]; simp only [bind_tc_ok]
    exact h_copy
  -- Step 6: build the per-byte post.
  refine triple_of_ok_sb (v := s2) h_impl_eq ?_
  refine ⟨h_s2_len', ?_⟩
  intro k hk
  rw [h_s2_bytes k hk]
  have hk_RATE : k < RATE.val := lt_of_lt_of_le hk h_out_le_RATE
  exact h_b1_bytes k hk_RATE

end libcrux_iot_sha3.Sponge
