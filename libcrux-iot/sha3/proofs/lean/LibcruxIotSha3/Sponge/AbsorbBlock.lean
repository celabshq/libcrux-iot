/-
  # `keccak.absorb_block` ↔ `sponge.absorb_block`

  This file hosts the single top-level `@[spec]` Triple bridging the
  impl's `keccak.absorb_block` to the sponge spec's `sponge.absorb_block`.

  ## Composition

  Impl side (`Extraction/Funs.lean:4306`):
  ```
  def keccak.absorb_block RATE s blocks start := do
    let s1 ← state.KeccakState.load_block RATE s blocks start
    keccak.keccakf1600 s1
  ```

  Spec side (`HacspecSha3/Extraction/Funs.lean:1157`):
  ```
  def sponge.absorb_block state block rate := do
    let state1 ← sponge.xor_block_into_state state block rate
    keccak_f.keccak_f state1
  ```

  ## Post

  The Triple carries the full textbook post: termination,
  `r.i.val = 0`, and the spec-side equation
  `sponge.absorb_block (lift s) <block> RATE = .ok (lift r)`
  where `<block> := block_of_blocks blocks start RATE _` is the
  rate-window slice of `blocks`.

  Bridge infrastructure:

    - `fromLEBytes_8_split_4_4`         — pure BV identity (bv_decide).
    - `padded4_eq_explicit` /
      `padded8_eq_explicit`             — list-shape: padded-window of
                                          4/8 bytes equals explicit
                                          getElem!-indexed byte list.
    - `block_take{4,8}_eq_blocks_take{4,8}`
                                        — `block.val = blocks.slice ...`
                                          ⇒ inner-window readouts match.
    - `UScalar_bv_of_U{32,64}_from_le_bytes_eq`
                                        — `Subtype.ext`-based reduction
                                          closing the `BitVec.cast` layer.
    - `load_block_to_xor_block_bridge`  — combines the above into the
                                          per-cell U64-equality
                                          connecting `load_block_spec`'s
                                          `Lane2U32_from_4byte_LE_pairs`
                                          BV form to
                                          `xor_block_value_at`'s
                                          `U64.from_le_bytes ∘ list_8_at`
                                          form.

  Composition (`keccak.absorb_block_spec`):

    1. `state.KeccakState.load_block_spec` (Bytes.lean) — yields impl
       `s1` with `s1.i = s.i` and per-cell BV-equation.
    2. `keccakf1600_seal_spec` (Opaque.lean) — yields impl `r` with
       `keccak_f.keccak_f (lift s1) = .ok (lift r)` and `r.i.val = 0`.
    3. `sponge_xor_block_into_state_spec` (XorBlockSpec.lean) — yields
       spec `s_spec_1` with per-cell `xor_block_value_at` equation.
    4. **Bridge**: `s_spec_1 = lift s1` by per-cell BV-equality
       (List.ext_getElem + UScalar.eq_of_val_eq + the per-cell bridge).
    5. Compose: `sponge.absorb_block (lift s) block RATE`
                = `keccak_f.keccak_f s_spec_1`
                = `keccak_f.keccak_f (lift s1)`
                = `.ok (lift r)`.
-/
import LibcruxIotSha3.Sponge.Bytes

open Aeneas Aeneas.Std Result Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

open libcrux_iot_sha3.Foundation

-- Defensive seal re-issue: no proof in this file may unfold either side
-- of Bridge 1.
set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ## Bridge infrastructure — `load_block` ↔ `xor_block_into_state` per-cell.

The two characterizations of the per-cell U64 value (after XOR) use
different bit-vector shapes:

* `load_block_spec` (in `Sponge/Bytes.lean`) gives, at impl-flat-index
  `5*(k%5) + k/5` for `k < 25`, the BV
  `(zeroExtend 64 hi.bv) <<< 32 ||| zeroExtend 64 lo.bv` where `lo` and
  `hi` are the two halves of `Lane2U32_from_4byte_LE_pairs blocks start b`.
* `sponge_xor_block_into_state_spec` (in `Sponge/XorBlockSpec.lean`) gives,
  at cell `k`, `xor_block_value_at state block rate k` which uses
  `U64.from_le_bytes (list_8_at block.val (8*b))`.

Both BVs are the same 8 LE-loaded bytes — bridge lemma:
`load_block_to_xor_block_bridge` below. -/

/-- Pure BV identity: splitting an 8-byte LE-load into hi/lo 4-byte halves.
    Closed by `bv_decide` once `BitVec.fromLEBytes` is unfolded. -/
theorem fromLEBytes_8_split_4_4
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    BitVec.fromLEBytes [b0, b1, b2, b3, b4, b5, b6, b7]
      = ((BitVec.fromLEBytes [b4, b5, b6, b7]).zeroExtend 64) <<< 32
          ||| (BitVec.fromLEBytes [b0, b1, b2, b3]).zeroExtend 64 := by
  simp only [BitVec.fromLEBytes, List.length_cons, List.length_nil]
  bv_decide

/-- List-shape: under `n + 4 ≤ L.length`, the padded 4-byte window
    `((L.drop n).take 4) ++ replicate ...` reduces to the explicit
    `getElem!`-indexed byte list. -/
private theorem padded4_eq_explicit (L : List Std.U8) (n : Nat) (h : n + 4 ≤ L.length) :
    (((L.drop n).take 4 ++ List.replicate (4 - ((L.drop n).take 4).length) (0#u8)) : List Std.U8)
      = [L[n]!, L[n+1]!, L[n+2]!, L[n+3]!] := by
  have hlen : ((L.drop n).take 4).length = 4 := by
    rw [List.length_take, List.length_drop]; omega
  rw [hlen, show (4 - 4 : Nat) = 0 from rfl, List.replicate_zero, List.append_nil]
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop]; omega
  intro i hi1 _
  rw [show ((L.drop n).take 4).length = 4 from hlen] at hi1
  rw [List.getElem_take, List.getElem_drop]
  have hidx : n + i < L.length := by omega
  rw [show L[n + i] = L[n + i]! from (getElem!_pos _ (n + i) hidx).symm]
  match i, hi1 with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl

/-- List-shape: under `n + 8 ≤ L.length`, the padded 8-byte window
    `((L.drop n).take 8) ++ replicate ...` reduces to the explicit
    `getElem!`-indexed byte list. -/
private theorem padded8_eq_explicit (L : List Std.U8) (n : Nat) (h : n + 8 ≤ L.length) :
    (((L.drop n).take 8 ++ List.replicate (8 - ((L.drop n).take 8).length) (0#u8)) : List Std.U8)
      = [L[n]!, L[n+1]!, L[n+2]!, L[n+3]!, L[n+4]!, L[n+5]!, L[n+6]!, L[n+7]!] := by
  have hlen : ((L.drop n).take 8).length = 8 := by
    rw [List.length_take, List.length_drop]; omega
  rw [hlen, show (8 - 8 : Nat) = 0 from rfl, List.replicate_zero, List.append_nil]
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop]; omega
  intro i hi1 _
  rw [show ((L.drop n).take 8).length = 8 from hlen] at hi1
  rw [List.getElem_take, List.getElem_drop]
  have hidx : n + i < L.length := by omega
  rw [show L[n + i] = L[n + i]! from (getElem!_pos _ (n + i) hidx).symm]
  match i, hi1 with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl
  | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl

/-- Inner-window: if `block.val` is the slice `blocks.slice start (start+RATE)`,
    then the 8-byte readout of `block` at offset `8*b` equals the 8-byte
    readout of `blocks` at offset `start + 8*b`. Used in
    `load_block_to_xor_block_bridge`. -/
private theorem block_take8_eq_blocks_take8
    (blocks : Slice Std.U8) (start RATE : Std.Usize) (b : Nat) (block : Slice Std.U8)
    (h_block_val : block.val = blocks.val.slice start.val (start.val + RATE.val))
    (h_8b : 8 * b + 8 ≤ RATE.val) :
    (block.val.drop (8 * b)).take 8 = (blocks.val.drop (start.val + 8 * b)).take 8 := by
  rw [h_block_val]; unfold List.slice
  rw [show start.val + RATE.val - start.val = RATE.val from by omega]
  rw [List.drop_take, List.drop_drop, List.take_take]; congr 1; omega

/-- Inner-window: 4-byte version of `block_take8_eq_blocks_take8`. -/
private theorem block_take4_eq_blocks_take4
    (blocks : Slice Std.U8) (start RATE : Std.Usize) (n : Nat) (block : Slice Std.U8)
    (h_block_val : block.val = blocks.val.slice start.val (start.val + RATE.val))
    (h : n + 4 ≤ RATE.val) :
    (block.val.drop n).take 4 = (blocks.val.drop (start.val + n)).take 4 := by
  rw [h_block_val]; unfold List.slice
  rw [show start.val + RATE.val - start.val = RATE.val from by omega]
  rw [List.drop_take, List.drop_drop, List.take_take]; congr 1; omega

/-- `(Std.core.num.U64.from_le_bytes a).bv = BitVec.fromLEBytes [b0.bv, ..., b7.bv]`
    when `a.val` is the explicit 8-byte list. Closes the `BitVec.cast` layer
    via the fact that `8 * 8 = 64` reduces definitionally, going via
    `Subtype.ext` to avoid a motive-not-type-correct rewrite. -/
private theorem UScalar_bv_of_U64_from_le_bytes_eq
    (a : Std.Array Std.U8 8#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8)
    (h_a_val : a.val = [b0, b1, b2, b3, b4, b5, b6, b7]) :
    (Std.core.num.U64.from_le_bytes a).bv =
      BitVec.fromLEBytes
        [b0.bv, b1.bv, b2.bv, b3.bv, b4.bv, b5.bv, b6.bv, b7.bv] := by
  -- Pull the equality into a `Subtype.ext`-style equality on the whole array
  -- (the length proof becomes trivial under `h_a_val`).
  have h_arr :
      a = (⟨[b0, b1, b2, b3, b4, b5, b6, b7], rfl⟩ : Std.Array Std.U8 8#usize) :=
    Subtype.ext h_a_val
  rw [h_arr]
  -- Now both sides have a concrete list, so the `.cast` is trivially `id`.
  show ((BitVec.fromLEBytes
            (List.map Std.U8.bv [b0, b1, b2, b3, b4, b5, b6, b7])).cast (by simp))
       = _
  simp only [List.map_cons, List.map_nil]
  rfl

/-- `(Std.core.num.U32.from_le_bytes a).bv = BitVec.fromLEBytes [b0.bv, ..., b3.bv]`
    when `a.val` is the explicit 4-byte list. -/
private theorem UScalar_bv_of_U32_from_le_bytes_eq
    (a : Std.Array Std.U8 4#usize)
    (b0 b1 b2 b3 : Std.U8)
    (h_a_val : a.val = [b0, b1, b2, b3]) :
    (Std.core.num.U32.from_le_bytes a).bv =
      BitVec.fromLEBytes [b0.bv, b1.bv, b2.bv, b3.bv] := by
  have h_arr :
      a = (⟨[b0, b1, b2, b3], rfl⟩ : Std.Array Std.U8 4#usize) :=
    Subtype.ext h_a_val
  rw [h_arr]
  show ((BitVec.fromLEBytes
            (List.map Std.U8.bv [b0, b1, b2, b3])).cast (by simp)) = _
  simp only [List.map_cons, List.map_nil]
  rfl

/-- **The bridge:** the per-cell U64 value produced by `load_block_spec`'s
    BV-interleave form equals the per-cell U64 value used in
    `xor_block_value_at`'s `U64.from_le_bytes` form, for the same 8 LE bytes
    read out of `blocks`. -/
private theorem load_block_to_xor_block_bridge
    (blocks : Slice Std.U8) (start RATE : Std.Usize) (b : Nat)
    (block : Slice Std.U8)
    (h_block_val : block.val = blocks.val.slice start.val (start.val + RATE.val))
    (h_blk : start.val + RATE.val ≤ blocks.val.length)
    (h_8b : 8 * b + 8 ≤ RATE.val) :
    ((BitVec.zeroExtend 64
        ((Lane2U32_from_4byte_LE_pairs blocks start b).val[1]!.bv)) <<< 32)
      ||| BitVec.zeroExtend 64
            ((Lane2U32_from_4byte_LE_pairs blocks start b).val[0]!.bv)
      = (Std.core.num.U64.from_le_bytes (list_8_at block.val (8 * b))).bv := by
  -- Names for the 8 bytes read out of `blocks` at offset `start.val + 8b`.
  set p := start.val + 8 * b with hp_def
  -- `blocks.val.length` is large enough for the 8-byte window.
  have h_p_8 : p + 8 ≤ blocks.val.length := by rw [hp_def]; omega
  -- Loop0's two 4-byte halves: at offsets `p` and `p + 4`.
  have h_p_4 : p + 4 ≤ blocks.val.length := by omega
  have h_p4_4 : p + 4 + 4 ≤ blocks.val.length := by omega
  -- ## Unfold `Lane2U32_from_4byte_LE_pairs` and reduce its `.val`s.
  have h_lo_val :
      (Lane2U32_from_4byte_LE_pairs blocks start b).val[0]! =
        Std.core.num.U32.from_le_bytes
          ⟨((blocks.val.drop p).take 4) ++
              List.replicate (4 - ((blocks.val.drop p).take 4).length) (0#u8),
           by
             have : ((blocks.val.drop p).take 4).length ≤ 4 := by
               simp [List.length_take]
             simp [List.length_append, List.length_replicate]⟩ := by
    unfold Lane2U32_from_4byte_LE_pairs
    rfl
  have h_hi_val :
      (Lane2U32_from_4byte_LE_pairs blocks start b).val[1]! =
        Std.core.num.U32.from_le_bytes
          ⟨((blocks.val.drop (p + 4)).take 4) ++
              List.replicate (4 - ((blocks.val.drop (p + 4)).take 4).length) (0#u8),
           by
             have : ((blocks.val.drop (p + 4)).take 4).length ≤ 4 := by
               simp [List.length_take]
             simp [List.length_append, List.length_replicate]⟩ := by
    unfold Lane2U32_from_4byte_LE_pairs
    rfl
  -- ## Reduce the U32 byte-lists via `padded4_eq_explicit`.
  have h_lo_bytes :
      ((blocks.val.drop p).take 4) ++
        List.replicate (4 - ((blocks.val.drop p).take 4).length) (0#u8)
      = [blocks.val[p]!, blocks.val[p+1]!, blocks.val[p+2]!, blocks.val[p+3]!] :=
    padded4_eq_explicit blocks.val p h_p_4
  have h_hi_bytes :
      ((blocks.val.drop (p+4)).take 4) ++
        List.replicate (4 - ((blocks.val.drop (p+4)).take 4).length) (0#u8)
      = [blocks.val[p+4]!, blocks.val[p+5]!, blocks.val[p+6]!, blocks.val[p+7]!] := by
    have h_eq := padded4_eq_explicit blocks.val (p + 4) h_p4_4
    -- Indices `(p+4)+i` simplify to `p + (4+i)`.
    simpa [show p + 4 + 1 = p + 5 from by omega,
           show p + 4 + 2 = p + 6 from by omega,
           show p + 4 + 3 = p + 7 from by omega] using h_eq
  -- ## Build the `bv` rewrite for each U32.
  have h_lo_bv :
      ((Lane2U32_from_4byte_LE_pairs blocks start b).val[0]!).bv
        = BitVec.fromLEBytes
            [blocks.val[p]!.bv, blocks.val[p+1]!.bv,
             blocks.val[p+2]!.bv, blocks.val[p+3]!.bv] := by
    rw [h_lo_val]
    exact UScalar_bv_of_U32_from_le_bytes_eq _ _ _ _ _ h_lo_bytes
  have h_hi_bv :
      ((Lane2U32_from_4byte_LE_pairs blocks start b).val[1]!).bv
        = BitVec.fromLEBytes
            [blocks.val[p+4]!.bv, blocks.val[p+5]!.bv,
             blocks.val[p+6]!.bv, blocks.val[p+7]!.bv] := by
    rw [h_hi_val]
    exact UScalar_bv_of_U32_from_le_bytes_eq _ _ _ _ _ h_hi_bytes
  -- ## Reduce `list_8_at block.val (8*b)`.
  have h_block_take8_blocks :
      (block.val.drop (8 * b)).take 8 = (blocks.val.drop p).take 8 := by
    rw [hp_def]
    exact block_take8_eq_blocks_take8 blocks start RATE b block h_block_val h_8b
  -- `list_8_at block.val (8*b)` unfolds to padded 8-byte list, which after
  -- the inner-window equality equals the explicit 8-byte list at `blocks`.
  have h_l8_val :
      (list_8_at block.val (8 * b)).val =
        [blocks.val[p]!, blocks.val[p+1]!, blocks.val[p+2]!, blocks.val[p+3]!,
         blocks.val[p+4]!, blocks.val[p+5]!, blocks.val[p+6]!, blocks.val[p+7]!] := by
    unfold list_8_at
    show ((block.val.drop (8 * b)).take 8) ++
         List.replicate (8 - ((block.val.drop (8 * b)).take 8).length) (0#u8) = _
    rw [h_block_take8_blocks]
    exact padded8_eq_explicit blocks.val p h_p_8
  -- ## Apply `UScalar_bv_of_U64_from_le_bytes_eq`.
  have h_u64_bv :
      (Std.core.num.U64.from_le_bytes (list_8_at block.val (8 * b))).bv
        = BitVec.fromLEBytes
            [blocks.val[p]!.bv, blocks.val[p+1]!.bv,
             blocks.val[p+2]!.bv, blocks.val[p+3]!.bv,
             blocks.val[p+4]!.bv, blocks.val[p+5]!.bv,
             blocks.val[p+6]!.bv, blocks.val[p+7]!.bv] :=
    UScalar_bv_of_U64_from_le_bytes_eq _ _ _ _ _ _ _ _ _ h_l8_val
  -- ## Close: LHS = the 4+4 split version, RHS = the 8-byte version. Use
  -- `fromLEBytes_8_split_4_4` to bridge.
  rw [h_lo_bv, h_hi_bv, h_u64_bv]
  exact (fromLEBytes_8_split_4_4 _ _ _ _ _ _ _ _).symm

/-! ## `keccak.absorb_block` ↔ `sponge.absorb_block`. -/

/-- Local triple-of-ok helper. -/
private theorem triple_of_ok_ab {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PredTrans.apply, hp]

/-- Local existence extractor: a Triple yields `∃ v, x = .ok v ∧ P v`. -/
private theorem triple_exists_ok_ab {α : Type} {x : Result α}
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

/-- The spec-side block window: a `Slice U8` whose `.val` is
    `blocks.val.slice start (start+RATE)`. This is the `<block>` argument
    to `sponge.absorb_block` in the textbook post of
    `keccak.absorb_block_spec`. -/
def block_of_blocks
    (blocks : Slice Std.U8) (start RATE : Std.Usize)
    (h_blk : start.val + RATE.val ≤ blocks.val.length) :
    Slice Std.U8 :=
  ⟨blocks.val.slice start.val (start.val + RATE.val), by
    -- `blocks.val.slice a b ` is `(blocks.val.drop a).take (b - a)`, length ≤ blocks.val.length.
    have h_len : (blocks.val.slice start.val (start.val + RATE.val)).length ≤ blocks.val.length := by
      unfold List.slice
      rw [List.length_take, List.length_drop]; omega
    have := blocks.property; omega⟩

/-- `keccak.absorb_block RATE s blocks start` — XOR a `RATE`-byte block
    from `blocks` (at offset `start`) into the state, then apply the
    Keccak-f permutation.

    Post: termination, `r.i.val = 0`, and the spec-side equation

        sponge.absorb_block (lift s) (block_of_blocks blocks start RATE _) RATE
          = .ok (lift r).

    The `r.i.val = 0` clause is what the downstream loop chain consumes;
    the spec equation feeds `absorb_rec` accumulation. -/
@[spec]
theorem keccak.absorb_block_spec
    (RATE : Std.Usize) (s : state.KeccakState) (blocks : Slice Std.U8)
    (start : Std.Usize)
    (h_i : s.i.val = 0)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_bnd : RATE.val ≤ 200)
    (h_blk : start.val + RATE.val ≤ blocks.val.length)
    (h_off : start.val + RATE.val ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.absorb_block RATE s blocks start
    ⦃ ⇓ r => ⌜ r.i.val = 0
              ∧ sponge.absorb_block (Foundation.lift s)
                    (block_of_blocks blocks start RATE h_blk) RATE
                  = .ok (Foundation.lift r) ⌝ ⦄ := by
  -- Step 1: discharge `load_block` via its @[spec] in Bytes.lean.
  obtain ⟨s1, h_s1_eq, h_s1_post⟩ :=
    triple_exists_ok_ab
      (state.KeccakState.load_block_spec RATE s blocks start
        h_RATE_mod h_RATE_bnd h_blk h_off)
  obtain ⟨h_s1_i, h_s1_lanes⟩ := h_s1_post
  -- Step 2: discharge `keccakf1600` via its @[spec] in Opaque.lean.
  -- Need: s1.i.val = 0. We have s1.i = s.i, and s.i.val = 0 via h_i.
  have h_s1_i_val : s1.i.val = 0 := by rw [h_s1_i]; exact h_i
  obtain ⟨r, h_r_eq, h_r_post⟩ :=
    triple_exists_ok_ab (keccakf1600_seal_spec s1 h_s1_i_val)
  obtain ⟨h_r_spec, h_r_i⟩ := h_r_post
  -- Step 3a: assemble impl-side equality `keccak.absorb_block ... = .ok r`.
  have h_impl_eq : keccak.absorb_block RATE s blocks start = .ok r := by
    unfold keccak.absorb_block
    rw [h_s1_eq]; simp only [bind_tc_ok]
    exact h_r_eq
  -- Step 4: spec-side composition.
  -- Let `block := block_of_blocks blocks start RATE h_blk`. We need:
  --   sponge.absorb_block (lift s) block RATE = .ok (lift r)
  -- via:
  --   (a) `sponge.xor_block_into_state (lift s) block RATE = .ok (lift s1)`
  --       — from `sponge_xor_block_into_state_spec` + per-cell rewrite
  --         using `load_block_to_xor_block_bridge`.
  --   (b) `keccak_f.keccak_f (lift s1) = .ok (lift r)` — from
  --       `keccakf1600_seal_spec`.
  let block := block_of_blocks blocks start RATE h_blk
  -- block.val = blocks.val.slice start.val (start.val + RATE.val) by defn.
  have h_block_val : block.val = blocks.val.slice start.val (start.val + RATE.val) := rfl
  have h_block_len : block.val.length = RATE.val := by
    rw [h_block_val]; unfold List.slice
    rw [List.length_take, List.length_drop]; omega
  -- Apply `sponge_xor_block_into_state_spec`.
  obtain ⟨s_spec_1, h_xbs_eq, h_xbs_post⟩ :=
    triple_exists_ok_ab
      (sponge_xor_block_into_state_spec RATE (Foundation.lift s) block
        h_RATE_bnd h_RATE_mod h_block_len)
  -- We claim `s_spec_1 = Foundation.lift s1` by per-cell equality.
  have h_spec_lift_s1 : s_spec_1 = Foundation.lift s1 := by
    -- Both are `Array U64 25#usize = { val : List U64 // val.length = 25 }`.
    -- Reduce to list equality, then per-cell.
    apply Subtype.ext
    apply List.ext_getElem
    · -- Lengths.
      have h1 : s_spec_1.val.length = 25 := s_spec_1.property
      have h2 : (Foundation.lift s1).val.length = 25 := (Foundation.lift s1).property
      omega
    intro k hk_lhs _
    have hk_25 : k < 25 := by
      have hlen : s_spec_1.val.length = 25 := s_spec_1.property
      omega
    -- Replace `[k]` with `[k]!` using `getElem!_pos`.
    have h_len1 : s_spec_1.val.length = 25 := s_spec_1.property
    have h_len2 : (Foundation.lift s1).val.length = 25 := (Foundation.lift s1).property
    rw [show s_spec_1.val[k] = s_spec_1.val[k]! from
          (getElem!_pos s_spec_1.val k (by rw [h_len1]; exact hk_25)).symm]
    rw [show (Foundation.lift s1).val[k] = (Foundation.lift s1).val[k]! from
          (getElem!_pos (Foundation.lift s1).val k (by rw [h_len2]; exact hk_25)).symm]
    -- Use h_xbs_post and h_s1_lanes.
    rw [h_xbs_post k hk_25]
    -- Compare with h_s1_lanes k hk_25.
    have h_lane := h_s1_lanes k hk_25
    -- Two `U64`s: equal iff their `.bv` are equal (single-field structure).
    apply Std.UScalar.eq_of_val_eq
    -- The goal is now on `.bv.toNat`. Apply `BitVec.toNat`-injectivity by
    -- reducing to a `.bv` equality.
    show (xor_block_value_at (Foundation.lift s) block RATE k).bv.toNat
         = ((Foundation.lift s1).val[k]!).bv.toNat
    -- Show the `.bv`-equality first, then transport via `congrArg`.
    suffices h_bv : (xor_block_value_at (Foundation.lift s) block RATE k).bv
                      = ((Foundation.lift s1).val[k]!).bv by
      rw [h_bv]
    -- Now we have a clean BitVec 64 = BitVec UScalarTy.U64.numBits goal —
    -- but `UScalarTy.U64.numBits` reduces to `64` definitionally.
    rw [h_lane]
    -- Unfold `xor_block_value_at`. Under the new spec layout, the byte
    -- block index equals the spec index `k` (no transpose).
    unfold xor_block_value_at
    by_cases h_k_lt : k < RATE.val / 8
    · -- Active cell: `k < RATE.val / 8`.
      rw [if_pos h_k_lt, if_pos h_k_lt]
      show (_ ^^^ _ : Std.U64).bv = _
      rw [Std.UScalar.bv_xor]
      -- Reduce `8 * k + 8 ≤ RATE.val` from `h_k_lt : k < RATE.val / 8`.
      have h_RATE_div_mul : 8 * (RATE.val / 8) ≤ RATE.val := by
        have h_decomp : RATE.val = 8 * (RATE.val / 8) + RATE.val % 8 :=
          (Nat.div_add_mod _ _).symm
        omega
      have h_8k : 8 * k + 8 ≤ RATE.val := by
        have : k + 1 ≤ RATE.val / 8 := h_k_lt
        have h_mul : 8 * (k + 1) ≤ 8 * (RATE.val / 8) :=
          Nat.mul_le_mul_left 8 this
        omega
      have h_bridge := load_block_to_xor_block_bridge
        blocks start RATE k block h_block_val h_blk h_8k
      rw [h_bridge]
    · -- Inactive cell.
      rw [if_neg h_k_lt, if_neg h_k_lt]
  -- Step 5: substitute `s_spec_1 = lift s1` into the do-chain.
  -- Goal: ⦃True⦄ keccak.absorb_block ... ⦃⇓r => r.i.val = 0 ∧ sponge.absorb_block (lift s) block RATE = .ok (lift r)⦄
  have h_spec_compose :
      sponge.absorb_block (Foundation.lift s) block RATE = .ok (Foundation.lift r) := by
    unfold sponge.absorb_block
    rw [h_xbs_eq]; simp only [bind_tc_ok]
    rw [h_spec_lift_s1]
    exact h_r_spec
  apply triple_of_ok_ab (v := r) h_impl_eq ⟨h_r_i, h_spec_compose⟩

end libcrux_iot_sha3.Sponge
