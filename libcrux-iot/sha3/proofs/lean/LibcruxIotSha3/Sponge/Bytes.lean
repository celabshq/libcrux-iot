/-
  # Byte ↔ Lane primitives (`load_block`, `store_block`,
  # `load_block_full`).

  Top-level `@[spec]` Triples bridging the impl's byte-loop
  loaders/stores to the sponge spec's byte ↔ lane view:

  - `state.KeccakState.load_block_spec`      — unwraps `load_block_2u32`,
    composes the two outer-loop Triples from `Sponge/LoopSpecs.lean`.
    Carries `⌜ r.i = s.i ⌝`.
  - `state.KeccakState.store_block_spec`     — unwraps `store_block_2u32`,
    composes the outer-loop Triple from `Sponge/LoopSpecs.lean` and
    preserves output-slice length.
  - `state.KeccakState.load_block_full_spec` — delegates to
    `load_block_spec` after `Array.to_slice` coercion.

  The BV-pure identity layer (`interleave_bv`, `deinterleave_bv`,
  `lift_lane_bv_xor`, `interleave_bv_lift_eq`,
  `deinterleave_bv_lift_eq`) lives in `Sponge/Interleave.lean`'s
  header section.
-/
import LibcruxIotSha3.Sponge.LoopSpecs
import LibcruxIotSha3.Sponge.XorBlockSpec

open Aeneas Aeneas.Std Result ControlFlow Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

open libcrux_iot_sha3.Foundation

-- Defensive seal re-issue: no proof in this file may unfold either side
-- of Bridge 1.
set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ## Top-level Triples for `load_block` / `store_block` /
       `load_block_full`. -/

/-- Local copy of `triple_of_ok_local`: an `.ok v` `Result` satisfies any
    Triple whose post `P r` holds at `v`. -/
private theorem triple_of_ok_bytes {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PredTrans.apply, hp]

/-- Local existence extractor: a Triple yields `∃ v, x = .ok v ∧ P v`. -/
private theorem triple_exists_ok_bytes {α : Type} {x : Result α}
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

/-! ### Pure-side reductions for the body of `state.load_block_2u32`.

We capture each step's `.ok`-equation as a small local lemma so the
final assembly is a straight `rw` chain. -/

/-- `CoreModels.core.slice.Slice.len v = .ok (Std.Slice.len v)`. -/
private theorem core_slice_len_eq_ok {T : Type} (v : Slice T) :
    CoreModels.core.slice.Slice.len v = .ok (Std.Slice.len v) := by
  unfold CoreModels.core.slice.Slice.len; rfl

/-- `RATE % 8#usize = .ok 0#usize` whenever `RATE.val % 8 = 0`. -/
private theorem rate_mod_8_eq_ok (RATE : Std.Usize) (h : RATE.val % 8 = 0) :
    (RATE % 8#usize : Result Std.Usize) = .ok 0#usize := by
  -- Use the bv-spec from Aeneas.
  have hnz : ((8#usize : Std.Usize).val : Nat) ≠ 0 := by decide
  -- `UScalar.rem` is `if y.val != 0 then ok ⟨BitVec.umod ...⟩ else fail`.
  show Std.UScalar.rem RATE 8#usize = _
  unfold Std.UScalar.rem
  have hne : ¬ ((8#usize : Std.Usize).val = 0) := hnz
  simp only [bne_iff_ne, ne_eq, hne, not_false_eq_true, ↓reduceIte]
  apply congrArg
  apply Std.UScalar.eq_of_val_eq
  show (BitVec.umod RATE.bv (8#usize : Std.Usize).bv).toNat = (0#usize : Std.Usize).val
  -- Reduce via val/bv toNat. `BitVec.umod x y = x % y` definitionally.
  show RATE.bv.toNat % ((8#usize : Std.Usize).bv).toNat = 0
  have h8 : ((8#usize : Std.Usize).bv).toNat = 8 := by decide
  rw [h8]
  exact h

/-- `lane.Lane2U32.zero = .ok ⟨[0#u32, 0#u32], _⟩`. -/
private theorem lane_zero_eq_ok :
    (lane.Lane2U32.zero : Result lane.Lane2U32) =
      .ok ⟨[0#u32, 0#u32], by decide⟩ := by
  unfold lane.Lane2U32.zero
         libcrux_secrets.traits.Classify.Blanket.classify
         lane.Lane2U32.from_ints
  rfl

/-- `RATE / 8#usize` succeeds and returns a value `i` with `i.val = RATE.val / 8`. -/
private theorem rate_div_8_ok (RATE : Std.Usize) :
    ∃ i : Std.Usize, (RATE / 8#usize : Result Std.Usize) = .ok i
      ∧ i.val = RATE.val / 8 := by
  have h := Std.UScalar.div_bv_spec RATE (y := 8#usize) (by decide)
  obtain ⟨i, hi_eq, hi_val, _⟩ := h
  refine ⟨i, hi_eq, ?_⟩
  rw [hi_val]
  show RATE.val / (8#usize : Std.Usize).val = RATE.val / 8
  have h8 : (8#usize : Std.Usize).val = 8 := by decide
  rw [h8]

/-! ### Helpers for textbook-form posts. -/

/-- Indexing `Foundation.lift s` at a `Fin 25` returns the lifted
    interleaved halves of `s.st[transpose_perm k]` (impl-side index after
    the spec↔impl transpose). -/
private theorem lift_getElem_bytes (s : state.KeccakState) (k : Fin 25) :
    (Foundation.lift s).val[k.val]! =
      (⟨lift_lane_bv ((s.st.val[(Foundation.transpose_perm k).val]!).val[0]!.bv)
                     ((s.st.val[(Foundation.transpose_perm k).val]!).val[1]!.bv)⟩
        : Std.U64) := by
  unfold Foundation.lift Foundation.lift_lane
  change (List.ofFn _)[k.val]! = _
  rw [getElem!_pos _ k.val (by simp), List.getElem_ofFn]

/-- Bytewise readout for `BitVec.toLEBytes` over 64-bit values: byte `i` is
    `BitVec.ofNat 8 ((bv.toNat >>> (8*i)) &&& 0xff)`. Stated at the
    BitVec level. -/
private theorem toLEBytes64_getElem!_eq_ofNat_shift_and
    (bv : BitVec 64) (i : Nat) (_hi : i < 8) :
    bv.toLEBytes[i]! = BitVec.ofNat 8 ((bv.toNat >>> (8 * i)) &&& 0xff) := by
  -- Each side is determined by its 8 bits (as Nats).
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 8
  · -- LHS bit j: use `BitVec.toLEBytes_getElem!_testBit`.
    -- RHS bit j: shift/and gives the (8i+j)-th bit of `bv.toNat`.
    have h_LHS_bit : (bv.toLEBytes[i]!).toNat.testBit j = bv.toNat.testBit (8 * i + j) := by
      have h := BitVec.toLEBytes_getElem!_testBit bv i j hj
      -- `h : Byte.testBit (toLEBytes[i]!) j = bv[8*i+j]!`
      -- `Byte.testBit b j = Nat.testBit b.toNat j` (by definition).
      -- `bv[8*i+j]! = bv.toNat.testBit (8*i+j)`.
      show Nat.testBit (bv.toLEBytes[i]!).toNat j = bv.toNat.testBit (8 * i + j)
      rw [show Nat.testBit (bv.toLEBytes[i]!).toNat j = Byte.testBit bv.toLEBytes[i]! j from rfl]
      rw [h, BitVec.getElem!_eq_testBit_toNat]
    rw [h_LHS_bit]
    -- RHS: `(BitVec.ofNat 8 ...).toNat = ... % 256`.
    simp only [BitVec.toNat_ofNat]
    have h_and_eq_mod : (bv.toNat >>> (8 * i)) &&& 0xff
                          = (bv.toNat >>> (8 * i)) % 256 := by
      show _ &&& 255 = _ % 256
      rw [show (255 : Nat) = 2^8 - 1 from by decide,
          show (256 : Nat) = 2^8 from by decide]
      exact Nat.and_two_pow_sub_one_eq_mod _ 8
    rw [h_and_eq_mod]
    rw [show (2^8 : Nat) = 256 from by decide]
    -- Goal: bv.toNat.testBit (8 * i + j) = (bv.toNat >>> (8 * i) % 256 % 256).testBit j
    have h_mm : (bv.toNat >>> (8 * i)) % 256 % 256 = (bv.toNat >>> (8 * i)) % 256 := by
      rw [Nat.mod_mod]
    rw [h_mm]
    rw [show (256 : Nat) = 2^8 from by decide]
    rw [Nat.testBit_mod_two_pow]
    simp only [decide_true, Bool.true_and, hj, Nat.testBit_shiftRight]
  · -- Bits j ≥ 8 are 0 on both sides.
    have hLHS_isLt : (bv.toLEBytes[i]!).toNat < 256 := by
      have := bv.toLEBytes[i]!.isLt; simpa using this
    have h_jj : 8 ≤ j := by omega
    have h_pow : (256 : Nat) = 2^8 := by decide
    have hRHS_isLt : (BitVec.ofNat 8 ((bv.toNat >>> (8 * i)) &&& 0xff)).toNat < 256 := by
      have := (BitVec.ofNat 8 ((bv.toNat >>> (8 * i)) &&& 0xff)).isLt
      have h_pow2 : (2 ^ 8 : Nat) = 256 := by decide
      omega
    have hLHS : (bv.toLEBytes[i]!).toNat.testBit j = false := by
      rw [Nat.testBit_eq_false_of_lt]
      calc (bv.toLEBytes[i]!).toNat < 256 := hLHS_isLt
        _ = 2 ^ 8 := h_pow
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) h_jj
    have hRHS : (BitVec.ofNat 8 ((bv.toNat >>> (8 * i)) &&& 0xff)).toNat.testBit j = false := by
      rw [Nat.testBit_eq_false_of_lt]
      calc (BitVec.ofNat 8 ((bv.toNat >>> (8 * i)) &&& 0xff)).toNat < 256 := hRHS_isLt
        _ = 2 ^ 8 := h_pow
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) h_jj
    rw [hLHS, hRHS]

/-- `store_block_byte_at s b` (the value the strong store-loop produces at
    byte position `b`) equals byte `b%8` of the LE-byte split of the spec-side
    `(Foundation.lift s).val[b/8]!`. Under the new spec layout, FIPS byte
    block `b/8` lives at spec position `b/8` directly (no transpose). -/
private theorem store_block_byte_at_eq_toLEBytes
    (s : state.KeccakState) (b : Nat) (hb : b / 8 < 25) :
    store_block_byte_at s b =
      ⟨(BitVec.toLEBytes
          ((Foundation.lift s).val[b / 8]!).bv)[b % 8]!⟩ := by
  -- Unfold store_block_byte_at; LHS is ⟨BitVec.ofNat 8 ((u64.bv.toNat >>> (8*(b%8))) &&& 0xff)⟩.
  unfold store_block_byte_at
  -- p < 25.
  have hp_lt : b / 8 < 25 := hb
  -- (Foundation.lift s).val[p]!.bv = lift_lane_bv (s.st[transpose_perm p]) ...
  have h_T : (Foundation.transpose_perm ⟨b / 8, hp_lt⟩).val
              = 5 * ((b / 8) % 5) + (b / 8) / 5 := rfl
  have h_lift : ((Foundation.lift s).val[b / 8]!).bv =
      lift_lane_bv
        ((s.st.val[5 * ((b / 8) % 5) + (b / 8) / 5]!).val[0]!).bv
        ((s.st.val[5 * ((b / 8) % 5) + (b / 8) / 5]!).val[1]!).bv := by
    rw [lift_getElem_bytes s ⟨_, hp_lt⟩, h_T]
  -- `lift_lane (s.st.val[p]!)).bv = lift_lane_bv ...` (by lift_lane def).
  have h_ll_bv :
      (Foundation.lift_lane (s.st.val[5 * ((b / 8) % 5) + (b / 8) / 5]!)).bv =
        lift_lane_bv
          ((s.st.val[5 * ((b / 8) % 5) + (b / 8) / 5]!).val[0]!).bv
          ((s.st.val[5 * ((b / 8) % 5) + (b / 8) / 5]!).val[1]!).bv := rfl
  have hb_mod : b % 8 < 8 := Nat.mod_lt _ (by decide)
  -- Both sides are `⟨BitVec 8⟩ = Std.U8`; reduce to the BitVec equality.
  apply Std.UScalar.eq_of_val_eq
  show (BitVec.ofNat 8 _).toNat = _
  -- Reduce the RHS via the toLEBytes lemma.
  have h_bytes := toLEBytes64_getElem!_eq_ofNat_shift_and
    ((Foundation.lift s).val[b / 8]!).bv
    (b % 8) hb_mod
  rw [h_bytes, h_lift]
  -- Both sides are now `BitVec.ofNat 8 ((lift_lane_bv _ _).toNat >>> (8*(b%8)) &&& 0xff)`.
  rfl

/-! ### Top-level Triples. -/

/-- `state.KeccakState.load_block RATE s blocks start` terminates with
    `.ok` whenever the standard sponge preconditions hold:
    `RATE.val ≤ 200`, `RATE.val % 8 = 0`, the byte window
    `[start, start+RATE)` fits inside `blocks`, and the offset arithmetic
    does not overflow.

    The two underlying loops walk `i ∈ [0, RATE/8) ⊆ [0, 25)` reading
    8-byte windows of `blocks` and updating the 25-cell `state_flat` then
    XORing into the impl's interleaved Keccak state. The body Triples
    are in `Sponge/LoopSpecs.lean`. -/
@[spec]
theorem state.KeccakState.load_block_spec
    (RATE : Std.Usize) (s : state.KeccakState) (blocks : Slice Std.U8)
    (start : Std.Usize)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_bnd : RATE.val ≤ 200)
    (h_blk  : start.val + RATE.val ≤ blocks.val.length)
    (h_off  : start.val + RATE.val ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄
    state.KeccakState.load_block RATE s blocks start
    ⦃ ⇓ r => ⌜
        r.i = s.i
        ∧ ∀ k : Nat, k < 25 →
            ((Foundation.lift r).val[k]!).bv =
              (if k < RATE.val / 8 then
                  ((Foundation.lift s).val[k]!).bv ^^^
                    (BitVec.zeroExtend 64
                        (((Lane2U32_from_4byte_LE_pairs blocks start k).val[1]!).bv) <<< 32
                     ||| BitVec.zeroExtend 64
                        (((Lane2U32_from_4byte_LE_pairs blocks start k).val[0]!).bv))
               else ((Foundation.lift s).val[k]!).bv)
    ⌝ ⦄ := by
  have h_blk_len : RATE.val ≤ blocks.val.length := by omega
  have h_RATE_div_le : RATE.val / 8 ≤ 25 := by omega
  have h_RATE_div_mul : 8 * (RATE.val / 8) = RATE.val := by
    have : RATE.val = 8 * (RATE.val / 8) + RATE.val % 8 :=
      (Nat.div_add_mod _ _).symm
    omega
  -- Compute the .ok values of each step in `state.load_block_2u32`.
  have h_len := core_slice_len_eq_ok blocks
  have h_RATE_le : RATE.val ≤ (Std.Slice.len blocks).val := by
    rw [Std.Slice.len_val]; exact h_blk_len
  have h_mod := rate_mod_8_eq_ok RATE h_RATE_mod
  have h_zero := lane_zero_eq_ok
  obtain ⟨i2, h_div_eq, h_i2_val⟩ := rate_div_8_ok RATE
  -- Bounds for loop0.
  have h_loop0_le : (0#usize : Std.Usize).val ≤ i2.val := by
    show 0 ≤ i2.val; omega
  have h_loop0_bnd : i2.val ≤ 25 := by rw [h_i2_val]; exact h_RATE_div_le
  have h_loop0_off : start.val + 8 * i2.val ≤ Std.Usize.max := by
    rw [h_i2_val]; omega
  have h_loop0_blk : start.val + 8 * i2.val ≤ blocks.val.length := by
    rw [h_i2_val]; omega
  let state_flat : Std.Array lane.Lane2U32 25#usize :=
    Std.Array.repeat 25#usize (⟨[0#u32, 0#u32], by decide⟩ : lane.Lane2U32)
  obtain ⟨state_flat1, h_loop0_eq, h_state_flat1⟩ :=
    triple_exists_ok_bytes
      (state.load_block_2u32_loop0_spec
        ⟨0#usize, i2⟩ blocks start state_flat
        h_loop0_le h_loop0_bnd h_loop0_off h_loop0_blk (by rfl))
  obtain ⟨r_final, h_loop1_eq, h_post⟩ :=
    triple_exists_ok_bytes
      (state.load_block_2u32_loop1_spec
        ⟨0#usize, i2⟩ state_flat1 s h_loop0_le h_loop0_bnd rfl)
  obtain ⟨h_r_i, h_post2⟩ := h_post
  obtain ⟨h_lanes, h_unchanged⟩ := h_post2
  -- Build the per-cell BV post. Under the new spec layout, spec index `k`
  -- maps to impl index `transpose_perm k = 5*(k%5) + k/5` (where the
  -- impl's loop0 stored byte block `k`).
  have h_per_cell : ∀ k : Nat, k < 25 →
      ((Foundation.lift r_final).val[k]!).bv =
        (if k < RATE.val / 8 then
            ((Foundation.lift s).val[k]!).bv ^^^
              (BitVec.zeroExtend 64
                  (((Lane2U32_from_4byte_LE_pairs blocks start k).val[1]!).bv) <<< 32
               ||| BitVec.zeroExtend 64
                  (((Lane2U32_from_4byte_LE_pairs blocks start k).val[0]!).bv))
         else ((Foundation.lift s).val[k]!).bv) := by
    intro k hk_25
    -- Apply lift_getElem_bytes at k. Under new lift, this reads impl
    -- position `transpose_perm k = 5*(k%5) + k/5`.
    rw [lift_getElem_bytes r_final ⟨k, hk_25⟩,
        lift_getElem_bytes s ⟨k, hk_25⟩]
    have h_T_val : (Foundation.transpose_perm ⟨k, hk_25⟩).val
                    = 5 * (k % 5) + k / 5 := rfl
    rw [h_T_val]
    show lift_lane_bv (r_final.st.val[5 * (k % 5) + k / 5]!.val[0]!.bv)
                      (r_final.st.val[5 * (k % 5) + k / 5]!.val[1]!.bv) = _
    -- Let b = 5*(k%5) + k/5 = transpose_perm k. Loop0/Loop1 use this index.
    set b := 5 * (k % 5) + k / 5 with hb_def
    have hk_div_5 : k / 5 < 5 := by
      have : k < 5 * 5 := by omega
      exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 5)).mpr this
    have hk_mod_5 : k % 5 < 5 := Nat.mod_lt _ (by decide)
    have hb_lt_25 : b < 25 := by show 5 * (k % 5) + k / 5 < 25; omega
    -- b%5 = k/5; b/5 = k%5.
    have h_b_mod : b % 5 = k / 5 := by
      show (5 * (k % 5) + k / 5) % 5 = k / 5
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hk_div_5
    have h_b_div : b / 5 = k % 5 := by
      show (5 * (k % 5) + k / 5) / 5 = k % 5
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by decide : 0 < 5)]
      have : k / 5 / 5 = 0 := Nat.div_eq_of_lt hk_div_5
      omega
    -- The byte block index equals the spec index k. The impl's
    -- loop ranges over j ∈ [0, RATE/8), so we want `k < RATE/8` to mean
    -- the lane was touched. But the impl stored byte block j at impl idx
    -- transpose(j); we read it back at impl idx b = transpose(k). So the
    -- impl iteration that touched impl idx b is j = transpose(b) = k.
    by_cases h_k_lt : k < RATE.val / 8
    · rw [if_pos h_k_lt]
      -- The lane at impl idx b was touched in Loop1 at iteration j = k
      -- (since transpose(b) = k). Use h_lanes at iteration b? No, h_lanes
      -- is iteration-indexed; iteration j ∈ [0, i2.val), and the j-th
      -- iteration touches impl idx 5*(j%5)+j/5 = transpose(j). For
      -- impl idx b, the touching iteration is transpose⁻¹(b) = k.
      have h_k_lt_i2 : k < i2.val := by rw [h_i2_val]; exact h_k_lt
      have h_lane := h_lanes k h_k_lt_i2 hk_25
      -- h_lane gives: lift_lane_bv r.st[5*(k%5)+k/5] = loop1_lane_at s state_flat1 k.
      -- i.e., lift_lane_bv r.st[b] = ... (since b = transpose(k))
      rw [h_lane]
      unfold loop1_lane_at
      rw [← lift_lane_bv_xor]
      -- The s.st side: lift_lane_bv (s.st[transpose_perm k][0]) (...[1])
      -- = lift_lane_bv (s.st[5*(k%5)+k/5][0]) (...[1])
      -- We need this to match (lift s)[k] -- which is what we already showed.
      apply congrArg ((lift_lane_bv (s.st.val[5 * (k % 5) + k / 5]!.val[0]!.bv)
                                    (s.st.val[5 * (k % 5) + k / 5]!.val[1]!.bv)) ^^^ ·)
      -- h_sf gives: state_flat1[k] = (interleave_bv ...).
      have h_sf := h_state_flat1 k h_k_lt_i2 hk_25
      have h_sf1 : (state_flat1.val[k]!).val[0]!.bv =
          (interleave_bv ((Lane2U32_from_4byte_LE_pairs blocks start k).val[0]!).bv
                         ((Lane2U32_from_4byte_LE_pairs blocks start k).val[1]!).bv).1 := by
        have := h_sf; exact (Prod.mk.injEq .. |>.mp this).1
      have h_sf2 : (state_flat1.val[k]!).val[1]!.bv =
          (interleave_bv ((Lane2U32_from_4byte_LE_pairs blocks start k).val[0]!).bv
                         ((Lane2U32_from_4byte_LE_pairs blocks start k).val[1]!).bv).2 := by
        have := h_sf; exact (Prod.mk.injEq .. |>.mp this).2
      rw [h_sf1, h_sf2]
      have h_ib := interleave_bv_lift_eq
        ((Lane2U32_from_4byte_LE_pairs blocks start k).val[0]!).bv
        ((Lane2U32_from_4byte_LE_pairs blocks start k).val[1]!).bv
      simp only at h_ib
      exact h_ib
    · rw [if_neg h_k_lt]
      have h_k_ge_i2 : i2.val ≤ k := by rw [h_i2_val]; omega
      have h_unch := h_unchanged k h_k_ge_i2 hk_25
      -- h_unch : r_final.st.val[5*(k%5)+k/5]! = s.st.val[5*(k%5)+k/5]!
      rw [h_unch]
  -- Assemble: walk the body of `load_block`, rewriting each step.
  apply triple_of_ok_bytes (v := r_final) _ ⟨h_r_i, h_per_cell⟩
  show state.KeccakState.load_block RATE s blocks start = .ok r_final
  unfold state.KeccakState.load_block state.load_block_2u32
  -- Chain rewrites of the pure `.ok`-steps.
  rw [h_len]; simp only [bind_tc_ok]
  -- massert (RATE ≤ blocks.len) — uses `≤` which here unfolds to `decide ... = true`.
  show (do massert (RATE ≤ Std.Slice.len blocks); _) = .ok r_final
  unfold massert
  rw [if_pos (by show RATE ≤ Std.Slice.len blocks;
                  exact (Std.UScalar.le_equiv RATE _).mpr h_RATE_le)]
  simp only [bind_tc_ok]
  rw [h_mod]; simp only [bind_tc_ok]
  show (do massert ((0#usize : Std.Usize) = (0#usize : Std.Usize)); _) = .ok r_final
  unfold massert
  rw [if_pos (by rfl)]
  simp only [bind_tc_ok]
  rw [h_zero]; simp only [bind_tc_ok]
  rw [h_div_eq]; simp only [bind_tc_ok]
  rw [h_loop0_eq]; simp only [bind_tc_ok]
  exact h_loop1_eq

/-- `state.KeccakState.store_block RATE s out` terminates with `.ok`,
    and the output slice's length is preserved. Preconditions match
    those of `store_block_2u32_loop_spec` after derivation through the
    outer wrapper. -/
@[spec]
theorem state.KeccakState.store_block_spec
    (RATE : Std.Usize) (s : state.KeccakState) (out : Slice Std.U8)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_bnd : RATE.val ≤ 200)
    (h_blk  : RATE.val ≤ out.val.length)
    (h_off  : RATE.val ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄
    state.KeccakState.store_block RATE s out
    ⦃ ⇓ r => ⌜
        r.val.length = out.val.length
        ∧ ∀ k : Nat, k < RATE.val →
            r.val[k]! = ⟨(BitVec.toLEBytes
              ((Foundation.lift s).val[k / 8]!).bv)[k % 8]!⟩
    ⌝ ⦄ := by
  have h_RATE_div_le : RATE.val / 8 ≤ 25 := by omega
  have h_RATE_div_mul : 8 * (RATE.val / 8) = RATE.val := by
    have : RATE.val = 8 * (RATE.val / 8) + RATE.val % 8 :=
      (Nat.div_add_mod _ _).symm
    omega
  obtain ⟨i_div, h_div_eq, h_div_val⟩ := rate_div_8_ok RATE
  have h_loop_le : (0#usize : Std.Usize).val ≤ i_div.val := by
    show 0 ≤ i_div.val; omega
  have h_loop_bnd : i_div.val ≤ 25 := by rw [h_div_val]; exact h_RATE_div_le
  have h_loop_off : 8 * i_div.val ≤ Std.Usize.max := by
    rw [h_div_val]; omega
  have h_loop_blk : 8 * i_div.val ≤ out.val.length := by
    rw [h_div_val]; omega
  obtain ⟨r, h_r_eq, h_r_len, h_r_bytes⟩ :=
    triple_exists_ok_bytes
      (state.store_block_2u32_loop_spec ⟨0#usize, i_div⟩ s out
        h_loop_le h_loop_bnd h_loop_off h_loop_blk (by rfl))
  -- The loop's strong post gives `r.val[b]! = store_block_byte_at s b`
  -- for `b < 8 * i_div.val = 8 * (RATE.val / 8) = RATE.val` (when RATE.val%8=0).
  -- We rewrite via `store_block_byte_at_eq_toLEBytes`.
  have h_r_textbook : ∀ k : Nat, k < RATE.val →
      r.val[k]! = ⟨(BitVec.toLEBytes
        ((Foundation.lift s).val[k / 8]!).bv)[k % 8]!⟩ := by
    intro k hk_RATE
    have hk_8idiv : k < 8 * i_div.val := by rw [h_div_val]; omega
    have hk_200 : k < 8 * 25 := by omega
    have hk_div : k / 8 < 25 := by
      have : k < 8 * 25 := hk_200
      omega
    have h_loop := h_r_bytes k hk_8idiv hk_200
    rw [h_loop]
    exact store_block_byte_at_eq_toLEBytes s k hk_div
  apply triple_of_ok_bytes (v := r) _ ⟨h_r_len, h_r_textbook⟩
  show state.KeccakState.store_block RATE s out = .ok r
  unfold state.KeccakState.store_block state.store_block_2u32
  simp only [h_div_eq, bind_tc_ok]
  exact h_r_eq

/-- `state.KeccakState.load_block_full RATE s blocks start` delegates to
    `load_block_2u32` after the `Array.to_slice` coercion. Same
    termination post as `load_block_spec`. -/
@[spec]
theorem state.KeccakState.load_block_full_spec
    (RATE : Std.Usize) (s : state.KeccakState)
    (blocks : Std.Array Std.U8 200#usize) (start : Std.Usize)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_bnd : RATE.val ≤ 200)
    (h_blk : start.val + RATE.val ≤ 200)
    (h_off : start.val + RATE.val ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄
    state.KeccakState.load_block_full RATE s blocks start
    ⦃ ⇓ r => ⌜
        r.i = s.i
        ∧ ∀ k : Nat, k < 25 →
            ((Foundation.lift r).val[k]!).bv =
              (if k < RATE.val / 8 then
                  ((Foundation.lift s).val[k]!).bv ^^^
                    (BitVec.zeroExtend 64
                        (((Lane2U32_from_4byte_LE_pairs (Std.Array.to_slice blocks) start
                            k).val[1]!).bv) <<< 32
                     ||| BitVec.zeroExtend 64
                        (((Lane2U32_from_4byte_LE_pairs (Std.Array.to_slice blocks) start
                            k).val[0]!).bv))
               else ((Foundation.lift s).val[k]!).bv)
    ⌝ ⦄ := by
  -- `Array.to_slice` preserves `.val`; the array has length 200.
  have h_to_slice_val : (Std.Array.to_slice blocks).val = blocks.val := rfl
  have h_to_slice_len : (Std.Array.to_slice blocks).val.length = 200 := by
    rw [h_to_slice_val]; exact blocks.property
  have h_blk' : start.val + RATE.val ≤ (Std.Array.to_slice blocks).val.length := by
    rw [h_to_slice_len]; exact h_blk
  obtain ⟨r_final, h_inner_eq, h_post⟩ :=
    triple_exists_ok_bytes
      (state.KeccakState.load_block_spec RATE s
        (Std.Array.to_slice blocks) start
        h_RATE_mod h_RATE_bnd h_blk' h_off)
  obtain ⟨h_r_i, h_r_per_cell⟩ := h_post
  have h_inner_unfold :
      state.load_block_2u32 RATE s (Std.Array.to_slice blocks) start = .ok r_final := by
    have := h_inner_eq; unfold state.KeccakState.load_block at this; exact this
  apply triple_of_ok_bytes (v := r_final) _ ⟨h_r_i, h_r_per_cell⟩
  show state.KeccakState.load_block_full RATE s blocks start = .ok r_final
  unfold state.KeccakState.load_block_full state.load_block_full_2u32
  -- The body is `do s1 ← lift (Array.to_slice blocks); load_block_2u32 RATE s s1 start`.
  -- For the public `Slice U8`, `lift` (here `Std.lift`) is `Result.ok` (identity).
  -- We reduce `lift x = .ok x` and then chain.
  show (do
        let s1 ← Std.lift (α := Slice Std.U8) (Std.Array.to_slice blocks)
        state.load_block_2u32 RATE s s1 start) = .ok r_final
  unfold Std.lift
  show (do
        let s1 ← (Result.ok (Std.Array.to_slice blocks) : Result (Slice Std.U8))
        state.load_block_2u32 RATE s s1 start) = .ok r_final
  simp only [bind_tc_ok]
  exact h_inner_unfold

end libcrux_iot_sha3.Sponge
