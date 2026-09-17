import LibcruxIotSha3.Composition.Pedantic.Lanes
import LibcruxIotSha3.Composition.Pedantic.Sha3
/-!
# `hacspec_sha3`'s byte-rate sponge, read bit by bit

`hacspec_sha3` absorbs and squeezes whole `u64` lanes built from little-endian
bytes; the pedantic sponge works on the flat 1600-bit string.  This module
relates the two: a block of bytes XORed into the lanes is the block's bits
XORed into the bit string, in the same order `h2b` produces them.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-! ### Reading `lanesToBits` by lane -/

theorem lanesToBits_lane (s : Lanes) {t z : Nat} (ht : t < 25) (hz : z < 64) :
    (lanesToBits s)[64 * t + z]! = (s.val[t]!).bv.getLsbD z := by
  have hx : t % 5 < 5 := by omega
  have hy : t / 5 < 5 := by omega
  have hb : 64 * t + z = bitPos (t % 5) (t / 5) z := by
    simp only [bitPos]; omega
  rw [hb, lanesToBits_get s hx hy hz, laneBit,
    show 5 * (t / 5) + t % 5 = t from by omega]

/-! ### Bytes to lane bits -/

theorem bv_getElem!_eq_getLsbD {w : Nat} (b : BitVec w) (j : Nat) :
    b[j]! = b.getLsbD j := by
  by_cases h : j < w
  · rw [BitVec.getElem!_eq_getElem b j h]
    rfl
  · rw [BitVec.getElem!_eq_false b j (by omega)]
    rw [BitVec.getLsbD_of_ge b j (by omega)]

/-- Bit `z` of a `u64` built from eight little-endian bytes is bit `z % 8` of
    byte `z / 8`. -/
theorem from_le_bytes_bit (a : Std.Array Std.U8 8#usize) (z : Nat) (hz : z < 64) :
    (Std.core.num.U64.from_le_bytes a).bv.getLsbD z = (a.val[z / 8]!).bv.getLsbD (z % 8) := by
  have hlen : a.val.length = 8 := a.property
  have hbv : Std.U64.bv (Std.core.num.U64.from_le_bytes a)
      = (BitVec.fromLEBytes (List.map Std.U8.bv a.val)).cast (by simp) := rfl
  rw [← bv_getElem!_eq_getLsbD, ← bv_getElem!_eq_getLsbD, hbv,
    BitVec.getElem!_cast, BitVec.fromLEBytes_getElem!]
  rw [show (List.map Std.U8.bv a.val)[z / 8]! = Std.U8.bv a.val[z / 8]! from by
    rw [getElem!_pos _ _ (by simp; omega), getElem!_pos a.val _ (by omega)]
    simp]
  rw [BitVec.getElem!_eq_testBit_toNat]


/-! ### Slicing and `try_from` -/

theorem array_from_fn_eq {T F : Type} (N : Std.Usize)
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (g : Nat → T)
    (hN : N.val ≤ 4294967296)
    (hcall : ∀ i : Std.Usize, i.val < N.val → inst.call_mut c i = ok (g i.val, c)) :
    rust_primitives.slice.array_from_fn N inst c = ok (mkArr N g) := by
  unfold rust_primitives.slice.array_from_fn
  rw [array_from_fn_go_eq inst c g N.val hN hcall N.val (le_refl _), bind_tc_ok,
    dif_pos (by simp)]
  rfl

theorem slice_index_range_eq {α : Type} (v : Slice α) (a b : Std.Usize)
    (hab : a.val ≤ b.val) (hb : b.val ≤ v.val.length) :
    core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α) v
      { start := a, «end» := b }
    = ok ⟨v.val.slice a.val b.val, by
        have := v.val.slice_length_le a.val b.val
        have := v.property
        scalar_tac⟩ := by
  simp [core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_slice, rust_primitives.slice.slice_length,
    Std.Slice.subslice, hab, hb]

theorem slice_slice_get {α : Type} [Inhabited α] (v : Slice α) (a b : Std.Usize) (i : Nat)
    (hab : a.val ≤ b.val) (hb : b.val ≤ v.val.length) (hi : i < b.val - a.val) :
    (v.val.slice a.val b.val)[i]! = v.val[a.val + i]! := by
  rw [getElem!_pos _ i (by rw [List.slice_length]; omega),
    getElem!_pos v.val (a.val + i) (by omega)]
  rw [List.getElem_slice _ _ _ _ (by omega)]

/-- `<[T; N]>::try_from` on a slice of the right length copies it. -/
theorem slice_try_from_eq {T : Type} [Inhabited T] (N : Std.Usize)
    (copyInst : core.marker.Copy T) (x : Slice T) (hx : x.val.length = N.val)
    (hN : N.val ≤ 4294967296) :
    core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from N copyInst x
      = ok (core.result.Result.Ok (mkArr N (fun i => x.val[i]!))) := by
  unfold core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
  simp only [rust_primitives.slice.slice_length, bind_tc_ok]
  rw [if_pos (show Std.Slice.len x = N from (Std.UScalar.eq_equiv _ _).mpr (by
    simp only [Std.Slice.len]
    rw [show (Std.Usize.ofNatCore x.val.length (by scalar_tac) : Std.Usize).val
      = x.val.length from by simp]
    omega))]
  rw [array_from_fn_eq N _ x (fun i => x.val[i]!) hN ?_, bind_tc_ok]
  intro i hi
  show (do
    let t ← rust_primitives.slice.slice_index x i
    ok (t, x)) = _
  rw [rust_primitives.slice.slice_index, slice_index_usize_eq x i (by omega), bind_tc_ok]

theorem unwrap_ok_eq {T E : Type} (inst : core.fmt.Debug E) (t : T) :
    core.result.Result.unwrap inst (core.result.Result.Ok t : core.result.Result T E) = ok t := rfl


theorem mkArr_congr {T : Type} (N : Std.Usize) {g h : Nat → T}
    (hgh : ∀ i < N.val, g i = h i) : mkArr N g = mkArr N h := by
  apply Subtype.ext
  show (List.range N.val).map g = (List.range N.val).map h
  apply List.map_congr_left
  intro i hi
  exact hgh i (by simpa using hi)

/-! ### `xor_block_into_state` -/

/-- The `u64` lane the block's bytes `8t … 8t+7` make up. -/
def blockLane (blk : Slice Std.U8) (t : Nat) : Std.U64 :=
  Std.core.num.U64.from_le_bytes (mkArr 8#usize (fun j => blk.val[8 * t + j]!))

/-- XORing a rate-sized block into the state, lane by lane. -/
def xorLanes (s : Lanes) (blk : Slice Std.U8) (rate : Std.Usize) : Lanes :=
  mkArr 25#usize (fun t => if t < rate.val / 8 then s.val[t]! ^^^ blockLane blk t else s.val[t]!)

theorem xor_block_into_state_eq (s : Lanes) (blk : Slice Std.U8) (rate : Std.Usize)
    (hblk : 8 * (rate.val / 8) ≤ blk.val.length) :
    hacspec_sha3.sponge.xor_block_into_state s blk rate = ok (xorLanes s blk rate) := by
  unfold hacspec_sha3.sponge.xor_block_into_state
  refine createi_eq _ _ _ _ (by simp) ?_
  intro t ht
  have ht25 : t.val < 25 := by simpa using ht
  unfold hacspec_sha3.sponge.xor_block_into_state.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  show hacspec_sha3.sponge.xor_block_into_state.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
    (rate, s, blk) t = _
  unfold
    hacspec_sha3.sponge.xor_block_into_state.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  obtain ⟨q, hq, hqv⟩ := usize_div_eq rate 8#usize (by simp)
  have hqn : q.val = rate.val / 8 := by rw [hqv]; simp
  show (do
      let i1 ← rate / 8#usize
      if t < i1 then do
        let i2 ← Std.Array.index_usize s t
        let i3 ← 8#usize * t
        let i4 ← i3 + 8#usize
        let s1 ← core.Slice.Insts.CoreOpsIndexIndex.index
          (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8) blk
          { start := i3, «end» := i4 }
        let r ← core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
          8#usize core.U8.Insts.CoreMarkerCopy s1
        let a1 ← core.result.Result.unwrap
          core.array.TryFromSliceError.Insts.CoreFmtDebug r
        let i5 ← core.num.U64.from_le_bytes a1
        let i6 ← Std.lift (i2 ^^^ i5)
        ok (i6, (rate, s, blk))
      else do
        let i2 ← Std.Array.index_usize s t
        ok (i2, (rate, s, blk))) = _
  rw [hq, bind_tc_ok]
  by_cases hlt : t.val < rate.val / 8
  · rw [if_pos (show t < q from (Std.UScalar.lt_equiv t q).mpr (by omega))]
    obtain ⟨a, ha, hav⟩ := usize_mul_eq 8#usize t (by scalar_tac)
    obtain ⟨b, hb, hbv⟩ := usize_add_eq a 8#usize (by scalar_tac)
    have han : a.val = 8 * t.val := by rw [hav]; simp
    have hbn : b.val = 8 * t.val + 8 := by rw [hbv, han]; simp
    rw [index_usize_eq s t (by simp; omega), bind_tc_ok, ha, bind_tc_ok, hb, bind_tc_ok,
      slice_index_range_eq blk a b (by omega) (by omega), bind_tc_ok,
      slice_try_from_eq 8#usize core.U8.Insts.CoreMarkerCopy _
        (by simp only []; rw [List.slice_length]; simp; omega) (by simp), bind_tc_ok,
      unwrap_ok_eq, bind_tc_ok]
    simp only [core.num.U64.from_le_bytes, rust_primitives.arithmetic.from_le_bytes_u64,
      bind_tc_ok, Std.lift]
    rw [show mkArr 8#usize (fun j => (blk.val.slice a.val b.val)[j]!)
        = mkArr 8#usize (fun j => blk.val[8 * t.val + j]!) from
      mkArr_congr _ (fun j hj => by
        rw [slice_slice_get blk a b j (by omega) (by omega) (by simp at hj; omega), han])]
    rw [if_pos hlt, blockLane]
    rfl
  · rw [if_neg (show ¬ t < q from fun hc => hlt (by
      have := (Std.UScalar.lt_equiv t q).mp hc; omega))]
    rw [index_usize_eq s t (by simp; omega), bind_tc_ok, if_neg hlt]
    rfl


/-! ### `h2b` by index -/

/-- Bit `8i + j` of a byte string's bit string is bit `j` of byte `i`. -/
theorem h2bList_get (l : List Std.U8) (i j : Nat) (hi : i < l.length) (hj : j < 8) :
    (h2bList l)[8 * i + j]! = (l[i]!).bv.getLsbD j := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    have hcons : h2bList (a :: t) = byteBits a ++ h2bList t := by
      simp only [h2bList, List.flatMap_cons]
    rw [hcons]
    cases i with
    | zero =>
      rw [show 8 * 0 + j = j from by omega,
        List.getElem!_append_left _ _ j (by rw [byteBits_len]; omega)]
      simp only [byteBits]
      rw [getElem!_pos _ j (by simp; omega)]
      simp
    | succ k =>
      have hk : k < t.length := by simp only [List.length_cons] at hi; omega
      rw [List.getElem!_append_right _ _ _ (by rw [byteBits_len]; omega), byteBits_len,
        show 8 * (k + 1) + j - 8 = 8 * k + j from by omega, ih k hk]
      simp


/-! ### The absorbed block, as bits -/

theorem list_ext_getElem! {α : Type} [Inhabited α] {l1 l2 : List α}
    (hlen : l1.length = l2.length) (h : ∀ i < l1.length, l1[i]! = l2[i]!) : l1 = l2 := by
  apply List.ext_getElem hlen
  intro i h1 h2
  have hi := h i h1
  rwa [getElem!_pos l1 i h1, getElem!_pos l2 i h2] at hi

/-- The rate-sized block, zero-extended to the full state width -- the second
    argument of the pedantic `absorbStep`'s XOR. -/
def blockMask (blk : Slice Std.U8) (L : Nat) : List Bool :=
  (h2bList blk.val).take (64 * L) ++ List.replicate (1600 - 64 * L) false

theorem blockMask_len (blk : Slice Std.U8) (L : Nat) (hL : L ≤ 25)
    (hblk : 8 * L ≤ blk.val.length) : (blockMask blk L).length = 1600 := by
  have hh : (h2bList blk.val).length = 8 * blk.val.length := h2bList_len blk.val
  simp only [blockMask, List.length_append, List.length_take, List.length_replicate, hh]
  omega

theorem blockMask_get (blk : Slice Std.U8) (L : Nat) (hL : L ≤ 25)
    (hblk : 8 * L ≤ blk.val.length) (t z : Nat) (ht : t < 25) (hz : z < 64) :
    (blockMask blk L)[64 * t + z]!
      = (if t < L then (blk.val[8 * t + z / 8]!).bv.getLsbD (z % 8) else false) := by
  have hh : (h2bList blk.val).length = 8 * blk.val.length := h2bList_len blk.val
  have htake : ((h2bList blk.val).take (64 * L)).length = 64 * L := by
    rw [List.length_take]; omega
  by_cases hlt : t < L
  · rw [blockMask, List.getElem!_append_left _ _ _ (by rw [htake]; omega)]
    rw [getElem!_pos _ _ (by rw [htake]; omega), List.getElem_take]
    rw [← getElem!_pos (h2bList blk.val) _ (by omega)]
    rw [show 64 * t + z = 8 * (8 * t + z / 8) + z % 8 from by omega,
      h2bList_get blk.val _ _ (by omega) (by omega), if_pos hlt]
  · rw [blockMask, List.getElem!_append_right _ _ _ (by rw [htake]; omega), htake]
    rw [getElem!_pos _ _ (by rw [List.length_replicate]; omega), List.getElem_replicate,
      if_neg hlt]

/-- XORing a block into the lanes is XORing its bits into the bit string. -/
theorem lanesToBits_xorLanes (s : Lanes) (blk : Slice Std.U8) (rate : Std.Usize)
    (hL : rate.val / 8 ≤ 25) (hblk : 8 * (rate.val / 8) ≤ blk.val.length) :
    lanesToBits (xorLanes s blk rate)
      = List.zipWith (· ^^ ·) (lanesToBits s) (blockMask blk (rate.val / 8)) := by
  have hmlen := blockMask_len blk (rate.val / 8) hL hblk
  apply list_ext_getElem!
  · simp only [lanesToBits_len, List.length_zipWith, hmlen]
    omega
  · intro p hp
    have hp1600 : p < 1600 := by simpa using hp
    obtain ⟨t, z, ht, hz, rfl⟩ : ∃ t z, t < 25 ∧ z < 64 ∧ p = 64 * t + z :=
      ⟨p / 64, p % 64, by omega, by omega, by omega⟩
    have hzip : (List.zipWith (· ^^ ·) (lanesToBits s)
          (blockMask blk (rate.val / 8)))[64 * t + z]!
        = ((lanesToBits s)[64 * t + z]! ^^ (blockMask blk (rate.val / 8))[64 * t + z]!) := by
      rw [getElem!_pos _ (64 * t + z)
          (by simp only [List.length_zipWith, lanesToBits_len, hmlen]; omega),
        List.getElem_zipWith,
        ← getElem!_pos (lanesToBits s) (64 * t + z) (by simp; omega),
        ← getElem!_pos (blockMask blk (rate.val / 8)) (64 * t + z) (by rw [hmlen]; omega)]
    rw [hzip, lanesToBits_lane _ ht hz, lanesToBits_lane _ ht hz,
      blockMask_get blk _ hL hblk _ _ ht hz]
    rw [xorLanes, mkArr_get 25#usize _ (by simp; omega)]
    by_cases hlt : t < rate.val / 8
    · rw [if_pos hlt, if_pos hlt, u64_xor_bit, blockLane,
        from_le_bytes_bit _ _ hz, mkArr_get 8#usize _ (by simp; omega)]
    · rw [if_neg hlt, if_neg hlt]
      simp


/-! ### `h2b` commutes with taking and dropping bytes -/

theorem h2bList_take (l : List Std.U8) (n : Nat) :
    h2bList (l.take n) = (h2bList l).take (8 * n) := by
  induction l generalizing n with
  | nil => simp [h2bList]
  | cons a t ih =>
    cases n with
    | zero => simp [h2bList]
    | succ k =>
      have hb : (byteBits a).length = 8 := byteBits_len a
      simp only [List.take_succ_cons, h2bList, List.flatMap_cons]
      rw [show 8 * (k + 1) = (byteBits a).length + 8 * k from by omega,
        List.take_append]
      simp only [h2bList] at ih
      rw [ih k]
      simp [hb]

theorem h2bList_drop (l : List Std.U8) (n : Nat) :
    h2bList (l.drop n) = (h2bList l).drop (8 * n) := by
  induction l generalizing n with
  | nil => simp [h2bList]
  | cons a t ih =>
    cases n with
    | zero => simp [h2bList]
    | succ k =>
      have hb : (byteBits a).length = 8 := byteBits_len a
      simp only [List.drop_succ_cons, h2bList, List.flatMap_cons]
      rw [show 8 * (k + 1) = (byteBits a).length + 8 * k from by omega,
        List.drop_append]
      simp only [h2bList] at ih
      rw [ih k]
      simp [hb]


/-! ### `absorb_block` -/

theorem absorb_block_eq (s : Lanes) (blk : Slice Std.U8) (rate : Std.Usize)
    (hL : rate.val / 8 ≤ 25) (hblk : 8 * (rate.val / 8) ≤ blk.val.length) :
    ∃ s' : Lanes, hacspec_sha3.sponge.absorb_block s blk rate = ok s' ∧
      lanesToBits s'
        = keccakF (List.zipWith (· ^^ ·) (lanesToBits s) (blockMask blk (rate.val / 8))) := by
  obtain ⟨s', hs', hbits⟩ := keccakF_lanes_eq (xorLanes s blk rate)
  refine ⟨s', ?_, ?_⟩
  · unfold hacspec_sha3.sponge.absorb_block
    rw [xor_block_into_state_eq s blk rate hblk, bind_tc_ok]
    exact hs'
  · rw [← hbits, lanesToBits_xorLanes s blk rate hL hblk]

/-! ### `pad_last_block` -/

/-- The 200-byte buffer before the trailing `0x80` is set: the message tail,
    then the domain-separation byte, then zeros. -/
def padBlockPre (msg : List Std.U8) (off rem : Nat) (delim : Std.U8) : List Std.U8 :=
  ((List.replicate 200 (0#u8)).setSlice! 0 (msg.slice off (off + rem))).set rem delim

/-- The whole padded last block. -/
def padBlockList (msg : List Std.U8) (off rem rate : Nat) (delim : Std.U8) : List Std.U8 :=
  (padBlockPre msg off rem delim).set (rate - 1)
    ((padBlockPre msg off rem delim)[rate - 1]! ||| 128#u8)

theorem padBlockPre_len (msg : List Std.U8) (off rem : Nat) (delim : Std.U8) :
    (padBlockPre msg off rem delim).length = 200 := by
  simp only [padBlockPre, List.length_set, List.length_setSlice!, List.length_replicate]

theorem padBlockList_len (msg : List Std.U8) (off rem rate : Nat) (delim : Std.U8) :
    (padBlockList msg off rem rate delim).length = 200 := by
  simp only [padBlockList, List.length_set, padBlockPre_len]

set_option maxRecDepth 10000 in
theorem pad_last_block_eq (message : Slice Std.U8) (off rem rate : Std.Usize) (delim : Std.U8)
    (hrem : rem.val < rate.val) (hrate200 : rate.val ≤ 200) (hrate1 : 1 ≤ rate.val)
    (hmsg : off.val + rem.val ≤ message.val.length) :
    hacspec_sha3.sponge.pad_last_block message off rem rate delim
      = ok ⟨padBlockList message.val off.val rem.val rate.val delim, by
          rw [padBlockList_len]; simp⟩ := by
  obtain ⟨i, hi, hiv⟩ := usize_add_eq off rem (by scalar_tac)
  have hin : i.val = off.val + rem.val := by rw [hiv]
  obtain ⟨j, hj, hjv⟩ := usize_sub_eq rate 1#usize (by simp; omega)
  have hjn : j.val = rate.val - 1 := by rw [hjv]; simp
  have hsl : (message.val.slice off.val i.val).length = rem.val := by
    rw [List.slice_length]; omega
  unfold hacspec_sha3.sponge.pad_last_block
  generalize hbuf : Std.Array.repeat 200#usize 0#u8 = buf
  have hblen : buf.val.length = 200 := by rw [← hbuf]; simp [Std.Array.repeat]
  have hbval : buf.val = List.replicate 200 (0#u8) := by rw [← hbuf]; simp [Std.Array.repeat]
  simp only [core.Array.Insts.CoreOpsIndexIndexMut.index_mut, core.array.Array.as_mut_slice,
    rust_primitives.slice.array_as_mut_slice, Std.Array.to_slice_mut, Std.Array.to_slice,
    core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
    core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    rust_primitives.slice.slice_slice_mut, Std.Slice.subslice, bind_tc_ok, Std.Slice.length]
  simp [hblen, show rem.val ≤ 200 from by omega]
  rw [hi, bind_tc_ok, slice_index_range_eq message off i (by omega) (by omega), bind_tc_ok,
    copy_from_slice_eq _ _ (by
      simp only [List.length_take, hsl]
      omega), bind_tc_ok]
  rw [array_update_eq _ rem delim (by simp; omega)]
  rw [bind_tc_ok, hj, bind_tc_ok, index_usize_eq _ j (by simp; omega), bind_tc_ok]
  simp only [Std.lift, bind_tc_ok]
  rw [array_update_eq _ j _ (by simp; omega)]
  apply congrArg
  apply Subtype.ext
  show ((Std.Array.from_slice buf ⟨buf.val.setSlice! 0 (message.val.slice off.val i.val), by
      rw [List.length_setSlice!, hblen]; scalar_tac⟩).val.set rem.val delim).set j.val
      (((Std.Array.from_slice buf ⟨buf.val.setSlice! 0 (message.val.slice off.val i.val), by
        rw [List.length_setSlice!, hblen]; scalar_tac⟩).val.set rem.val delim)[j.val]! ||| 128#u8)
    = padBlockList message.val off.val rem.val rate.val delim
  rw [Std.Array.from_slice_val _ _ (by rw [List.length_setSlice!]; exact hblen)]
  simp only [padBlockList, padBlockPre, hbval, hin, hjn]


/-! ### The padded block, byte by byte -/

theorem list_getElem!_set {α : Type} [Inhabited α] (l : List α) (i : Nat) (x : α) (k : Nat)
    (hk : k < l.length) : (l.set i x)[k]! = if k = i then x else l[k]! := by
  rw [getElem!_pos _ k (by simpa using hk), getElem!_pos l k hk, List.getElem_set]
  by_cases h : k = i
  · subst h; simp
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]

theorem list_slice_get {α : Type} [Inhabited α] (l : List α) (a b k : Nat)
    (hb : b ≤ l.length) (hk : a + k < b) : (l.slice a b)[k]! = l[a + k]! := by
  rw [getElem!_pos _ k (by rw [List.slice_length]; omega),
    getElem!_pos l (a + k) (by omega), List.getElem_slice _ _ _ _ (by omega)]

/-- The byte the padded block holds at `k`, before the trailing `0x80`. -/
def padBlockBase (msg : List Std.U8) (off rem : Nat) (delim : Std.U8) (k : Nat) : Std.U8 :=
  if k < rem then msg[off + k]! else if k = rem then delim else 0#u8

theorem padBlockPre_get (msg : List Std.U8) (off rem : Nat) (delim : Std.U8)
    (hrem : rem < 200) (hmsg : off + rem ≤ msg.length) (k : Nat) (hk : k < 200) :
    (padBlockPre msg off rem delim)[k]! = padBlockBase msg off rem delim k := by
  have hsl : (msg.slice off (off + rem)).length = rem := by
    rw [List.slice_length]; omega
  have hrl : (List.replicate 200 (0#u8)).length = 200 := List.length_replicate
  simp only [padBlockPre]
  rw [list_getElem!_set _ _ _ k (by rw [List.length_setSlice!]; omega)]
  by_cases hkr : k < rem
  · rw [if_neg (by omega),
      List.getElem!_setSlice!_middle (List.replicate 200 (0#u8)) (msg.slice off (off + rem)) 0 k
        ⟨by omega, by rw [hsl]; omega, by rw [hrl]; omega⟩, Nat.sub_zero,
      list_slice_get msg off (off + rem) k (by omega) (by omega)]
    simp only [padBlockBase, if_pos hkr]
  · by_cases hke : k = rem
    · rw [if_pos hke]
      simp only [padBlockBase, if_neg hkr, if_pos hke]
    · rw [if_neg hke,
        List.getElem!_setSlice!_suffix (List.replicate 200 (0#u8)) (msg.slice off (off + rem)) 0 k
          (by rw [hsl]; omega)]
      rw [getElem!_pos _ k (by rw [hrl]; omega), List.getElem_replicate]
      simp only [padBlockBase, if_neg hkr, if_neg hke]

theorem padBlockList_get (msg : List Std.U8) (off rem rate : Nat) (delim : Std.U8)
    (hrem : rem < rate) (hrate200 : rate ≤ 200) (hmsg : off + rem ≤ msg.length)
    (k : Nat) (hk : k < 200) :
    (padBlockList msg off rem rate delim)[k]!
      = (if k = rate - 1 then padBlockBase msg off rem delim k ||| 128#u8
         else padBlockBase msg off rem delim k) := by
  simp only [padBlockList]
  rw [list_getElem!_set _ _ _ k (by rw [padBlockPre_len]; omega)]
  by_cases hke : k = rate - 1
  · rw [if_pos hke, if_pos hke, hke,
      padBlockPre_get msg off rem delim (by omega) hmsg (rate - 1) (by omega)]
  · rw [if_neg hke, if_neg hke, padBlockPre_get msg off rem delim (by omega) hmsg k hk]


/-! ### The padded block, bit by bit -/

theorem byteBits_get (x : Std.U8) (j : Nat) :
    (byteBits x)[j]! = if j < 8 then x.bv.getLsbD j else false := by
  by_cases h : j < 8
  · rw [if_pos h]
    simp only [byteBits]
    rw [getElem!_pos _ j (by simp only [List.length_map, List.length_range]; omega)]
    simp
  · rw [if_neg h, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [byteBits_len]; omega)]
    rfl

theorem u8_or_bit (a b : Std.U8) (z : Nat) :
    (a ||| b).bv.getLsbD z = (a.bv.getLsbD z || b.bv.getLsbD z) := by
  show (a.bv ||| b.bv).getLsbD z = _
  simp

theorem bit128 : ∀ j < 8, (128#u8 : Std.U8).bv.getLsbD j = decide (j = 7) := by decide

/-- Bit `q` of the `rate`-byte padded last block. -/
theorem padBlockBits_get (msg : List Std.U8) (off rem rate : Nat) (delim : Std.U8)
    (hrem : rem < rate) (hrate200 : rate ≤ 200) (hmsg : off + rem ≤ msg.length)
    (q : Nat) (hq : q < 8 * rate) :
    (h2bList ((padBlockList msg off rem rate delim).take rate))[q]!
      = ((if q < 8 * rem then (msg[off + q / 8]!).bv.getLsbD (q % 8)
          else (byteBits delim)[q - 8 * rem]!) || decide (q = 8 * rate - 1)) := by
  have hlen : (padBlockList msg off rem rate delim).length = 200 := padBlockList_len _ _ _ _ _
  have htlen : ((padBlockList msg off rem rate delim).take rate).length = rate := by
    rw [List.length_take, hlen]; omega
  have hqe : q = 8 * (q / 8) + q % 8 := by omega
  rw [show (h2bList ((padBlockList msg off rem rate delim).take rate))[q]!
      = (((padBlockList msg off rem rate delim).take rate)[q / 8]!).bv.getLsbD (q % 8) from by
    conv_lhs => rw [hqe]
    exact h2bList_get _ (q / 8) (q % 8) (by rw [htlen]; omega) (by omega)]
  rw [getElem!_pos _ (q / 8) (by rw [htlen]; omega), List.getElem_take,
    ← getElem!_pos (padBlockList msg off rem rate delim) (q / 8) (by rw [hlen]; omega),
    padBlockList_get msg off rem rate delim hrem hrate200 hmsg (q / 8) (by omega)]
  by_cases hq8 : q / 8 = rate - 1
  · rw [if_pos hq8, u8_or_bit, bit128 (q % 8) (by omega)]
    congr 1
    · by_cases hkr : q / 8 < rem
      · rw [if_pos (by omega)]
        simp only [padBlockBase, if_pos hkr]
      · by_cases hke : q / 8 = rem
        · rw [if_neg (by omega)]
          simp only [padBlockBase, if_neg hkr, if_pos hke]
          rw [byteBits_get, if_pos (by omega), show q - 8 * rem = q % 8 from by omega]
        · rw [if_neg (by omega)]
          simp only [padBlockBase, if_neg hkr, if_neg hke]
          rw [byteBits_get, if_neg (by omega)]
          simp
    · simp only [decide_eq_decide]
      omega
  · rw [if_neg hq8]
    rw [show decide (q = 8 * rate - 1) = false from by
      simp only [decide_eq_false_iff_not]
      omega, Bool.or_false]
    by_cases hkr : q / 8 < rem
    · rw [if_pos (by omega)]
      simp only [padBlockBase, if_pos hkr]
    · by_cases hke : q / 8 = rem
      · rw [if_neg (by omega)]
        simp only [padBlockBase, if_neg hkr, if_pos hke]
        rw [byteBits_get, if_pos (by omega), show q - 8 * rem = q % 8 from by omega]
      · rw [if_neg (by omega)]
        simp only [padBlockBase, if_neg hkr, if_neg hke]
        rw [byteBits_get, if_neg (by omega)]
        simp

end LibcruxIotSha3.Composition.Pedantic
