import LibcruxIotSha3.Composition.Pedantic.Lanes
import LibcruxIotSha3.Composition.Pedantic.Bytes
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

end LibcruxIotSha3.Composition.Pedantic
