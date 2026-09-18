import LibcruxIotSha3.LaneModel
/-!
# The sponge on 25 lanes

The lane model of Section 4 of FIPS 202 as the implementation arranges it:
the rate measured in bytes, a block XOR-ed in lane by lane, `pad10*1` folded
into a 200-byte buffer.  As in `LibcruxIotSha3/LaneModel.lean` these are
ordinary total functions -- the arguments are `List`s and `Nat`s rather than
`Slice`s and `Usize`s, so nothing here carries a bounds proof -- and as there,
nothing here is trusted: `Composition/Pedantic/Lane*.lean` pins each one to
the transcript's bit-level sponge.
-/

open Aeneas Aeneas.Std
open LibcruxIotSha3.LaneModel

namespace LibcruxIotSha3.SpongeModel

/-! ### Absorbing -/

/-- The `u64` lane the block's bytes `8t … 8t+7` make up. -/
def blockLane (blk : List Std.U8) (t : Nat) : Std.U64 :=
  Std.core.num.U64.from_le_bytes (mkArr 8#usize (fun j => blk[8 * t + j]!))

/-- XORing a rate-sized block into the state, lane by lane.  Lanes past the
    rate are the capacity and are left alone. -/
def xorLanes (s : Lanes) (blk : List Std.U8) (rate : Nat) : Lanes :=
  mkArr 25#usize (fun t => if t < rate / 8 then s.val[t]! ^^^ blockLane blk t else s.val[t]!)

/-- One absorb step: XOR the block in, then permute. -/
def absorbBlockLanes (s : Lanes) (blk : List Std.U8) (rate : Nat) : Lanes :=
  keccakFLanes (xorLanes s blk rate)

/-! ### The padded last block

`pad10*1` (FIPS 202, Algorithm 9) as the implementation writes it: a
200-byte buffer holding the message tail, then the domain-separation byte
(whose low bits are the suffix and whose next bit is the `1` that opens the
padding), then zeros, with `0x80` -- the padding's closing `1` -- OR-ed into
the last byte of the rate. -/

/-- The buffer before the trailing `0x80` is set. -/
def padBlockPre (msg : List Std.U8) (off rem : Nat) (delim : Std.U8) : List Std.U8 :=
  ((List.replicate 200 (0#u8)).setSlice! 0 (msg.slice off (off + rem))).set rem delim

/-- The whole padded last block. -/
def padBlockList (msg : List Std.U8) (off rem rate : Nat) (delim : Std.U8) : List Std.U8 :=
  (padBlockPre msg off rem delim).set (rate - 1)
    ((padBlockPre msg off rem delim)[rate - 1]! ||| 128#u8)

/-- The byte the padded block holds at `k`, before the trailing `0x80`. -/
def padBlockBase (msg : List Std.U8) (off rem : Nat) (delim : Std.U8) (k : Nat) : Std.U8 :=
  if k < rem then msg[off + k]! else if k = rem then delim else 0#u8

/-- Presenting the tail as a dropped suffix from offset `0`, or as the original
    message from offset `a`, pads to the same block. -/
theorem padBlockList_drop (msg : List Std.U8) (a rem rate : Nat) (delim : Std.U8) :
    padBlockList (msg.drop a) 0 rem rate delim = padBlockList msg a rem rate delim := by
  simp only [padBlockList, padBlockPre, List.slice, Nat.sub_zero, List.drop_zero,
    Nat.add_sub_cancel_left, Nat.zero_add]

/-- Absorbing the last block: pad it, then absorb the rate-sized prefix of the
    200-byte buffer.  (The bytes past the rate are never read -- `xorLanes`
    stops at `rate / 8` lanes -- but taking them off keeps this in step with
    the `block[0 .. rate]` the specification writes.) -/
def absorbFinalLanes (s : Lanes) (msg : List Std.U8) (off rem rate : Nat)
    (delim : Std.U8) : Lanes :=
  absorbBlockLanes s ((padBlockList msg off rem rate delim).take rate) rate

/-- Absorbing a whole message: full blocks while they last, then the padded
    last block (which is always absorbed, even when nothing is left over --
    that is what makes the padding injective). -/
def absorbRecLanes (rate : Nat) (delim : Std.U8) : Lanes → List Std.U8 → Lanes
  | s, msg =>
    if _h : 0 < rate ∧ rate ≤ msg.length then
      absorbRecLanes rate delim (absorbBlockLanes s (msg.take rate) rate) (msg.drop rate)
    else absorbFinalLanes s msg 0 msg.length rate delim
  termination_by _ msg => msg.length
  decreasing_by
    simp only [List.length_drop]
    omega

/-- The all-zero starting state, and the whole absorb phase. -/
def absorbLanes (rate : Nat) (delim : Std.U8) (msg : List Std.U8) : Lanes :=
  absorbRecLanes rate delim (Std.Array.repeat 25#usize 0#u64) msg

/-! ### Squeezing -/

/-- The byte whose bit `j` is `f j`. -/
def byteOf (f : Nat → Bool) : Std.U8 :=
  ⟨(List.range 8).foldl (fun acc j => if f j then acc ||| BitVec.twoPow 8 j else acc) 0#8⟩

theorem byteOf_get (f : Nat → Bool) (k : Nat) (hk : k < 8) :
    (byteOf f).bv.getLsbD k = f k := by
  have key : ∀ (n : Nat), n ≤ 8 → ∀ k < 8,
      (((List.range n).foldl
          (fun acc j => if f j then acc ||| BitVec.twoPow 8 j else acc) 0#8)).getLsbD k
        = (decide (k < n) && f k) := by
    intro n
    induction n with
    | zero => intro _ k _; simp
    | succ n ih =>
      intro hn k hk
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hf : f n
      · rw [if_pos hf, BitVec.getLsbD_or, ih (by omega) k hk, BitVec.getLsbD_twoPow]
        by_cases hkn : k = n
        · subst hkn
          rw [show decide (k < k) = false from by simp,
            show decide (k = k) = true from by simp,
            show decide (k < 8) = true from by simp [hk],
            show decide (k < k + 1) = true from by simp, hf]
          simp
        · rw [show decide (n = k) = false from by simp; omega, Bool.and_false, Bool.or_false]
          congr 1
          simp only [decide_eq_decide]
          omega
      · have hf' : f n = false := by simpa using hf
        rw [if_neg hf, ih (by omega) k hk]
        by_cases hkn : k = n
        · subst hkn
          rw [hf']
          simp
        · congr 1
          simp only [decide_eq_decide]
          omega
  have hkey := key 8 (le_refl _) k hk
  rw [show (byteOf f).bv = (List.range 8).foldl
      (fun acc j => if f j then acc ||| BitVec.twoPow 8 j else acc) 0#8 from rfl, hkey]
  simp [hk]

theorem byteOf_congr {f g : Nat → Bool} (h : ∀ t, t < 8 → f t = g t) : byteOf f = byteOf g := by
  apply Std.U8.bv_eq_imp_eq
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [byteOf_get f k hk, byteOf_get g k hk, h k hk]

theorem byteOf_bits (x : Std.U8) : byteOf (fun j => x.bv.getLsbD j) = x := by
  apply Std.U8.bv_eq_imp_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact byteOf_get _ i hi

theorem bv_getElem!_eq_getLsbD {w : Nat} (b : BitVec w) (j : Nat) :
    b[j]! = b.getLsbD j := by
  by_cases h : j < w
  · rw [BitVec.getElem!_eq_getElem b j h]
    rfl
  · rw [BitVec.getElem!_eq_false b j (by omega)]
    rw [BitVec.getLsbD_of_ge b j (by omega)]

/-- Byte `j` of the lane-major serialisation of a state: byte `j % 8` of
    lane `j / 8`, little-endian within the lane. -/
def squeezeByteAt (s : Lanes) (j : Nat) : Std.U8 :=
  ⟨(BitVec.toLEBytes (s.val[j / 8]!).bv)[j % 8]!⟩

/-- Reading the state as a flat bit string agrees with reading it byte by
    byte, as long as the byte is inside the state. -/
theorem squeezeByteAt_bit (s : Lanes) (j t : Nat) (ht : t < 8) :
    (squeezeByteAt s j).bv.getLsbD t = laneBitAt s (8 * j + t) := by
  have hd : (8 * j + t) / 64 = j / 8 := by omega
  have hm : (8 * j + t) % 64 = 8 * (j % 8) + t := by omega
  have h320 : (8 * j + t) / 320 = ((8 * j + t) / 64) / 5 := by
    rw [Nat.div_div_eq_div_mul]
  rw [laneBitAt, laneBit, h320, hd, hm,
    show 5 * ((j / 8) / 5) + (j / 8) % 5 = j / 8 from by omega]
  show ((BitVec.toLEBytes (s.val[j / 8]!).bv)[j % 8]!).getLsbD t = _
  rw [← bv_getElem!_eq_getLsbD, ← bv_getElem!_eq_getLsbD]
  exact BitVec.getElem!_toLEBytes _ (j % 8) t ht

/-- Output byte `i`: permute `i / rate` more times, then read byte `i % rate`
    of the rate portion of the state. -/
def squeezeLanes (OUTPUT_LEN : Std.Usize) (s : Lanes) (rate : Nat) :
    Std.Array Std.U8 OUTPUT_LEN :=
  mkArr OUTPUT_LEN (fun i => byteOf (fun t =>
    laneBitAt (keccakFLanes^[i / rate] s) (8 * (i % rate) + t)))

theorem squeezeLanes_getElem (OUTPUT_LEN : Std.Usize) (s : Lanes) (rate : Nat)
    (k : Nat) (hk : k < OUTPUT_LEN.val) :
    (squeezeLanes OUTPUT_LEN s rate).val[k]!
      = squeezeByteAt (keccakFLanes^[k / rate] s) (k % rate) := by
  rw [squeezeLanes, mkArr_get OUTPUT_LEN _ hk]
  refine (byteOf_congr ?_).trans (byteOf_bits _)
  intro t ht
  rw [squeezeByteAt_bit _ (k % rate) t ht]

/-- `KECCAK[c]` at the byte level: absorb, then squeeze. -/
def keccakLanes (OUTPUT_LEN : Std.Usize) (rate : Nat) (delim : Std.U8)
    (msg : List Std.U8) : Std.Array Std.U8 OUTPUT_LEN :=
  squeezeLanes OUTPUT_LEN (absorbLanes rate delim msg) rate

end LibcruxIotSha3.SpongeModel
