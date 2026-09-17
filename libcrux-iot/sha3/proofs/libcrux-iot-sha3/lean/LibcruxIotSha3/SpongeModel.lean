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

/-- Output byte `i`: permute `i / rate` more times, then read byte `i % rate`
    of the rate portion of the state. -/
def squeezeLanes (OUTPUT_LEN : Std.Usize) (s : Lanes) (rate : Nat) :
    Std.Array Std.U8 OUTPUT_LEN :=
  mkArr OUTPUT_LEN (fun i => byteOf (fun t =>
    laneBitAt (keccakFLanes^[i / rate] s) (8 * (i % rate) + t)))

/-- `KECCAK[c]` at the byte level: absorb, then squeeze. -/
def keccakLanes (OUTPUT_LEN : Std.Usize) (rate : Nat) (delim : Std.U8)
    (msg : List Std.U8) : Std.Array Std.U8 OUTPUT_LEN :=
  squeezeLanes OUTPUT_LEN (absorbLanes rate delim msg) rate

end LibcruxIotSha3.SpongeModel
