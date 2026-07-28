/-
  # Aeneas-Result lifts of `Lane2U32.interleave` / `Lane2U32.deinterleave`.

  Bridges the impl's 13-stage bit-deposit code (`Extraction/Funs.lean` lines
  116-163 and 3993-4065) to the pure-`BitVec` models `interleave_bv` /
  `deinterleave_bv` defined at the top of this file.

  Both Triples post:
  - `interleave_spec`:  the two output halves equal `interleave_bv  lo hi`.
  - `deinterleave_spec`: the two output halves equal `deinterleave_bv e o`.

  Composing with `interleave_bv_lift_eq` / `deinterleave_bv_lift_eq` (also
  in this file) recovers the LE-concatenated `u64` form consumed by the
  byte-bridge layer in `Sponge/Bytes.lean`.

  Technique: a pure `hax_mvcgen` walk through ~30 `Std.U32`/`Std.U64` ops,
  finishing with a single `BitVec` equality closed by `bv_decide` (after
  exposing the underlying `.bv` content through `Std.U32.bv_eq_imp_eq` /
  `Std.U64.bv_eq_imp_eq` + `UScalar.bv_*`).

  The BV-pure identity layer (`interleave_bv`, `deinterleave_bv`,
  `lift_lane_bv_xor`, `interleave_bv_lift_eq`, `deinterleave_bv_lift_eq`)
  lives in this file (rather than in `Sponge/Bytes.lean`) so that
  `Sponge/Bytes.lean` can depend on `Sponge/LoopSpecs.lean` (which itself
  imports this file) without an import cycle.
-/
import LibcruxIotSha3.Sponge.Opaque

open Aeneas Aeneas.Std Result Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

set_option mvcgen.warning false

open libcrux_iot_sha3.Foundation

-- Defensive seal re-issue: no proof in this file may unfold either side
-- of Bridge 1.
set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ## Load-bearing bit-level identities (BV form)

Three pure-BitVec identities anchor the byte ↔ interleaved-lane bridge:

1. **`lift_lane_bv_xor`** — `lift_lane_bv` distributes over per-half XOR.
2. **`interleave_bv_lift_eq`** — the impl's 13-stage even/odd-bit deposit
   (computing `Lane2U32.interleave (lo, hi)`'s halves) round-trips
   through `lift_lane_bv` to recover `(hi <<32) ||| lo`, i.e.
   `u64_from_le_bytes (lo.toLEBytes ++ hi.toLEBytes)`.
3. **`deinterleave_bv_lift_eq`** — the dual: deinterleave's two output
   halves equal the LE-byte split of `lift_lane_bv even_bits odd_bits`.

All three are discharged purely by `bv_decide` after the relevant unfold. -/

/-- `lift_lane_bv` distributes over per-half XOR.  Pure `bv_decide`. -/
theorem lift_lane_bv_xor (z0 z1 w0 w1 : BitVec 32) :
    lift_lane_bv z0 z1 ^^^ lift_lane_bv w0 w1 =
      lift_lane_bv (z0 ^^^ w0) (z1 ^^^ w1) := by
  unfold lift_lane_bv spread_to_even
  bv_decide

/-- Pure-BitVec model of the impl's `Lane2U32.interleave` body
    (Extraction/Funs.lean:116-163), expressed as a function from
    `(lo, hi) : BitVec 32 × BitVec 32` to the resulting `(even, odd)`
    halves.

    This mirrors the 13-stage bit-deposit (six per parity) applied to
    `lane_u64 := (hi << 32) ||| lo`. -/
def interleave_bv (lo hi : BitVec 32) : BitVec 32 × BitVec 32 :=
  let lane_u64 : BitVec 64 := (hi.zeroExtend 64) <<< 32 ||| lo.zeroExtend 64
  let even_bits := lane_u64 &&& 6148914691236517205#64
  let even_bits := even_bits ^^^ (even_bits >>> 1)
  let even_bits := even_bits &&& 3689348814741910323#64
  let even_bits := even_bits ^^^ (even_bits >>> 2)
  let even_bits := even_bits &&& 1085102592571150095#64
  let even_bits := even_bits ^^^ (even_bits >>> 4)
  let even_bits := even_bits &&& 71777214294589695#64
  let even_bits := even_bits ^^^ (even_bits >>> 8)
  let even_bits := even_bits &&& 281470681808895#64
  let even_bits := even_bits ^^^ (even_bits >>> 16)
  let even_bits := even_bits &&& 4294967295#64
  let odd_bits := (lane_u64 >>> 1) &&& 6148914691236517205#64
  let odd_bits := odd_bits ^^^ (odd_bits >>> 1)
  let odd_bits := odd_bits &&& 3689348814741910323#64
  let odd_bits := odd_bits ^^^ (odd_bits >>> 2)
  let odd_bits := odd_bits &&& 1085102592571150095#64
  let odd_bits := odd_bits ^^^ (odd_bits >>> 4)
  let odd_bits := odd_bits &&& 71777214294589695#64
  let odd_bits := odd_bits ^^^ (odd_bits >>> 8)
  let odd_bits := odd_bits &&& 281470681808895#64
  let odd_bits := odd_bits ^^^ (odd_bits >>> 16)
  let odd_bits := odd_bits &&& 4294967295#64
  (even_bits.truncate 32, odd_bits.truncate 32)

/-- Pure-BitVec model of the impl's `Lane2U32.deinterleave` body
    (Extraction/Funs.lean:3993-4065), expressed as a function from
    `(even, odd) : BitVec 32 × BitVec 32` (the two halves of an
    interleaved lane) to the resulting `(lo, hi)` 32-bit pair that an
    LE-byte split of the lifted u64 would yield. -/
def deinterleave_bv (even_bits odd_bits : BitVec 32) : BitVec 32 × BitVec 32 :=
  let evlo := even_bits &&& 65535#32
  let evlo := evlo ^^^ (evlo <<< 16)
  let evlo := evlo &&& 65535#32
  let evlo := evlo ^^^ (evlo <<< 8)
  let evlo := evlo &&& 16711935#32
  let evlo := evlo ^^^ (evlo <<< 4)
  let evlo := evlo &&& 252645135#32
  let evlo := evlo ^^^ (evlo <<< 2)
  let evlo := evlo &&& 858993459#32
  let evlo := evlo ^^^ (evlo <<< 1)
  let evlo5 := evlo &&& 1431655765#32
  let evhi := even_bits >>> 16
  let evhi := evhi ^^^ (evhi <<< 16)
  let evhi := evhi &&& 65535#32
  let evhi := evhi ^^^ (evhi <<< 8)
  let evhi := evhi &&& 16711935#32
  let evhi := evhi ^^^ (evhi <<< 4)
  let evhi := evhi &&& 252645135#32
  let evhi := evhi ^^^ (evhi <<< 2)
  let evhi := evhi &&& 858993459#32
  let evhi := evhi ^^^ (evhi <<< 1)
  let evhi5 := evhi &&& 1431655765#32
  let odlo := odd_bits &&& 65535#32
  let odlo := odlo ^^^ (odlo <<< 16)
  let odlo := odlo &&& 65535#32
  let odlo := odlo ^^^ (odlo <<< 8)
  let odlo := odlo &&& 16711935#32
  let odlo := odlo ^^^ (odlo <<< 4)
  let odlo := odlo &&& 252645135#32
  let odlo := odlo ^^^ (odlo <<< 2)
  let odlo := odlo &&& 858993459#32
  let odlo := odlo ^^^ (odlo <<< 1)
  let odlo5 := odlo &&& 1431655765#32
  let odhi := odd_bits >>> 16
  let odhi := odhi ^^^ (odhi <<< 16)
  let odhi := odhi &&& 65535#32
  let odhi := odhi ^^^ (odhi <<< 8)
  let odhi := odhi &&& 16711935#32
  let odhi := odhi ^^^ (odhi <<< 4)
  let odhi := odhi &&& 252645135#32
  let odhi := odhi ^^^ (odhi <<< 2)
  let odhi := odhi &&& 858993459#32
  let odhi := odhi ^^^ (odhi <<< 1)
  let odhi5 := odhi &&& 1431655765#32
  let lo_out := evlo5 ||| (odlo5 <<< 1)
  let hi_out := evhi5 ||| (odhi5 <<< 1)
  (lo_out, hi_out)

/-- Load-bearing bit-level bridge: lifting the two halves produced by
    `interleave_bv lo hi` recovers the LE-concatenated 64-bit form
    `(hi << 32) ||| lo`.  Discharged by `bv_decide`. -/
theorem interleave_bv_lift_eq (lo hi : BitVec 32) :
    let (e, o) := interleave_bv lo hi
    lift_lane_bv e o = (hi.zeroExtend 64) <<< 32 ||| lo.zeroExtend 64 := by
  simp only [interleave_bv, lift_lane_bv, spread_to_even]
  bv_decide

/-- Load-bearing bit-level bridge: lifting two interleaved halves equals
    the LE-concatenated form of the deinterleave halves.  Discharged by
    `bv_decide`. -/
theorem deinterleave_bv_lift_eq (even_bits odd_bits : BitVec 32) :
    let (lo, hi) := deinterleave_bv even_bits odd_bits
    (hi.zeroExtend 64) <<< 32 ||| lo.zeroExtend 64 =
      lift_lane_bv even_bits odd_bits := by
  simp only [deinterleave_bv, lift_lane_bv, spread_to_even]
  bv_decide

/-- Bridge: `0#32 ++ x` (BV64) equals `x.setWidth 64`. Used to feed
    the impl's `as_u64` cast (which Lean computes as `0#32 ++ x`) into
    `bv_decide` (which doesn't natively destructure `BitVec.append`). -/
private theorem zero_append_eq_setWidth_32 (x : BitVec 32) :
    (0#32 ++ x : BitVec 64) = x.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_setWidth]
  have hbnd : x.toNat < 2 ^ 64 := by
    have := x.isLt; omega
  simp
  omega

/-- Bridge: `x ++ 0#32` (BV64) equals `(x.setWidth 64) <<< 32`. -/
private theorem append_zero_32_eq_shiftLeft_setWidth (x : BitVec 32) :
    (x ++ 0#32 : BitVec 64) = (x.setWidth 64) <<< 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth]
  simp [Nat.shiftLeft_eq]
  have hbnd : x.toNat < 2 ^ 32 := x.isLt
  have h64 : x.toNat * 2 ^ 32 < 2 ^ 64 := by
    have : x.toNat * 2^32 < 2^32 * 2^32 :=
      Nat.mul_lt_mul_of_lt_of_le hbnd (le_refl _) (by decide)
    omega
  omega


/-! ## Aeneas-`Result` lift of `Lane2U32.interleave`. -/
@[spec]
theorem lane.Lane2U32.interleave_spec (self : lane.Lane2U32) :
    ⦃ ⌜ True ⌝ ⦄
    lane.Lane2U32.interleave self
    ⦃ ⇓ r => ⌜ ((r.val[0]!).bv, (r.val[1]!).bv) =
                interleave_bv (self.val[0]!).bv (self.val[1]!).bv ⌝ ⦄ := by
  have h0 : (0 : Nat) < self.val.length := by simp
  have h1 : (1 : Nat) < self.val.length := by simp
  have h0_eq : self.val[0]! = self.val[0]'h0 := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h0]; rfl
  have h1_eq : self.val[1]! = self.val[1]'h1 := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  unfold lane.Lane2U32.interleave
  unfold libcrux_secrets.U32.Insts.Libcrux_secretsIntCastOps.as_u64
  unfold libcrux_secrets.U64.Insts.Libcrux_secretsIntCastOps.as_u32
  unfold lane.Lane2U32.Insts.CoreOpsIndexIndexUsizeU32.index
  unfold lane.Lane2U32.from_ints
  hax_mvcgen
  all_goals
    first
    | scalar_tac
    | (simp only [interleave_bv, Std.UScalar.cast,
                  Std.Array.make,
                  List.getElem!_cons_zero, List.getElem!_cons_succ,
                  Std.U32.bv, Std.U64.bv,
                  Std.UScalarTy.U32_numBits_eq, Std.UScalarTy.U64_numBits_eq,
                  Std.U64.ofNat_bv,
                  show ((0#usize : Std.Usize).val) = 0 from rfl,
                  show ((1#usize : Std.Usize).val) = 1 from rfl,
                  show (1#i32).toNat  = 1 from rfl,
                  show (2#i32).toNat  = 2 from rfl,
                  show (4#i32).toNat  = 4 from rfl,
                  show (8#i32).toNat  = 8 from rfl,
                  show (16#i32).toNat = 16 from rfl,
                  show (32#i32).toNat = 32 from rfl,
                  *]
       refine Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩ <;> rw [BitVec.or_comm])

/-! ## Aeneas-`Result` lift of `Lane2U32.deinterleave`. -/
@[spec]
theorem lane.Lane2U32.deinterleave_spec (self : lane.Lane2U32) :
    ⦃ ⌜ True ⌝ ⦄
    lane.Lane2U32.deinterleave self
    ⦃ ⇓ r => ⌜ ((r.val[0]!).bv, (r.val[1]!).bv) =
                deinterleave_bv (self.val[0]!).bv (self.val[1]!).bv ⌝ ⦄ := by
  have h0 : (0 : Nat) < self.val.length := by simp
  have h1 : (1 : Nat) < self.val.length := by simp
  have h0_eq : self.val[0]! = self.val[0]'h0 := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h0]; rfl
  have h1_eq : self.val[1]! = self.val[1]'h1 := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  unfold lane.Lane2U32.deinterleave
  hax_mvcgen
  all_goals
    first
    | scalar_tac
    | (simp only [deinterleave_bv, Std.Array.make,
                  List.getElem!_cons_zero, List.getElem!_cons_succ,
                  Std.U32.bv,
                  Std.UScalarTy.U32_numBits_eq,
                  Std.U32.ofNat_bv,
                  show ((0#usize : Std.Usize).val) = 0 from rfl,
                  show ((1#usize : Std.Usize).val) = 1 from rfl,
                  show (1#i32).toNat  = 1 from rfl,
                  show (2#i32).toNat  = 2 from rfl,
                  show (4#i32).toNat  = 4 from rfl,
                  show (8#i32).toNat  = 8 from rfl,
                  show (16#i32).toNat = 16 from rfl,
                  *])

end libcrux_iot_sha3.Sponge
