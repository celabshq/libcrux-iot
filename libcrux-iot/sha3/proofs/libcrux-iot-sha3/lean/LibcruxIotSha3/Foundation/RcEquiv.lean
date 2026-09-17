/-
  Round constant equivalence.

  The implementation stores each Keccak round constant as two 32-bit
  interleaved halves at indices 0..23 of `RC_INTERLEAVED_0` /
  `RC_INTERLEAVED_1`. `RcTable` carries the full 64-bit constants. We need
  the bit-interleaved combination of the two halves to equal the table's
  entry at every round.
-/
import LibcruxIotSha3.Foundation.Lift
import LibcruxIotSha3.Tables

open Aeneas Aeneas.Std libcrux_iot_sha3

namespace libcrux_iot_sha3.Foundation

/-- Auxiliary `Fin 24` form. The interleaved-RC and `ROUND_CONSTANTS` arrays
  are `@[irreducible]`, so we need to unfold them explicitly. -/
private theorem rc_equiv_aux (i : Fin 24) :
    lift_lane_bv
      (keccak.RC_INTERLEAVED_0.val[i.val]!).bv
      (keccak.RC_INTERLEAVED_1.val[i.val]!).bv =
    (roundConstants.val[i.val]!).bv := by
  revert i
  unfold keccak.RC_INTERLEAVED_0 keccak.RC_INTERLEAVED_1 roundConstants
  decide

/-- Round constant equivalence for `i : Nat` with `i < 24`. -/
theorem rc_equiv (i : Nat) (hi : i < 24) :
    lift_lane_bv
      (keccak.RC_INTERLEAVED_0.val[i]!).bv
      (keccak.RC_INTERLEAVED_1.val[i]!).bv =
    (roundConstants.val[i]!).bv :=
  rc_equiv_aux ⟨i, hi⟩

end libcrux_iot_sha3.Foundation
