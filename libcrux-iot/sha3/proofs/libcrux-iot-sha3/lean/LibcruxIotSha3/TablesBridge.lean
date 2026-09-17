import LibcruxIotSha3.Tables
import HacspecSha3
/-!
# The local constant tables are `hacspec_sha3`'s

`LibcruxIotSha3.Tables` keeps local copies of the two Keccak constant tables --
the round constants `RC[0] … RC[23]` and ρ's rotation offsets -- so that the
proofs need not name `hacspec_sha3`'s.  This file is the one place that still
relates them, and it disappears together with the rest of the `hacspec_sha3`
half of the bridge.
-/

open Aeneas Aeneas.Std

namespace libcrux_iot_sha3

theorem hacspec_roundConstants_eq :
    hacspec_sha3.keccak_f.ROUND_CONSTANTS = roundConstants := by
  simp only [hacspec_sha3.keccak_f.ROUND_CONSTANTS, roundConstants]

theorem hacspec_rhoOffsets_eq :
    hacspec_sha3.keccak_f.RHO_OFFSETS = rhoOffsets := by
  simp only [hacspec_sha3.keccak_f.RHO_OFFSETS, rhoOffsets]

end libcrux_iot_sha3
