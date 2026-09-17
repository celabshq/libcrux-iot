/-
  The Keccak round-constant table.

  FIPS 202 does not tabulate the round constants: Algorithm 6 (ι) obtains
  `RC[i_r]` from the shift register of Algorithm 5 (`rc`). Implementations
  tabulate them, and so does this proof -- once, here, so that the two sides
  that need the table share one copy:

    * the implementation stores each constant as two interleaved 32-bit halves
      (`keccak.RC_INTERLEAVED_{0,1}`); `Foundation/RcEquiv.lean` proves the
      interleaving of those halves is this table's entry.
    * the FIPS-202 transcript computes them; `Composition/Pedantic/RoundConstants.lean`
      proves Algorithm 5's LFSR produces exactly this table, by `decide` -- so the
      table is CHECKED against the Standard rather than trusted, and nothing is
      added to the trusted base by writing it down here.

  The file deliberately has no dependency beyond Aeneas, so both of those layers
  can import it without either depending on the other.
-/
import Aeneas

open Aeneas Aeneas.Std

namespace libcrux_iot_sha3

/-- `RC[0] … RC[23]`, the twenty-four round constants of `KECCAK-f[1600]`. -/
@[irreducible]
def roundConstants : Std.Array Std.U64 24#usize :=
  Std.Array.make 24#usize [
    1#u64, 32898#u64, 9223372036854808714#u64, 9223372039002292224#u64,
    32907#u64, 2147483649#u64, 9223372039002292353#u64,
    9223372036854808585#u64, 138#u64, 136#u64, 2147516425#u64, 2147483658#u64,
    2147516555#u64, 9223372036854775947#u64, 9223372036854808713#u64,
    9223372036854808579#u64, 9223372036854808578#u64, 9223372036854775936#u64,
    32778#u64, 9223372039002259466#u64, 9223372039002292353#u64,
    9223372036854808704#u64, 2147483649#u64, 9223372039002292232#u64
    ]

/-- The rotation offsets of ρ, flattened by the `5*y + x` lane layout
    (FIPS 202, the offsets `(t+1)(t+2)/2 mod 64` of Algorithm 2). -/
@[irreducible]
def rhoOffsets : Std.Array Std.U32 25#usize :=
  Std.Array.make 25#usize [
    0#u32, 1#u32, 62#u32, 28#u32, 27#u32, 36#u32, 44#u32, 6#u32, 55#u32,
    20#u32, 3#u32, 10#u32, 43#u32, 25#u32, 39#u32, 41#u32, 45#u32, 15#u32,
    21#u32, 8#u32, 18#u32, 2#u32, 61#u32, 56#u32, 14#u32
    ]

end libcrux_iot_sha3
