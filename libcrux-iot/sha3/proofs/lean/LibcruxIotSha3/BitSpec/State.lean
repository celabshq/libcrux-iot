/-
  Pure-Lean state record for the intermediate Keccak spec.

  Mirrors the SHAPE of `libcrux_iot_sha3.state.KeccakState` but has zero
  dependence on Aeneas-extracted types — only `BitVec 32`, `Vector`, and
  `Nat`. This is the impl-side type of the intermediate spec
  (`bit_keccak_spec`); the iso to the Aeneas-side `state.KeccakState`
  lives in `StateIso.lean`.

  The naming-discipline rule from the plan: this file mentions no `lift`,
  `lift_perm`, `impl_perm`, `impl_swap`. Those concepts only enter at the
  algebraic-equivalence bridge to the hacspec (`AlgebraicEquiv.lean`).

  The one Aeneas-side type we keep is `Std.Usize` for the round counter
  `i` — it's a thin `BitVec`-wrapping data type (no `Triple`, `Result`,
  `WP`, or other Aeneas machinery), and matching the impl's `i` type
  makes the iso `KState ↔ state.KeccakState` trivial on this
  field.
-/
import Init.Data.Vector.Basic
import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Notations

namespace libcrux_iot_sha3.BitSpec

/-- A single Keccak lane in bit-interleaved form: two 32-bit halves
    storing the even-bit (`z0`) and odd-bit (`z1`) bits of the lane's
    canonical 64-bit value. Mirror of `libcrux_iot_sha3.lane.Lane2U32`
    (an `Array Std.U32 2`) but as a fresh record. -/
structure Lane where
  z0 : BitVec 32
  z1 : BitVec 32
  deriving DecidableEq, Repr

/-- The full Keccak state, mirroring `libcrux_iot_sha3.state.KeccakState`:

    - `st` — 25 lanes (the Keccak A-array, indexed by `5*y + x` in the
      Rust impl's convention).
    - `c`  — 5 column-XOR scratchpad cells (one per spec column).
    - `d`  — 5 column-difference scratchpad cells (one per spec column).
    - `i`  — round counter (`Nat`, not `Usize`, since this is the pure
      spec universe).

    All `BitVec`/`Vector`-based; no `Aeneas.Std.UScalar`, `Aeneas.Std.Array`,
    or `Lane2U32` anywhere. -/
structure KState where
  st : Vector Lane 25
  c  : Vector Lane 5
  d  : Vector Lane 5
  i  : Aeneas.Std.Usize
  deriving DecidableEq, Repr

/-- The all-zero lane. -/
def Lane.zero : Lane := { z0 := 0, z1 := 0 }

/-- The all-zero state with round counter 0. -/
def KState.zero : KState :=
  { st := Vector.replicate 25 Lane.zero,
    c  := Vector.replicate 5 Lane.zero,
    d  := Vector.replicate 5 Lane.zero,
    i  := 0#usize }

end libcrux_iot_sha3.BitSpec
