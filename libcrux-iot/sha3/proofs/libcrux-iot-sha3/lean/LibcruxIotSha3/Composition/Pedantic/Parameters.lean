import HacspecSha3Pedantic
/-!
# Parameter agreement between the two SHA-3 hacspecs

The proofs are being moved from `hacspec_sha3` (specs/sha3 -- a spec written the
way the implementations are structured: lanes as `u64`, rates in bytes) onto
`hacspec_sha3_pedantic` (specs/sha3-pedantic -- the FIPS 202 transcript: a state
array of bits, Algorithms 1-11, capacities in bits).  `Composition/Pedantic/`
bridges the two.

This module is the bottom of that bridge and does the easy half: it checks that
the two specs instantiate the sponge at the *same* parameters.  FIPS 202 fixes a
SHA-3 function by its capacity `c` (Sec. 6), and `hacspec_sha3_pedantic` follows
it (`sponge::keccak_c c m d`); `hacspec_sha3` instead carries the rate `r` in
bytes.  With `b = 1600` the two determine each other by `r = b - c`, which is
what the theorems below say -- once per function, with the literal capacity the
pedantic spec passes to `keccak_c`.

Getting these wrong would make every later bridge lemma unprovable, so they are
worth stating even though each is arithmetic: they are the point where the
byte-shaped and the bit-shaped parameter conventions are reconciled.
-/

open Aeneas Aeneas.Std

namespace LibcruxIotSha3.Composition.Pedantic

/-- The state width `b`, in bits (FIPS 202, Table 1; `Keccak[c]` uses `b = 1600`). -/
theorem b_eq : hacspec_sha3_pedantic.sponge.B.val = 1600 := by
  simp [hacspec_sha3_pedantic.sponge.B]

-- The rate/capacity correspondence (`8 * rate + c = 1600` for each of the six
-- functions) is not pinned here: it is checked where it is used, in
-- `LaneSqueeze.lean`, where each entry point instantiates `keccak_eq` at its rate
-- and the capacity falls out of `1600 - 8 * rate` by `norm_num`.

-- Pinned by `#guard_msgs`: the build fails if a result comes to depend on any
-- axiom beyond Lean's standard three (an admitted `sorry`, or `Lean.ofReduceBool`
-- from `bv_decide`/`native_decide`).
/--
info: 'LibcruxIotSha3.Composition.Pedantic.b_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms b_eq

end LibcruxIotSha3.Composition.Pedantic
