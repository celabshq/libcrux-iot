import LibcruxIotSha3.Composition.Pedantic.Iota
import LibcruxIotSha3.Tables
/-!
# The round constants: the LFSR against the table

The implementations carry the twenty-four round constants as a table of `u64`s,
the way implementations do.  `hacspec_sha3_pedantic` does not carry them at all:
it derives each bit from the linear feedback shift register of FIPS 202
Algorithm 5, as the standard defines it (`rcBitAt`, built on `rcOf`).

The two therefore have to be reconciled once, and this module is that once.  It
is a finite check -- 24 constants, 64 bits each -- and it is done by `decide`,
so the kernel replays the shift register itself.  No `native_decide`: the whole
development stays on Lean's three standard axioms.

Bit `z` of round constant `i_r` is `rc(j + 7 i_r)` when `z = 2^j - 1` for some
`j ≤ l`, and zero otherwise; that the table's other 57 bits per constant really
are zero is part of what is checked here.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

namespace LibcruxIotSha3.Composition.Pedantic

set_option maxRecDepth 100000 in
/-- The round constant of round `i_r`, bit by bit: the shift register of
    Algorithm 5 computes exactly the table `hacspec_sha3` carries. -/
theorem rcBitAt_table : ∀ i_r : Nat, i_r < 24 → ∀ z : Nat, z < 64 →
    rcBitAt (i_r : Int) z
      = ((libcrux_iot_sha3.roundConstants).val[i_r]!).bv.getLsbD z := by
  simp only [libcrux_iot_sha3.roundConstants]
  decide

-- Pinned by `#guard_msgs`: the build fails if this comes to depend on any axiom
-- beyond Lean's standard three -- in particular on `Lean.ofReduceBool`, which is
-- what `native_decide` would have added.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.rcBitAt_table' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rcBitAt_table

end LibcruxIotSha3.Composition.Pedantic
