/-
  # `Vector/Portable/Arithmetic/BvMasks.lean` — bitvector-mask identities
  used by `arithmetic.rs` Triples.

  Currently exports a single identity needed by
  `get_n_least_significant_bits_spec`.
-/
import Mathlib.Tactic.IntervalCases

namespace libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks
/-- The 32-bit BV mask `(1 <<< n) - 1` has `.toNat = 2^n - 1` for any
    `n ≤ 16` (and in fact for `n < 32`, but 16 is what L0.1 needs).

    Proof: enumerate the 17 cases `n ∈ {0, …, 16}` and discharge each
    by `decide` on the closed BV expression. Mediates the
    `interval_cases` use that was previously inline in
    `Equivalence/L0_FieldArith.lean`. -/
theorem mask_pow2_minus_one_toNat (n : Nat) (h : n ≤ 16) :
    ((1#32 <<< n) - 1#32).toNat = 2 ^ n - 1 := by
  interval_cases n <;> decide

end libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks