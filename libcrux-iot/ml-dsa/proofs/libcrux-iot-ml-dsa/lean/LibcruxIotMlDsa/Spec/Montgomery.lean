import LibcruxIotMlDsa.Spec.Parameters

/-!
# ML-DSA Montgomery keystones

The implementation works in the Montgomery domain with radix `R = 2³²`; the
clean spec (`Spec/Pure.lean`) does not. The equivalence proof therefore strips
`R` via the lift (`Spec/Lift.lean`) and reconciles per-seam `R`-factors.

All constants below are numerically verified and pinned here by
elaboration-time `#guard` (no axioms). The load-bearing relations are restated
as `ZMod q` / `ZMod R` `theorem`s for use inside proofs.
-/

namespace libcrux_iot_ml_dsa.Spec.Montgomery
open libcrux_iot_ml_dsa.Spec.Parameters

/-- Montgomery radix: the impl's `montgomery_reduce_element` shifts by 32. -/
abbrev R : Nat := 2 ^ 32

/-- `R mod q`. -/
abbrev RmodQ : Nat := 4193792

/-- `R⁻¹ mod q` — the logical effect of one `montgomery_reduce`
    (`mont_red value ≡ value · 8265825 (mod q)`). -/
abbrev RINV : Nat := 8265825

/-- `-q⁻¹ mod R` (`simd::traits::INVERSE_OF_MODULUS_MOD_MONTGOMERY_R`),
    used inside `montgomery_reduce_element`. -/
abbrev QPRIME : Nat := 58728449

/-- `256⁻¹ mod q` — the clean spec's `reduce_polynomial` scale. -/
abbrev INV256 : Nat := 8347681

/-- `R² · 256⁻¹ mod q` — the impl's `invert_ntt_montgomery` finalize constant
    (`montgomery_multiply_by_constant(·, 41978)`). -/
abbrev INTT_FINAL : Nat := 41978

#guard (R % Q) = RmodQ
#guard (R * RINV) % Q = 1                 -- R · R⁻¹ ≡ 1 (mod q)
#guard (QPRIME * Q) % R = 1               -- q' · q ≡ 1 (mod R)
#guard (256 * INV256) % Q = 1             -- 256 · 256⁻¹ ≡ 1 (mod q)
#guard (R * R * INV256) % Q = INTT_FINAL  -- 41978 = R²·256⁻¹ (mod q)
#guard (ZETA ^ 512) % Q = 1               -- ζ is a 512-th root of unity …
#guard (ZETA ^ 256) % Q = Q - 1           -- … and primitive (ζ²⁵⁶ = −1)

/-! ### L0 `ZMod`-form keystones (signed Montgomery reduction).

    These restate the pinned `#guard`s above as `ZMod q` / `Int`-divisibility
    `theorem`s consumed by `Vector.Portable.Arithmetic`'s
    `montgomery_reduce_element_spec`. Stated via mediated `ZMod`/`Int.ModEq`
    lemmas (no `decide` on `ZMod Q`). -/

/-- `q' · q ≡ 1 (mod R)` as an `Int`-level divisibility fact (the cancellation
    that makes `value - k·q` vanish in the low 32 bits). The impl chooses
    `k ≡ value · q' (mod R)`, so `k · q ≡ value · (q' · q) ≡ value (mod R)`. -/
theorem qprime_q_emod_R :
    ((QPRIME : Int) * (Q : Int)) % (R : Int) = 1 := by
  have h : (QPRIME * Q) % R = 1 := by decide
  exact_mod_cast h

/-- `R · R⁻¹ ≡ 1 (mod q)` in `ZMod q`: the radix and its inverse cancel. -/
theorem R_RINV_cast_eq_one :
    ((R : ZMod Q) * (RINV : ZMod Q)) = 1 := by
  have h : ((R * RINV : Nat) : ZMod Q) = ((1 : Nat) : ZMod Q) := by
    rw [ZMod.natCast_eq_natCast_iff]
    show (R * RINV) % Q = 1 % Q
    decide
  push_cast at h
  simpa using h

/-- **The L0 algebraic keystone (signed Montgomery reduction).**

    Given that `value - k · q` is divisible by `R = 2³²` (the low-bit
    cancellation the impl arranges), the Montgomery quotient
    `res := (value - k·q) / R` satisfies, in `ZMod q`,

      `(res : ZMod q) = (value : ZMod q) · (R⁻¹ : ZMod q)`.

    Proof sketch: `res · R = value - k·q` exactly (from divisibility), so
    `(res : ZMod q) · R = value` in `ZMod q` (the `k·q` term is `0`); multiply
    by `R⁻¹` and use `R · R⁻¹ = 1`. -/
theorem mont_reduce_zmod
    (value k res : Int)
    (h_res_R : res * (R : Int) = value - k * (Q : Int)) :
    (res : ZMod Q) = (value : ZMod Q) * (RINV : ZMod Q) := by
  -- Cast the exact identity into `ZMod Q`; the `k·q` term vanishes.
  have h_cast : (res : ZMod Q) * (R : ZMod Q) = (value : ZMod Q) := by
    have h := congrArg (Int.cast : Int → ZMod Q) h_res_R
    push_cast at h
    -- (Q : ZMod Q) = 0 kills the k·q term.
    simpa [ZMod.natCast_self] using h
  -- Multiply both sides by RINV and collapse R · RINV = 1.
  calc (res : ZMod Q)
      = (res : ZMod Q) * ((R : ZMod Q) * (RINV : ZMod Q)) := by rw [R_RINV_cast_eq_one, mul_one]
    _ = ((res : ZMod Q) * (R : ZMod Q)) * (RINV : ZMod Q) := by ring
    _ = (value : ZMod Q) * (RINV : ZMod Q) := by rw [h_cast]

/-- Integer identity: when `(a - b) % R = 0`, we have `a / R - b / R = (a - b) / R`.

    Used by `Vector.Portable.Arithmetic.montgomery_reduce_element_spec` to
    collapse the pair of shifts `(value >> 32) - (km >> 32)` into the single
    Montgomery quotient `(value - km) / R`. -/
theorem sub_div_of_emod_eq_zero
    (a b R : Int) (hRne : R ≠ 0) (h_dvd : (a - b) % R = 0) :
    a / R - b / R = (a - b) / R := by
  have hd : R ∣ (a - b) := Int.dvd_of_emod_eq_zero h_dvd
  obtain ⟨q, hq⟩ := hd
  rw [hq, Int.mul_ediv_cancel_left q hRne]
  have h_a : a = b + R * q := by omega
  rw [h_a, Int.add_mul_ediv_left b q hRne]
  ring

end libcrux_iot_ml_dsa.Spec.Montgomery
