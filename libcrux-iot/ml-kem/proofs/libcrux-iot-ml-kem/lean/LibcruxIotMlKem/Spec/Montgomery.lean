/-
  # `Util.Montgomery` — Montgomery-form algebraic bridges

  Pure `Int`-arithmetic helpers anchoring the Montgomery-reduction
  family of Triples (L0.3, L0.4, L2.x, L6.x).

  This is **the L0.3 keystone module**. It contains the integer-level
  "given that `(value + k·q) % R = 0`, the Montgomery identity
  holds" lemma referenced from
  Tier 1. Closing this file unblocks `montgomery_reduce_element_spec`
  and (transitively) every downstream Triple that reasons about
  values in the Montgomery domain.

  Conventions: `q = 3329`, `R = 2^16`. The lemmas are stated on
  `Int` (not `Nat`), since signed Montgomery reduction in libcrux-iot
  ML-KEM operates on `Std.I32` values whose `.val : Int` can be
  negative.

  The downstream user uses `mont_reduce_int_form` immediately after
  reducing the impl Triple to an `Int`-level chain via the BV-to-Int
  bridge for `IScalar.cast`, `wrapping_mul`, and `>>>` (arithmetic
  shift right).
-/
-- Mathlib footprint here is BARRIER-LAYER ONLY. Consumers above the
-- abstraction barrier use only the `modq_eq`-shaped lemmas exported
-- from this file; they MUST NOT import Mathlib themselves.
-- `Linarith` dropped; both prior `linarith` calls migrated to `omega`
-- (core Lean), which handles linear int arithmetic with the same or
-- greater capability for the goals this file proves.
import LibcruxIotMlKem.Spec.ModularArith
import LibcruxIotMlKem.Spec.NumericKeystones
import Mathlib.Tactic.Ring

namespace libcrux_iot_ml_kem.Spec.Montgomery
open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.NumericKeystones
/-- **`mont_reduce_int_form`** — the L0.3 algebraic keystone.

    Given that `value + k · q` is divisible by `R = 2^16` (as an
    integer), the Montgomery quotient `(value + k · q) / R` satisfies
    `quotient · R ≡ value (mod q)`.

    This is the integer-arithmetic content of the signed-Montgomery-
    reduction correctness argument. The `+` (vs `-`) here matches the
    impl's two's-complement choice of `k`: the impl computes `k` so
    that `value + k · q` cancels in the low 16 bits (the
    `(62209 · 3329) % 2^16 = 1` keystone makes the choice
    `k := value · 62209 (mod 2^16)` give that cancellation, with the
    sign absorbed into the wrap-around).

    § "Reusable infrastructure" Tier 1. -/
theorem mont_reduce_int_form
    (value k : Int)
    (h_div : (value + k * 3329) % (2^16 : Int) = 0) :
    modq_eq ((value + k * 3329) / (2^16 : Int) * (2^16 : Int)) value 3329 := by
  -- Strategy: from `h_div`, get `(value + k*3329) = 2^16 * m` for some `m`.
  -- Then `(value + k*3329) / 2^16 = m`, so
  -- `m * 2^16 - value = k * 3329`, which is divisible by 3329.
  unfold modq_eq
  have h_dvd : (2^16 : Int) ∣ (value + k * 3329) :=
    Int.dvd_of_emod_eq_zero h_div
  obtain ⟨m, hm⟩ := h_dvd
  have h_R_ne_zero : (2^16 : Int) ≠ 0 := by decide
  have h_div_eq : (value + k * 3329) / (2^16 : Int) = m := by
    rw [hm]
    exact Int.mul_ediv_cancel_left m h_R_ne_zero
  rw [h_div_eq]
  -- Goal: (m * 2^16 - value) % 3329 = 0.
  -- From `hm : value + k * 3329 = 2^16 * m`, we get
  -- `m * 2^16 - value = k * 3329`.
  have h_eq : m * (2^16 : Int) - value = k * 3329 := by omega
  rw [h_eq]
  exact Int.mul_emod_left _ _

/-- **`sub_div_of_emod_eq_zero`** — auxiliary used by L0.3.

    When `(a - b) % R = 0` (i.e. `a ≡ b (mod R)`), the difference of
    floored quotients `a / R - b / R` equals the exact quotient
    `(a - b) / R`. This is what bridges the impl's two separate
    arithmetic-shift-right operations (`value >> 16` and
    `(k · q) >> 16`) to the single mathematical quotient
    `(value - k · q) / 2^16` that the keystone uses.

    Used by `montgomery_reduce_element_spec` (L0.3) immediately after
    the BV-level reduction places the goal in `Int` form. -/
theorem sub_div_of_emod_eq_zero
    (a b R : Int) (hRne : R ≠ 0) (h_dvd : (a - b) % R = 0) :
    a / R - b / R = (a - b) / R := by
  have hd : R ∣ (a - b) := Int.dvd_of_emod_eq_zero h_dvd
  obtain ⟨q, hq⟩ := hd
  rw [hq, Int.mul_ediv_cancel_left q hRne]
  have h_a : a = b + R * q := by omega
  rw [h_a, Int.add_mul_ediv_left b q hRne]
  ring

/-- **Bridge: old → new Montgomery modq form.**

    Given the old-form modular equation `r * 2^16 ≡ v (mod 3329)`,
    derive the new-form `r ≡ v * 169 (mod 3329)` via the
    `mont_R_inv_q` keystone `(2^16 * 169) % 3329 = 1`.

    The keystone implies `r * (2^16 * 169) ≡ r (mod 3329)`, hence
    multiplying both sides of the old form by 169 yields the new form.

    Used by L0.4 `montgomery_multiply_fe_by_fer_spec` and any
    downstream Triple that needs to convert from the
    `r·R ≡ v (mod q)` shape (impl-native) to the
    `r ≡ v·R⁻¹ (mod q)` shape (F*-native, with `R⁻¹ = 169`). -/
theorem modq_R_to_169
    (r v : Int) (h : modq_eq (r * (2^16 : Int)) v 3329) :
    modq_eq r (v * 169) 3329 := by
  unfold modq_eq at h ⊢
  have h_dvd_diff : (3329 : Int) ∣ (r * (2^16 : Int) - v) := Int.dvd_of_emod_eq_zero h
  have h_keystone : ((2^16 : Int) * 169) % 3329 = 1 := by decide
  have h_dvd_keystone : (3329 : Int) ∣ ((2^16 : Int) * 169 - 1) := by
    have : ((2^16 : Int) * 169 - 1) % 3329 = 0 := by
      rw [Int.sub_emod, h_keystone]; decide
    exact Int.dvd_of_emod_eq_zero this
  have h_dvd_r : (3329 : Int) ∣ (r * ((2^16 : Int) * 169) - r) := by
    have h_eq : r * ((2^16 : Int) * 169) - r = r * ((2^16 : Int) * 169 - 1) := by ring
    rw [h_eq]
    exact Dvd.dvd.mul_left h_dvd_keystone r
  have h_dvd_169 : (3329 : Int) ∣ ((r * (2^16 : Int) - v) * 169) :=
    Dvd.dvd.mul_right h_dvd_diff 169
  have h_dvd_final : (3329 : Int) ∣ (r - v * 169) := by
    have h_eq : (r - v * 169)
              = (r * (2^16 : Int) - v) * 169 - (r * ((2^16 : Int) * 169) - r) := by ring
    rw [h_eq]
    exact dvd_sub h_dvd_169 h_dvd_r
  exact Int.emod_eq_zero_of_dvd h_dvd_final

end libcrux_iot_ml_kem.Spec.Montgomery