/-
  # `Util.ModularArith` — canonical modular-equality predicate for ML-KEM

  Defines `modq_eq a b q := (a - b) % q = 0` and its standard algebraic
  lemma surface (reflexivity, symmetry, transitivity, additive /
  subtractive / constant-multiplicative compatibility, and a bridge
  to `ZMod q`).

  Every L0–L9 Triple postcondition that asserts `a ≡ b (mod q)` uses
  this single named predicate. The subtraction-mod spelling is preferred
  over `a % q = b % q` because it composes additively without side
  conditions.
-/
-- Mathlib footprint here is BARRIER-LAYER ONLY. Consumers of `modq_eq`
-- above the abstraction barrier MUST NOT import Mathlib themselves;
-- they use only the lemmas exported by this module.
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

namespace libcrux_iot_ml_kem.Spec.ModularArith
/-- Canonical modular-equality predicate: `a ≡ b (mod q)` in the
    subtraction-mod spelling.

    Equivalent to `Int.ModEq q a b` (= `a % q = b % q`) but easier to
    discharge directly via `decide` / `scalar_tac` on concrete values. -/
def modq_eq (a b : Int) (q : Int) : Prop := (a - b) % q = 0

variable {a b c k : Int} {q : Int}

@[simp] theorem modq_eq_refl : modq_eq a a q := by
  unfold modq_eq
  simp

theorem modq_eq_symm : modq_eq a b q → modq_eq b a q := by
  unfold modq_eq
  intro h
  have hdvd : q ∣ (a - b) := Int.dvd_of_emod_eq_zero h
  have hdvd' : q ∣ (b - a) := by
    have : (b - a) = -(a - b) := by ring
    rw [this]; exact dvd_neg.mpr hdvd
  exact Int.emod_eq_zero_of_dvd hdvd'

theorem modq_eq_trans : modq_eq a b q → modq_eq b c q → modq_eq a c q := by
  unfold modq_eq
  intro h1 h2
  have hdvd1 : q ∣ (a - b) := Int.dvd_of_emod_eq_zero h1
  have hdvd2 : q ∣ (b - c) := Int.dvd_of_emod_eq_zero h2
  have hdvd : q ∣ (a - c) := by
    have : (a - c) = (a - b) + (b - c) := by ring
    rw [this]; exact dvd_add hdvd1 hdvd2
  exact Int.emod_eq_zero_of_dvd hdvd

theorem modq_eq_add :
    modq_eq a b q → modq_eq c d q → modq_eq (a + c) (b + d) q := by
  unfold modq_eq
  intro h1 h2
  have hdvd1 : q ∣ (a - b) := Int.dvd_of_emod_eq_zero h1
  have hdvd2 : q ∣ (c - d) := Int.dvd_of_emod_eq_zero h2
  have : ((a + c) - (b + d)) = (a - b) + (c - d) := by ring
  rw [this]
  exact Int.emod_eq_zero_of_dvd (dvd_add hdvd1 hdvd2)

theorem modq_eq_sub :
    modq_eq a b q → modq_eq c d q → modq_eq (a - c) (b - d) q := by
  unfold modq_eq
  intro h1 h2
  have hdvd1 : q ∣ (a - b) := Int.dvd_of_emod_eq_zero h1
  have hdvd2 : q ∣ (c - d) := Int.dvd_of_emod_eq_zero h2
  have : ((a - c) - (b - d)) = (a - b) - (c - d) := by ring
  rw [this]
  exact Int.emod_eq_zero_of_dvd (dvd_sub hdvd1 hdvd2)

theorem modq_eq_const_mul :
    modq_eq a b q → modq_eq (k * a) (k * b) q := by
  unfold modq_eq
  intro h
  have hdvd : q ∣ (a - b) := Int.dvd_of_emod_eq_zero h
  have : (k * a - k * b) = k * (a - b) := by ring
  rw [this]
  exact Int.emod_eq_zero_of_dvd (Dvd.dvd.mul_left hdvd k)

/-- Bridge to mathlib's `ZMod` view: `modq_eq a b q` is equivalent to
    `(a : ZMod q) = (b : ZMod q)`. Stated with `q : ℕ` plus an
    explicit cast so we can reuse mathlib's `ZMod.intCast_eq_intCast_iff`
    machinery; the `[NeZero q]` instance keeps the bridge usable on
    every nonzero modulus (in particular `q = 3329`). -/
theorem modq_eq_iff_zmod {q : ℕ} [NeZero q] (a b : Int) :
    modq_eq a b q ↔ (a : ZMod q) = (b : ZMod q) := by
  unfold modq_eq
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- (a - b) % q = 0 → (q : Int) ∣ (b - a)
    have hdvd : (q : Int) ∣ (a - b) := Int.dvd_of_emod_eq_zero h
    have : (b - a) = -(a - b) := by ring
    rw [this]; exact dvd_neg.mpr hdvd
  · -- (q : Int) ∣ (b - a) → (a - b) % q = 0
    have hdvd : (q : Int) ∣ (a - b) := by
      have : (a - b) = -(b - a) := by ring
      rw [this]; exact dvd_neg.mpr h
    exact Int.emod_eq_zero_of_dvd hdvd

end libcrux_iot_ml_kem.Spec.ModularArith