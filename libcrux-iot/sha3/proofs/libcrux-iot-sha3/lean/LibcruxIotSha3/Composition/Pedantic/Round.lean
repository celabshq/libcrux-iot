import LibcruxIotSha3.Composition.Pedantic.Theta
import LibcruxIotSha3.Composition.Pedantic.Rho
import LibcruxIotSha3.Composition.Pedantic.Pi
import LibcruxIotSha3.Composition.Pedantic.Chi
import LibcruxIotSha3.Composition.Pedantic.Iota
/-!
# The round function (FIPS 202, Algorithm 7, step 1)

`Rnd(A, i_r) = ι(χ(π(ρ(θ(A)))), i_r)`, and each of the five is already pinned
down as `ok (mkSA (…Bit (bitAt …)))`.  Composing them is then only a matter of
reading the bits back out of each intermediate state array, which is
`bitAt_mkSA` -- in range, which is all `mkSA_congr` asks for.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-- Bit functions that agree on the indices of a state array. -/
def AgreeInRange (f g : Nat → Nat → Nat → Bool) : Prop :=
  ∀ x < 5, ∀ y < 5, ∀ z < 64, f x y z = g x y z

theorem agree_bitAt_mkSA (f : Nat → Nat → Nat → Bool) : AgreeInRange (bitAt (mkSA f)) f :=
  fun _ hx _ hy _ hz => bitAt_mkSA _ hx hy hz

theorem AgreeInRange.trans {f g h : Nat → Nat → Nat → Bool}
    (h1 : AgreeInRange f g) (h2 : AgreeInRange g h) : AgreeInRange f h :=
  fun x hx y hy z hz => (h1 x hx y hy z hz).trans (h2 x hx y hy z hz)

/-! Each step mapping reads its argument only at indices of the state array, so
each one respects `AgreeInRange`. -/

/-- The column parities read the state only at in-range indices. -/
theorem cBit_congr {f g} (h : AgreeInRange f g) :
    ∀ x < 5, ∀ z < 64, cBit f x z = cBit g x z := by
  intro x hx z hz
  simp only [cBit]
  rw [h x hx 0 (by omega) z hz, h x hx 1 (by omega) z hz, h x hx 2 (by omega) z hz,
    h x hx 3 (by omega) z hz, h x hx 4 (by omega) z hz]

theorem dBit_congr {c d} (h : ∀ x < 5, ∀ z < 64, c x z = d x z) :
    ∀ x < 5, ∀ z < 64, dBit c x z = dBit d x z := by
  intro x hx z hz
  simp only [dBit]
  rw [h _ (Nat.mod_lt _ (by omega)) z hz,
    h _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega))]

theorem thetaBit_congr {f g} (h : AgreeInRange f g) : AgreeInRange (thetaBit f) (thetaBit g) := by
  intro x hx y hy z hz
  simp only [thetaBit]
  rw [h x hx y hy z hz, dBit_congr (cBit_congr h) x hx z hz]

theorem rhoBit_congr {f g} (h : AgreeInRange f g) : AgreeInRange (rhoBit f) (rhoBit g) := by
  intro x hx y hy z hz
  simp only [rhoBit]
  exact h x hx y hy _ (Nat.mod_lt _ (by omega))

theorem piBit_congr {f g} (h : AgreeInRange f g) : AgreeInRange (piBit f) (piBit g) := by
  intro x hx y hy z hz
  simp only [piBit]
  exact h _ (Nat.mod_lt _ (by omega)) x hx z hz

theorem chiBit_congr {f g} (h : AgreeInRange f g) : AgreeInRange (chiBit f) (chiBit g) := by
  intro x hx y hy z hz
  simp only [chiBit]
  rw [h x hx y hy z hz, h _ (Nat.mod_lt _ (by omega)) y hy z hz,
    h _ (Nat.mod_lt _ (by omega)) y hy z hz]

theorem iotaBit_congr {f g} (i_r : Int) (h : AgreeInRange f g) :
    AgreeInRange (iotaBit f i_r) (iotaBit g i_r) := by
  intro x hx y hy z hz
  simp only [iotaBit]
  rw [h x hx y hy z hz]

/-- FIPS 202, Algorithm 7 step 1, on the bit function of a state array. -/
def roundBit (f : Nat → Nat → Nat → Bool) (i_r : Int) : Nat → Nat → Nat → Bool :=
  iotaBit (chiBit (piBit (rhoBit (thetaBit f)))) i_r

/-- One round of `Keccak-p`. -/
theorem rnd_eq (A : SA) (i_r : Std.I64)
    (hlo : -1000000000 ≤ i_r.val) (hhi : i_r.val ≤ 1000000000) :
    hacspec_sha3_pedantic.keccak_p.rnd A i_r = ok (mkSA (roundBit (bitAt A) i_r.val)) := by
  unfold hacspec_sha3_pedantic.keccak_p.rnd
  rw [theta_eq, bind_tc_ok, rho_eq, bind_tc_ok, pi_eq, bind_tc_ok, chi_eq, bind_tc_ok,
    iota_eq _ i_r hlo hhi]
  apply congrArg
  refine mkSA_congr (fun x y z hx hy hz => ?_)
  simp only [roundBit]
  exact iotaBit_congr i_r.val
    ((agree_bitAt_mkSA _).trans (chiBit_congr
      ((agree_bitAt_mkSA _).trans (piBit_congr
        ((agree_bitAt_mkSA _).trans (rhoBit_congr (agree_bitAt_mkSA _)))))))
    x hx y hy z hz

-- Pinned by `#guard_msgs`: the build fails if this comes to depend on any axiom
-- beyond Lean's standard three.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.rnd_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rnd_eq

end LibcruxIotSha3.Composition.Pedantic
