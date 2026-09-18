import LibcruxIotSha3.Composition.Pedantic.Permutation
import LibcruxIotSha3.Composition.Pedantic.RoundConstants
import LibcruxIotSha3.Composition.Pedantic.KeccakC
import LibcruxIotSha3.LaneModel
/-!
# The lane model's `Keccak-f[1600]` is the transcript's

`LibcruxIotSha3/LaneModel.lean` keeps the state as 25 `u64` lanes and writes each
step mapping as a function of the lane index; `hacspec_sha3_pedantic` writes them
as triple loops over `(x, y, z)`.  This module shows the two agree bit for bit,
which is what makes the lane model a faithful reading of FIPS 202 rather than
merely a convenient one.
-/

open CoreModels Aeneas
open LibcruxIotSha3.LaneModel
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-! ### Bit-level arithmetic on lanes -/

/-- Rotating a lane left by `r` moves bit `(z - r) mod 64` to bit `z`, which is
    exactly the index ρ reads from. -/
theorem rotate_left_bit (v : Std.U64) (r : Std.U32) (z : Nat) (hz : z < 64) :
    (Std.UScalar.rotate_left v r).bv.getLsbD z = v.bv.getLsbD (rotIndex r.val z) := by
  show (v.bv.rotateLeft r.val).getLsbD z = _
  rw [BitVec.getLsbD_rotateLeft]
  have hm : r.val % 64 < 64 := Nat.mod_lt _ (by omega)
  by_cases h : z < r.val % 64
  · simp only [h, decide_true, cond_true]
    congr 1
    simp only [rotIndex]
    omega
  · simp only [h, decide_false, cond_false, hz, decide_true, Bool.true_and]
    congr 1
    simp only [rotIndex]
    omega

/-! ### θ -/

theorem theta_bit (s : Lanes) (x y z : Nat) (hx : x < 5) (hy : y < 5) (hz : z < 64) :
    laneBit (thetaLanes s) x y z = thetaBit (laneBit s) x y z := by
  have hcb : ∀ (x' z' : Nat), x' < 5 →
      ((mkArr 5#usize (cLane s)).val[x']!).bv.getLsbD z' = cBit (laneBit s) x' z' := by
    intro x' z' hx'
    rw [mkArr_get 5#usize (cLane s) (by simp; omega)]
    simp only [cLane, cBit, laneBit, u64_xor_bit]
  have hrot : rotIndex (1#u32 : Std.U32).val z = (z + 63) % 64 := by
    simp [rotIndex]
  have hdb : ((mkArr 5#usize (dLane (mkArr 5#usize (cLane s)))).val[x]!).bv.getLsbD z
      = dBit (cBit (laneBit s)) x z := by
    rw [mkArr_get 5#usize _ (by simp; omega)]
    simp only [dLane, u64_xor_bit]
    rw [rotate_left_bit _ _ z hz, hrot, hcb ((x + 4) % 5) z (by omega),
      hcb ((x + 1) % 5) ((z + 63) % 64) (by omega)]
    rfl
  rw [thetaLanes, laneBit_mkArr _ hx hy]
  simp only [u64_xor_bit]
  rw [show (5 * y + x) % 5 = x from by omega, hdb]
  simp only [thetaBit, laneBit]


/-! ### ρ -/

/-- The tabulated rotation offsets are the ones FIPS 202's ρ walk produces
    (modulo the lane width, which is all `rotIndex` sees). -/
theorem rho_offsets_table : ∀ x < 5, ∀ y < 5,
    (libcrux_iot_sha3.rhoOffsets.val[5 * y + x]!).val % 64 = rhoOffsetOf x y % 64 := by
  simp only [libcrux_iot_sha3.rhoOffsets]
  decide

theorem rho_bit (s : Lanes) (x y z : Nat) (hx : x < 5) (hy : y < 5) (hz : z < 64) :
    laneBit (rhoLanes s) x y z = rhoBit (laneBit s) x y z := by
  rw [rhoLanes, laneBit_mkArr _ hx hy, rotate_left_bit _ _ z hz]
  simp only [rhoBit, laneBit, rotIndex, rho_offsets_table x hx y hy]

/-! ### π -/

theorem pi_bit (s : Lanes) (x y z : Nat) (hx : x < 5) (hy : y < 5) :
    laneBit (piLanes s) x y z = piBit (laneBit s) x y z := by
  rw [piLanes, laneBit_mkArr _ hx hy]
  rw [show (5 * y + x) % 5 = x from by omega, show (5 * y + x) / 5 = y from by omega]
  rfl

/-! ### χ -/

theorem chi_bit (s : Lanes) (x y z : Nat) (hx : x < 5) (hy : y < 5) (hz : z < 64) :
    laneBit (chiLanes s) x y z = chiBit (laneBit s) x y z := by
  rw [chiLanes, laneBit_mkArr _ hx hy]
  rw [show (5 * y + x) % 5 = x from by omega, show (5 * y + x) / 5 = y from by omega]
  rw [u64_xor_bit, u64_and_bit, u64_not_bit _ z hz]
  rfl

/-! ### ι -/

theorem iota_bit (s : Lanes) (r : Nat) (hr : r < 24) (x y z : Nat)
    (hx : x < 5) (hy : y < 5) (hz : z < 64) :
    laneBit (iotaLanes s r) x y z = iotaBit (laneBit s) (r : Int) x y z := by
  have hset : ∀ i : Nat, i < 25 →
      (iotaLanes s r).val[i]! =
        if i = 0 then s.val[0]! ^^^ libcrux_iot_sha3.roundConstants.val[r]!
        else s.val[i]! := by
    intro i hi
    have hlen : s.val.length = 25 := s.property
    show (s.val.set 0 _)[i]! = _
    rw [getElem!_pos _ i (by simp; omega), getElem!_pos s.val i (by omega)]
    rw [List.getElem_set]
    by_cases h : i = 0 <;> simp [h]
  rw [laneBit, hset (5 * y + x) (by omega)]
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos (by omega)]
    rw [u64_xor_bit, ← rcBitAt_table r hr z hz]
    simp only [iotaBit, laneBit]
    simp
  · rw [if_neg (show 5 * y + x ≠ 0 from by omega)]
    simp only [iotaBit, laneBit, if_neg h]


/-! ### One round, and the 24-round permutation -/

theorem round_lanes_bit (s : Lanes) (r : Nat) (hr : r < 24) :
    AgreeInRange (laneBit (roundLanes s r)) (roundBit (laneBit s) (r : Int)) := by
  have h1 : AgreeInRange (laneBit (thetaLanes s)) (thetaBit (laneBit s)) :=
    fun x hx y hy z hz => theta_bit s x y z hx hy hz
  have h2 : AgreeInRange (laneBit (rhoLanes (thetaLanes s))) (rhoBit (thetaBit (laneBit s))) :=
    AgreeInRange.trans (fun x hx y hy z hz => rho_bit _ x y z hx hy hz) (rhoBit_congr h1)
  have h3 : AgreeInRange (laneBit (piLanes (rhoLanes (thetaLanes s))))
      (piBit (rhoBit (thetaBit (laneBit s)))) :=
    AgreeInRange.trans (fun x hx y hy z _ => pi_bit _ x y z hx hy) (piBit_congr h2)
  have h4 : AgreeInRange (laneBit (chiLanes (piLanes (rhoLanes (thetaLanes s)))))
      (chiBit (piBit (rhoBit (thetaBit (laneBit s))))) :=
    AgreeInRange.trans (fun x hx y hy z hz => chi_bit _ x y z hx hy hz) (chiBit_congr h3)
  exact AgreeInRange.trans (fun x hx y hy z hz => iota_bit _ r hr x y z hx hy hz)
    (iotaBit_congr _ h4)

/-- Each round of the lane model is the transcript's round, so `n` of them are
    `roundsFrom … 0 n`.  With `n = 24` this is `Keccak-f[1600]`. -/
theorem roundsUpTo_bit (s : Lanes) (n : Nat) (hn : n ≤ 24) :
    AgreeInRange (laneBit (roundsUpTo s n)) (roundsFrom (laneBit s) 0 n) := by
  induction n with
  | zero => exact AgreeInRange.refl (laneBit s)
  | succ k ih =>
    have hk : k < 24 := by omega
    show AgreeInRange (laneBit (roundLanes (roundsUpTo s k) k))
      (roundBit (roundsFrom (laneBit s) 0 k) (0 + (k : Int)))
    rw [show (0 : Int) + (k : Int) = (k : Int) from by ring]
    exact AgreeInRange.trans (round_lanes_bit _ k hk)
      (roundBit_congr _ (ih (by omega)))


/-! ### The lane state as a flat bit string -/

theorem lanesToBits_get (s : Lanes) {x y z : Nat} (hx : x < 5) (hy : y < 5) (hz : z < 64) :
    (lanesToBits s)[bitPos x y z]! = laneBit s x y z := by
  have hlt : bitPos x y z < 1600 := by simp only [bitPos]; omega
  have h1 : (bitPos x y z / 64) % 5 = x := by simp only [bitPos]; omega
  have h2 : bitPos x y z / 320 = y := by simp only [bitPos]; omega
  have h3 : bitPos x y z % 64 = z := by simp only [bitPos]; omega
  simp only [lanesToBits]
  rw [getElem!_pos _ _ (by simp only [List.length_map, List.length_range]; exact hlt)]
  simp only [List.getElem_map, List.getElem_range, laneBitAt, h1, h2, h3]

theorem bitsOfList_lanesToBits (s : Lanes) :
    AgreeInRange (bitsOfList (lanesToBits s)) (laneBit s) :=
  fun _ hx _ hy _ hz => lanesToBits_get s hx hy hz

/-- The lane model's `Keccak-f[1600]`, read as a function on the 1600 bits, is
    the `keccakF` the pedantic sponge uses.  This is the statement the rest of
    the proof rests on: it mentions no specification but the transcript's. -/
theorem keccakF_lanesToBits (s : Lanes) :
    keccakF (lanesToBits s) = lanesToBits (keccakFLanes s) := by
  have hbit := roundsUpTo_bit s 24 (le_refl _)
  have hcongr := roundsFrom_congr (0 : Int) 24 (bitsOfList_lanesToBits s)
  show keccakF (lanesToBits s)
    = (List.range 1600).map
        (fun p => laneBit (keccakFLanes s) ((p / 64) % 5) (p / 320) (p % 64))
  simp only [keccakF]
  apply List.map_congr_left
  intro p hp
  have hp1600 : p < 1600 := by simpa using hp
  have hx : (p / 64) % 5 < 5 := by omega
  have hy : p / 320 < 5 := by omega
  have hz : p % 64 < 64 := by omega
  rw [hcongr _ hx _ hy _ hz, ← hbit _ hx _ hy _ hz]
  rfl

-- Pin the lane-level permutation bridge to Lean's standard three axioms.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.keccakF_lanesToBits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms keccakF_lanesToBits

end LibcruxIotSha3.Composition.Pedantic
