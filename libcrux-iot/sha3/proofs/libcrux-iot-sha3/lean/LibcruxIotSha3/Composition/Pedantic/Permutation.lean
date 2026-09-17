import LibcruxIotSha3.Composition.Pedantic.Round
/-!
# The round loop of `Keccak-p` (FIPS 202, Algorithm 7)

`Keccak-p[b, n_r]` applies `Rnd(·, i_r)` for `i_r = 12 + 2l - n_r … 12 + 2l - 1`,
in that order.  `roundsFrom f first n` is those `n` rounds as a function of the
bits, built so that the *outermost* application is the last round -- which is
the opposite of the order the loop performs them in, so `roundsFrom_succ_shift`
is what reconciles the two.

This module stops at the loop: `keccak_p` itself also converts between the flat
bit string and the state array (`from_bits` / `to_bits`, FIPS 202 Sec. 3.1.2 and
3.1.3), which belongs with the sponge boundary.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-- `n` rounds, starting at round index `first`. -/
def roundsFrom (f : Nat → Nat → Nat → Bool) (first : Int) : Nat → (Nat → Nat → Nat → Bool)
  | 0 => f
  | n + 1 => roundBit (roundsFrom f first n) (first + n)

theorem roundBit_congr {f g : Nat → Nat → Nat → Bool} (i_r : Int) (h : AgreeInRange f g) :
    AgreeInRange (roundBit f i_r) (roundBit g i_r) :=
  iotaBit_congr i_r (chiBit_congr (piBit_congr (rhoBit_congr (thetaBit_congr h))))

theorem roundsFrom_congr {f g : Nat → Nat → Nat → Bool} (first : Int) (n : Nat)
    (h : AgreeInRange f g) : AgreeInRange (roundsFrom f first n) (roundsFrom g first n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact roundBit_congr _ ih

/-- Performing the first round and then `n` more from `first + 1` is the same as
    `n + 1` rounds from `first`. -/
theorem roundsFrom_succ_shift (f : Nat → Nat → Nat → Bool) (first : Int) (n : Nat) :
    roundsFrom (roundBit f first) (first + 1) n = roundsFrom f first (n + 1) := by
  induction n with
  | zero => simp [roundsFrom]
  | succ n ih =>
    show roundBit (roundsFrom (roundBit f first) (first + 1) n) (first + 1 + n) = _
    rw [ih]
    show _ = roundBit (roundsFrom f first (n + 1)) (first + (n + 1))
    congr 1
    ring

/-! ### The loop -/

theorem keccak_p_body_cont (A : SA) (i e : Std.I64) (hle : i.val ≤ e.val)
    (hlo : -1000000000 ≤ i.val) (hhi : i.val ≤ 1000000000) :
    ∃ s : Std.I64, s.val = i.val + 1 ∧
      hacspec_sha3_pedantic.keccak_p.keccak_p_loop.body { start := i, «end» := e } A
        = ok (.cont ({ start := s, «end» := e }, mkSA (roundBit (bitAt A) i.val))) := by
  have hmaxI : Std.IScalar.max Std.IScalarTy.I64 = 9223372036854775807 := by
    rw [Std.IScalar.max_IScalarTy_I64_eq, Std.I64.max_eq]
  obtain ⟨s, hs, hnext⟩ := range_incl_next_le_i64 i e hle (by omega)
  refine ⟨s, hs, ?_⟩
  unfold hacspec_sha3_pedantic.keccak_p.keccak_p_loop.body
  rw [hnext]
  simp [rnd_eq A i hlo hhi]

theorem keccak_p_body_done (A : SA) (i e : Std.I64) (h : e.val < i.val) :
    hacspec_sha3_pedantic.keccak_p.keccak_p_loop.body { start := i, «end» := e } A
      = ok (.done A) := by
  unfold hacspec_sha3_pedantic.keccak_p.keccak_p_loop.body
  rw [range_incl_next_gt_i64 i e h]
  simp

theorem AgreeInRange.refl (f : Nat → Nat → Nat → Bool) : AgreeInRange f f :=
  fun _ _ _ _ _ _ => rfl

/-- The round loop: from `first` through `last`, one `Rnd` per index. -/
theorem keccak_p_loop_eq (A : SA) (first last : Std.I64)
    (hfl : first.val ≤ last.val + 1)
    (hlo : -1000000000 ≤ first.val) (hhi : last.val ≤ 1000000000) :
    ∃ A' : SA,
      hacspec_sha3_pedantic.keccak_p.keccak_p_loop { start := first, «end» := last } A = ok A' ∧
      AgreeInRange (bitAt A')
        (roundsFrom (bitAt A) first.val (last.val + 1 - first.val).toNat) := by
  refine loop_range_incl_eq_inv_i64 (β := SA) (γ := SA)
    (fun p => hacspec_sha3_pedantic.keccak_p.keccak_p_loop.body p.1 p.2)
    last
    (fun i _ => -1000000000 ≤ i.val ∧ i.val ≤ last.val + 1)
    (fun i acc r => AgreeInRange (bitAt r)
      (roundsFrom (bitAt acc) i.val (last.val + 1 - i.val).toNat))
    ?hstep ?hdone (last.val + 1 - first.val).toNat first A (by omega) ⟨hlo, by omega⟩
  case hstep =>
    rintro i acc hi ⟨hilo, hihi⟩
    obtain ⟨s, hs, hbody⟩ := keccak_p_body_cont acc i last hi hilo (by omega)
    refine ⟨s, mkSA (roundBit (bitAt acc) i.val), hs, ⟨by omega, by omega⟩, hbody, ?_⟩
    intro r hr
    -- `hr` describes the run from `i + 1`; shift it back by one round
    have hn : (last.val + 1 - i.val).toNat = (last.val - i.val).toNat + 1 := by omega
    have hs' : (last.val + 1 - (i.val + 1)).toNat = (last.val - i.val).toNat := by omega
    have hshift : roundsFrom (roundBit (bitAt acc) i.val) s.val (last.val + 1 - s.val).toNat
        = roundsFrom (bitAt acc) i.val (last.val + 1 - i.val).toNat := by
      rw [hs, hs', hn]
      exact roundsFrom_succ_shift (bitAt acc) i.val _
    refine hr.trans ?_
    rw [← hshift]
    exact roundsFrom_congr _ _ (agree_bitAt_mkSA _)
  case hdone =>
    rintro i acc hi ⟨hilo, hihi⟩
    refine ⟨acc, keccak_p_body_done acc i last hi, ?_⟩
    rw [show (last.val + 1 - i.val).toNat = 0 by omega]
    exact AgreeInRange.refl _

-- Pinned by `#guard_msgs`: the build fails if this comes to depend on any axiom
-- beyond Lean's standard three.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.keccak_p_loop_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms keccak_p_loop_eq

end LibcruxIotSha3.Composition.Pedantic
