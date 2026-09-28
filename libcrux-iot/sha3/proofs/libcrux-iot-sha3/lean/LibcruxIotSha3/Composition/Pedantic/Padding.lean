import LibcruxIotSha3.Composition.Pedantic.BitsOps
/-!
# `pad10*1` (FIPS 202, Algorithm 9)

`pad10*1(x, m) = 1 || 0^j || 1` with `j = (-m - 2) mod x`.

The transcript computes `j` as `(x - ((m + 2) mod x)) mod x`, which is that
value without a signed type: for an arbitrary-length message there is no type
wide enough to hold `-m`. `pad_j_eq` below is what says the two agree, and it
is the only arithmetic left in this file — the padding itself is now three
calls into the opaque bit-string type rather than a loop, so the loop
induction this file used to carry is gone.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-- FIPS 202, Algorithm 9: the padding for a message of `m` bits at rate `x`. -/
def padBits (x m : Nat) : List Bool :=
  true :: (List.replicate ((-(m : Int) - 2) % (x : Int)).toNat false ++ [true])

/-- The transcript's unsigned `j` is the Standard's `(-m - 2) mod x`. -/
theorem pad_j_eq (x m : Nat) (hx : 0 < x) :
    (x - (m % x + 2) % x) % x = ((-(m : Int) - 2) % (x : Int)).toNat := by
  have hX : (0 : Int) < (x : Int) := by exact_mod_cast hx
  have hmod : (m % x + 2) % x = (m + 2) % x := by simp [Nat.add_mod]
  rw [hmod]
  set c := (m + 2) % x with hc
  have hcx : c < x := Nat.mod_lt _ hx
  have hcI : (c : Int) = ((m : Int) + 2) % (x : Int) := by
    rw [hc]; push_cast [Int.natCast_mod]; ring_nf
  -- `-(m) - 2` and `x - c` differ by a multiple of `x`
  have hcong : (-(m : Int) - 2) % (x : Int) = ((x : Int) - (c : Int)) % (x : Int) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have hrw : (-(m : Int) - 2) - ((x : Int) - (c : Int))
        = -(((m : Int) + 2) - (c : Int)) - (x : Int) := by ring
    rw [hrw]
    have hdvd : (x : Int) ∣ (((m : Int) + 2) - (c : Int)) := by
      refine ⟨((m : Int) + 2) / (x : Int), ?_⟩
      have hde := Int.mul_ediv_add_emod ((m : Int) + 2) (x : Int)
      rw [hcI]; omega
    obtain ⟨k, hk⟩ := hdvd
    rw [hk]
    have : -((x : Int) * k) - (x : Int) = (x : Int) * (-k - 1) := by ring
    rw [this, Int.mul_emod_right]
  have hsub : ((x : Int) - (c : Int)) = ((x - c : Nat) : Int) := by
    push_cast [Nat.cast_sub (le_of_lt hcx)]; ring
  have hfinal : (((x - c) % x : Nat) : Int) = (-(m : Int) - 2) % (x : Int) := by
    rw [hcong, hsub]; push_cast; ring
  rw [← hfinal]
  -- `simp` would push the cast straight back in, so close it directly.
  exact (Int.toNat_natCast _).symm

/-- The padding the transcript builds, as a list.

    Three opaque operations — `from_bits [1]`, `zeros j`, and two `concat`s —
    so the whole proof is the arithmetic for `j` plus the models. That
    arithmetic is `nat::Nat`'s now rather than a `u64`'s: `rem` and `sub` are
    the only steps that can fail, at a zero divisor and below zero, and
    `(m % x + 2) % x < x` rules both out. The `x ≤ 1600` hypothesis this
    theorem used to carry — there to keep `m % x + 2` inside a word — is gone
    with the word. -/
theorem pad10_star_1_eq (x m : Nat) (hx : 0 < x) :
    hacspec_sha3_pedantic.sponge.pad10_star_1 x m = ok (padBits x m) := by
  have hxne : ¬ (x = 0) := by omega
  have h0 : ((0#u64 : Std.U64).val) = 0 := by simp
  have h2 : ((2#u64 : Std.U64).val) = 2 := by simp
  have hle : (m % x + 2) % x ≤ x := le_of_lt (Nat.mod_lt _ hx)
  unfold hacspec_sha3_pedantic.sponge.pad10_star_1
    hacspec_sha3_pedantic.nat.Nat.new
    hacspec_sha3_pedantic.nat.Nat.Insts.CoreCmpPartialOrdNat.gt
    hacspec_sha3_pedantic.nat.Nat.Insts.CoreOpsArithRemNatNat.rem
    hacspec_sha3_pedantic.nat.Nat.Insts.CoreOpsArithAddNatNat.add
    hacspec_sha3_pedantic.nat.Nat.Insts.CoreOpsArithSubNatNat.sub
    hacspec_sha3_pedantic.bits.BitStr.from_bits
    hacspec_sha3_pedantic.bits.BitStr.zeros
    hacspec_sha3_pedantic.bits.BitStr.concat
    Aeneas.Std.massert
  simp only [h0, h2, Std.lift, bind_tc_ok, decide_eq_true_eq,
    if_neg hxne, if_pos hx, if_pos hle]
  simp [padBits, ← pad_j_eq x m hx, Std.Array.to_slice, Std.Array.make]

end LibcruxIotSha3.Composition.Pedantic
