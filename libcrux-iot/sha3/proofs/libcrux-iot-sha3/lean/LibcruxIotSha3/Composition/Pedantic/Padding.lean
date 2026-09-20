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
    so the whole proof is the arithmetic for `j` plus the models. -/
theorem pad10_star_1_eq (x m : Std.U64) (hx : 0 < x.val) (hxb : x.val ≤ 1600) :
    hacspec_sha3_pedantic.sponge.pad10_star_1 x m = ok (padBits x.val m.val) := by
  have hxne : x.val ≠ 0 := by omega
  -- `massert (x > 0)`
  have hmassert : (massert (x > 0#u64) : RustM Unit) = .ok () := by
    unfold Aeneas.Std.massert
    refine if_pos ?_
    show (0#u64 : Std.U64).val < x.val
    simpa using hx
  -- the four scalar steps that compute `j`
  obtain ⟨i, hi, hiv, _⟩ := Std.WP.spec_imp_exists
    (Std.UScalar.rem_bv_spec m (y := x) hxne)
  have hix : i.val < x.val := by rw [hiv]; exact Nat.mod_lt _ hx
  obtain ⟨i1, hi1, hi1v⟩ := Std.WP.spec_imp_exists
    (Std.WP.spec_of_partialSpec (Std.UScalar.add_spec (x := i) (y := (2#u64 : Std.U64)))
      (by intro e; cases e <;> simp; scalar_tac) (by simp))
  obtain ⟨i2, hi2, hi2v, _⟩ := Std.WP.spec_imp_exists
    (Std.UScalar.rem_bv_spec i1 (y := x) hxne)
  have hi2x : i2.val < x.val := by rw [hi2v]; exact Nat.mod_lt _ hx
  obtain ⟨i3, hi3, hi3v, -⟩ := Std.WP.spec_imp_exists
    (Std.WP.spec_of_partialSpec (Std.UScalar.sub_spec (x := x) (y := i2))
      (by intro e; cases e <;> simp; scalar_tac) (by simp))
  obtain ⟨j, hj, hjv, _⟩ := Std.WP.spec_imp_exists
    (Std.UScalar.rem_bv_spec i3 (y := x) hxne)
  have hjval : j.val = ((-(m.val : Int) - 2) % (x.val : Int)).toNat := by
    rw [← pad_j_eq x.val m.val hx, hjv, hi3v, hi2v, hi1v, hiv]
    simp
  unfold hacspec_sha3_pedantic.sponge.pad10_star_1
  rw [hmassert, bind_tc_ok, hi, bind_tc_ok, hi1, bind_tc_ok, hi2, bind_tc_ok,
    hi3, bind_tc_ok, hj, bind_tc_ok]
  -- `from_bits`, `zeros` and the two `concat`s are the hand-written models
  show (do
    let s ← Std.lift (Std.Array.to_slice (Std.Array.make 1#usize [true]))
    let one ← hacspec_sha3_pedantic.bits.BitStr.from_bits s
    let bs ← hacspec_sha3_pedantic.bits.BitStr.zeros j
    let bs1 ← hacspec_sha3_pedantic.bits.BitStr.concat one bs
    hacspec_sha3_pedantic.bits.BitStr.concat bs1 one) = ok (padBits x.val m.val)
  simp only [hacspec_sha3_pedantic.bits.BitStr.from_bits,
    hacspec_sha3_pedantic.bits.BitStr.zeros,
    hacspec_sha3_pedantic.bits.BitStr.concat, Std.lift, bind_tc_ok]
  simp only [padBits, hjval]
  rfl

end LibcruxIotSha3.Composition.Pedantic
