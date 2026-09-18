import LibcruxIotSha3.Composition.Pedantic.Permutation
import LibcruxIotSha3.Composition.Pedantic.Bits
/-!
# `Keccak-p[1600, n_r]` (FIPS 202, Algorithm 7)

The three pieces are in place: the bit string becomes a state array
(`from_bits_eq`), the rounds run from `12 + 2l - n_r` through `12 + 2l - 1`
(`keccak_p_loop_eq`), and the state array becomes a bit string again
(`to_bits_eq`).  At `w = 64` those bounds are `24 - n_r` and `23`, so the loop
performs exactly `n_r` rounds.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-- The bit function of a 1600-bit string, read as a state array. -/
def bitsOf (s : Slice Bool) : Nat → Nat → Nat → Bool := fun x y z => s.val[bitPos x y z]!

/-- `Keccak-p[1600, n_r]`: `n_r` rounds, ending at round index `12 + 2l - 1 = 23`. -/
theorem keccak_p_eq (s : Slice Bool) (hslen : s.val.length = 1600)
    (n_r : Std.Usize) (hnr0 : 0 < n_r.val) (hnr : n_r.val ≤ 24) :
    ∃ out : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.keccak_p.keccak_p 64#usize s n_r = ok out ∧
      out.val.length = 1600 ∧
      ∀ p < 1600, out.val[p]!
        = roundsFrom (bitsOf s) (24 - (n_r.val : Int)) n_r.val
            ((p / 64) % 5) (p / 320) (p % 64) := by
  have hmaxI : Std.IScalar.max Std.IScalarTy.I64 = 9223372036854775807 := by
    rw [Std.IScalar.max_IScalarTy_I64_eq, Std.I64.max_eq]
  have hminI : Std.IScalar.min Std.IScalarTy.I64 = -9223372036854775808 := by
    rw [Std.IScalar.min_IScalarTy_I64_eq, Std.I64.min_eq]
  have hminN : Std.I64.min = -9223372036854775808 := Std.I64.min_eq
  have hmaxN : Std.I64.max = 9223372036854775807 := Std.I64.max_eq
  have hnrn : (n_r.val : Int) ≤ 24 := by exact_mod_cast hnr
  -- the bit string becomes a state array
  obtain ⟨A, hfrom, hA⟩ := from_bits_eq s hslen
  have hagree : AgreeInRange (bitAt A) (bitsOf s) := fun x hx y hy z hz => hA x hx y hy z hz
  -- the round indices
  have hL : hacspec_sha3_pedantic.state_array.StateArray.L 64#usize = ok 6#usize := by
    unfold hacspec_sha3_pedantic.state_array.StateArray.L
    simp
  obtain ⟨l6, hl6, hl6v⟩ := usize_to_i64 6#usize (by scalar_tac)
  obtain ⟨m, hm, hmv⟩ := i64_mul_eq 2#i64 l6 (by simp [hl6v]; omega) (by simp [hl6v]; omega)
  obtain ⟨tw, htw, htwv⟩ := i64_add_eq 12#i64 m (by simp [hmv, hl6v]; omega)
    (by simp [hmv, hl6v]; omega)
  obtain ⟨last, hlast, hlastv⟩ := i64_sub_eq tw 1#i64 (by simp [htwv, hmv, hl6v]; omega)
    (by simp [htwv, hmv, hl6v]; omega)
  have hlastn : last.val = 23 := by simp [hlastv, htwv, hmv, hl6v]
  obtain ⟨nri, hnri, hnriv⟩ := usize_to_i64 n_r (by scalar_tac)
  obtain ⟨d, hd, hdv⟩ := i64_sub_eq last nri (by omega) (by omega)
  obtain ⟨first, hfirst, hfirstv⟩ := i64_add_eq d 1#i64 (by simp [hdv]; omega)
    (by simp [hdv]; omega)
  have hfirstn : first.val = 24 - (n_r.val : Int) := by
    simp [hfirstv, hdv, hlastn, hnriv]
    omega
  have hnew : core.ops.range.RangeInclusive.new first last
      = ok ({ start := first, «end» := last } : core.ops.range.RangeInclusive Std.I64) := rfl
  -- the rounds
  obtain ⟨A', hloop, hbits⟩ := keccak_p_loop_eq A first last (by omega) (by omega) (by omega)
  -- and back to a bit string
  obtain ⟨out, hto, htolen, htobits⟩ := to_bits_eq A'
  refine ⟨out, ?_, htolen, fun p hp => ?_⟩
  · -- Sec. 3 takes a positive number of rounds; Algorithm 7 checks it.
    have hpos : (massert (n_r > 0#usize) : RustM Unit) = .ok () := by
      unfold Aeneas.Std.massert
      rw [if_pos (show n_r > 0#usize by scalar_tac)]
    unfold hacspec_sha3_pedantic.keccak_p.keccak_p
    simp only [hpos, bind_tc_ok, hfrom, hL, hl6, hm, htw, hlast, hnri, hd, hfirst, hnew,
      hloop, hto]
  · rw [htobits p hp]
    have hxlt : (p / 64) % 5 < 5 := Nat.mod_lt _ (by omega)
    have hylt : p / 320 < 5 := by omega
    have hzlt : p % 64 < 64 := Nat.mod_lt _ (by omega)
    rw [hbits _ hxlt _ hylt _ hzlt]
    have hn : (last.val + 1 - first.val).toNat = n_r.val := by
      rw [hlastn, hfirstn]
      omega
    rw [hn, hfirstn] at *
    exact roundsFrom_congr _ _ hagree _ hxlt _ hylt _ hzlt

-- Pinned by `#guard_msgs`: the build fails if this comes to depend on any axiom
-- beyond Lean's standard three.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.keccak_p_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms keccak_p_eq

end LibcruxIotSha3.Composition.Pedantic
