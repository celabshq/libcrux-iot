import LibcruxIotSha3.Composition.Pedantic.BitsOps
/-!
# `pad10*1` (FIPS 202, Algorithm 9)

`pad10*1(x, m) = 1 || 0^j || 1` with `j = (-m - 2) mod x`.  Rust's `%` truncates
towards zero, so the spec computes the modulus the same way `imod` does --
`((a % x) + x) % x` -- and `i64_emod_chain` is what says that is `Int.emod`.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-- FIPS 202, Algorithm 9: the padding for a message of `m` bits at rate `x`. -/
def padBits (x m : Nat) : List Bool :=
  true :: (List.replicate ((-(m : Int) - 2) % (x : Int)).toNat false ++ [true])

theorem pad10_star_1_eq (x m : Std.Usize) (hx : 0 < x.val) (hxb : x.val ≤ 1600)
    (hmb : m.val ≤ 1000000000) :
    ∃ out : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.sponge.pad10_star_1 x m = ok out ∧ out.val = padBits x.val m.val := by
  have hminI : Std.IScalar.min Std.IScalarTy.I64 = -9223372036854775808 := by
    rw [Std.IScalar.min_IScalarTy_I64_eq, Std.I64.min_eq]
  have hmaxI : Std.IScalar.max Std.IScalarTy.I64 = 9223372036854775807 := by
    rw [Std.IScalar.max_IScalarTy_I64_eq, Std.I64.max_eq]
  have hminN : Std.I64.min = -9223372036854775808 := Std.I64.min_eq
  have hmaxN : Std.I64.max = 9223372036854775807 := Std.I64.max_eq
  have hxn : (x.val : Int) ≤ 1600 := by exact_mod_cast hxb
  have hxpos : (0 : Int) < (x.val : Int) := by exact_mod_cast hx
  have hmn : (m.val : Int) ≤ 1000000000 := by exact_mod_cast hmb
  -- the modulus `j = (-m - 2) mod x`
  obtain ⟨xi, hxi, hxiv⟩ := usize_to_i64 x (by scalar_tac)
  obtain ⟨mi, hmi, hmiv⟩ := usize_to_i64 m (by scalar_tac)
  obtain ⟨nm, hnm, hnmv⟩ := i64_neg_eq mi (by omega)
  obtain ⟨a, ha, hav⟩ := i64_sub_eq nm 2#i64 (by simp; omega) (by simp; omega)
  have hav' : a.val = -(m.val : Int) - 2 := by rw [hav, hnmv, hmiv]; simp
  obtain ⟨i3, i4, j, hi3, hi4, hj, hjv⟩ :=
    i64_emod_chain a xi (by omega) (by omega) (by omega)
  have hjv' : j.val = (-(m.val : Int) - 2) % (x.val : Int) := by rw [hjv, hav', hxiv]
  have hj0 : 0 ≤ j.val := by rw [hjv']; exact Int.emod_nonneg _ (by omega)
  have hjb : j.val < (x.val : Int) := by
    rw [hjv']; exact Int.emod_lt_of_pos _ (by omega)
  -- the string `1 || 0^j || 1`
  have hone : alloc.vec.Vec.push (Aeneas.Std.alloc.vec.Vec.new Bool) true
      = ok ⟨[true], by simp; scalar_tac⟩ := by
    rw [vec_push_eq _ _ (by simp; scalar_tac)]
    apply congrArg
    apply Subtype.ext
    simp
  obtain ⟨p2, hloop, hp2⟩ := push_const_loop_i64
    (fun p => hacspec_sha3_pedantic.sponge.pad10_star_1_loop.body p.1 p.2)
    j hj0 false ⟨[true], by simp; scalar_tac⟩
    (by
      intro i acc hi hinv
      obtain ⟨t, ht, hnext⟩ := range_next_lt_i64 i j hi
      have hacclen : acc.val.length = 1 + i.val.toNat := by rw [hinv]; simp; omega
      refine ⟨t, ⟨acc.val ++ [false], by simp; scalar_tac⟩, ht, by simp, ?_⟩
      unfold hacspec_sha3_pedantic.sponge.pad10_star_1_loop.body
      rw [hnext]
      simp [vec_push_eq acc _ (by scalar_tac)])
    (by
      intro acc
      unfold hacspec_sha3_pedantic.sponge.pad10_star_1_loop.body
      rw [range_next_ge_i64 j j (le_refl _)]
      simp)
  refine ⟨⟨p2.val ++ [true], by simp; scalar_tac⟩, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.sponge.pad10_star_1
    rw [hxi, bind_tc_ok, hmi, bind_tc_ok, hnm, bind_tc_ok, ha, bind_tc_ok, hi3, bind_tc_ok,
      hi4, bind_tc_ok, hj, bind_tc_ok, vec_new_eq]
    show (do
        let p1 ← alloc.vec.Vec.push (Aeneas.Std.alloc.vec.Vec.new Bool) true
        let p2 ← hacspec_sha3_pedantic.sponge.pad10_star_1_loop
          { start := 0#i64, «end» := j } p1
        alloc.vec.Vec.push p2 true) = _
    rw [hone]
    show (do
        let p2' ← hacspec_sha3_pedantic.sponge.pad10_star_1_loop
          { start := 0#i64, «end» := j } ⟨[true], by simp; scalar_tac⟩
        alloc.vec.Vec.push p2' true) = _
    unfold hacspec_sha3_pedantic.sponge.pad10_star_1_loop
    rw [hloop]
    show alloc.vec.Vec.push p2 true = _
    rw [vec_push_eq p2 _ (by scalar_tac)]
  · simp only [padBits, hp2, ← hjv']
    simp

end LibcruxIotSha3.Composition.Pedantic
