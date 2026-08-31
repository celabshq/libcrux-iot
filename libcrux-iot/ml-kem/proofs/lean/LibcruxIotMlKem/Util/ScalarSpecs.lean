/-
  # `Util/ScalarSpecs.lean` — monadic `Usize` arithmetic in `∃ … = .ok …` form.

  THE CANONICAL HOME for "this scalar operation succeeds, and here is its value".
  Six lemmas, no attributes, and the same single import `Spec/Lift.lean` already has —
  so importing this module adds nothing transitively and cannot widen what `simp`/`mvcgen`
  see downstream. (Skill §2.1: hoisting an ATTRIBUTED lemma into a widely-imported file
  silently changes proof search. Checked, not assumed: this file declares none.)

  ## Why it exists
  A reviewer found the same six helpers written THREE times: `Spec/Lift.lean`'s `nb_*`
  set (the NTT bridge), `Matrix/ComputeMessage/Hacspec.lean`'s `*_ok'` set, and — for
  mul and add only — `Util/Shared.lean`'s `usize_mul_ok_e` / `usize_add_ok_e`. All three
  are `private` or effectively local, so none could cite another: `private` is
  file-scoped, and `Matrix/ComputeMessage/Hacspec.lean` sits DOWNSTREAM of `Spec/Lift.lean`
  in the import order. That is the §2.1 duplication trap exactly — a lemma copied because
  it could not be reached, and then invisible to the dependency walk.

  ## Status of the other copies
  `Spec/Lift.lean`'s six are DELETED and now cite this module. Still to collapse when
  those files are next touched (each is a live obligation surface, so they are not
  disturbed for a cleanup):
    * `Matrix/ComputeMessage/Hacspec.lean` — `umul_ok'`, `uadd_ok'`, `usub_ok'`,
      `udiv_ok'`, `umod_ok'` (~:1009-1041), `shl_one_ok` (~:1540)
    * `Util/Shared.lean` — `usize_mul_ok_e`, `usize_add_ok_e` (statement-identical to
      `usize_mul_ok` / `usize_add_ok` here; different proofs)
-/

import LibcruxIotMlKem.Extraction.Funs

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do

namespace libcrux_iot_ml_kem.Util.ScalarSpecs

theorem usize_mul_ok (a b : Std.Usize) (h : a.val * b.val ≤ Std.Usize.max) :
    ∃ c : Std.Usize, (a * b : RustM Std.Usize) = .ok c ∧ c.val = a.val * b.val := by
  have hspec := Std.WP.spec_of_partialSpec (@Std.Usize.mul_spec a b)
    (fun e => by cases e <;> scalar_tac) (by simp)
  obtain ⟨v, h_eq, h_v⟩ := Std.WP.spec_imp_exists hspec
  exact ⟨v, h_eq, h_v⟩

theorem usize_add_ok (a b : Std.Usize) (h : a.val + b.val ≤ Std.Usize.max) :
    ∃ c : Std.Usize, (a + b : RustM Std.Usize) = .ok c ∧ c.val = a.val + b.val := by
  have hspec := Std.WP.spec_of_partialSpec (@Std.Usize.add_spec a b)
    (fun e => by cases e <;> scalar_tac) (by simp)
  obtain ⟨v, h_eq, h_v⟩ := Std.WP.spec_imp_exists hspec
  exact ⟨v, h_eq, h_v⟩

theorem usize_sub_ok (a b : Std.Usize) (h : b.val ≤ a.val) :
    ∃ c : Std.Usize, (a - b : RustM Std.Usize) = .ok c ∧ c.val = a.val - b.val := by
  have hT := Std.WP.spec_of_partialSpec (@Std.Usize.sub_spec a b)
    (fun e => by cases e <;> scalar_tac) (by simp)
  obtain ⟨c, h_eq, h_v⟩ := Std.WP.spec_imp_exists hT
  exact ⟨c, h_eq, h_v.1⟩

theorem usize_div_ok (a b : Std.Usize) (h : b.val ≠ 0) :
    ∃ c : Std.Usize, (a / b : RustM Std.Usize) = .ok c ∧ c.val = a.val / b.val := by
  obtain ⟨v, h_eq, h_v⟩ := Std.UScalar.div_spec a h
  exact ⟨v, h_eq, h_v⟩

theorem usize_mod_ok (a b : Std.Usize) (h : b.val ≠ 0) :
    ∃ c : Std.Usize, (a % b : RustM Std.Usize) = .ok c ∧ c.val = a.val % b.val := by
  obtain ⟨v, h_eq, h_v⟩ := Std.WP.spec_imp_exists (Std.UScalar.rem_spec a h)
  exact ⟨v, h_eq, h_v⟩

/-- `(1#usize <<< n)` succeeds with value `2^n.val`. -/
theorem usize_shl_one_ok (n : Std.Usize) (hn : n.val < UScalarTy.Usize.numBits) :
    ∃ len : Std.Usize, (1#usize <<< n : RustM Std.Usize) = .ok len ∧ len.val = 2 ^ n.val := by
  have h_one_shl_pow : ((1#usize : Std.Usize).val <<< n.val) < 2 ^ System.Platform.numBits := by
    have h_one_eq : (1#usize : Std.Usize).val = 1 := rfl
    rw [h_one_eq, Nat.shiftLeft_eq, Nat.one_mul]
    have hnb : n.val < System.Platform.numBits := by
      rwa [Std.UScalarTy.Usize_numBits_eq] at hn
    rcases System.Platform.numBits_eq with h32 | h64
    · rw [h32]; rw [h32] at hnb; exact Nat.pow_lt_pow_right (by decide) hnb
    · rw [h64]; rw [h64] at hnb; exact Nat.pow_lt_pow_right (by decide) hnb
  have hT := Aeneas.Std.UScalar.ShiftLeft_spec (1#usize : Std.Usize) n
    (Aeneas.Std.UScalar.size Aeneas.Std.UScalarTy.Usize) hn rfl
  obtain ⟨z, h_eq, h_v_mod, _h_bv⟩ := Std.WP.spec_imp_exists hT
  refine ⟨z, h_eq, ?_⟩
  have h_one_eq : (1#usize : Std.Usize).val = 1 := rfl
  have h_size_eq : (Aeneas.Std.UScalar.size Aeneas.Std.UScalarTy.Usize)
      = 2 ^ System.Platform.numBits := by
    rw [Aeneas.Std.UScalar.size]; rw [Std.UScalarTy.Usize_numBits_eq]
  rw [h_v_mod, h_one_eq, h_size_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt]
  rw [h_one_eq, Nat.shiftLeft_eq, Nat.one_mul] at h_one_shl_pow
  exact h_one_shl_pow

end libcrux_iot_ml_kem.Util.ScalarSpecs
