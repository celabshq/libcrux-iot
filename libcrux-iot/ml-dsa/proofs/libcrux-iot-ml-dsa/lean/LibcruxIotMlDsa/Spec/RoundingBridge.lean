/-
  # `Spec/RoundingBridge.lean` — hand spec ↔ extracted hacspec, ROUNDING layer

  `Spec/HacspecBridge.lean` does this for the poly layer (`poly_add`/`poly_sub`/
  `poly_pointwise_mul`) so that the extracted `hacspec_ml_dsa.*` spec, not the
  hand-written Lean one, is the trusted reference. The rounding layer had no such
  bridge, even though `specs/ml-dsa/src/arithmetic.rs` carries the whole of it
  (`mod_q`, `mod_pm`, `power2round`, `decompose`, ...) and `Spec/Rounding.lean`
  describes itself as a "faithful translation" of exactly that file.

  This is that bridge for `mod_pm` and `decompose`. Both sides are the same
  algorithm; what has to be supplied is

    * the checked-arithmetic plumbing — each operation stays in range, so the
      extraction returns `.ok` rather than `fail`; and
    * that Aeneas's TRUNCATED `%` / `/` (`Int.tmod` / `Int.tdiv`, Rust semantics)
      agree with Lean's `Int` `%` / `/` (`emod` / `ediv`) on the non-negative
      arguments that actually occur here.

  `Spec.HacspecBridge.mod_q_eq` is the already-proved companion for the `mod_q`
  step and the source of the idiom used below (`IScalar.rem_spec`,
  `IScalar.cast_inBounds_spec`, `IScalar.add_spec` via `spec_of_partialSpec`).
-/
import LibcruxIotMlDsa.Spec.HacspecBridge
import LibcruxIotMlDsa.Spec.Rounding

open CoreModels Aeneas Aeneas.Std RustM Std.Do

namespace libcrux_iot_ml_dsa.Spec.RoundingBridge

open libcrux_iot_ml_dsa.Spec
open libcrux_iot_ml_dsa.Spec.Parameters
open libcrux_iot_ml_dsa.Spec.Rounding

set_option maxHeartbeats 2000000

/-! ## Small arithmetic facts -/

private theorem hQval : (hacspec_ml_dsa.parameters.Q).val = 8380417 := by
  unfold hacspec_ml_dsa.parameters.Q; decide

private theorem v0 : ((0#i32 : Std.I32)).val = 0 := by decide
private theorem v1 : ((1#i32 : Std.I32)).val = 1 := by decide

/-- Every `I32` fits in an `I64`, so the widening casts always succeed. -/
private theorem i32_fits_i64 (x : Std.I32) :
    Aeneas.Std.IScalar.min .I64 ≤ x.val ∧ x.val ≤ Aeneas.Std.IScalar.max .I64 := by
  simp only [Aeneas.Std.IScalar.min_IScalarTy_I64_eq, Aeneas.Std.IScalar.max_IScalarTy_I64_eq,
    Aeneas.Std.I64.min, Aeneas.Std.I64.max, Aeneas.Std.I64.numBits,
    Aeneas.Std.IScalarTy.I64_numBits_eq]
  scalar_tac

/-- `modPm` on a NON-NEGATIVE argument: the double reduction collapses. -/
private theorem modPm_of_nonneg (a m : Int) (_ha : 0 ≤ a) (_hm : 0 < m) :
    modPm a m = (if a % m > m / 2 then a % m - m else a % m) := by
  unfold modPm
  have hcollapse : ((a % m) + m) % m = a % m := by
    rw [Int.add_emod_right, Int.emod_emod_of_dvd _ dvd_rfl]
  rw [hcollapse]

/-! ## `mod_pm` -/

/-- **`mod_pm` bridge.** For a non-negative `a` and a positive `m` (which is what
    `decompose` feeds it), the extracted `mod_pm` succeeds and computes the hand
    spec's `modPm`. -/
theorem mod_pm_eq (a m : Std.I32) (ha : 0 ≤ a.val) (hm0 : 0 < m.val)
    (hmb : m.val ≤ 1000000) :
    ∃ r : Std.I32, hacspec_ml_dsa.arithmetic.mod_pm a m = .ok r
      ∧ r.val = modPm a.val m.val := by
  unfold hacspec_ml_dsa.arithmetic.mod_pm
  -- the two widening casts
  obtain ⟨a64, ha64_eq, ha64_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Aeneas.Std.IScalar.cast_inBounds_spec .I64 a (i32_fits_i64 a))
  rw [ha64_eq]; simp only [Aeneas.Std.bind_tc_ok]
  obtain ⟨m64, hm64_eq, hm64_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Aeneas.Std.IScalar.cast_inBounds_spec .I64 m (i32_fits_i64 m))
  rw [hm64_eq]; simp only [Aeneas.Std.bind_tc_ok]
  have hm64_nz : m64.val ≠ 0 := by rw [hm64_val]; omega
  -- i = a64 % m64 = a.val % m.val   (tmod = emod on a nonneg argument)
  obtain ⟨i, hi_eq, hi_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Aeneas.Std.IScalar.rem_spec a64 hm64_nz
        (by rw [hm64_val]; simp only [not_and]; intro _; omega))
  rw [hi_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [ha64_val, hm64_val, Int.tmod_eq_emod_of_nonneg ha] at hi_val
  have hi_lo : 0 ≤ i.val := by rw [hi_val]; exact Int.emod_nonneg _ (by omega)
  have hi_hi : i.val < m.val := by rw [hi_val]; exact Int.emod_lt_of_pos _ hm0
  -- i1 = i + m64, in [m, 2m)
  obtain ⟨i1, hi1_eq, hi1_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Aeneas.Std.WP.spec_of_partialSpec (@Std.IScalar.add_spec _ i m64)
        (fun e => by
          cases e <;>
            simp_all [Aeneas.Std.IScalar.min_IScalarTy_I64_eq,
              Aeneas.Std.IScalar.max_IScalarTy_I64_eq, Aeneas.Std.I64.min,
              Aeneas.Std.I64.max, Aeneas.Std.I64.numBits,
              Aeneas.Std.IScalarTy.I64_numBits_eq]; omega)
        (by simp))
  rw [hi1_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hm64_val] at hi1_val
  -- r = i1 % m64 = i  (i1 in [m, 2m) so the truncated remainder is i1 - m)
  obtain ⟨r, hr_eq, hr_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Aeneas.Std.IScalar.rem_spec i1 hm64_nz
        (by rw [hm64_val]; simp only [not_and]; intro _; omega))
  rw [hr_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hm64_val, hi1_val, Int.tmod_eq_emod_of_nonneg (by omega)] at hr_val
  have hr_i : r.val = i.val := by
    rw [hr_val, Int.add_emod_right]
    exact Int.emod_eq_of_lt hi_lo hi_hi
  -- narrow back to I32
  have hrb : Aeneas.Std.IScalar.min .I32 ≤ r.val ∧ r.val ≤ Aeneas.Std.IScalar.max .I32 := by
    simp only [Aeneas.Std.IScalar.min_IScalarTy_I32_eq, Aeneas.Std.IScalar.max_IScalarTy_I32_eq,
      Aeneas.Std.I32.min, Aeneas.Std.I32.max, Aeneas.Std.I32.numBits,
      Aeneas.Std.IScalarTy.I32_numBits_eq]
    rw [hr_i]; omega
  obtain ⟨r1, hr1_eq, hr1_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.cast_inBounds_spec .I32 r hrb)
  rw [hr1_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr_i] at hr1_val
  -- i2 = m / 2
  obtain ⟨i2, hi2_eq, hi2_val⟩ :=
    Aeneas.Std.IScalar.div_spec (x := m) (y := 2#i32) (by decide)
      (by simp only [not_and]; intro _; decide)
  rw [hi2_eq]; simp only [Aeneas.Std.bind_tc_ok]
  have hi2 : i2.val = m.val / 2 := by
    rw [hi2_val]
    show Int.tdiv m.val (2 : Int) = m.val / 2
    exact Int.tdiv_eq_ediv_of_nonneg (by omega)
  rw [modPm_of_nonneg a.val m.val ha hm0, ← hi_val]
  have hiff : (r1 > i2) ↔ i.val > m.val / 2 := by
    simp only [gt_iff_lt, Aeneas.Std.IScalar.lt_equiv, hr1_val, hi2]
  by_cases hgt : i.val > m.val / 2
  · rw [if_pos (hiff.mpr hgt), if_pos hgt]
    obtain ⟨r2, hr2_eq, hr2_val⟩ :=
      Aeneas.Std.WP.spec_imp_exists
        (Aeneas.Std.WP.spec_of_partialSpec (@Std.IScalar.sub_spec _ r1 m)
          (fun e => by
            cases e <;>
              simp_all [Aeneas.Std.IScalar.min_IScalarTy_I32_eq,
                Aeneas.Std.IScalar.max_IScalarTy_I32_eq, Aeneas.Std.I32.min,
                Aeneas.Std.I32.max, Aeneas.Std.I32.numBits,
                Aeneas.Std.IScalarTy.I32_numBits_eq]; omega)
          (by simp))
    exact ⟨r2, hr2_eq, by rw [hr2_val, hr1_val]⟩
  · rw [if_neg (fun h => hgt (hiff.mp h)), if_neg hgt]
    exact ⟨r1, rfl, hr1_val⟩

/-! ## `decompose` -/

/-- **`decompose` bridge.** On a canonical `r` in `[0, Q)` and a FIPS-204 `gamma2`,
    the extracted `decompose` succeeds and returns the hand spec's pair. -/
theorem decompose_eq (rc gamma2 : Std.I32)
    (hlo : 0 ≤ rc.val) (hhi : rc.val < 8380417)
    (hg : gamma2 = 95232#i32 ∨ gamma2 = 261888#i32) :
    ∃ r1 r0 : Std.I32,
      hacspec_ml_dsa.arithmetic.decompose rc gamma2 = .ok (r1, r0)
        ∧ r1.val = (Rounding.decompose rc.val gamma2.val).1
        ∧ r0.val = (Rounding.decompose rc.val gamma2.val).2 := by
  have hgval : gamma2.val = 95232 ∨ gamma2.val = 261888 := by
    rcases hg with h | h <;> subst h <;> [left; right] <;> decide
  unfold hacspec_ml_dsa.arithmetic.decompose
  -- r_plus = rc % Q = rc
  obtain ⟨rp, hrp_eq, hrp_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Aeneas.Std.IScalar.rem_spec rc (by rw [hQval]; decide)
        (by rw [hQval]; simp only [not_and]; intro _; decide))
  rw [hrp_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hQval, Int.tmod_eq_emod_of_nonneg hlo] at hrp_val
  have hrp : rp.val = rc.val := by
    rw [hrp_val]; exact Int.emod_eq_of_lt hlo (by omega)
  -- the `if r_plus < 0` guard is dead
  have hnn : ¬ (rp < (0#i32 : Std.I32)) := by
    simp only [Aeneas.Std.IScalar.lt_equiv, v0]
    omega
  rw [show (if rp < (0#i32 : Std.I32) then rp + hacspec_ml_dsa.parameters.Q
            else ok rp) = ok rp from by rw [if_neg hnn]]
  simp only [Aeneas.Std.bind_tc_ok]
  -- alpha = 2 * gamma2
  obtain ⟨alpha, halpha_eq, halpha_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Aeneas.Std.IScalar.mul_spec (x := (2#i32 : Std.I32)) (y := gamma2)
        (by simp only [Aeneas.Std.IScalar.min_IScalarTy_I32_eq, Aeneas.Std.I32.min,
              Aeneas.Std.I32.numBits, Aeneas.Std.IScalarTy.I32_numBits_eq]
            show (-2147483648 : Int) ≤ (2 : Int) * gamma2.val
            rcases hgval with h | h <;> rw [h] <;> decide)
        (by simp only [Aeneas.Std.IScalar.max_IScalarTy_I32_eq, Aeneas.Std.I32.max,
              Aeneas.Std.I32.numBits, Aeneas.Std.IScalarTy.I32_numBits_eq]
            show (2 : Int) * gamma2.val ≤ 2147483647
            rcases hgval with h | h <;> rw [h] <;> decide))
  rw [halpha_eq]; simp only [Aeneas.Std.bind_tc_ok]
  have halpha : alpha.val = 2 * gamma2.val := by
    rw [halpha_val]; show (2 : Int) * gamma2.val = _; ring
  have halpha_pos : 0 < alpha.val := by rw [halpha]; rcases hgval with h | h <;> rw [h] <;> decide
  have halpha_bnd : alpha.val ≤ 1000000 := by
    rw [halpha]; rcases hgval with h | h <;> rw [h] <;> decide
  -- r0 = mod_pm r_plus alpha
  obtain ⟨r0, hr0_eq, hr0_val⟩ :=
    mod_pm_eq rp alpha (by rw [hrp]; exact hlo) halpha_pos halpha_bnd
  rw [hr0_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hrp, halpha] at hr0_val
  -- r0 is the centred representative, so |r0| <= alpha/2
  have hr0_bnd : -(alpha.val) ≤ r0.val ∧ r0.val ≤ alpha.val := by
    rw [hr0_val, modPm_of_nonneg rc.val (2 * gamma2.val) hlo (by omega)]
    have h1 : 0 ≤ rc.val % (2 * gamma2.val) :=
      Int.emod_nonneg _ (by omega)
    have h2 : rc.val % (2 * gamma2.val) < 2 * gamma2.val :=
      Int.emod_lt_of_pos _ (by omega)
    rw [halpha]
    split <;> omega
  -- i = r_plus - r0
  obtain ⟨d, hd_eq, hd_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Aeneas.Std.WP.spec_of_partialSpec (@Std.IScalar.sub_spec _ rp r0)
        (fun e => by
          cases e <;>
            (try simp only [Aeneas.Std.IScalar.min_IScalarTy_I32_eq,
              Aeneas.Std.IScalar.max_IScalarTy_I32_eq, Aeneas.Std.I32.min,
              Aeneas.Std.I32.max, Aeneas.Std.I32.numBits,
              Aeneas.Std.IScalarTy.I32_numBits_eq, not_or, not_lt]) <;>
            first | exact not_false | omega)
        (by simp))
  rw [hd_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hrp] at hd_val
  -- i1 = Q - 1
  obtain ⟨qm1, hqm1_eq, hqm1_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Aeneas.Std.WP.spec_of_partialSpec
        (@Std.IScalar.sub_spec _ hacspec_ml_dsa.parameters.Q (1#i32 : Std.I32))
        (fun e => by
          cases e <;>
            (try simp only [hQval, Aeneas.Std.IScalar.min_IScalarTy_I32_eq,
              Aeneas.Std.IScalar.max_IScalarTy_I32_eq, Aeneas.Std.I32.min,
              Aeneas.Std.I32.max, Aeneas.Std.I32.numBits,
              Aeneas.Std.IScalarTy.I32_numBits_eq, v1, not_or, not_lt]) <;>
            first | exact not_false | omega)
        (by simp))
  rw [hqm1_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hQval] at hqm1_val
  -- and now the two branches, in lockstep with the hand spec
  unfold Rounding.decompose
  simp only [Rounding.Qi]
  have hQi : (Q : Int) = 8380417 := by norm_num [Q]
  rw [show rc.val % (Q : Int) = rc.val from by rw [hQi]; exact Int.emod_eq_of_lt hlo (by omega)]
  rw [if_neg (show ¬ (rc.val < 0) from by omega)]
  by_cases hb : d = qm1
  · rw [if_pos hb]
    have hb' : rc.val - r0.val = (Q : Int) - 1 := by
      have h := congrArg Aeneas.Std.IScalar.val hb
      rw [hd_val, hqm1_val, v1] at h
      rw [hQi]; omega
    rw [if_pos (by rw [← hr0_val]; exact hb')]
    obtain ⟨r0m1, hr0m1_eq, hr0m1_val⟩ :=
      Aeneas.Std.WP.spec_imp_exists
        (Aeneas.Std.WP.spec_of_partialSpec (@Std.IScalar.sub_spec _ r0 (1#i32 : Std.I32))
          (fun e => by
          cases e <;>
            (try simp only [Aeneas.Std.IScalar.min_IScalarTy_I32_eq,
              Aeneas.Std.IScalar.max_IScalarTy_I32_eq, Aeneas.Std.I32.min,
              Aeneas.Std.I32.max, Aeneas.Std.I32.numBits,
              Aeneas.Std.IScalarTy.I32_numBits_eq, v1, not_or, not_lt]) <;>
            first | exact not_false | omega)
          (by simp))
    rw [hr0m1_eq]; simp only [Aeneas.Std.bind_tc_ok]
    refine ⟨0#i32, r0m1, rfl, v0, ?_⟩
    rw [hr0m1_val, hr0_val, v1]
  · rw [if_neg hb]
    have hb' : ¬ (rc.val - r0.val = (Q : Int) - 1) := by
      intro h
      refine hb (Aeneas.Std.IScalar.eq_of_val_eq ?_)
      rw [hd_val, hqm1_val, v1]
      rw [hQi] at h
      omega
    rw [if_neg (by rw [← hr0_val]; exact hb')]
    -- the quotient: `d` is a non-negative multiple of alpha, so tdiv = ediv
    have hd_nonneg : 0 ≤ d.val := by
      rw [hd_val, hr0_val, modPm_of_nonneg rc.val (2 * gamma2.val) hlo (by omega)]
      have h1 : 0 ≤ rc.val % (2 * gamma2.val) := Int.emod_nonneg _ (by omega)
      have h2 : rc.val % (2 * gamma2.val) < 2 * gamma2.val := Int.emod_lt_of_pos _ (by omega)
      have h3 : rc.val % (2 * gamma2.val) ≤ rc.val := by
        have h4 := Int.emod_add_mul_ediv rc.val (2 * gamma2.val)
        have h5 : 0 ≤ (2 * gamma2.val) * (rc.val / (2 * gamma2.val)) :=
          mul_nonneg (by omega) (Int.ediv_nonneg hlo (by omega))
        omega
      split <;> omega
    obtain ⟨q, hq_eq, hq_val⟩ :=
      Aeneas.Std.IScalar.div_spec (x := d) (y := alpha) (by omega)
        (by simp only [not_and]; intro _; omega)
    rw [hq_eq]; simp only [Aeneas.Std.bind_tc_ok]
    refine ⟨q, r0, rfl, ?_, by rw [hr0_val]⟩
    rw [hq_val, hd_val, halpha, hr0_val]
    exact Int.tdiv_eq_ediv_of_nonneg (by rw [hd_val, hr0_val] at hd_nonneg; exact hd_nonneg)

/-! ## `power2round`

    Simpler than `decompose`: no `gamma2`, and no `Q - 1` boundary branch. The
    modulus is the constant `2^D = 8192`, which the extraction builds with a
    shift. -/

/-- **`power2round` bridge.** On a canonical `r` in `[0, Q)` the extracted
    `power2round` succeeds and returns the hand spec's pair. -/
theorem power2round_eq (rc : Std.I32)
    (hlo : 0 ≤ rc.val) (hhi : rc.val < 8380417) :
    ∃ r1 r0 : Std.I32,
      hacspec_ml_dsa.arithmetic.power2round rc = .ok (r1, r0)
        ∧ r1.val = (Rounding.power2round rc.val).1
        ∧ r0.val = (Rounding.power2round rc.val).2 := by
  unfold hacspec_ml_dsa.arithmetic.power2round
  -- r_plus = rc % Q = rc, and the `< 0` guard is dead
  obtain ⟨rp, hrp_eq, hrp_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Aeneas.Std.IScalar.rem_spec rc (by rw [hQval]; decide)
        (by rw [hQval]; simp only [not_and]; intro _; decide))
  rw [hrp_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hQval, Int.tmod_eq_emod_of_nonneg hlo] at hrp_val
  have hrp : rp.val = rc.val := by
    rw [hrp_val]; exact Int.emod_eq_of_lt hlo (by omega)
  have hnn : ¬ (rp < (0#i32 : Std.I32)) := by
    simp only [Aeneas.Std.IScalar.lt_equiv, v0]; omega
  rw [show (if rp < (0#i32 : Std.I32) then rp + hacspec_ml_dsa.parameters.Q
            else ok rp) = ok rp from by rw [if_neg hnn]]
  simp only [Aeneas.Std.bind_tc_ok]
  -- two_d = 1 <<< D = 8192, a closed term
  rw [show ((1#i32 : Std.I32) <<< hacspec_ml_dsa.parameters.D : RustM Std.I32)
        = ok (8192#i32 : Std.I32) from by
      unfold hacspec_ml_dsa.parameters.D; rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  have htwod : ((8192#i32 : Std.I32)).val = 8192 := by decide
  -- r0 = mod_pm r_plus two_d
  obtain ⟨r0, hr0_eq, hr0_val⟩ :=
    mod_pm_eq rp (8192#i32) (by rw [hrp]; exact hlo) (by rw [htwod]; decide)
      (by rw [htwod]; decide)
  rw [hr0_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hrp, htwod] at hr0_val
  have hr0_bnd : -8192 ≤ r0.val ∧ r0.val ≤ 8192 := by
    rw [hr0_val, modPm_of_nonneg rc.val 8192 hlo (by decide)]
    have h1 : 0 ≤ rc.val % 8192 := Int.emod_nonneg _ (by decide)
    have h2 : rc.val % 8192 < 8192 := Int.emod_lt_of_pos _ (by decide)
    split <;> omega
  -- i = r_plus - r0, non-negative (r0 is the centred representative)
  obtain ⟨d, hd_eq, hd_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Aeneas.Std.WP.spec_of_partialSpec (@Std.IScalar.sub_spec _ rp r0)
        (fun e => by
          cases e <;>
            (try simp only [Aeneas.Std.IScalar.min_IScalarTy_I32_eq,
              Aeneas.Std.IScalar.max_IScalarTy_I32_eq, Aeneas.Std.I32.min,
              Aeneas.Std.I32.max, Aeneas.Std.I32.numBits,
              Aeneas.Std.IScalarTy.I32_numBits_eq, not_or, not_lt]) <;>
            first | exact not_false | omega)
        (by simp))
  rw [hd_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hrp] at hd_val
  have hd_nonneg : 0 ≤ d.val := by
    rw [hd_val, hr0_val, modPm_of_nonneg rc.val 8192 hlo (by decide)]
    have h1 : 0 ≤ rc.val % 8192 := Int.emod_nonneg _ (by decide)
    have h2 : rc.val % 8192 < 8192 := Int.emod_lt_of_pos _ (by decide)
    have h3 : rc.val % 8192 ≤ rc.val := by
      have h4 := Int.emod_add_mul_ediv rc.val (8192 : Int)
      have h5 : 0 ≤ (8192 : Int) * (rc.val / 8192) :=
        mul_nonneg (by decide) (Int.ediv_nonneg hlo (by decide))
      omega
    split <;> omega
  -- r1 = i / two_d, and `tdiv = ediv` because `i >= 0`
  obtain ⟨r1, hr1_eq, hr1_val⟩ :=
    Aeneas.Std.IScalar.div_spec (x := d) (y := (8192#i32 : Std.I32)) (by decide)
      (by simp only [not_and]; intro _; decide)
  rw [hr1_eq]; simp only [Aeneas.Std.bind_tc_ok]
  refine ⟨r1, r0, rfl, ?_, ?_⟩
  · unfold Rounding.power2round
    simp only [Rounding.Qi, Rounding.twoD]
    have hQi : (Q : Int) = 8380417 := by norm_num [Q]
    rw [show rc.val % (Q : Int) = rc.val from by
      rw [hQi]; exact Int.emod_eq_of_lt hlo (by omega)]
    rw [if_neg (show ¬ (rc.val < 0) from by omega)]
    rw [hr1_val, hd_val, htwod, hr0_val]
    exact Int.tdiv_eq_ediv_of_nonneg (by rw [hd_val, hr0_val] at hd_nonneg; exact hd_nonneg)
  · unfold Rounding.power2round
    simp only [Rounding.Qi, Rounding.twoD]
    have hQi : (Q : Int) = 8380417 := by norm_num [Q]
    rw [show rc.val % (Q : Int) = rc.val from by
      rw [hQi]; exact Int.emod_eq_of_lt hlo (by omega)]
    rw [if_neg (show ¬ (rc.val < 0) from by omega)]
    rw [hr0_val]
    norm_num [Rounding.Dbits]

/-! ## `use_hint`

    A step beyond `decompose`/`power2round`: the result depends on `decompose`'s
    `r1`, so the bridge first needs a BOUND on that (for overflow-freedom of the
    `r1 +- 1`), and the `((r1 - 1) % m + m) % m` cannot be handled by a pointwise
    `tmod = emod` rewrite -- the intermediate genuinely differs (`-1` vs `m - 1`)
    and the two only agree after the second reduction. -/

/-- `decompose`'s high part is small: `0 <= r1 <= 44` for both FIPS-204 `gamma2`.
    Enough for every `+- 1` below to be overflow-free. -/
private theorem decompose_fst_bnd (rc gamma2 : Int)
    (hlo : 0 ≤ rc) (hhi : rc < 8380417) (hg : gamma2 = 95232 ∨ gamma2 = 261888) :
    0 ≤ (Rounding.decompose rc gamma2).1 ∧ (Rounding.decompose rc gamma2).1 ≤ 44 := by
  have halpha_pos : 0 < 2 * gamma2 := by rcases hg with h | h <;> rw [h] <;> decide
  have hQi : (Rounding.Qi) = 8380417 := by norm_num [Rounding.Qi, Q]
  simp only [Rounding.decompose, hQi]
  rw [show rc % (8380417 : Int) = rc from Int.emod_eq_of_lt hlo (by omega)]
  rw [if_neg (show ¬ (rc < 0) from by omega)]
  have hr0 := modPm_of_nonneg rc (2 * gamma2) hlo halpha_pos
  have h1 : 0 ≤ rc % (2 * gamma2) := Int.emod_nonneg _ (by omega)
  have h2 : rc % (2 * gamma2) < 2 * gamma2 := Int.emod_lt_of_pos _ halpha_pos
  have hd_lo : 0 ≤ rc - modPm rc (2 * gamma2) := by
    rw [hr0]
    have h3 : rc % (2 * gamma2) ≤ rc := by
      have h4 := Int.emod_add_mul_ediv rc (2 * gamma2)
      have h5 : 0 ≤ (2 * gamma2) * (rc / (2 * gamma2)) :=
        mul_nonneg (by omega) (Int.ediv_nonneg hlo (by omega))
      omega
    split <;> omega
  have hd_hi : rc - modPm rc (2 * gamma2) ≤ 8380416 + gamma2 := by
    rw [hr0]; split <;> omega
  split
  · simp
  · refine ⟨Int.ediv_nonneg hd_lo (by omega), ?_⟩
    have hmono : (rc - modPm rc (2 * gamma2)) / (2 * gamma2)
        ≤ (8380416 + gamma2) / (2 * gamma2) := Int.ediv_le_ediv halpha_pos hd_hi
    rcases hg with h | h <;> rw [h] at hmono ⊢ <;>
      exact le_trans hmono (by decide)

/-- **`use_hint` bridge.** On a canonical `r` in `[0, Q)` the extracted
    `use_hint` succeeds and computes the hand spec's `useHint`. -/
theorem use_hint_eq (b : Bool) (rc gamma2 : Std.I32)
    (hlo : 0 ≤ rc.val) (hhi : rc.val < 8380417)
    (hg : gamma2 = 95232#i32 ∨ gamma2 = 261888#i32) :
    ∃ z : Std.I32, hacspec_ml_dsa.arithmetic.use_hint b rc gamma2 = .ok z
      ∧ z.val = Rounding.useHint b rc.val gamma2.val := by
  have hgval : gamma2.val = 95232 ∨ gamma2.val = 261888 := by
    rcases hg with h | h <;> subst h <;> [left; right] <;> decide
  have hQi : (Rounding.Qi) = 8380417 := by norm_num [Rounding.Qi, Q]
  unfold hacspec_ml_dsa.arithmetic.use_hint
  -- i = Q - 1
  obtain ⟨i, hi_eq, hi_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Aeneas.Std.WP.spec_of_partialSpec
        (@Std.IScalar.sub_spec _ hacspec_ml_dsa.parameters.Q (1#i32 : Std.I32))
        (fun e => by
          cases e <;>
            (try simp only [hQval, Aeneas.Std.IScalar.min_IScalarTy_I32_eq,
              Aeneas.Std.IScalar.max_IScalarTy_I32_eq, Aeneas.Std.I32.min,
              Aeneas.Std.I32.max, Aeneas.Std.I32.numBits,
              Aeneas.Std.IScalarTy.I32_numBits_eq, v1, not_or, not_lt]) <;>
            first | exact not_false | omega)
        (by simp))
  rw [hi_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hQval, v1] at hi_val
  -- i1 = 2 * gamma2
  obtain ⟨i1, hi1_eq, hi1_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Aeneas.Std.IScalar.mul_spec (x := (2#i32 : Std.I32)) (y := gamma2)
        (by simp only [Aeneas.Std.IScalar.min_IScalarTy_I32_eq, Aeneas.Std.I32.min,
              Aeneas.Std.I32.numBits, Aeneas.Std.IScalarTy.I32_numBits_eq]
            show (-2147483648 : Int) ≤ (2 : Int) * gamma2.val
            rcases hgval with h | h <;> rw [h] <;> decide)
        (by simp only [Aeneas.Std.IScalar.max_IScalarTy_I32_eq, Aeneas.Std.I32.max,
              Aeneas.Std.I32.numBits, Aeneas.Std.IScalarTy.I32_numBits_eq]
            show (2 : Int) * gamma2.val ≤ 2147483647
            rcases hgval with h | h <;> rw [h] <;> decide))
  rw [hi1_eq]; simp only [Aeneas.Std.bind_tc_ok]
  have hi1 : i1.val = 2 * gamma2.val := by
    rw [hi1_val]; show (2 : Int) * gamma2.val = _; ring
  have hi1_pos : 0 < i1.val := by rw [hi1]; rcases hgval with h | h <;> rw [h] <;> decide
  -- m = (Q - 1) / (2 * gamma2)
  obtain ⟨m, hm_eq, hm_val⟩ :=
    Aeneas.Std.IScalar.div_spec (x := i) (y := i1) (by omega)
      (by simp only [not_and]; intro _; omega)
  rw [hm_eq]; simp only [Aeneas.Std.bind_tc_ok]
  have hm : m.val = 8380416 / (2 * gamma2.val) := by
    rw [hm_val, hi_val, hi1]
    exact Int.tdiv_eq_ediv_of_nonneg (by decide)
  have hm_pos : 0 < m.val := by
    rw [hm]; rcases hgval with h | h <;> rw [h] <;> decide
  have hm_bnd : m.val ≤ 44 := by
    rw [hm]; rcases hgval with h | h <;> rw [h] <;> decide
  have hm_lo : 16 ≤ m.val := by
    rw [hm]; rcases hgval with h | h <;> rw [h] <;> decide
  have hm_ne : m.val ≠ 0 := by omega
  have hm_ne1 : m.val ≠ -1 := by omega
  -- the spec's `m` is the same number
  have hspec_m : (Rounding.Qi - 1) / (2 * gamma2.val) = m.val := by
    rw [hQi, hm]; norm_num
  -- decompose, via the bridge
  obtain ⟨r1, r0, hd_eq, hr1_val, hr0_val⟩ := decompose_eq rc gamma2 hlo hhi hg
  rw [hd_eq]; simp only [Aeneas.Std.bind_tc_ok]
  obtain ⟨hr1_lo, hr1_hi⟩ := decompose_fst_bnd rc.val gamma2.val hlo hhi hgval
  rw [← hr1_val] at hr1_lo hr1_hi
  -- spec side
  simp only [Rounding.useHint]
  rw [hspec_m, ← hr1_val, ← hr0_val]
  -- NOTE the extracted side still carries `let (r1, r0) := (r1, r0)`, which
  -- REBINDS `r1`/`r0` as fresh locals shadowing these ones. No `rw`/`simp only`
  -- mentioning the outer names can fire inside it, and neither `dsimp only` nor
  -- `simp only []` reduces it. Plain `simp`, given every equation at once, does.
  cases b with
  | false =>
      exact ⟨r1, rfl, by rw [if_neg (by simp), if_neg (by simp)]⟩
  | true =>
      by_cases hpos : (0 : Int) < r0.val
      · -- hint set, r0 > 0: (r1 + 1) % m
        have hsc : r0 > (0#i32 : Std.I32) := by
          simp only [gt_iff_lt, Aeneas.Std.IScalar.lt_equiv, v0]; omega
        obtain ⟨z1, hz1_eq, hz1_val⟩ :=
          Aeneas.Std.WP.spec_imp_exists
            (Aeneas.Std.WP.spec_of_partialSpec (@Std.IScalar.add_spec _ r1 (1#i32 : Std.I32))
              (fun e => by
          cases e <;>
            (try simp only [Aeneas.Std.IScalar.min_IScalarTy_I32_eq,
              Aeneas.Std.IScalar.max_IScalarTy_I32_eq, Aeneas.Std.I32.min,
              Aeneas.Std.I32.max, Aeneas.Std.I32.numBits,
              Aeneas.Std.IScalarTy.I32_numBits_eq, v1, not_or, not_lt]) <;>
            first | exact not_false | omega)
              (by simp))
        rw [v1] at hz1_val
        obtain ⟨z, hz_eq, hz_val⟩ :=
          Aeneas.Std.WP.spec_imp_exists
            (Aeneas.Std.IScalar.rem_spec (y := m) z1 hm_ne
              (by simp only [not_and]; intro _; exact hm_ne1))
        refine ⟨z, by simp [hz1_eq, hz_eq]; omega, ?_⟩
        rw [if_pos (show (true = true) ∧ r0.val > 0 from ⟨rfl, hpos⟩)]
        rw [hz_val, hz1_val]
        exact Int.tmod_eq_emod_of_nonneg (by omega)
      · -- hint set, r0 <= 0: ((r1 - 1) % m + m) % m
        have hsc : ¬ (r0 > (0#i32 : Std.I32)) := by
          intro h
          simp only [gt_iff_lt, Aeneas.Std.IScalar.lt_equiv, v0] at h
          omega
        have hsc2 : r0 ≤ (0#i32 : Std.I32) := by
          simp only [Aeneas.Std.IScalar.le_equiv, v0]; omega
        obtain ⟨y1, hy1_eq, hy1_val⟩ :=
          Aeneas.Std.WP.spec_imp_exists
            (Aeneas.Std.WP.spec_of_partialSpec (@Std.IScalar.sub_spec _ r1 (1#i32 : Std.I32))
              (fun e => by
          cases e <;>
            (try simp only [Aeneas.Std.IScalar.min_IScalarTy_I32_eq,
              Aeneas.Std.IScalar.max_IScalarTy_I32_eq, Aeneas.Std.I32.min,
              Aeneas.Std.I32.max, Aeneas.Std.I32.numBits,
              Aeneas.Std.IScalarTy.I32_numBits_eq, v1, not_or, not_lt]) <;>
            first | exact not_false | omega)
              (by simp))
        rw [v1] at hy1_val
        obtain ⟨y2, hy2_eq, hy2_val⟩ :=
          Aeneas.Std.WP.spec_imp_exists
            (Aeneas.Std.IScalar.rem_spec (y := m) y1 hm_ne
              (by simp only [not_and]; intro _; exact hm_ne1))
        -- `y2 = (r1 - 1) tmod m`, hence `|y2| < m`
        have hy2_bnd : -m.val < y2.val ∧ y2.val < m.val := by
          have hb : (Int.tmod y1.val m.val).natAbs = (y1.val).natAbs % (m.val).natAbs :=
            Int.natAbs_tmod y1.val m.val
          have hlt : (Int.tmod y1.val m.val).natAbs < (m.val).natAbs := by
            rw [hb]; exact Nat.mod_lt _ (by omega)
          rw [hy2_val]; omega
        obtain ⟨y3, hy3_eq, hy3_val⟩ :=
          Aeneas.Std.WP.spec_imp_exists
            (Aeneas.Std.WP.spec_of_partialSpec (@Std.IScalar.add_spec _ y2 m)
              (fun e => by
                cases e <;>
                  (try simp only [Aeneas.Std.IScalar.min_IScalarTy_I32_eq,
              Aeneas.Std.IScalar.max_IScalarTy_I32_eq, Aeneas.Std.I32.min,
              Aeneas.Std.I32.max, Aeneas.Std.I32.numBits,
              Aeneas.Std.IScalarTy.I32_numBits_eq, not_or, not_lt]) <;>
                  first | exact not_false | omega)
              (by simp))
        obtain ⟨z, hz_eq, hz_val⟩ :=
          Aeneas.Std.WP.spec_imp_exists
            (Aeneas.Std.IScalar.rem_spec (y := m) y3 hm_ne
              (by simp only [not_and]; intro _; exact hm_ne1))
        have hle : r0.val ≤ 0 := by omega
        refine ⟨z, by simp [hpos, hle, hy1_eq, hy2_eq, hy3_eq, hz_eq], ?_⟩
        rw [if_neg (show ¬ ((true = true) ∧ r0.val > 0) from by
              rintro ⟨-, h⟩; omega),
          if_pos (show (true = true) ∧ r0.val ≤ 0 from ⟨rfl, by omega⟩)]
        -- both sides reduce to `(r1 - 1) emod m`
        have hspec : ((r1.val - 1) % m.val + m.val) % m.val = (r1.val - 1) % m.val := by
          rw [Int.add_emod_right, Int.emod_emod_of_dvd _ dvd_rfl]
        rw [hspec, hz_val, hy3_val, hy2_val, hy1_val]
        by_cases hz0 : 0 ≤ r1.val - 1
        · -- non-negative: the two semantics agree throughout
          rw [Int.tmod_eq_emod_of_nonneg hz0]
          have hlt : (r1.val - 1) % m.val < m.val := Int.emod_lt_of_pos _ hm_pos
          have hge : 0 ≤ (r1.val - 1) % m.val := Int.emod_nonneg _ (by omega)
          rw [Int.tmod_eq_emod_of_nonneg (by omega), Int.add_emod_right,
            Int.emod_emod_of_dvd _ dvd_rfl]
        · -- r1 = 0, so `r1 - 1 = -1`. This is the one step where a pointwise
          -- `tmod = emod` rewrite is WRONG: truncated gives `-1`, Euclidean
          -- `m - 1`. They only agree after the second reduction.
          have hr1z : r1.val = 0 := by omega
          rw [hr1z]
          have hneg1 : ((0 : Int) - 1) = -1 := by ring
          -- truncated: `(-1) tmod m = -(1 tmod m) = -1`
          have h1 : Int.tmod (0 - 1 : Int) m.val = -1 := by
            rw [hneg1]
            have hn : Int.tmod (-1 : Int) m.val = -(Int.tmod (1 : Int) m.val) := by
              simp [Int.neg_tmod]
            rw [hn, Int.tmod_eq_emod_of_nonneg (by omega),
              Int.emod_eq_of_lt (by omega) (by omega)]
          -- Euclidean: `(-1) emod m = m - 1`
          have h2 : (-1 : Int) % m.val = m.val - 1 := by
            rw [show (-1 : Int) = (m.val - 1) + m.val * (-1) by ring,
              Int.add_mul_emod_self_left]
            exact Int.emod_eq_of_lt (by omega) (by omega)
          rw [h1, Int.tmod_eq_emod_of_nonneg (by omega),
            show (-1 + m.val : Int) = m.val - 1 by ring,
            Int.emod_eq_of_lt (by omega) (by omega), hneg1, h2]

/-! ## Canonicalisation

    `Rounding.decompose` only looks at `r` through `r % Qi`, so replacing `r` by
    any congruent canonical representative leaves it unchanged. -/

theorem decompose_canonical (x rc g : Std.I32)
    (hcong : ((rc.val : Int) : Zq) = ((x.val : Int) : Zq))
    (h0 : 0 ≤ rc.val) (h1 : rc.val < 8380417) :
    Rounding.decompose rc.val g.val = Rounding.decompose x.val g.val := by
  have hQi : (Rounding.Qi) = 8380417 := by norm_num [Rounding.Qi, Q]
  -- the `Zq` congruence is exactly `Q | x - rc`
  have hdvd : ((Q : Int)) ∣ (x.val - rc.val) := by
    have hz : ((x.val - rc.val : Int) : Zq) = 0 := by
      push_cast; rw [hcong]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have hQ : (Q : Int) = 8380417 := by norm_num [Q]
  -- ... so `x` and `rc` have the same canonical residue
  have hx : x.val % Rounding.Qi = rc.val := by
    obtain ⟨k, hk⟩ := hdvd
    rw [hQ] at hk
    have hxk : x.val = rc.val + 8380417 * k := by omega
    rw [hQi, hxk, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt h0 (by omega)
  have hrc : rc.val % Rounding.Qi = rc.val := by
    rw [hQi]; exact Int.emod_eq_of_lt h0 (by omega)
  -- `decompose` only reads its first argument through that residue
  unfold Rounding.decompose
  rw [hrc, hx]

/-- Same for `power2round`, which opens with the same two lines. -/
theorem power2round_canonical (x rc : Std.I32)
    (hcong : ((rc.val : Int) : Zq) = ((x.val : Int) : Zq))
    (h0 : 0 ≤ rc.val) (h1 : rc.val < 8380417) :
    Rounding.power2round rc.val = Rounding.power2round x.val := by
  have hQi : (Rounding.Qi) = 8380417 := by norm_num [Rounding.Qi, Q]
  have hdvd : ((Q : Int)) ∣ (x.val - rc.val) := by
    have hz : ((x.val - rc.val : Int) : Zq) = 0 := by
      push_cast; rw [hcong]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have hQ : (Q : Int) = 8380417 := by norm_num [Q]
  have hx : x.val % Rounding.Qi = rc.val := by
    obtain ⟨k, hk⟩ := hdvd
    rw [hQ] at hk
    have hxk : x.val = rc.val + 8380417 * k := by omega
    rw [hQi, hxk, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt h0 (by omega)
  have hrc : rc.val % Rounding.Qi = rc.val := by
    rw [hQi]; exact Int.emod_eq_of_lt h0 (by omega)
  unfold Rounding.power2round
  rw [hrc, hx]

/-- Same for `useHint`, which reads `r` only by calling `decompose`. -/
theorem useHint_canonical (b : Bool) (x rc g : Std.I32)
    (hcong : ((rc.val : Int) : Zq) = ((x.val : Int) : Zq))
    (h0 : 0 ≤ rc.val) (h1 : rc.val < 8380417) :
    Rounding.useHint b rc.val g.val = Rounding.useHint b x.val g.val := by
  unfold Rounding.useHint
  rw [decompose_canonical x rc g hcong h0 h1]

end libcrux_iot_ml_dsa.Spec.RoundingBridge
