/-
  Structural equivalence: each Aeneas-extracted `keccak.keccakf1600_*`
  sub-function is observationally equal to the corresponding pure-Lean
  `bit_*` definition under `KState.fromAeneas`.

  For each sub-function, the proof:
  - Consumes the existing `@[spec high]`-tagged FC lemma from
    `PrcLift.lean` via `mvcgen` (no need to re-do its bv chain locally).
  - Splits the residual `KState.fromAeneas r = bit_* ...` into four
    field equalities. The `st` field collapses by `simp` once the
    iso-projection lemmas (`Lane.fromAeneas_*`,
    `stateArray*FromAeneas_getElem` in `Project.lean`) are in scope;
    `c`/`d`/`i` are trivial chain rewrites.
-/
import LibcruxIotSha3.BitSpec.Spec
import LibcruxIotSha3.BitSpec.StateIso
import LibcruxIotSha3.BitSpec.Project
import LibcruxIotSha3.Foundation.PrcLift
import LibcruxIotSha3.Foundation.ThetaLiftDefs
import LibcruxIotSha3.Foundation.I32LoopSpec
import LibcruxIotSha3.Foundation.SpecChain
import Hax

namespace libcrux_iot_sha3.Structural

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3
open libcrux_iot_sha3.Foundation
open libcrux_iot_sha3.BitSpec

set_option mvcgen.warning false

attribute [local spec] Aeneas.Std.uncurry

/-- Bridge: when `r.i.val = s.i.val + 1` and `s.i.val < 24`, recover the
    UScalar-level equality `r.i = ⟨s.i.bv + 1⟩`. Used in every PrcLift FC
    sub-fn that increments `s.i` (the `_zeta1` family with RC). -/
private theorem usize_succ_eq
    {r s : Aeneas.Std.Usize} (hi_eq : r.val = s.val + 1) (hi : s.val < 24) :
    r = ⟨s.bv + (1 : BitVec System.Platform.numBits)⟩ := by
  apply Std.UScalar.eq_of_val_eq
  rw [hi_eq]
  show s.val + 1 = (s.bv + (1 : BitVec System.Platform.numBits)).toNat
  have h32 : (32 : Nat) ≤ System.Platform.numBits := by
    have := System.Platform.numBits_eq
    omega
  have hpow : (2 : Nat) ^ 32 ≤ 2 ^ System.Platform.numBits :=
    Nat.pow_le_pow_right (by decide) h32
  have hone : (1 : BitVec System.Platform.numBits).toNat = 1 := by
    have h1 : (1 : Nat) % 2 ^ System.Platform.numBits = 1 := by
      apply Nat.mod_eq_of_lt; omega
    simp [BitVec.toNat_ofNat, h1]
  rw [BitVec.toNat_add, hone]
  have hsv : s.bv.toNat = s.val := rfl
  have hmod : (s.bv.toNat + 1) % 2 ^ System.Platform.numBits = s.bv.toNat + 1 := by
    apply Nat.mod_eq_of_lt
    rw [hsv]; omega
  rw [hmod, hsv]

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_pi_rho_chi_y0_zeta0_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y0_zeta0 BR (KState.fromAeneas s) ∧
      r.i = s.i ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine ⟨?_, hi_eq⟩
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · -- st: structural collapse via the iso projection lemmas + bit-side unfold
    apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · -- c
    show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · -- d
    show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · -- i
    show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_pi_rho_chi_y0_zeta1_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y0_zeta1 BR (KState.fromAeneas s) ∧
      r.i.val = s.i.val + 1 ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine ⟨?_, hi_eq⟩
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · exact usize_succ_eq hi_eq hi

/-! ## No-RC PrcLift sub-fns (y1..y4 × ζ0/ζ1) — preserve `s.i`. -/

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_pi_rho_chi_y1_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y1_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_pi_rho_chi_y1_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y1_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_pi_rho_chi_y2_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y2_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_pi_rho_chi_y2_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y2_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_pi_rho_chi_y3_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y3_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_pi_rho_chi_y3_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y3_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_pi_rho_chi_y4_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y4_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_pi_rho_chi_y4_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_pi_rho_chi_y4_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

/-! ## θ-stage c-cell sub-fns -/

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x0_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x0_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta0, KState.fromAeneas, stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x0_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x0_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x1_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x1_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta0, KState.fromAeneas, stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x1_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x1_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x2_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x2_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta0, KState.fromAeneas, stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x2_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x2_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x3_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x3_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta0, KState.fromAeneas, stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x3_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x3_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x4_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x4_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta0, KState.fromAeneas, stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_theta_c_x4_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_c_x4_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hd hc
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · apply Vector.toArray_inj.mp
    simp [stateArray5FromAeneas, hc, List.map_set,
      Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray25FromAeneas_getElem, Std.UScalar.bv_xor]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

/-! ## θ-stage d-cell sub-fn

The FC `theta_d_spec` gives a 10-conjunct postcondition (one per
`r.d[i]!.val[j]!` cell), unlike the c-family which gives a single
`r.c = s.c.set …` equation. We therefore can't fold the result with
`rw [hd]` + `List.map_set`; we instead reduce to a 5-way
`Vector.ext` and discharge each lane via `Lane.mk.injEq` on z0/z1.
-/

set_option maxHeartbeats 8000000 in
@[spec high]
theorem bit_theta_d_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_theta_d (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hc hd00 hd01 hd10 hd11 hd20 hd21 hd30 hd31 hd40 hd41
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · -- d: 10 cell equalities determine 5 lanes; case-split on i.
    show stateArray5FromAeneas r.d = _
    apply Vector.ext
    intro i hi
    rw [stateArray5FromAeneas_getElem! r.d i hi]
    match i, hi with
    | 0, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd00]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd01]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
    | 1, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd10]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd11]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
    | 2, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd20]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd21]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
    | 3, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd30]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd31]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
    | 4, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd40]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd41]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
  · show r.i = s.i
    exact hi_eq

/-! ## θ-step composition (round 0)

With the 11 sub-fn equivalences tagged `@[spec high]`, `mvcgen` threads
them through the 11-step do-chain of `keccak.keccakf1600_round0_theta`
(the `high` priority overrides the FC default-priority `@[spec]`s in
`Foundation/ThetaLiftDefs.lean` that target the same sub-fns). The
residual after `mvcgen` is the definitional unfolding of
`bit_keccakf1600_round0_theta` applied to `KState.fromAeneas s`. -/

section ThetaComp
/-! Same `attribute [local irreducible]` pattern as `PrcLiftComp`
    below — keeps `mvcgen` from whnf-reducing the ~5-line nested set
    chain in each `bit_theta_c_*` sub-fn while threading the 11-bind
    chain. With them irreducible, the chain threads in default
    heartbeats; without, ~4M are needed. -/
attribute [local irreducible]
  bit_theta_c_x0_z0 bit_theta_c_x0_z1
  bit_theta_c_x1_z0 bit_theta_c_x1_z1
  bit_theta_c_x2_z0 bit_theta_c_x2_z1
  bit_theta_c_x3_z0 bit_theta_c_x3_z1
  bit_theta_c_x4_z0 bit_theta_c_x4_z1
  bit_theta_d

@[spec high]
theorem keccakf1600_round0_theta_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round0_theta (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round0_theta
  mvcgen
  expose_names
  intro h_last
  rw [h_last, h_9, h_8, h_7, h_6, h_5, h_4, h_3, h_2, h_1, h]
  rfl

end ThetaComp

/-! ## PrcLift compositions (round 0)

Same threading pattern as `keccakf1600_round0_theta_eq` — `mvcgen`
uses the `@[spec high]`-tagged bit-side per-sub-fn equivalences. -/

section PrcLiftComp
/-! `attribute [local irreducible]` on the per-sub-fn bit-side defs is
    crucial: without it, `mvcgen` whnf-reduces them while processing the
    bind chain — each contains ~30 lines of nested `Vector.set` /
    `BitVec` operations, and four nested expansions blow well past 4M
    heartbeats. With them irreducible, the chain threads in <200K. -/
attribute [local irreducible]
  bit_pi_rho_chi_y0_zeta0 bit_pi_rho_chi_y0_zeta1
  bit_pi_rho_chi_y1_zeta0 bit_pi_rho_chi_y1_zeta1
  bit_pi_rho_chi_y2_zeta0 bit_pi_rho_chi_y2_zeta1
  bit_pi_rho_chi_y3_zeta0 bit_pi_rho_chi_y3_zeta1
  bit_pi_rho_chi_y4_zeta0 bit_pi_rho_chi_y4_zeta1

@[spec high]
theorem keccakf1600_round0_pi_rho_chi_1_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round0_pi_rho_chi_1 BR (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round0_pi_rho_chi_1
  mvcgen
  -- vc2.hi: y0_zeta1's precondition `r.i.val < 24` from the conjunctive
  -- post of y0_zeta0_eq. `scalar_tac` reads `r.i = s.i ∧ s.i.val < 24`.
  · scalar_tac
  -- Main chain: thread the 4 hypotheses + close the bit composition.
  · expose_names
    intro h_y1z1
    rw [h_y1z1, h_2, h_1.1, h.1]
    rfl

@[spec high]
theorem keccakf1600_round0_pi_rho_chi_2_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round0_pi_rho_chi_2 (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round0_pi_rho_chi_2
  mvcgen
  expose_names
  intro h_last
  rw [h_last, h_4, h_3, h_2, h_1, h]
  rfl

end PrcLiftComp

/-! # Round 1 sub-fn equivalences

Same template as the round-0 proofs above, but on the round-1
sub-functions, whose lane addressing follows `impl_perm` (see
`BitSpec/Spec.lean` round-1 defs for the per-sub-fn mapping). No
round-1 FC `@[spec]` lemmas exist in `Foundation/`, so `mvcgen` chains
the primitive `get_with_zeta_spec` / `set_with_zeta_spec` /
`set_lane_value_spec` / `rotate_left_u32_spec` / etc. as it threads the
body. -/

/-! ## θ-stage c-cell sub-fns (round 1)

Same proof shape as the round-0 theta_c equivalences. `mvcgen` chains
the FC-default `set_lane_value_spec` and the local `theta_c_x{X}_z{Z}_spec`
in `ThetaLiftDefs.lean`... no wait, those are round-0-specific. For
round 1 mvcgen chains `set_lane_value_spec` + `get_with_zeta_spec` +
`lift`/xor primitives directly through the body. The resulting
hypothesis set is identical in shape to round 0 (since theta_c_x{X}_z{Z}
both end with the same `set_lane_value`). -/

/- Proof template for a round-1 `theta_c_x{X}_z{Z}` equivalence: after
   `hax_mvcgen` on the manually-unfolded body, close the index-bound VCs
   with `scalar_tac`, then `rename_i` the post-conjuncts (`hst, hi_eq,
   hd, hc`) and decompose the bit-side `KState.fromAeneas` equality field
   by field, using `simp [*]` to thread the chain of XOR hypotheses on
   the c-cell. Hygiene disabled so the `rename_i`-introduced names
   (`r`, `hst`, `hi_eq`, `hd`, `hc`) and the theorem's outer `s` resolve
   against the runtime context. -/
set_option hygiene false in
local macro "round1_theta_c_proof" subfun:ident : tactic => `(tactic|
  (unfold $subfun
   hax_mvcgen
   all_goals try scalar_tac
   rename_i r hst hi_eq hd hc
   refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
   · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
     rw [hst]
   · apply Vector.toArray_inj.mp
     simp [stateArray5FromAeneas, hc, List.map_set,
       Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1, KState.fromAeneas,
       stateArray25FromAeneas_getElem, Std.UScalar.bv_xor, *]
   · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
     rw [hd]
   · show r.i = s.i
     exact hi_eq))

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x0_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x0_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x0_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x0_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x0_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x0_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x1_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x1_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x1_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x1_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x1_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x1_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x2_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x2_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x2_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x2_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x2_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x2_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x3_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x3_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x3_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x3_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x3_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x3_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x4_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x4_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x4_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_theta_c_x4_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_c_x4_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round1_theta_c_x4_z1

/-! ## θ-stage d-cell sub-fn (round 1)

Round 1's `keccakf1600_round1_theta_d` body is a long Array-update chain
(no FC sub-fn `@[spec]` exists in `Foundation/`); we publish a local
FC `@[spec]` mirroring `Foundation/ThetaLiftDefs.lean:theta_d_spec` so
the `bit_round1_theta_d_eq` proof can reuse the round-0 template. The
formulas are identical to round 0 (same XOR-rotate-1 pattern on `s.c`);
only the function name differs. -/

set_option maxHeartbeats 1600000 in
@[spec]
private theorem round1_theta_d_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_d s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.c = s.c ∧
        r.d.val[0]!.val[0]! =
          s.c.val[4]!.val[0]! ^^^ Foundation.rot32 s.c.val[1]!.val[1]! 1 ∧
        r.d.val[0]!.val[1]! =
          s.c.val[4]!.val[1]! ^^^ s.c.val[1]!.val[0]! ∧
        r.d.val[1]!.val[0]! =
          s.c.val[0]!.val[0]! ^^^ Foundation.rot32 s.c.val[2]!.val[1]! 1 ∧
        r.d.val[1]!.val[1]! =
          s.c.val[0]!.val[1]! ^^^ s.c.val[2]!.val[0]! ∧
        r.d.val[2]!.val[0]! =
          s.c.val[1]!.val[0]! ^^^ Foundation.rot32 s.c.val[3]!.val[1]! 1 ∧
        r.d.val[2]!.val[1]! =
          s.c.val[1]!.val[1]! ^^^ s.c.val[3]!.val[0]! ∧
        r.d.val[3]!.val[0]! =
          s.c.val[2]!.val[0]! ^^^ Foundation.rot32 s.c.val[4]!.val[1]! 1 ∧
        r.d.val[3]!.val[1]! =
          s.c.val[2]!.val[1]! ^^^ s.c.val[4]!.val[0]! ∧
        r.d.val[4]!.val[0]! =
          s.c.val[3]!.val[0]! ^^^ Foundation.rot32 s.c.val[0]!.val[1]! 1 ∧
        r.d.val[4]!.val[1]! =
          s.c.val[3]!.val[1]! ^^^ s.c.val[0]!.val[0]! ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_theta_d
  mvcgen
  all_goals first
    | scalar_tac
    | (refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
       (apply Std.U32.bv_eq_imp_eq
        simp_all [WP.uncurry', Std.Array.set_val_eq,
                  Std.UScalar.bv_xor, Foundation.rot32]))

set_option maxHeartbeats 8000000 in
@[spec high]
theorem bit_round1_theta_d_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta_d s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_theta_d (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hc hd00 hd01 hd10 hd11 hd20 hd21 hd30 hd31 hd40 hd41
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = _
    apply Vector.ext
    intro i hi
    rw [stateArray5FromAeneas_getElem! r.d i hi]
    match i, hi with
    | 0, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd00]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd01]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
    | 1, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd10]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd11]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
    | 2, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd20]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd21]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
    | 3, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd30]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd31]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
    | 4, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd40]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd41]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
  · show r.i = s.i
    exact hi_eq

/-! ## PrcLift sub-fns (round 1)

Round-1 PrcLift sub-fns have no FC `@[spec]` in `Foundation/PrcLift.lean`,
so we publish private FC specs locally (mirroring the R1-chained-set form
in PrcLift.lean) and then prove the bit-side equivalences using those
FCs as the `mvcgen` consumers. -/

/-- Local copy of `Foundation.PrcLift.apply_5_writes` (which is `private`
    and not re-exported). Used by the round-1 PrcLift FC posts to express
    the 5-write chain compactly. -/
@[reducible]
private def apply_5_writes
    (l : List lane.Lane2U32)
    (lane0 lane1 lane2 lane3 lane4 : Nat)
    (half0 half1 half2 half3 half4 : Std.Usize)
    (v0 v1 v2 v3 v4 : Std.U32) : List lane.Lane2U32 :=
  let l := l.set lane0 ((l[lane0]!).set half0 v0)
  let l := l.set lane1 ((l[lane1]!).set half1 v1)
  let l := l.set lane2 ((l[lane2]!).set half2 v2)
  let l := l.set lane3 ((l[lane3]!).set half3 v3)
  l.set lane4 ((l[lane4]!).set half4 v4)

/-! ### Round-1 FC specs and bit-side equivalences

Each round-1 PrcLift sub-fn has the same control flow as its round-0
counterpart (5 lane reads, 5 d-cell reads, 5 lift+rotate, 5 chi values,
5 writes), so `hax_mvcgen` produces the same h_25..h_62 names. The
proof bodies of the FC specs below are byte-identical to round 0's
PrcLift.lean templates except for `_round0_` → `_round1_` and the
constants in the post (lanes/halves/rotations). -/

/- Local copy of `Foundation.PrcLift`'s `prc_y_zeta_no_rc_proof` macro
   (which is `private` and not re-exported). Discharges the 4-conjunct
   FC post for any round's y1..y4 PrcLift sub-fn (no RC step, preserves
   `s.i`). Hygiene disabled so the `h_25..h_55` names produced by
   `hax_mvcgen` resolve. -/
set_option hygiene false in
local macro "round1_prc_y_zeta_no_rc_proof" subfun:ident : tactic => `(tactic|
  (unfold $subfun
   hax_mvcgen
   all_goals try scalar_tac
   expose_names
   refine ⟨?_, ?_, ?_, ?_⟩
   · exact h_58.trans (h_51.trans (h_44.trans (h_37.trans h_30)))
   · exact h_57.trans (h_50.trans (h_43.trans (h_36.trans h_29)))
   · exact h_56.trans (h_49.trans (h_42.trans (h_35.trans h_28)))
   · rw [h_59, h_52, h_45, h_38, h_31]
     norm_num [apply_5_writes]
     congr 6
     all_goals try apply Std.U32.bv_eq_imp_eq
     all_goals (
       simp only [
         h_27.2, h_26.2, h_25,
         h_34.2, h_33.2, h_32,
         h_41.2, h_40.2, h_39,
         h_48.2, h_47.2, h_46,
         h_55.2, h_54.2, h_53,
         h_7, h_9, h_20, h_22, h_24,
         h_6.2, h_8.2, h_19.2, h_21.2, h_23.2,
         h, h_1, h_2, h_3, h_4, h_5, h_10, h_11, h_12, h_13, h_14, h_15, h_16, h_17, h_18,
         Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, Foundation.rot32]
       norm_num)))

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y0_zeta0_spec_fc
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[0]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 0
      let bx1 := Foundation.rot32 (s.st.val[8]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 22
      let bx2 := Foundation.rot32 (s.st.val[11]!.val[1]! ^^^ s.d.val[2]!.val[1]!) 22
      let bx3 := Foundation.rot32 (s.st.val[19]!.val[1]! ^^^ s.d.val[3]!.val[1]!) 11
      let bx4 := Foundation.rot32 (s.st.val[22]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 7
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        0 8 11 19 22
        0#usize 1#usize 1#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_0.val[s.i.val]!)
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_pi_rho_chi_y0_zeta0
  hax_mvcgen
  all_goals try scalar_tac
  expose_names
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_60.trans (h_53.trans (h_46.trans (h_39.trans h_32)))
  · exact h_59.trans (h_52.trans (h_45.trans (h_38.trans h_31)))
  · exact h_58.trans (h_51.trans (h_44.trans (h_37.trans h_30)))
  · have hb : s.i.val < keccak.RC_INTERLEAVED_0.val.length := by
      have hl : keccak.RC_INTERLEAVED_0.val.length = 255 := Array.length_eq _
      omega
    have hRC : keccak.RC_INTERLEAVED_0.val[s.i.val]?.getD default
             = keccak.RC_INTERLEAVED_0.val[s.i.val]'hb := by
      rw [List.getElem?_eq_getElem hb]; rfl
    rw [h_61, h_54, h_47, h_40, h_33]
    norm_num [apply_5_writes]
    congr 6
    all_goals apply Std.U32.bv_eq_imp_eq
    all_goals (
      simp only [
        hRC,
        h_29.2, h_27.2, h_26.2, h_25,
        h_36.2, h_35.2, h_34,
        h_43.2, h_42.2, h_41,
        h_50.2, h_49.2, h_48,
        h_57.2, h_56.2, h_55,
        h_7, h_9, h_20, h_22, h_24,
        h_6.2, h_8.2, h_19.2, h_21.2, h_23.2,
        h_28,
        h, h_1, h_2, h_3, h_4, h_5, h_10, h_11, h_12, h_13, h_14, h_15, h_16, h_17, h_18,
        Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, Foundation.rot32]
      norm_num)

/- Round-1 y0_zeta1 FC (RC + s.i++): same proof shape as round-0's
   `pi_rho_chi_y0_zeta1_spec_fc`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y0_zeta1_spec_fc
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[0]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 0
      let bx1 := Foundation.rot32 (s.st.val[8]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 22
      let bx2 := Foundation.rot32 (s.st.val[11]!.val[0]! ^^^ s.d.val[2]!.val[0]!) 21
      let bx3 := Foundation.rot32 (s.st.val[19]!.val[0]! ^^^ s.d.val[3]!.val[0]!) 10
      let bx4 := Foundation.rot32 (s.st.val[22]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 7
      r.d = s.d ∧ r.c = s.c ∧ r.i.val = s.i.val + 1 ∧
      r.st.val = apply_5_writes s.st.val
        0 8 11 19 22
        1#usize 0#usize 0#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_1.val[s.i.val]!)
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_pi_rho_chi_y0_zeta1
  hax_mvcgen
  all_goals try scalar_tac
  expose_names
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_61.trans (h_54.trans (h_47.trans (h_40.trans h_33)))
  · exact h_60.trans (h_53.trans (h_46.trans (h_39.trans h_32)))
  · rw [h_59, h_52, h_45, h_38, h_31, h_30]
    rfl
  · have hb : s.i.val < keccak.RC_INTERLEAVED_1.val.length := by
      have hl : keccak.RC_INTERLEAVED_1.val.length = 255 := Array.length_eq _
      omega
    have hRC : keccak.RC_INTERLEAVED_1.val[s.i.val]?.getD default
             = keccak.RC_INTERLEAVED_1.val[s.i.val]'hb := by
      rw [List.getElem?_eq_getElem hb]; rfl
    rw [h_62, h_55, h_48, h_41, h_34]
    norm_num [apply_5_writes]
    congr 6
    all_goals apply Std.U32.bv_eq_imp_eq
    all_goals (
      simp only [
        hRC,
        h_29.2, h_27.2, h_26.2, h_25,
        h_37.2, h_36.2, h_35,
        h_44.2, h_43.2, h_42,
        h_51.2, h_50.2, h_49,
        h_58.2, h_57.2, h_56,
        h_7, h_9, h_20, h_22, h_24,
        h_6.2, h_8.2, h_19.2, h_21.2, h_23.2,
        h_28,
        h, h_1, h_2, h_3, h_4, h_5, h_10, h_11, h_12, h_13, h_14, h_15, h_16, h_17, h_18,
        Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, Foundation.rot32]
      norm_num)

/-! Round-1 y1..y4 × ζ0/ζ1 FCs (no RC; preserve `s.i`). -/

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y1_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[18]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 14
      let bx1 := Foundation.rot32 (s.st.val[21]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 10
      let bx2 := Foundation.rot32 (s.st.val[4]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 2
      let bx3 := Foundation.rot32 (s.st.val[7]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 23
      let bx4 := Foundation.rot32 (s.st.val[10]!.val[1]! ^^^ s.d.val[2]!.val[1]!) 31
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        4 7 10 18 21
        1#usize 1#usize 1#usize 1#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y1_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y1_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[18]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 14
      let bx1 := Foundation.rot32 (s.st.val[21]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 10
      let bx2 := Foundation.rot32 (s.st.val[4]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 1
      let bx3 := Foundation.rot32 (s.st.val[7]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 22
      let bx4 := Foundation.rot32 (s.st.val[10]!.val[0]! ^^^ s.d.val[2]!.val[0]!) 30
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        4 7 10 18 21
        0#usize 0#usize 0#usize 0#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y1_zeta1

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y2_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[6]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 1
      let bx1 := Foundation.rot32 (s.st.val[14]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 3
      let bx2 := Foundation.rot32 (s.st.val[17]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 13
      let bx3 := Foundation.rot32 (s.st.val[20]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 4
      let bx4 := Foundation.rot32 (s.st.val[3]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 9
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        3 6 14 17 20
        1#usize 1#usize 1#usize 0#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y2_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y2_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[6]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 0
      let bx1 := Foundation.rot32 (s.st.val[14]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 3
      let bx2 := Foundation.rot32 (s.st.val[17]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 12
      let bx3 := Foundation.rot32 (s.st.val[20]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 4
      let bx4 := Foundation.rot32 (s.st.val[3]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 9
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        3 6 14 17 20
        0#usize 0#usize 0#usize 1#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y2_zeta1

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y3_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[24]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 14
      let bx1 := Foundation.rot32 (s.st.val[2]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 18
      let bx2 := Foundation.rot32 (s.st.val[5]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 5
      let bx3 := Foundation.rot32 (s.st.val[13]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 8
      let bx4 := Foundation.rot32 (s.st.val[16]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 28
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        2 5 13 16 24
        1#usize 1#usize 0#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y3_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y3_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[24]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 13
      let bx1 := Foundation.rot32 (s.st.val[2]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 18
      let bx2 := Foundation.rot32 (s.st.val[5]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 5
      let bx3 := Foundation.rot32 (s.st.val[13]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 7
      let bx4 := Foundation.rot32 (s.st.val[16]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 28
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        2 5 13 16 24
        0#usize 0#usize 1#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y3_zeta1

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y4_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[12]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 31
      let bx1 := Foundation.rot32 (s.st.val[15]!.val[1]! ^^^ s.d.val[3]!.val[1]!) 28
      let bx2 := Foundation.rot32 (s.st.val[23]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 20
      let bx3 := Foundation.rot32 (s.st.val[1]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 21
      let bx4 := Foundation.rot32 (s.st.val[9]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 1
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        1 9 12 15 23
        1#usize 0#usize 1#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y4_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round1_pi_rho_chi_y4_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[12]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 31
      let bx1 := Foundation.rot32 (s.st.val[15]!.val[0]! ^^^ s.d.val[3]!.val[0]!) 27
      let bx2 := Foundation.rot32 (s.st.val[23]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 19
      let bx3 := Foundation.rot32 (s.st.val[1]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 20
      let bx4 := Foundation.rot32 (s.st.val[9]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 1
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        1 9 12 15 23
        0#usize 1#usize 0#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y4_zeta1

/-! ### Round-1 PrcLift bit-side equivalences

With the 10 FC `@[spec]`s above registered, `mvcgen` threads the
conjunctive post into `hd, hc, hi_eq, hst` exactly as for round 0.
The proof shape mirrors round-0's `bit_pi_rho_chi_*_eq`. -/

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_pi_rho_chi_y0_zeta0_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y0_zeta0 BR (KState.fromAeneas s) ∧
      r.i = s.i ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine ⟨?_, hi_eq⟩
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_pi_rho_chi_y0_zeta1_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y0_zeta1 BR (KState.fromAeneas s) ∧
      r.i.val = s.i.val + 1 ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine ⟨?_, hi_eq⟩
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · exact usize_succ_eq hi_eq hi

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_pi_rho_chi_y1_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y1_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_pi_rho_chi_y1_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y1_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_pi_rho_chi_y2_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y2_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_pi_rho_chi_y2_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y2_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_pi_rho_chi_y3_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y3_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_pi_rho_chi_y3_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y3_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_pi_rho_chi_y4_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y4_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round1_pi_rho_chi_y4_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round1_pi_rho_chi_y4_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

/-! ## Compositions (round 1)

Same idiom as round-0's `ThetaComp` / `PrcLiftComp`: `attribute [local
irreducible]` on the round-1 bit-side sub-fn defs keeps `mvcgen` from
whnf-reducing them while threading the bind chain. -/

section Round1ThetaComp
attribute [local irreducible]
  bit_round1_theta_c_x0_z0 bit_round1_theta_c_x0_z1
  bit_round1_theta_c_x1_z0 bit_round1_theta_c_x1_z1
  bit_round1_theta_c_x2_z0 bit_round1_theta_c_x2_z1
  bit_round1_theta_c_x3_z0 bit_round1_theta_c_x3_z1
  bit_round1_theta_c_x4_z0 bit_round1_theta_c_x4_z1
  bit_round1_theta_d

@[spec high]
theorem keccakf1600_round1_theta_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round1_theta (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_theta
  mvcgen
  expose_names
  intro h_last
  rw [h_last, h_9, h_8, h_7, h_6, h_5, h_4, h_3, h_2, h_1, h]
  rfl

end Round1ThetaComp

section Round1PrcLiftComp
attribute [local irreducible]
  bit_round1_pi_rho_chi_y0_zeta0 bit_round1_pi_rho_chi_y0_zeta1
  bit_round1_pi_rho_chi_y1_zeta0 bit_round1_pi_rho_chi_y1_zeta1
  bit_round1_pi_rho_chi_y2_zeta0 bit_round1_pi_rho_chi_y2_zeta1
  bit_round1_pi_rho_chi_y3_zeta0 bit_round1_pi_rho_chi_y3_zeta1
  bit_round1_pi_rho_chi_y4_zeta0 bit_round1_pi_rho_chi_y4_zeta1

@[spec high]
theorem keccakf1600_round1_pi_rho_chi_1_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round1_pi_rho_chi_1 BR (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_pi_rho_chi_1
  mvcgen
  · scalar_tac
  · expose_names
    intro h_y1z1
    rw [h_y1z1, h_2, h_1.1, h.1]
    rfl

@[spec high]
theorem keccakf1600_round1_pi_rho_chi_2_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round1_pi_rho_chi_2 (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_pi_rho_chi_2
  mvcgen
  expose_names
  intro h_last
  rw [h_last, h_4, h_3, h_2, h_1, h]
  rfl

end Round1PrcLiftComp

/-! # Round 2 -/

/-! ## θ-stage c-cell sub-fns (round 2)

Same control flow as round 1 (5 XOR-reads + 1 set_lane_value); the only
differences are the zeta-pattern (the impl_perm²-image of round-0's
column-read pattern) and the function name. So `round1_theta_c_proof`
is reusable. -/

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x0_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x0_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x0_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x0_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x0_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x0_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x1_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x1_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x1_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x1_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x1_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x1_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x2_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x2_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x2_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x2_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x2_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x2_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x3_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x3_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x3_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x3_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x3_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x3_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x4_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x4_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x4_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_theta_c_x4_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_c_x4_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round2_theta_c_x4_z1

/-! ## θ-stage d-cell sub-fn (round 2)

Identical formulas to rounds 0/1; only the function name differs. -/

set_option maxHeartbeats 1600000 in
@[spec]
private theorem round2_theta_d_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_theta_d s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.c = s.c ∧
        r.d.val[0]!.val[0]! =
          s.c.val[4]!.val[0]! ^^^ Foundation.rot32 s.c.val[1]!.val[1]! 1 ∧
        r.d.val[0]!.val[1]! =
          s.c.val[4]!.val[1]! ^^^ s.c.val[1]!.val[0]! ∧
        r.d.val[1]!.val[0]! =
          s.c.val[0]!.val[0]! ^^^ Foundation.rot32 s.c.val[2]!.val[1]! 1 ∧
        r.d.val[1]!.val[1]! =
          s.c.val[0]!.val[1]! ^^^ s.c.val[2]!.val[0]! ∧
        r.d.val[2]!.val[0]! =
          s.c.val[1]!.val[0]! ^^^ Foundation.rot32 s.c.val[3]!.val[1]! 1 ∧
        r.d.val[2]!.val[1]! =
          s.c.val[1]!.val[1]! ^^^ s.c.val[3]!.val[0]! ∧
        r.d.val[3]!.val[0]! =
          s.c.val[2]!.val[0]! ^^^ Foundation.rot32 s.c.val[4]!.val[1]! 1 ∧
        r.d.val[3]!.val[1]! =
          s.c.val[2]!.val[1]! ^^^ s.c.val[4]!.val[0]! ∧
        r.d.val[4]!.val[0]! =
          s.c.val[3]!.val[0]! ^^^ Foundation.rot32 s.c.val[0]!.val[1]! 1 ∧
        r.d.val[4]!.val[1]! =
          s.c.val[3]!.val[1]! ^^^ s.c.val[0]!.val[0]! ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_theta_d
  mvcgen
  all_goals first
    | scalar_tac
    | (refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
       (apply Std.U32.bv_eq_imp_eq
        simp_all [WP.uncurry', Std.Array.set_val_eq,
                  Std.UScalar.bv_xor, Foundation.rot32]))

set_option maxHeartbeats 8000000 in
@[spec high]
theorem bit_round2_theta_d_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta_d s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_theta_d (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hc hd00 hd01 hd10 hd11 hd20 hd21 hd30 hd31 hd40 hd41
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = _
    apply Vector.ext
    intro i hi
    rw [stateArray5FromAeneas_getElem! r.d i hi]
    match i, hi with
    | 0, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd00]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd01]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
    | 1, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd10]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd11]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
    | 2, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd20]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd21]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
    | 3, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd30]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd31]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
    | 4, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd40]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd41]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
  · show r.i = s.i
    exact hi_eq

/-! ## PrcLift sub-fns (round 2)

Same control flow as round 1, so the round-1 macros `round1_prc_y_zeta_no_rc_proof`
and the FC spec template are reusable. -/

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y0_zeta0_spec_fc
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[0]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 0
      let bx1 := Foundation.rot32 (s.st.val[7]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 22
      let bx2 := Foundation.rot32 (s.st.val[14]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 22
      let bx3 := Foundation.rot32 (s.st.val[16]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 11
      let bx4 := Foundation.rot32 (s.st.val[23]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 7
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        0 7 14 16 23
        0#usize 1#usize 0#usize 0#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_0.val[s.i.val]!)
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_pi_rho_chi_y0_zeta0
  hax_mvcgen
  all_goals try scalar_tac
  expose_names
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_60.trans (h_53.trans (h_46.trans (h_39.trans h_32)))
  · exact h_59.trans (h_52.trans (h_45.trans (h_38.trans h_31)))
  · exact h_58.trans (h_51.trans (h_44.trans (h_37.trans h_30)))
  · have hb : s.i.val < keccak.RC_INTERLEAVED_0.val.length := by
      have hl : keccak.RC_INTERLEAVED_0.val.length = 255 := Array.length_eq _
      omega
    have hRC : keccak.RC_INTERLEAVED_0.val[s.i.val]?.getD default
             = keccak.RC_INTERLEAVED_0.val[s.i.val]'hb := by
      rw [List.getElem?_eq_getElem hb]; rfl
    rw [h_61, h_54, h_47, h_40, h_33]
    norm_num [apply_5_writes]
    congr 6
    all_goals apply Std.U32.bv_eq_imp_eq
    all_goals (
      simp only [
        hRC,
        h_29.2, h_27.2, h_26.2, h_25,
        h_36.2, h_35.2, h_34,
        h_43.2, h_42.2, h_41,
        h_50.2, h_49.2, h_48,
        h_57.2, h_56.2, h_55,
        h_7, h_9, h_20, h_22, h_24,
        h_6.2, h_8.2, h_19.2, h_21.2, h_23.2,
        h_28,
        h, h_1, h_2, h_3, h_4, h_5, h_10, h_11, h_12, h_13, h_14, h_15, h_16, h_17, h_18,
        Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, Foundation.rot32]
      norm_num)

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y0_zeta1_spec_fc
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[0]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 0
      let bx1 := Foundation.rot32 (s.st.val[7]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 22
      let bx2 := Foundation.rot32 (s.st.val[14]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 21
      let bx3 := Foundation.rot32 (s.st.val[16]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 10
      let bx4 := Foundation.rot32 (s.st.val[23]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 7
      r.d = s.d ∧ r.c = s.c ∧ r.i.val = s.i.val + 1 ∧
      r.st.val = apply_5_writes s.st.val
        0 7 14 16 23
        1#usize 0#usize 1#usize 1#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_1.val[s.i.val]!)
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_pi_rho_chi_y0_zeta1
  hax_mvcgen
  all_goals try scalar_tac
  expose_names
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_61.trans (h_54.trans (h_47.trans (h_40.trans h_33)))
  · exact h_60.trans (h_53.trans (h_46.trans (h_39.trans h_32)))
  · rw [h_59, h_52, h_45, h_38, h_31, h_30]
    rfl
  · have hb : s.i.val < keccak.RC_INTERLEAVED_1.val.length := by
      have hl : keccak.RC_INTERLEAVED_1.val.length = 255 := Array.length_eq _
      omega
    have hRC : keccak.RC_INTERLEAVED_1.val[s.i.val]?.getD default
             = keccak.RC_INTERLEAVED_1.val[s.i.val]'hb := by
      rw [List.getElem?_eq_getElem hb]; rfl
    rw [h_62, h_55, h_48, h_41, h_34]
    norm_num [apply_5_writes]
    congr 6
    all_goals apply Std.U32.bv_eq_imp_eq
    all_goals (
      simp only [
        hRC,
        h_29.2, h_27.2, h_26.2, h_25,
        h_37.2, h_36.2, h_35,
        h_44.2, h_43.2, h_42,
        h_51.2, h_50.2, h_49,
        h_58.2, h_57.2, h_56,
        h_7, h_9, h_20, h_22, h_24,
        h_6.2, h_8.2, h_19.2, h_21.2, h_23.2,
        h_28,
        h, h_1, h_2, h_3, h_4, h_5, h_10, h_11, h_12, h_13, h_14, h_15, h_16, h_17, h_18,
        Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, Foundation.rot32]
      norm_num)

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y1_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[19]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 14
      let bx1 := Foundation.rot32 (s.st.val[21]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 10
      let bx2 := Foundation.rot32 (s.st.val[3]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 2
      let bx3 := Foundation.rot32 (s.st.val[5]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 23
      let bx4 := Foundation.rot32 (s.st.val[12]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 31
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        3 5 12 19 21
        0#usize 0#usize 0#usize 1#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round2_pi_rho_chi_y1_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y1_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[19]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 14
      let bx1 := Foundation.rot32 (s.st.val[21]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 10
      let bx2 := Foundation.rot32 (s.st.val[3]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 1
      let bx3 := Foundation.rot32 (s.st.val[5]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 22
      let bx4 := Foundation.rot32 (s.st.val[12]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 30
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        3 5 12 19 21
        1#usize 1#usize 1#usize 0#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round2_pi_rho_chi_y1_zeta1

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y2_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[8]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 1
      let bx1 := Foundation.rot32 (s.st.val[10]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 3
      let bx2 := Foundation.rot32 (s.st.val[17]!.val[1]! ^^^ s.d.val[3]!.val[1]!) 13
      let bx3 := Foundation.rot32 (s.st.val[24]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 4
      let bx4 := Foundation.rot32 (s.st.val[1]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 9
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        1 8 10 17 24
        1#usize 0#usize 1#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round2_pi_rho_chi_y2_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y2_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[8]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 0
      let bx1 := Foundation.rot32 (s.st.val[10]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 3
      let bx2 := Foundation.rot32 (s.st.val[17]!.val[0]! ^^^ s.d.val[3]!.val[0]!) 12
      let bx3 := Foundation.rot32 (s.st.val[24]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 4
      let bx4 := Foundation.rot32 (s.st.val[1]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 9
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        1 8 10 17 24
        0#usize 1#usize 0#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round2_pi_rho_chi_y2_zeta1

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y3_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[22]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 14
      let bx1 := Foundation.rot32 (s.st.val[4]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 18
      let bx2 := Foundation.rot32 (s.st.val[6]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 5
      let bx3 := Foundation.rot32 (s.st.val[13]!.val[1]! ^^^ s.d.val[2]!.val[1]!) 8
      let bx4 := Foundation.rot32 (s.st.val[15]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 28
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        4 6 13 15 22
        1#usize 1#usize 1#usize 1#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round2_pi_rho_chi_y3_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y3_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[22]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 13
      let bx1 := Foundation.rot32 (s.st.val[4]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 18
      let bx2 := Foundation.rot32 (s.st.val[6]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 5
      let bx3 := Foundation.rot32 (s.st.val[13]!.val[0]! ^^^ s.d.val[2]!.val[0]!) 7
      let bx4 := Foundation.rot32 (s.st.val[15]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 28
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        4 6 13 15 22
        0#usize 0#usize 0#usize 0#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round2_pi_rho_chi_y3_zeta1

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y4_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[11]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 31
      let bx1 := Foundation.rot32 (s.st.val[18]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 28
      let bx2 := Foundation.rot32 (s.st.val[20]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 20
      let bx3 := Foundation.rot32 (s.st.val[2]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 21
      let bx4 := Foundation.rot32 (s.st.val[9]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 1
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        2 9 11 18 20
        0#usize 0#usize 1#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round2_pi_rho_chi_y4_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round2_pi_rho_chi_y4_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round2_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[11]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 31
      let bx1 := Foundation.rot32 (s.st.val[18]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 27
      let bx2 := Foundation.rot32 (s.st.val[20]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 19
      let bx3 := Foundation.rot32 (s.st.val[2]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 20
      let bx4 := Foundation.rot32 (s.st.val[9]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 1
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        2 9 11 18 20
        1#usize 1#usize 0#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round2_pi_rho_chi_y4_zeta1

/-! ### Round-2 PrcLift bit-side equivalences -/

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_pi_rho_chi_y0_zeta0_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y0_zeta0 BR (KState.fromAeneas s) ∧
      r.i = s.i ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine ⟨?_, hi_eq⟩
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_pi_rho_chi_y0_zeta1_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y0_zeta1 BR (KState.fromAeneas s) ∧
      r.i.val = s.i.val + 1 ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine ⟨?_, hi_eq⟩
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · exact usize_succ_eq hi_eq hi

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_pi_rho_chi_y1_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y1_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_pi_rho_chi_y1_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y1_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_pi_rho_chi_y2_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y2_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_pi_rho_chi_y2_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y2_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_pi_rho_chi_y3_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y3_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_pi_rho_chi_y3_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y3_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_pi_rho_chi_y4_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y4_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round2_pi_rho_chi_y4_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round2_pi_rho_chi_y4_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

/-! ## Compositions (round 2) -/

section Round2ThetaComp
attribute [local irreducible]
  bit_round2_theta_c_x0_z0 bit_round2_theta_c_x0_z1
  bit_round2_theta_c_x1_z0 bit_round2_theta_c_x1_z1
  bit_round2_theta_c_x2_z0 bit_round2_theta_c_x2_z1
  bit_round2_theta_c_x3_z0 bit_round2_theta_c_x3_z1
  bit_round2_theta_c_x4_z0 bit_round2_theta_c_x4_z1
  bit_round2_theta_d

@[spec high]
theorem keccakf1600_round2_theta_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round2_theta (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_theta
  mvcgen
  expose_names
  intro h_last
  rw [h_last, h_9, h_8, h_7, h_6, h_5, h_4, h_3, h_2, h_1, h]
  rfl

end Round2ThetaComp

section Round2PrcLiftComp
attribute [local irreducible]
  bit_round2_pi_rho_chi_y0_zeta0 bit_round2_pi_rho_chi_y0_zeta1
  bit_round2_pi_rho_chi_y1_zeta0 bit_round2_pi_rho_chi_y1_zeta1
  bit_round2_pi_rho_chi_y2_zeta0 bit_round2_pi_rho_chi_y2_zeta1
  bit_round2_pi_rho_chi_y3_zeta0 bit_round2_pi_rho_chi_y3_zeta1
  bit_round2_pi_rho_chi_y4_zeta0 bit_round2_pi_rho_chi_y4_zeta1

@[spec high]
theorem keccakf1600_round2_pi_rho_chi_1_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round2_pi_rho_chi_1 BR (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_pi_rho_chi_1
  mvcgen
  · scalar_tac
  · expose_names
    intro h_y1z1
    rw [h_y1z1, h_2, h_1.1, h.1]
    rfl

@[spec high]
theorem keccakf1600_round2_pi_rho_chi_2_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round2_pi_rho_chi_2 (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round2_pi_rho_chi_2
  mvcgen
  expose_names
  intro h_last
  rw [h_last, h_4, h_3, h_2, h_1, h]
  rfl

end Round2PrcLiftComp

/-! ## θ-stage c-cell sub-fns (round 3)

Same control flow as round 1/2 (5 XOR-reads + 1 set_lane_value); the only
differences are the zeta-pattern (the impl_perm³-image of round-0's
column-read pattern) and the function name. So `round1_theta_c_proof`
is reusable. -/

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_theta_c_x0_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_theta_c_x0_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round3_theta_c_x0_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_theta_c_x0_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_theta_c_x0_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round3_theta_c_x0_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_theta_c_x1_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_theta_c_x1_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round3_theta_c_x1_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_theta_c_x1_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_theta_c_x1_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round3_theta_c_x1_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_theta_c_x2_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_theta_c_x2_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round3_theta_c_x2_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_theta_c_x2_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_theta_c_x2_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round3_theta_c_x2_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_theta_c_x3_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_theta_c_x3_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round3_theta_c_x3_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_theta_c_x3_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_theta_c_x3_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round3_theta_c_x3_z1

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_theta_c_x4_z0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_theta_c_x4_z0 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round3_theta_c_x4_z0

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_theta_c_x4_z1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_theta_c_x4_z1 (KState.fromAeneas s) ⌝ ⦄ := by
  round1_theta_c_proof keccak.keccakf1600_round3_theta_c_x4_z1

/-! ## θ-stage d-cell sub-fn (round 3)

Identical formulas to rounds 0/1/2; only the function name differs. -/

set_option maxHeartbeats 1600000 in
@[spec]
private theorem round3_theta_d_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_d s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.c = s.c ∧
        r.d.val[0]!.val[0]! =
          s.c.val[4]!.val[0]! ^^^ Foundation.rot32 s.c.val[1]!.val[1]! 1 ∧
        r.d.val[0]!.val[1]! =
          s.c.val[4]!.val[1]! ^^^ s.c.val[1]!.val[0]! ∧
        r.d.val[1]!.val[0]! =
          s.c.val[0]!.val[0]! ^^^ Foundation.rot32 s.c.val[2]!.val[1]! 1 ∧
        r.d.val[1]!.val[1]! =
          s.c.val[0]!.val[1]! ^^^ s.c.val[2]!.val[0]! ∧
        r.d.val[2]!.val[0]! =
          s.c.val[1]!.val[0]! ^^^ Foundation.rot32 s.c.val[3]!.val[1]! 1 ∧
        r.d.val[2]!.val[1]! =
          s.c.val[1]!.val[1]! ^^^ s.c.val[3]!.val[0]! ∧
        r.d.val[3]!.val[0]! =
          s.c.val[2]!.val[0]! ^^^ Foundation.rot32 s.c.val[4]!.val[1]! 1 ∧
        r.d.val[3]!.val[1]! =
          s.c.val[2]!.val[1]! ^^^ s.c.val[4]!.val[0]! ∧
        r.d.val[4]!.val[0]! =
          s.c.val[3]!.val[0]! ^^^ Foundation.rot32 s.c.val[0]!.val[1]! 1 ∧
        r.d.val[4]!.val[1]! =
          s.c.val[3]!.val[1]! ^^^ s.c.val[0]!.val[0]! ⌝ ⦄ := by
  unfold keccak.keccakf1600_round3_theta_d
  mvcgen
  all_goals first
    | scalar_tac
    | (refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
       (apply Std.U32.bv_eq_imp_eq
        simp_all [WP.uncurry', Std.Array.set_val_eq,
                  Std.UScalar.bv_xor, Foundation.rot32]))

set_option maxHeartbeats 8000000 in
@[spec high]
theorem bit_round3_theta_d_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_theta_d s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_theta_d (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hst hi_eq hc hd00 hd01 hd10 hd11 hd20 hd21 hd30 hd31 hd40 hd41
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · show stateArray25FromAeneas r.st = stateArray25FromAeneas s.st
    rw [hst]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = _
    apply Vector.ext
    intro i hi
    rw [stateArray5FromAeneas_getElem! r.d i hi]
    match i, hi with
    | 0, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd00]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd01]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
    | 1, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd10]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd11]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
    | 2, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd20]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd21]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
    | 3, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd30]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd31]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
    | 4, _ =>
      simp only [Vector.getElem_set]
      rw [Lane.fromAeneas_mk]
      refine Lane.mk.injEq .. |>.mpr ⟨?_, ?_⟩
      · rw [hd40]
        simp [Std.UScalar.bv_xor, KState.fromAeneas,
          Foundation.rot32]
      · rw [hd41]
        simp [Std.UScalar.bv_xor, KState.fromAeneas]
  · show r.i = s.i
    exact hi_eq

/-! ## PrcLift sub-fns (round 3)

Same control flow as round 1/2; macros `round1_prc_y_zeta_no_rc_proof`
and the FC spec template are reusable. -/

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round3_pi_rho_chi_y0_zeta0_spec_fc
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[0]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 0
      let bx1 := Foundation.rot32 (s.st.val[5]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 22
      let bx2 := Foundation.rot32 (s.st.val[10]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 22
      let bx3 := Foundation.rot32 (s.st.val[15]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 11
      let bx4 := Foundation.rot32 (s.st.val[20]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 7
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        0 5 10 15 20
        0#usize 0#usize 0#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_0.val[s.i.val]!)
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round3_pi_rho_chi_y0_zeta0
  hax_mvcgen
  all_goals try scalar_tac
  expose_names
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_60.trans (h_53.trans (h_46.trans (h_39.trans h_32)))
  · exact h_59.trans (h_52.trans (h_45.trans (h_38.trans h_31)))
  · exact h_58.trans (h_51.trans (h_44.trans (h_37.trans h_30)))
  · have hb : s.i.val < keccak.RC_INTERLEAVED_0.val.length := by
      have hl : keccak.RC_INTERLEAVED_0.val.length = 255 := Array.length_eq _
      omega
    have hRC : keccak.RC_INTERLEAVED_0.val[s.i.val]?.getD default
             = keccak.RC_INTERLEAVED_0.val[s.i.val]'hb := by
      rw [List.getElem?_eq_getElem hb]; rfl
    rw [h_61, h_54, h_47, h_40, h_33]
    norm_num [apply_5_writes]
    congr 6
    all_goals apply Std.U32.bv_eq_imp_eq
    all_goals (
      simp only [
        hRC,
        h_29.2, h_27.2, h_26.2, h_25,
        h_36.2, h_35.2, h_34,
        h_43.2, h_42.2, h_41,
        h_50.2, h_49.2, h_48,
        h_57.2, h_56.2, h_55,
        h_7, h_9, h_20, h_22, h_24,
        h_6.2, h_8.2, h_19.2, h_21.2, h_23.2,
        h_28,
        h, h_1, h_2, h_3, h_4, h_5, h_10, h_11, h_12, h_13, h_14, h_15, h_16, h_17, h_18,
        Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, Foundation.rot32]
      norm_num)

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round3_pi_rho_chi_y0_zeta1_spec_fc
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[0]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 0
      let bx1 := Foundation.rot32 (s.st.val[5]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 22
      let bx2 := Foundation.rot32 (s.st.val[10]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 21
      let bx3 := Foundation.rot32 (s.st.val[15]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 10
      let bx4 := Foundation.rot32 (s.st.val[20]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 7
      r.d = s.d ∧ r.c = s.c ∧ r.i.val = s.i.val + 1 ∧
      r.st.val = apply_5_writes s.st.val
        0 5 10 15 20
        1#usize 1#usize 1#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_1.val[s.i.val]!)
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round3_pi_rho_chi_y0_zeta1
  hax_mvcgen
  all_goals try scalar_tac
  expose_names
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_61.trans (h_54.trans (h_47.trans (h_40.trans h_33)))
  · exact h_60.trans (h_53.trans (h_46.trans (h_39.trans h_32)))
  · rw [h_59, h_52, h_45, h_38, h_31, h_30]
    rfl
  · have hb : s.i.val < keccak.RC_INTERLEAVED_1.val.length := by
      have hl : keccak.RC_INTERLEAVED_1.val.length = 255 := Array.length_eq _
      omega
    have hRC : keccak.RC_INTERLEAVED_1.val[s.i.val]?.getD default
             = keccak.RC_INTERLEAVED_1.val[s.i.val]'hb := by
      rw [List.getElem?_eq_getElem hb]; rfl
    rw [h_62, h_55, h_48, h_41, h_34]
    norm_num [apply_5_writes]
    congr 6
    all_goals apply Std.U32.bv_eq_imp_eq
    all_goals (
      simp only [
        hRC,
        h_29.2, h_27.2, h_26.2, h_25,
        h_37.2, h_36.2, h_35,
        h_44.2, h_43.2, h_42,
        h_51.2, h_50.2, h_49,
        h_58.2, h_57.2, h_56,
        h_7, h_9, h_20, h_22, h_24,
        h_6.2, h_8.2, h_19.2, h_21.2, h_23.2,
        h_28,
        h, h_1, h_2, h_3, h_4, h_5, h_10, h_11, h_12, h_13, h_14, h_15, h_16, h_17, h_18,
        Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, Foundation.rot32]
      norm_num)

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round3_pi_rho_chi_y1_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[16]!.val[0]! ^^^ s.d.val[3]!.val[0]!) 14
      let bx1 := Foundation.rot32 (s.st.val[21]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 10
      let bx2 := Foundation.rot32 (s.st.val[1]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 2
      let bx3 := Foundation.rot32 (s.st.val[6]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 23
      let bx4 := Foundation.rot32 (s.st.val[11]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 31
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        1 6 11 16 21
        0#usize 0#usize 0#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round3_pi_rho_chi_y1_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round3_pi_rho_chi_y1_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[16]!.val[1]! ^^^ s.d.val[3]!.val[1]!) 14
      let bx1 := Foundation.rot32 (s.st.val[21]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 10
      let bx2 := Foundation.rot32 (s.st.val[1]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 1
      let bx3 := Foundation.rot32 (s.st.val[6]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 22
      let bx4 := Foundation.rot32 (s.st.val[11]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 30
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        1 6 11 16 21
        1#usize 1#usize 1#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round3_pi_rho_chi_y1_zeta1

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round3_pi_rho_chi_y2_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[7]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 1
      let bx1 := Foundation.rot32 (s.st.val[12]!.val[0]! ^^^ s.d.val[2]!.val[0]!) 3
      let bx2 := Foundation.rot32 (s.st.val[17]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 13
      let bx3 := Foundation.rot32 (s.st.val[22]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 4
      let bx4 := Foundation.rot32 (s.st.val[2]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 9
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        2 7 12 17 22
        0#usize 0#usize 0#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round3_pi_rho_chi_y2_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round3_pi_rho_chi_y2_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[7]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 0
      let bx1 := Foundation.rot32 (s.st.val[12]!.val[1]! ^^^ s.d.val[2]!.val[1]!) 3
      let bx2 := Foundation.rot32 (s.st.val[17]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 12
      let bx3 := Foundation.rot32 (s.st.val[22]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 4
      let bx4 := Foundation.rot32 (s.st.val[2]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 9
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        2 7 12 17 22
        1#usize 1#usize 1#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round3_pi_rho_chi_y2_zeta1

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round3_pi_rho_chi_y3_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[23]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 14
      let bx1 := Foundation.rot32 (s.st.val[3]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 18
      let bx2 := Foundation.rot32 (s.st.val[8]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 5
      let bx3 := Foundation.rot32 (s.st.val[13]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 8
      let bx4 := Foundation.rot32 (s.st.val[18]!.val[0]! ^^^ s.d.val[3]!.val[0]!) 28
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        3 8 13 18 23
        0#usize 0#usize 0#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round3_pi_rho_chi_y3_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round3_pi_rho_chi_y3_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[23]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 13
      let bx1 := Foundation.rot32 (s.st.val[3]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 18
      let bx2 := Foundation.rot32 (s.st.val[8]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 5
      let bx3 := Foundation.rot32 (s.st.val[13]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 7
      let bx4 := Foundation.rot32 (s.st.val[18]!.val[1]! ^^^ s.d.val[3]!.val[1]!) 28
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        3 8 13 18 23
        1#usize 1#usize 1#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round3_pi_rho_chi_y3_zeta1

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round3_pi_rho_chi_y4_zeta0_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[14]!.val[0]! ^^^ s.d.val[2]!.val[0]!) 31
      let bx1 := Foundation.rot32 (s.st.val[19]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 28
      let bx2 := Foundation.rot32 (s.st.val[24]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 20
      let bx3 := Foundation.rot32 (s.st.val[4]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 21
      let bx4 := Foundation.rot32 (s.st.val[9]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 1
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        4 9 14 19 24
        0#usize 0#usize 0#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round3_pi_rho_chi_y4_zeta0

set_option maxHeartbeats 16000000 in
@[spec]
private theorem round3_pi_rho_chi_y4_zeta1_spec_fc (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := Foundation.rot32 (s.st.val[14]!.val[1]! ^^^ s.d.val[2]!.val[1]!) 31
      let bx1 := Foundation.rot32 (s.st.val[19]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 27
      let bx2 := Foundation.rot32 (s.st.val[24]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 19
      let bx3 := Foundation.rot32 (s.st.val[4]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 20
      let bx4 := Foundation.rot32 (s.st.val[9]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 1
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        4 9 14 19 24
        1#usize 1#usize 1#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  round1_prc_y_zeta_no_rc_proof keccak.keccakf1600_round3_pi_rho_chi_y4_zeta1

/-! ### Round-3 PrcLift bit-side equivalences -/

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_pi_rho_chi_y0_zeta0_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_pi_rho_chi_y0_zeta0 BR (KState.fromAeneas s) ∧
      r.i = s.i ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine ⟨?_, hi_eq⟩
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_pi_rho_chi_y0_zeta1_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_pi_rho_chi_y0_zeta1 BR (KState.fromAeneas s) ∧
      r.i.val = s.i.val + 1 ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine ⟨?_, hi_eq⟩
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · exact usize_succ_eq hi_eq hi

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_pi_rho_chi_y1_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_pi_rho_chi_y1_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_pi_rho_chi_y1_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_pi_rho_chi_y1_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_pi_rho_chi_y2_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_pi_rho_chi_y2_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_pi_rho_chi_y2_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_pi_rho_chi_y2_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_pi_rho_chi_y3_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_pi_rho_chi_y3_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_pi_rho_chi_y3_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_pi_rho_chi_y3_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_pi_rho_chi_y4_zeta0_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_pi_rho_chi_y4_zeta0 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta0, KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

set_option maxHeartbeats 4000000 in
@[spec high]
theorem bit_round3_pi_rho_chi_y4_zeta1_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_round3_pi_rho_chi_y4_zeta1 (KState.fromAeneas s) ⌝ ⦄ := by
  mvcgen
  rename_i r
  intro hd hc hi_eq hst
  refine KState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · apply Vector.toArray_inj.mp
    simp [stateArray25FromAeneas, hst, List.map_set,
      Lane.fromAeneas_set_zeta1,
      KState.fromAeneas, stateArray5FromAeneas_getElem]
  · show stateArray5FromAeneas r.c = stateArray5FromAeneas s.c
    rw [hc]
  · show stateArray5FromAeneas r.d = stateArray5FromAeneas s.d
    rw [hd]
  · show r.i = s.i
    exact hi_eq

/-! ## Compositions (round 3) -/

section Round3ThetaComp
attribute [local irreducible]
  bit_round3_theta_c_x0_z0 bit_round3_theta_c_x0_z1
  bit_round3_theta_c_x1_z0 bit_round3_theta_c_x1_z1
  bit_round3_theta_c_x2_z0 bit_round3_theta_c_x2_z1
  bit_round3_theta_c_x3_z0 bit_round3_theta_c_x3_z1
  bit_round3_theta_c_x4_z0 bit_round3_theta_c_x4_z1
  bit_round3_theta_d

@[spec high]
theorem keccakf1600_round3_theta_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_theta s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round3_theta (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round3_theta
  mvcgen
  expose_names
  intro h_last
  rw [h_last, h_9, h_8, h_7, h_6, h_5, h_4, h_3, h_2, h_1, h]
  rfl

end Round3ThetaComp

section Round3PrcLiftComp
attribute [local irreducible]
  bit_round3_pi_rho_chi_y0_zeta0 bit_round3_pi_rho_chi_y0_zeta1
  bit_round3_pi_rho_chi_y1_zeta0 bit_round3_pi_rho_chi_y1_zeta1
  bit_round3_pi_rho_chi_y2_zeta0 bit_round3_pi_rho_chi_y2_zeta1
  bit_round3_pi_rho_chi_y3_zeta0 bit_round3_pi_rho_chi_y3_zeta1
  bit_round3_pi_rho_chi_y4_zeta0 bit_round3_pi_rho_chi_y4_zeta1

@[spec high]
theorem keccakf1600_round3_pi_rho_chi_1_eq
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_pi_rho_chi_1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round3_pi_rho_chi_1 BR (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round3_pi_rho_chi_1
  mvcgen
  · scalar_tac
  · expose_names
    intro h_y1z1
    rw [h_y1z1, h_2, h_1.1, h.1]
    rfl

@[spec high]
theorem keccakf1600_round3_pi_rho_chi_2_eq (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round3_pi_rho_chi_2 (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round3_pi_rho_chi_2
  mvcgen
  expose_names
  intro h_last
  rw [h_last, h_4, h_3, h_2, h_1, h]
  rfl

end Round3PrcLiftComp

/-! # Loop bridge

Closes the structural equivalence by lifting the 12 round-level `_eq` theorems through
the impl's 4-round bundle, then through the 6-iteration outer loop,
landing the top-level `keccakf1600 s ≡ bit_keccak_spec (KState.fromAeneas s)`.

Architecture: no `Balanced`-preservation needed — the bit-side defs are
pure `KState → KState` and `KState.fromAeneas r = bit_… (KState.fromAeneas s)`
chains cleanly across iterations.

Pattern:
1. Strengthen the 12 round-level `_eq` posts to include i-info (`r.i = s.i`
   for theta/pi_rho_chi_2, `r.i.val = s.i.val + 1` for pi_rho_chi_1).
2. Bundle into a 4-round `keccakf1600_4rounds_eq` (+ `r.i.val = s.i.val + 4`).
3. Iterate via `loop_range_spec_i32` for 6 iterations.
4. Post-reset `i := 0` to match `bit_keccak_spec`'s wrap.
-/

section LoopBridge

/-! ## Bit-side i-projection lemmas

The bit-side composer fns are nested let-bindings whose `.i` field
projects definitionally. Each `theta`/`pi_rho_chi_2` composer preserves
`i`; each `pi_rho_chi_1` composer bumps `i` by 1 (via the `y0_zeta1`
RC-bearing sub-piece). Used by the round-level `_i` theorems below to
derive the i-info from the bit-side equality. -/

theorem bit_keccakf1600_round0_theta_i (s : KState) :
    (bit_keccakf1600_round0_theta s).i = s.i := by
  unfold bit_keccakf1600_round0_theta bit_theta_d
    bit_theta_c_x0_z0 bit_theta_c_x0_z1
    bit_theta_c_x1_z0 bit_theta_c_x1_z1
    bit_theta_c_x2_z0 bit_theta_c_x2_z1
    bit_theta_c_x3_z0 bit_theta_c_x3_z1
    bit_theta_c_x4_z0 bit_theta_c_x4_z1
  rfl

theorem bit_keccakf1600_round0_pi_rho_chi_1_i (BR : Std.Usize) (s : KState) :
    (bit_keccakf1600_round0_pi_rho_chi_1 BR s).i =
      ⟨s.i.bv + (1 : BitVec System.Platform.numBits)⟩ := by
  unfold bit_keccakf1600_round0_pi_rho_chi_1
    bit_pi_rho_chi_y0_zeta0 bit_pi_rho_chi_y0_zeta1
    bit_pi_rho_chi_y1_zeta0 bit_pi_rho_chi_y1_zeta1
  rfl

theorem bit_keccakf1600_round0_pi_rho_chi_2_i (s : KState) :
    (bit_keccakf1600_round0_pi_rho_chi_2 s).i = s.i := by
  unfold bit_keccakf1600_round0_pi_rho_chi_2
    bit_pi_rho_chi_y2_zeta0 bit_pi_rho_chi_y2_zeta1
    bit_pi_rho_chi_y3_zeta0 bit_pi_rho_chi_y3_zeta1
    bit_pi_rho_chi_y4_zeta0 bit_pi_rho_chi_y4_zeta1
  rfl

theorem bit_keccakf1600_round1_theta_i (s : KState) :
    (bit_keccakf1600_round1_theta s).i = s.i := by
  unfold bit_keccakf1600_round1_theta bit_round1_theta_d
    bit_round1_theta_c_x0_z0 bit_round1_theta_c_x0_z1
    bit_round1_theta_c_x1_z0 bit_round1_theta_c_x1_z1
    bit_round1_theta_c_x2_z0 bit_round1_theta_c_x2_z1
    bit_round1_theta_c_x3_z0 bit_round1_theta_c_x3_z1
    bit_round1_theta_c_x4_z0 bit_round1_theta_c_x4_z1
  rfl

theorem bit_keccakf1600_round1_pi_rho_chi_1_i (BR : Std.Usize) (s : KState) :
    (bit_keccakf1600_round1_pi_rho_chi_1 BR s).i =
      ⟨s.i.bv + (1 : BitVec System.Platform.numBits)⟩ := by
  unfold bit_keccakf1600_round1_pi_rho_chi_1
    bit_round1_pi_rho_chi_y0_zeta0 bit_round1_pi_rho_chi_y0_zeta1
    bit_round1_pi_rho_chi_y1_zeta0 bit_round1_pi_rho_chi_y1_zeta1
  rfl

theorem bit_keccakf1600_round1_pi_rho_chi_2_i (s : KState) :
    (bit_keccakf1600_round1_pi_rho_chi_2 s).i = s.i := by
  unfold bit_keccakf1600_round1_pi_rho_chi_2
    bit_round1_pi_rho_chi_y2_zeta0 bit_round1_pi_rho_chi_y2_zeta1
    bit_round1_pi_rho_chi_y3_zeta0 bit_round1_pi_rho_chi_y3_zeta1
    bit_round1_pi_rho_chi_y4_zeta0 bit_round1_pi_rho_chi_y4_zeta1
  rfl

theorem bit_keccakf1600_round2_theta_i (s : KState) :
    (bit_keccakf1600_round2_theta s).i = s.i := by
  unfold bit_keccakf1600_round2_theta bit_round2_theta_d
    bit_round2_theta_c_x0_z0 bit_round2_theta_c_x0_z1
    bit_round2_theta_c_x1_z0 bit_round2_theta_c_x1_z1
    bit_round2_theta_c_x2_z0 bit_round2_theta_c_x2_z1
    bit_round2_theta_c_x3_z0 bit_round2_theta_c_x3_z1
    bit_round2_theta_c_x4_z0 bit_round2_theta_c_x4_z1
  rfl

theorem bit_keccakf1600_round2_pi_rho_chi_1_i (BR : Std.Usize) (s : KState) :
    (bit_keccakf1600_round2_pi_rho_chi_1 BR s).i =
      ⟨s.i.bv + (1 : BitVec System.Platform.numBits)⟩ := by
  unfold bit_keccakf1600_round2_pi_rho_chi_1
    bit_round2_pi_rho_chi_y0_zeta0 bit_round2_pi_rho_chi_y0_zeta1
    bit_round2_pi_rho_chi_y1_zeta0 bit_round2_pi_rho_chi_y1_zeta1
  rfl

theorem bit_keccakf1600_round2_pi_rho_chi_2_i (s : KState) :
    (bit_keccakf1600_round2_pi_rho_chi_2 s).i = s.i := by
  unfold bit_keccakf1600_round2_pi_rho_chi_2
    bit_round2_pi_rho_chi_y2_zeta0 bit_round2_pi_rho_chi_y2_zeta1
    bit_round2_pi_rho_chi_y3_zeta0 bit_round2_pi_rho_chi_y3_zeta1
    bit_round2_pi_rho_chi_y4_zeta0 bit_round2_pi_rho_chi_y4_zeta1
  rfl

theorem bit_keccakf1600_round3_theta_i (s : KState) :
    (bit_keccakf1600_round3_theta s).i = s.i := by
  unfold bit_keccakf1600_round3_theta bit_round3_theta_d
    bit_round3_theta_c_x0_z0 bit_round3_theta_c_x0_z1
    bit_round3_theta_c_x1_z0 bit_round3_theta_c_x1_z1
    bit_round3_theta_c_x2_z0 bit_round3_theta_c_x2_z1
    bit_round3_theta_c_x3_z0 bit_round3_theta_c_x3_z1
    bit_round3_theta_c_x4_z0 bit_round3_theta_c_x4_z1
  rfl

theorem bit_keccakf1600_round3_pi_rho_chi_1_i (BR : Std.Usize) (s : KState) :
    (bit_keccakf1600_round3_pi_rho_chi_1 BR s).i =
      ⟨s.i.bv + (1 : BitVec System.Platform.numBits)⟩ := by
  unfold bit_keccakf1600_round3_pi_rho_chi_1
    bit_round3_pi_rho_chi_y0_zeta0 bit_round3_pi_rho_chi_y0_zeta1
    bit_round3_pi_rho_chi_y1_zeta0 bit_round3_pi_rho_chi_y1_zeta1
  rfl

theorem bit_keccakf1600_round3_pi_rho_chi_2_i (s : KState) :
    (bit_keccakf1600_round3_pi_rho_chi_2 s).i = s.i := by
  unfold bit_keccakf1600_round3_pi_rho_chi_2
    bit_round3_pi_rho_chi_y2_zeta0 bit_round3_pi_rho_chi_y2_zeta1
    bit_round3_pi_rho_chi_y3_zeta0 bit_round3_pi_rho_chi_y3_zeta1
    bit_round3_pi_rho_chi_y4_zeta0 bit_round3_pi_rho_chi_y4_zeta1
  rfl

/-- `(KState.fromAeneas r).i = r.i` definitionally. Used to project i-info
    out of the bit-side equality. -/
private theorem fromAeneas_i_eq (r : state.KeccakState) :
    (KState.fromAeneas r).i = r.i := rfl

/-- Inverse of `usize_succ_eq`: from `r.bv = s.bv + 1` (the bit-side
    increment encoding) and `s.val < 24` (overflow guard), recover the
    UScalar-level equation `r.val = s.val + 1`. -/
private theorem usize_succ_val_eq
    {r s : Aeneas.Std.Usize} (hr : r = ⟨s.bv + (1 : BitVec System.Platform.numBits)⟩)
    (hi : s.val < 24) :
    r.val = s.val + 1 := by
  subst hr
  show (s.bv + (1 : BitVec System.Platform.numBits)).toNat = s.val + 1
  have h32 : (32 : Nat) ≤ System.Platform.numBits := by
    have := System.Platform.numBits_eq; omega
  have hpow : (2 : Nat) ^ 32 ≤ 2 ^ System.Platform.numBits :=
    Nat.pow_le_pow_right (by decide) h32
  have hone : (1 : BitVec System.Platform.numBits).toNat = 1 := by
    have h1 : (1 : Nat) % 2 ^ System.Platform.numBits = 1 := by
      apply Nat.mod_eq_of_lt; omega
    simp [BitVec.toNat_ofNat, h1]
  rw [BitVec.toNat_add, hone]
  have hsv : s.bv.toNat = s.val := rfl
  have hmod : (s.bv.toNat + 1) % 2 ^ System.Platform.numBits = s.bv.toNat + 1 := by
    apply Nat.mod_eq_of_lt
    rw [hsv]; omega
  rw [hmod, hsv]

/-! ## Bundled round-level Triples

Each combines the existing `keccakf1600_round{k}_{theta,pi_rho_chi_1,pi_rho_chi_2}_eq`
(bit-side equality) with the i-info derived via the `_i` projection
lemmas above. The bundled posts thread `r.i = s.i` (for non-mutating
calls) or `r.i.val = s.i.val + 1` (for `pi_rho_chi_1`), enabling
`hi : s_iter.i.val < 24` discharge in the 4-round `Triple.bind` chain. -/

private theorem round0_theta_bundled (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round0_theta (KState.fromAeneas s)
      ∧ r.i = s.i ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_round0_theta_eq s)
  rw [PostCond.entails_noThrow]
  intro r h_eq
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_eq ⊢
  refine ⟨h_eq, ?_⟩
  have hi : (KState.fromAeneas r).i = (bit_keccakf1600_round0_theta (KState.fromAeneas s)).i :=
    congrArg (·.i) h_eq
  rw [bit_keccakf1600_round0_theta_i] at hi
  exact hi

private theorem round0_pi_rho_chi_1_bundled
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round0_pi_rho_chi_1 BR (KState.fromAeneas s)
      ∧ r.i.val = s.i.val + 1 ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_round0_pi_rho_chi_1_eq BR s hi)
  rw [PostCond.entails_noThrow]
  intro r h_eq
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_eq ⊢
  refine ⟨h_eq, ?_⟩
  have heq : (KState.fromAeneas r).i =
      (bit_keccakf1600_round0_pi_rho_chi_1 BR (KState.fromAeneas s)).i :=
    congrArg (·.i) h_eq
  rw [bit_keccakf1600_round0_pi_rho_chi_1_i] at heq
  exact usize_succ_val_eq heq hi

private theorem round0_pi_rho_chi_2_bundled (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round0_pi_rho_chi_2 (KState.fromAeneas s)
      ∧ r.i = s.i ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_round0_pi_rho_chi_2_eq s)
  rw [PostCond.entails_noThrow]
  intro r h_eq
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_eq ⊢
  refine ⟨h_eq, ?_⟩
  have hi : (KState.fromAeneas r).i = (bit_keccakf1600_round0_pi_rho_chi_2 (KState.fromAeneas s)).i :=
    congrArg (·.i) h_eq
  rw [bit_keccakf1600_round0_pi_rho_chi_2_i] at hi
  exact hi

private theorem round1_theta_bundled (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round1_theta (KState.fromAeneas s)
      ∧ r.i = s.i ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_round1_theta_eq s)
  rw [PostCond.entails_noThrow]
  intro r h_eq
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_eq ⊢
  refine ⟨h_eq, ?_⟩
  have hi : (KState.fromAeneas r).i = (bit_keccakf1600_round1_theta (KState.fromAeneas s)).i :=
    congrArg (·.i) h_eq
  rw [bit_keccakf1600_round1_theta_i] at hi
  exact hi

private theorem round1_pi_rho_chi_1_bundled
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round1_pi_rho_chi_1 BR (KState.fromAeneas s)
      ∧ r.i.val = s.i.val + 1 ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_round1_pi_rho_chi_1_eq BR s hi)
  rw [PostCond.entails_noThrow]
  intro r h_eq
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_eq ⊢
  refine ⟨h_eq, ?_⟩
  have heq : (KState.fromAeneas r).i =
      (bit_keccakf1600_round1_pi_rho_chi_1 BR (KState.fromAeneas s)).i :=
    congrArg (·.i) h_eq
  rw [bit_keccakf1600_round1_pi_rho_chi_1_i] at heq
  exact usize_succ_val_eq heq hi

private theorem round1_pi_rho_chi_2_bundled (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round1_pi_rho_chi_2 (KState.fromAeneas s)
      ∧ r.i = s.i ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_round1_pi_rho_chi_2_eq s)
  rw [PostCond.entails_noThrow]
  intro r h_eq
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_eq ⊢
  refine ⟨h_eq, ?_⟩
  have hi : (KState.fromAeneas r).i = (bit_keccakf1600_round1_pi_rho_chi_2 (KState.fromAeneas s)).i :=
    congrArg (·.i) h_eq
  rw [bit_keccakf1600_round1_pi_rho_chi_2_i] at hi
  exact hi

private theorem round2_theta_bundled (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_theta s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round2_theta (KState.fromAeneas s)
      ∧ r.i = s.i ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_round2_theta_eq s)
  rw [PostCond.entails_noThrow]
  intro r h_eq
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_eq ⊢
  refine ⟨h_eq, ?_⟩
  have hi : (KState.fromAeneas r).i = (bit_keccakf1600_round2_theta (KState.fromAeneas s)).i :=
    congrArg (·.i) h_eq
  rw [bit_keccakf1600_round2_theta_i] at hi
  exact hi

private theorem round2_pi_rho_chi_1_bundled
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round2_pi_rho_chi_1 BR (KState.fromAeneas s)
      ∧ r.i.val = s.i.val + 1 ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_round2_pi_rho_chi_1_eq BR s hi)
  rw [PostCond.entails_noThrow]
  intro r h_eq
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_eq ⊢
  refine ⟨h_eq, ?_⟩
  have heq : (KState.fromAeneas r).i =
      (bit_keccakf1600_round2_pi_rho_chi_1 BR (KState.fromAeneas s)).i :=
    congrArg (·.i) h_eq
  rw [bit_keccakf1600_round2_pi_rho_chi_1_i] at heq
  exact usize_succ_val_eq heq hi

private theorem round2_pi_rho_chi_2_bundled (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round2_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round2_pi_rho_chi_2 (KState.fromAeneas s)
      ∧ r.i = s.i ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_round2_pi_rho_chi_2_eq s)
  rw [PostCond.entails_noThrow]
  intro r h_eq
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_eq ⊢
  refine ⟨h_eq, ?_⟩
  have hi : (KState.fromAeneas r).i = (bit_keccakf1600_round2_pi_rho_chi_2 (KState.fromAeneas s)).i :=
    congrArg (·.i) h_eq
  rw [bit_keccakf1600_round2_pi_rho_chi_2_i] at hi
  exact hi

private theorem round3_theta_bundled (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_theta s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round3_theta (KState.fromAeneas s)
      ∧ r.i = s.i ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_round3_theta_eq s)
  rw [PostCond.entails_noThrow]
  intro r h_eq
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_eq ⊢
  refine ⟨h_eq, ?_⟩
  have hi : (KState.fromAeneas r).i = (bit_keccakf1600_round3_theta (KState.fromAeneas s)).i :=
    congrArg (·.i) h_eq
  rw [bit_keccakf1600_round3_theta_i] at hi
  exact hi

private theorem round3_pi_rho_chi_1_bundled
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_pi_rho_chi_1 BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round3_pi_rho_chi_1 BR (KState.fromAeneas s)
      ∧ r.i.val = s.i.val + 1 ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_round3_pi_rho_chi_1_eq BR s hi)
  rw [PostCond.entails_noThrow]
  intro r h_eq
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_eq ⊢
  refine ⟨h_eq, ?_⟩
  have heq : (KState.fromAeneas r).i =
      (bit_keccakf1600_round3_pi_rho_chi_1 BR (KState.fromAeneas s)).i :=
    congrArg (·.i) h_eq
  rw [bit_keccakf1600_round3_pi_rho_chi_1_i] at heq
  exact usize_succ_val_eq heq hi

private theorem round3_pi_rho_chi_2_bundled (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_pi_rho_chi_2 s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_round3_pi_rho_chi_2 (KState.fromAeneas s)
      ∧ r.i = s.i ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_round3_pi_rho_chi_2_eq s)
  rw [PostCond.entails_noThrow]
  intro r h_eq
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_eq ⊢
  refine ⟨h_eq, ?_⟩
  have hi : (KState.fromAeneas r).i = (bit_keccakf1600_round3_pi_rho_chi_2 (KState.fromAeneas s)).i :=
    congrArg (·.i) h_eq
  rw [bit_keccakf1600_round3_pi_rho_chi_2_i] at hi
  exact hi

/-! ## Main 4-round equivalence

Chains the 12 bundled round-level Triples via `Triple.bind`. The
threaded i-info from each call's conjunctive post discharges the
`s_iter.i.val < 24` precondition required by the next `pi_rho_chi_1`.

The bit-side equality threading is straightforward: each step rewrites
`KState.fromAeneas s_{k+1} = bit_… (KState.fromAeneas s_k)`, and the
final conclusion follows by `unfold bit_keccakf1600_4rounds; rfl`-style
collapse over the 12 chained equalities. -/

open libcrux_iot_sha3.Foundation (triple_imp_intro triple_conj_post
  loop_range_spec_i32 IteratorRange_next_spec_i32
  pure_prop_holds of_pure_prop_holds)

open Result ControlFlow

/-- Local copy of the private `triple_of_ok_i32` from `Keccakf1600Loop.lean`:
    a pure `ok v` value satisfies any `Triple` whose post `P r` holds at `v`. -/
private theorem triple_of_ok_local {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = Aeneas.Std.Result.ok v) (hp : P v) :
    (⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) := by
  subst hx; simp [Std.Do.Triple, WP.wp, PredTrans.apply, hp]

set_option maxHeartbeats 4000000 in
theorem keccakf1600_4rounds_eq (BR : Std.Usize) (s : state.KeccakState)
    (hi : s.i.val + 4 ≤ 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_4rounds BR s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r = bit_keccakf1600_4rounds BR (KState.fromAeneas s)
      ∧ r.i.val = s.i.val + 4 ⌝ ⦄ := by
  unfold keccak.keccakf1600_4rounds
  -- Round 0
  apply Std.Do.Triple.bind _ _ (round0_theta_bundled s)
  intro s1
  apply triple_imp_intro
  rintro ⟨h_eq_1, h_i_1⟩
  apply Std.Do.Triple.bind _ _
    (round0_pi_rho_chi_1_bundled BR s1 (by rw [h_i_1]; omega))
  intro s2
  apply triple_imp_intro
  rintro ⟨h_eq_2, h_i_2⟩
  apply Std.Do.Triple.bind _ _ (round0_pi_rho_chi_2_bundled s2)
  intro s3
  apply triple_imp_intro
  rintro ⟨h_eq_3, h_i_3⟩
  -- Round 1
  apply Std.Do.Triple.bind _ _ (round1_theta_bundled s3)
  intro s4
  apply triple_imp_intro
  rintro ⟨h_eq_4, h_i_4⟩
  apply Std.Do.Triple.bind _ _
    (round1_pi_rho_chi_1_bundled BR s4
      (by rw [show s4.i = s3.i from h_i_4, show s3.i = s2.i from h_i_3, h_i_2,
              show s1.i = s.i from h_i_1]; omega))
  intro s5
  apply triple_imp_intro
  rintro ⟨h_eq_5, h_i_5⟩
  apply Std.Do.Triple.bind _ _ (round1_pi_rho_chi_2_bundled s5)
  intro s6
  apply triple_imp_intro
  rintro ⟨h_eq_6, h_i_6⟩
  -- Round 2
  apply Std.Do.Triple.bind _ _ (round2_theta_bundled s6)
  intro s7
  apply triple_imp_intro
  rintro ⟨h_eq_7, h_i_7⟩
  apply Std.Do.Triple.bind _ _
    (round2_pi_rho_chi_1_bundled BR s7
      (by rw [show s7.i = s6.i from h_i_7, show s6.i = s5.i from h_i_6, h_i_5,
              show s4.i = s3.i from h_i_4, show s3.i = s2.i from h_i_3, h_i_2,
              show s1.i = s.i from h_i_1]; omega))
  intro s8
  apply triple_imp_intro
  rintro ⟨h_eq_8, h_i_8⟩
  apply Std.Do.Triple.bind _ _ (round2_pi_rho_chi_2_bundled s8)
  intro s9
  apply triple_imp_intro
  rintro ⟨h_eq_9, h_i_9⟩
  -- Round 3
  apply Std.Do.Triple.bind _ _ (round3_theta_bundled s9)
  intro s10
  apply triple_imp_intro
  rintro ⟨h_eq_10, h_i_10⟩
  apply Std.Do.Triple.bind _ _
    (round3_pi_rho_chi_1_bundled BR s10
      (by rw [show s10.i = s9.i from h_i_10, show s9.i = s8.i from h_i_9, h_i_8,
              show s7.i = s6.i from h_i_7, show s6.i = s5.i from h_i_6, h_i_5,
              show s4.i = s3.i from h_i_4, show s3.i = s2.i from h_i_3, h_i_2,
              show s1.i = s.i from h_i_1]; omega))
  intro s11
  apply triple_imp_intro
  rintro ⟨h_eq_11, h_i_11⟩
  -- Tail: round3_pi_rho_chi_2 — combine with the chain to derive the post.
  apply Std.Do.Triple.of_entails_right _ (round3_pi_rho_chi_2_bundled s11)
  rw [PostCond.entails_noThrow]
  intro r ⟨h_eq_12, h_i_12⟩
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_eq_12 h_i_12 ⊢
  refine ⟨?_, ?_⟩
  · -- bit-side equality: chain the 12 h_eq_k's into the bit_keccakf1600_4rounds unfolding
    unfold bit_keccakf1600_4rounds
    rw [h_eq_12, h_eq_11, h_eq_10, h_eq_9, h_eq_8, h_eq_7, h_eq_6, h_eq_5,
        h_eq_4, h_eq_3, h_eq_2, h_eq_1]
  · -- r.i.val = s.i.val + 4: chain the 12 h_i_k's.
    -- r.i = s11.i (h_i_12), s11.i.val = s10.i.val + 1 (h_i_11),
    -- s10.i = s9.i (h_i_10), s9.i = s8.i (h_i_9), s8.i.val = s7.i.val + 1 (h_i_8),
    -- s7.i = s6.i (h_i_7), s6.i = s5.i (h_i_6), s5.i.val = s4.i.val + 1 (h_i_5),
    -- s4.i = s3.i (h_i_4), s3.i = s2.i (h_i_3), s2.i.val = s1.i.val + 1 (h_i_2),
    -- s1.i = s.i (h_i_1).
    have : r.i = s11.i := h_i_12
    have : r.i.val = s11.i.val := congrArg (·.val) this
    rw [this, h_i_11,
        show s10.i = s9.i from h_i_10, show s9.i = s8.i from h_i_9, h_i_8,
        show s7.i = s6.i from h_i_7, show s6.i = s5.i from h_i_6, h_i_5,
        show s4.i = s3.i from h_i_4, show s3.i = s2.i from h_i_3, h_i_2,
        show s1.i = s.i from h_i_1]

/-! ## Loop bridge: iterate `bit_keccakf1600_4rounds` 6 times

Uses `loop_range_spec_i32` (from `Foundation/I32LoopSpec.lean`) with an
invariant that tracks both the iteration-index → `s.i` correspondence
(`s_iter.i.val = 4 * k.val.toNat`) and the bit-side equality
(`KState.fromAeneas s_iter = f^[k] (...)`). No `Balanced` / `lift_perm`
machinery is needed: the bit-side defs chain structurally. -/

/-- Per-iteration invariant for the bit-side loop bridge: at iter
    boundary `k ∈ [0, 6]`, the impl state has `i.val = 4k`, and its
    iso projection equals the `k`-fold bit-side iteration. -/
private def bit_loop_inv (s_0 : state.KeccakState) (k : Std.I32)
    (s_iter : state.KeccakState) : Prop :=
  0 ≤ k.val ∧ k.val ≤ 6 ∧
  s_iter.i.val = 4 * k.val.toNat ∧
  KState.fromAeneas s_iter =
    Nat.iterate (bit_keccakf1600_4rounds 0#usize) k.val.toNat (KState.fromAeneas s_0)

set_option maxHeartbeats 4000000 in
theorem keccakf1600_loop_eq (s : state.KeccakState) (h_i : s.i = 0#usize) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_loop { start := 0#i32, «end» := 6#i32 } s
    ⦃ ⇓ r => ⌜
      KState.fromAeneas r =
        Nat.iterate (bit_keccakf1600_4rounds 0#usize) 6 (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_i32
      (fun (iter1, s1) => keccak.keccakf1600_loop.body iter1 s1)
      s 0#i32 6#i32
      (fun k s_iter => pure (bit_loop_inv s k s_iter))
      (by decide)
      (by -- h_init: invariant at k=0 with s_iter = s.
          apply pure_prop_holds
          refine ⟨by decide, by decide, ?_, ?_⟩
          · rw [h_i]; rfl
          · show KState.fromAeneas s = KState.fromAeneas s
            rfl)
      ?_)
  · -- Post-entailment: extract bit-side eq at k=6.
    rw [PostCond.entails_noThrow]
    intro s_final hinv
    dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at hinv ⊢
    have ⟨_, _, _, h_iter⟩ := of_pure_prop_holds hinv
    have h6 : (6#i32 : Std.I32).val.toNat = 6 := by decide
    rw [h6] at h_iter
    exact h_iter
  · -- h_step: per-iteration body Triple.
    intro acc k h_ge h_le hinv
    have hk_inv := of_pure_prop_holds hinv
    obtain ⟨h_ge_k, h_le_k, h_acc_i, h_iter_acc⟩ := hk_inv
    unfold keccak.keccakf1600_loop.body
    apply Std.Do.Triple.bind _ _
      (IteratorRange_next_spec_i32 k 6#i32 (by decide)
        (Q := PostCond.noThrow fun (oi : Option Std.I32 × _) => ⌜
          match oi.1 with
          | none => k.val ≥ (6#i32 : Std.I32).val ∧ oi.2 = { start := k, «end» := 6#i32 }
          | some i => i = k ∧ k.val < (6#i32 : Std.I32).val ∧
                      oi.2.«end» = 6#i32 ∧ oi.2.start.val = k.val + 1
        ⌝)
        (fun hlt s hs => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          refine ⟨rfl, hlt, rfl, hs⟩)
        (fun hge => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          exact ⟨hge, rfl⟩))
    intro ⟨o, iter1⟩
    apply triple_imp_intro
    rcases o with _ | i
    · -- none branch: k.val = 6, body returns done acc.
      rintro ⟨hge, hiter1_eq⟩
      have h6 : (6#i32 : Std.I32).val = 6 := by decide
      have hk_eq : k.val = 6 := by omega
      have hk_eq_i32 : k = 6#i32 := Std.IScalar.eq_of_val_eq (by rw [hk_eq, h6])
      show ⦃⌜True⌝⦄ (Aeneas.Std.Result.ok (done acc) : Result _) ⦃_⦄
      apply triple_of_ok_local rfl
      apply pure_prop_holds
      refine ⟨by decide, by decide, ?_, ?_⟩
      · rw [hk_eq_i32] at h_acc_i; exact h_acc_i
      · rw [hk_eq_i32] at h_iter_acc; exact h_iter_acc
    · -- some i branch: body runs keccakf1600_4rounds 0 acc, returns cont (iter1, s1).
      rintro ⟨hi_eq, hk_lt, hiter1_end, hiter1_start⟩
      have h6 : (6#i32 : Std.I32).val = 6 := by decide
      cases hi_eq
      have hk_lt' : k.val < 6 := by rw [← h6]; exact hk_lt
      have hk_toNat_lt : k.val.toNat < 6 := by omega
      have h_i_bnd : acc.i.val + 4 ≤ 24 := by rw [h_acc_i]; omega
      show ⦃⌜True⌝⦄
        (do let s1 ← keccak.keccakf1600_4rounds 0#usize acc; Aeneas.Std.Result.ok (cont (iter1, s1)))
        ⦃_⦄
      apply Std.Do.Triple.bind _ _ (keccakf1600_4rounds_eq 0#usize acc h_i_bnd)
      intro s1
      apply triple_imp_intro
      rintro ⟨h_eq_s1, h_i_s1⟩
      apply triple_of_ok_local rfl
      refine ⟨hk_lt, hiter1_end, hiter1_start, ?_⟩
      apply pure_prop_holds
      have h_start_val : iter1.start.val = k.val + 1 := hiter1_start
      have h_start_ge : 0 ≤ iter1.start.val := by rw [h_start_val]; omega
      have h_start_le : iter1.start.val ≤ 6 := by rw [h_start_val]; omega
      have h_start_toNat : iter1.start.val.toNat = k.val.toNat + 1 := by
        rw [h_start_val, Int.toNat_add (by omega) (by decide)]; rfl
      refine ⟨h_start_ge, h_start_le, ?_, ?_⟩
      · -- s1.i.val = 4 * iter1.start.val.toNat
        rw [h_i_s1, h_acc_i, h_start_toNat]; ring
      · -- KState.fromAeneas s1 = f^[iter1.start.val.toNat] (KState.fromAeneas s)
        rw [h_start_toNat]
        -- f^[k+1] x = f (f^[k] x) via Function.iterate_succ_apply'
        rw [Function.iterate_succ_apply']
        rw [← h_iter_acc, ← h_eq_s1]

/-! ## Top-level keccakf1600 equivalence

Composes `keccakf1600_loop_eq` (the 6×4-round iteration) with the
trailing `{ s1 with i := 0#usize }` reset that matches the bit-side
`bit_keccak_spec`'s `{ s' with i := 0#usize }` wrap. -/

theorem keccakf1600_eq (s : state.KeccakState) (h_i : s.i = 0#usize) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600 s
    ⦃ ⇓ r => ⌜ KState.fromAeneas r = bit_keccak_spec (KState.fromAeneas s) ⌝ ⦄ := by
  unfold keccak.keccakf1600
  apply Std.Do.Triple.bind _ _ (keccakf1600_loop_eq s h_i)
  intro s1
  apply triple_imp_intro
  intro h_loop
  -- The tail: ok { s1 with i := 0#usize }.
  apply triple_of_ok_local rfl
  unfold bit_keccak_spec
  -- Goal: KState.fromAeneas { s1 with i := 0#usize } =
  --       { Nat.iterate (...) 6 (KState.fromAeneas s) with i := 0#usize }
  -- LHS = { KState.fromAeneas s1 with i := 0#usize } (by definition of fromAeneas)
  -- RHS = { Nat.iterate ... with i := 0#usize }; substitute h_loop.
  show KState.fromAeneas { s1 with i := 0#usize } =
    { Nat.iterate (bit_keccakf1600_4rounds 0#usize) 6 (KState.fromAeneas s) with i := 0#usize }
  rw [← h_loop]
  rfl

end LoopBridge

end libcrux_iot_sha3.Structural
