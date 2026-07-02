/-
  # `Matrix/ComputeMessage/FC.lean` — L7.4 FC theorem glue.

  Houses the L7.4 FC theorem `compute_message_fc`, gluing the direct
  decomposition (impl walk via `triple_*_ok_fc` + the A/B/C/D chain).

  POST:
    `hacspec_ml_kem.matrix.compute_message (lift_poly v)
       (lift_vec secret_as_ntt) (lift_vec u_as_ntt) = .ok (lift_poly p.1)`.
-/
import LibcruxIotMlKem.Spec.Lift
import LibcruxIotMlKem.Vector.Portable.Arithmetic.PerElement
import LibcruxIotMlKem.Vector.Portable.Arithmetic.Element
import LibcruxIotMlKem.Vector.Portable.Ntt
import LibcruxIotMlKem.Ntt
import LibcruxIotMlKem.InvertNtt
import LibcruxIotMlKem.Polynomial.NttDrivers
import LibcruxIotMlKem.Polynomial.PolyOps
import LibcruxIotMlKem.Polynomial.PolyOpsFcBarrett
import LibcruxIotMlKem.Polynomial.PolyOpsFc
import LibcruxIotMlKem.Polynomial.NttMultiply
import LibcruxIotMlKem.Matrix.Common
import LibcruxIotMlKem.Matrix.ComputeAsPlusE
import LibcruxIotMlKem.Matrix.Common
import LibcruxIotMlKem.Matrix.ComputeMessage.Impl
import LibcruxIotMlKem.Matrix.ComputeMessage.Hacspec

namespace libcrux_iot_ml_kem.Matrix.ComputeMessage.FC
open libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeMessage.Bridges libcrux_iot_ml_kem.Matrix.ComputeMessage.Hacspec libcrux_iot_ml_kem.Matrix.ComputeMessage.Impl
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec
open libcrux_iot_ml_kem.InvertNtt libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeAsPlusE libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.NttMultiply libcrux_iot_ml_kem.Polynomial.PolyOpsFc libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt

/-- Local copy of the `private triple_exists_ok_fc` helper (Impl/ComputeMessage):
    a `True`-pre Triple yielding `.ok` with the post is an existential witness. -/
private theorem triple_exists_ok_fc {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl, (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

/-- Local copy of the `private triple_of_ok_fc` helper (Impl/ComputeMessage). -/
private theorem triple_of_ok_fc {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

/-- `scaleZ c p` lanes are `feOfZMod _`, hence canonical (local copy of the
    `private canonArr_scaleZ'` in ComputeMessage/Hacspec). -/
private theorem scaleZ_canon (c : ZMod 3329)
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (j : Nat) (hj : j < 256) :
    libcrux_iot_ml_kem.Spec.Pure.Canonical ((scaleZ c p).val[j]!) := by
  unfold scaleZ
  show libcrux_iot_ml_kem.Spec.Pure.Canonical
    (((List.range 256).map (fun k => feOfZMod (c * zmodOfFE (p.val[k]!))))[j]!)
  rw [getElem!_pos _ j (by simp [List.length_map, List.length_range, hj])]
  rw [List.getElem_map, List.getElem_range]
  unfold libcrux_iot_ml_kem.Spec.Pure.Canonical feOfZMod
  have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
  rw [hq]
  show (BitVec.ofNat 16 ((c * zmodOfFE (p.val[j]!)).val)).toNat < 3329
  set z := c * zmodOfFE (p.val[j]!)
  have h_lt16 : z.val < 2 ^ 16 := by have := ZMod.val_lt z; omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt16]
  exact ZMod.val_lt _

/-- `lift_poly x` lanes are `lift_fe _ = feOfZMod _`, hence canonical. -/
private theorem lift_poly_canon
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (j : Nat) (hj : j < 256) :
    libcrux_iot_ml_kem.Spec.Pure.Canonical ((lift_poly re).val[j]!) := by
  unfold lift_poly
  show libcrux_iot_ml_kem.Spec.Pure.Canonical
    (((List.range 256).map (fun i =>
        lift_fe (re.coefficients.val[i / 16]!).elements.val[i % 16]!))[j]!)
  rw [getElem!_pos _ j (by simp [List.length_map, List.length_range, hj])]
  rw [List.getElem_map, List.getElem_range]
  unfold lift_fe libcrux_iot_ml_kem.Spec.Pure.Canonical feOfZMod
  have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
  rw [hq]
  show (⟨BitVec.ofNat 16 ((i16_to_spec_fe_plain
          (re.coefficients.val[j / 16]!).elements.val[j % 16]!).val)⟩ : Std.U16).val < 3329
  show (BitVec.ofNat 16 ((i16_to_spec_fe_plain
          (re.coefficients.val[j / 16]!).elements.val[j % 16]!).val)).toNat < 3329
  set z := i16_to_spec_fe_plain (re.coefficients.val[j / 16]!).elements.val[j % 16]!
  have h_lt16 : z.val < 2 ^ 16 := by
    have := ZMod.val_lt z; omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt16]
  exact ZMod.val_lt _

/-! ## (iii) — L7.4 FC theorem (glue of (i) + (ii)).

    PRE: `hK : K.val ≤ 4` plus per-lane `≤ 3328` bounds on `secret_as_ntt`,
    `u_as_ntt`, `v`. No `h_acc_bnd` (the impl re-zeros the accumulator). -/
@[spec]
theorem compute_message_fc
    {K : Std.Usize}
    (v : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (secret_as_ntt u_as_ntt : Std.Array
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (result : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (accumulator : Std.Array Std.I32 256#usize)
    (hK : K.val ≤ 4)
    (h_secret_bnd : ∀ k : Nat, k < K.val → ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((secret_as_ntt.val[k]!.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3328)
    (h_u_bnd : ∀ k : Nat, k < K.val → ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((u_as_ntt.val[k]!.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3328)
    (h_v_bnd : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((v.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_message
      (vectortraitsOperationsInst := portable_ops_inst)
      v secret_as_ntt u_as_ntt result scratch accumulator
    ⦃ ⇓ p => ⌜ ∃ spec_out,
                  hacspec_ml_kem.matrix.compute_message
                    (lift_poly v)
                    (lift_vec secret_as_ntt) (lift_vec u_as_ntt)
                  = .ok spec_out
                ∧ PolyMatches p.1 spec_out ⌝ ⦄ := by
  -- Fin-form bounds for the loop lemma.
  have h_secret_fin : ∀ k : Fin K.val, ∀ i j : Fin 16,
      ((secret_as_ntt.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328 :=
    fun k i j => h_secret_bnd k.val k.isLt i.val i.isLt j.val j.isLt
  have h_u_fin : ∀ k : Fin K.val, ∀ i j : Fin 16,
      ((u_as_ntt.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328 :=
    fun k i j => h_u_bnd k.val k.isLt i.val i.isLt j.val j.isLt
  -- Step 0: classify 0#i32 = .ok 0#i32; acc1 = repeat 256 (0#i32) (all-zero).
  set acc1 : Std.Array Std.I32 256#usize :=
    Std.Array.repeat (256#usize : Std.Usize) (0#i32 : Std.I32) with h_acc1_def
  have h_acc1_zero : ∀ n : Nat, n < 256 → (acc1.val[n]!).val = 0 := by
    intro n hn
    rw [h_acc1_def, Std.Array.repeat_val]
    rw [getElem!_pos _ n (by rw [List.length_replicate]; exact hn)]
    rw [List.getElem_replicate]; rfl
  -- Acc budget for the loop: acc1[n] = 0, K ≤ 4, so K·2^25 ≤ 2^30.
  have h_acc_budget : ∀ n : Fin 256,
      (acc1.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30 := by
    intro n
    have h0 : (acc1.val[n.val]!).val.natAbs = 0 := by rw [h_acc1_zero n.val n.isLt]; rfl
    rw [h0]
    have : K.val * 2^25 ≤ 4 * 2^25 := Nat.mul_le_mul_right _ hK
    omega
  -- S1: run the accumulation loop; get acc2 with the loop invariant.
  obtain ⟨acc2, h_acc2_eq, h_char⟩ := triple_exists_ok_fc
    (compute_message_loop_fc secret_as_ntt u_as_ntt acc1
      h_secret_fin h_u_fin h_acc_budget)
  -- Accumulator bound: acc2[n].natAbs ≤ K·2^25 ≤ 2^27 (from loop_inv conjunct 2).
  have h_acc2_bnd : ∀ n : Nat, n < 256 → (acc2.val[n]!).val.natAbs ≤ 2^27 := by
    intro n hn
    obtain ⟨_, h_inv_bnd⟩ := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_char
    have hb := h_inv_bnd n hn
    have h0 : (acc1.val[n]!).val.natAbs = 0 := by rw [h_acc1_zero n hn]; rfl
    rw [h0] at hb
    have hK4 : K.val * 2^25 ≤ 4 * 2^25 := Nat.mul_le_mul_right _ hK
    have : (2 ^ 27 : Nat) = 4 * 2^25 := by norm_num
    omega
  -- reducing step: result1.
  set s := Aeneas.Std.Array.to_slice acc2 with h_s_def
  have h_s_len : s.length = 256 := by
    rw [h_s_def, Aeneas.Std.Array.length_to_slice]; rfl
  have h_s_bnd : ∀ i : Nat, i < 256 → (s.val[i]!).val.natAbs ≤ 2^16 * 3328 := by
    intro i hi
    rw [h_s_def, Aeneas.Std.Array.val_to_slice]
    have := h_acc2_bnd i hi
    have h27 : (2 ^ 27 : Nat) ≤ 2^16 * 3328 := by norm_num
    omega
  obtain ⟨result1, h_result1_eq, h_result1_mont, h_result1_lane_bnd⟩ :=
    triple_exists_ok_fc
      (poly_reducing_from_i32_array_fc s result h_s_len h_s_bnd)
  -- lift_poly result1 = mont_strip (poly_reducing s).
  have h_result1_lift : lift_poly result1
      = Impl.mont_strip_pure (Spec.poly_reducing_from_i32_array_pure s) := by
    rw [← h_result1_mont, Impl.mont_strip_lift_poly_mont_eq_lift_poly]
  -- invert step. PRE ≤13312 from result1 ≤4993.
  have h_result1_bnd : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((result1.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 13312 := by
    intro chunk hchunk k hk
    have := h_result1_lane_bnd chunk hchunk k hk
    omega
  obtain ⟨⟨result2, scratch1⟩, h_inv_eq, h_result2_lift, h_result2_bnd⟩ :=
    triple_exists_ok_fc
      (invert_ntt_montgomery_fc (K := K) result1 scratch h_result1_bnd)
  dsimp only at h_inv_eq h_result2_lift h_result2_bnd
  -- subtract step. PRE: v ≤29439, result2 ≤32767.
  have h_v_self_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((v.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 29439 := by
    intro chunk hchunk ℓ hℓ
    have := h_v_bnd chunk hchunk ℓ hℓ; omega
  have h_result2_b_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((result2.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 32767 := by
    intro chunk hchunk ℓ hℓ
    have := h_result2_bnd chunk hchunk ℓ hℓ; omega
  obtain ⟨result3, h_sub_eq, h_result3_lift, h_result3_bnd⟩ :=
    triple_exists_ok_fc
      (subtract_reduce_fc v result2 h_v_self_bnd h_result2_b_bnd)
  -- Reduce the impl do-block to `.ok (result3, scratch1, acc2)`.
  apply triple_of_ok_fc
    (v := (result3, scratch1, acc2))
  · unfold libcrux_iot_ml_kem.matrix.compute_message
    simp only [libcrux_secrets.traits.Classify.Blanket.classify, Aeneas.Std.lift,
      Aeneas.Std.bind_tc_ok]
    rw [show (Std.Array.repeat (256#usize : Std.Usize) (0#i32 : Std.I32)) = acc1 from rfl]
    rw [h_acc2_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [← h_s_def, h_result1_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_inv_eq]; simp only [Aeneas.Std.bind_tc_ok]
    show (do
        let result3 ← polynomial.PolynomialRingElement.subtract_reduce portable_ops_inst v result2
        Aeneas.Std.Result.ok (result3, scratch1, acc2)) = Aeneas.Std.Result.ok (result3, scratch1, acc2)
    rw [h_sub_eq]; simp only [Aeneas.Std.bind_tc_ok]
  · -- Spec witness `lift_poly result3`, then the per-lane `LaneMatches` bridge.
    refine ⟨lift_poly result3, ?_, ?_⟩
    -- Chain A/B/C/D: prove the hacspec spec = .ok (lift_poly result3).
    · show hacspec_ml_kem.matrix.compute_message (lift_poly v)
          (lift_vec secret_as_ntt) (lift_vec u_as_ntt) = .ok (lift_poly result3)
      unfold hacspec_ml_kem.matrix.compute_message
      -- A: multiply_vectors = .ok (scaleZ 2285 (lift_poly result1)).
      have hA := compute_message_acc_bridge secret_as_ntt u_as_ntt acc1 acc2
        h_acc1_zero h_secret_fin h_u_fin h_char
      rw [← h_result1_lift] at hA
      rw [hA]; simp only [Aeneas.Std.bind_tc_ok]
      -- C: ntt_inverse (scaleZ 2285 (lift_poly result1))
      --      = .ok (scaleZ 3303 (invert_pure (scaleZ 2285 (lift_poly result1)))).
      have hCanon_s : ∀ j : Nat, j < 256 →
          libcrux_iot_ml_kem.Spec.Pure.Canonical
            ((scaleZ 2285 (lift_poly result1)).val[j]!) :=
        fun j hj => scaleZ_canon 2285 (lift_poly result1) j hj
      rw [ntt_inverse_eq_scaleZ_invert_pure (scaleZ 2285 (lift_poly result1)) hCanon_s]
      simp only [Aeneas.Std.bind_tc_ok]
      -- B: invert_pure (scaleZ 2285 x) = scaleZ 2285 (invert_pure x).
      rw [invert_ntt_montgomery_pure_scaleZ 2285 (lift_poly result1)
          (fun j hj => lift_poly_canon result1 j hj)]
      -- scaleZ 3303 (scaleZ 2285 y) = scaleZ 512 y.
      rw [scaleZ_compose 3303 2285 (Spec.invert_ntt_montgomery_pure (lift_poly result1)),
          glue_3303_2285]
      -- invert_pure (lift_poly result1) = lift_poly result2.
      rw [← h_result2_lift]
      -- D: sub_polynomials (lift_poly v) (scaleZ 512 (lift_poly result2))
      --      = .ok (subtract_reduce_pure (lift_poly v) (lift_poly result2)).
      rw [sub_polynomials_scaleZ_eq (lift_poly v) (lift_poly result2)
          (fun j hj => lift_poly_canon v j hj)]
      -- subtract_reduce_pure (lift_poly v) (lift_poly result2) = lift_poly result3.
      rw [← h_result3_lift]
    · -- Per-lane bridge: the impl output is the centered Barrett representative
      -- `|x| ≤ 1664`; `LaneMatches` records the tight bound + the residue equality
      -- `(x : ZMod q) = zmodOfFE (spec lane)`, discharged by `laneMatches_lift_fe`.
      unfold PolyMatches
      intro ℓ hℓ
      have hj : ℓ / 16 < 16 := Nat.div_lt_iff_lt_mul (by decide : 0 < 16) |>.mpr hℓ
      have hm : ℓ % 16 < 16 := Nat.mod_lt _ (by decide : 0 < 16)
      have hbnd : (((result3.coefficients.val[ℓ / 16]!).elements.val[ℓ % 16]!).val).natAbs ≤ 1664 :=
        h_result3_bnd (ℓ / 16) hj (ℓ % 16) hm
      rw [lift_poly_getElem result3 ℓ hℓ]
      exact laneMatches_lift_fe _ hbnd

/--
info: 'libcrux_iot_ml_kem.Matrix.ComputeMessage.FC.compute_message_fc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms compute_message_fc

end libcrux_iot_ml_kem.Matrix.ComputeMessage.FC