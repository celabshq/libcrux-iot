/-
  # `Matrix/ComputeRingElementV/FC.lean` — L7.3 FC theorem glue.

  Houses the L7.3 FC theorem `compute_ring_element_v_fc`, gluing the
  direct decomposition (impl walk via `triple_*_ok_fc` + the A/C/B/
  compose/glue/D′ chain). Mirrors L7.4 `compute_message_fc`
  near-verbatim, swapping the loop (chunks-exact deserialize loop
  instead of the sampled use-cache loop) and the tail (two
  `add_polynomials` instead of a single `subtract`).

  POST:
    `hacspec_ml_kem.matrix.compute_ring_element_v
       (lift_t_as_ntt_from_public_key public_key K) (lift_vec_slice r_as_ntt K)
       (lift_poly error_2) (lift_poly message) = .ok (lift_poly p.2.1)`.
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
import LibcruxIotMlKem.Sampling
import LibcruxIotMlKem.Serialize
import LibcruxIotMlKem.Matrix.ComputeRingElementV.Impl
import LibcruxIotMlKem.Matrix.ComputeMessage.Hacspec
import LibcruxIotMlKem.Matrix.ComputeVectorU.Hacspec
import LibcruxIotMlKem.Matrix.ComputeRingElementV.Hacspec

namespace libcrux_iot_ml_kem.Matrix.ComputeRingElementV.FC
open libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeMessage.Bridges libcrux_iot_ml_kem.Matrix.ComputeMessage.Hacspec libcrux_iot_ml_kem.Matrix.ComputeMessage.Impl libcrux_iot_ml_kem.Matrix.ComputeRingElementV.Hacspec libcrux_iot_ml_kem.Matrix.ComputeRingElementV.Impl libcrux_iot_ml_kem.Matrix.ComputeVectorU.Hacspec
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec
open libcrux_iot_ml_kem.InvertNtt libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeAsPlusE libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.NttMultiply libcrux_iot_ml_kem.Polynomial.PolyOpsFc libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Sampling libcrux_iot_ml_kem.Serialize libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-- Local copy of the `private triple_exists_ok_fc` helper. -/
private theorem triple_exists_ok_fc {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl, (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

/-- Local copy of the `private triple_of_ok_fc` helper. -/
private theorem triple_of_ok_fc {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

/-- `scaleZ c p` lanes are canonical. -/
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

/-- `lift_poly x` lanes are canonical. -/
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

/-! ## L7.3 FC theorem (capstone). -/
set_option maxHeartbeats 4000000 in
@[spec]
theorem compute_ring_element_v_fc
    (K : Std.Usize)
    (public_key : Slice Std.U8)
    (t_as_ntt_entry : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (r_as_ntt : Slice
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (error_2 message result :
      libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (cache : Slice
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (accumulator : Std.Array Std.I32 256#usize)
    (hK : K.val ≤ 4)
    (h_pk_len : public_key.length = K.val * 384)
    (h_r_len : r_as_ntt.length = K.val)
    (h_cache_len : cache.length = K.val)
    (h_r_bnd : ∀ c : Nat, c < K.val → ∀ a : Fin 16, ∀ b : Fin 16,
        ((r_as_ntt.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_cache_char : ∀ c : Nat, c < K.val →
        accumulating_ntt_multiply_poly_cache_post (r_as_ntt.val[c]!) (cache.val[c]!))
    (h_acc_zero : ∀ n : Nat, n < 256 → (accumulator.val[n]!).val = 0)
    (h_error_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
        ((error_2.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 3328)
    (h_message_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
        ((message.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_ring_element_v
      K (vectortraitsOperationsInst := portable_ops_inst)
      public_key t_as_ntt_entry r_as_ntt error_2 message result scratch
      cache accumulator
    ⦃ ⇓ p => ⌜ ∃ spec_out,
                  hacspec_ml_kem.matrix.compute_ring_element_v
                    (lift_t_as_ntt_from_public_key public_key K)
                    (lift_vec_slice r_as_ntt K)
                    (lift_poly error_2) (lift_poly message)
                  = .ok spec_out
                ∧ PolyMatches p.2.1 spec_out ⌝ ⦄ := by
  -- r_arr : Array Poly K from r_as_ntt.
  set r_arr : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K :=
    ⟨r_as_ntt.val, by rw [← h_r_len]⟩ with h_r_arr_def
  have h_r_arr : ∀ c : Nat, c < K.val → r_arr.val[c]! = r_as_ntt.val[c]! := by
    intro c hc; rfl
  -- Step 0: classify 0#i32 = .ok 0#i32; acc1 = repeat 256 (0#i32) (all-zero).
  set acc1 : Std.Array Std.I32 256#usize :=
    Std.Array.repeat (256#usize : Std.Usize) (0#i32 : Std.I32) with h_acc1_def
  have h_acc1_zero : ∀ n : Nat, n < 256 → (acc1.val[n]!).val = 0 := by
    intro n hn
    rw [h_acc1_def, Std.Array.repeat_val]
    rw [getElem!_pos _ n (by rw [List.length_replicate]; exact hn)]
    rw [List.getElem_replicate]; rfl
  -- iter0 reduction: BYTES_PER_RING_ELEMENT = 384; chunks_exact + enumerate.
  set iter0 : EnumCE :=
    { iter := { cs := 384#usize, elements := public_key }, count := 0#usize } with h_iter0_def
  -- S1: run the chunks-exact deserialize loop; get acc2 with the loop invariant.
  obtain ⟨⟨t_ent1, acc2⟩, h_loop_eq, h_char⟩ := triple_exists_ok_fc
    (compute_ring_element_v_loop_fc K hK public_key h_pk_len t_as_ntt_entry
      r_as_ntt cache r_arr h_r_len h_cache_len h_r_arr h_r_bnd h_cache_char
      acc1 h_acc1_zero iter0 h_iter0_def)
  -- Accumulator bound: acc2[n].natAbs ≤ K·2^25 ≤ 2^27 (from loop_inv conjunct 2).
  have h_acc2_bnd : ∀ n : Nat, n < 256 → (acc2.val[n]!).val.natAbs ≤ 2^27 := by
    intro n hn
    obtain ⟨_, h_inv_bnd⟩ := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_char
    have hb : (acc2.val[n]!).val.natAbs ≤ (acc1.val[n]!).val.natAbs + K.val * 2^25 :=
      h_inv_bnd n hn
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
  -- add-message-error step. PRE: result2 ≤32767, error_2+message ≤29439.
  have h_result2_b_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((result2.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 32767 := by
    intro chunk hchunk ℓ hℓ
    have := h_result2_bnd chunk hchunk ℓ hℓ; omega
  have h_sum_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      (((error_2.coefficients.val[chunk]!).elements.val[ℓ]!).val
        + ((message.coefficients.val[chunk]!).elements.val[ℓ]!).val
            : Int).natAbs ≤ 29439 := by
    intro chunk hchunk ℓ hℓ
    have he := h_error_bnd chunk hchunk ℓ hℓ
    have hm := h_message_bnd chunk hchunk ℓ hℓ
    omega
  obtain ⟨⟨result3, scratch2⟩, h_add_eq, h_result3_lift, h_result3_bnd⟩ :=
    triple_exists_ok_fc
      (add_message_error_reduce_fc error_2 message result2 scratch1
        h_result2_b_bnd h_sum_bnd)
  dsimp only at h_add_eq h_result3_lift h_result3_bnd
  -- BYTES_PER_RING_ELEMENT reduces to 384 (both constants are `irreducible`).
  have h_bpr : (libcrux_iot_ml_kem.constants.BYTES_PER_RING_ELEMENT : Result Std.Usize)
      = .ok (384#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.constants.BYTES_PER_RING_ELEMENT
    unfold libcrux_iot_ml_kem.constants.BITS_PER_RING_ELEMENT
    unfold libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
    -- 256 * 12 = 3072.
    have hm_max : (256#usize : Std.Usize).val * (12#usize : Std.Usize).val ≤ Std.Usize.max := by
      scalar_tac
    obtain ⟨m, hm_eq, hm_v⟩ := Std.WP.spec_imp_exists (Std.Usize.mul_spec hm_max)
    have hm : m = (3072#usize : Std.Usize) := by
      apply Aeneas.Std.UScalar.eq_of_val_eq
      show m.val = (3072#usize : Std.Usize).val; rw [hm_v]; decide
    rw [hm_eq, hm]
    -- 3072 / 8 = 384.
    obtain ⟨d, hd_eq, hd_v⟩ := Aeneas.Std.UScalar.div_spec (3072#usize : Std.Usize)
      (by decide : ((8#usize : Std.Usize).val : Nat) ≠ 0)
    have hd : d = (384#usize : Std.Usize) := by
      apply Aeneas.Std.UScalar.eq_of_val_eq
      show d.val = (384#usize : Std.Usize).val; rw [hd_v]; decide
    simp only [Aeneas.Std.bind_tc_ok, hd_eq, hd]
  -- Reduce the impl do-block to `.ok (t_ent1, result3, scratch2, acc2)`.
  apply triple_of_ok_fc
    (v := (t_ent1, result3, scratch2, acc2))
  · unfold libcrux_iot_ml_kem.matrix.compute_ring_element_v
    simp only [libcrux_secrets.traits.Classify.Blanket.classify, Aeneas.Std.lift,
      Aeneas.Std.bind_tc_ok]
    rw [show (Std.Array.repeat (256#usize : Std.Usize) (0#i32 : Std.I32)) = acc1 from rfl]
    -- BYTES_PER_RING_ELEMENT = 384, chunks_exact + enumerate = iter0.
    rw [h_bpr]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [show (CoreModels.core.slice.Slice.chunks_exact public_key (384#usize : Std.Usize))
          = .ok { cs := 384#usize, elements := public_key } from rfl]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [show (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice.enumerate
              { cs := (384#usize : Std.Usize), elements := public_key })
          = .ok iter0 from rfl]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [h_loop_eq]; simp only [Aeneas.Std.bind_tc_ok]
    show (do
        let result1 ← polynomial.PolynomialRingElement.reducing_from_i32_array
            portable_ops_inst (Aeneas.Std.Array.to_slice acc2) result
        let (result2, scratch1) ←
          invert_ntt.invert_ntt_montgomery K portable_ops_inst result1 scratch
        let (result3, scratch2) ←
          polynomial.PolynomialRingElement.add_message_error_reduce
            portable_ops_inst error_2 message result2 scratch1
        Result.ok (t_ent1, result3, scratch2, acc2))
        = Result.ok (t_ent1, result3, scratch2, acc2)
    rw [← h_s_def, h_result1_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_inv_eq]; simp only [Aeneas.Std.bind_tc_ok]
    show (do
        let (result3, scratch2) ←
          polynomial.PolynomialRingElement.add_message_error_reduce
            portable_ops_inst error_2 message result2 scratch1
        Result.ok (t_ent1, result3, scratch2, acc2))
        = Result.ok (t_ent1, result3, scratch2, acc2)
    rw [h_add_eq]; rfl
  · -- Spec witness `lift_poly result3`, then the per-lane `LaneMatches` bridge.
    refine ⟨lift_poly result3, ?_, ?_⟩
    -- Chain A/C/B/compose/glue/D′: prove hacspec spec = .ok (lift_poly result3).
    · show hacspec_ml_kem.matrix.compute_ring_element_v
          (lift_t_as_ntt_from_public_key public_key K) (lift_vec_slice r_as_ntt K)
          (lift_poly error_2) (lift_poly message) = .ok (lift_poly result3)
      unfold hacspec_ml_kem.matrix.compute_ring_element_v
      -- A: multiply_vectors = .ok (scaleZ 2285 (lift_poly result1)).
      have hA := compute_ring_element_v_acc_bridge hK public_key r_as_ntt r_arr
        acc1 acc2 h_acc1_zero h_r_arr h_r_bnd t_ent1 h_char
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
      -- D′: (add_polynomials (scaleZ 512 (lift_poly result2)) (lift_poly error_2)
      --       >>= add_polynomials · (lift_poly message))
      --      = .ok (add_message_error_reduce_pure (lift_poly error_2) (lift_poly message)
      --              (lift_poly result2)).
      rw [add_message_error_scaleZ_eq (lift_poly result2) (lift_poly error_2) (lift_poly message)
          (fun j hj => lift_poly_canon result2 j hj)]
      -- add_message_error_reduce_pure (lift_poly error_2) (lift_poly message) (lift_poly result2)
      --   = lift_poly result3.
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
info: 'libcrux_iot_ml_kem.Matrix.ComputeRingElementV.FC.compute_ring_element_v_fc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 deserialize_to_reduced_ring_element_fc]-/
#guard_msgs in
#print axioms compute_ring_element_v_fc

end libcrux_iot_ml_kem.Matrix.ComputeRingElementV.FC