/-
  # `Matrix/SpecDischarge.lean` — discharging the generated matrix `.spec`s

  The four L7 matrix top-level theorems are stated in `matrix.rs` as
  `#[requires]`/`#[ensures]`, so hax generates `matrix.<fn>.spec` (a wp Triple
  guarded by `<fn>.pre`). Each is discharged here from the hand-written FC
  theorem (`Matrix/Compute*/FC.lean`) via

  * the **pre-peel** lemmas in `Matrix/PreDecode.lean` (decoding the `Prop.and`
    of `from_bool`/`vec_bnd`/`poly_bnd` conjuncts into the FC's `natAbs` bounds),
    and

  * a **post-lift** rewriting the generated `.post` (extracted
    `matrix.lift_poly`/`matrix.lift_vec` + a Rust array `==`) through the
    `LiftAgree` bridges into the proof-side `= .ok (lift_poly …)` the FC proves.
-/
import LibcruxIotMlKem.Extraction
import LibcruxIotMlKem.Matrix.PreDecode
import LibcruxIotMlKem.Matrix.ComputeMessage.FC
import LibcruxIotMlKem.Matrix.ComputeVectorU.FC
import LibcruxIotMlKem.Matrix.ComputeRingElementV.FC
import LibcruxIotMlKem.Util.Shared

namespace libcrux_iot_ml_kem.Matrix.SpecDischarge

open CoreModels Aeneas Aeneas.Std RustM Std.Do
open libcrux_iot_ml_kem
open libcrux_iot_ml_kem.Spec
open libcrux_iot_ml_kem.Spec.Lift
open libcrux_iot_ml_kem.Matrix.LiftAgree
open libcrux_iot_ml_kem.Matrix.PreDecode

set_option linter.unusedVariables false

/-- Post-weakening for a `⌜True⌝`-pre Triple on a fixed computation. -/
private theorem triple_mono {α : Type} {x : RustM α} {P Q : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) (hpq : ∀ r, P r → Q r) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ Q r ⌝ ⦄ := by
  cases x with
  | ok v =>
      have hv : P v := by simpa [Std.Do.Triple, WP.wp, PredTrans.apply] using h
      simp only [Std.Do.Triple, WP.wp, PredTrans.apply]
      exact SPred.pure_intro (hpq v hv)
  | fail e => exfalso; simpa [Std.Do.Triple, WP.wp, PredTrans.apply] using h
  | div => exfalso; simpa [Std.Do.Triple, WP.wp, PredTrans.apply] using h

/-- The generated `.spec` post is `holds (do a ← <post>; pure (a = true))`; once
    `<post>` is shown to be `ok true` it holds. -/
private theorem holds_post_of_ok {x : RustM Bool} (h : x = .ok true) :
    RustM.holds (do let a ← x; pure (a = true)) := by
  subst h
  show RustM.holds (RustM.ok (true = true))
  simp [RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply]

/-- Decode `holds (do b ← x; ok (Q b))` into the successful value and its `Q`. -/
private theorem holds_bind_ok {α : Type} {x : RustM α} {Q : α → Prop}
    (h : RustM.holds (do let b ← x; ok (Q b))) : ∃ bv, x = .ok bv ∧ Q bv := by
  cases x with
  | ok bb =>
      exact ⟨bb, rfl, by simpa [RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply] using h⟩
  | fail e => exfalso; simp [RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply] at h
  | div => exfalso; simp [RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply] at h

private theorem holds_final {x : RustM Bool} {Q : Prop}
    (h : RustM.holds (do let b ← x; ok (Q ∧ b = true))) : Q ∧ x = .ok true := by
  cases x with
  | ok bb =>
      have hqb : Q ∧ bb = true := by
        simpa [RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply] using h
      exact ⟨hqb.1, by rw [hqb.2]⟩
  | fail e => exfalso; simp [RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply] at h
  | div => exfalso; simp [RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply] at h

set_option maxRecDepth 4000 in
theorem compute_message_spec_proof {K : Std.Usize}
    (v : polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector)
    (secret_as_ntt u_as_ntt : Std.Array
      (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector) K)
    (result : polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector)
    (scratch : vector.portable.vector_type.PortableVector)
    (accumulator : Std.Array Std.I32 256#usize) :
    matrix.compute_message.spec portable_ops_inst v secret_as_ntt u_as_ntt
      result scratch accumulator := by
  intro hpre
  simp only [matrix.compute_message.pre, matrix.vec_bnd, hax_lib.prop.forall,
    hax_lib.prop.Prop.from_bool, hax_lib.prop.Prop.and,
    core.convert.Into.Blanket.into, core.convert.From.Blanket.from,
    hax_lib.prop.Prop.Insts.CoreConvertFromBool, bind_tc_ok] at hpre
  obtain ⟨⟨⟨hK, hsec⟩, hu⟩, hpolyv⟩ := holds_final hpre
  have hKle : K.val ≤ 4 := by have h := of_decide_eq_true hK; scalar_tac
  have h_secret := vec_bnd_natAbs_4095 secret_as_ntt hsec
  have h_u := vec_bnd_natAbs_3328 u_as_ntt hu
  have h_v := poly_bnd_natAbs_3328 v hpolyv
  have hfc := ComputeMessage.FC.compute_message_fc v secret_as_ntt u_as_ntt result scratch
    accumulator hKle h_secret h_u h_v
  refine triple_mono hfc ?_
  intro res hP
  obtain ⟨rf, sc2, ac2⟩ := res
  obtain ⟨heq, _hbnd⟩ := hP
  -- FieldElement `==` is reflexive lane-wise, so the array `==` on `lift_poly rf`
  -- against itself is `ok true`.
  have hrefl : ∀ j : Nat, j < (256#usize : Std.Usize).val →
      hacspec_ml_kem.parameters.FieldElement.Insts.CoreCmpPartialEqFieldElement.eq
        ((lift_poly rf).val[j]!) ((lift_poly rf).val[j]!) = .ok true := by
    intro j hj
    simp [hacspec_ml_kem.parameters.FieldElement.Insts.CoreCmpPartialEqFieldElement.eq]
  have harr := PreDecode.array_eq_self
    hacspec_ml_kem.parameters.FieldElement.Insts.CoreCmpPartialEqFieldElement
    (lift_poly rf) hrefl
  have hpost : matrix.compute_message.post portable_ops_inst v secret_as_ntt u_as_ntt
      result scratch accumulator (rf, sc2, ac2) = .ok true := by
    simp only [matrix.compute_message.post, lift_poly_ok, lift_vec_ok, bind_tc_ok, heq]
    exact harr
  exact holds_post_of_ok hpost

set_option maxRecDepth 4000 in
theorem compute_As_plus_e_spec_proof {K : Std.Usize}
    (t_as_ntt : Std.Array
      (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector) K)
    (matrix_A : Slice
      (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector))
    (s_as_ntt error_as_ntt s_cache : Std.Array
      (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector) K)
    (accumulator : Std.Array Std.I32 256#usize) :
    matrix.compute_As_plus_e.spec portable_ops_inst t_as_ntt matrix_A s_as_ntt
      error_as_ntt s_cache accumulator := by
  intro hpre
  simp only [matrix.compute_As_plus_e.pre, matrix.matrix_slice_bnd, matrix.vec_bnd,
    matrix.acc_zero, hax_lib.prop.forall, hax_lib.prop.Prop.from_bool, hax_lib.prop.Prop.and,
    core.convert.Into.Blanket.into, core.convert.From.Blanket.from,
    hax_lib.prop.Prop.Insts.CoreConvertFromBool, bind_tc_ok] at hpre
  obtain ⟨bv, hbx, ⟨⟨⟨⟨hbv, hmat⟩, hs⟩, herr⟩, hacc⟩⟩ := holds_bind_ok hpre
  subst hbv
  -- decode the K-conditions ifchain (`= ok true`)
  by_cases hK0 : K > 0#usize
  · rw [if_pos hK0] at hbx
    by_cases hK4 : K ≤ 4#usize
    · rw [if_pos hK4] at hbx
      have hKv4 : K.val ≤ 4 := by scalar_tac
      have hKpos : 0 < K.val := by scalar_tac
      obtain ⟨kk, hkk_eq, hkk_val, _⟩ :=
        Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.UScalar.mul_bv_spec (x := K) (y := K)
          (by have : K.val * K.val ≤ 4 * 4 := Nat.mul_le_mul hKv4 hKv4
              show K.val * K.val ≤ Aeneas.Std.UScalar.max .Usize
              have hmx : (16 : Nat) ≤ Aeneas.Std.UScalar.max .Usize := by scalar_tac
              omega))
      rw [hkk_eq] at hbx
      simp only [CoreModels.core.slice.Slice.len,
        CoreModels.rust_primitives.slice.slice_length, bind_tc_ok] at hbx
      -- hbx : ok (decide (Std.Slice.len matrix_A = kk)) = ok true
      have hAlen : matrix_A.val.length = K.val * K.val := by
        have hd : (Std.Slice.len matrix_A) = kk := by
          have := (RustM.ok.injEq _ _).mp hbx; simpa using this
        have := congrArg Aeneas.Std.UScalar.val hd
        rw [Aeneas.Std.Slice.len_val, hkk_val] at this
        exact this
      -- FC hypotheses
      have h_matrix_bnd : ∀ k : Fin matrix_A.length, ∀ i j : Fin 16,
          ((matrix_A.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328 := by
        intro k i j
        exact matrix_slice_natAbs_3328 matrix_A (le_of_eq hAlen.symm) hmat k.val
          (by have hlt := k.isLt; have he : matrix_A.length = K.val * K.val := hAlen; omega)
          i.val i.isLt j.val j.isLt
      have h_s_bnd : ∀ k : Fin K.val, ∀ i j : Fin 16,
          ((s_as_ntt.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328 :=
        fun k i j => vec_bnd_natAbs_3328 s_as_ntt hs k.val k.isLt i.val i.isLt j.val j.isLt
      have h_error_bnd : ∀ k : Fin K.val, ∀ i j : Fin 16,
          ((error_as_ntt.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 29439 :=
        fun k i j => vec_bnd_natAbs_29439 error_as_ntt herr k.val k.isLt i.val i.isLt j.val j.isLt
      have h_acc_zero : ∀ n : Nat, n < 256 → accumulator.val[n]! = (0#i32 : Std.I32) :=
        acc_zero_of_holds accumulator hacc
      have h_acc_bnd : ∀ n : Fin 256,
          (accumulator.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30 := by
        intro n
        rw [h_acc_zero n.val n.isLt]
        have h0 : ((0#i32 : Std.I32)).val.natAbs = 0 := by decide
        rw [h0]; omega
      refine triple_mono (Matrix.ComputeAsPlusE.compute_As_plus_e_fc t_as_ntt matrix_A
        s_as_ntt error_as_ntt s_cache accumulator
        (show matrix_A.length = K.val * K.val from hAlen) hKv4
        h_matrix_bnd h_s_bnd h_error_bnd h_acc_bnd h_acc_zero hKpos) ?_
      intro res hP
      obtain ⟨tf, r2, r3⟩ := res
      -- lane-wise FieldElement reflexivity → inner (256) `==` → outer (K) `==`
      have hFErefl : ∀ (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize),
          ∀ jj : Nat, jj < (256#usize : Std.Usize).val →
            hacspec_ml_kem.parameters.FieldElement.Insts.CoreCmpPartialEqFieldElement.eq
              (p.val[jj]!) (p.val[jj]!) = .ok true := by
        intro p jj hjj
        simp [hacspec_ml_kem.parameters.FieldElement.Insts.CoreCmpPartialEqFieldElement.eq]
      have harr : CoreModels.core.Array.Insts.CoreCmpPartialEqArray.eq
          (CoreModels.core.Array.Insts.CoreCmpPartialEqArray 256#usize
            hacspec_ml_kem.parameters.FieldElement.Insts.CoreCmpPartialEqFieldElement)
          (lift_vec tf) (lift_vec tf) = .ok true :=
        PreDecode.array_eq_self _ (lift_vec tf)
          (fun k hk => PreDecode.array_eq_self _ ((lift_vec tf).val[k]!)
            (fun jj hjj => hFErefl _ jj hjj))
      have hpost : matrix.compute_As_plus_e.post portable_ops_inst t_as_ntt matrix_A s_as_ntt
          error_as_ntt s_cache accumulator (tf, r2, r3) = .ok true := by
        simp only [matrix.compute_As_plus_e.post,
          lift_matrix_from_slice_ok matrix_A (le_of_eq hAlen.symm),
          lift_vec_ok, bind_tc_ok, hP]
        exact harr
      exact holds_post_of_ok hpost
    · rw [if_neg hK4] at hbx; simp at hbx
  · rw [if_neg hK0] at hbx; simp at hbx

/-- An array equals the array rebuilt from its own indexed elements. Needed
    because `lift_matrix_from_seed = Spec.sample_matrix_A_pure` is OPAQUE, so the
    nested `from_fn` result can't be `rfl`'d against it (unlike the concrete
    `lift_matrix_from_slice`). -/
private theorem array_rebuild {T : Type} [Inhabited T] {K : Std.Usize}
    (a : Std.Array T K) :
    (⟨(List.range K.val).map (fun i => a.val[i]!), by simp⟩ : Std.Array T K) = a := by
  apply Subtype.ext
  show (List.range K.val).map (fun i => a.val[i]!) = a.val
  have hlen : a.val.length = K.val := a.property
  apply List.ext_getElem
  · simp [hlen]
  · intro n h1 h2
    rw [List.getElem_map, List.getElem_range, getElem!_pos a.val n (by omega)]

/-- Triple → `∃ ok`: extract the successful value and post from a `⌜True⌝`-pre
    Triple (A1 is such a Triple; `spec_imp_exists` only takes a `partialSpec`). -/
private theorem triple_exists_ok {α : Type} {x : RustM α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ v => ⌜ P v ⌝ ⦄) : ∃ v, x = .ok v ∧ P v := by
  cases x with
  | ok v => exact ⟨v, rfl, by simpa [Std.Do.Triple, WP.wp, PredTrans.apply] using h⟩
  | fail e => exfalso; simpa [Std.Do.Triple, WP.wp, PredTrans.apply] using h
  | div => exfalso; simpa [Std.Do.Triple, WP.wp, PredTrans.apply] using h

-- `lift_matrix_from_seed` agreement — the on-the-fly XOF-sampled matrix. Each
-- entry goes through the opaque `sample_matrix_entry`, characterized by the A1
-- axiom `Sampling.sample_matrix_entry_fc`. So this bridge is A1-dependent.
open libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.SliceSpecs in
set_option maxHeartbeats 1000000 in
theorem lift_matrix_from_seed_ok {K : Std.Usize} {Hasher : Type}
    (hasherInst : hash_functions.Hash Hasher)
    (seed : Slice Std.U8) (hseed : seed.length = 32) :
    matrix.lift_matrix_from_seed K portable_ops_inst hasherInst seed
      = .ok (lift_matrix_from_seed seed K) := by
  have hKlt : K.val < 2 ^ UScalarTy.Usize.numBits := K.bv.isLt
  unfold matrix.lift_matrix_from_seed
  rw [from_fn_pure_eq K
      (matrix.lift_matrix_from_seed.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayArrayFieldElement256K
        K portable_ops_inst hasherInst)
      seed (fun i => (lift_matrix_from_seed seed K).val[i]!)
      (by
        intro i hi
        have hival : (BitVec.ofNat UScalarTy.Usize.numBits i#uscalar : Std.Usize).val = i := by
          show (BitVec.ofNat UScalarTy.Usize.numBits i).toNat = i
          rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
        simp only
          [matrix.lift_matrix_from_seed.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayArrayFieldElement256K.call_mut]
        rw [from_fn_pure_eq K
            (matrix.lift_matrix_from_seed.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256
              K portable_ops_inst hasherInst)
            ((seed, (BitVec.ofNat UScalarTy.Usize.numBits i#uscalar : Std.Usize)) :
              matrix.lift_matrix_from_seed.closure.closure
                vector.portable.vector_type.PortableVector Hasher K)
            (fun j => (lift_matrix_from_seed seed K).val[i]!.val[j]!)
            (by
              intro j hj
              have hjval : (BitVec.ofNat UScalarTy.Usize.numBits j#uscalar : Std.Usize).val = j := by
                show (BitVec.ofNat UScalarTy.Usize.numBits j).toNat = j
                rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
              obtain ⟨z, hz_eq⟩ :
                  ∃ z, (polynomial.PolynomialRingElement.ZERO portable_ops_inst :
                    RustM (polynomial.PolynomialRingElement
                      vector.portable.vector_type.PortableVector)) = .ok z := ⟨_, rfl⟩
              obtain ⟨p, hp_eq, hp_lift, _⟩ := triple_exists_ok
                (Sampling.sample_matrix_entry_fc hasherInst z seed
                  (BitVec.ofNat UScalarTy.Usize.numBits i#uscalar : Std.Usize)
                  (BitVec.ofNat UScalarTy.Usize.numBits j#uscalar : Std.Usize) K
                  hseed (by rw [hival]; exact hi) (by rw [hjval]; exact hj))
              simp only
                [matrix.lift_matrix_from_seed.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut]
              show (do
                  let entry ← polynomial.PolynomialRingElement.ZERO portable_ops_inst
                  let entry1 ← matrix.sample_matrix_entry portable_ops_inst hasherInst entry seed
                    (BitVec.ofNat UScalarTy.Usize.numBits i#uscalar : Std.Usize)
                    (BitVec.ofNat UScalarTy.Usize.numBits j#uscalar : Std.Usize)
                  let a ← matrix.lift_poly portable_ops_inst entry1
                  ok (a, ((seed, (BitVec.ofNat UScalarTy.Usize.numBits i#uscalar : Std.Usize)) :
                    matrix.lift_matrix_from_seed.closure.closure
                      vector.portable.vector_type.PortableVector Hasher K)))
                = ok ((lift_matrix_from_seed seed K).val[i]!.val[j]!,
                    ((seed, (BitVec.ofNat UScalarTy.Usize.numBits i#uscalar : Std.Usize)) :
                      matrix.lift_matrix_from_seed.closure.closure
                        vector.portable.vector_type.PortableVector Hasher K))
              rw [hz_eq]; simp only [bind_tc_ok]
              rw [hp_eq]; simp only [bind_tc_ok]
              rw [lift_poly_ok p]; simp only [bind_tc_ok]
              rw [hp_lift, hival, hjval])]
        simp only [bind_tc_ok]
        rw [array_rebuild (lift_matrix_from_seed seed K).val[i]!])]
  exact congrArg RustM.ok (array_rebuild (lift_matrix_from_seed seed K))

set_option maxRecDepth 4000 in
theorem compute_vector_u_spec_proof {K : Std.Usize} {Hasher : Type}
    (hasherInst : hash_functions.Hash Hasher)
    (matrix_entry : polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector)
    (seed : Slice Std.U8)
    (r_as_ntt error_1 result : Slice
      (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector))
    (scratch : vector.portable.vector_type.PortableVector)
    (cache : Slice (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector))
    (accumulator : Std.Array Std.I32 256#usize) :
    matrix.compute_vector_u.spec K portable_ops_inst hasherInst matrix_entry seed
      r_as_ntt error_1 result scratch cache accumulator := by
  intro hpre
  simp only [matrix.compute_vector_u.pre, matrix.vec_slice_bnd, hax_lib.prop.forall,
    hax_lib.prop.Prop.from_bool, hax_lib.prop.Prop.and, core.convert.Into.Blanket.into,
    core.convert.From.Blanket.from, hax_lib.prop.Prop.Insts.CoreConvertFromBool, bind_tc_ok] at hpre
  obtain ⟨bv, hbx, ⟨⟨hbv, hr_bnd⟩, herr_bnd⟩⟩ := holds_bind_ok hpre
  subst hbv
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length,
    bind_tc_ok] at hbx
  by_cases hs : Std.Slice.len seed = 32#usize
  · by_cases hr : Std.Slice.len r_as_ntt = K
    · by_cases he : Std.Slice.len error_1 = K
      · by_cases hres : Std.Slice.len result = K
        · by_cases hca : Std.Slice.len cache = K
          · by_cases hkp : K > 0#usize
            · rw [if_pos hs, if_pos hr, if_pos he, if_pos hres, if_pos hca, if_pos hkp] at hbx
              have hK4 : K.val ≤ 4 := by have hd := (RustM.ok.injEq _ _).mp hbx; scalar_tac
              have hKpos : 1 ≤ K.val := by scalar_tac
              have h_seed_len : seed.length = 32 := by
                have := congrArg Aeneas.Std.UScalar.val hs
                rw [Aeneas.Std.Slice.len_val] at this; simpa using this
              have h_r_len : r_as_ntt.length = K.val := by
                have := congrArg Aeneas.Std.UScalar.val hr; rw [Aeneas.Std.Slice.len_val] at this; exact this
              have h_err_len : error_1.length = K.val := by
                have := congrArg Aeneas.Std.UScalar.val he; rw [Aeneas.Std.Slice.len_val] at this; exact this
              have h_result_len : result.length = K.val := by
                have := congrArg Aeneas.Std.UScalar.val hres; rw [Aeneas.Std.Slice.len_val] at this; exact this
              have h_cache_len : cache.length = K.val := by
                have := congrArg Aeneas.Std.UScalar.val hca; rw [Aeneas.Std.Slice.len_val] at this; exact this
              have h_r_bnd := vec_slice_natAbs_3328 r_as_ntt (le_of_eq h_r_len.symm) hr_bnd
              have h_err_bnd := vec_slice_natAbs_29439 error_1 (le_of_eq h_err_len.symm) herr_bnd
              refine triple_mono (ComputeVectorU.FC.compute_vector_u_fc K hasherInst matrix_entry
                seed r_as_ntt error_1 result scratch cache accumulator hK4 hKpos h_seed_len
                h_r_len h_err_len h_result_len h_cache_len
                (fun c hc a b => h_r_bnd c hc a.val a.isLt b.val b.isLt)
                (fun c hc a b => h_err_bnd c hc a.val a.isLt b.val b.isLt)) ?_
              intro res hP
              obtain ⟨me, rf, sc, cf, af⟩ := res
              obtain ⟨heq, h_rf_len, _h_cache, _h_cache_len⟩ := hP
              have hFErefl : ∀ (q : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize),
                  ∀ jj : Nat, jj < (256#usize : Std.Usize).val →
                    hacspec_ml_kem.parameters.FieldElement.Insts.CoreCmpPartialEqFieldElement.eq
                      (q.val[jj]!) (q.val[jj]!) = .ok true := by
                intro q jj hjj
                simp [hacspec_ml_kem.parameters.FieldElement.Insts.CoreCmpPartialEqFieldElement.eq]
              have harr : CoreModels.core.Array.Insts.CoreCmpPartialEqArray.eq
                  (CoreModels.core.Array.Insts.CoreCmpPartialEqArray 256#usize
                    hacspec_ml_kem.parameters.FieldElement.Insts.CoreCmpPartialEqFieldElement)
                  (lift_vec_slice rf K) (lift_vec_slice rf K) = .ok true :=
                PreDecode.array_eq_self _ (lift_vec_slice rf K)
                  (fun k hk => PreDecode.array_eq_self _ ((lift_vec_slice rf K).val[k]!)
                    (fun jj hjj => hFErefl _ jj hjj))
              have hpost : matrix.compute_vector_u.post K portable_ops_inst hasherInst matrix_entry
                  seed r_as_ntt error_1 result scratch cache accumulator (me, rf, sc, cf, af)
                  = .ok true := by
                simp only [matrix.compute_vector_u.post,
                  lift_matrix_from_seed_ok hasherInst seed h_seed_len,
                  lift_vec_slice_ok r_as_ntt (le_of_eq h_r_len.symm),
                  lift_vec_slice_ok error_1 (le_of_eq h_err_len.symm),
                  bind_tc_ok, heq]
                -- the post's `let (_, result_future, _, _, _) := (me,rf,…)` reduces defeq
                show (do
                    let a4 ← matrix.lift_vec_slice K portable_ops_inst rf
                    core.Array.Insts.CoreCmpPartialEqArray.eq
                      (core.Array.Insts.CoreCmpPartialEqArray 256#usize
                        hacspec_ml_kem.parameters.FieldElement.Insts.CoreCmpPartialEqFieldElement)
                      (lift_vec_slice rf K) a4) = .ok true
                rw [lift_vec_slice_ok rf (le_of_eq h_rf_len.symm)]
                simp only [bind_tc_ok]
                exact harr
              exact holds_post_of_ok hpost
            · exfalso; rw [if_pos hs, if_pos hr, if_pos he, if_pos hres, if_pos hca, if_neg hkp] at hbx; simp at hbx
          · exfalso; rw [if_pos hs, if_pos hr, if_pos he, if_pos hres, if_neg hca] at hbx; simp at hbx
        · exfalso; rw [if_pos hs, if_pos hr, if_pos he, if_neg hres] at hbx; simp at hbx
      · exfalso; rw [if_pos hs, if_pos hr, if_neg he] at hbx; simp at hbx
    · exfalso; rw [if_pos hs, if_neg hr] at hbx; simp at hbx
  · exfalso; rw [if_neg hs] at hbx; simp at hbx

-- ============================================================================
-- L7.2 ∘ L7.3 COMPOSED: `compute_u_and_v` (spec-only wrapper) — `compute_vector_u`
-- feeds its freshly-filled cache into `compute_ring_element_v`, so the composed
-- spec carries NO cache/accumulator precondition; the cache-correctness is
-- discharged internally from `compute_vector_u_fc`'s output. A1 (matrix sampling,
-- via the `u` step) + A2 (public-key deserialization, via the `v` step).
-- ============================================================================

/-- Peel one monadic bind under `holds`: the head must succeed, and the tail
    continues to hold at that value. -/
private theorem holds_bind_cont {α : Type} {x : RustM α} {rest : α → RustM Prop}
    (h : RustM.holds (x >>= rest)) : ∃ bv, x = .ok bv ∧ RustM.holds (rest bv) := by
  cases x with
  | ok bb => refine ⟨bb, rfl, ?_⟩; simpa only [bind_tc_ok] using h
  | fail e => exfalso; simp [RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply] at h
  | div => exfalso; simp [RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply] at h

/-- `holds (ok P)` is just `P`. -/
private theorem holds_ok {P : Prop} (h : RustM.holds (RustM.ok P)) : P := by
  simpa [RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply] using h

/-- A `⌜True⌝`-pre Triple on a literal `ok w` reduces to its postcondition at `w`. -/
private theorem triple_ok_intro {α : Type} {w : α} {P : α → Prop} (h : P w) :
    ⦃ ⌜ True ⌝ ⦄ (RustM.ok w) ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  simp only [Std.Do.Triple, WP.wp, PredTrans.apply]
  exact SPred.pure_intro h

/-- The shared-range subindex `pk[a..b]` in closed form: length `b-a`, and element
    `i` reads `pk[a+i]`. (Local copy of `SerializeFc`'s private lemma so this file
    need not import that module.) -/
private theorem slice_range_strict {T : Type} [Inhabited T]
    (s : Slice T) (a b : Std.Usize)
    (h0 : a.val < b.val) (h1 : b.val ≤ s.val.length) :
    ∃ ns : Slice T,
      CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
        (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) s
        ⟨a, b⟩ = .ok ns
      ∧ ns.val.length = b.val - a.val
      ∧ ∀ i : Nat, i < b.val - a.val → ns.val[i]! = s.val[a.val + i]! := by
  obtain ⟨ns, hns_eq, hns_val, -, -, -, hns_get⟩ :=
    Std.WP.spec_imp_exists (Std.WP.spec_of_partialSpec
      (Aeneas.Std.Slice.subslice_spec s ⟨a, b⟩)
      (by intro e; cases e <;> simp_all <;> omega) (by simp))
  have hlen : ns.val.length = b.val - a.val := by
    rw [hns_val]
    show (List.slice a.val b.val s.val).length = b.val - a.val
    rw [List.slice_length]; omega
  refine ⟨ns, ?_, hlen, ?_⟩
  · unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
      CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
      CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get
      CoreModels.rust_primitives.slice.slice_slice
      CoreModels.rust_primitives.slice.slice_length
    simp only [hns_eq, bind_tc_ok]
    split_ifs with hc1 hc2
    · rfl
    · exfalso; scalar_tac
    · exfalso; scalar_tac
  · intro i hi
    rw [hns_val]
    show (List.slice a.val b.val s.val)[i]! = _
    rw [List.getElem!_slice a.val b.val i s.val ⟨by omega, by omega⟩]

/-- The impl-side `BYTES_PER_RING_ELEMENT` constant reduces to `384`. -/
private theorem impl_bpre_local :
    (constants.BYTES_PER_RING_ELEMENT : RustM Std.Usize) = .ok (384#usize : Std.Usize) := by
  unfold constants.BYTES_PER_RING_ELEMENT constants.BITS_PER_RING_ELEMENT
    constants.COEFFICIENTS_IN_RING_ELEMENT
  rw [Util.Shared.usize_mul_lit (256#usize : Std.Usize) (12#usize : Std.Usize)
    (3072#usize : Std.Usize) (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  exact Util.Shared.usize_div_lit _ _ _ (by scalar_tac) (by scalar_tac)

-- `lift_t_as_ntt_from_public_key` agreement — the public-key deserialization.
-- Each 384-byte chunk goes through the opaque `deserialize_to_reduced_ring_element`,
-- characterized by the A2 axiom `Serialize.deserialize_to_reduced_ring_element_fc`.
open libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.Shared in
set_option maxHeartbeats 1000000 in
theorem lift_t_as_ntt_from_public_key_ok {K : Std.Usize}
    (public_key : Slice Std.U8) (hpk : public_key.length = K.val * 384) :
    matrix.lift_t_as_ntt_from_public_key K portable_ops_inst public_key
      = .ok (lift_t_as_ntt_from_public_key public_key K) := by
  have hKlt : K.val < 2 ^ UScalarTy.Usize.numBits := K.bv.isLt
  have hKmax : K.val * 384 ≤ Std.Usize.max := by rw [← hpk]; exact public_key.property
  unfold matrix.lift_t_as_ntt_from_public_key
  rw [from_fn_pure_eq K
      (matrix.lift_t_as_ntt_from_public_key.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256
        K portable_ops_inst)
      public_key (fun k => (lift_t_as_ntt_from_public_key public_key K).val[k]!)
      (by
        intro k hk
        have hkval : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k := by
          show (BitVec.ofNat UScalarTy.Usize.numBits k).toNat = k
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        have h384 : (384#usize : Std.Usize).val = 384 := rfl
        have hk384' : k * 384 + 384 ≤ K.val * 384 := by
          have h : (k + 1) * 384 ≤ K.val * 384 := Nat.mul_le_mul_right _ (by omega)
          calc k * 384 + 384 = (k + 1) * 384 := by ring
            _ ≤ K.val * 384 := h
        obtain ⟨z, hz_eq⟩ :
            ∃ z, (polynomial.PolynomialRingElement.ZERO portable_ops_inst :
              RustM (polynomial.PolynomialRingElement
                vector.portable.vector_type.PortableVector)) = .ok z := ⟨_, rfl⟩
        obtain ⟨st, hst_eq, hst_val⟩ := usize_mul_ok_e
          (⟨BitVec.ofNat _ k⟩ : Std.Usize) (384#usize : Std.Usize)
          (by rw [hkval]; exact le_trans (Nat.le_add_right _ 384) (le_trans hk384' hKmax))
        rw [hkval, h384] at hst_val
        have h1 : (1#usize : Std.Usize).val = 1 := rfl
        obtain ⟨sp, hsp_eq, hsp_val⟩ := usize_add_ok_e
          (⟨BitVec.ofNat _ k⟩ : Std.Usize) (1#usize : Std.Usize)
          (by rw [hkval]; omega)
        rw [hkval, h1] at hsp_val
        obtain ⟨en, hen_eq, hen_val⟩ := usize_mul_ok_e sp (384#usize : Std.Usize)
          (by rw [hsp_val, h384]
              calc (k + 1) * 384 = k * 384 + 384 := by ring
                _ ≤ K.val * 384 := hk384'
                _ ≤ Std.Usize.max := hKmax)
        rw [hsp_val, h384] at hen_val
        have hen_val' : en.val = k * 384 + 384 := by rw [hen_val]; ring
        obtain ⟨ns, hns_eq, hns_len, hns_get⟩ := slice_range_strict public_key st en
          (by rw [hst_val, hen_val']; omega)
          (by rw [hen_val']
              show k * 384 + 384 ≤ public_key.val.length
              rw [show public_key.val.length = K.val * 384 from hpk]; exact hk384')
        have hns_len' : ns.val.length = 384 := by rw [hns_len, hen_val', hst_val]; omega
        have h_chunk_eq : ∀ ℓ : Nat, ℓ < 384 →
            ns.val[ℓ]! = public_key.val[(⟨BitVec.ofNat _ k⟩ : Std.Usize).val * 384 + ℓ]! := by
          intro ℓ hℓ
          have hg := hns_get ℓ (by rw [hen_val', hst_val]; omega)
          rw [hg, hst_val, hkval]
        obtain ⟨p, hp_eq, hp_lift, _hp_bnd⟩ := triple_exists_ok
          (Serialize.deserialize_to_reduced_ring_element_fc public_key K z
            (⟨BitVec.ofNat _ k⟩ : Std.Usize) hpk (by rw [hkval]; exact hk)
            ns hns_len' h_chunk_eq)
        rw [hkval] at hp_lift
        simp only
          [matrix.lift_t_as_ntt_from_public_key.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut]
        show (do
            let re ← polynomial.PolynomialRingElement.ZERO portable_ops_inst
            let i ← constants.BYTES_PER_RING_ELEMENT
            let i1 ← (⟨BitVec.ofNat _ k⟩ : Std.Usize) * i
            let i2 ← (⟨BitVec.ofNat _ k⟩ : Std.Usize) + 1#usize
            let i3 ← i2 * i
            let s ← core.Slice.Insts.CoreOpsIndexIndex.index
              (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
              public_key { start := i1, «end» := i3 }
            let s1 ← libcrux_secrets.SharedASlice.Insts.Libcrux_secretsTraitsClassifyRefSharedASlice.classify_ref
              libcrux_secrets.U8.Insts.Libcrux_secretsTraitsScalar s
            let re1 ← serialize.deserialize_to_reduced_ring_element portable_ops_inst s1 re
            let a ← matrix.lift_poly portable_ops_inst re1
            ok (a, public_key))
          = ok ((lift_t_as_ntt_from_public_key public_key K).val[k]!, public_key)
        rw [hz_eq]; simp only [bind_tc_ok]
        rw [impl_bpre_local]; simp only [bind_tc_ok]
        rw [hst_eq]; simp only [bind_tc_ok]
        rw [hsp_eq]; simp only [bind_tc_ok]
        rw [hen_eq]; simp only [bind_tc_ok]
        rw [hns_eq]; simp only [bind_tc_ok]
        rw [show (libcrux_secrets.SharedASlice.Insts.Libcrux_secretsTraitsClassifyRefSharedASlice.classify_ref
              libcrux_secrets.U8.Insts.Libcrux_secretsTraitsScalar ns : RustM (Slice Std.U8))
            = .ok ns from rfl]
        simp only [bind_tc_ok]
        rw [hp_eq]; simp only [bind_tc_ok]
        rw [lift_poly_ok p]; simp only [bind_tc_ok]
        rw [hp_lift])]
  exact congrArg RustM.ok (array_rebuild (lift_t_as_ntt_from_public_key public_key K))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem compute_u_and_v_spec_proof {K : Std.Usize} {Hasher : Type}
    (hasherInst : hash_functions.Hash Hasher)
    (seed public_key : Slice Std.U8)
    (r_as_ntt error_1 : Slice
      (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector))
    (error_2 message matrix_entry t_as_ntt_entry :
      polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector)
    (result_u : Slice
      (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector))
    (result_v : polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector)
    (scratch : vector.portable.vector_type.PortableVector)
    (cache : Slice
      (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector))
    (accumulator : Std.Array Std.I32 256#usize) :
    matrix.compute_u_and_v.spec K portable_ops_inst hasherInst seed public_key
      r_as_ntt error_1 error_2 message matrix_entry t_as_ntt_entry result_u result_v
      scratch cache accumulator := by
  intro hpre
  simp only [matrix.compute_u_and_v.pre, matrix.vec_slice_bnd, hax_lib.prop.forall,
    hax_lib.prop.Prop.from_bool, hax_lib.prop.Prop.and, core.convert.Into.Blanket.into,
    core.convert.From.Blanket.from, hax_lib.prop.Prop.Insts.CoreConvertFromBool, bind_tc_ok] at hpre
  -- pre = do b ← C; be2 ← poly_bnd e2; bmsg ← poly_bnd msg; ok ((((b=true ∧ R)∧E1)∧be2=true)∧bmsg=true)
  obtain ⟨bv, hbx, hcont⟩ := holds_bind_cont hpre
  obtain ⟨be2, hbe2, hcont2⟩ := holds_bind_cont hcont
  obtain ⟨bmsg, hbmsg, hcont3⟩ := holds_bind_cont hcont2
  obtain ⟨⟨⟨⟨hbv, hr_bnd⟩, herr_bnd⟩, hbe2t⟩, hbmt⟩ := holds_ok hcont3
  subst hbv
  -- poly bounds for error_2 / message.
  rw [hbe2t] at hbe2
  rw [hbmt] at hbmsg
  have h_e2_bnd := poly_bnd_natAbs_3328 error_2 hbe2
  have h_msg_bnd := poly_bnd_natAbs_3328 message hbmsg
  -- decode the length/K ifchain from `C = .ok true`.
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length,
    bind_tc_ok] at hbx
  by_cases hkp : K > 0#usize
  · rw [if_pos hkp] at hbx
    by_cases hK4 : K ≤ 4#usize
    · rw [if_pos hK4] at hbx
      have hK4v : K.val ≤ 4 := by scalar_tac
      have hKpos : 1 ≤ K.val := by scalar_tac
      -- reduce BYTES_PER_RING_ELEMENT and the pk multiplication.
      obtain ⟨pkprod, hpkprod_eq, hpkprod_val⟩ := Util.Shared.usize_mul_ok_e
        (384#usize : Std.Usize) K
        (by have h384 : (384#usize : Std.Usize).val = 384 := rfl
            rw [h384]; have hmx : (1536 : Nat) ≤ Std.Usize.max := by scalar_tac
            calc 384 * K.val ≤ 384 * 4 := by exact Nat.mul_le_mul_left _ hK4v
              _ ≤ Std.Usize.max := by omega)
      rw [impl_bpre_local] at hbx
      simp only [bind_tc_ok] at hbx
      rw [hpkprod_eq] at hbx
      simp only [bind_tc_ok] at hbx
      by_cases hs : Std.Slice.len seed = 32#usize
      · rw [if_pos hs] at hbx
        by_cases hpkc : Std.Slice.len public_key = pkprod
        · rw [if_pos hpkc] at hbx
          by_cases hr : Std.Slice.len r_as_ntt = K
          · rw [if_pos hr] at hbx
            by_cases he : Std.Slice.len error_1 = K
            · rw [if_pos he] at hbx
              by_cases hres : Std.Slice.len result_u = K
              · rw [if_pos hres] at hbx
                -- hbx : ok (decide (Std.Slice.len cache = K)) = ok true
                have hca : Std.Slice.len cache = K := by
                  have hd := (RustM.ok.injEq _ _).mp hbx; simpa using hd
                -- length facts.
                have h_seed_len : seed.length = 32 := by
                  have := congrArg Aeneas.Std.UScalar.val hs
                  rw [Aeneas.Std.Slice.len_val] at this; simpa using this
                have h_pk_len : public_key.length = K.val * 384 := by
                  have hv := congrArg Aeneas.Std.UScalar.val hpkc
                  rw [Aeneas.Std.Slice.len_val] at hv
                  rw [hv, hpkprod_val]
                  have h384 : (384#usize : Std.Usize).val = 384 := rfl
                  rw [h384]; ring
                have h_r_len : r_as_ntt.length = K.val := by
                  have := congrArg Aeneas.Std.UScalar.val hr
                  rw [Aeneas.Std.Slice.len_val] at this; exact this
                have h_err_len : error_1.length = K.val := by
                  have := congrArg Aeneas.Std.UScalar.val he
                  rw [Aeneas.Std.Slice.len_val] at this; exact this
                have h_result_len : result_u.length = K.val := by
                  have := congrArg Aeneas.Std.UScalar.val hres
                  rw [Aeneas.Std.Slice.len_val] at this; exact this
                have h_cache_len : cache.length = K.val := by
                  have := congrArg Aeneas.Std.UScalar.val hca
                  rw [Aeneas.Std.Slice.len_val] at this; exact this
                have h_r_bnd := vec_slice_natAbs_3328 r_as_ntt (le_of_eq h_r_len.symm) hr_bnd
                have h_err_bnd := vec_slice_natAbs_29439 error_1 (le_of_eq h_err_len.symm) herr_bnd
                -- Step A: run compute_vector_u; get its cache-correctness + length.
                obtain ⟨⟨me1, ru1, sc1, cf1, ac1⟩, h_cvu_eq, _h_u, _h_ru_len, h_cache_char, h_cf1_len⟩ :=
                  triple_exists_ok (ComputeVectorU.FC.compute_vector_u_fc K hasherInst matrix_entry
                    seed r_as_ntt error_1 result_u scratch cache accumulator hK4v hKpos h_seed_len
                    h_r_len h_err_len h_result_len h_cache_len
                    (fun c hc a b => h_r_bnd c hc a.val a.isLt b.val b.isLt)
                    (fun c hc a b => h_err_bnd c hc a.val a.isLt b.val b.isLt))
                -- Step B: run compute_ring_element_v on that cache.
                obtain ⟨⟨te1, rv1, sc2, ac2⟩, h_crv_eq, h_v_correct⟩ :=
                  triple_exists_ok (ComputeRingElementV.FC.compute_ring_element_v_fc K public_key
                    t_as_ntt_entry r_as_ntt error_2 message result_v sc1 cf1 ac1 hK4v h_pk_len
                    h_r_len h_cf1_len
                    (fun c hc a b => h_r_bnd c hc a.val a.isLt b.val b.isLt)
                    h_cache_char
                    (fun chunk hchunk ℓ hℓ => h_e2_bnd chunk hchunk ℓ hℓ)
                    (fun chunk hchunk ℓ hℓ => h_msg_bnd chunk hchunk ℓ hℓ))
                -- The whole wrapper reduces to a single `ok`.
                have h_uv_eq : matrix.compute_u_and_v K portable_ops_inst hasherInst seed
                    public_key r_as_ntt error_1 error_2 message matrix_entry t_as_ntt_entry
                    result_u result_v scratch cache accumulator
                    = .ok (me1, te1, ru1, rv1, sc2, cf1, ac2) := by
                  unfold matrix.compute_u_and_v
                  rw [h_cvu_eq]; simp only [bind_tc_ok]
                  show (do
                      let (t_as_ntt_entry1, result_v1, scratch2, accumulator2) ←
                        matrix.compute_ring_element_v K portable_ops_inst public_key
                          t_as_ntt_entry r_as_ntt error_2 message result_v sc1 cf1 ac1
                      ok (me1, t_as_ntt_entry1, ru1, result_v1, scratch2, cf1, accumulator2))
                    = .ok (me1, te1, ru1, rv1, sc2, cf1, ac2)
                  rw [h_crv_eq]; simp only [bind_tc_ok]
                rw [h_uv_eq]
                apply triple_ok_intro
                -- post: v-correctness as a reflexive array `==` (result_v is a Polynomial).
                have hrefl : ∀ jj : Nat, jj < (256#usize : Std.Usize).val →
                    hacspec_ml_kem.parameters.FieldElement.Insts.CoreCmpPartialEqFieldElement.eq
                      ((lift_poly rv1).val[jj]!) ((lift_poly rv1).val[jj]!) = .ok true := by
                  intro jj hjj
                  simp [hacspec_ml_kem.parameters.FieldElement.Insts.CoreCmpPartialEqFieldElement.eq]
                have harr := PreDecode.array_eq_self
                  hacspec_ml_kem.parameters.FieldElement.Insts.CoreCmpPartialEqFieldElement
                  (lift_poly rv1) hrefl
                have hpost : matrix.compute_u_and_v.post K portable_ops_inst hasherInst seed
                    public_key r_as_ntt error_1 error_2 message matrix_entry t_as_ntt_entry
                    result_u result_v scratch cache accumulator
                    (me1, te1, ru1, rv1, sc2, cf1, ac2) = .ok true := by
                  simp only [matrix.compute_u_and_v.post,
                    lift_t_as_ntt_from_public_key_ok public_key h_pk_len,
                    lift_vec_slice_ok r_as_ntt (le_of_eq h_r_len.symm),
                    lift_poly_ok, bind_tc_ok, h_v_correct]
                  exact harr
                exact holds_post_of_ok hpost
              · exfalso; rw [if_neg hres] at hbx; simp at hbx
            · exfalso; rw [if_neg he] at hbx; simp at hbx
          · exfalso; rw [if_neg hr] at hbx; simp at hbx
        · exfalso; rw [if_neg hpkc] at hbx; simp at hbx
      · exfalso; rw [if_neg hs] at hbx; simp at hbx
    · exfalso; rw [if_neg hK4] at hbx; simp at hbx
  · exfalso; rw [if_neg hkp] at hbx; simp at hbx
