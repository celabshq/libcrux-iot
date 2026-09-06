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
              obtain ⟨heq, h_rf_len⟩ := hP
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
