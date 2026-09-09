/-
  # `Matrix/LiftAgree.lean` — extracted spec-only lifts = proof-side lifts

  The four matrix top-level theorems are stated in the Rust source (`matrix.rs`)
  through spec-only lift functions (`matrix.lift_poly`, `matrix.lift_vec`,
  `matrix.lift_matrix_from_slice`). Their generated `.post`s reference the
  EXTRACTED lifts, while the FC theorems (`Spec/Lift.lean`) use the proof-side
  `Spec.Lift.{lift_poly,lift_vec,...}`. This file bridges the two so the
  generated `<fn>.spec` discharges from the FC theorem.
-/
import LibcruxIotMlKem.Spec.Lift
import LibcruxIotMlKem.Util.CreateI

namespace libcrux_iot_ml_kem.Matrix.LiftAgree

open CoreModels Aeneas Aeneas.Std RustM Std.Do
open libcrux_iot_ml_kem
open libcrux_iot_ml_kem.Spec
open libcrux_iot_ml_kem.Spec.Lift
open libcrux_iot_ml_kem.Util.CreateI

set_option linter.unusedVariables false

/-! ## `from_i16` = `lift_fe`

    The extracted `hacspec_ml_kem.parameters.FieldElement.from_i16 v` computes
    the canonical residue `((v tmod q) + q) tmod q` (in `[0, q)`) and wraps it
    as a `U16`. That is exactly `lift_fe v = feOfZMod (v.val : ZMod 3329)`. -/

/-- The residue chain `((v tmod q) + q) tmod q` equals the Euclidean residue
    `v emod q` (`q = 3329`). `Int.tmod_eq_emod` rewrites each `tmod` to
    `emod - (if …)`; `omega` (which understands `%` and literal `∣`) finishes. -/
private theorem residue_chain (v : Int) :
    Int.tmod (Int.tmod v 3329 + 3329) 3329 = v % 3329 := by
  simp only [Int.tmod_eq_emod]
  have h0 := Int.emod_nonneg v (show (3329:Int) ≠ 0 by norm_num)
  have h1 := Int.emod_lt_of_pos v (show (0:Int) < 3329 by norm_num)
  split_ifs <;> omega

set_option maxHeartbeats 1000000 in
theorem from_i16_eq (v : Std.I16) :
    hacspec_ml_kem.parameters.FieldElement.from_i16 v = .ok (lift_fe v) := by
  unfold hacspec_ml_kem.parameters.FieldElement.from_i16
  rw [show (Aeneas.Std.lift (Aeneas.Std.UScalar.hcast .I32 hacspec_ml_kem.parameters.FIELD_MODULUS)
        : RustM Std.I32) = .ok (3329#i32 : Std.I32) from by
      simp only [hacspec_ml_kem.parameters.FIELD_MODULUS]; rfl]
  simp only [bind_tc_ok]
  -- i = (v : I32).
  obtain ⟨w, hw_eq, hw_val⟩ : ∃ w : Std.I32,
      Aeneas.Std.lift (Aeneas.Std.IScalar.cast .I32 v) = .ok w ∧ w.val = v.val := by
    have hb : Aeneas.Std.IScalar.min .I32 ≤ v.val ∧ v.val ≤ Aeneas.Std.IScalar.max .I32 := by
      have h1 := Aeneas.Std.IScalar.hBounds v
      simp only [IScalar.min_IScalarTy_I32_eq, IScalar.max_IScalarTy_I32_eq, Aeneas.Std.I32.min,
        Aeneas.Std.I32.max, Aeneas.Std.I32.numBits, IScalarTy.I32_numBits_eq,
        IScalarTy.I16_numBits_eq] at *
      omega
    obtain ⟨w, hweq, hwval⟩ :=
      Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.cast_inBounds_spec .I32 v hb)
    exact ⟨w, hweq, hwval⟩
  rw [hw_eq]; simp only [bind_tc_ok]
  have h3329_ne : ((3329#i32 : Std.I32)).val ≠ 0 := by decide
  obtain ⟨r1, hr1_eq, hr1_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Aeneas.Std.IScalar.rem_spec w (y := (3329#i32 : Std.I32)) h3329_ne
        (by rintro ⟨-, hb⟩; exact absurd hb (by decide)))
  rw [hr1_eq]; simp only [bind_tc_ok]
  have hr1v : r1.val = Int.tmod w.val 3329 := by rw [hr1_val]; rfl
  have hr1_bnd : -3328 ≤ r1.val ∧ r1.val ≤ 3328 := by
    rw [hr1v, Int.tmod_eq_emod]
    have h0 := Int.emod_nonneg w.val (show (3329:Int) ≠ 0 by norm_num)
    have h1 := Int.emod_lt_of_pos w.val (show (0:Int) < 3329 by norm_num)
    split_ifs <;> omega
  obtain ⟨r2, hr2_eq, hr2_val, _⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Aeneas.Std.IScalar.add_bv_spec (x := r1) (y := (3329#i32 : Std.I32))
        (by have h := (show ((3329#i32 : Std.I32)).val = 3329 from by decide)
            simp only [IScalar.min_IScalarTy_I32_eq, Aeneas.Std.I32.min, Aeneas.Std.I32.numBits,
              IScalarTy.I32_numBits_eq]; omega)
        (by have h := (show ((3329#i32 : Std.I32)).val = 3329 from by decide)
            simp only [IScalar.max_IScalarTy_I32_eq, Aeneas.Std.I32.max, Aeneas.Std.I32.numBits,
              IScalarTy.I32_numBits_eq]; omega))
  rw [hr2_eq]; simp only [bind_tc_ok]
  have hr2v : r2.val = r1.val + 3329 := by rw [hr2_val]; simp
  obtain ⟨r3, hr3_eq, hr3_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Aeneas.Std.IScalar.rem_spec r2 (y := (3329#i32 : Std.I32)) h3329_ne
        (by rintro ⟨-, hb⟩; exact absurd hb (by decide)))
  rw [hr3_eq]; simp only [bind_tc_ok]
  have hr3v : r3.val = v.val % 3329 := by
    rw [hr3_val, show ((3329#i32 : Std.I32)).val = 3329 from by decide,
        hr2v, hr1v, hw_val]
    exact residue_chain v.val
  have hr3_range : 0 ≤ r3.val ∧ r3.val < 3329 := by
    rw [hr3v]; exact ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  -- r = (r3 : U16), value preserved.
  rw [show (Aeneas.Std.lift (Aeneas.Std.IScalar.hcast .U16 r3) : RustM Std.U16)
        = .ok (Aeneas.Std.IScalar.hcast .U16 r3) from rfl]
  simp only [bind_tc_ok]
  unfold hacspec_ml_kem.parameters.FieldElement.new
  -- both FieldElements: compare `.val` (U16), which compare via Nat value.
  refine congrArg RustM.ok ?_
  unfold lift_fe feOfZMod i16_to_spec_fe_plain
  refine congrArg (fun u => (⟨u⟩ : hacspec_ml_kem.parameters.FieldElement)) ?_
  apply Aeneas.Std.UScalar.eq_of_val_eq
  -- both `.val` (Nat): LHS = hcast value = r3.val.toNat (r3 ∈ [0,3329) ⊂ [0,2^16));
  -- RHS = (v.val : ZMod 3329).val = (v.val % 3329).toNat = r3.val.toNat.
  have hlhs : (Aeneas.Std.IScalar.hcast .U16 r3 : Std.U16).val = r3.val.toNat := by
    rw [Aeneas.Std.IScalar.hcast_val_eq, UScalarTy.U16_numBits_eq]
    congr 1
    apply Int.emod_eq_of_lt hr3_range.1
    have : r3.val < 3329 := hr3_range.2; omega
  have hrhs : ((⟨BitVec.ofNat 16 ((v.val : ZMod 3329)).val⟩ : Std.U16)).val
      = (v.val : ZMod 3329).val := by
    show (BitVec.ofNat 16 ((v.val : ZMod 3329)).val).toNat = _
    rw [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have := ZMod.val_lt (n := 3329) ((v.val : ZMod 3329)); omega
  rw [hlhs, hrhs, hr3v]
  have hzi := ZMod.val_intCast (n := 3329) (v.val)
  omega

/-! ## `repr` = `.elements`

    The extracted portable `Repr::repr` writes `self.elements` (declassified,
    identity) into a fresh 16-element array via `to_i16_array` -- an
    `index_mut [0,16)` + `copy_from_slice`. The net result is `self.elements`. -/

open libcrux_iot_ml_kem.Util.SliceSpecs in
set_option maxHeartbeats 2000000 in
theorem repr_eq (self : vector.portable.vector_type.PortableVector) :
    vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsRepr.repr self
      = .ok self.elements := by
  unfold vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsRepr.repr
    vector.portable.vector_type.to_i16_array
  set out := Aeneas.Std.Array.repeat 16#usize (0#i16 : Std.I16) with hout
  have hlen16 : (Aeneas.Std.Array.to_slice out).val.length = 16 := by
    rw [Aeneas.Std.Array.val_to_slice, hout, Aeneas.Std.Array.repeat_val]; simp
  -- the sub-slice [0,16) of the len-16 slice.
  obtain ⟨ns, hns_eq, hns_val⟩ := Slice.subslice_le_eq (Aeneas.Std.Array.to_slice out)
      ⟨0#usize, 16#usize⟩ (by simp) (by rw [hlen16]; simp)
  have hns_len : ns.val.length = 16 := by
    rw [hns_val]; simp only [List.slice_length]; rw [hlen16]; simp
  have hsrc_len : (Aeneas.Std.Array.to_slice self.elements).val.length = 16 := by
    rw [Aeneas.Std.Array.val_to_slice]; exact self.elements.property
  have hmassert : (Std.Slice.len (Aeneas.Std.Array.to_slice out)).val = 16 := by
    rw [Aeneas.Std.Slice.len_val]; exact hlen16
  -- plain `simp` on the goal reduces the destructuring `let`s, len, massert,
  -- index_mut, declassify, copy_from_slice, and `from_slice`.
  simp [Aeneas.Std.Array.to_slice_mut,
    CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
    CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    CoreModels.rust_primitives.slice.slice_slice_mut,
    show libcrux_secrets.traits.Declassify.Blanket.declassify self.elements
        = .ok self.elements from rfl,
    show CoreModels.core.slice.Slice.len (Aeneas.Std.Array.to_slice out)
        = .ok (Std.Slice.len (Aeneas.Std.Array.to_slice out)) from by
      simp [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length],
    hns_eq,
    core_models_slice_Slice_copy_from_slice_eq CoreModels.core.I16.Insts.CoreMarkerCopy
      ns (Aeneas.Std.Array.to_slice self.elements) (by rw [hns_len, hsrc_len]) (by intro x; rfl),
    Aeneas.Std.massert, hmassert,
    Aeneas.Std.Array.from_slice,
    Aeneas.Std.Array.val_to_slice,
    Aeneas.Std.lift, bind_tc_ok]
  -- ⟨out.setSlice! 0 self.elements.val, _⟩ = self.elements: full-length replace.
  apply Subtype.ext
  show (out.val).setSlice! 0 (self.elements.val) = self.elements.val
  have hle : self.elements.val.length = out.val.length := by
    rw [self.elements.property, hout, Aeneas.Std.Array.repeat_val]; simp
  simp [List.setSlice!, hle]

/-! ## `lift_poly` / `lift_vec` agreement

    The extracted `matrix.lift_poly` builds a 256-array via `core.array.from_fn`
    over a pure closure that reads `Vector::repr(re.coefficients[k/16])[k%16]` and
    lifts it with `FieldElement::from_i16`. On the portable instance `repr` is the
    identity on `.elements` (`repr_eq`) and `from_i16 = lift_fe` (`from_i16_eq`),
    so the whole builder equals the proof-side `Spec.lift_poly`. -/

open libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.SliceSpecs in
theorem lift_poly_ok
    (re : polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector) :
    matrix.lift_poly portable_ops_inst re = .ok (lift_poly re) := by
  unfold matrix.lift_poly
  rw [from_fn_pure_eq 256#usize _ re
      (fun k => lift_fe ((re.coefficients.val[k / 16]!).elements.val[k % 16]!))
      (by
        intro k hk
        have hk' : k < 256 := hk
        simp only
          [matrix.lift_poly.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut]
        have hpow : (2:Nat)^16 ≤ 2 ^ UScalarTy.Usize.numBits := by
          rw [UScalarTy.Usize_numBits_eq]
          exact Nat.pow_le_pow_right (by norm_num)
            (by cases System.Platform.numBits_eq <;> omega)
        have hxval : (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize).val = k := by
          show (BitVec.ofNat UScalarTy.Usize.numBits k).toNat = k
          rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
        -- div: qi = k / 16
        obtain ⟨qi, hqi_eq, hqi_val⟩ :=
          Aeneas.Std.UScalar.div_spec
            (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize)
            (y := 16#usize) (by decide)
        have hqi16 : qi.val = k / 16 := by rw [hqi_val, hxval]; rfl
        rw [hqi_eq]; simp only [bind_tc_ok]
        -- index into coefficients
        have hcoef_len : re.coefficients.val.length = 16 := re.coefficients.property
        obtain ⟨t, ht_eq, ht_val⟩ :=
          Array.index_usize_exists re.coefficients qi (by rw [hqi16, hcoef_len]; omega)
        rw [ht_eq]; simp only [bind_tc_ok]
        -- repr on the portable instance is the identity on `.elements`
        rw [repr_eq t]; simp only [bind_tc_ok]
        -- rem: ri = k % 16
        obtain ⟨ri, hri_eq, hri_val⟩ :=
          Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.UScalar.rem_spec
            (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize)
            (y := 16#usize) (by decide))
        have hri16 : ri.val = k % 16 := by rw [hri_val, hxval]; rfl
        rw [hri_eq]; simp only [bind_tc_ok]
        -- index into elements
        have hel_len : t.elements.val.length = 16 := t.elements.property
        obtain ⟨i2, hi2_eq, hi2_val⟩ :=
          Array.index_usize_exists t.elements ri (by rw [hri16, hel_len]; omega)
        rw [hi2_eq]; simp only [bind_tc_ok]
        -- from_i16 is lift_fe
        rw [from_i16_eq i2]
        -- reconcile the two index expressions (`getElem'h` = `getElem!`); `congr 1`
        -- discharges the index equality from `hqi16`/`hri16` in context.
        have ht' : t = re.coefficients.val[k / 16]! := by
          rw [ht_val]
          conv_rhs => rw [getElem!_pos re.coefficients.val (k / 16) (by rw [hcoef_len]; omega)]
          congr 1
        have hi2' : i2 = t.elements.val[k % 16]! := by
          rw [hi2_val]
          conv_rhs => rw [getElem!_pos t.elements.val (k % 16) (by rw [hel_len]; omega)]
          congr 1
        simp only [bind_tc_ok]
        rw [hi2', ht'])]
  unfold lift_poly
  rfl

open libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.SliceSpecs in
theorem lift_vec_ok {K : Std.Usize}
    (v : Std.Array
          (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector) K) :
    matrix.lift_vec portable_ops_inst v = .ok (lift_vec v) := by
  unfold matrix.lift_vec
  rw [from_fn_pure_eq K _ v (fun k => lift_poly v.val[k]!)
      (by
        intro k hk
        have hk' : k < K.val := hk
        have hvlen : v.val.length = K.val := v.property
        have hKlt : K.val < 2 ^ UScalarTy.Usize.numBits := K.bv.isLt
        simp only
          [matrix.lift_vec.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut]
        have hxval : (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize).val = k := by
          show (BitVec.ofNat UScalarTy.Usize.numBits k).toNat = k
          rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
        -- index v[k]
        obtain ⟨pre, hpre_eq, hpre_val⟩ :=
          Array.index_usize_exists v
            (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize)
            (by rw [hxval, hvlen]; omega)
        rw [hpre_eq]; simp only [bind_tc_ok]
        -- the extracted per-chunk lift_poly = proof-side lift_poly
        rw [lift_poly_ok pre]; simp only [bind_tc_ok]
        have hpre' : pre = v.val[k]! := by
          rw [hpre_val]
          conv_rhs => rw [getElem!_pos v.val k (by rw [hvlen]; omega)]
          congr 1
        rw [hpre'])]
  -- `(range K).map (fun k => lift_poly v[k]!)` = `v.val.map lift_poly`
  unfold lift_vec
  refine congrArg RustM.ok (Subtype.ext ?_)
  show (List.range K.val).map (fun k => lift_poly v.val[k]!) = v.val.map lift_poly
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, v.property]
  · intro n h1 h2
    rw [List.getElem_map, List.getElem_range, List.getElem_map,
        getElem!_pos v.val n (by simp only [List.length_map] at h2; exact h2)]

/-- `Slice.index_usize` in range as a plain equation (Slice mirror of
    `Array.index_usize_exists`). -/
private theorem slice_index_ok {T : Type} [Inhabited T] (s : Slice T)
    (i : Std.Usize) (h : i.val < s.val.length) :
    Aeneas.Std.Slice.index_usize s i = .ok (s.val[i.val]!) := by
  unfold Aeneas.Std.Slice.index_usize
  rw [Aeneas.Std.Slice.getElem?_Usize_eq, List.getElem?_eq_getElem h,
    List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

-- `lift_matrix_from_slice` agreement: the nested `core.array.from_fn` builder
-- (outer column `j`, inner row `i`, reading `slice[i*K + j]`) equals the
-- proof-side `Spec.Lift.lift_matrix_from_slice`, given the slice holds `K*K`
-- ring elements.
open libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.SliceSpecs in
set_option maxHeartbeats 1000000 in
theorem lift_matrix_from_slice_ok {K : Std.Usize}
    (slice : Slice
      (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector))
    (hlen : K.val * K.val ≤ slice.val.length) :
    matrix.lift_matrix_from_slice K portable_ops_inst slice
      = .ok (lift_matrix_from_slice slice K) := by
  have hKlt : K.val < 2 ^ UScalarTy.Usize.numBits := K.bv.isLt
  have hslen : slice.val.length ≤ Aeneas.Std.UScalar.max .Usize := by
    have := slice.property; scalar_tac
  unfold matrix.lift_matrix_from_slice
  rw [from_fn_pure_eq K _ slice
      (fun j => (⟨(List.range K.val).map
          (fun i => lift_poly slice.val[i * K.val + j]!), by simp⟩ :
          Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K))
      (by
        intro j hj
        have hjval : (BitVec.ofNat UScalarTy.Usize.numBits j#uscalar : Std.Usize).val = j := by
          show (BitVec.ofNat UScalarTy.Usize.numBits j).toNat = j
          rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
        simp only
          [matrix.lift_matrix_from_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayArrayFieldElement256K.call_mut]
        rw [from_fn_pure_eq K
            (matrix.lift_matrix_from_slice.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256
              K portable_ops_inst)
            ((slice, (BitVec.ofNat UScalarTy.Usize.numBits j#uscalar : Std.Usize)) :
              matrix.lift_matrix_from_slice.closure.closure
                vector.portable.vector_type.PortableVector K)
            (fun i => lift_poly slice.val[i * K.val + j]!)
            (by
              intro i hi
              have hival : (BitVec.ofNat UScalarTy.Usize.numBits i#uscalar : Std.Usize).val = i := by
                show (BitVec.ofNat UScalarTy.Usize.numBits i).toNat = i
                rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
              have hKK : ∀ a : Nat, a < K.val → a * K.val + j < K.val * K.val := by
                intro a ha
                have hpos : 1 ≤ K.val := by omega
                have h1 : a * K.val ≤ (K.val - 1) * K.val := Nat.mul_le_mul_right _ (by omega)
                have h2 : (K.val - 1) * K.val + K.val = K.val * K.val := by
                  rw [← Nat.succ_mul]; congr 1; omega
                omega
              have hij : i * K.val + j < slice.val.length := by have := hKK i hi; omega
              -- i1 = i * K
              obtain ⟨m, hm_eq, hm_val, _⟩ :=
                Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.UScalar.mul_bv_spec
                  (x := (BitVec.ofNat UScalarTy.Usize.numBits i#uscalar : Std.Usize)) (y := K)
                  (by rw [hival]
                      show i * K.val ≤ Aeneas.Std.UScalar.max .Usize
                      have := hKK i hi; omega))
              have hm16 : m.val = i * K.val := by rw [hm_val, hival]
              -- i2 = i1 + j
              obtain ⟨s2, hs2_eq, hs2_val, _⟩ :=
                Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.UScalar.add_bv_spec
                  (x := m) (y := (BitVec.ofNat UScalarTy.Usize.numBits j#uscalar : Std.Usize))
                  (by rw [hm16, hjval]
                      show i * K.val + j ≤ Aeneas.Std.UScalar.max .Usize
                      have := hKK i hi; omega))
              have hs2v : s2.val = i * K.val + j := by rw [hs2_val, hm16, hjval]
              simp only
                [matrix.lift_matrix_from_slice.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut]
              -- eliminate the `let (s, i0) := (slice, ⟨..j⟩)` destructure (defeq)
              show (do
                  let i1 ← (BitVec.ofNat UScalarTy.Usize.numBits i#uscalar : Std.Usize) * K
                  let i2 ← i1 + (BitVec.ofNat UScalarTy.Usize.numBits j#uscalar : Std.Usize)
                  let pre ← Aeneas.Std.Slice.index_usize slice i2
                  let a ← matrix.lift_poly portable_ops_inst pre
                  ok (a, ((slice, (BitVec.ofNat UScalarTy.Usize.numBits j#uscalar : Std.Usize)) :
                    matrix.lift_matrix_from_slice.closure.closure
                      vector.portable.vector_type.PortableVector K)))
                = ok (lift_poly slice.val[i * K.val + j]!,
                    ((slice, (BitVec.ofNat UScalarTy.Usize.numBits j#uscalar : Std.Usize)) :
                      matrix.lift_matrix_from_slice.closure.closure
                        vector.portable.vector_type.PortableVector K))
              rw [hm_eq]; simp only [bind_tc_ok]
              rw [hs2_eq]; simp only [bind_tc_ok]
              rw [slice_index_ok slice s2 (by rw [hs2v]; exact hij)]
              simp only [bind_tc_ok]
              rw [lift_poly_ok (slice.val[s2.val]!)]
              have hpre' : slice.val[s2.val]! = slice.val[i * K.val + j]! := by rw [hs2v]
              rw [hpre']; simp only [bind_tc_ok])]
        rfl)]
  unfold lift_matrix_from_slice
  rfl

-- `lift_vec_slice` agreement (the `Slice` analogue of `lift_vec_ok`).
open libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.SliceSpecs in
theorem lift_vec_slice_ok {K : Std.Usize}
    (v : Slice (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector))
    (hlen : K.val ≤ v.val.length) :
    matrix.lift_vec_slice K portable_ops_inst v = .ok (lift_vec_slice v K) := by
  have hslen : v.val.length ≤ Aeneas.Std.UScalar.max .Usize := by
    have := v.property; scalar_tac
  unfold matrix.lift_vec_slice
  rw [from_fn_pure_eq K _ v (fun i => lift_poly v.val[i]!)
      (by
        intro i hi
        have hival : (BitVec.ofNat UScalarTy.Usize.numBits i#uscalar : Std.Usize).val = i := by
          show (BitVec.ofNat UScalarTy.Usize.numBits i).toNat = i
          rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt
          have : K.val < 2 ^ UScalarTy.Usize.numBits := K.bv.isLt
          omega
        simp only
          [matrix.lift_vec_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut]
        rw [slice_index_ok v (BitVec.ofNat UScalarTy.Usize.numBits i#uscalar : Std.Usize)
            (by rw [hival]; omega)]
        simp only [bind_tc_ok]
        rw [lift_poly_ok (v.val[(BitVec.ofNat UScalarTy.Usize.numBits i#uscalar : Std.Usize).val]!)]
        have hpre' : v.val[(BitVec.ofNat UScalarTy.Usize.numBits i#uscalar : Std.Usize).val]!
            = v.val[i]! := by rw [hival]
        rw [hpre']; simp only [bind_tc_ok])]
  unfold lift_vec_slice
  rfl
