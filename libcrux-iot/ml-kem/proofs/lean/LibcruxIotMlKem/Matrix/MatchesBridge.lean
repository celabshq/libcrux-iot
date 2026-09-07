import LibcruxIotMlKem.Extraction
import LibcruxIotMlKem.Matrix.LiftAgree
import LibcruxIotMlKem.Matrix.PreDecode
namespace libcrux_iot_ml_kem.Matrix.MatchesBridge
open CoreModels Aeneas Aeneas.Std RustM Std.Do
open libcrux_iot_ml_kem
open libcrux_iot_ml_kem.Spec.Lift
open libcrux_iot_ml_kem.Matrix.LiftAgree
open libcrux_iot_ml_kem.Util.SliceSpecs

private abbrev PolyArr := Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize

private theorem holds_ok_prop {P : Prop} (h : P) : (RustM.ok P).holds := by
  simp only [RustM.holds, Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.apply,
             Std.Do.PostCond.noThrow]
  exact Std.Do.SPred.pure_intro h

/-- `lane_matches x (lift_fe x) = ok true` whenever `|x| ≤ 1664`: the residue
    comparison is `from_i16 x == from_i16 x`, reflexively true. -/
private theorem lane_matches_lift_self (x : Std.I16) (h : x.val.natAbs ≤ 1664) :
    matrix.lane_matches x (lift_fe x) = .ok true := by
  have hlo : (-1664)#i16 ≤ x := by scalar_tac
  have hhi : x ≤ 1664#i16 := by scalar_tac
  simp only [matrix.lane_matches, hlo, hhi, if_true, from_i16_eq x, Aeneas.Std.bind_tc_ok,
             hacspec_ml_kem.parameters.FieldElement.Insts.CoreCmpPartialEqFieldElement.eq]
  simp

theorem poly_matches_self
    (re : polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector)
    (h_bnd : ∀ l : Nat, l < 256 →
        ((re.coefficients.val[l / 16]!).elements.val[l % 16]!).val.natAbs ≤ 1664) :
    (matrix.poly_matches portable_ops_inst re (lift_poly re)).holds := by
  have key : ∀ t : Std.Usize,
      (do
        let u ← matrix.poly_matches.closure.Insts.CoreOpsFunctionFnTupleUsizeBool.call
                  portable_ops_inst (re, lift_poly re) t
        core.convert.Into.Blanket.into hax_lib.prop.Prop.Insts.CoreConvertFromBool u).holds := by
    intro t
    simp only [matrix.poly_matches.closure.Insts.CoreOpsFunctionFnTupleUsizeBool.call,
               core.convert.Into.Blanket.into, hax_lib.prop.Prop.Insts.CoreConvertFromBool]
    by_cases ht : t < 256#usize
    · have hlt : t.val < 256 := by scalar_tac
      simp only [reduceIte, ht]
      change (do
          let b ← (do
            let i ← t / 16#usize
            let t_1 ← re.coefficients.index_usize i
            let a1 ← vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsRepr.repr t_1
            let i1 ← t % 16#usize
            let i2 ← a1.index_usize i1
            let fe ← (lift_poly re).index_usize t
            matrix.lane_matches i2 fe)
          ok (b = true)).holds
      -- div: qi = t / 16
      obtain ⟨qi, hqi_eq, hqi_val⟩ :=
        Aeneas.Std.UScalar.div_spec t (y := 16#usize) (by decide)
      have hqi16 : qi.val = t.val / 16 := by rw [hqi_val]; rfl
      rw [hqi_eq]; simp only [Aeneas.Std.bind_tc_ok]
      -- index into coefficients
      have hcoef_len : re.coefficients.val.length = 16 := re.coefficients.property
      obtain ⟨tc, htc_eq, htc_val⟩ :=
        Array.index_usize_exists re.coefficients qi (by rw [hqi16, hcoef_len]; omega)
      rw [htc_eq]; simp only [Aeneas.Std.bind_tc_ok]
      -- repr on the portable instance is the identity on `.elements`
      rw [repr_eq tc]; simp only [Aeneas.Std.bind_tc_ok]
      -- rem: ri = t % 16
      obtain ⟨ri, hri_eq, hri_val⟩ :=
        Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.UScalar.rem_spec t (y := 16#usize) (by decide))
      have hri16 : ri.val = t.val % 16 := by rw [hri_val]; rfl
      rw [hri_eq]; simp only [Aeneas.Std.bind_tc_ok]
      -- index into elements
      have hel_len : tc.elements.val.length = 16 := tc.elements.property
      obtain ⟨i2, hi2_eq, hi2_val⟩ :=
        Array.index_usize_exists tc.elements ri (by rw [hri16, hel_len]; omega)
      rw [hi2_eq]; simp only [Aeneas.Std.bind_tc_ok]
      -- index into `lift_poly re`
      have hlp_len : (lift_poly re).val.length = 256 := (lift_poly re).property
      obtain ⟨fe, hfe_eq, hfe_val⟩ :=
        Array.index_usize_exists (lift_poly re) t (by rw [hlp_len]; exact hlt)
      rw [hfe_eq]; simp only [Aeneas.Std.bind_tc_ok]
      -- reconcile indices to the `getElem!` form used by `h_bnd` / `lift_poly_getElem`
      have htc' : tc = re.coefficients.val[t.val / 16]! := by
        rw [htc_val]
        conv_rhs => rw [getElem!_pos re.coefficients.val (t.val / 16) (by rw [hcoef_len]; omega)]
        congr 1
      have hi2' : i2 = tc.elements.val[t.val % 16]! := by
        rw [hi2_val]
        conv_rhs => rw [getElem!_pos tc.elements.val (t.val % 16) (by rw [hel_len]; omega)]
        congr 1
      have hfe' : fe = (lift_poly re).val[t.val]! := by
        rw [hfe_val]
        conv_rhs => rw [getElem!_pos (lift_poly re).val t.val (by rw [hlp_len]; exact hlt)]
      -- the spec lane `fe` is `lift_fe` of the impl lane `i2`
      have hfe_lift : fe = lift_fe i2 := by
        rw [hfe', hi2', htc', lift_poly_getElem re t.val hlt]
      -- the impl lane satisfies the tight bound (from `h_bnd`)
      have hi2_bnd : i2.val.natAbs ≤ 1664 := by
        rw [hi2', htc']; exact h_bnd t.val hlt
      rw [hfe_lift, lane_matches_lift_self i2 hi2_bnd]
      simp only [Aeneas.Std.bind_tc_ok]
      exact holds_ok_prop (by trivial)
    · simp only [reduceIte, ht]
      exact holds_ok_prop (by trivial)
  unfold matrix.poly_matches hax_lib.prop.forall
  simp only [RustM.holds, Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.apply, Std.Do.PostCond.noThrow]
  exact Std.Do.SPred.pure_intro key

/-- `Slice.index_usize` in range, as a plain equation (local copy). -/
private theorem slice_index_ok {T : Type} [Inhabited T] (s : Aeneas.Std.Slice T)
    (i : Std.Usize) (h : i.val < s.val.length) :
    Aeneas.Std.Slice.index_usize s i = .ok (s.val[i.val]!) := by
  unfold Aeneas.Std.Slice.index_usize
  rw [Aeneas.Std.Slice.getElem?_Usize_eq, List.getElem?_eq_getElem h,
    List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- Vector analogue of `poly_matches_self`. Generic over the spec: given a
    per-lane bound and a per-lane equality `spec[r][ℓ] = lift_fe (impl lane)`,
    `vec_matches` holds. The discharges instantiate `spec` with `lift_vec` /
    `lift_vec_slice` of the result and supply the equality from the lift getters. -/
theorem vec_matches_self {K : Std.Usize}
    (sv : Slice (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector))
    (spec : Std.Array PolyArr K)
    (hKmax : K.val * 256 ≤ Aeneas.Std.Usize.max)
    (hlen : sv.val.length = K.val)
    (hmatch : ∀ r : Nat, r < K.val → ∀ l : Nat, l < 256 →
        ((sv.val[r]!.coefficients.val[l / 16]!).elements.val[l % 16]!).val.natAbs ≤ 1664 ∧
        (spec.val[r]!).val[l]!
          = lift_fe ((sv.val[r]!.coefficients.val[l / 16]!).elements.val[l % 16]!)) :
    (matrix.vec_matches portable_ops_inst sv spec).holds := by
  have key : ∀ t : Std.Usize,
      (do
        let u ← matrix.vec_matches.closure.Insts.CoreOpsFunctionFnTupleUsizeBool.call portable_ops_inst (sv, spec) t
        core.convert.Into.Blanket.into hax_lib.prop.Prop.Insts.CoreConvertFromBool u).holds := by
    intro t
    simp only [matrix.vec_matches.closure.Insts.CoreOpsFunctionFnTupleUsizeBool.call,
               core.convert.Into.Blanket.into, hax_lib.prop.Prop.Insts.CoreConvertFromBool]
    change (do
        let b ← (do
          let i ← K * 256#usize
          if t < i then (do
            let i1 ← t / 256#usize
            let i2 ← t % 256#usize
            let i3 ← i2 / 16#usize
            let pre ← Slice.index_usize sv i1
            let tt ← pre.coefficients.index_usize i3
            let a1 ← vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsRepr.repr tt
            let i4 ← i2 % 16#usize
            let i5 ← a1.index_usize i4
            let a2 ← spec.index_usize i1
            let fe ← a2.index_usize i2
            matrix.lane_matches i5 fe)
          else ok true)
        ok (b = true)).holds
    -- resolve the `K * 256` guard
    obtain ⟨km, hkm_eq, hkm_val⟩ :=
      Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.UScalar.mul_spec (x := K) (y := 256#usize) (by scalar_tac))
    rw [hkm_eq]; simp only [Aeneas.Std.bind_tc_ok]
    have hkm256 : km.val = K.val * 256 := by rw [hkm_val]; rfl
    by_cases ht : t < km
    · rw [if_pos ht]
      have hlt : t.val < K.val * 256 := by rw [← hkm256]; exact ht
      -- i1 = t / 256  (row)
      obtain ⟨i1, hi1_eq, hi1_val⟩ := Aeneas.Std.UScalar.div_spec t (y := 256#usize) (by decide)
      have hi1v : i1.val = t.val / 256 := by rw [hi1_val]; rfl
      rw [hi1_eq]; simp only [Aeneas.Std.bind_tc_ok]
      -- i2 = t % 256  (lane within poly)
      obtain ⟨i2, hi2_eq, hi2_val⟩ :=
        Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.UScalar.rem_spec t (y := 256#usize) (by decide))
      have hi2v : i2.val = t.val % 256 := by rw [hi2_val]; rfl
      rw [hi2_eq]; simp only [Aeneas.Std.bind_tc_ok]
      -- i3 = i2 / 16  (chunk)
      obtain ⟨i3, hi3_eq, hi3_val⟩ := Aeneas.Std.UScalar.div_spec i2 (y := 16#usize) (by decide)
      have hi3v : i3.val = t.val % 256 / 16 := by rw [hi3_val, hi2v]; rfl
      rw [hi3_eq]; simp only [Aeneas.Std.bind_tc_ok]
      -- pre = sv[i1]
      obtain ⟨pre, hpre_eq, hpre_val⟩ :=
        (fun h => ⟨sv.val[i1.val]!, slice_index_ok sv i1 h, rfl⟩ :
          i1.val < sv.val.length →
            ∃ pre, Slice.index_usize sv i1 = .ok pre ∧ pre = sv.val[i1.val]!)
          (by rw [hlen, hi1v]; omega)
      rw [hpre_eq]; simp only [Aeneas.Std.bind_tc_ok]
      -- tt = pre.coefficients[i3]
      have hcoef_len : pre.coefficients.val.length = 16 := pre.coefficients.property
      obtain ⟨tt, htt_eq, htt_val⟩ :=
        Array.index_usize_exists pre.coefficients i3 (by rw [hi3v, hcoef_len]; omega)
      rw [htt_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [repr_eq tt]; simp only [Aeneas.Std.bind_tc_ok]
      -- i4 = i2 % 16
      obtain ⟨i4, hi4_eq, hi4_val⟩ :=
        Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.UScalar.rem_spec i2 (y := 16#usize) (by decide))
      have hi4v : i4.val = t.val % 256 % 16 := by rw [hi4_val, hi2v]; rfl
      rw [hi4_eq]; simp only [Aeneas.Std.bind_tc_ok]
      -- i5 = tt.elements[i4]
      have hel_len : tt.elements.val.length = 16 := tt.elements.property
      obtain ⟨i5, hi5_eq, hi5_val⟩ :=
        Array.index_usize_exists tt.elements i4 (by rw [hi4v, hel_len]; omega)
      rw [hi5_eq]; simp only [Aeneas.Std.bind_tc_ok]
      -- a2 = spec[i1]
      have hspec_len : spec.val.length = K.val := spec.property
      obtain ⟨a2, ha2_eq, ha2_val⟩ :=
        Array.index_usize_exists spec i1 (by rw [hspec_len, hi1v]; omega)
      rw [ha2_eq]; simp only [Aeneas.Std.bind_tc_ok]
      -- fe = a2[i2]
      have ha2_len : a2.val.length = 256 := a2.property
      obtain ⟨fe, hfe_eq, hfe_val⟩ :=
        Array.index_usize_exists a2 i2 (by rw [ha2_len, hi2v]; omega)
      rw [hfe_eq]; simp only [Aeneas.Std.bind_tc_ok]
      -- reconcile to the flat (row, lane) getElem! form
      have hr : t.val / 256 < K.val := by omega
      have hlmod : t.val % 256 < 256 := Nat.mod_lt _ (by omega)
      -- reconcile each obtained value to the `getElem!` (row, lane) form, one level at a time
      have hpre' : pre = sv.val[t.val / 256]! := by rw [hpre_val, hi1v]
      have htt' : tt = pre.coefficients.val[t.val % 256 / 16]! := by
        rw [htt_val]; simp only [← hi3v]
        rw [getElem!_pos pre.coefficients.val i3.val (by rw [hcoef_len, hi3v]; omega)]
      have hi5' : i5 = tt.elements.val[t.val % 256 % 16]! := by
        rw [hi5_val]; simp only [← hi4v]
        rw [getElem!_pos tt.elements.val i4.val (by rw [hel_len, hi4v]; omega)]
      have ha2' : a2 = spec.val[t.val / 256]! := by
        rw [ha2_val]; simp only [← hi1v]
        rw [getElem!_pos spec.val i1.val (by rw [hspec_len, hi1v]; omega)]
      have hfe' : fe = a2.val[t.val % 256]! := by
        rw [hfe_val]; simp only [← hi2v]
        rw [getElem!_pos a2.val i2.val (by rw [ha2_len, hi2v]; omega)]
      have hi5'' : i5 = (sv.val[t.val / 256]!.coefficients.val[t.val % 256 / 16]!).elements.val[t.val % 256 % 16]! := by
        rw [hi5', htt', hpre']
      have hfe'' : fe = (spec.val[t.val / 256]!).val[t.val % 256]! := by rw [hfe', ha2']
      obtain ⟨hbnd, heq⟩ := hmatch (t.val / 256) hr (t.val % 256) hlmod
      have hfe_lift : fe = lift_fe i5 := by rw [hfe'', heq, hi5'']
      have hi5_bnd : i5.val.natAbs ≤ 1664 := by rw [hi5'']; exact hbnd
      rw [hfe_lift, lane_matches_lift_self i5 hi5_bnd]
      simp only [Aeneas.Std.bind_tc_ok]
      exact holds_ok_prop (by trivial)
    · rw [if_neg ht]
      simp only [Aeneas.Std.bind_tc_ok]
      exact holds_ok_prop (by trivial)
  unfold matrix.vec_matches hax_lib.prop.forall
  simp only [RustM.holds, Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.apply, Std.Do.PostCond.noThrow]
  exact Std.Do.SPred.pure_intro key

end libcrux_iot_ml_kem.Matrix.MatchesBridge
