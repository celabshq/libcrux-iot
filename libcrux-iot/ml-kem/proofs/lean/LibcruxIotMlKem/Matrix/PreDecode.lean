/-
  # `Matrix/PreDecode.lean` — discharging the generated matrix `.spec`s

  The four L7 matrix top-level theorems are stated in `matrix.rs` as
  `#[requires]`/`#[ensures]`, so hax generates `matrix.<fn>.spec` (a wp Triple
  guarded by `<fn>.pre`). Each is discharged here from the hand-written FC
  theorem (`Matrix/Compute*/FC.lean`) by

  * **pre-peel**: decoding `<fn>.pre.holds` — a `Prop.and` of `from_bool`,
    `vec_bnd` (a `hax_lib::prop::forall` + if-then-else) and `poly_bnd`
    conjuncts — into the per-lane `natAbs` bounds and `K ≤ 4` the FC wants; and

  * **post-lift**: rewriting the generated `.post` (which uses the EXTRACTED
    `matrix.lift_poly`/`matrix.lift_vec` and a Rust array `==`) through the
    `LiftAgree` bridges into the proof-side `= .ok (lift_poly …)` the FC proves.
-/
import LibcruxIotMlKem.Matrix.LiftAgree


namespace libcrux_iot_ml_kem.Matrix.PreDecode

open CoreModels Aeneas Aeneas.Std RustM Std.Do
open libcrux_iot_ml_kem
open libcrux_iot_ml_kem.Spec
open libcrux_iot_ml_kem.Spec.Lift
open libcrux_iot_ml_kem.Matrix.LiftAgree

set_option linter.unusedVariables false

/-! ## Ported wp/`holds` bridges (mirroring `Verification/ProofObligations.lean`) -/

/-- An in-range `Array.index_usize` as a plain equation. -/
private theorem array_index_ok {α : Type} [Inhabited α] {n : Std.Usize}
    (v : Aeneas.Std.Array α n) (i : Std.Usize) (h : i.val < v.val.length) :
    v.index_usize i = .ok (v.val[i.val]!) := by
  unfold Aeneas.Std.Array.index_usize
  rw [Aeneas.Std.Array.getElem?_Usize_eq, List.getElem?_eq_getElem h,
    List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- One link of an unrolled `&&`: `true` result forces both sides. -/
private theorem bind_if_ok_true {x rest : RustM Bool}
    (h : (do let b ← x; if b then rest else RustM.ok false) = RustM.ok true) :
    x = .ok true ∧ rest = .ok true := by
  cases x with
  | ok b =>
      cases b with
      | true => exact ⟨rfl, by simpa using h⟩
      | false => exfalso; simp at h
  | fail e => exfalso; simp at h
  | div => exfalso; simp at h

/-! ## Lane / chunk / poly bound decode -/

/-- `lane_bnd x b = ok true` gives `|x| ≤ B` when `b = B` and `-.b = -B`. -/
private theorem lane_bnd_true {x b negb : Std.I16} {B : Nat}
    (hneg : (-. b : RustM Std.I16) = .ok negb)
    (hnegv : negb.val = -(B : Int)) (hboundv : b.val = (B : Int))
    (h : matrix.lane_bnd x b = .ok true) : x.val.natAbs ≤ B := by
  simp only [matrix.lane_bnd, hneg, Aeneas.Std.bind_tc_ok] at h
  by_cases h1 : negb ≤ x
  · by_cases h2 : x ≤ b
    · have hlo : negb.val ≤ x.val := by scalar_tac
      have hhi : x.val ≤ b.val := by scalar_tac
      rw [hnegv] at hlo; rw [hboundv] at hhi
      omega
    · exfalso; rw [if_pos h1] at h; simp [h2] at h
  · exfalso; rw [if_neg h1] at h; simp at h

/-- `-.b = ok (-B)` and `b = B` for the two literal bounds, via `lane_bnd_true`. -/
private theorem lane_bnd_le_3328 {x : Std.I16}
    (h : matrix.lane_bnd x 3328#i16 = .ok true) : x.val.natAbs ≤ 3328 :=
  lane_bnd_true (negb := (-3328)#i16) (B := 3328)
    (by rfl) (by rfl) (by rfl) h

private theorem lane_bnd_le_4095 {x : Std.I16}
    (h : matrix.lane_bnd x 4095#i16 = .ok true) : x.val.natAbs ≤ 4095 :=
  lane_bnd_true (negb := (-4095)#i16) (B := 4095)
    (by rfl) (by rfl) (by rfl) h

private theorem lane_bnd_le_29439 {x : Std.I16}
    (h : matrix.lane_bnd x 29439#i16 = .ok true) : x.val.natAbs ≤ 29439 :=
  lane_bnd_true (negb := (-29439)#i16) (B := 29439)
    (by rfl) (by rfl) (by rfl) h

/-- `chunk_bnd c b = ok true` gives every one of the sixteen `lane_bnd`s. On the
    portable instance `repr c = ok c.elements` (`repr_eq`), so the nested-`if`
    ranges over `lane_bnd (c.elements[i]!) b`. Mirrors `elements_abs_le_lanes`. -/
private theorem chunk_bnd_lanes
    (c : vector.portable.vector_type.PortableVector) (b : Std.I16)
    (h : matrix.chunk_bnd portable_ops_inst c b = .ok true) :
    ∀ i : Nat, i < 16 → matrix.lane_bnd (c.elements.val[i]!) b = .ok true := by
  have hlen : c.elements.val.length = 16 := c.elements.property
  simp only [matrix.chunk_bnd, repr_eq c, Aeneas.Std.bind_tc_ok,
    array_index_ok c.elements 0#usize (by simp [hlen]),
    array_index_ok c.elements 1#usize (by simp [hlen]),
    array_index_ok c.elements 2#usize (by simp [hlen]),
    array_index_ok c.elements 3#usize (by simp [hlen]),
    array_index_ok c.elements 4#usize (by simp [hlen]),
    array_index_ok c.elements 5#usize (by simp [hlen]),
    array_index_ok c.elements 6#usize (by simp [hlen]),
    array_index_ok c.elements 7#usize (by simp [hlen]),
    array_index_ok c.elements 8#usize (by simp [hlen]),
    array_index_ok c.elements 9#usize (by simp [hlen]),
    array_index_ok c.elements 10#usize (by simp [hlen]),
    array_index_ok c.elements 11#usize (by simp [hlen]),
    array_index_ok c.elements 12#usize (by simp [hlen]),
    array_index_ok c.elements 13#usize (by simp [hlen]),
    array_index_ok c.elements 14#usize (by simp [hlen]),
    array_index_ok c.elements 15#usize (by simp [hlen])] at h
  obtain ⟨h0, h⟩ := bind_if_ok_true h
  obtain ⟨h1, h⟩ := bind_if_ok_true h
  obtain ⟨h2, h⟩ := bind_if_ok_true h
  obtain ⟨h3, h⟩ := bind_if_ok_true h
  obtain ⟨h4, h⟩ := bind_if_ok_true h
  obtain ⟨h5, h⟩ := bind_if_ok_true h
  obtain ⟨h6, h⟩ := bind_if_ok_true h
  obtain ⟨h7, h⟩ := bind_if_ok_true h
  obtain ⟨h8, h⟩ := bind_if_ok_true h
  obtain ⟨h9, h⟩ := bind_if_ok_true h
  obtain ⟨h10, h⟩ := bind_if_ok_true h
  obtain ⟨h11, h⟩ := bind_if_ok_true h
  obtain ⟨h12, h⟩ := bind_if_ok_true h
  obtain ⟨h13, h⟩ := bind_if_ok_true h
  obtain ⟨h14, h15⟩ := bind_if_ok_true h
  intro i hi
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · exact absurd hi (by omega)

/-- `poly_bnd re b = ok true` gives every one of the sixteen `chunk_bnd`s. -/
private theorem poly_bnd_chunks
    (re : polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector)
    (b : Std.I16)
    (h : matrix.poly_bnd portable_ops_inst re b = .ok true) :
    ∀ i : Nat, i < 16 →
      matrix.chunk_bnd portable_ops_inst (re.coefficients.val[i]!) b = .ok true := by
  have hlen : re.coefficients.val.length = 16 := re.coefficients.property
  simp only [matrix.poly_bnd, Aeneas.Std.bind_tc_ok,
    array_index_ok re.coefficients 0#usize (by simp [hlen]),
    array_index_ok re.coefficients 1#usize (by simp [hlen]),
    array_index_ok re.coefficients 2#usize (by simp [hlen]),
    array_index_ok re.coefficients 3#usize (by simp [hlen]),
    array_index_ok re.coefficients 4#usize (by simp [hlen]),
    array_index_ok re.coefficients 5#usize (by simp [hlen]),
    array_index_ok re.coefficients 6#usize (by simp [hlen]),
    array_index_ok re.coefficients 7#usize (by simp [hlen]),
    array_index_ok re.coefficients 8#usize (by simp [hlen]),
    array_index_ok re.coefficients 9#usize (by simp [hlen]),
    array_index_ok re.coefficients 10#usize (by simp [hlen]),
    array_index_ok re.coefficients 11#usize (by simp [hlen]),
    array_index_ok re.coefficients 12#usize (by simp [hlen]),
    array_index_ok re.coefficients 13#usize (by simp [hlen]),
    array_index_ok re.coefficients 14#usize (by simp [hlen]),
    array_index_ok re.coefficients 15#usize (by simp [hlen])] at h
  obtain ⟨h0, h⟩ := bind_if_ok_true h
  obtain ⟨h1, h⟩ := bind_if_ok_true h
  obtain ⟨h2, h⟩ := bind_if_ok_true h
  obtain ⟨h3, h⟩ := bind_if_ok_true h
  obtain ⟨h4, h⟩ := bind_if_ok_true h
  obtain ⟨h5, h⟩ := bind_if_ok_true h
  obtain ⟨h6, h⟩ := bind_if_ok_true h
  obtain ⟨h7, h⟩ := bind_if_ok_true h
  obtain ⟨h8, h⟩ := bind_if_ok_true h
  obtain ⟨h9, h⟩ := bind_if_ok_true h
  obtain ⟨h10, h⟩ := bind_if_ok_true h
  obtain ⟨h11, h⟩ := bind_if_ok_true h
  obtain ⟨h12, h⟩ := bind_if_ok_true h
  obtain ⟨h13, h⟩ := bind_if_ok_true h
  obtain ⟨h14, h15⟩ := bind_if_ok_true h
  intro i hi
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · exact absurd hi (by omega)

/-- `poly_bnd re 3328 = ok true` unrolled to per-lane `natAbs ≤ 3328`. -/
theorem poly_bnd_natAbs_3328
    (re : polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector)
    (h : matrix.poly_bnd portable_ops_inst re 3328#i16 = .ok true) :
    ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3328 := by
  intro i hi j hj
  exact lane_bnd_le_3328
    (chunk_bnd_lanes _ 3328#i16 (poly_bnd_chunks re 3328#i16 h i hi) j hj)

/-- `poly_bnd re 4095 = ok true` unrolled to per-lane `natAbs ≤ 4095`. -/
theorem poly_bnd_natAbs_4095
    (re : polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector)
    (h : matrix.poly_bnd portable_ops_inst re 4095#i16 = .ok true) :
    ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 4095 := by
  intro i hi j hj
  exact lane_bnd_le_4095
    (chunk_bnd_lanes _ 4095#i16 (poly_bnd_chunks re 4095#i16 h i hi) j hj)

/-- `poly_bnd re 29439 = ok true` unrolled to per-lane `natAbs ≤ 29439`. -/
theorem poly_bnd_natAbs_29439
    (re : polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector)
    (h : matrix.poly_bnd portable_ops_inst re 29439#i16 = .ok true) :
    ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 29439 := by
  intro i hi j hj
  exact lane_bnd_le_29439
    (chunk_bnd_lanes _ 29439#i16 (poly_bnd_chunks re 29439#i16 h i hi) j hj)

/-- `holds (do bb ← x; ok (bb = true))` forces `x = ok true`. -/
private theorem holds_bind_eq_true {x : RustM Bool}
    (h : RustM.holds (do let bb ← x; ok (bb = true))) : x = .ok true := by
  cases x with
  | ok bb =>
      have hbb : bb = true := by
        simpa [RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply] using h
      rw [hbb]
  | fail e => exfalso; simp [RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply] at h
  | div => exfalso; simp [RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply] at h

/-- The `vec_bnd` `forall` conjunct, as it appears once the `pre`'s `Prop.and`
    layer and the `From<bool>` `into` are simped away (the closure returns a
    `Bool`, so the quantified body is `holds (do bb ← closure …; ok (bb = true))`),
    peeled to `poly_bnd (a[k]!) bnd = ok true` for each `k < K`. -/
private theorem vec_forall_to_poly {K : Std.Usize}
    (a : Std.Array
          (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector) K)
    (bnd : Std.I16)
    (h : ∀ t : Std.Usize, RustM.holds (do
          let bb ← matrix.vec_bnd.closure.Insts.CoreOpsFunctionFnTupleUsizeBool.call
                     portable_ops_inst (a, bnd) t
          ok (bb = true)))
    (k : Nat) (hk : k < K.val) :
    matrix.poly_bnd portable_ops_inst (a.val[k]!) bnd = .ok true := by
  have ht := h (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize)
  simp only [matrix.vec_bnd.closure.Insts.CoreOpsFunctionFnTupleUsizeBool.call] at ht
  have hxval : (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize).val = k := by
    show (BitVec.ofNat UScalarTy.Usize.numBits k).toNat = k
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt
    have hKlt : K.val < 2 ^ UScalarTy.Usize.numBits := K.bv.isLt
    omega
  have hvlen : a.val.length = K.val := a.property
  have hlt : (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize) < K := by scalar_tac
  simp only [hlt, if_true] at ht
  -- the `let (a,i) := (a,bnd)` destructure reduces definitionally
  have ht2 : RustM.holds (do
      let bb ← (do
        let pre ← a.index_usize (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize)
        matrix.poly_bnd portable_ops_inst pre bnd)
      ok (bb = true)) := ht
  rw [array_index_ok a (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize)
      (by rw [hxval, hvlen]; exact hk), hxval] at ht2
  simp only [bind_tc_ok] at ht2
  exact holds_bind_eq_true ht2

/-- The decoded `vec_bnd a 4095` `forall` conjunct, unrolled to per-chunk/lane
    `natAbs ≤ 4095` (the FC `h_secret_bnd` shape). -/
theorem vec_bnd_natAbs_4095 {K : Std.Usize}
    (a : Std.Array
          (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector) K)
    (h : ∀ t : Std.Usize, RustM.holds (do
          let bb ← matrix.vec_bnd.closure.Insts.CoreOpsFunctionFnTupleUsizeBool.call
                     portable_ops_inst (a, 4095#i16) t
          ok (bb = true))) :
    ∀ k : Nat, k < K.val → ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((a.val[k]!.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 4095 := by
  intro k hk i hi j hj
  exact poly_bnd_natAbs_4095 (a.val[k]!) (vec_forall_to_poly a 4095#i16 h k hk) i hi j hj

/-- The decoded `vec_bnd a 3328` `forall` conjunct, unrolled to per-chunk/lane
    `natAbs ≤ 3328` (the FC `h_u_bnd` shape). -/
theorem vec_bnd_natAbs_3328 {K : Std.Usize}
    (a : Std.Array
          (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector) K)
    (h : ∀ t : Std.Usize, RustM.holds (do
          let bb ← matrix.vec_bnd.closure.Insts.CoreOpsFunctionFnTupleUsizeBool.call
                     portable_ops_inst (a, 3328#i16) t
          ok (bb = true))) :
    ∀ k : Nat, k < K.val → ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((a.val[k]!.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3328 := by
  intro k hk i hi j hj
  exact poly_bnd_natAbs_3328 (a.val[k]!) (vec_forall_to_poly a 3328#i16 h k hk) i hi j hj

/-- The decoded `vec_bnd a 29439` `forall` conjunct, unrolled to per-lane
    `natAbs ≤ 29439` (the FC `h_error_bnd` shape). -/
theorem vec_bnd_natAbs_29439 {K : Std.Usize}
    (a : Std.Array
          (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector) K)
    (h : ∀ t : Std.Usize, RustM.holds (do
          let bb ← matrix.vec_bnd.closure.Insts.CoreOpsFunctionFnTupleUsizeBool.call
                     portable_ops_inst (a, 29439#i16) t
          ok (bb = true))) :
    ∀ k : Nat, k < K.val → ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((a.val[k]!.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 29439 := by
  intro k hk i hi j hj
  exact poly_bnd_natAbs_29439 (a.val[k]!) (vec_forall_to_poly a 29439#i16 h k hk) i hi j hj

/-! ## Array `==` reflexivity

    The generated `#[ensures]` posts compare two `[FieldElement; 256]` with the
    Rust `==` (`core.Array…PartialEqArray.eq`), an element-wise `loop`. When both
    sides are the SAME lifted polynomial the walk returns `ok true`; this is the
    reusable reflexivity fact that closes every post once `LiftAgree` collapses
    the two sides. -/

open CoreModels in
/-- `Slice.index_usize` in range, as a plain equation. -/
private theorem slice_index_ok {T : Type} [Inhabited T] (s : Aeneas.Std.Slice T)
    (i : Std.Usize) (h : i.val < s.val.length) :
    Aeneas.Std.Slice.index_usize s i = .ok (s.val[i.val]!) := by
  unfold Aeneas.Std.Slice.index_usize
  rw [Aeneas.Std.Slice.getElem?_Usize_eq, List.getElem?_eq_getElem h,
    List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

open CoreModels in
private theorem array_index_self_ok {T : Type} [Inhabited T] {N : Std.Usize}
    (x : Std.Array T N) (i : Std.Usize) (h : i.val < N.val) :
    CoreModels.rust_primitives.slice.array_index x i = .ok (x.val[i.val]!) := by
  have hlen : (Aeneas.Std.Array.to_slice x).val.length = N.val := by
    rw [Aeneas.Std.Array.val_to_slice]; exact x.property
  unfold CoreModels.rust_primitives.slice.array_index
  rw [slice_index_ok (Aeneas.Std.Array.to_slice x) i (by rw [hlen]; exact h),
    Aeneas.Std.Array.val_to_slice]

open CoreModels in
/-- The element-wise `==` loop on equal arrays returns `ok true`, by downward
    induction on the remaining `fuel = N - i`. -/
private theorem array_eq_loop_self {T : Type} [Inhabited T] {N : Std.Usize}
    (inst : CoreModels.core.cmp.PartialEq T T) (x : Std.Array T N)
    (hrefl : ∀ j : Nat, j < N.val → inst.eq (x.val[j]!) (x.val[j]!) = .ok true) :
    ∀ (fuel : Nat) (i : Std.Usize), i.val + fuel = N.val →
      CoreModels.core.Array.Insts.CoreCmpPartialEqArray.eq_loop inst x x i = .ok true := by
  intro fuel
  induction fuel with
  | zero =>
      intro i hi
      unfold CoreModels.core.Array.Insts.CoreCmpPartialEqArray.eq_loop
      rw [Aeneas.Std.loop.eq_1]
      simp only [CoreModels.core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body]
      have hnlt : ¬ (i < N) := by scalar_tac
      simp only [hnlt, if_false, reduceIte]
  | succ f ih =>
      intro i hi
      have hlt : i.val < N.val := by omega
      have hltB : (i < N) := by scalar_tac
      have hNmax : N.val ≤ Aeneas.Std.UScalar.max .Usize := by
        have := N.hBounds; scalar_tac
      have hadd : ∃ i1 : Std.Usize,
          (i + 1#usize : RustM Std.Usize) = .ok i1 ∧ i1.val = i.val + 1 := by
        obtain ⟨i1, h1, h2, _⟩ :=
          Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.UScalar.add_bv_spec (x := i) (y := 1#usize)
            (by show i.val + 1 ≤ Aeneas.Std.UScalar.max .Usize; omega))
        exact ⟨i1, h1, by simp [h2]⟩
      obtain ⟨i1, hi1_eq, hi1_val⟩ := hadd
      unfold CoreModels.core.Array.Insts.CoreCmpPartialEqArray.eq_loop
      rw [Aeneas.Std.loop.eq_1]
      simp only [CoreModels.core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body,
        if_pos hltB, array_index_self_ok x i hlt, bind_tc_ok, hrefl i.val hlt, hi1_eq,
        if_true]
      show CoreModels.core.Array.Insts.CoreCmpPartialEqArray.eq_loop inst x x i1 = .ok true
      exact ih i1 (by omega)

open CoreModels in
/-- Rust `==` on an array against itself is `ok true`, given element reflexivity. -/
theorem array_eq_self {T : Type} [Inhabited T] {N : Std.Usize}
    (inst : CoreModels.core.cmp.PartialEq T T) (x : Std.Array T N)
    (hrefl : ∀ j : Nat, j < N.val → inst.eq (x.val[j]!) (x.val[j]!) = .ok true) :
    CoreModels.core.Array.Insts.CoreCmpPartialEqArray.eq inst x x = .ok true := by
  unfold CoreModels.core.Array.Insts.CoreCmpPartialEqArray.eq
  exact array_eq_loop_self inst x hrefl N.val 0#usize (by simp)

/-! ## `matrix_slice_bnd` and `acc_zero` decode (for `compute_As_plus_e`) -/

/-- The decoded `matrix_slice_bnd slice bnd` `forall` conjunct (over `k < K*K`),
    peeled to `poly_bnd (slice[k]!) bnd = ok true`. Mirrors `vec_forall_to_poly`
    with the extra `i1 ← K*K` bound and the `Slice` index. -/
private theorem matrix_slice_forall_to_poly {K : Std.Usize}
    (slice : Slice
      (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector))
    (bnd : Std.I16) (hlen : K.val * K.val ≤ slice.val.length)
    (h : ∀ t : Std.Usize, RustM.holds (do
          let bb ← matrix.matrix_slice_bnd.closure.Insts.CoreOpsFunctionFnTupleUsizeBool.call
                     (K := K) portable_ops_inst (slice, bnd) t
          ok (bb = true)))
    (k : Nat) (hk : k < K.val * K.val) :
    matrix.poly_bnd portable_ops_inst (slice.val[k]!) bnd = .ok true := by
  have hslen : slice.val.length ≤ Aeneas.Std.UScalar.max .Usize := by
    have := slice.property; scalar_tac
  have hmaxlt : Aeneas.Std.UScalar.max UScalarTy.Usize < 2 ^ UScalarTy.Usize.numBits := by
    scalar_tac
  have hxval : (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize).val = k := by
    show (BitVec.ofNat UScalarTy.Usize.numBits k).toNat = k
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
  obtain ⟨kk, hkk_eq, hkk_val, _⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.UScalar.mul_bv_spec (x := K) (y := K)
      (by show K.val * K.val ≤ Aeneas.Std.UScalar.max .Usize; omega))
  have hkkv : kk.val = K.val * K.val := by rw [hkk_val]
  have hguard : (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize) < kk := by
    scalar_tac
  have ht := h (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize)
  simp only
    [matrix.matrix_slice_bnd.closure.Insts.CoreOpsFunctionFnTupleUsizeBool.call] at ht
  have ht2 : RustM.holds (do
      let bb ← (do
        let i1 ← K * K
        if (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize) < i1 then
          (do let pre ← Aeneas.Std.Slice.index_usize slice
                (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize)
              matrix.poly_bnd portable_ops_inst pre bnd)
        else ok true)
      ok (bb = true)) := ht
  rw [hkk_eq] at ht2
  simp only [bind_tc_ok, if_pos hguard,
    slice_index_ok slice (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize)
      (by rw [hxval]; omega), hxval] at ht2
  exact holds_bind_eq_true ht2

/-- `matrix_slice_bnd` conjunct unrolled to per-lane `natAbs ≤ 3328` over `K*K`. -/
theorem matrix_slice_natAbs_3328 {K : Std.Usize}
    (slice : Slice
      (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector))
    (hlen : K.val * K.val ≤ slice.val.length)
    (h : ∀ t : Std.Usize, RustM.holds (do
          let bb ← matrix.matrix_slice_bnd.closure.Insts.CoreOpsFunctionFnTupleUsizeBool.call
                     (K := K) portable_ops_inst (slice, 3328#i16) t
          ok (bb = true))) :
    ∀ k : Nat, k < K.val * K.val → ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((slice.val[k]!.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3328 := by
  intro k hk i hi j hj
  exact poly_bnd_natAbs_3328 (slice.val[k]!)
    (matrix_slice_forall_to_poly slice 3328#i16 hlen h k hk) i hi j hj

/-- The decoded `acc_zero accumulator` `forall` conjunct, peeled to
    `accumulator[n]! = 0#i32` for each `n < 256`. -/
theorem acc_zero_of_holds (accumulator : Std.Array Std.I32 256#usize)
    (h : ∀ t : Std.Usize, RustM.holds (do
          let bb ← matrix.acc_zero.closure.Insts.CoreOpsFunctionFnTupleUsizeBool.call accumulator t
          ok (bb = true)))
    (n : Nat) (hn : n < 256) :
    accumulator.val[n]! = (0#i32 : Std.I32) := by
  have hxval : (BitVec.ofNat UScalarTy.Usize.numBits n#uscalar : Std.Usize).val = n := by
    show (BitVec.ofNat UScalarTy.Usize.numBits n).toNat = n
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt
    have h256 : (2 : Nat) ^ 16 ≤ 2 ^ UScalarTy.Usize.numBits := by
      rw [UScalarTy.Usize_numBits_eq]
      exact Nat.pow_le_pow_right (by norm_num) (by cases System.Platform.numBits_eq <;> omega)
    omega
  have hguard : (BitVec.ofNat UScalarTy.Usize.numBits n#uscalar : Std.Usize) < 256#usize := by
    scalar_tac
  have hlen : accumulator.val.length = 256 := by have := accumulator.property; simpa using this
  have ht := h (BitVec.ofNat UScalarTy.Usize.numBits n#uscalar : Std.Usize)
  simp only [matrix.acc_zero.closure.Insts.CoreOpsFunctionFnTupleUsizeBool.call, if_pos hguard] at ht
  rw [array_index_ok accumulator (BitVec.ofNat UScalarTy.Usize.numBits n#uscalar : Std.Usize)
      (by rw [hxval, hlen]; exact hn)] at ht
  simp only [libcrux_secrets.traits.Declassify.Blanket.declassify, bind_tc_ok, hxval] at ht
  -- ht : holds (ok (decide (accumulator[n]! = 0#i32) = true))
  have hb : decide (accumulator.val[n]! = (0#i32 : Std.I32)) = true := by
    simpa [RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply] using ht
  exact of_decide_eq_true hb

/-! ## `vec_slice_bnd` decode (for `compute_vector_u`) -/

/-- The decoded `vec_slice_bnd slice bnd` `forall` conjunct (over `k < K`, a
    `Slice`), peeled to `poly_bnd (slice[k]!) bnd = ok true`. -/
private theorem vec_slice_forall_to_poly {K : Std.Usize}
    (slice : Slice
      (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector))
    (bnd : Std.I16) (hlen : K.val ≤ slice.val.length)
    (h : ∀ t : Std.Usize, RustM.holds (do
          let bb ← matrix.vec_slice_bnd.closure.Insts.CoreOpsFunctionFnTupleUsizeBool.call
                     (K := K) portable_ops_inst (slice, bnd) t
          ok (bb = true)))
    (k : Nat) (hk : k < K.val) :
    matrix.poly_bnd portable_ops_inst (slice.val[k]!) bnd = .ok true := by
  have hKlt : K.val < 2 ^ UScalarTy.Usize.numBits := K.bv.isLt
  have hxval : (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize).val = k := by
    show (BitVec.ofNat UScalarTy.Usize.numBits k).toNat = k
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
  have hguard : (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize) < K := by
    scalar_tac
  have ht := h (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize)
  simp only
    [matrix.vec_slice_bnd.closure.Insts.CoreOpsFunctionFnTupleUsizeBool.call] at ht
  have ht2 : RustM.holds (do
      let bb ← (if (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize) < K then
        (do let pre ← Aeneas.Std.Slice.index_usize slice
              (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize)
            matrix.poly_bnd portable_ops_inst pre bnd)
        else ok true)
      ok (bb = true)) := ht
  simp only [if_pos hguard,
    slice_index_ok slice (BitVec.ofNat UScalarTy.Usize.numBits k#uscalar : Std.Usize)
      (by rw [hxval]; omega), hxval, bind_tc_ok] at ht2
  exact holds_bind_eq_true ht2

/-- `vec_slice_bnd slice 3328` conjunct unrolled to per-lane `natAbs ≤ 3328`. -/
theorem vec_slice_natAbs_3328 {K : Std.Usize}
    (slice : Slice
      (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector))
    (hlen : K.val ≤ slice.val.length)
    (h : ∀ t : Std.Usize, RustM.holds (do
          let bb ← matrix.vec_slice_bnd.closure.Insts.CoreOpsFunctionFnTupleUsizeBool.call
                     (K := K) portable_ops_inst (slice, 3328#i16) t
          ok (bb = true))) :
    ∀ k : Nat, k < K.val → ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((slice.val[k]!.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3328 := by
  intro k hk i hi j hj
  exact poly_bnd_natAbs_3328 (slice.val[k]!)
    (vec_slice_forall_to_poly slice 3328#i16 hlen h k hk) i hi j hj

/-- `vec_slice_bnd slice 29439` conjunct unrolled to per-lane `natAbs ≤ 29439`. -/
theorem vec_slice_natAbs_29439 {K : Std.Usize}
    (slice : Slice
      (polynomial.PolynomialRingElement vector.portable.vector_type.PortableVector))
    (hlen : K.val ≤ slice.val.length)
    (h : ∀ t : Std.Usize, RustM.holds (do
          let bb ← matrix.vec_slice_bnd.closure.Insts.CoreOpsFunctionFnTupleUsizeBool.call
                     (K := K) portable_ops_inst (slice, 29439#i16) t
          ok (bb = true))) :
    ∀ k : Nat, k < K.val → ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((slice.val[k]!.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 29439 := by
  intro k hk i hi j hj
  exact poly_bnd_natAbs_29439 (slice.val[k]!)
    (vec_slice_forall_to_poly slice 29439#i16 hlen h k hk) i hi j hj
