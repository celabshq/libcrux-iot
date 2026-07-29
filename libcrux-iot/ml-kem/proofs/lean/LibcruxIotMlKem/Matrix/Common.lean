/-
  # `Matrix/Common.lean` — shared L7.4 scaffolding.

  Holds the small shared definitions used by the L7.4 `compute_message`
  proof and (prospectively) reused by L7.2/L7.3:

  * `Impl.compute_message_zero` — the all-zero canonical-domain poly used
    as the accumulator fold seed (mirrors the impl's `accumulator1 :=
    Array.repeat 256 (classify 0)` re-zero at `matrix.rs:96`).

  These live above the `Impl.*_pure` mirror (defined in
  `L7/Impl/ComputeMessage.lean`) and the bridge lemmas (in
  `Matrix/ComputeMessage/Hacspec.lean`).

  SKELETON — no proofs beyond what is needed for these defs to
  elaborate. The named obligations live in the Impl/Hacspec/FC files.
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
import LibcruxIotMlKem.Polynomial.PolyOps
import LibcruxIotMlKem.Polynomial.PolyOpsFcBarrett
import LibcruxIotMlKem.Polynomial.PolyOpsFc

namespace libcrux_iot_ml_kem.Matrix.Common
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec
open libcrux_iot_ml_kem.InvertNtt libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.NttMultiply libcrux_iot_ml_kem.Polynomial.PolyOpsFc libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt

/-- The all-zero canonical-domain ring element (256 lanes, each
    `FieldElement.val = 0`). This is the fold seed for
    `Impl.compute_message_acc_pure`, mirroring the impl's explicit
    accumulator re-zero (`matrix.rs:96`, modeled in `` as
    `Array.repeat 256#usize (classify 0#i32)`). -/
noncomputable def Impl.compute_message_zero :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Std.Array.make 256#usize
    ((List.range 256).map (fun _ => ({ val := 0#u16 } : hacspec_ml_kem.parameters.FieldElement)))
    (by rw [List.length_map, List.length_range]; rfl)

/-! ## Mont→canonical BRIDGE for the `reducing_from_i32_array` step.

    `poly_reducing_from_i32_array_fc` characterizes its output `result1`
    in the `lift_poly_mont` domain (`lift_poly_mont result1 = …pure`), but
    `invert_ntt_montgomery_fc` consumes `result1` in the `lift_poly` domain
    (`lift_poly result1`). The two differ by one Montgomery factor `R` per
    lane. The impl's `montgomery_multiply_by_constant 1353` (= `R²` mod q)
    convention used by the L6.3a finalizer means the canonical lane value
    is `mul_pure (mont-lane) (lift_fe_mont 1353)` (since
    `1353 ≡ R² (mod q)` and `lift_fe_mont` carries an `R⁻¹`, the product is
    `(a·R⁻¹)·(R²·R⁻¹) = a`).

    `Impl.mont_strip_pure` is the poly-level BRIDGE; the bridge lemma
    `Impl.mont_strip_lift_poly_mont_eq_lift_poly` re-derives FCTargets'
    `private lift_poly_mont_to_lift_poly` from public primitives so the L7
    files (which cannot see the private original) can apply it. -/

/-- Local copy of `Spec.Pure.uscalar_rem_ok_U32` (private there); the L7
    files re-derive it from `BitVec.umod` to reprove `mul_pure_val_eq`. -/
private theorem Impl.uscalar_rem_ok_U32 (z m : Std.U32) (hm : m.val ≠ 0) :
    ∃ w : Std.U32, (z % m : Result Std.U32) = .ok w ∧ w.val = z.val % m.val := by
  have heq : (z % m : Result Std.U32) = Std.UScalar.rem z m := rfl
  unfold Std.UScalar.rem at heq
  simp [hm] at heq
  refine ⟨_, heq, ?_⟩
  show (BitVec.umod z.bv m.bv).toNat = z.val % m.val
  unfold BitVec.umod
  simp only [BitVec.toNat_ofNatLT]
  rfl

/-- Local copy of FCTargets' `private mul_pure_val_eq`:
    `(mul_pure a b).val.val = (a.val.val * b.val.val) % 3329`,
    unconditional (the U32 widening keeps the product `< 2^32`). -/
private theorem Impl.mul_pure_val_eq
    (a b : hacspec_ml_kem.parameters.FieldElement) :
    (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure a b).val.val
      = (a.val.val * b.val.val) % 3329 := by
  have hmul :
      hacspec_ml_kem.parameters.FieldElement.mul a b
        = .ok (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure a b) :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_eq_ok a b
  unfold hacspec_ml_kem.parameters.FieldElement.mul at hmul
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok] at hmul
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Aeneas.Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hae := Std.UScalar.mul_equiv x y
  have heqmul : (x * y : Result Std.U32) = Std.UScalar.mul x y := rfl
  cases hxy : (x * y : Result Std.U32) with
  | ok z =>
    rw [hxy] at hmul
    rw [heqmul] at hxy; rw [hxy] at hae; simp at hae
    obtain ⟨_, hzval, _⟩ := hae
    simp only [Aeneas.Std.bind_tc_ok] at hmul
    have hmod_val :
        (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS).val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; simp
    have hmod_ne :
        (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS).val ≠ 0 := by
      rw [hmod_val]; decide
    set m : Std.U32 := Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS
    obtain ⟨w, hw_eq, hwval⟩ := Impl.uscalar_rem_ok_U32 z m hmod_ne
    rw [hw_eq] at hmul; simp only [Aeneas.Std.bind_tc_ok] at hmul
    unfold hacspec_ml_kem.parameters.FieldElement.new at hmul
    simp at hmul
    have hwbnd : w.val < 3329 := by
      rw [hwval, hmod_val]; exact Nat.mod_lt _ (by decide)
    have hwcast : (Std.UScalar.cast .U16 w).val = w.val := by
      apply Std.UScalar.cast_val_mod_pow_of_inBounds_eq
      simp [Aeneas.Std.UScalarTy.numBits]; omega
    rw [← hmul]
    show (Std.UScalar.cast .U16 w).val = (a.val.val * b.val.val) % 3329
    rw [hwcast, hwval, hmod_val, hzval, hxval, hyval]
  | fail _ =>
    rw [heqmul] at hxy; rw [hxy] at hae
    simp only [Std.UScalar.max, Aeneas.Std.UScalarTy.numBits] at hae
    rw [hxval, hyval] at hae
    have : a.val.val * b.val.val < 2^32 := by
      have h1 : a.val.val * b.val.val ≤ (2^16 - 1) * (2^16 - 1) := by
        apply Nat.mul_le_mul <;> omega
      have heq : (2^16 - 1) * (2^16 - 1) = 2^32 - 2*2^16 + 1 := by decide
      omega
    omega
  | div => rw [heqmul] at hxy; rw [hxy] at hae; exact hae.elim

/-- `zmodOfFE` distributes over `mul_pure` (public re-derivation of
    FCTargets' `private L2_8c.zmodOfFE_mul_pure`). -/
private theorem Impl.zmodOfFE_mul_pure
    (a b : hacspec_ml_kem.parameters.FieldElement) :
    zmodOfFE (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure a b)
      = zmodOfFE a * zmodOfFE b := by
  unfold zmodOfFE
  rw [Impl.mul_pure_val_eq]
  rw [ZMod.natCast_mod]
  push_cast
  rfl

/-- `zmodOfFE (lift_fe_mont x) = x.val · 169` (public re-derivation of
    FCTargets' `private L2_8c.zmodOfFE_lift_fe_mont`). -/
private theorem Impl.zmodOfFE_lift_fe_mont (x : Std.I16) :
    zmodOfFE (lift_fe_mont x) = (x.val : ZMod 3329) * 169 := by
  unfold lift_fe_mont
  rw [zmodOfFE_feOfZMod]
  rfl

/-- FE-level Mont→canonical bridge:
    `mul_pure (lift_fe_mont x) (lift_fe_mont 1353) = lift_fe x`.
    In `ZMod 3329`: `lift_fe_mont y = y·169` and `1353·169·169 ≡ 1`, so the
    product canonically round-trips to `x`. Reproves the `private`
    `lift_fe_mont_mul_1353_eq_lift_fe` from public lemmas. -/
theorem Impl.lift_fe_mont_mul_1353_eq_lift_fe (x : Std.I16) :
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
      (lift_fe_mont x) (lift_fe_mont (1353#i16 : Std.I16))
      = lift_fe x := by
  set s : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
      (lift_fe_mont x) (lift_fe_mont (1353#i16 : Std.I16)) with hs_def
  -- (1) `s` is canonical (`Canonical_mul_pure` is unconditional).
  have h_canon : s.val.val < 3329 := by
    have h_cs := libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure
      (lift_fe_mont x) (lift_fe_mont (1353#i16 : Std.I16))
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at h_cs
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cs
    exact h_cs
  -- (2) Canonical round-trip `feOfZMod (zmodOfFE s) = s`.
  have h_round_trip : feOfZMod (zmodOfFE s) = s := by
    unfold feOfZMod zmodOfFE
    have hzval : ((s.val.val : ZMod 3329)).val = s.val.val :=
      ZMod.val_natCast_of_lt h_canon
    rw [hzval]
    have hsval : s.val.val < 2 ^ 16 := by
      have h_p : (3329 : Nat) ≤ 2 ^ 16 := by decide
      omega
    have hsbv : BitVec.ofNat 16 s.val.val = s.val.bv := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      show s.val.val % 2 ^ 16 = s.val.bv.toNat
      rw [Nat.mod_eq_of_lt hsval]; rfl
    show ({ val := ⟨BitVec.ofNat 16 s.val.val⟩ } :
            hacspec_ml_kem.parameters.FieldElement) = s
    rw [hsbv]
  -- (3) `zmodOfFE s = (x.val : ZMod 3329)`.
  have h_zmod_s : zmodOfFE s = ((x.val : Int) : ZMod 3329) := by
    rw [hs_def, Impl.zmodOfFE_mul_pure,
        Impl.zmodOfFE_lift_fe_mont, Impl.zmodOfFE_lift_fe_mont]
    have h_1353 : (((1353#i16 : Std.I16).val : Int) : ZMod 3329) = 1353 := by
      decide
    rw [h_1353]
    have h_inv : (169 : ZMod 3329) * (1353 * 169) = 1 := by decide
    calc ((x.val : Int) : ZMod 3329) * 169 * (1353 * 169)
        = ((x.val : Int) : ZMod 3329) * (169 * (1353 * 169)) := by ring
      _ = ((x.val : Int) : ZMod 3329) * 1 := by rw [h_inv]
      _ = ((x.val : Int) : ZMod 3329) := by ring
  -- (4) Glue: `s = feOfZMod (zmodOfFE s) = lift_fe x`.
  show s = lift_fe x
  rw [← h_round_trip, h_zmod_s]
  unfold lift_fe i16_to_spec_fe_plain
  rfl

/-- Poly-level Mont→canonical bridge function. Maps each of the 256 lanes
    through `mul_pure · (lift_fe_mont 1353)`. -/
noncomputable def Impl.mont_strip_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Std.Array.make 256#usize
    ((List.range 256).map (fun i =>
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
        (p.val[i]!) (lift_fe_mont (1353#i16 : Std.I16))))
    (by simp)

/-- Poly-level Mont→canonical BRIDGE law:
    `mont_strip_pure (lift_poly_mont re) = lift_poly re`.
    Reproves FCTargets' `private lift_poly_mont_to_lift_poly` (poly form)
    from the FE-level helper. This is the lemma that lets S2 connect the
    `reducing_from_i32_array` POST (stated via `lift_poly_mont`) to the
    `invert_ntt_montgomery` PRE (stated via `lift_poly`). -/
theorem Impl.mont_strip_lift_poly_mont_eq_lift_poly
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Impl.mont_strip_pure (libcrux_iot_ml_kem.Spec.Lift.lift_poly_mont re) = lift_poly re := by
  unfold Impl.mont_strip_pure
  apply Subtype.ext
  show (List.range 256).map (fun i =>
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            ((libcrux_iot_ml_kem.Spec.Lift.lift_poly_mont re).val[i]!) (lift_fe_mont (1353#i16 : Std.I16)))
      = (lift_poly re).val
  unfold lift_poly
  show (List.range 256).map (fun i =>
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            ((libcrux_iot_ml_kem.Spec.Lift.lift_poly_mont re).val[i]!) (lift_fe_mont (1353#i16 : Std.I16)))
      = (List.range 256).map (fun j =>
          lift_fe (re.coefficients.val[j / 16]!).elements.val[j % 16]!)
  apply List.ext_getElem
  · simp
  · intro j hj1 _hj2
    have hj : j < 256 := by
      have : j < ((List.range 256).map (fun i =>
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            ((libcrux_iot_ml_kem.Spec.Lift.lift_poly_mont re).val[i]!) (lift_fe_mont (1353#i16 : Std.I16)))).length := hj1
      simpa using this
    simp only [List.getElem_map, List.getElem_range]
    -- LHS lane = mul_pure (lift_fe_mont x) (lift_fe_mont 1353); RHS = lift_fe x.
    set x : Std.I16 :=
      (re.coefficients.val[j / 16]!).elements.val[j % 16]! with hx_def
    have h_mont : (libcrux_iot_ml_kem.Spec.Lift.lift_poly_mont re).val[j]! = lift_fe_mont x := by
      unfold libcrux_iot_ml_kem.Spec.Lift.lift_poly_mont
      show ((List.range 256).map (fun k =>
              lift_fe_mont (re.coefficients.val[k / 16]!).elements.val[k % 16]!))[j]!
            = lift_fe_mont x
      have h_len : ((List.range 256).map (fun k =>
              lift_fe_mont (re.coefficients.val[k / 16]!).elements.val[k % 16]!)).length = 256 := by
        simp
      rw [getElem!_pos _ j (by rw [h_len]; exact hj)]
      rw [List.getElem_map, List.getElem_range]
    rw [h_mont]
    exact Impl.lift_fe_mont_mul_1353_eq_lift_fe x

end libcrux_iot_ml_kem.Matrix.Common
/-! ### Extracted from FCTargets.lean (§matrix_entry). -/

namespace libcrux_iot_ml_kem.Matrix.Common
open libcrux_iot_ml_kem.InvertNtt libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.NttMultiply libcrux_iot_ml_kem.Polynomial.PolyOpsFc libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec

/-! ## §L6.8 — matrix per-cell accessor.

    `matrix.entry K matrix i j` is a pure indexing op on a flat K·K slice
    of polynomial-ring elements. The FC equation lifts the result via
    `lift_poly` and matches the (i, j)-th matrix entry, which under
    `lift_matrix_from_slice`'s column-major convention is accessed as
    `L.val[j.val]!.val[i.val]!` (outer = column, inner = row). Uses the
    file-scoped `Inhabited` instances `instInhabitedFEPoly_fcTargets` and
    `instInhabitedFEPolyVec_fcTargets` (declared next to
    `instInhabitedFEChunk_fcTargets`). -/

/-- Pure-projection side lemma for `matrix.entry`. Reduces the impl `do`-block
    to a single `Slice.index_usize` at row-major offset `i.val * K.val + j.val`,
    under the canonical preconditions `matrix.length = K·K`, `i < K`, `j < K`.
    Named without a `matrix.` prefix to avoid Lean's dot-notation projection
    being triggered when a local variable `matrix` is in scope at the call
    site (in `matrix.entry_fc`). -/
theorem entry_eq_ok_fc_aux
    (K : Std.Usize)
    (matrix : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (i j : Std.Usize)
    (h_len : matrix.val.length = K.val * K.val)
    (h_i : i.val < K.val) (h_j : j.val < K.val) :
    libcrux_iot_ml_kem.matrix.entry K portable_ops_inst matrix i j
      = .ok (matrix.val[i.val * K.val + j.val]!) := by
  -- Slice invariant + h_len combine to give the arithmetic bounds.
  have h_slice_max : matrix.val.length ≤ Std.Usize.max := matrix.property
  have h_KK_max : K.val * K.val ≤ Std.Usize.max := by rw [← h_len]; exact h_slice_max
  -- K.val > 0 because i.val < K.val.
  have h_K_pos : 0 < K.val := Nat.lt_of_le_of_lt (Nat.zero_le _) h_i
  -- i.val * K.val ≤ (K.val - 1) * K.val < K.val * K.val.
  have h_iK_lt : i.val * K.val < K.val * K.val :=
    (Nat.mul_lt_mul_right h_K_pos).mpr h_i
  have h_iK_max : i.val * K.val ≤ Std.Usize.max := by
    apply le_trans (Nat.le_of_lt h_iK_lt) h_KK_max
  -- i.val * K.val + j.val < K.val * K.val.
  have h_idx_lt_KK : i.val * K.val + j.val < K.val * K.val := by
    have : i.val * K.val + j.val < i.val * K.val + K.val := Nat.add_lt_add_left h_j _
    have h_step : i.val * K.val + K.val ≤ K.val * K.val := by
      have : (i.val + 1) * K.val ≤ K.val * K.val :=
        Nat.mul_le_mul_right _ h_i
      have h_expand : (i.val + 1) * K.val = i.val * K.val + K.val := by ring
      rw [h_expand] at this; exact this
    omega
  have h_idx_max : i.val * K.val + j.val ≤ Std.Usize.max := by
    apply le_trans (Nat.le_of_lt h_idx_lt_KK) h_KK_max
  have h_idx_lt_len : i.val * K.val + j.val < matrix.val.length := by
    rw [h_len]; exact h_idx_lt_KK
  -- Now reduce the do-block step by step.
  unfold libcrux_iot_ml_kem.matrix.entry
  -- Step 1: `core.slice.Slice.len matrix` = `.ok matrix.len`.
  unfold core.slice.Slice.len
  -- Step 2: `K * K` = `.ok` of a Usize with val = K.val * K.val.
  obtain ⟨kk, h_kk_eq, h_kk_val⟩ := usize_mul_ok_eq_fc K K h_KK_max
  -- Step 3: `i * K` = `.ok` of a Usize with val = i.val * K.val.
  obtain ⟨ik, h_ik_eq, h_ik_val⟩ := usize_mul_ok_eq_fc i K h_iK_max
  -- Step 4: `ik + j` = `.ok` of a Usize with val = i.val * K.val + j.val.
  have h_ikj_max : ik.val + j.val ≤ Std.Usize.max := by rw [h_ik_val]; exact h_idx_max
  obtain ⟨idx, h_idx_eq, h_idx_val⟩ := usize_add_ok_eq_fc ik j h_ikj_max
  -- Massert preconditions.
  have h_massert_len : (Aeneas.Std.Slice.len matrix : Std.Usize) = kk := by
    apply Std.UScalar.eq_of_val_eq
    show matrix.val.length = kk.val
    rw [h_kk_val, h_len]
  -- Slice.index_usize at idx returns matrix.val[idx.val]!.
  have h_idx_lt_matrix : idx.val < matrix.val.length := by
    rw [h_idx_val, h_ik_val]; exact h_idx_lt_len
  have h_slice_idx :
      Aeneas.Std.Slice.index_usize matrix idx = .ok (matrix.val[idx.val]!) :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq matrix idx h_idx_lt_matrix
  -- Rewrite the do-block.
  simp only [pure, Pure.pure, Aeneas.Std.bind_tc_ok, h_kk_eq, h_ik_eq, h_idx_eq,
             h_slice_idx, h_massert_len]
  -- Discharge massert (i = kk equality), massert (i < K), massert (j < K).
  unfold Aeneas.Std.massert
  have h_i_K : i < K := (Std.UScalar.lt_equiv i K).mpr h_i
  have h_j_K : j < K := (Std.UScalar.lt_equiv j K).mpr h_j
  simp only [if_true, Aeneas.Std.bind_tc_ok, h_i_K, h_j_K]
  -- Final goal: matrix.val[idx.val]! = matrix.val[i.val * K.val + j.val]!.
  rw [h_idx_val, h_ik_val]

/-- L6.8 — `matrix.entry`: row-major access of a flat K·K poly slice.
    The FC equation says the impl's returned `PolynomialRingElement`
    lifts (via `lift_poly`) to the `(i, j)`-th matrix entry, accessed
    under `lift_matrix_from_slice`'s column-major convention as
    `L.val[j.val]!.val[i.val]!` (outer = column, inner = row). -/
@[spec]
theorem matrix.entry_fc
    (K : Std.Usize)
    (matrix : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (i j : Std.Usize)
    (h_len : matrix.val.length = K.val * K.val)
    (h_i : i.val < K.val) (h_j : j.val < K.val) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.entry K portable_ops_inst matrix i j
    ⦃ ⇓ r => ⌜ lift_poly r = (lift_matrix_from_slice matrix K).val[j.val]!.val[i.val]! ⌝ ⦄ := by
  apply triple_of_ok_fc (entry_eq_ok_fc_aux K matrix i j h_len h_i h_j)
  -- Goal: lift_poly matrix.val[i.val * K.val + j.val]!
  --     = (lift_matrix_from_slice matrix K).val[j.val]!.val[i.val]!
  -- Reduce the matrix lift's nested `Std.Array.make` constructions explicitly.
  -- `(Std.Array.make n init _).val = init` (definitional), so each outer
  -- `.val[idx]!` collapses to a `List`-indexing on the inner `init` list.
  -- Under the column-major convention, outer index = j (column),
  -- inner index = i (row).
  unfold lift_matrix_from_slice
  -- Outer-list index reduction (outer index = column `j`).
  have h_range_len : (List.range K.val).length = K.val := by simp
  have h_outer_len : ((List.range K.val).map (fun j' =>
        Std.Array.make K ((List.range K.val).map (fun i' =>
          lift_poly matrix.val[i' * K.val + j']!)) (by simp))).length = K.val := by
    rw [List.length_map, h_range_len]
  have h_j_lt_outer : j.val < ((List.range K.val).map (fun j' =>
        Std.Array.make K ((List.range K.val).map (fun i' =>
          lift_poly matrix.val[i' * K.val + j']!)) (by simp))).length := by
    rw [h_outer_len]; exact h_j
  -- Use `Std.Array.make`'s definitional `.val = init` to expose the outer list,
  -- then resolve the outer index via `getElem!_pos`.
  show lift_poly matrix.val[i.val * K.val + j.val]!
       = ((((List.range K.val).map (fun j' =>
            Std.Array.make K ((List.range K.val).map (fun i' =>
              lift_poly matrix.val[i' * K.val + j']!)) (by simp)))[j.val]!).val[i.val]!)
  rw [getElem!_pos _ j.val h_j_lt_outer]
  rw [List.getElem_map, List.getElem_range]
  -- The outer `(fun j' => Std.Array.make K ... _) j.val` β-reduces to
  -- `Std.Array.make K (...) _`; its `.val` is the inner list.
  show lift_poly matrix.val[i.val * K.val + j.val]!
       = ((List.range K.val).map (fun i' =>
            lift_poly matrix.val[i' * K.val + j.val]!))[i.val]!
  have h_inner_len : ((List.range K.val).map (fun i' =>
        lift_poly matrix.val[i' * K.val + j.val]!)).length = K.val := by
    rw [List.length_map, h_range_len]
  have h_i_lt_inner : i.val < ((List.range K.val).map (fun i' =>
        lift_poly matrix.val[i' * K.val + j.val]!)).length := by
    rw [h_inner_len]; exact h_i
  rw [getElem!_pos _ i.val h_i_lt_inner]
  rw [List.getElem_map, List.getElem_range]


end libcrux_iot_ml_kem.Matrix.Common