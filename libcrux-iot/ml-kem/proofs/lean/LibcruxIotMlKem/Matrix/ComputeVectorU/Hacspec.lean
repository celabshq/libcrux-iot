/-
  # `Matrix/ComputeVectorU/Hacspec.lean` — L7.2 `D''` tail bridge.

  The hacspec↔pure equational bridge for the *add* (error-injection) tail of
  the `compute_vector_u` decomposition, directly analogous to the proven `D`
  lemma `ComputeMessage.sub_polynomials_scaleZ_eq`.

  * **D'' (hacspec side)** — `add_polynomials (scaleZ 512 b) e
    = add_error_reduce_pure b e` for canonical `b` lanes (the `·512` factor
    matches the impl's fused Montgomery `·1441` correction, since
    `1441 · 169 ≡ 512` in `ZMod 3329`; `Bridges.glue_1441_169`).

  The factor `512` is `#eval`-validated (PBT, 2026-05-29). Per-lane
  characterization mirrors `Bridges.zmodOfFE_subtract_reduce_pure_lane`.

  Local copies of the `private` lane-access / canonicity helpers from
  `ComputeMessage` / `Bridges` are re-derived here (this file imports only
  FCTargets/Common/Bridges, so the `private` originals are out of scope).
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
import LibcruxIotMlKem.Matrix.ComputeMessage.Bridges

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace libcrux_iot_ml_kem.Matrix.ComputeVectorU.Hacspec
open libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeMessage.Bridges
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec
open libcrux_iot_ml_kem.InvertNtt libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeAsPlusE libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.NttMultiply libcrux_iot_ml_kem.Polynomial.PolyOpsFc libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt
open libcrux_iot_ml_kem.Spec.Pure (Canonical)
section AddPolyScaleZ

/-! ### Local lane-access / canonicity helpers (copies of the `private`
    originals in `ComputeMessage` / `Bridges`). -/

/-- Generic `Std.Array.make … (range m).map f` lane access (local copy). -/
private theorem mkN_map_lane'' {α : Type} [Inhabited α] {n : Std.Usize} {m : Nat}
    (f : Nat → α) (k : Nat) (hk : k < m)
    (hlen : ((List.range m).map f).length = n.val) :
    (Std.Array.make n ((List.range m).map f) hlen).val[k]! = f k := by
  show ((List.range m).map f)[k]! = f k
  have h_len : ((List.range m).map f).length = m := by simp
  rw [getElem!_pos _ k (by rw [h_len]; exact hk)]
  simp

/-- `chunk_at` lane access (local copy). -/
private theorem chunk_at_lane''
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (k ℓ : Nat) (hℓ : ℓ < 16) :
    (Spec.chunk_at p k).val[ℓ]! = p.val[16 * k + ℓ]! := by
  unfold Spec.chunk_at
  show ((List.range 16).map (fun j => p.val[16 * k + j]!))[ℓ]! = p.val[16 * k + ℓ]!
  have h_len : ((List.range 16).map (fun j => p.val[16 * k + j]!)).length = 16 := by simp
  rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
  rw [List.getElem_map, List.getElem_range]

/-- Lane access for a 16-chunk flatten shape (local copy of
    `flatten_chunk_map_lane`). -/
private theorem flatten_chunk_map_lane''
    (H : Nat → Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (j : Nat) (hj : j < 256)
    (h : ((List.range 16).map H).length = (16#usize).val) :
    (Spec.flatten_chunks (Std.Array.make 16#usize ((List.range 16).map H) h)).val[j]!
      = (H (j / 16)).val[j % 16]! := by
  have hk : j / 16 < 16 := by omega
  unfold Spec.flatten_chunks
  rw [mkN_map_lane'' _ j hj]
  rw [mkN_map_lane'' H (j / 16) hk]

/-- Canonical round-trip (local copy). -/
private theorem canon_feOfZMod'' (z : ZMod 3329) : Canonical (feOfZMod z) := by
  unfold Canonical feOfZMod hacspec_ml_kem.parameters.FIELD_MODULUS
  show (BitVec.ofNat 16 z.val).toNat < _
  rw [BitVec.toNat_ofNat]
  have hz : z.val < 3329 := ZMod.val_lt z
  have : z.val % 2 ^ 16 = z.val := Nat.mod_eq_of_lt (by omega)
  simp only [this]; simpa using hz

/-- Canonical round-trip (local copy of `feOfZMod_zmodOfFE_of_canon'`). -/
private theorem feOfZMod_zmodOfFE_of_canon''
    (fe : hacspec_ml_kem.parameters.FieldElement) (h : Canonical fe) :
    feOfZMod (zmodOfFE fe) = fe := by
  have h' : fe.val.val < 3329 := by
    unfold Canonical hacspec_ml_kem.parameters.FIELD_MODULUS at h; simpa using h
  unfold feOfZMod zmodOfFE
  have hzval : ((fe.val.val : ZMod 3329)).val = fe.val.val := ZMod.val_natCast_of_lt h'
  rw [hzval]
  have hfeval : fe.val.val < 2 ^ 16 := by
    have h_p : (3329 : Nat) ≤ 2 ^ 16 := by decide
    omega
  have hfebv : BitVec.ofNat 16 fe.val.val = fe.val.bv := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    show fe.val.val % 2 ^ 16 = fe.val.bv.toNat
    rw [Nat.mod_eq_of_lt hfeval]; rfl
  show ({ val := ⟨BitVec.ofNat 16 fe.val.val⟩ } :
          hacspec_ml_kem.parameters.FieldElement) = fe
  rw [hfebv]

/-- `scaleZ c p` is canonical per lane (local copy of `canonArr_scaleZ'`). -/
private theorem canonArr_scaleZ'' (c : ZMod 3329)
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (j : Nat) (hj : j < 256) : Canonical ((scaleZ c p).val[j]!) := by
  unfold scaleZ
  rw [mkN_map_lane'' (fun k => feOfZMod (c * zmodOfFE (p.val[k]!))) j hj _]
  exact canon_feOfZMod'' _

/-- Two canonical 256-arrays with equal `zmodOfFE` lanes are equal (local copy
    of `eq_of_zmod_lane_canon`). -/
private theorem eq_of_zmod_lane_canon''
    (u v : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (hcu : ∀ j : Nat, j < 256 → Canonical (u.val[j]!))
    (hcv : ∀ j : Nat, j < 256 → Canonical (v.val[j]!))
    (hz : ∀ j : Nat, j < 256 → zmodOfFE (u.val[j]!) = zmodOfFE (v.val[j]!)) :
    u = v := by
  apply Subtype.ext
  apply List.ext_getElem
  · rw [Aeneas.Std.Array.length_eq u, Aeneas.Std.Array.length_eq v]
  · intro j hj1 _hj2
    have hj : j < 256 := by rw [Aeneas.Std.Array.length_eq u] at hj1; simpa using hj1
    have heq : u.val[j]! = v.val[j]! := by
      rw [← feOfZMod_zmodOfFE_of_canon'' (u.val[j]!) (hcu j hj),
          ← feOfZMod_zmodOfFE_of_canon'' (v.val[j]!) (hcv j hj), hz j hj]
    have huj : u.val[j]! = u.val[j] :=
      getElem!_pos u.val j (by rw [Aeneas.Std.Array.length_eq u]; exact hj)
    have hvj : v.val[j]! = v.val[j] :=
      getElem!_pos v.val j (by rw [Aeneas.Std.Array.length_eq v]; exact hj)
    rw [← huj, ← hvj]; exact heq

/-! ### The genuinely-new per-lane characterization of `add_error_reduce_pure`. -/

/-- Per-lane characterization of `Spec.add_error_reduce_pure`: for `j < 256`
    and canonical `b[j]`,
    `zmodOfFE ((add_error_reduce_pure b e)[j]) = 512 · zmodOfFE (b[j]) + zmodOfFE (e[j])`.
    The impl's fused Montgomery `·1441` correction equals `·512` in `ZMod 3329`
    since `1441 · 169 ≡ 512` (`glue_1441_169`). Mirrors
    `Bridges.zmodOfFE_subtract_reduce_pure_lane`. -/
private theorem zmodOfFE_add_error_reduce_pure_lane
    (b e : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (j : Nat) (hj : j < 256)
    (hb : libcrux_iot_ml_kem.Spec.Pure.Canonical (b.val[j]!)) :
    zmodOfFE ((Spec.add_error_reduce_pure b e).val[j]!)
      = 512 * zmodOfFE (b.val[j]!) + zmodOfFE (e.val[j]!) := by
  have hℓ : j % 16 < 16 := Nat.mod_lt _ (by decide)
  have hjeq : 16 * (j / 16) + j % 16 = j := by omega
  unfold Spec.add_error_reduce_pure
  rw [flatten_chunk_map_lane'' (fun k => Spec.chunk_add_error_reduce_pure
        (Spec.chunk_at b k) (Spec.chunk_at e k)) j hj (by simp)]
  unfold Spec.chunk_add_error_reduce_pure
  rw [mkN_map_lane'' _ (j % 16) hℓ]
  -- lane = add_pure (mul_pure (chunk_at b k)[ℓ] (lift_fe_mont 1441)) (chunk_at e k)[ℓ]
  rw [chunk_at_lane'' b (j / 16) (j % 16) hℓ, chunk_at_lane'' e (j / 16) (j % 16) hℓ]
  rw [hjeq]
  rw [zmodOfFE_add_pure]
  rw [zmodOfFE_mul_pure]
  rw [zmodOfFE_lift_fe_mont]
  have h1441 : (((1441#i16 : Std.I16).val : ZMod 3329)) = 1441 := by decide
  rw [h1441]
  have h512 : (1441 : ZMod 3329) * 169 = 512 := glue_1441_169
  rw [show (zmodOfFE (b.val[j]!) * (1441 * 169) : ZMod 3329)
        = 512 * zmodOfFE (b.val[j]!) by rw [h512]; ring]

/-! ### D'' — the `add_polynomials ∘ scaleZ` bridge.

    Mirrors `ComputeMessage.sub_polynomials_scaleZ_eq` exactly: the createi
    reduction `matrix_add_polynomials_eq_ok` (public, FCTargets) gives the
    per-lane `add_pure` array; `eq_of_zmod_lane_canon''` reduces equality to
    canonicity + per-lane `zmodOfFE`. -/
set_option maxHeartbeats 1000000 in
theorem add_polynomials_scaleZ_eq
    (b e : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (hb : ∀ j : Nat, j < 256 →
      libcrux_iot_ml_kem.Spec.Pure.Canonical (b.val[j]!)) :
    hacspec_ml_kem.matrix.add_polynomials (scaleZ 512 b) e
      = .ok (Spec.add_error_reduce_pure b e) := by
  have hc : ∀ k : Nat, k < 256 → Canonical ((scaleZ 512 b).val[k]!) :=
    fun k hk => canonArr_scaleZ'' 512 b k hk
  rw [Stage4MatrixAddFC.matrix_add_polynomials_eq_ok (scaleZ 512 b) e]
  -- The reduced LHS array (set L); show it equals `add_error_reduce_pure b e`.
  set L : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
    ⟨(List.range 256).map (fun k =>
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          ((scaleZ 512 b).val[k]!) (e.val[k]!)),
     by simp [List.length_map, List.length_range]⟩ with hL_def
  have hL_lane : ∀ j : Nat, j < 256 →
      L.val[j]! = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                    ((scaleZ 512 b).val[j]!) (e.val[j]!) := by
    intro j hj
    show ((List.range 256).map (fun k =>
            libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              ((scaleZ 512 b).val[k]!) (e.val[k]!)))[j]! = _
    rw [getElem!_pos _ j (by simp [List.length_map, List.length_range, hj])]
    rw [List.getElem_map, List.getElem_range]
  apply congrArg Result.ok
  apply eq_of_zmod_lane_canon''
  · -- L lanes canonical
    intro j hj
    rw [hL_lane j hj]
    exact libcrux_iot_ml_kem.Spec.Pure.Canonical_add_pure _ _
  · -- add_error_reduce_pure lanes canonical
    intro j hj
    have hℓ : j % 16 < 16 := Nat.mod_lt _ (by decide)
    have hjeq : 16 * (j / 16) + j % 16 = j := by omega
    unfold Spec.add_error_reduce_pure
    rw [flatten_chunk_map_lane'' (fun k => Spec.chunk_add_error_reduce_pure
          (Spec.chunk_at b k) (Spec.chunk_at e k)) j hj (by simp)]
    unfold Spec.chunk_add_error_reduce_pure
    rw [mkN_map_lane'' _ (j % 16) hℓ]
    exact libcrux_iot_ml_kem.Spec.Pure.Canonical_add_pure _ _
  · -- per-lane zmodOfFE equality
    intro j hj
    rw [hL_lane j hj]
    rw [zmodOfFE_add_pure]
    rw [scaleZ_lane 512 b j hj]
    rw [zmodOfFE_add_error_reduce_pure_lane b e j hj (hb j hj)]

end AddPolyScaleZ

/-! ## L7.2-P0.2 — matrix-column product = vector product over the column.

    `multiply_matrix_by_column_at m vec i` (loop body folds
    `add_polynomials result (multiply_ntts m[j][i] vec[j])`) is structurally
    identical to `multiply_vectors (extractCol m i) vec` (loop body folds
    `add_polynomials result (multiply_ntts (extractCol m i)[j] vec[j])`) since
    `(extractCol m i)[j] = m[j][i]`. We reduce BOTH loops, via two
    `loop_range_spec_usize` applications with the SAME invariant, to a common
    per-lane fold `mcol_result_at_step`, then combine.

    `multiply_ntts` / `add_polynomials` are treated opaquely: only the index
    fact `(extractCol m i)[j]! = m[j]![i]!` is needed to align the bodies. -/
section MatrixColEqVectors

open hacspec_ml_kem.parameters (FieldElement)

/-- Polynomial as a 256-lane field-element array (avoids repeating the
    `256#usize` literal in nested binder types, which re-triggers the
    `n#usize` macro tactic — SKILL §9.13 / nested-index trap). -/
private abbrev Poly256 := Std.Array FieldElement 256#usize

/-- Local copy of the `private triple_of_ok_fc`. -/
private theorem triple_of_ok_fc' {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply, hp]

/-- Local copy of the `private triple_exists_ok_fc`. -/
private theorem triple_exists_ok_fc' {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl, (by subst hx; simpa [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply])

/-- Column `i` extracted from matrix `m`: lane `j` is `m[j][i]`. -/
private noncomputable def extractCol {K : Std.Usize}
    (m : Std.Array (Std.Array (Poly256) K) K)
    (i : Std.Usize) : Std.Array (Poly256) K :=
  Std.Array.make K ((List.range K.val).map (fun j => (m.val[j]!).val[i.val]!))
    (by simp [List.length_map, List.length_range])

/-- Lane access for `extractCol`: `(extractCol m i)[j]! = m[j]![i]!` for `j < K`. -/
private theorem extractCol_lane {K : Std.Usize}
    (m : Std.Array (Std.Array (Poly256) K) K)
    (i : Std.Usize) (j : Nat) (hj : j < K.val) :
    (extractCol m i).val[j]! = (m.val[j]!).val[i.val]! := by
  unfold extractCol
  show ((List.range K.val).map (fun j => (m.val[j]!).val[i.val]!))[j]! = _
  rw [getElem!_pos _ j (by simp [List.length_map, List.length_range, hj])]
  simp [List.getElem_map, List.getElem_range]

/-- Per-lane partial sum produced by the matrix-column / vector loop at step `k`:
    the `add_polynomials`-product foldl, lane `ℓ`, seeded at `⟨0#u16⟩`.
    Folds the raw `multiply_ntts_pure` lane of `col[c]` against `vec[c]`. -/
private noncomputable def mcol_lane_at_step {K : Std.Usize}
    (col vec : Std.Array (Poly256) K)
    (k : Nat) (ℓ : Nat) : FieldElement :=
  (List.range k).foldl
    (fun s c =>
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
        ((Spec.multiply_ntts_pure (col.val[c]!) (vec.val[c]!)).val[ℓ]!))
    ({ val := 0#u16 } : FieldElement)

/-- The per-step accumulator array: lane `ℓ` is `mcol_lane_at_step ... k ℓ`. -/
private noncomputable def mcol_result_at_step {K : Std.Usize}
    (col vec : Std.Array (Poly256) K)
    (k : Nat) : Poly256 :=
  ⟨(List.range 256).map (fun ℓ => mcol_lane_at_step col vec k ℓ),
   by simp [List.length_map, List.length_range]⟩

private theorem mcol_result_at_step_val_lane {K : Std.Usize}
    (col vec : Std.Array (Poly256) K)
    (k : Nat) (ℓ : Nat) (hℓ : ℓ < 256) :
    (mcol_result_at_step col vec k).val[ℓ]! = mcol_lane_at_step col vec k ℓ := by
  unfold mcol_result_at_step
  show ((List.range 256).map (fun ℓ' => mcol_lane_at_step col vec k ℓ'))[ℓ]! = _
  rw [getElem!_pos _ ℓ (by simp [List.length_map, List.length_range, hℓ])]
  rw [List.getElem_map, List.getElem_range]

private theorem mcol_lane_at_step_zero {K : Std.Usize}
    (col vec : Std.Array (Poly256) K) (ℓ : Nat) :
    mcol_lane_at_step col vec 0 ℓ = ({ val := 0#u16 } : FieldElement) := by
  unfold mcol_lane_at_step
  rw [List.range_zero, List.foldl_nil]

private theorem mcol_lane_at_step_succ {K : Std.Usize}
    (col vec : Std.Array (Poly256) K) (k : Nat) (ℓ : Nat) :
    mcol_lane_at_step col vec (k + 1) ℓ
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          (mcol_lane_at_step col vec k ℓ)
          ((Spec.multiply_ntts_pure (col.val[k]!) (vec.val[k]!)).val[ℓ]!) := by
  unfold mcol_lane_at_step
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The accumulator-advance fact shared by both loop bodies: one column step
    `add_polynomials acc (multiply_ntts col[k] vec[k])` evaluates to
    `.ok (mcol_result_at_step col vec (k+1))` when `acc = mcol_result_at_step col vec k`. -/
private theorem mcol_step_add_eq {K : Std.Usize}
    (col vec : Std.Array (Poly256) K) (k : Nat) :
    hacspec_ml_kem.matrix.add_polynomials (mcol_result_at_step col vec k)
        (Spec.multiply_ntts_pure (col.val[k]!) (vec.val[k]!))
      = .ok (mcol_result_at_step col vec (k + 1)) := by
  rw [Stage4MatrixAddFC.matrix_add_polynomials_eq_ok]
  apply congrArg Result.ok
  apply Subtype.ext
  show (List.range 256).map (fun n =>
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
        (mcol_result_at_step col vec k).val[n]!
        (Spec.multiply_ntts_pure (col.val[k]!) (vec.val[k]!)).val[n]!)
    = (mcol_result_at_step col vec (k + 1)).val
  unfold mcol_result_at_step
  apply List.map_congr_left
  intro n hn_mem
  have hn_lt : n < 256 := List.mem_range.mp hn_mem
  show libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
      (mcol_result_at_step col vec k).val[n]!
      (Spec.multiply_ntts_pure (col.val[k]!) (vec.val[k]!)).val[n]!
    = mcol_lane_at_step col vec (k + 1) n
  rw [mcol_result_at_step_val_lane _ _ _ _ hn_lt, mcol_lane_at_step_succ]

/-- The shared step-body `multiply_ntts` reduction. -/
private theorem mcol_mult_eq (a1 a2 : Poly256) :
    hacspec_ml_kem.ntt.multiply_ntts a1 a2 = .ok (Spec.multiply_ntts_pure a1 a2) := by
  unfold Spec.multiply_ntts_pure
  rw [HelpersFC.multiply_ntts_eq_pure_array]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 1000 in
/-- **Triple B.** `multiply_vectors col vec` reduces to `mcol_result_at_step col vec K`.
    Direct specialization of the `multiply_vectors_eq` pattern, but on raw
    FE-array-typed `col`/`vec` (no `lift_vec`). -/
private theorem multiply_vectors_eq_mcol {K : Std.Usize}
    (col vec : Std.Array (Poly256) K) :
    hacspec_ml_kem.matrix.multiply_vectors col vec
      = .ok (mcol_result_at_step col vec K.val) := by
  unfold hacspec_ml_kem.matrix.multiply_vectors
  unfold hacspec_ml_kem.parameters.FieldElement.new
  simp only [bind_tc_ok]
  have h_triple : ⦃ ⌜ True ⌝ ⦄
      hacspec_ml_kem.matrix.multiply_vectors_loop
        ({ start := 0#usize, «end» := K } : CoreModels.core.ops.range.Range Std.Usize)
        col vec
        (Std.Array.repeat (256#usize : Std.Usize) ({ val := 0#u16 } : FieldElement))
      ⦃ ⇓ r => ⌜ r = mcol_result_at_step col vec K.val ⌝ ⦄ := by
    unfold hacspec_ml_kem.matrix.multiply_vectors_loop
    apply Std.Do.Triple.of_entails_right _
      (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
        (fun p : CoreModels.core.ops.range.Range Std.Usize ×
                   Poly256 =>
          hacspec_ml_kem.matrix.multiply_vectors_loop.body col vec p.1 p.2)
        (β := Poly256)
        (Std.Array.repeat (256#usize : Std.Usize) ({ val := 0#u16 } : FieldElement))
        0#usize K
        (fun k result => pure (result = mcol_result_at_step col vec k.val))
        (Nat.zero_le _)
        (by
          show (pure _ : Result Prop).holds
          simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
          intro _
          apply Subtype.ext
          rw [Std.Array.repeat_val]
          unfold mcol_result_at_step
          show List.replicate 256 _ = (List.range 256).map _
          apply List.ext_getElem
          · rw [List.length_replicate, List.length_map, List.length_range]
          intro n h_n_lhs _
          have h_n_lt : n < 256 := by
            rw [List.length_replicate] at h_n_lhs; exact h_n_lhs
          rw [List.getElem_replicate, List.getElem_map, List.getElem_range]
          show _ = mcol_lane_at_step col vec 0 n
          rw [mcol_lane_at_step_zero])
        ?_)
    · rw [PostCond.entails_noThrow]
      intro r hh
      have h_eq : (pure (r = mcol_result_at_step col vec K.val) : Result Prop).holds := by
        simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_eq
    · intro acc k _h_ge h_le hinv
      have h_acc_eq : acc = mcol_result_at_step col vec k.val := by
        simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using hinv
      subst h_acc_eq
      unfold hacspec_ml_kem.matrix.multiply_vectors_loop.body
      by_cases h_lt : k.val < K.val
      · have h_iter_step :
            ⦃ ⌜ True ⌝ ⦄
            CoreModels.core.iter.range.IteratorRange.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize)
            ⦃ ⇓ r => ⌜ ∃ s : Std.Usize, s.val = k.val + 1 ∧
                        r = (some k, ({ start := s, «end» := K }
                              : CoreModels.core.ops.range.Range Std.Usize)) ⌝ ⦄ :=
          libcrux_iot_ml_kem.Util.LoopSpecs.IteratorRange_next_spec_usize k K
            (fun _ s hs => by
              dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
              exact ⟨s, hs, rfl⟩)
            (fun hge => absurd h_lt (Nat.not_lt.mpr hge))
        obtain ⟨v_iter, hv_iter_eq, hv_iter_post⟩ := triple_exists_ok_fc' h_iter_step
        obtain ⟨s_iter, hs_iter_val, hv_iter_pair⟩ := hv_iter_post
        have hlen_col : col.length = K.val := Std.Array.length_eq col
        have hlen_vec : vec.length = K.val := Std.Array.length_eq vec
        have h_idx_a1 : Aeneas.Std.Array.index_usize col k = .ok (col.val[k.val]!) :=
          libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq col k
            (by rw [hlen_col]; exact h_lt)
        have h_idx_a2 : Aeneas.Std.Array.index_usize vec k = .ok (vec.val[k.val]!) :=
          libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq vec k
            (by rw [hlen_vec]; exact h_lt)
        have h_body :
            (fun p : CoreModels.core.ops.range.Range Std.Usize ×
                       Poly256 =>
              hacspec_ml_kem.matrix.multiply_vectors_loop.body col vec p.1 p.2)
              ({ start := k, «end» := K }, mcol_result_at_step col vec k.val)
            = .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize),
                  mcol_result_at_step col vec (k.val + 1))) := by
          show hacspec_ml_kem.matrix.multiply_vectors_loop.body col vec
                { start := k, «end» := K } (mcol_result_at_step col vec k.val) = _
          unfold hacspec_ml_kem.matrix.multiply_vectors_loop.body
          conv_lhs =>
            rw [show
              (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                  core.Usize.Insts.CoreIterRangeStep
                  ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize))
                = (CoreModels.core.iter.range.IteratorRange.next
                    core.Usize.Insts.CoreIterRangeStep
                    ({ start := k, «end» := K }
                      : CoreModels.core.ops.range.Range Std.Usize))
              from rfl]
          rw [hv_iter_pair] at hv_iter_eq
          rw [hv_iter_eq]
          simp only [Aeneas.Std.bind_tc_ok]
          show ((do
                  let a ← Aeneas.Std.Array.index_usize col k
                  let a1' ← Aeneas.Std.Array.index_usize vec k
                  let product ← hacspec_ml_kem.ntt.multiply_ntts a a1'
                  let result1 ← hacspec_ml_kem.matrix.add_polynomials
                    (mcol_result_at_step col vec k.val) product
                  Aeneas.Std.Result.ok (ControlFlow.cont
                    (({ start := s_iter, «end» := K }
                      : CoreModels.core.ops.range.Range Std.Usize), result1)))
                : Result _) = _
          rw [h_idx_a1]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [h_idx_a2]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [mcol_mult_eq]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [mcol_step_add_eq]
          simp only [Aeneas.Std.bind_tc_ok]
        apply triple_of_ok_fc' h_body
        refine ⟨h_lt, rfl, hs_iter_val, ?_⟩
        show (pure (mcol_result_at_step col vec (k.val + 1)
                      = mcol_result_at_step col vec s_iter.val) : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        rw [hs_iter_val]
        rfl
      · have hk_ge : k.val ≥ K.val := Nat.not_lt.mp h_lt
        have hk_eq : k.val = K.val := by omega
        have h_iter_none :
            ⦃ ⌜ True ⌝ ⦄
            CoreModels.core.iter.range.IteratorRange.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize)
            ⦃ ⇓ r => ⌜ r = ((none : Option Std.Usize),
                              ({ start := k, «end» := K }
                                : CoreModels.core.ops.range.Range Std.Usize)) ⌝ ⦄ :=
          libcrux_iot_ml_kem.Util.LoopSpecs.IteratorRange_next_spec_usize k K
            (fun hlt => absurd hlt (Nat.not_lt.mpr hk_ge))
            (fun _ => by dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure])
        obtain ⟨v_iter, hv_iter_eq, hv_iter_post⟩ := triple_exists_ok_fc' h_iter_none
        have h_body :
            (fun p : CoreModels.core.ops.range.Range Std.Usize ×
                       Poly256 =>
              hacspec_ml_kem.matrix.multiply_vectors_loop.body col vec p.1 p.2)
              ({ start := k, «end» := K }, mcol_result_at_step col vec k.val)
            = .ok (ControlFlow.done (mcol_result_at_step col vec k.val)) := by
          show hacspec_ml_kem.matrix.multiply_vectors_loop.body col vec
                { start := k, «end» := K } (mcol_result_at_step col vec k.val) = _
          unfold hacspec_ml_kem.matrix.multiply_vectors_loop.body
          conv_lhs =>
            rw [show
              (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                  core.Usize.Insts.CoreIterRangeStep
                  ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize))
                = (CoreModels.core.iter.range.IteratorRange.next
                    core.Usize.Insts.CoreIterRangeStep
                    ({ start := k, «end» := K }
                      : CoreModels.core.ops.range.Range Std.Usize))
              from rfl]
          rw [hv_iter_post] at hv_iter_eq
          rw [hv_iter_eq]
          rfl
        apply triple_of_ok_fc' h_body
        show (pure (mcol_result_at_step col vec k.val
                      = mcol_result_at_step col vec K.val) : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        rw [hk_eq]
        rfl
  obtain ⟨v, hv_eq, hv_post⟩ := triple_exists_ok_fc' h_triple
  rw [hv_eq, hv_post]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 1000 in
/-- **Triple A (matrix).** `multiply_matrix_by_column_at m vec i` reduces to
    `mcol_result_at_step (extractCol m i) vec K`. Same invariant/structure as
    Triple B; the only difference is the loop body's extra `index_usize m j`/
    `index_usize a i` steps, aligned via `extractCol_lane`. -/
private theorem multiply_matrix_by_column_at_eq_mcol {K : Std.Usize}
    (m : Std.Array (Std.Array (Poly256) K) K)
    (vec : Std.Array (Poly256) K) (i : Std.Usize)
    (hi : i.val < K.val) :
    hacspec_ml_kem.matrix.multiply_matrix_by_column_at m vec i
      = .ok (mcol_result_at_step (extractCol m i) vec K.val) := by
  unfold hacspec_ml_kem.matrix.multiply_matrix_by_column_at
  unfold hacspec_ml_kem.parameters.FieldElement.new
  simp only [bind_tc_ok]
  have h_triple : ⦃ ⌜ True ⌝ ⦄
      hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop
        ({ start := 0#usize, «end» := K } : CoreModels.core.ops.range.Range Std.Usize)
        m vec i
        (Std.Array.repeat (256#usize : Std.Usize) ({ val := 0#u16 } : FieldElement))
      ⦃ ⇓ r => ⌜ r = mcol_result_at_step (extractCol m i) vec K.val ⌝ ⦄ := by
    unfold hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop
    apply Std.Do.Triple.of_entails_right _
      (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
        (fun p : CoreModels.core.ops.range.Range Std.Usize ×
                   Poly256 =>
          hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body m vec i p.1 p.2)
        (β := Poly256)
        (Std.Array.repeat (256#usize : Std.Usize) ({ val := 0#u16 } : FieldElement))
        0#usize K
        (fun k result => pure (result = mcol_result_at_step (extractCol m i) vec k.val))
        (Nat.zero_le _)
        (by
          show (pure _ : Result Prop).holds
          simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
          intro _
          apply Subtype.ext
          rw [Std.Array.repeat_val]
          unfold mcol_result_at_step
          show List.replicate 256 _ = (List.range 256).map _
          apply List.ext_getElem
          · rw [List.length_replicate, List.length_map, List.length_range]
          intro n h_n_lhs _
          have h_n_lt : n < 256 := by
            rw [List.length_replicate] at h_n_lhs; exact h_n_lhs
          rw [List.getElem_replicate, List.getElem_map, List.getElem_range]
          show _ = mcol_lane_at_step (extractCol m i) vec 0 n
          rw [mcol_lane_at_step_zero])
        ?_)
    · rw [PostCond.entails_noThrow]
      intro r hh
      have h_eq : (pure (r = mcol_result_at_step (extractCol m i) vec K.val)
                  : Result Prop).holds := by
        simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_eq
    · intro acc k _h_ge h_le hinv
      have h_acc_eq : acc = mcol_result_at_step (extractCol m i) vec k.val := by
        simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using hinv
      subst h_acc_eq
      unfold hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body
      by_cases h_lt : k.val < K.val
      · have h_iter_step :
            ⦃ ⌜ True ⌝ ⦄
            CoreModels.core.iter.range.IteratorRange.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize)
            ⦃ ⇓ r => ⌜ ∃ s : Std.Usize, s.val = k.val + 1 ∧
                        r = (some k, ({ start := s, «end» := K }
                              : CoreModels.core.ops.range.Range Std.Usize)) ⌝ ⦄ :=
          libcrux_iot_ml_kem.Util.LoopSpecs.IteratorRange_next_spec_usize k K
            (fun _ s hs => by
              dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
              exact ⟨s, hs, rfl⟩)
            (fun hge => absurd h_lt (Nat.not_lt.mpr hge))
        obtain ⟨v_iter, hv_iter_eq, hv_iter_post⟩ := triple_exists_ok_fc' h_iter_step
        obtain ⟨s_iter, hs_iter_val, hv_iter_pair⟩ := hv_iter_post
        -- index_usize m k = m[k]!; index_usize (m[k]!) i = m[k]![i]! = (extractCol m i)[k]!
        have hlen_m : m.length = K.val := Std.Array.length_eq m
        have hlen_vec : vec.length = K.val := Std.Array.length_eq vec
        have hlen_mk : (m.val[k.val]!).length = K.val := Std.Array.length_eq (m.val[k.val]!)
        have h_idx_mk : Aeneas.Std.Array.index_usize m k = .ok (m.val[k.val]!) :=
          libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq m k
            (by rw [hlen_m]; exact h_lt)
        have h_col_eq : (extractCol m i).val[k.val]! = (m.val[k.val]!).val[i.val]! :=
          extractCol_lane m i k.val h_lt
        have h_idx_a1 :
            Aeneas.Std.Array.index_usize (m.val[k.val]!) i = .ok ((extractCol m i).val[k.val]!) := by
          rw [h_col_eq]
          exact libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq (m.val[k.val]!) i
            (by rw [hlen_mk]; exact hi)
        have h_idx_a2 : Aeneas.Std.Array.index_usize vec k = .ok (vec.val[k.val]!) :=
          libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq vec k
            (by rw [hlen_vec]; exact h_lt)
        have h_body :
            (fun p : CoreModels.core.ops.range.Range Std.Usize ×
                       Poly256 =>
              hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body m vec i p.1 p.2)
              ({ start := k, «end» := K }, mcol_result_at_step (extractCol m i) vec k.val)
            = .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize),
                  mcol_result_at_step (extractCol m i) vec (k.val + 1))) := by
          show hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body m vec i
                { start := k, «end» := K }
                (mcol_result_at_step (extractCol m i) vec k.val) = _
          unfold hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body
          conv_lhs =>
            rw [show
              (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                  core.Usize.Insts.CoreIterRangeStep
                  ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize))
                = (CoreModels.core.iter.range.IteratorRange.next
                    core.Usize.Insts.CoreIterRangeStep
                    ({ start := k, «end» := K }
                      : CoreModels.core.ops.range.Range Std.Usize))
              from rfl]
          rw [hv_iter_pair] at hv_iter_eq
          rw [hv_iter_eq]
          simp only [Aeneas.Std.bind_tc_ok]
          show ((do
                  let a ← Aeneas.Std.Array.index_usize m k
                  let a1 ← Aeneas.Std.Array.index_usize a i
                  let a2 ← Aeneas.Std.Array.index_usize vec k
                  let product ← hacspec_ml_kem.ntt.multiply_ntts a1 a2
                  let result1 ← hacspec_ml_kem.matrix.add_polynomials
                    (mcol_result_at_step (extractCol m i) vec k.val) product
                  Aeneas.Std.Result.ok (ControlFlow.cont
                    (({ start := s_iter, «end» := K }
                      : CoreModels.core.ops.range.Range Std.Usize), result1)))
                : Result _) = _
          rw [h_idx_mk]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [h_idx_a1]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [h_idx_a2]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [mcol_mult_eq]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [mcol_step_add_eq]
          simp only [Aeneas.Std.bind_tc_ok]
        apply triple_of_ok_fc' h_body
        refine ⟨h_lt, rfl, hs_iter_val, ?_⟩
        show (pure (mcol_result_at_step (extractCol m i) vec (k.val + 1)
                      = mcol_result_at_step (extractCol m i) vec s_iter.val)
              : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        rw [hs_iter_val]
        rfl
      · have hk_ge : k.val ≥ K.val := Nat.not_lt.mp h_lt
        have hk_eq : k.val = K.val := by omega
        have h_iter_none :
            ⦃ ⌜ True ⌝ ⦄
            CoreModels.core.iter.range.IteratorRange.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize)
            ⦃ ⇓ r => ⌜ r = ((none : Option Std.Usize),
                              ({ start := k, «end» := K }
                                : CoreModels.core.ops.range.Range Std.Usize)) ⌝ ⦄ :=
          libcrux_iot_ml_kem.Util.LoopSpecs.IteratorRange_next_spec_usize k K
            (fun hlt => absurd hlt (Nat.not_lt.mpr hk_ge))
            (fun _ => by dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure])
        obtain ⟨v_iter, hv_iter_eq, hv_iter_post⟩ := triple_exists_ok_fc' h_iter_none
        have h_body :
            (fun p : CoreModels.core.ops.range.Range Std.Usize ×
                       Poly256 =>
              hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body m vec i p.1 p.2)
              ({ start := k, «end» := K }, mcol_result_at_step (extractCol m i) vec k.val)
            = .ok (ControlFlow.done (mcol_result_at_step (extractCol m i) vec k.val)) := by
          show hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body m vec i
                { start := k, «end» := K }
                (mcol_result_at_step (extractCol m i) vec k.val) = _
          unfold hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body
          conv_lhs =>
            rw [show
              (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                  core.Usize.Insts.CoreIterRangeStep
                  ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize))
                = (CoreModels.core.iter.range.IteratorRange.next
                    core.Usize.Insts.CoreIterRangeStep
                    ({ start := k, «end» := K }
                      : CoreModels.core.ops.range.Range Std.Usize))
              from rfl]
          rw [hv_iter_post] at hv_iter_eq
          rw [hv_iter_eq]
          rfl
        apply triple_of_ok_fc' h_body
        show (pure (mcol_result_at_step (extractCol m i) vec k.val
                      = mcol_result_at_step (extractCol m i) vec K.val)
              : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        rw [hk_eq]
        rfl
  obtain ⟨v, hv_eq, hv_post⟩ := triple_exists_ok_fc' h_triple
  rw [hv_eq, hv_post]

/-- **L7.2-P0.2.** `multiply_matrix_by_column_at m vec i` equals
    `multiply_vectors (extractCol m i) vec`: the matrix-column product is the
    vector product over the extracted column. Both reduce to the same
    `mcol_result_at_step` fold. -/
theorem multiply_matrix_by_column_at_eq_multiply_vectors {K : Std.Usize}
    (m : Std.Array (Std.Array (Poly256) K) K)
    (vec : Std.Array (Poly256) K)
    (i : Std.Usize) (hi : i.val < K.val) :
    hacspec_ml_kem.matrix.multiply_matrix_by_column_at m vec i
      = hacspec_ml_kem.matrix.multiply_vectors (extractCol m i) vec := by
  rw [multiply_matrix_by_column_at_eq_mcol m vec i hi, multiply_vectors_eq_mcol]

end MatrixColEqVectors

end libcrux_iot_ml_kem.Matrix.ComputeVectorU.Hacspec