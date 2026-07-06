/-
  # `Spec/Lift.lean` — extracted from `FCTargets.lean` §lift.
-/
import LibcruxIotMlKem.Spec
import LibcruxIotMlKem.Spec.Pure
import LibcruxIotMlKem.Spec.AlgEquiv
import LibcruxIotMlKem.Spec.ModularArith
import LibcruxIotMlKem.Extraction.Funs
import HacspecMlKem.Extraction.Funs

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_kem.Spec.Lift
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec

/-! ## §0 Lift tower

    Each `lift_*` projects an impl-side carrier to the corresponding
    hacspec carrier. Type signatures are load-bearing — they are what
    the FC equation reads on both sides. Bodies use existing M.1
    pieces (`i16_to_spec_fe_mont`, `feOfZMod`, `to_spec_poly_mont`)
    where convenient. -/

/-- Default `FieldElement` used by `[i]!` projections inside the
    lift bodies below. The canonical residue 0 mod q. -/
noncomputable def defaultFE :
    hacspec_ml_kem.parameters.FieldElement :=
  feOfZMod (0 : ZMod 3329)

private noncomputable instance : Inhabited hacspec_ml_kem.parameters.FieldElement :=
  ⟨defaultFE⟩

/-- Local `Inhabited` instance for `PortableVector` used by `[i]!`
    indexing in `lift_chunk` / `lift_poly`. Mirrors the `local instance`
    in `Spec.lean` (which is file-scoped). -/
private instance instInhabitedPortableVector_fcTargets :
    Inhabited libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
  ⟨{ elements := Std.Array.make 16#usize (List.replicate 16 (0#i16 : Std.I16))
        (by simp) }⟩

/-- Local `Inhabited` instance for `PolynomialRingElement PortableVector`
    used by `[i]!` indexing in `lift_poly` / `lift_vec_slice`. -/
private instance instInhabitedPolynomialRingElement_fcTargets
    {Vector : Type} [Inhabited Vector] :
    Inhabited (libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector) :=
  ⟨{ coefficients :=
       Std.Array.make 16#usize (List.replicate 16 default) (by simp) }⟩

/-- Plain-domain lane lift from `Int` to a hacspec `FieldElement`.
    Used by `barrett_reduce_element_fc` (the impl carries the value
    in plain domain). -/
noncomputable def lift_fe_int (x : Int) : hacspec_ml_kem.parameters.FieldElement :=
  feOfZMod (x : ZMod 3329)

/-- Plain-domain lane lift from `Std.I16` to a hacspec `FieldElement`.
    Composes `i16_to_spec_fe_plain` with `feOfZMod`. -/
noncomputable def lift_fe (lane : Std.I16) : hacspec_ml_kem.parameters.FieldElement :=
  feOfZMod (i16_to_spec_fe_plain lane)

/-- Mont-domain lane lift from `Std.I16` to a hacspec `FieldElement`.
    Used for outputs of impl ops that produce Mont-form lanes
    (`montgomery_multiply_*`, `montgomery_reduce_element`). -/
noncomputable def lift_fe_mont (lane : Std.I16) : hacspec_ml_kem.parameters.FieldElement :=
  feOfZMod (i16_to_spec_fe_mont lane)

/-- Plain-domain poly lift `PortableVector chunk → 16 FE-array`.
    Maps each of the 16 lanes through `lift_fe`. -/
noncomputable def lift_chunk
    (chunk : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize (chunk.elements.val.map lift_fe) (by
    simp [])

/-- Mont-domain poly lift `PortableVector chunk → 16 FE-array`.
    Maps each of the 16 lanes through `lift_fe_mont`. -/
noncomputable def lift_chunk_mont
    (chunk : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize (chunk.elements.val.map lift_fe_mont) (by
    simp [])

/-- Plain-domain poly lift: `PolynomialRingElement PortableVector →
    Array FE 256`. The result is the hacspec "ring element" type.
    Flattens 16 chunks × 16 lanes via the standard
    `i = j / 16`, `k = j % 16` decomposition. -/
noncomputable def lift_poly
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Std.Array.make 256#usize
    ((List.range 256).map (fun j =>
      lift_fe (re.coefficients.val[j / 16]!).elements.val[j % 16]!))
    (by simp)

/-- Mont-domain poly lift. Same shape as `lift_poly` but strips one
    `R` factor per lane via `i16_to_spec_fe_mont`. -/
noncomputable def lift_poly_mont
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Std.Array.make 256#usize
    ((List.range 256).map (fun j =>
      lift_fe_mont (re.coefficients.val[j / 16]!).elements.val[j % 16]!))
    (by simp)

/-- Vector lift: `Array (PolynomialRingElement) K → Array (Array FE 256) K`. -/
noncomputable def lift_vec {K : Std.Usize}
    (v : Std.Array
          (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K) :
    Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K :=
  Std.Array.make K (v.val.map lift_poly) (by
    simp [])

/-- Vector-slice variant for `Slice`-typed impl args
    (e.g. `compute_ring_element_v` takes `r_as_ntt : Slice ...`).
    The FC theorems that consume this expect `v.length = K.val` as a
    precondition; out-of-range indices default to the unit chunk. -/
noncomputable def lift_vec_slice
    (v : Slice
          (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (K : Std.Usize) :
    Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K :=
  Std.Array.make K
    ((List.range K.val).map (fun i => lift_poly v.val[i]!))
    (by simp)

/-- Plain-domain lift from a 256-lane `Std.I32` accumulator to a
    `FieldElement` poly. Each lane goes through `lift_fe_int` on its
    `.val` (Int). Used by the L6c NTT-multiply family FC equations to
    relate the impl-side I32 accumulator to a `FieldElement 256`-array.
    Matches the `Spec.poly_reducing_from_i32_array_pure` lane shape — composes cleanly with L6.7. -/
noncomputable def lift_accumulator_i32
    (acc : Std.Array Std.I32 256#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Std.Array.make 256#usize
    ((List.range 256).map (fun i => lift_fe_int (acc.val[i]!).val))
    (by simp)

/-- Matrix lift: `Array (Array (PolynomialRingElement) K) K → Array (Array (Array FE 256) K) K`. -/
noncomputable def lift_matrix {K : Std.Usize}
    (m : Std.Array
          (Std.Array
            (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K) K) :
    Std.Array
      (Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K) K :=
  Std.Array.make K (m.val.map lift_vec) (by
    simp [])

/-- Pure projection of `matrix.sample_matrix_A` from the public-key seed.
    Forward-declared here (rather than in §0.5 below) so
    `lift_matrix_from_seed` can reference it.

    Pending pure-projection side lemma:
    `hacspec_ml_kem.matrix.sample_matrix_A seed K
    = .ok (Spec.sample_matrix_A_pure seed K)`. -/
noncomputable opaque Spec.sample_matrix_A_pure
    (seed : Slice Std.U8) (K : Std.Usize) :
    Std.Array
      (Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K) K

/-- Matrix-from-seed lift: the impl `matrix.compute_vector_u` reconstructs
    the matrix in-place via `sample_matrix_entry`; the hacspec spec calls
    `matrix.sample_matrix_A` on the seed once at the top. Defers to
    `Spec.sample_matrix_A_pure` above for the deterministic projection. -/
noncomputable def lift_matrix_from_seed
    (seed : Slice Std.U8) (K : Std.Usize) :
    Std.Array
      (Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K) K :=
  Spec.sample_matrix_A_pure seed K

/-- Matrix-from-flat-slice lift: the impl `matrix.compute_As_plus_e` takes
    `matrix_A : Slice (PolynomialRingElement)` as a flat K·K slice in
    row-major order (impl convention: `matrix_A[i*K+j]` is the
    (row `i`, column `j`) entry). We reshape it into a 2D K×K matrix using
    FIPS 203's column-major convention — "a matrix is a set of column
    vectors" (`specs/ml-kem/src/matrix.rs:8-9`) — so the outer index is
    the column and the inner index is the row:
    `(lift_matrix_from_slice slice K).val[j]!.val[i]!
        = lift_poly slice.val[i * K.val + j]!`.
    This matches how hacspec's `multiply_matrix_by_column_at` accesses
    `m[j][i]` (column-major). Used by L7.1's locked POST. Requires the
    caller's `matrix_A.length = K.val * K.val` precondition for the
    indexing to be in-range (out-of-range indices default to the unit poly
    via the `Inhabited` instance). -/
noncomputable def lift_matrix_from_slice
    (slice : Slice
              (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (K : Std.Usize) :
    Std.Array
      (Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K) K :=
  Std.Array.make K
    ((List.range K.val).map (fun j =>
      Std.Array.make K
        ((List.range K.val).map (fun i =>
          lift_poly slice.val[i * K.val + j]!))
        (by simp)))
    (by simp)

/-- Pure projection of the public-key deserialization producing
    `t_as_ntt : Array (Array FE 256) K`. The impl `matrix.compute_ring_element_v`
    consumes `public_key : Slice U8` via `chunks_exact public_key
    BYTES_PER_RING_ELEMENT`, deserializing each chunk into a ring element.
    Used by L7.3's locked post. Declared `opaque` here; the explicit
    deserialization spec is a pending obligation paralleling
    `Spec.sample_matrix_A_pure`. -/
noncomputable opaque Spec.t_as_ntt_from_public_key_pure
    (public_key : Slice Std.U8) (K : Std.Usize) :
    Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K

/-- Public-key-bytes lift wrapping `Spec.t_as_ntt_from_public_key_pure`.
    The impl `matrix.compute_ring_element_v` deserializes `public_key` into
    a vector of ring elements; the hacspec spec receives this vector
    pre-deserialized as its first argument. -/
noncomputable def lift_t_as_ntt_from_public_key
    (public_key : Slice Std.U8) (K : Std.Usize) :
    Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K :=
  Spec.t_as_ntt_from_public_key_pure public_key K

/-! ## §0.5 Spec `_pure` aliases needed beyond `Spec.Pure.lean`.

    `Spec.Pure.lean` already provides:
      - `FieldElement.{add,sub,mul,neg}_pure`
      - `polynomial.{add_to_ring_element,poly_barrett_reduce,subtract_reduce}_pure`

    We add here the missing `_pure` aliases referenced by FC equations
    below. Each is the `Result`-stripped pure projection of a
    `Result`-monadic hacspec op; bodies use the standard
    `match | .ok r => r | _ => default`
    pattern (see `Spec.Pure.lean`). Bodies left `sorry` here for brevity
    — types are load-bearing. -/

/-- Pure projection of `parameters.FieldElement.new (x.val % q)` —
    the canonical-residue constructor, here re-expressed as the round-trip
    `feOfZMod ∘ zmodOfFE`. The two forms are equivalent: both produce
    `{ val := ⟨BitVec.ofNat 16 (x.val.val % 3329)⟩ }` since `zmodOfFE x`
    is `(x.val.val : ZMod 3329)` (whose underlying Nat is `x.val.val % 3329`)
    and `parameters.FieldElement.new` always returns `.ok ⟨_⟩` unconditionally.
    The round-trip form composes with the existing `zmodOfFE_feOfZMod`
    identity in M.1, making the FC equation reduce to "lift_fe r = lift_fe value
    given r ≡ value mod q". -/
noncomputable def Spec.barrett_pure (x : hacspec_ml_kem.parameters.FieldElement) :
    hacspec_ml_kem.parameters.FieldElement :=
  feOfZMod (zmodOfFE x)

/-- Pure projection of Montgomery reduction at the FE level. The impl
    `montgomery_reduce_element` takes an `Std.I32` and returns an `Std.I16`
    in Mont domain (encoding `a · R`). The hacspec spec has no direct
    counterpart at the FE level. The FC equation
    `lift_fe_mont r = Spec.mont_reduce_pure (lift_fe_int value.val)`
    combines two factors of R⁻¹:
      (i) the impl's invariant `r ≡ value · R⁻¹ (mod q)`, and
      (ii) `lift_fe_mont`'s own R-stripping (it returns `(r.val : ZMod 3329) · 169`).
    The TOTAL effect is `value.val · R⁻² mod q`. Since `R⁻¹ = 169 mod q`,
    `R⁻² = 169² mod q`. So `Spec.mont_reduce_pure` multiplies its
    ZMod-projected argument by `169 · 169`. -/
noncomputable def Spec.mont_reduce_pure (x : hacspec_ml_kem.parameters.FieldElement) :
    hacspec_ml_kem.parameters.FieldElement :=
  feOfZMod (zmodOfFE x * 169 * 169)

/-- Pure projection of Montgomery `fe · fer / R`: given two FEs, returns
    `fe · fer · R⁻¹` in canonical domain (i.e., `zmodOfFE fe · zmodOfFE fer · 169`
    in ZMod 3329). The factor `169 = R⁻¹ mod q` comes from the impl's
    Montgomery reduction step (the L0.3 calculation gave 169² because the
    INPUT was plain-via-`lift_fe_int`, whereas here `fer` is already
    interpreted in Mont domain through `lift_fe_mont`, so only ONE R⁻¹
    factor is needed). The math intent of the impl: given fe (plain, math
    value = fe) and fer (Mont, math value = fer · R⁻¹), output Mont-encoded
    fe · (fer · R⁻¹) = fe · fer · R⁻¹ in Mont. The Mont encoding is then
    stripped by `lift_fe_mont`, giving the canonical math value
    fe · fer · R⁻¹. -/
noncomputable def Spec.montgomery_multiply_fe_by_fer_pure
    (fe fer : hacspec_ml_kem.parameters.FieldElement) :
    hacspec_ml_kem.parameters.FieldElement :=
  feOfZMod (zmodOfFE fe * zmodOfFE fer * 169)

/-- Pure projection of `get_n_least_significant_bits` — pure modular
    truncation on `Std.U32`. -/
def Spec.get_n_least_significant_bits_pure (n : Std.U8) (value : Std.U32) : Std.U32 :=
  ⟨value.bv &&& ((1#32 <<< n.val) - 1#32)⟩

/-- Pure pointwise add at the FE-array level (16-lane chunk).
    Lifts `FieldElement.add_pure` across the 16 lanes via `List.range 16`. -/
noncomputable def Spec.chunk_add_pure
    (a b : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize
    ((List.range 16).map (fun i =>
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
        (a.val[i]!) (b.val[i]!)))
    (by simp)

/-- Pure pointwise sub at the FE-array level (16-lane chunk).
    Lifts `FieldElement.sub_pure` across the 16 lanes. -/
noncomputable def Spec.chunk_sub_pure
    (a b : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize
    ((List.range 16).map (fun i =>
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
        (a.val[i]!) (b.val[i]!)))
    (by simp)

/-- Pure pointwise neg at the FE-array level (16-lane chunk).
    Lifts `FieldElement.neg_pure` across the 16 lanes. -/
noncomputable def Spec.chunk_neg_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize
    ((List.range 16).map (fun i =>
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure
        (a.val[i]!)))
    (by simp)

/-- Pure pointwise barrett-reduce at the FE-array level.
    Lifts `Spec.barrett_pure` (the canonical round-trip) across 16 lanes. -/
noncomputable def Spec.chunk_barrett_reduce_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize
    ((List.range 16).map (fun i =>
      Spec.barrett_pure (a.val[i]!)))
    (by simp)

/-- Pure pointwise `montgomery_multiply_by_constant` at the chunk level
    (each lane: `fe · c / R`). Lifts `Spec.montgomery_multiply_fe_by_fer_pure`
    across 16 lanes, with the second arg threaded as the constant `c`. -/
noncomputable def Spec.chunk_montgomery_multiply_by_constant_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (c : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize
    ((List.range 16).map (fun i =>
      Spec.montgomery_multiply_fe_by_fer_pure (a.val[i]!) c))
    (by simp)

/-- Pure pointwise plain `multiply_by_constant` at the chunk level.
    Lifts `FieldElement.mul_pure` across 16 lanes with the constant `c`. -/
noncomputable def Spec.chunk_multiply_by_constant_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (c : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize
    ((List.range 16).map (fun i =>
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
        (a.val[i]!) c))
    (by simp)

/-- Pure pointwise `bitwise_and_with_constant` at the chunk level.
    NO HACSPEC EQUIVALENT — this is a bit-level mask used only in
    serialize/compress paths. The body applies BV-and on each FE's
    underlying `U16` BV.

    WARNING (FC obstruction): the FC equation for `bitwise_and_with_constant_fc`
    against `lift_chunk`-style inputs is NOT provable in general because
    `lift_chunk` discards the bit pattern (keeping only mod-3329 residue),
    while bit-level AND depends on the raw `I16` bit pattern. The body here
    is the canonical FE-side BV operation; the FC proof will STOP and report
    when attempted. Not on the L7 critical path (used only in compress/
    serialize, which lives outside the 4 matrix-level targets). -/
noncomputable def Spec.chunk_bitwise_and_with_constant_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (c : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize
    ((List.range 16).map (fun i =>
      let ai_bv : BitVec Aeneas.Std.UScalarTy.U16.numBits := (a.val[i]!).val.bv
      let c_bv  : BitVec Aeneas.Std.UScalarTy.U16.numBits := c.val.bv
      ({ val := { bv := ai_bv &&& c_bv } } : hacspec_ml_kem.parameters.FieldElement)))
    (by simp)

/-- Pure pointwise `shift_right` at the chunk level.
    NO HACSPEC EQUIVALENT at the FE level. The body applies a logical
    right shift on each FE's underlying `U16` BV by `SHIFT_BY.val.toNat`.

    WARNING (FC obstruction): same as `chunk_bitwise_and_with_constant_pure`
    — the FC equation is not provable through `lift_chunk` because the
    underlying `I16` sshiftRight depends on raw bit pattern. The body here
    serves as a placeholder; the FC proof will STOP and report. Not on
    the L7 critical path. -/
noncomputable def Spec.chunk_shift_right_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (SHIFT_BY : Std.I32) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize
    ((List.range 16).map (fun i =>
      let ai_bv : BitVec Aeneas.Std.UScalarTy.U16.numBits := (a.val[i]!).val.bv
      let shift : Nat := SHIFT_BY.val.toNat
      ({ val := { bv := ai_bv >>> shift } } : hacspec_ml_kem.parameters.FieldElement)))
    (by simp)

/-- Pure `reducing_from_i32_array` at the chunk level. Lifts `Spec.mont_reduce_pure`
    over 16 lanes of the input `i32` slice. Each lane: take `array[i]`,
    project through `lift_fe_int`, apply Montgomery reduction. -/
noncomputable def Spec.chunk_reducing_from_i32_array_pure
    (array : Slice Std.I32) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize
    ((List.range 16).map (fun i =>
      Spec.mont_reduce_pure (lift_fe_int (array.val[i]!).val)))
    (by simp)

/-! ### §M.1 — Per-lane unfolds for `Spec.chunk_*_pure`.

    Direct lane projections for the chunk-level pointwise operations.
    Save ~30-50 LOC per proof that needs to extract a specific lane
    from a chunk-pure result (e.g. L6.3 step lemma, L7 row composition,
    L6.3c cache-variant wrap). Each lemma collapses the
    `Std.Array.make 16#usize ((List.range 16).map ...)` + `[k]!` + `List.getElem_map`
    + `List.getElem_range` cascade into a single rewrite. -/

/-- Lane projection of `Spec.chunk_add_pure`. -/
theorem Spec.chunk_add_pure_lane_eq
    (a b : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (k : Nat) (hk : k < 16) :
    (Spec.chunk_add_pure a b).val[k]!
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          (a.val[k]!) (b.val[k]!) := by
  unfold Spec.chunk_add_pure
  show ((List.range 16).map (fun i =>
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          (a.val[i]!) (b.val[i]!)))[k]! = _
  have h_l : ((List.range 16).map (fun i =>
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          (a.val[i]!) (b.val[i]!))).length = 16 := by simp
  rw [getElem!_pos _ k (by rw [h_l]; exact hk)]
  rw [List.getElem_map, List.getElem_range]

/-- Lane projection of `Spec.chunk_sub_pure`. -/
theorem Spec.chunk_sub_pure_lane_eq
    (a b : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (k : Nat) (hk : k < 16) :
    (Spec.chunk_sub_pure a b).val[k]!
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
          (a.val[k]!) (b.val[k]!) := by
  unfold Spec.chunk_sub_pure
  show ((List.range 16).map (fun i =>
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
          (a.val[i]!) (b.val[i]!)))[k]! = _
  have h_l : ((List.range 16).map (fun i =>
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
          (a.val[i]!) (b.val[i]!))).length = 16 := by simp
  rw [getElem!_pos _ k (by rw [h_l]; exact hk)]
  rw [List.getElem_map, List.getElem_range]

/-- Lane projection of `Spec.chunk_neg_pure`. -/
theorem Spec.chunk_neg_pure_lane_eq
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (k : Nat) (hk : k < 16) :
    (Spec.chunk_neg_pure a).val[k]!
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure
          (a.val[k]!) := by
  unfold Spec.chunk_neg_pure
  show ((List.range 16).map (fun i =>
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure
          (a.val[i]!)))[k]! = _
  have h_l : ((List.range 16).map (fun i =>
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure
          (a.val[i]!))).length = 16 := by simp
  rw [getElem!_pos _ k (by rw [h_l]; exact hk)]
  rw [List.getElem_map, List.getElem_range]

/-- Lane projection of `Spec.chunk_reducing_from_i32_array_pure`. -/
theorem Spec.chunk_reducing_from_i32_array_pure_lane_eq
    (array : Slice Std.I32) (k : Nat) (hk : k < 16) :
    (Spec.chunk_reducing_from_i32_array_pure array).val[k]!
      = Spec.mont_reduce_pure (lift_fe_int (array.val[k]!).val) := by
  unfold Spec.chunk_reducing_from_i32_array_pure
  show ((List.range 16).map (fun i =>
        Spec.mont_reduce_pure (lift_fe_int (array.val[i]!).val)))[k]! = _
  have h_l : ((List.range 16).map (fun i =>
        Spec.mont_reduce_pure (lift_fe_int (array.val[i]!).val))).length = 16 := by simp
  rw [getElem!_pos _ k (by rw [h_l]; exact hk)]
  rw [List.getElem_map, List.getElem_range]

/-- Pure NTT butterfly step at the chunk level: applies `ntt.butterfly`
    pointwise to the lane pair `(i, j)` with `zeta`. Mirrors the impl's
    write order (`a[j] := a-t`, then `a[i] := a+t`) so that when `i = j`
    the second write wins (matching impl semantics). When `i ≠ j` the
    `(i, j)` lanes become `(add_pure a[i] (mul_pure a[j] zeta),
    sub_pure a[i] (mul_pure a[j] zeta))` respectively. -/
noncomputable def Spec.chunk_ntt_step_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (zeta : hacspec_ml_kem.parameters.FieldElement) (i j : Std.Usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  let t_fe :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure (a.val[j.val]!) zeta
  let a_minus_t :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure (a.val[i.val]!) t_fe
  let a_plus_t :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure (a.val[i.val]!) t_fe
  (a.set j a_minus_t).set i a_plus_t

/-- Pure NTT-layer-1 step at the chunk level. Mirrors the impl's
    8 sequential `ntt_step` calls at pairs (0,2)(1,3)(4,6)(5,7)
    (8,10)(9,11)(12,14)(13,15) with zetas z0,z0,z1,z1,z2,z2,z3,z3. -/
noncomputable def Spec.chunk_ntt_layer_1_step_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z0 z1 z2 z3 : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  let a1 := Spec.chunk_ntt_step_pure a  z0 0#usize  2#usize
  let a2 := Spec.chunk_ntt_step_pure a1 z0 1#usize  3#usize
  let a3 := Spec.chunk_ntt_step_pure a2 z1 4#usize  6#usize
  let a4 := Spec.chunk_ntt_step_pure a3 z1 5#usize  7#usize
  let a5 := Spec.chunk_ntt_step_pure a4 z2 8#usize 10#usize
  let a6 := Spec.chunk_ntt_step_pure a5 z2 9#usize 11#usize
  let a7 := Spec.chunk_ntt_step_pure a6 z3 12#usize 14#usize
  Spec.chunk_ntt_step_pure a7 z3 13#usize 15#usize

/-- Pure NTT-layer-2 step at the chunk level. Mirrors the impl's
    8 sequential `ntt_step` calls at pairs (0,4)(1,5)(2,6)(3,7)
    (8,12)(9,13)(10,14)(11,15) with zetas z0,z0,z0,z0,z1,z1,z1,z1. -/
noncomputable def Spec.chunk_ntt_layer_2_step_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z0 z1 : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  let a1 := Spec.chunk_ntt_step_pure a  z0 0#usize  4#usize
  let a2 := Spec.chunk_ntt_step_pure a1 z0 1#usize  5#usize
  let a3 := Spec.chunk_ntt_step_pure a2 z0 2#usize  6#usize
  let a4 := Spec.chunk_ntt_step_pure a3 z0 3#usize  7#usize
  let a5 := Spec.chunk_ntt_step_pure a4 z1 8#usize 12#usize
  let a6 := Spec.chunk_ntt_step_pure a5 z1 9#usize 13#usize
  let a7 := Spec.chunk_ntt_step_pure a6 z1 10#usize 14#usize
  Spec.chunk_ntt_step_pure a7 z1 11#usize 15#usize

/-- Pure NTT-layer-3 step at the chunk level. Mirrors the impl's
    8 sequential `ntt_step` calls at pairs (0,8)(1,9)(2,10)(3,11)
    (4,12)(5,13)(6,14)(7,15) all with the same zeta. -/
noncomputable def Spec.chunk_ntt_layer_3_step_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  let a1 := Spec.chunk_ntt_step_pure a  z 0#usize  8#usize
  let a2 := Spec.chunk_ntt_step_pure a1 z 1#usize  9#usize
  let a3 := Spec.chunk_ntt_step_pure a2 z 2#usize 10#usize
  let a4 := Spec.chunk_ntt_step_pure a3 z 3#usize 11#usize
  let a5 := Spec.chunk_ntt_step_pure a4 z 4#usize 12#usize
  let a6 := Spec.chunk_ntt_step_pure a5 z 5#usize 13#usize
  let a7 := Spec.chunk_ntt_step_pure a6 z 6#usize 14#usize
  Spec.chunk_ntt_step_pure a7 z 7#usize 15#usize

/-- Pure inverse-NTT step at the chunk level. Mirrors the impl's
    write order (`a[i] := add_pure a[j] a[i]`, then
    `a[j] := mul_pure (sub_pure a[j] a[i_original]) zeta`).
    Because the impl reads `vec[j]` (`= i1`) and `vec[i]` (`= i2`)
    BEFORE writing, the `(i, j)` lanes become:
      - new `a[i] = add_pure a[j] a[i]`  (barrett collapses to canonical sum)
      - new `a[j] = mul_pure (sub_pure a[j] a[i]) zeta`  (Mont-mul with zeta)
    where the reads on the RHS are at the ORIGINAL `a`. When `i = j` the
    second write wins (matching impl semantics). -/
noncomputable def Spec.chunk_inv_ntt_step_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (zeta : hacspec_ml_kem.parameters.FieldElement) (i j : Std.Usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  let a_i := a.val[i.val]!
  let a_j := a.val[j.val]!
  let new_i :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure a_j a_i
  let diff :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure a_j a_i
  let new_j :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure diff zeta
  (a.set i new_i).set j new_j

/-- Pure projection of `vector.portable.ntt.inv_ntt_layer_1_step`:
    8 sequential `Spec.chunk_inv_ntt_step_pure` calls at disjoint lane pairs
    `(0,2)(1,3)(4,6)(5,7)(8,10)(9,11)(12,14)(13,15)` with zetas
    `z0,z0,z1,z1,z2,z2,z3,z3`. Mirrors `Spec.chunk_ntt_layer_1_step_pure` on the same lane-pair sequence but with the inverse
    butterfly direction (`chunk_inv_ntt_step_pure` vs `chunk_ntt_step_pure`). -/
noncomputable def Spec.chunk_inv_ntt_layer_1_step_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z0 z1 z2 z3 : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  let a1 := Spec.chunk_inv_ntt_step_pure a  z0 0#usize  2#usize
  let a2 := Spec.chunk_inv_ntt_step_pure a1 z0 1#usize  3#usize
  let a3 := Spec.chunk_inv_ntt_step_pure a2 z1 4#usize  6#usize
  let a4 := Spec.chunk_inv_ntt_step_pure a3 z1 5#usize  7#usize
  let a5 := Spec.chunk_inv_ntt_step_pure a4 z2 8#usize 10#usize
  let a6 := Spec.chunk_inv_ntt_step_pure a5 z2 9#usize 11#usize
  let a7 := Spec.chunk_inv_ntt_step_pure a6 z3 12#usize 14#usize
  Spec.chunk_inv_ntt_step_pure a7 z3 13#usize 15#usize

/-- Pure projection of `vector.portable.ntt.inv_ntt_layer_2_step`:
    8 sequential `Spec.chunk_inv_ntt_step_pure` calls at disjoint lane pairs
    `(0,4)(1,5)(2,6)(3,7)(8,12)(9,13)(10,14)(11,15)` with zetas
    `z0,z0,z0,z0,z1,z1,z1,z1`. Mirror of `Spec.chunk_ntt_layer_2_step_pure`. -/
noncomputable def Spec.chunk_inv_ntt_layer_2_step_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z0 z1 : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  let a1 := Spec.chunk_inv_ntt_step_pure a  z0 0#usize  4#usize
  let a2 := Spec.chunk_inv_ntt_step_pure a1 z0 1#usize  5#usize
  let a3 := Spec.chunk_inv_ntt_step_pure a2 z0 2#usize  6#usize
  let a4 := Spec.chunk_inv_ntt_step_pure a3 z0 3#usize  7#usize
  let a5 := Spec.chunk_inv_ntt_step_pure a4 z1 8#usize 12#usize
  let a6 := Spec.chunk_inv_ntt_step_pure a5 z1 9#usize 13#usize
  let a7 := Spec.chunk_inv_ntt_step_pure a6 z1 10#usize 14#usize
  Spec.chunk_inv_ntt_step_pure a7 z1 11#usize 15#usize

/-- Pure projection of `vector.portable.ntt.inv_ntt_layer_3_step`:
    8 sequential `Spec.chunk_inv_ntt_step_pure` calls at disjoint lane pairs
    `(0,8)(1,9)(2,10)(3,11)(4,12)(5,13)(6,14)(7,15)` with a single zeta `z`.
    Mirror of `Spec.chunk_ntt_layer_3_step_pure`. -/
noncomputable def Spec.chunk_inv_ntt_layer_3_step_pure
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  let a1 := Spec.chunk_inv_ntt_step_pure a  z 0#usize  8#usize
  let a2 := Spec.chunk_inv_ntt_step_pure a1 z 1#usize  9#usize
  let a3 := Spec.chunk_inv_ntt_step_pure a2 z 2#usize 10#usize
  let a4 := Spec.chunk_inv_ntt_step_pure a3 z 3#usize 11#usize
  let a5 := Spec.chunk_inv_ntt_step_pure a4 z 4#usize 12#usize
  let a6 := Spec.chunk_inv_ntt_step_pure a5 z 5#usize 13#usize
  let a7 := Spec.chunk_inv_ntt_step_pure a6 z 6#usize 14#usize
  Spec.chunk_inv_ntt_step_pure a7 z 7#usize 15#usize

/-- Pure accumulating NTT-multiply at the chunk level. Mirrors the impl
    `vector.portable.ntt.accumulating_ntt_multiply`,
    which fans out 8 calls of `accumulating_ntt_multiply_binomials` with
    alternating ±zeta:
      pair i ∈ {0..7}, zeta_i = [z0, -z0, z1, -z1, z2, -z2, z3, -z3][i]
    For lane pair (2i, 2i+1):
      - acc[2i]   := acc[2i]   + a[2i]·b[2i]   + a[2i+1]·b[2i+1]·zeta_i
      - acc[2i+1] := acc[2i+1] + a[2i]·b[2i+1] + a[2i+1]·b[2i]
    All arithmetic in canonical `FieldElement` domain (the impl's
    Montgomery `bj·ζ_mont → mont_reduce → bj·ζ_canonical` collapses
    under `lift_fe_int`). -/
noncomputable def Spec.chunk_accumulating_ntt_multiply_pure
    (a b acc : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z0 z1 z2 z3 : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  let zeta_for_pair (i : Nat) : hacspec_ml_kem.parameters.FieldElement :=
    if i = 0 then z0
    else if i = 1 then libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure z0
    else if i = 2 then z1
    else if i = 3 then libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure z1
    else if i = 4 then z2
    else if i = 5 then libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure z2
    else if i = 6 then z3
    else if i = 7 then libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure z3
    else defaultFE
  Std.Array.make 16#usize
    ((List.range 16).map (fun ℓ =>
      let i := ℓ / 2
      let ζ := zeta_for_pair i
      if ℓ % 2 = 0 then
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure (acc.val[ℓ]!)
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (a.val[ℓ]!) (b.val[ℓ]!))
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                (a.val[ℓ + 1]!) (b.val[ℓ + 1]!))
              ζ))
      else
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure (acc.val[ℓ]!)
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (a.val[ℓ - 1]!) (b.val[ℓ]!))
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (a.val[ℓ]!) (b.val[ℓ - 1]!)))))
    (by simp)

/-- The PortableVector `Operations` instance used by Triples that
    target the impl monomorphised at `PortableVector`. The concrete
    instance is `vector.portable.vector_type.PortableVector.Insts.
    Libcrux_iot_ml_kemVectorTraitsOperations` in `Extraction/Funs.lean`;
    this alias decouples the FC statements from the precise extraction
    identifier in case aeneas re-mangles the name later. -/
@[reducible] def portable_ops_inst :
    libcrux_iot_ml_kem.vector.traits.Operations
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations

/-- Local `Inhabited` for 16-element FE arrays, used by `[!]` indexing
    inside `Spec.flatten_chunks`. -/
private noncomputable instance instInhabitedFEChunk_fcTargets :
    Inhabited (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :=
  ⟨Std.Array.make 16#usize (List.replicate 16 defaultFE) (by simp)⟩

/-- Local `Inhabited` for the 256-FE poly-ring array, used by `[!]` indexing
    inside `lift_matrix_from_slice`'s outer projection and the L6c
    accumulator-lift family. -/
private noncomputable instance instInhabitedFEPoly_fcTargets :
    Inhabited (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :=
  ⟨Std.Array.make 256#usize (List.replicate 256 defaultFE) List.length_replicate⟩

/-- Local `Inhabited` for the K-shape array-of-polys, used by `[!]` indexing
    inside `lift_matrix_from_slice`'s outer projection and `lift_vec`. -/
private noncomputable instance instInhabitedFEPolyVec_fcTargets
    {K : Std.Usize} :
    Inhabited (Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K) :=
  ⟨Std.Array.make K (List.replicate K.val default) List.length_replicate⟩

/-- Per-index zeta lookup: project lane `i` of
    `polynomial.ZETAS_TIMES_MONTGOMERY_R` into a canonical-domain FE.
    The Mont-domain table holds `Std.I16` values; `lift_fe_mont` strips
    one factor of R (yielding the canonical zeta). Out-of-range lookups
    default to `lift_fe_mont 0 = 0` via `[!]`. -/
noncomputable def Spec.zeta_at (i : Nat) : hacspec_ml_kem.parameters.FieldElement :=
  lift_fe_mont (libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[i]!)

/-- Chunk projection: extract the `k`-th 16-element chunk of a 256-array.
    Used to address the impl's `re.coefficients[k]` chunk slot at the
    spec level. -/
noncomputable def Spec.chunk_at
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) (k : Nat) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize ((List.range 16).map (fun j => p.val[16 * k + j]!))
    (by simp)

/-- Flatten 16 chunks of 16 FEs into a 256-array. Inverse of
    `Spec.chunk_at` under the `lift_poly` decomposition. -/
noncomputable def Spec.flatten_chunks
    (chunks : Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
                16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Std.Array.make 256#usize ((List.range 256).map (fun j =>
    (chunks.val[j / 16]!).val[j % 16]!)) (by simp)

/-- Pure projection of `ntt_at_layer_1` driver: 16 chunks, each chunk
    transformed by `chunk_ntt_layer_1_step_pure` with 4 zetas drawn
    from positions `zeta_i + 4k + {1..4}` in the global ZETAS table. -/
noncomputable def Spec.ntt_layer_1_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i : Std.Usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Spec.flatten_chunks
    (Std.Array.make 16#usize ((List.range 16).map (fun k =>
      Spec.chunk_ntt_layer_1_step_pure (Spec.chunk_at p k)
        (Spec.zeta_at (zeta_i.val + 4 * k + 1))
        (Spec.zeta_at (zeta_i.val + 4 * k + 2))
        (Spec.zeta_at (zeta_i.val + 4 * k + 3))
        (Spec.zeta_at (zeta_i.val + 4 * k + 4))))
      (by simp))

/-- Pure projection of `ntt_at_layer_2` driver: 16 chunks, each chunk
    transformed by `chunk_ntt_layer_2_step_pure` with 2 zetas at
    positions `zeta_i + 2k + {1, 2}`. -/
noncomputable def Spec.ntt_layer_2_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i : Std.Usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Spec.flatten_chunks
    (Std.Array.make 16#usize ((List.range 16).map (fun k =>
      Spec.chunk_ntt_layer_2_step_pure (Spec.chunk_at p k)
        (Spec.zeta_at (zeta_i.val + 2 * k + 1))
        (Spec.zeta_at (zeta_i.val + 2 * k + 2))))
      (by simp))

/-- Pure projection of `ntt_at_layer_3` driver: 16 chunks, each chunk
    transformed by `chunk_ntt_layer_3_step_pure` with 1 zeta at
    position `zeta_i + k + 1`. -/
noncomputable def Spec.ntt_layer_3_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i : Std.Usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Spec.flatten_chunks
    (Std.Array.make 16#usize ((List.range 16).map (fun k =>
      Spec.chunk_ntt_layer_3_step_pure (Spec.chunk_at p k)
        (Spec.zeta_at (zeta_i.val + k + 1))))
      (by simp))

/-- Pure projection of `invert_ntt.invert_ntt_at_layer_1` driver loop. 16 chunks; for chunk `k ∈ {0..15}` reads 4 zetas at
    Mont-table indices `[zeta_i - 4k - 1, zeta_i - 4k - 2, zeta_i - 4k - 3,
    zeta_i - 4k - 4]` (decreasing — opposite direction from the forward
    layer-1 driver) and applies `chunk_inv_ntt_layer_1_step_pure`. The
    impl initialises `zeta_i = 64` and decrements 4 per chunk, so the
    indices read across all 16 chunks span `[zeta_i - 64 .. zeta_i - 1]`.
    For the natural composer (top-level invert_ntt_montgomery) `zeta_i =
    64`, giving indices `[0..63]`. -/
noncomputable def Spec.invert_ntt_layer_1_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i : Std.Usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Spec.flatten_chunks
    (Std.Array.make 16#usize ((List.range 16).map (fun k =>
      Spec.chunk_inv_ntt_layer_1_step_pure (Spec.chunk_at p k)
        (Spec.zeta_at (zeta_i.val - 4 * k - 1))
        (Spec.zeta_at (zeta_i.val - 4 * k - 2))
        (Spec.zeta_at (zeta_i.val - 4 * k - 3))
        (Spec.zeta_at (zeta_i.val - 4 * k - 4))))
      (by simp))

/-- Pure projection of `invert_ntt.invert_ntt_at_layer_2` driver loop. 16 chunks; for chunk `k ∈ {0..15}` reads 2 zetas at
    Mont-table indices `[zeta_i - 2k - 1, zeta_i - 2k - 2]` (decreasing)
    and applies `chunk_inv_ntt_layer_2_step_pure`. The impl decrements
    `zeta_i` by 2 per chunk, so indices span `[zeta_i - 32 .. zeta_i - 1]`.
    Natural composer entry: `zeta_i = 32`, giving indices `[0..31]`. -/
noncomputable def Spec.invert_ntt_layer_2_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i : Std.Usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Spec.flatten_chunks
    (Std.Array.make 16#usize ((List.range 16).map (fun k =>
      Spec.chunk_inv_ntt_layer_2_step_pure (Spec.chunk_at p k)
        (Spec.zeta_at (zeta_i.val - 2 * k - 1))
        (Spec.zeta_at (zeta_i.val - 2 * k - 2))))
      (by simp))

/-- Pure projection of `invert_ntt.invert_ntt_at_layer_3` driver loop. 16 chunks; for chunk `k ∈ {0..15}` reads 1 zeta at
    Mont-table index `zeta_i - k - 1` (decreasing) and applies
    `chunk_inv_ntt_layer_3_step_pure`. The impl decrements `zeta_i` by 1
    per chunk, so indices span `[zeta_i - 16 .. zeta_i - 1]`. Natural
    composer entry: `zeta_i = 16`, giving indices `[0..15]`. -/
noncomputable def Spec.invert_ntt_layer_3_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i : Std.Usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Spec.flatten_chunks
    (Std.Array.make 16#usize ((List.range 16).map (fun k =>
      Spec.chunk_inv_ntt_layer_3_step_pure (Spec.chunk_at p k)
        (Spec.zeta_at (zeta_i.val - k - 1))))
      (by simp))

/-- Pure INVERSE NTT (Gentleman-Sande) butterfly between TWO chunks, a-side.
    Mirrors the impl `invert_ntt.inv_ntt_layer_int_vec_step_reduce`
    on the a-side write: `new_a[ℓ] := barrett_reduce(a[ℓ] + b[ℓ])`, which under
    `lift_fe_mont`'s canonical lift is simply `a[ℓ] + b[ℓ]` (no zeta on a-side
    for the inverse direction). -/
noncomputable def Spec.chunk_inv_pair_butterfly_a_pure
    (chunk_a chunk_b : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize ((List.range 16).map (fun ℓ =>
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
      (chunk_a.val[ℓ]!) (chunk_b.val[ℓ]!)))
    (by simp)

/-- Pure INVERSE NTT (Gentleman-Sande) butterfly between TWO chunks, b-side.
    Mirrors the impl b-side write: `new_b[ℓ] := mont_mul (2·b[ℓ] − barrett(a+b)) zeta_r`,
    which under `lift_fe_mont`'s canonical lift collapses to
    `(b[ℓ] − a[ℓ]) * z` (canonical, with `z = lift_fe_mont zeta_r` consuming
    the Mont-domain `R⁻¹` of the impl's `mont_mul`). -/
noncomputable def Spec.chunk_inv_pair_butterfly_b_pure
    (chunk_a chunk_b : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize ((List.range 16).map (fun ℓ =>
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
        (chunk_b.val[ℓ]!) (chunk_a.val[ℓ]!))
      z))
    (by simp)

/-- Per-chunk output for the INVERSE layer-4+ driver, parameterized by zeta
    source. Mirror of `Spec.chunk_at_layer_4_plus_pure` but
    using the inverse butterflies (`chunk_inv_pair_butterfly_{a,b}_pure`).
    Chunk position `c ∈ 0..16`; step_vec/group/offset/partner relations same
    as forward. -/
noncomputable def Spec.chunk_inv_at_layer_4_plus_pure
    (chunks : Std.Array
      (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize)
    (layer : Std.Usize) (zeta_fn : Nat → hacspec_ml_kem.parameters.FieldElement)
    (c : Nat) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  let step_vec := (1 <<< layer.val) / 16
  let group := c / (2 * step_vec)
  let offset := c % (2 * step_vec)
  let z := zeta_fn group
  if offset < step_vec then
    Spec.chunk_inv_pair_butterfly_a_pure
      (chunks.val[c]!) (chunks.val[c + step_vec]!)
  else
    Spec.chunk_inv_pair_butterfly_b_pure
      (chunks.val[c - step_vec]!) (chunks.val[c]!) z

/-- Pure projection of `invert_ntt.invert_ntt_at_layer_4_plus` for layers 4-7.
    Iterates `128 >>> layer` outer rounds, each round processing `step_vec`
    chunk-pairs at `(round*2*step_vec + j, round*2*step_vec + step_vec + j)`
    for `j ∈ 0..step_vec`. zeta_i decrements by 1 per outer round, with the
    constant zeta `polynomial.zeta (zeta_i_initial − 1 − round)` used across
    each round's inner loop.

    Note: unlike the forward layer-4+ which uses `zeta_i + group + 1`,
    inverse uses `zeta_i - 1 - group` (zeta_i decrements per outer iter). -/
noncomputable def Spec.invert_ntt_layer_4_plus_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i : Std.Usize) (layer : Std.Usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  let chunks0 : Std.Array
      (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize :=
    Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at p)) (by simp)
  let zeta_fn : Nat → hacspec_ml_kem.parameters.FieldElement :=
    fun group => Spec.zeta_at (zeta_i.val - 1 - group)
  Spec.flatten_chunks
    (Std.Array.make 16#usize ((List.range 16).map (fun c =>
      Spec.chunk_inv_at_layer_4_plus_pure chunks0 layer zeta_fn c))
      (by simp))

/-- Pure projection of `invert_ntt.invert_ntt_montgomery` top-level composer. Initial `zeta_i = 128` (= `COEFFICIENTS_IN_RING_ELEMENT / 2`).
    Composes seven layers in inverse order: layer 1, 2, 3, 4_plus(4),
    4_plus(5), 4_plus(6), 4_plus(7). zeta_i thread:
    `128 → 64 → 32 → 16 → 8 → 4 → 2 → 1` (final, discarded). -/
noncomputable def Spec.invert_ntt_montgomery_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  let p1 := Spec.invert_ntt_layer_1_pure p 128#usize
  let p2 := Spec.invert_ntt_layer_2_pure p1 64#usize
  let p3 := Spec.invert_ntt_layer_3_pure p2 32#usize
  let p4 := Spec.invert_ntt_layer_4_plus_pure p3 16#usize 4#usize
  let p5 := Spec.invert_ntt_layer_4_plus_pure p4 8#usize 5#usize
  let p6 := Spec.invert_ntt_layer_4_plus_pure p5 4#usize 6#usize
  Spec.invert_ntt_layer_4_plus_pure p6 2#usize 7#usize

/-- Pure projection of `polynomial.PolynomialRingElement.accumulating_ntt_multiply`:
    16 chunks of accumulating NTT-multiplication. For chunk k ∈ {0..15},
    applies `chunk_accumulating_ntt_multiply_pure` with the 4 canonical-domain
    zetas at `Spec.zeta_at (64 + 4*k + m)` for `m ∈ {0..3}` (matching the
    impl's `polynomial.zeta` lookups at `64 + 4*k + m` per chunk —). -/
noncomputable def Spec.accumulating_ntt_multiply_pure
    (a b acc : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Spec.flatten_chunks
    (Std.Array.make 16#usize ((List.range 16).map (fun k =>
      Spec.chunk_accumulating_ntt_multiply_pure
        (Spec.chunk_at a k) (Spec.chunk_at b k) (Spec.chunk_at acc k)
        (Spec.zeta_at (64 + 4 * k))
        (Spec.zeta_at (64 + 4 * k + 1))
        (Spec.zeta_at (64 + 4 * k + 2))
        (Spec.zeta_at (64 + 4 * k + 3))))
      (by simp))

/-! ### Spec helpers for layer 4+ (cross-chunk butterflies). -/

/-- Pure NTT butterfly between TWO chunks, applied to all 16 lanes
    simultaneously. Mirrors the impl's `ntt_layer_int_vec_step`:
    lane ℓ in chunk_a becomes `chunk_a[ℓ] + chunk_b[ℓ] * z` (plain ZMod
    via Montgomery cancellation in `lift_fe_mont`); lane ℓ in chunk_b
    becomes `chunk_a[ℓ] - chunk_b[ℓ] * z`. -/
noncomputable def Spec.chunk_pair_butterfly_a_pure
    (chunk_a chunk_b : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize ((List.range 16).map (fun ℓ =>
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure (chunk_a.val[ℓ]!)
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
        (chunk_b.val[ℓ]!) z)))
    (by simp)

noncomputable def Spec.chunk_pair_butterfly_b_pure
    (chunk_a chunk_b : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize ((List.range 16).map (fun ℓ =>
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure (chunk_a.val[ℓ]!)
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
        (chunk_b.val[ℓ]!) z)))
    (by simp)

/-- Per-chunk output for the layer-4+ driver, parameterized by zeta source.
    For chunk position `c ∈ 0..16`:
    - `step_vec := (1 <<< layer) / 16` (= 1, 2, 4, 8 for layers 4..7).
    - `group := c / (2 * step_vec)`, `offset := c % (2 * step_vec)`.
    - If `offset < step_vec`: c is the a-side; partner is `c + step_vec`.
      New chunk = chunk_a + chunk_partner * zeta_fn group.
    - Else: c is the b-side; partner is `c - step_vec`.
      New chunk = chunk_partner - chunk_c * zeta_fn group.
    The `zeta_fn : Nat → FE` lets layer-4-6 use the zeta table and
    layer-7 use the constant `lift_fe_mont (-1600)`. -/
noncomputable def Spec.chunk_at_layer_4_plus_pure
    (chunks : Std.Array
      (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize)
    (layer : Std.Usize) (zeta_fn : Nat → hacspec_ml_kem.parameters.FieldElement)
    (c : Nat) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  let step_vec := (1 <<< layer.val) / 16
  let group := c / (2 * step_vec)
  let offset := c % (2 * step_vec)
  let z := zeta_fn group
  if offset < step_vec then
    Spec.chunk_pair_butterfly_a_pure
      (chunks.val[c]!) (chunks.val[c + step_vec]!) z
  else
    Spec.chunk_pair_butterfly_b_pure
      (chunks.val[c - step_vec]!) (chunks.val[c]!) z

/-- Pure projection of `ntt_at_layer_4_plus` driver for layers 4, 5, 6.
    Iterates `2 * (128 >>> layer)` chunk-pair butterflies (= 16 chunks
    touched once each), with zeta_offset incrementing every `step_vec`
    inner butterflies (8 distinct zetas across the layer for layers 4-6). -/
noncomputable def Spec.ntt_at_layer_4_plus_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i : Std.Usize) (layer : Std.Usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  let chunks0 : Std.Array
      (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize :=
    Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at p)) (by simp)
  let zeta_fn : Nat → hacspec_ml_kem.parameters.FieldElement :=
    fun group => Spec.zeta_at (zeta_i.val + group + 1)
  Spec.flatten_chunks
    (Std.Array.make 16#usize ((List.range 16).map (fun c =>
      Spec.chunk_at_layer_4_plus_pure chunks0 layer zeta_fn c))
      (by simp))

/-- The constant zeta used by `ntt_at_layer_7`. Impl uses
    `multiply_by_constant scratch1 ((-1600)#i16)` (PLAIN multiplication,
    not Mont — `multiply_by_constant_fc` lifts via `lift_fe`, not
    `lift_fe_mont`). Lifted value is `lift_fe ((-1600)#i16)`, a fixed
    element of the field. -/
noncomputable def Spec.zeta_layer_7 :
    hacspec_ml_kem.parameters.FieldElement :=
  lift_fe ((-1600)#i16)

/-- Pure projection of `ntt_at_layer_7` driver. Single layer of 8
    chunk-pair butterflies between chunks `(j, j+8)` for j ∈ 0..8, all
    with the constant zeta `Spec.zeta_layer_7`. -/
noncomputable def Spec.ntt_at_layer_7_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  let chunks0 : Std.Array
      (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize :=
    Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at p)) (by simp)
  let zeta_fn : Nat → hacspec_ml_kem.parameters.FieldElement :=
    fun _ => Spec.zeta_layer_7
  Spec.flatten_chunks
    (Std.Array.make 16#usize ((List.range 16).map (fun c =>
      Spec.chunk_at_layer_4_plus_pure chunks0 7#usize zeta_fn c))
      (by simp))

/-- Pure projection of the full hacspec `ntt.ntt`. Composes layer-7,
    three layer-4_plus calls (layers 6, 5, 4), layer-3, layer-2, layer-1
    + final barrett, mirroring the impl `ntt_binomially_sampled_ring_element`
    shape with cumulative zeta_i offsets:
    - layer 7: zeta_i unchanged (constant zeta, no table use).
    - layer 6: zeta_i starts at 1, advances by `128 >>> 6 = 2` to 3.
    - layer 5: starts at 3, advances by `128 >>> 5 = 4` to 7.
    - layer 4: starts at 7, advances by `128 >>> 4 = 8` to 15.
    - layer 3: starts at 15, advances by 16 to 31.
    - layer 2: starts at 31, advances by 32 to 63.
    - layer 1: starts at 63, advances by 64 to 127.
    Total zetas: 0 + 2 + 4 + 8 + 16 + 32 + 64 = 126 (indices 1..126 used). -/
noncomputable def Spec.ntt_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  let p7 := Spec.ntt_at_layer_7_pure p
  let p6 := Spec.ntt_at_layer_4_plus_pure p7 1#usize 6#usize
  let p5 := Spec.ntt_at_layer_4_plus_pure p6 3#usize 5#usize
  let p4 := Spec.ntt_at_layer_4_plus_pure p5 7#usize 4#usize
  let p3 := Spec.ntt_layer_3_pure p4 15#usize
  let p2 := Spec.ntt_layer_2_pure p3 31#usize
  let p1 := Spec.ntt_layer_1_pure p2 63#usize
  Spec.Pure.polynomial.poly_barrett_reduce_pure p1

/-- Pure projection of `ntt_vector_u`'s full NTT chain. Mirrors `Spec.ntt_pure`
    but uses `Spec.ntt_at_layer_4_plus_pure p 0 7` for the first step instead
    of `Spec.ntt_at_layer_7_pure p`. The two specs are mathematically
    equivalent in `ZMod 3329` (see `Spec.zeta_at_one_eq_layer_7` below: the
    Mont-multiply layer-7 step via `ZETAS_TIMES_MONTGOMERY_R[1] = -758` and
    the plain-multiply layer-7 step with constant `-1600` produce the same
    field element). They differ structurally because `ntt_vector_u`'s impl
    uses the Mont path while `ntt_binomially_sampled_ring_element` uses the
    plain path; we target each spec at the impl actually used. -/
noncomputable def Spec.ntt_pure_vec_u
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  let p7 := Spec.ntt_at_layer_4_plus_pure p 0#usize 7#usize
  let p6 := Spec.ntt_at_layer_4_plus_pure p7 1#usize 6#usize
  let p5 := Spec.ntt_at_layer_4_plus_pure p6 3#usize 5#usize
  let p4 := Spec.ntt_at_layer_4_plus_pure p5 7#usize 4#usize
  let p3 := Spec.ntt_layer_3_pure p4 15#usize
  let p2 := Spec.ntt_layer_2_pure p3 31#usize
  let p1 := Spec.ntt_layer_1_pure p2 63#usize
  Spec.Pure.polynomial.poly_barrett_reduce_pure p1

/-- `ZETAS_TIMES_MONTGOMERY_R[1]! = -758#i16`. -/
theorem Spec.ZETAS_TIMES_MONTGOMERY_R_get_one :
    libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[1]!
      = ((-758)#i16 : Std.I16) := by
  unfold libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R
  decide

/-- Spec-level zeta equivalence between L3.7 (plain `multiply_by_constant`)
    and L3.4_plus at layer=7 (Mont multiply through `ZETAS_TIMES_MONTGOMERY_R[1]`).

    In `ZMod 3329`: `Spec.zeta_at 1 = lift_fe_mont (-758) = lift_fe ((-758) * 169)
    = lift_fe (-1600) = Spec.zeta_layer_7` (since `-758 * 169 ≡ -1600 mod 3329`).
    Both equal the canonical field element 1729. -/
theorem Spec.zeta_at_one_eq_layer_7 :
    Spec.zeta_at 1 = Spec.zeta_layer_7 := by
  unfold Spec.zeta_at Spec.zeta_layer_7
  rw [Spec.ZETAS_TIMES_MONTGOMERY_R_get_one]
  unfold lift_fe_mont lift_fe
    libcrux_iot_ml_kem.Spec.i16_to_spec_fe_mont
    libcrux_iot_ml_kem.Spec.i16_to_spec_fe_plain
  congr 1

/-- Per-chunk pure projection of `polynomial.add_error_reduce`: for the
    `ℓ`-th lane of a 16-lane chunk,
    `out[ℓ] := self_chunk[ℓ] · lift_fe_mont(1441#i16) + error_chunk[ℓ]`. -/
noncomputable def Spec.chunk_add_error_reduce_pure
    (self_chunk error_chunk :
        Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize ((List.range 16).map (fun ℓ =>
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
        (self_chunk.val[ℓ]!) (lift_fe_mont (1441#i16)))
      (error_chunk.val[ℓ]!)))
    (by simp)

/-- Per-chunk pure projection of `polynomial.add_standard_error_reduce`:
    for the `ℓ`-th lane,
    `out[ℓ] := self_chunk[ℓ] · lift_fe_mont(1353#i16) + error_chunk[ℓ]`,
    where `1353 ≡ R² (mod q)` (cf. `libcrux_iot_ml_kem.Spec.NumericKeystones.mont_1353_eq_RR_mod_q`). -/
noncomputable def Spec.chunk_add_standard_error_reduce_pure
    (self_chunk error_chunk :
        Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize ((List.range 16).map (fun ℓ =>
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
        (self_chunk.val[ℓ]!) (lift_fe_mont (1353#i16)))
      (error_chunk.val[ℓ]!)))
    (by simp)

/-- Per-chunk pure projection of `polynomial.add_message_error_reduce`:
    for the `ℓ`-th lane,
    `out[ℓ] := result_chunk[ℓ] · lift_fe_mont(1441#i16)
              + (self_chunk[ℓ] + message_chunk[ℓ])`.
    The impl barrett-reduces this sum, but `barrett_pure` is identity
    after `lift_fe`. -/
noncomputable def Spec.chunk_add_message_error_reduce_pure
    (self_chunk message_chunk result_chunk :
        Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize ((List.range 16).map (fun ℓ =>
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
        (result_chunk.val[ℓ]!) (lift_fe_mont (1441#i16)))
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
        (self_chunk.val[ℓ]!) (message_chunk.val[ℓ]!))))
    (by simp)

/-- Pure projection of `polynomial.add_error_reduce`. The hacspec spec
    does not expose a dedicated `add_error_reduce` at the poly level —
    the impl's behaviour is "multiply by R/128 then add error then
    barrett". chunk `k ∈ 0..16` and lane `ℓ`:
    `out_chunk[k][ℓ] := self[k][ℓ] · lift_fe_mont(1441#i16) + error[k][ℓ]`,
    flattened to a 256-array via `Spec.flatten_chunks`. -/
noncomputable def Spec.add_error_reduce_pure
    (self error : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Spec.flatten_chunks
    (Std.Array.make 16#usize ((List.range 16).map (fun k =>
      Spec.chunk_add_error_reduce_pure
        (Spec.chunk_at self k) (Spec.chunk_at error k)))
      (by simp))

/-- Pure projection of `polynomial.add_standard_error_reduce`. chunk
    `k` and lane `ℓ`:
    `out[k][ℓ] := self[k][ℓ] · lift_fe_mont(1353#i16) + error[k][ℓ]`
    (1353 ≡ R² mod q lifts to `× R` in canonical domain). -/
noncomputable def Spec.add_standard_error_reduce_pure
    (self error : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Spec.flatten_chunks
    (Std.Array.make 16#usize ((List.range 16).map (fun k =>
      Spec.chunk_add_standard_error_reduce_pure
        (Spec.chunk_at self k) (Spec.chunk_at error k)))
      (by simp))

/-- Pure projection of `polynomial.add_message_error_reduce`. chunk
    `k` and lane `ℓ`:
    `out[k][ℓ] := result[k][ℓ] · lift_fe_mont(1441#i16) +
                  (self[k][ℓ] + message[k][ℓ])`. -/
noncomputable def Spec.add_message_error_reduce_pure
    (self message : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (result : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Spec.flatten_chunks
    (Std.Array.make 16#usize ((List.range 16).map (fun k =>
      Spec.chunk_add_message_error_reduce_pure
        (Spec.chunk_at self k) (Spec.chunk_at message k) (Spec.chunk_at result k)))
      (by simp))

/-- Pure projection of poly-level `reducing_from_i32_array`. Direct 256-lane
    construction: for `i ∈ 0..256`,
    `out[i] := Spec.mont_reduce_pure (lift_fe_int array.val[i].val)`.
    Mirrors `Spec.chunk_reducing_from_i32_array_pure` per chunk-of-16. -/
noncomputable def Spec.poly_reducing_from_i32_array_pure
    (array : Slice Std.I32) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Std.Array.make 256#usize
    ((List.range 256).map (fun i =>
      Spec.mont_reduce_pure (lift_fe_int (array.val[i]!).val)))
    (by simp)

/-- Per-chunk pure projection of `polynomial.subtract_reduce`: for the
    `ℓ`-th lane of a 16-lane chunk,
    `out[ℓ] := self_chunk[ℓ] - b_chunk[ℓ] * lift_fe_mont (1441#i16)`.

    This is the chunk-level building block used by `Spec.subtract_reduce_pure`
    (which flattens 16 chunks via `Spec.flatten_chunks`). -/
noncomputable def Spec.chunk_subtract_reduce_pure
    (self_chunk b_chunk : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Std.Array.make 16#usize ((List.range 16).map (fun ℓ =>
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure (self_chunk.val[ℓ]!)
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
        (b_chunk.val[ℓ]!) (lift_fe_mont (1441#i16)))))
    (by simp)

/-- Pure projection of `polynomial.subtract_reduce`. The hacspec spec
    computes `self - b`, but the impl fuses a Mont-multiply on b by the
    constant `1441#i16` BEFORE the subtract. the C.4 commute
    `1441 · R⁻¹ ≡ 1441 · 169 ≡ 512 (mod q)`, this is equivalent in
    ZMod q to computing `self - 512 · b` pointwise, NOT `self - b`.

    Hence we model the impl directly: per chunk `k ∈ 0..16` and lane
    `ℓ ∈ 0..16`,
    `out_chunk[k][ℓ] := self_chunk[k][ℓ] - b_chunk[k][ℓ] * lift_fe_mont (1441#i16)`,
    then flatten 16 chunks to a 256-array via `Spec.flatten_chunks`. The
    chunk-level form mirrors the impl's chunk-loop structure and pairs
    with `flatten_chunks_eq_lift_poly_fc` in the FC closure proof. -/
noncomputable def Spec.subtract_reduce_pure
    (self b : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Spec.flatten_chunks
    (Std.Array.make 16#usize ((List.range 16).map (fun k =>
      Spec.chunk_subtract_reduce_pure
        (Spec.chunk_at self k) (Spec.chunk_at b k)))
      (by simp))

-- `Spec.sample_matrix_A_pure` is declared above (with `lift_matrix_from_seed`).

/-! ## §Audit — the lift bridge is faithful and non-degenerate

    The L7 matrix-level FC theorems state spec/impl equivalence *through*
    the `lift_*` tower (`lift_fe → lift_poly → lift_vec /
    lift_matrix_from_slice`). Both sides of each POST equation have already
    been pushed through `lift`, so the theorem is only as strong as `lift`
    is information-preserving: a degenerate `lift` (e.g. one collapsing every
    lane to `0`) would make the equation vacuously true while saying nothing
    about the impl.

    Auditing the tower therefore reduces to two checkable facts about the
    single leaf map `lift_fe`, which this section states and proves so a
    reviewer can trust the bridge from **lemma statements** rather than by
    reading the `lift_*` bodies:

    * **Faithfulness** (`lift_fe_spec`) — projecting a lifted lane back with
      `zmodOfFE` returns exactly the impl lane taken mod `q = 3329`. So `lift`
      *is* the intended reduction, and forgets nothing beyond the residue class.
    * **Injectivity up to `q`** (`lift_fe_inj_mod`) — equal lifts force equal
      lanes mod `q`. This rules out the "constant/collapsing lift" vacuity mode
      by a fact, not by inspecting code.

    Everything above `lift_fe` is purely structural (`List.map` over the fixed
    16×16 lane decomposition and the K-shaped vector / K×K matrix reshapes).
    The `*_spec` / `*_inj_mod` lemmas below lift both facts up each structural
    layer, so the whole tower feeding L7.1's POST — `lift_matrix_from_slice`
    (inputs), `lift_vec` (inputs and the `lift_vec p.1` output) — is certified
    faithful and injective mod `q` position-by-position. Concretely,
    `lift_vec_inj_mod` applied to the output says: the L7.1 equation pins every
    coefficient lane of the impl's `t_as_ntt` to the spec's value mod `q`.

    (This is exactly the "equal as elements of `ZMod 3329`, position-by-position"
    guarantee; it does not constrain the concrete i16 representative beyond its
    residue class — see the README trust-boundary discussion.) -/

/-- **Faithfulness of the leaf lift.** Lifting an `Std.I16` lane to a
    `FieldElement` and projecting back with `zmodOfFE` yields exactly the
    lane taken mod `q = 3329`. The bridge is the intended reduction. -/
theorem lift_fe_spec (x : Std.I16) :
    zmodOfFE (lift_fe x) = (x.val : ZMod 3329) := by
  unfold lift_fe
  rw [zmodOfFE_feOfZMod, i16_to_spec_fe_plain_unfold]

/-- **Injectivity of the leaf lift, up to `q`.** Equal lifts force equal
    lanes mod `q`. Rules out a degenerate/collapsing `lift_fe`. -/
theorem lift_fe_inj_mod {x y : Std.I16} (h : lift_fe x = lift_fe y) :
    (x.val : ZMod 3329) = (y.val : ZMod 3329) := by
  have h' := congrArg zmodOfFE h
  rwa [lift_fe_spec, lift_fe_spec] at h'

/-- **Impl lane `x` is the canonical *centered* Barrett representative of spec
    field element `f`.**

    Shared per-lane output relation for all four L7 POSTs. Two conjuncts:
    * `x.natAbs ≤ 1664 = ⌊q/2⌋` — the symmetric Barrett range, a *complete*
      residue system of exactly `q = 3329` values, so together with the residue
      the representative `x` is **unique**;
    * `(x : ZMod 3329) = f` — the residue equality, stated directly in `ZMod 3329`
      (no `.toNat`, no sign correction). -/
def LaneMatches (x : Int) (f : ZMod 3329) : Prop :=
  x.natAbs ≤ 1664 ∧ (x : ZMod 3329) = f

/-- Bridge: an impl lane `x` with the tight centered bound `|x| ≤ 1664` matches
    (via `LaneMatches`) the residue of its own leaf lift `zmodOfFE (lift_fe x)`.
    Discharges the per-lane obligation in the L7 endgames after the spec residue
    has been rewritten to `zmodOfFE (lift_fe x)` through the §Audit getters. -/
theorem laneMatches_lift_fe (x : Std.I16) (h : x.val.natAbs ≤ 1664) :
    LaneMatches x.val (zmodOfFE (lift_fe x)) :=
  ⟨h, (lift_fe_spec x).symm⟩

/-- **An impl ring element matches a spec ring element.** Lane-wise `LaneMatches`
    over all 256 coefficients: each impl coefficient is the unique centered Barrett
    representative of the corresponding spec residue. The shared output relation
    for the single-polynomial L7 POSTs (L7.3 `compute_ring_element_v`,
    L7.4 `compute_message`). -/
def PolyMatches
    (impl : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (spec : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) : Prop :=
  ∀ ℓ : Nat, ℓ < 256 →
    LaneMatches ((impl.coefficients.val[ℓ / 16]!).elements.val[ℓ % 16]!.val)
      (zmodOfFE (spec.val[ℓ]!))

/-- **An impl vector matches a spec vector.** Row-wise `PolyMatches` over the `K`
    ring elements. The shared output relation for the vector-valued L7 POSTs
    (L7.1 `compute_As_plus_e`, L7.2 `compute_vector_u`).

    The impl rows are passed as the underlying `List` (`.val`) so this serves both
    the `Std.Array`-backed output of `compute_As_plus_e` and the `Slice`-backed
    output of `compute_vector_u` uniformly. -/
def VecMatches {K : Std.Usize}
    (impl : List
              (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (spec : Std.Array
              (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K) : Prop :=
  ∀ r : Nat, r < K.val → PolyMatches (impl[r]!) (spec.val[r]!)

/-- Lane getter for `lift_poly`: the `j`-th of the 256 output lanes is
    `lift_fe` of the impl coefficient at chunk `j / 16`, lane `j % 16`. -/
theorem lift_poly_getElem
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (j : Nat) (hj : j < 256) :
    (lift_poly re).val[j]!
      = lift_fe (re.coefficients.val[j / 16]!).elements.val[j % 16]! := by
  unfold lift_poly
  show ((List.range 256).map (fun j =>
          lift_fe (re.coefficients.val[j / 16]!).elements.val[j % 16]!))[j]! = _
  have h_len : ((List.range 256).map (fun j =>
          lift_fe (re.coefficients.val[j / 16]!).elements.val[j % 16]!)).length = 256 := by simp
  rw [getElem!_pos _ j (by rw [h_len]; exact hj)]
  rw [List.getElem_map, List.getElem_range]

/-- **Faithfulness of `lift_poly`** (per lane). -/
theorem lift_poly_spec
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (j : Nat) (hj : j < 256) :
    zmodOfFE ((lift_poly re).val[j]!)
      = (((re.coefficients.val[j / 16]!).elements.val[j % 16]!).val : ZMod 3329) := by
  rw [lift_poly_getElem re j hj, lift_fe_spec]

/-- **Injectivity of `lift_poly`, up to `q`** (per lane). -/
theorem lift_poly_inj_mod
    (re re' : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (j : Nat) (hj : j < 256) (h : lift_poly re = lift_poly re') :
    (((re.coefficients.val[j / 16]!).elements.val[j % 16]!).val : ZMod 3329)
      = (((re'.coefficients.val[j / 16]!).elements.val[j % 16]!).val : ZMod 3329) := by
  rw [← lift_poly_spec re j hj, ← lift_poly_spec re' j hj, h]

/-- Row getter for `lift_vec`: the `r`-th of the K output rows is
    `lift_poly` of the impl's `r`-th ring element. -/
theorem lift_vec_getElem {K : Std.Usize}
    (v : Std.Array
          (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (r : Nat) (hr : r < K.val) :
    (lift_vec v).val[r]! = lift_poly (v.val[r]!) := by
  unfold lift_vec
  show (v.val.map lift_poly)[r]! = lift_poly (v.val[r]!)
  have h_len : (v.val.map lift_poly).length = K.val := by
    rw [List.length_map]; exact v.property
  rw [getElem!_pos _ r (by rw [h_len]; exact hr)]
  rw [List.getElem_map, getElem!_pos v.val r (by rw [v.property]; exact hr)]

/-- **Faithfulness of `lift_vec`** (per row, per lane). -/
theorem lift_vec_spec {K : Std.Usize}
    (v : Std.Array
          (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (r : Nat) (hr : r < K.val) (j : Nat) (hj : j < 256) :
    zmodOfFE ((lift_vec v).val[r]!.val[j]!)
      = (((v.val[r]!.coefficients.val[j / 16]!).elements.val[j % 16]!).val : ZMod 3329) := by
  rw [lift_vec_getElem v r hr, lift_poly_spec _ j hj]

/-- **Injectivity of `lift_vec`, up to `q`** (per row, per lane).
    Applied to L7.1's output `lift_vec p.1`, this is precisely the
    guarantee that the theorem pins every impl coefficient lane to the
    spec value mod `q`. -/
theorem lift_vec_inj_mod {K : Std.Usize}
    (u v : Std.Array
          (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (r : Nat) (hr : r < K.val) (j : Nat) (hj : j < 256)
    (h : lift_vec u = lift_vec v) :
    (((u.val[r]!.coefficients.val[j / 16]!).elements.val[j % 16]!).val : ZMod 3329)
      = (((v.val[r]!.coefficients.val[j / 16]!).elements.val[j % 16]!).val : ZMod 3329) := by
  rw [← lift_vec_spec u r hr j hj, ← lift_vec_spec v r hr j hj, h]

/-- Entry getter for `lift_matrix_from_slice`: under the column-major
    convention (outer index = column `j`, inner index = row `i`), the
    `(j, i)` entry is `lift_poly` of the flat row-major slot `i * K + j`.
    Mirrors `Matrix.Common.matrix.entry_fc`'s reshape. -/
theorem lift_matrix_from_slice_getElem
    (slice : Slice
              (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (K : Std.Usize) (i j : Nat) (hi : i < K.val) (hj : j < K.val) :
    (lift_matrix_from_slice slice K).val[j]!.val[i]!
      = lift_poly slice.val[i * K.val + j]! := by
  unfold lift_matrix_from_slice
  have h_outer_len : ((List.range K.val).map (fun j' =>
        Std.Array.make K ((List.range K.val).map (fun i' =>
          lift_poly slice.val[i' * K.val + j']!)) (by simp))).length = K.val := by
    rw [List.length_map, List.length_range]
  show ((((List.range K.val).map (fun j' =>
          Std.Array.make K ((List.range K.val).map (fun i' =>
            lift_poly slice.val[i' * K.val + j']!)) (by simp)))[j]!).val[i]!) = _
  rw [getElem!_pos _ j (by rw [h_outer_len]; exact hj)]
  rw [List.getElem_map, List.getElem_range]
  show ((List.range K.val).map (fun i' =>
          lift_poly slice.val[i' * K.val + j]!))[i]! = _
  have h_inner_len : ((List.range K.val).map (fun i' =>
        lift_poly slice.val[i' * K.val + j]!)).length = K.val := by
    rw [List.length_map, List.length_range]
  rw [getElem!_pos _ i (by rw [h_inner_len]; exact hi)]
  rw [List.getElem_map, List.getElem_range]

/-- **Faithfulness of `lift_matrix_from_slice`** (per entry, per lane). -/
theorem lift_matrix_from_slice_spec
    (slice : Slice
              (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (K : Std.Usize) (i j : Nat) (hi : i < K.val) (hj : j < K.val)
    (ℓ : Nat) (hℓ : ℓ < 256) :
    zmodOfFE ((lift_matrix_from_slice slice K).val[j]!.val[i]!.val[ℓ]!)
      = (((slice.val[i * K.val + j]!.coefficients.val[ℓ / 16]!).elements.val[ℓ % 16]!).val
          : ZMod 3329) := by
  rw [lift_matrix_from_slice_getElem slice K i j hi hj, lift_poly_spec _ ℓ hℓ]

/-- **Injectivity of `lift_matrix_from_slice`, up to `q`** (per entry, per lane). -/
theorem lift_matrix_from_slice_inj_mod
    (s t : Slice
              (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (K : Std.Usize) (i j : Nat) (hi : i < K.val) (hj : j < K.val)
    (ℓ : Nat) (hℓ : ℓ < 256)
    (h : lift_matrix_from_slice s K = lift_matrix_from_slice t K) :
    (((s.val[i * K.val + j]!.coefficients.val[ℓ / 16]!).elements.val[ℓ % 16]!).val : ZMod 3329)
      = (((t.val[i * K.val + j]!.coefficients.val[ℓ / 16]!).elements.val[ℓ % 16]!).val
          : ZMod 3329) := by
  rw [← lift_matrix_from_slice_spec s K i j hi hj ℓ hℓ,
      ← lift_matrix_from_slice_spec t K i j hi hj ℓ hℓ, h]


end libcrux_iot_ml_kem.Spec.Lift
