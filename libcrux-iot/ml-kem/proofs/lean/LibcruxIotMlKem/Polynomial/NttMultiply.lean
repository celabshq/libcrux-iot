/-
  # `Polynomial/NttMultiply.lean` — extracted from `FCTargets.lean` §ntt_multiply.
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

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_kem.Polynomial.NttMultiply
open libcrux_iot_ml_kem.InvertNtt libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.PolyOpsFc libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec

/-! ## §L2.8 / §L6.3 — NTT-multiply scaffolding.

    Statement skeletons for the NTT-domain multiplication chain that
    the L7 matrix-level targets depend on.

    Naming convention (distinguishes vector-level from polynomial-level
    since both impl namespaces define `accumulating_ntt_multiply`):
      L2.8 base   : `accumulating_ntt_multiply_fc`  (vector chunk, I32 slice)
      L6.3 base   : `accumulating_ntt_multiply_poly_fc`  (polynomial, I32[256])

    Helpers introduced here (also sorry-bodied, filled by sub-dispatches):
      `ntt_multiply_base_case_post` : Prop predicate captured by L2.8.
        Body (the per-pair degree-2 polynomial multiply mod (X²−ζ²)
        equation) is filled by L2.8b (`ntt_multiply_base_case_alg`).
      `Spec.multiply_ntts_pure` : pure projection of hacspec
        `ntt.multiply_ntts`. Body is filled by an M.1 pre-stage
        commit before L6.3b dispatches its FC equation.

    Cache variants (`_fill_cache`, `_use_cache`) are deferred to L2.8d
    / L6.3c sibling-adaptation dispatches and are NOT locked here. -/

/-- Pure projection of `hacspec_ml_kem.ntt.multiply_ntts` (the N=256
    polynomial NTT-domain multiply spec). The `.ok` value of the
    hacspec `Result` is the spec polynomial; on `.fail` (unreachable
    for canonical inputs) we default to the zero polynomial.

    Used by L6.3 locked POST as the spec-side RHS, anchoring the
    impl's I32 accumulator (after L1.10's Mont-reduce) to the hacspec
    `multiply_ntts` projection. Composes with the L6.3a per-chunk
    decomposition + L2.8's `Spec.chunk_reducing_from_i32_array_pure`
    chain. -/
noncomputable def Spec.multiply_ntts_pure
    (p1 p2 : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  match hacspec_ml_kem.ntt.multiply_ntts p1 p2 with
  | .ok r => r
  | _ => default

/-- Pure no-accumulate base-case NTT multiply (the "product" part).

    Given Mont-domain lifts of `lhs`, `rhs` (16 lanes each) and 4
    Mont-domain zetas, computes the 16-lane product of the per-pair
    degree-2 polynomial multiplies mod (X²−ζ²). Each pair `j ∈ 0..7`
    consumes effective zeta `[zeta0, -zeta0, zeta1, -zeta1, zeta2,
    -zeta2, zeta3, -zeta3][j]` and produces
    `product[2j]   = a[2j]·b[2j]   + a[2j+1]·b[2j+1]·ζ_j`
    `product[2j+1] = a[2j]·b[2j+1] + a[2j+1]·b[2j]`.

    All arithmetic is in `FieldElement` (ZMod 3329). The accumulating
    variant `ntt_multiply_base_case_alg` is the pointwise sum of this
    product with an initial accumulator (`Spec.chunk_add_pure acc
    product`). Separating the two simplifies the per-pair commute
    (A.16/A.17/A.18 fire directly on the product) and makes the L7
    bridge to hacspec `multiply_ntts` (non-accumulating) trivial when
    the initial accumulator is zero. -/
noncomputable def Spec.ntt_multiply_pure_no_acc
    (lhs_m rhs_m : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (zeta0_m zeta1_m zeta2_m zeta3_m : hacspec_ml_kem.parameters.FieldElement) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  let neg := libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure
  let add := libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
  let mul := libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
  let zetas : List hacspec_ml_kem.parameters.FieldElement :=
    [zeta0_m, neg zeta0_m, zeta1_m, neg zeta1_m,
     zeta2_m, neg zeta2_m, zeta3_m, neg zeta3_m]
  Std.Array.make 16#usize
    ((List.range 16).map (fun k =>
      let pair_idx := k / 2
      let zeta := zetas[pair_idx]!
      let a0 := lhs_m.val[2 * pair_idx]!
      let a1 := lhs_m.val[2 * pair_idx + 1]!
      let b0 := rhs_m.val[2 * pair_idx]!
      let b1 := rhs_m.val[2 * pair_idx + 1]!
      if k % 2 = 0 then add (mul a0 b0) (mul (mul a1 b1) zeta)
      else add (mul a0 b1) (mul a1 b0)))
    (by simp)

/-! ### §L6.3b — `Spec.multiply_ntts_pure` ↔ chunked `Spec.ntt_multiply_pure_no_acc`
    bridge.

    Required by the L7 matrix-level FC theorems (compute_As_plus_e_fc et al.)
    to connect the impl-side per-chunk Mont accumulator (which the L6.3
    family produces in `Spec.ntt_multiply_pure_no_acc` form) to the hacspec
    `multiply_ntts`-based matrix product spec. The bridge is a SpecPure-side
    algebraic identity — no impl side, no Triple, no Mont-domain crossing
    beyond what `Spec.zeta_at` already absorbs. -/

set_option maxRecDepth 4000 in
set_option maxHeartbeats 16000000 in
/-- : `ntt.ZETAS` reduces to a concrete `.ok` value (since
    `parameters.FieldElement.new` is unconditional), and for `i ∈ [64, 128)`
    the `i`-th lookup of that value equals `Spec.zeta_at i`. The numeric
    fact at each position is the keystone identity
    `(ZETAS_TIMES_MONTGOMERY_R[i].val * 169) mod 3329 = ntt.ZETAS[i].val`
    (i.e. impl-side Mont zeta times R⁻¹ = canonical zeta). -/
theorem hacspec_ZETAS_ok_and_zeta_at :
    ∃ zs : Aeneas.Std.Array hacspec_ml_kem.parameters.FieldElement 128#usize,
      hacspec_ml_kem.ntt.ZETAS = .ok zs
      ∧ (∀ i : Nat, 64 ≤ i → i < 128 → Spec.zeta_at i = zs.val[i]!) := by
  unfold hacspec_ml_kem.ntt.ZETAS
  refine ⟨_, rfl, ?_⟩
  intro i h_lo h_hi
  interval_cases i <;>
  · show lift_fe_mont _ = _
    unfold lift_fe_mont i16_to_spec_fe_mont feOfZMod
    simp only [libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R]
    rfl

/-! ### §L6.3b — .2/3/4: per-lane reduction + `from_fn_pure_eq` lift
    + chunked assembly.

    The chain below realises `Spec.multiply_ntts_pure_eq_chunked_no_acc` (the
    canonical bridge between hacspec `ntt.multiply_ntts` and the impl-side
    chunked `Spec.ntt_multiply_pure_no_acc` form, required by every L7
    matrix-level FC theorem).

    Architecture mirrors `LibcruxIotSha3/Sponge/` (the
    `sponge_squeeze_byte_eq` yardstick): a per-call_mut `_eq_pure` Result
    equation drives `libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq` to lift the entire 256-lane
    `multiply_ntts` to a pure-list, then `Subtype.ext` + per-lane reduction
    closes the chunked-decomposition equality.

    Helpers live inside `HelpersFC` namespace for hygiene; only the final
    theorem is re-exported. -/

namespace HelpersFC

/-- `feOfZMod` always produces a canonical FE (since `z.val < 3329`). The
    `BitVec.ofNat 16` lift is in-range modulo `2^16 = 65536 > 3329`. -/
theorem Canonical_feOfZMod (z : ZMod 3329) :
    Spec.Pure.Canonical (feOfZMod z) := by
  unfold Spec.Pure.Canonical feOfZMod hacspec_ml_kem.parameters.FIELD_MODULUS
  have h_lt : z.val < 3329 := ZMod.val_lt z
  show (BitVec.ofNat 16 z.val).toNat < 3329
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  · exact h_lt
  · exact Nat.lt_of_lt_of_le h_lt (by decide)

/-- Zeta projections (`Spec.zeta_at i = feOfZMod _`) are always canonical. -/
theorem Canonical_zeta_at (i : Nat) :
    Spec.Pure.Canonical (Spec.zeta_at i) := by
  unfold Spec.zeta_at lift_fe_mont
  exact Canonical_feOfZMod _

/-- `Slice.index_usize` reduces to `.ok (s.val[i.val]!)` for in-bounds index. -/
theorem slice_index_usize_eq_ok' {α} [Inhabited α]
    (s : Aeneas.Std.Slice α) (i : Std.Usize) (h : i.val < s.val.length) :
    Aeneas.Std.Slice.index_usize s i = .ok (s.val[i.val]!) := by
  unfold Aeneas.Std.Slice.index_usize
  have h_eq : s[i]? = s.val[i.val]? := rfl
  rw [h_eq, List.getElem?_eq_getElem h]
  show Aeneas.Std.Result.ok _ = Aeneas.Std.Result.ok _
  congr
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- `Aeneas.Std.Array.index_usize` reduces to `.ok (a.val[i.val]!)`. -/
theorem array_index_usize_eq_ok' {α n} [Inhabited α]
    (a : Aeneas.Std.Array α n) (i : Std.Usize) (h : i.val < a.val.length) :
    Aeneas.Std.Array.index_usize a i = .ok (a.val[i.val]!) := by
  unfold Aeneas.Std.Array.index_usize
  have h_eq : a[i]? = a.val[i.val]? := rfl
  rw [h_eq, List.getElem?_eq_getElem h]
  show Aeneas.Std.Result.ok _ = Aeneas.Std.Result.ok _
  congr
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- `base_case_multiply_even` reduces to `.ok (a0*b0 + (a1*b1)*ζ)` via the
    three `mul_eq_ok`s and the final `add_eq_ok`. -/
theorem base_case_multiply_even_eq
    (a0 a1 b0 b1 zeta : hacspec_ml_kem.parameters.FieldElement) :
    hacspec_ml_kem.ntt.base_case_multiply_even a0 a1 b0 b1 zeta = .ok
      (Spec.Pure.FieldElement.add_pure (Spec.Pure.FieldElement.mul_pure a0 b0)
        (Spec.Pure.FieldElement.mul_pure
          (Spec.Pure.FieldElement.mul_pure a1 b1) zeta)) := by
  unfold hacspec_ml_kem.ntt.base_case_multiply_even
  rw [Spec.Pure.FieldElement.mul_eq_ok]; simp only [bind_tc_ok]
  rw [Spec.Pure.FieldElement.mul_eq_ok]; simp only [bind_tc_ok]
  rw [Spec.Pure.FieldElement.mul_eq_ok]; simp only [bind_tc_ok]
  rw [Spec.Pure.FieldElement.add_eq_ok]

/-- `base_case_multiply_odd` reduces to `.ok (a0*b1 + a1*b0)` via two
    `mul_eq_ok`s and the final `add_eq_ok`. -/
theorem base_case_multiply_odd_eq
    (a0 a1 b0 b1 : hacspec_ml_kem.parameters.FieldElement) :
    hacspec_ml_kem.ntt.base_case_multiply_odd a0 a1 b0 b1 = .ok
      (Spec.Pure.FieldElement.add_pure (Spec.Pure.FieldElement.mul_pure a0 b1)
        (Spec.Pure.FieldElement.mul_pure a1 b0)) := by
  unfold hacspec_ml_kem.ntt.base_case_multiply_odd
  rw [Spec.Pure.FieldElement.mul_eq_ok]; simp only [bind_tc_ok]
  rw [Spec.Pure.FieldElement.mul_eq_ok]; simp only [bind_tc_ok]
  rw [Spec.Pure.FieldElement.add_eq_ok]

/-- Pure lane value of `multiply_ntts` at index `i ∈ [0, 256)`.

    Mirrors the impl `ntt_multiply_n_at` body: looks up zeta from the slice at
    `i/4` (negated when `i % 4 ≥ 2`), then dispatches to
    `base_case_multiply_{even,odd}` per `i % 2`. The pure form replaces the
    `Result`-monad ops with their `_pure` projections (`add_pure`, `mul_pure`,
    `neg_pure`). The zeta is taken from `Spec.zeta_at (64 + i/4)` to match
    the impl's `zetas[64..128]` slice access. -/
noncomputable def multiply_ntts_lane_pure
    (p1 p2 : Aeneas.Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (i : Nat) : hacspec_ml_kem.parameters.FieldElement :=
  let group := i / 4
  let i1 := i % 4
  let zeta_base := Spec.zeta_at (64 + group)
  let zeta := if i1 < 2 then zeta_base
              else Spec.Pure.FieldElement.neg_pure zeta_base
  if i % 2 = 0 then
    let a0 := p1.val[i]!
    let a1 := p1.val[i+1]!
    let b0 := p2.val[i]!
    let b1 := p2.val[i+1]!
    Spec.Pure.FieldElement.add_pure (Spec.Pure.FieldElement.mul_pure a0 b0)
      (Spec.Pure.FieldElement.mul_pure
        (Spec.Pure.FieldElement.mul_pure a1 b1) zeta)
  else
    let a0 := p1.val[i-1]!
    let a1 := p1.val[i]!
    let b0 := p2.val[i-1]!
    let b1 := p2.val[i]!
    Spec.Pure.FieldElement.add_pure (Spec.Pure.FieldElement.mul_pure a0 b1)
      (Spec.Pure.FieldElement.mul_pure a1 b0)

set_option maxHeartbeats 16000000 in
/-- **Per-lane reduction of `ntt.ntt_multiply_n_at`.**

    For any slice `s` of length 64 satisfying `s.val[k]! = Spec.zeta_at
    (64 + k)` for `k < 64`, the hacspec body `ntt.ntt_multiply_n_at p1 p2 s
    i` succeeds with `multiply_ntts_lane_pure p1 p2 i.val`. Drives the
    `from_fn_pure_eq` lift in .3. -/
theorem ntt_multiply_n_at_eq_pure
    (p1 p2 : Aeneas.Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (s : Aeneas.Std.Slice hacspec_ml_kem.parameters.FieldElement)
    (h_slen : s.val.length = 64)
    (h_zeta_eq : ∀ k : Nat, k < 64 → s.val[k]! = Spec.zeta_at (64 + k))
    (i : Std.Usize) (hi : i.val < 256) :
    hacspec_ml_kem.ntt.ntt_multiply_n_at p1 p2 s i
      = .ok (multiply_ntts_lane_pure p1 p2 i.val) := by
  unfold hacspec_ml_kem.ntt.ntt_multiply_n_at
  -- Step 1: group ← i / 4#usize.
  obtain ⟨group, h_g_eq, h_g_v, _⟩ :=
    Std.UScalar.div_bv_spec i (show ((4#usize : Std.Usize)).val ≠ 0 by decide)
  rw [h_g_eq]; simp only [bind_tc_ok]
  have h_g_val : group.val = i.val / 4 := by rw [h_g_v]; rfl
  have h_g_lt : group.val < 64 := by rw [h_g_val]; omega
  have h_g_lt_slen : group.val < s.val.length := by rw [h_slen]; exact h_g_lt
  -- Step 2: i1 ← i % 4#usize.
  obtain ⟨i1, h_i1_eq, h_i1_v, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.rem_bv_spec i
      (show ((4#usize : Std.Usize)).val ≠ 0 by decide))
  rw [h_i1_eq]; simp only [bind_tc_ok]
  have h_i1_val : i1.val = i.val % 4 := by rw [h_i1_v]; rfl
  -- Slice index lookup + zeta correspondence + canonicity.
  have h_slice_idx_ok :
      Aeneas.Std.Slice.index_usize s group = .ok (s.val[group.val]!) :=
    slice_index_usize_eq_ok' s group h_g_lt_slen
  have h_zeta_val : s.val[group.val]! = Spec.zeta_at (64 + group.val) :=
    h_zeta_eq group.val h_g_lt
  have h_canon_zeta : Spec.Pure.Canonical (s.val[group.val]!) := by
    rw [h_zeta_val]; exact Canonical_zeta_at _
  -- Step 3: zeta. Collapse the zeta branch into a uniform tail.
  set zeta_pure : hacspec_ml_kem.parameters.FieldElement :=
    if i.val % 4 < 2 then Spec.zeta_at (64 + i.val / 4)
    else Spec.Pure.FieldElement.neg_pure (Spec.zeta_at (64 + i.val / 4))
    with h_zeta_pure_def
  have h_zeta_result :
      (do let z ← (if i1 < 2#usize then Aeneas.Std.Slice.index_usize s group
              else do let fe ← Aeneas.Std.Slice.index_usize s group
                      hacspec_ml_kem.parameters.FieldElement.neg fe);
          (do let i2 ← i % 2#usize;
              if i2 = 0#usize
              then do let fe ← Aeneas.Std.Array.index_usize p1 i;
                      let i3 ← i + 1#usize;
                      let fe1 ← Aeneas.Std.Array.index_usize p1 i3;
                      let fe2 ← Aeneas.Std.Array.index_usize p2 i;
                      let fe3 ← Aeneas.Std.Array.index_usize p2 i3;
                      hacspec_ml_kem.ntt.base_case_multiply_even fe fe1 fe2 fe3 z
              else do let i3 ← i - 1#usize;
                      let fe ← Aeneas.Std.Array.index_usize p1 i3;
                      let fe1 ← Aeneas.Std.Array.index_usize p1 i;
                      let fe2 ← Aeneas.Std.Array.index_usize p2 i3;
                      let fe3 ← Aeneas.Std.Array.index_usize p2 i;
                      hacspec_ml_kem.ntt.base_case_multiply_odd fe fe1 fe2 fe3)) =
      (do let i2 ← i % 2#usize;
          if i2 = 0#usize
          then do let fe ← Aeneas.Std.Array.index_usize p1 i;
                  let i3 ← i + 1#usize;
                  let fe1 ← Aeneas.Std.Array.index_usize p1 i3;
                  let fe2 ← Aeneas.Std.Array.index_usize p2 i;
                  let fe3 ← Aeneas.Std.Array.index_usize p2 i3;
                  hacspec_ml_kem.ntt.base_case_multiply_even fe fe1 fe2 fe3 zeta_pure
          else do let i3 ← i - 1#usize;
                  let fe ← Aeneas.Std.Array.index_usize p1 i3;
                  let fe1 ← Aeneas.Std.Array.index_usize p1 i;
                  let fe2 ← Aeneas.Std.Array.index_usize p2 i3;
                  let fe3 ← Aeneas.Std.Array.index_usize p2 i;
                  hacspec_ml_kem.ntt.base_case_multiply_odd fe fe1 fe2 fe3) := by
    rcases (Nat.lt_or_ge i1.val 2) with h_i1_lt | h_i1_ge
    · rw [if_pos (show i1 < 2#usize from h_i1_lt)]
      rw [h_slice_idx_ok]; simp only [bind_tc_ok]
      rw [h_zeta_val]
      simp only [h_zeta_pure_def,
                 show i.val % 4 < 2 from h_i1_val ▸ h_i1_lt, if_true]
      rw [h_g_val]
    · rw [if_neg (show ¬ i1 < 2#usize from by show ¬ i1.val < 2; omega)]
      rw [h_slice_idx_ok]; simp only [bind_tc_ok]
      rw [Spec.Pure.FieldElement.neg_eq_ok _ h_canon_zeta]
      simp only [bind_tc_ok]
      rw [h_zeta_val]
      simp only [h_zeta_pure_def,
                 show ¬ i.val % 4 < 2 from by
                   have : i1.val = i.val % 4 := h_i1_val; omega, if_false]
      rw [h_g_val]
  rw [h_zeta_result]
  -- Step 4: i2 ← i % 2#usize.
  obtain ⟨i2, h_i2_eq, h_i2_v, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.rem_bv_spec i
      (show ((2#usize : Std.Usize)).val ≠ 0 by decide))
  rw [h_i2_eq]; simp only [bind_tc_ok]
  have h_i2_val : i2.val = i.val % 2 := by rw [h_i2_v]; rfl
  -- Array bounds (p1.val.length = p2.val.length = 256).
  have h_p1_len : p1.val.length = 256 := p1.property
  have h_p2_len : p2.val.length = 256 := p2.property
  have h_i_lt_p1 : i.val < p1.val.length := by rw [h_p1_len]; exact hi
  have h_i_lt_p2 : i.val < p2.val.length := by rw [h_p2_len]; exact hi
  have h_i2_lt_2 : i2.val < 2 := by
    rw [h_i2_val]; exact Nat.mod_lt _ (by decide)
  -- Step 5: branch on i2.val = 0 vs 1.
  rcases (show i2.val = 0 ∨ i2.val = 1 from by omega) with h_i2_0 | h_i2_1
  · -- Even branch.
    have h_i2_eq_0 : i2 = 0#usize :=
      Std.UScalar.eq_of_val_eq (by rw [h_i2_0]; rfl)
    rw [if_pos h_i2_eq_0]
    obtain ⟨i3, h_i3_eq, h_i3_v, _⟩ :=
      Std.WP.spec_imp_exists
        (Std.UScalar.add_bv_spec (x := i) (y := 1#usize) (by scalar_tac))
    have h_i3_val : i3.val = i.val + 1 := by rw [h_i3_v]; rfl
    have h_i3_lt_p1 : i3.val < p1.val.length := by
      rw [h_p1_len, h_i3_val]; omega
    have h_i3_lt_p2 : i3.val < p2.val.length := by
      rw [h_p2_len, h_i3_val]; omega
    rw [array_index_usize_eq_ok' p1 i h_i_lt_p1]; simp only [bind_tc_ok]
    rw [h_i3_eq]; simp only [bind_tc_ok]
    rw [array_index_usize_eq_ok' p1 i3 h_i3_lt_p1]; simp only [bind_tc_ok]
    rw [array_index_usize_eq_ok' p2 i h_i_lt_p2]; simp only [bind_tc_ok]
    rw [array_index_usize_eq_ok' p2 i3 h_i3_lt_p2]; simp only [bind_tc_ok]
    rw [base_case_multiply_even_eq]
    congr 1
    unfold multiply_ntts_lane_pure
    have h_imod2 : i.val % 2 = 0 := by rw [← h_i2_val]; exact h_i2_0
    simp only [h_imod2, if_true, h_i3_val, h_zeta_pure_def]
  · -- Odd branch.
    have h_i2_ne_0 : ¬ (i2 = 0#usize) := by
      intro heq
      have h_zero : i2.val = 0 := by rw [heq]; rfl
      omega
    rw [if_neg h_i2_ne_0]
    have h_i_ge_1 : 1 ≤ i.val := by
      have h_imod2 : i.val % 2 = 1 := by rw [← h_i2_val]; exact h_i2_1
      omega
    obtain ⟨i3, h_i3_eq, h_i3_v, _⟩ :=
      Std.WP.spec_imp_exists
        (Std.UScalar.sub_bv_spec (x := i) (y := 1#usize) (by scalar_tac))
    have h_i3_val : i3.val = i.val - 1 := by rw [h_i3_v]; rfl
    have h_i3_lt_p1 : i3.val < p1.val.length := by
      rw [h_p1_len, h_i3_val]; omega
    have h_i3_lt_p2 : i3.val < p2.val.length := by
      rw [h_p2_len, h_i3_val]; omega
    rw [h_i3_eq]; simp only [bind_tc_ok]
    rw [array_index_usize_eq_ok' p1 i3 h_i3_lt_p1]; simp only [bind_tc_ok]
    rw [array_index_usize_eq_ok' p1 i h_i_lt_p1]; simp only [bind_tc_ok]
    rw [array_index_usize_eq_ok' p2 i3 h_i3_lt_p2]; simp only [bind_tc_ok]
    rw [array_index_usize_eq_ok' p2 i h_i_lt_p2]; simp only [bind_tc_ok]
    rw [base_case_multiply_odd_eq]
    congr 1
    unfold multiply_ntts_lane_pure
    have h_imod2 : i.val % 2 = 1 := by rw [← h_i2_val]; exact h_i2_1
    simp only [h_imod2, Nat.one_ne_zero, if_false, h_i3_val]

/-! ### §L6.3b — .3: lift `multiply_ntts` to a pure 256-list. -/

/-- The 64-position slice extracted from a length-128 array has length 64. -/
lemma slice_length_64
    (zs : Aeneas.Std.Array hacspec_ml_kem.parameters.FieldElement 128#usize) :
    (List.slice 64 128 zs.val).length = 64 := by
  have h : zs.val.length = 128 := zs.property
  unfold List.slice
  simp [List.length_take, h]

/-- The hacspec slice-by-range extraction `zs[64..128]` reduces to the
    explicit `List.slice 64 128 zs.val` slice. Drives the slice-step in
    .3's reduction of `ntt.multiply_ntts`. -/
lemma slice_zetas_succeeds
    (zs : Aeneas.Std.Array hacspec_ml_kem.parameters.FieldElement 128#usize) :
    core.Array.Insts.CoreOpsIndexIndex.index
      (core.Slice.Insts.CoreOpsIndexIndex
      (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
      hacspec_ml_kem.parameters.FieldElement)) zs
      { start := 64#usize, «end» := 128#usize }
    = .ok (⟨List.slice 64 128 zs.val, by
            rw [slice_length_64]; scalar_tac⟩ :
           Aeneas.Std.Slice hacspec_ml_kem.parameters.FieldElement) := by
  unfold core.Array.Insts.CoreOpsIndexIndex.index
         core.slice.index.Slice.index
         core.Slice.Insts.CoreOpsIndexIndex
         core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
  show core.slice.index.SliceIndexRangeUsizeSlice.index
      (core.cmRangeUsizeToAeneas _) zs.to_slice = _
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index
         core.cmRangeUsizeToAeneas
  have h_alen : zs.val.length = 128 := zs.property
  have h_cond : (64#usize : Std.Usize) ≤ (128#usize : Std.Usize) ∧
      (128#usize : Std.Usize).val ≤ zs.to_slice.val.length := by
    refine ⟨by show (64 : Nat) ≤ 128; decide, by
      show 128 ≤ zs.to_slice.val.length
      show 128 ≤ zs.val.length; omega⟩
  rw [if_pos h_cond]
  rfl

/-- `List.slice a b l [k]! = l[a + k]!` when `a ≤ b`, `b ≤ l.length`,
    and `k < b - a`. -/
lemma slice_getElem_at {α} [Inhabited α]
    (l : List α) (a b : Nat) (h_le_a : a ≤ b) (h_le_b : b ≤ l.length)
    (k : Nat) (hk : k < b - a) :
    (List.slice a b l)[k]! = l[a + k]! := by
  unfold List.slice
  have h_ak_lt : a + k < l.length := by omega
  have h_drop_len : (l.drop a).length = l.length - a := by simp
  have h_k_lt_drop : k < (l.drop a).length := by rw [h_drop_len]; omega
  have h_take_idx :
      ((l.drop a).take (b - a))[k]? = (l.drop a)[k]? := by
    rw [List.getElem?_take, if_pos hk]
  have h_drop_idx : (l.drop a)[k]? = l[a + k]? := by
    rw [List.getElem?_drop]
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
      h_take_idx, h_drop_idx]

/-- `BitVec.ofNat _ k` round-trips through `Usize.val` when `k < 256`. -/
lemma usize_ofNat_val_eq_self_of_lt_256 (k : Nat) (h : k < 256) :
    (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k := by
  show (BitVec.ofNat System.Platform.numBits k).toNat = k
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have h_max : k ≤ Std.Usize.max := by scalar_tac
  have h_max_def : Std.Usize.max + 1 = 2 ^ System.Platform.numBits := by scalar_tac
  omega

set_option maxHeartbeats 4000000 in
/-- **`hacspec_ml_kem.ntt.multiply_ntts p1 p2` reduces to the pure 256-lane
    array.**

    Composes .1 (ZETAS = .ok zs + zeta correspondence), the
    slice-extraction reduction, and .2's per-lane reduction via
    `libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq`. The result is the pure FE-arithmetic list
    `(List.range 256).map (multiply_ntts_lane_pure p1 p2)`. -/
-- Public (exported for L7.4 `compute_message_acc_bridge`): per-multiply reduction
-- of the hacspec `ntt.multiply_ntts` to its pure-lane array form. Visibility-only
-- change (proof/statement unchanged).
theorem multiply_ntts_eq_pure_array
    (p1 p2 : Aeneas.Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    hacspec_ml_kem.ntt.multiply_ntts p1 p2
    = .ok (⟨(List.range 256).map (multiply_ntts_lane_pure p1 p2),
            by simp [List.length_map, List.length_range]⟩ :
           Aeneas.Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) := by
  unfold hacspec_ml_kem.ntt.multiply_ntts
  -- Step 1: ntt.ZETAS = .ok zs.
  obtain ⟨zs, h_zetas_eq, h_zeta_at⟩ := hacspec_ZETAS_ok_and_zeta_at
  rw [h_zetas_eq]; simp only [bind_tc_ok]
  -- Step 2: slice extraction.
  rw [slice_zetas_succeeds]; simp only [bind_tc_ok]
  -- Step 3: ntt.ntt_multiply_n p1 p2 s ⇒ parameters.createi 256 inst (p1, p2, s)
  --                                    ⇒ core.array.from_fn 256 inst.FnMutInst (p1, p2, s).
  unfold hacspec_ml_kem.ntt.ntt_multiply_n
         hacspec_ml_kem.parameters.createi
  -- Slice / properties.
  set s : Aeneas.Std.Slice hacspec_ml_kem.parameters.FieldElement :=
    ⟨List.slice 64 128 zs.val, by rw [slice_length_64]; scalar_tac⟩ with h_s_def
  have h_slen : s.val.length = 64 := slice_length_64 zs
  have h_zeta_eq_slice : ∀ k : Nat, k < 64 → s.val[k]! = Spec.zeta_at (64 + k) := by
    intro k hk
    show (List.slice 64 128 zs.val)[k]! = _
    have h_zlen : zs.val.length = 128 := zs.property
    rw [slice_getElem_at zs.val 64 128 (by omega) (by omega) k (by omega)]
    exact (h_zeta_at (64 + k) (by omega) (by omega)).symm
  -- Set f and build the per-call_mut equation.
  set f : Nat → hacspec_ml_kem.parameters.FieldElement :=
    multiply_ntts_lane_pure p1 p2 with h_f_def
  have h_call_mut_eq : ∀ k : Nat, k < (256#usize : Std.Usize).val →
      ((hacspec_ml_kem.ntt.ntt_multiply_n.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement
          256#usize).FnMutInst).call_mut (p1, p2, s) ⟨BitVec.ofNat _ k⟩
      = .ok (f k, (p1, p2, s)) := by
    intro k hk
    have hk' : k < 256 := hk
    have h_k_val : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k :=
      usize_ofNat_val_eq_self_of_lt_256 k hk'
    show (do let fe ← hacspec_ml_kem.ntt.ntt_multiply_n_at p1 p2 s
              (⟨BitVec.ofNat _ k⟩ : Std.Usize);
             .ok (fe, (p1, p2, s))) = _
    have h_lane := ntt_multiply_n_at_eq_pure p1 p2 s h_slen h_zeta_eq_slice
                     (⟨BitVec.ofNat _ k⟩ : Std.Usize) (by rw [h_k_val]; exact hk')
    rw [h_lane]; simp only [bind_tc_ok]
    rw [h_k_val]
    rfl
  -- Apply from_fn_pure_eq.
  have h_from_fn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq 256#usize
    (hacspec_ml_kem.ntt.ntt_multiply_n.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement
        256#usize).FnMutInst
    (p1, p2, s) f h_call_mut_eq
  exact h_from_fn

/-! ### §L6.3b — .4: chunked assembly + final theorem. -/

set_option maxHeartbeats 8000000 in
/-- **Per-lane equality, `j/ℓ` form.**

    For `j < 16`, `ℓ < 16`, the flat lane value
    `multiply_ntts_lane_pure p1 p2 (16 * j + ℓ)` equals the `ℓ`-th
    lane of the per-chunk product
    `Spec.ntt_multiply_pure_no_acc (chunk_at p1 j) (chunk_at p2 j)
    ζ_{4j..4j+3}`. Closed via `interval_cases ℓ` (16 cases), each
    `rfl` after unfolding `multiply_ntts_lane_pure`,
    `Spec.ntt_multiply_pure_no_acc`, and `Spec.chunk_at`. -/
theorem multiply_ntts_lane_pure_eq_chunked_aux
    (p1 p2 : Aeneas.Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (j ℓ : Nat) (hj : j < 16) (hℓ : ℓ < 16) :
    multiply_ntts_lane_pure p1 p2 (16 * j + ℓ) =
      (Spec.ntt_multiply_pure_no_acc
        (Spec.chunk_at p1 j) (Spec.chunk_at p2 j)
        (Spec.zeta_at (64 + 4 * j))
        (Spec.zeta_at (64 + 4 * j + 1))
        (Spec.zeta_at (64 + 4 * j + 2))
        (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]! := by
  unfold multiply_ntts_lane_pure
  have h_div : (16 * j + ℓ) / 4 = 4 * j + ℓ / 4 := by omega
  have h_mod4 : (16 * j + ℓ) % 4 = ℓ % 4 := by omega
  have h_mod2 : (16 * j + ℓ) % 2 = ℓ % 2 := by omega
  rw [h_div, h_mod4, h_mod2]
  unfold Spec.ntt_multiply_pure_no_acc
  -- Use `conv_rhs` to scope the index-reduction to the RHS so it doesn't
  -- accidentally target an LHS `_[m]!` first. After `unfold`, the RHS has
  -- the (List.range 16)-map structure wrapped in `Std.Array.make`/`↑`;
  -- the `show` brings the outer projection inline so `rw` can match.
  conv_rhs =>
    rw [show ∀ (l : List _) (h : l.length = (16#usize : Std.Usize).val) (k : Nat),
            (↑(Std.Array.make 16#usize l h) : List _)[k]! = l[k]! from fun _ _ _ => rfl,
        List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hℓ]
  unfold Spec.chunk_at
  interval_cases ℓ <;> rfl

/-- **Per-lane equality, `i` form (wrapper around `_aux`).** -/
theorem multiply_ntts_lane_pure_eq_chunked
    (p1 p2 : Aeneas.Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (i : Nat) (hi : i < 256) :
    multiply_ntts_lane_pure p1 p2 i =
      (Spec.ntt_multiply_pure_no_acc
        (Spec.chunk_at p1 (i / 16)) (Spec.chunk_at p2 (i / 16))
        (Spec.zeta_at (64 + 4 * (i / 16)))
        (Spec.zeta_at (64 + 4 * (i / 16) + 1))
        (Spec.zeta_at (64 + 4 * (i / 16) + 2))
        (Spec.zeta_at (64 + 4 * (i / 16) + 3))).val[i % 16]! := by
  have h_i : i = 16 * (i / 16) + (i % 16) := by omega
  conv_lhs => rw [h_i]
  exact multiply_ntts_lane_pure_eq_chunked_aux p1 p2 (i / 16) (i % 16)
    (by omega) (Nat.mod_lt _ (by decide))

end HelpersFC

set_option maxHeartbeats 4000000 in
/-- **§L6.3b bridge: hacspec `multiply_ntts` ↔ chunked `ntt_multiply_pure_no_acc`.**

    Connects the spec-side projection of hacspec `ntt.multiply_ntts`
    (canonical `Spec.multiply_ntts_pure`) to the impl-side per-chunk
    Mont-domain product form `Spec.ntt_multiply_pure_no_acc` aggregated
    via `Spec.flatten_chunks` over the 16 chunks.

    This is the bridge required by every L7 matrix-level FC theorem
    (`compute_As_plus_e_fc`, `compute_vector_u_fc`,
    `compute_ring_element_v_fc`, `compute_message_fc`): the impl
    accumulator at row `(i, k)` produces `Spec.ntt_multiply_pure_no_acc
    (lift_chunk_mont row[k]) (lift_chunk_mont t[k]) Spec.zeta_at(64+4j..)`
    per chunk `j`, and this theorem allows the matrix Triple to collapse
    that decomposition into the hacspec `multiply_ntts` form used by
    `Spec.compute_As_plus_e` and friends.

    Proof composes:
    - .1 (`hacspec_ZETAS_ok_and_zeta_at`): zetas at [64..128)
      correspondence.
    - .3 (`HelpersFC.multiply_ntts_eq_pure_array`): lifts
      `ntt.multiply_ntts p1 p2` to `.ok ⟨pure-list, _⟩`.
    - .4 (`HelpersFC.multiply_ntts_lane_pure_eq_chunked`): per-lane
      equality.
    - Array extensionality (`Subtype.ext` + `List.map_congr_left`). -/
theorem Spec.multiply_ntts_pure_eq_chunked_no_acc
    (p1 p2 : Aeneas.Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    Spec.multiply_ntts_pure p1 p2 =
      Spec.flatten_chunks
        ⟨(List.range 16).map (fun j =>
          Spec.ntt_multiply_pure_no_acc
            (Spec.chunk_at p1 j) (Spec.chunk_at p2 j)
            (Spec.zeta_at (64 + 4 * j))
            (Spec.zeta_at (64 + 4 * j + 1))
            (Spec.zeta_at (64 + 4 * j + 2))
            (Spec.zeta_at (64 + 4 * j + 3))),
         by simp⟩ := by
  unfold Spec.multiply_ntts_pure
  rw [HelpersFC.multiply_ntts_eq_pure_array]
  -- Reduce `match .ok r with .ok r => r | _ => default` to `r` so the Array constructor
  -- on the LHS aligns with the Spec.flatten_chunks Array on the RHS.
  show (⟨(List.range 256).map (HelpersFC.multiply_ntts_lane_pure p1 p2),
          by simp [List.length_map, List.length_range]⟩ :
         Aeneas.Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) = _
  apply Subtype.ext
  -- Goal: pure_list = (Spec.flatten_chunks ⟨chunks_list, _⟩).val
  -- Reduce: ↑⟨L, _⟩ = L by `Subtype.coe_mk`-rfl, and `(Spec.flatten_chunks ⟨L, h⟩).val =
  -- (List.range 256).map (fun j => ⟨L, h⟩.val[j/16]!.val[j%16]!) = (List.range 256).map
  -- (fun j => L[j/16]!.val[j%16]!)` by unfolding Spec.flatten_chunks and Std.Array.make.
  show (List.range 256).map (HelpersFC.multiply_ntts_lane_pure p1 p2) =
       (List.range 256).map (fun j =>
         ((List.range 16).map (fun j' =>
           Spec.ntt_multiply_pure_no_acc
             (Spec.chunk_at p1 j') (Spec.chunk_at p2 j')
             (Spec.zeta_at (64 + 4 * j'))
             (Spec.zeta_at (64 + 4 * j' + 1))
             (Spec.zeta_at (64 + 4 * j' + 2))
             (Spec.zeta_at (64 + 4 * j' + 3))))[j / 16]!.val[j % 16]!)
  apply List.map_congr_left
  intro i hi
  have h_i_lt : i < 256 := List.mem_range.mp hi
  have hi_div_lt : i / 16 < 16 := by omega
  -- Reduce the chunks-list lookup at index `i / 16` to the explicit
  -- `ntt_multiply_pure_no_acc` value, via List.getElem? expansion of the
  -- inner `[i / 16]!`. We do this via a one-shot `have` lemma to scope the
  -- rewrites to the inner index only (leaving the outer `[i % 16]!` intact).
  have h_chunks_at : ((List.range 16).map (fun j' =>
        Spec.ntt_multiply_pure_no_acc
          (Spec.chunk_at p1 j') (Spec.chunk_at p2 j')
          (Spec.zeta_at (64 + 4 * j'))
          (Spec.zeta_at (64 + 4 * j' + 1))
          (Spec.zeta_at (64 + 4 * j' + 2))
          (Spec.zeta_at (64 + 4 * j' + 3))))[i / 16]! =
      Spec.ntt_multiply_pure_no_acc
        (Spec.chunk_at p1 (i / 16)) (Spec.chunk_at p2 (i / 16))
        (Spec.zeta_at (64 + 4 * (i / 16)))
        (Spec.zeta_at (64 + 4 * (i / 16) + 1))
        (Spec.zeta_at (64 + 4 * (i / 16) + 2))
        (Spec.zeta_at (64 + 4 * (i / 16) + 3)) := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hi_div_lt]; rfl
  show HelpersFC.multiply_ntts_lane_pure p1 p2 i =
      ((List.range 16).map (fun j' =>
        Spec.ntt_multiply_pure_no_acc
          (Spec.chunk_at p1 j') (Spec.chunk_at p2 j')
          (Spec.zeta_at (64 + 4 * j'))
          (Spec.zeta_at (64 + 4 * j' + 1))
          (Spec.zeta_at (64 + 4 * j' + 2))
          (Spec.zeta_at (64 + 4 * j' + 3))))[i / 16]!.val[i % 16]!
  rw [h_chunks_at]
  exact HelpersFC.multiply_ntts_lane_pure_eq_chunked p1 p2 i h_i_lt

/-- Accumulating base-case NTT multiply: pointwise sum of the initial
    accumulator with the no-acc product. Defined as
    `chunk_add_pure acc (ntt_multiply_pure_no_acc ...)`. The L2.8 POST
    anchors against this; downstream provers reduce to the product +
    a single trivial additive step. -/
noncomputable def ntt_multiply_base_case_alg
    (lhs_m rhs_m : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (zeta0_m zeta1_m zeta2_m zeta3_m : hacspec_ml_kem.parameters.FieldElement)
    (acc_m : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize :=
  Spec.chunk_add_pure acc_m
    (Spec.ntt_multiply_pure_no_acc lhs_m rhs_m
      zeta0_m zeta1_m zeta2_m zeta3_m)

/-- Algebraic POST predicate for the L2.8 vector-level base-case NTT
    multiply. Relates the resulting I32 accumulator slice `r` to the
    inputs (`lhs`, `rhs`, 4 zetas, initial accumulator `out`) per the
    per-pair degree-2 polynomial multiply equation mod (X²−ζ²).

    The impl chains 8 calls to `accumulating_ntt_multiply_binomials`
    with effective zetas `[zeta0, -zeta0, zeta1, -zeta1, zeta2, -zeta2,
    zeta3, -zeta3]` across pairs `(out[2k], out[2k+1])` for k = 0..7.

    Body uses `Spec.chunk_reducing_from_i32_array_pure` (per-lane
    Montgomery reduction) to lift the I32 accumulator to Mont-domain
    FE-array, then compares with `ntt_multiply_base_case_alg` applied
    to the Mont-domain lifts of inputs. Mirrors the L1.10
    `lift_poly_mont = Spec.poly_reducing_from_i32_array_pure` idiom. -/
noncomputable def ntt_multiply_base_case_post
    (lhs rhs : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta0 zeta1 zeta2 zeta3 : Std.I16)
    (out r : Aeneas.Std.Slice Std.I32) : Prop :=
  Spec.chunk_reducing_from_i32_array_pure r =
    ntt_multiply_base_case_alg
      (lift_chunk_mont lhs) (lift_chunk_mont rhs)
      (lift_fe_mont zeta0) (lift_fe_mont zeta1)
      (lift_fe_mont zeta2) (lift_fe_mont zeta3)
      (Spec.chunk_reducing_from_i32_array_pure out)

/-! ### L2.8c — helper Triples and bridge lemmas.

    Per-pair binomial Triple + ZMod-side FE-equation closer. The
    per-pair Triple isolates one `accumulating_ntt_multiply_binomials`
    call; L2.8c chains 8 of these with alternating-sign zetas. -/

/-- I32 → ZMod 3329 cast bridge for sign-extending I16 to I32.
    `(as_i32 x : I32).val = x.val` since I16 ⊆ I32. -/
theorem L2_8c.as_i32_val_eq (x : Std.I16) :
    libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 x
      = .ok ((Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 x : Std.I32)) := by
  unfold libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32
  unfold libcrux_secrets.traits.Declassify.Blanket.declassify
  unfold libcrux_secrets.traits.Classify.Blanket.classify
  rfl

/-- The `cast .I32` of an I16 carries the same Int value. -/
theorem L2_8c.cast_I32_val (x : Std.I16) :
    (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 x : Std.I32).val = x.val := by
  exact Aeneas.Std.IScalar.val_mod_pow_greater_numBits Aeneas.Std.IScalarTy.I32 x (by decide)

/-- `classify` is the identity on its `.ok` value (mirror of
    `ntt_step_fc.classify_ok_eq` for use by the binomials proof). -/
theorem L2_8c.classify_ok_eq {T : Type} (x : T) :
    libcrux_secrets.traits.Classify.Blanket.classify x = .ok x := rfl

/-- Reduction of `core.num.I32.wrapping_mul` to its `.ok`
    representation in terms of the underlying `Std.I32.wrapping_mul`. -/
theorem L2_8c.cm_wrapping_mul_i32_ok_eq (x y : Std.I32) :
    CoreModels.core.num.I32.wrapping_mul x y = .ok (Aeneas.Std.I32.wrapping_mul x y) := by
  unfold CoreModels.core.num.I32.wrapping_mul
  unfold rust_primitives.arithmetic.wrapping_mul_i32
  rfl

/-- Reduction of `core.num.I32.wrapping_add` to the underlying
    Aeneas `Std.I32.wrapping_add`. -/
theorem L2_8c.cm_wrapping_add_i32_ok_eq (x y : Std.I32) :
    CoreModels.core.num.I32.wrapping_add x y = .ok (Aeneas.Std.I32.wrapping_add x y) := by
  unfold CoreModels.core.num.I32.wrapping_add
  unfold rust_primitives.arithmetic.wrapping_add_i32
  rfl

/-- Reduction of `core.num.I16.wrapping_neg` to its `.ok` rep
    via `Std.I16.wrapping_sub 0 x`. Mirror of `negate_per_elem_spec`. -/
theorem L2_8c.cm_wrapping_neg_i16_ok_eq (x : Std.I16) :
    CoreModels.core.num.I16.wrapping_neg x = .ok (Aeneas.Std.I16.wrapping_sub (0#i16) x) := by
  unfold CoreModels.core.num.I16.wrapping_neg
  unfold rust_primitives.arithmetic.wrapping_sub_i16
  rfl

/-- I16 wrapping-neg is exact when |x.val| < 2^15.
    `(wrapping_sub 0 x).val = -x.val` when `-x.val ∈ [-2^15, 2^15)`,
    i.e. when `x.val ∈ (-2^15, 2^15]`. We use `≤ 2^15 - 1` (strictly
    inside, away from boundary). -/
theorem L2_8c.wrapping_neg_val_eq (x : Std.I16)
    (h : x.val.natAbs ≤ 2^15 - 1) :
    (Aeneas.Std.I16.wrapping_sub (0#i16) x).val = -x.val := by
  rw [Aeneas.Std.I16.wrapping_sub_val_eq]
  show Int.bmod ((0#i16 : Std.I16).val - x.val) (2^16) = -x.val
  have h_zero : (0#i16 : Std.I16).val = 0 := by decide
  rw [h_zero]
  show Int.bmod (0 - x.val) (2^16) = -x.val
  have h_lb : -(2^15 : Int) ≤ 0 - x.val := by
    have : x.val ≤ (2^15 - 1 : Int) := by
      have h_abs := h
      have : x.val.natAbs ≤ 2^15 - 1 := h_abs
      omega
    omega
  have h_ub : (0 - x.val : Int) < (2^15 : Int) := by
    have : -(2^15 - 1 : Int) ≤ x.val := by
      have h_abs := h
      have : x.val.natAbs ≤ 2^15 - 1 := h_abs
      omega
    omega
  have h_bmod : Int.bmod (0 - x.val) (2^16) = 0 - x.val := by
    apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
    · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
      exact le_trans h_const h_lb
    · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
      exact lt_of_lt_of_le h_ub h_const
  rw [h_bmod]; ring

/-- I32 wrapping multiplication is exact under the no-overflow bound. -/
theorem L2_8c.wrapping_mul_i32_no_overflow (x y : Std.I32)
    (h : (x.val * y.val).natAbs < 2^31) :
    (Aeneas.Std.I32.wrapping_mul x y).val = x.val * y.val := by
  rw [Aeneas.Std.I32.wrapping_mul_val_eq]
  have h_abs_lt : |x.val * y.val| < (2^31 : Int) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast h
  have h_lb : -(2^31 : Int) ≤ x.val * y.val := by
    have := neg_abs_le (x.val * y.val)
    have h1 : -|x.val * y.val| ≤ x.val * y.val := this
    have h2 : -(2^31 : Int) < -|x.val * y.val| := by linarith
    linarith
  have h_ub : x.val * y.val < (2^31 : Int) := by
    have := le_abs_self (x.val * y.val)
    linarith
  apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
  · have h_red : ((2 : Int)^(32-1)) = (2 : Int)^31 := by decide
    rw [h_red]; exact h_lb
  · have h_red : ((2 : Int)^(32-1)) = (2 : Int)^31 := by decide
    rw [h_red]; exact h_ub

/-- I32 wrapping addition is exact under the no-overflow bound. -/
theorem L2_8c.wrapping_add_i32_no_overflow (x y : Std.I32)
    (h : (x.val + y.val).natAbs < 2^31) :
    (Aeneas.Std.I32.wrapping_add x y).val = x.val + y.val := by
  rw [Aeneas.Std.I32.wrapping_add_val_eq]
  have h_abs_lt : |x.val + y.val| < (2^31 : Int) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast h
  have h_lb : -(2^31 : Int) ≤ x.val + y.val := by
    have := neg_abs_le (x.val + y.val)
    linarith
  have h_ub : x.val + y.val < (2^31 : Int) := by
    have := le_abs_self (x.val + y.val)
    linarith
  apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
  · have h_red : ((2 : Int)^(32-1)) = (2 : Int)^31 := by decide
    rw [h_red]; exact h_lb
  · have h_red : ((2 : Int)^(32-1)) = (2 : Int)^31 := by decide
    rw [h_red]; exact h_ub

/-- Mont-domain variant of `lift_fe_neg_pure_eq`. Under the bound
    `|a.val| ≤ 2^15 - 1` (boundary excluded), the I16 negation
    `r` of `a` satisfies `lift_fe_mont r = neg_pure (lift_fe_mont a)`. -/
theorem L2_8c.lift_fe_mont_neg_pure_eq
    (a r : Std.I16)
    (hbnd : a.val.natAbs ≤ 2^15 - 1)
    (hrv : r.val = -a.val) :
    lift_fe_mont r
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont a) := by
  set s : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont a) with hs_def
  have h_lm_canon : libcrux_iot_ml_kem.Spec.Pure.Canonical (lift_fe_mont a) := by
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS
    show (lift_fe_mont a).val.val < 3329
    rw [lift_fe_mont_val_val]
    exact ZMod.val_lt _
  have h_canon : s.val.val < 3329 := by
    have h_cs := libcrux_iot_ml_kem.Spec.Pure.Canonical_neg_pure
      (lift_fe_mont a) h_lm_canon
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at h_cs
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS at h_cs; simpa using h_cs
  have h_round_trip : feOfZMod (zmodOfFE s) = s :=
    feOfZMod_zmodOfFE_of_canonical s h_canon
  -- LHS reduction.
  have h_lhs : lift_fe_mont r = feOfZMod (-((a.val : ZMod 3329)) * 169) := by
    unfold lift_fe_mont i16_to_spec_fe_mont
    congr 1
    rw [hrv]; push_cast; ring
  -- zmodOfFE s = -((a.val : ZMod q) * 169).
  have h_lm_zmod : zmodOfFE (lift_fe_mont a) = (a.val : ZMod 3329) * 169 := by
    unfold zmodOfFE
    rw [lift_fe_mont_val_val]
    rw [ZMod.natCast_zmod_val]
    unfold i16_to_spec_fe_mont
    rfl
  -- Convert `(3329 - X : Nat)` as ZMod q to `-(X : ZMod q)`.
  have h_nat_sub_zmod (X : Nat) (hX : X < 3329) :
      (((3329 - X : Nat)) : ZMod 3329) = -((X : Nat) : ZMod 3329) := by
    have h_sum_nat : (3329 - X : Nat) + X = 3329 := by omega
    have h_sum_zmod : (((3329 - X : Nat) : ZMod 3329)) + ((X : ZMod 3329)) = 0 := by
      rw [← Nat.cast_add, h_sum_nat]; exact ZMod.natCast_self 3329
    exact eq_neg_of_add_eq_zero_left h_sum_zmod
  have h_zmod_s : zmodOfFE s = -((a.val : ZMod 3329) * 169) := by
    unfold zmodOfFE
    rw [neg_pure_val_eq _ h_lm_canon]
    rw [ZMod.natCast_mod]
    have h_lm_lt : (lift_fe_mont a).val.val < 3329 := by
      rw [lift_fe_mont_val_val]; exact ZMod.val_lt _
    rw [h_nat_sub_zmod _ h_lm_lt]
    -- Goal: -((lift_fe_mont a).val.val : ZMod q) = -((a.val : ZMod q) * 169).
    rw [show ((lift_fe_mont a).val.val : ZMod 3329) = zmodOfFE (lift_fe_mont a) from by
      unfold zmodOfFE; rfl]
    rw [h_lm_zmod]
  rw [h_lhs, ← h_round_trip, h_zmod_s]
  congr 1; ring

/-! ### ZMod 3329 projection lemmas — used by L2.8 / L6.3 / L7 closures.
    These are pure-arithmetic facts about how `zmodOfFE` distributes
    over the SpecPure FE operations and the lift functions. Factored
    out of `mont_reduce_{even,odd}_fe_eq` so future closures (L6.3a/b/c,
    L2.8d cache variants) can reuse them without inlining. -/

/-- `zmodOfFE` of `Spec.mont_reduce_pure ∘ lift_fe_int`: in ZMod 3329,
    `mont_reduce_pure (lift_fe_int v) = v · 169²` (i.e., `v · R⁻²`). -/
theorem L2_8c.zmodOfFE_mont_reduce_lift_fe_int (v : Int) :
    zmodOfFE (Spec.mont_reduce_pure (lift_fe_int v))
      = (v : ZMod 3329) * 169 * 169 := by
  rw [mont_reduce_pure_lift_fe_int]
  rw [zmodOfFE_feOfZMod]

/-- `zmodOfFE` of `lift_fe_mont`: in ZMod 3329,
    `lift_fe_mont x = x.val · 169` (i.e., `x · R⁻¹`). -/
theorem L2_8c.zmodOfFE_lift_fe_mont (x : Std.I16) :
    zmodOfFE (lift_fe_mont x) = (x.val : ZMod 3329) * 169 := by
  unfold lift_fe_mont
  rw [zmodOfFE_feOfZMod]
  rfl

/-- `zmodOfFE` distributes over `FieldElement.mul_pure` in ZMod 3329. -/
theorem L2_8c.zmodOfFE_mul_pure
    (a b : hacspec_ml_kem.parameters.FieldElement) :
    zmodOfFE (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure a b)
      = zmodOfFE a * zmodOfFE b := by
  unfold zmodOfFE
  rw [mul_pure_val_eq]
  rw [ZMod.natCast_mod]
  push_cast
  rfl

/-- `zmodOfFE` distributes over `FieldElement.add_pure` in ZMod 3329. -/
theorem L2_8c.zmodOfFE_add_pure
    (a b : hacspec_ml_kem.parameters.FieldElement) :
    zmodOfFE (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure a b)
      = zmodOfFE a + zmodOfFE b := by
  unfold zmodOfFE
  rw [add_pure_val_eq]
  rw [ZMod.natCast_mod]
  push_cast
  rfl

set_option maxHeartbeats 400000 in
/-- Mont-domain FE equation builder for the L2.8c per-pair Triple:
    if the new accumulator lane `r` (as I32) and the per-pair operands
    (as I16) satisfy the ZMod 3329 modular equation
    `r * 2^16 ≡ out * 2^16 + ai * bi * 2^16 + aj * bj * zeta (mod q)`
    (the impl-side raw I32 equation projected to ZMod q), then the
    FE-level equation
    `mont_reduce_pure (lift_fe_int r.val)
      = add_pure (mont_reduce_pure (lift_fe_int out.val))
          (add_pure (mul_pure ai_m bi_m)
                    (mul_pure (mul_pure aj_m bj_m) zeta_m))`
    holds, where each `x_m = lift_fe_mont x`.

    Algebra: both sides reduce (via `mont_reduce_pure_lift_fe_int`
    + add/mul_pure round-trip) to a `feOfZMod` of a ZMod q expression.
    The Mont-inversion identity `2285 · 169 ≡ 1 (mod q)` (since
    `2^16 ≡ 2285 (mod q)`, `R⁻¹ = 169`) collapses the powers; `ring`
    closes after. -/
theorem L2_8c.mont_reduce_even_fe_eq
    (out r : Std.I32) (ai bi aj bj zeta : Std.I16)
    (h_zmod : ((r.val * (2 ^ 16 : Int)) : ZMod 3329)
      = ((out.val * (2 ^ 16 : Int) + ai.val * bi.val * (2 ^ 16 : Int)
            + aj.val * bj.val * zeta.val) : ZMod 3329)) :
    Spec.mont_reduce_pure (lift_fe_int r.val)
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          (Spec.mont_reduce_pure (lift_fe_int out.val))
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (lift_fe_mont ai) (lift_fe_mont bi))
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                (lift_fe_mont aj) (lift_fe_mont bj))
              (lift_fe_mont zeta))) := by
  -- LHS: feOfZMod ((r.val : ZMod q) * 169 * 169).
  rw [mont_reduce_pure_lift_fe_int]
  -- RHS: round-trip via canonicity.
  set s : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
      (Spec.mont_reduce_pure (lift_fe_int out.val))
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont ai) (lift_fe_mont bi))
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (lift_fe_mont aj) (lift_fe_mont bj))
          (lift_fe_mont zeta))) with hs_def
  have h_canon : s.val.val < 3329 := by
    have h_cs := libcrux_iot_ml_kem.Spec.Pure.Canonical_add_pure
      (Spec.mont_reduce_pure (lift_fe_int out.val))
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont ai) (lift_fe_mont bi))
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (lift_fe_mont aj) (lift_fe_mont bj))
          (lift_fe_mont zeta)))
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at h_cs
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cs
    exact h_cs
  have h_round_trip : feOfZMod (zmodOfFE s) = s :=
    feOfZMod_zmodOfFE_of_canonical s h_canon
  -- Push s through the 4 zmodOfFE projection lemmas to get a pure ZMod expression.
  have h_zmod_s : zmodOfFE s
      = (out.val : ZMod 3329) * 169 * 169
        + ((ai.val : ZMod 3329) * 169 * ((bi.val : ZMod 3329) * 169)
          + ((aj.val : ZMod 3329) * 169 * ((bj.val : ZMod 3329) * 169))
            * ((zeta.val : ZMod 3329) * 169)) := by
    simp only [hs_def,
      L2_8c.zmodOfFE_add_pure,
      L2_8c.zmodOfFE_mont_reduce_lift_fe_int,
      L2_8c.zmodOfFE_mul_pure,
      L2_8c.zmodOfFE_lift_fe_mont]
  -- Push h_zmod through ZMod, then `ring` closes.
  -- Goal after rw [← h_round_trip]: feOfZMod (((r.val : Int) : ZMod 3329) * 169 * 169) = feOfZMod (zmodOfFE s).
  rw [← h_round_trip, h_zmod_s]
  -- Goal: feOfZMod (... LHS ...) = feOfZMod (... RHS ...). Closed by congr 1 + ring on h_zmod.
  congr 1
  -- ZMod q equation: (r.val : ZMod q) * 169 * 169 = out * 169² + ai*169*(bi*169) + ((aj*169)*(bj*169))*(zeta*169).
  -- From h_zmod: r.val * R = out * R + ai*bi*R + aj*bj*zeta.
  -- The Mont-inversion identity: 2^16 * 169^2 ≡ 169 (mod q) and 2^16 * 169 ≡ 1 (mod q).
  have h_inv : ((2285 : ZMod 3329)) * 169 = 1 := by decide
  -- Push the cast `(2^16 : Int) : ZMod 3329` to 2285 in h_zmod.
  push_cast at h_zmod
  -- h_zmod : (r.val : ZMod q) * 2285 = out*2285 + ai*bi*2285 + aj*bj*zeta in ZMod q.
  -- Strategy: rewrite h_zmod with `* 169 * 169 * 169` on both sides, then use
  -- inv to collapse `2285 * 169 = 1` in each term, then `ring`.
  have h_mul_169_cubed :
      (r.val : ZMod 3329) * (2^16 : Int) * 169 * 169 * 169
        = ((out.val : ZMod 3329) * (2^16 : Int) + (ai.val : ZMod 3329) * (bi.val : ZMod 3329) * (2^16 : Int)
            + (aj.val : ZMod 3329) * (bj.val : ZMod 3329) * (zeta.val : ZMod 3329)) * 169 * 169 * 169 := by
    have := h_zmod
    push_cast at this ⊢
    rw [this]
  -- (2^16 : Int) : ZMod 3329 = 2285.
  have h_2_16 : ((2^16 : Int) : ZMod 3329) = 2285 := by decide
  rw [h_2_16] at h_mul_169_cubed
  -- Now: r * 2285 * 169 * 169 * 169 = (out * 2285 + ai*bi*2285 + aj*bj*zeta) * 169 * 169 * 169.
  -- LHS reduces: r * (2285*169) * 169 * 169 = r * 169 * 169 (using 2285*169 = 1).
  -- We want: r * 169 * 169 = out*169*169 + ai*169*(bi*169) + (aj*169*(bj*169))*(zeta*169).
  have h_lhs :
      (r.val : ZMod 3329) * 169 * 169
        = (r.val : ZMod 3329) * 2285 * 169 * 169 * 169 := by
    have : (r.val : ZMod 3329) * 169 * 169 = (r.val : ZMod 3329) * (2285 * 169) * 169 * 169 := by
      rw [h_inv]; ring
    rw [this]; ring
  rw [h_lhs, h_mul_169_cubed]
  -- Goal: (out*2285 + ai*bi*2285 + aj*bj*zeta) * 169 * 169 * 169
  --       = out*169*169 + (ai*169*(bi*169) + (aj*169*(bj*169))*(zeta*169)).
  -- Reorganize LHS by extracting `2285 * (169*169*169) = 169*169`:
  have h_expand : ((out.val : ZMod 3329) * 2285
            + (ai.val : ZMod 3329) * (bi.val : ZMod 3329) * 2285
            + (aj.val : ZMod 3329) * (bj.val : ZMod 3329) * (zeta.val : ZMod 3329))
          * 169 * 169 * 169
        = (out.val : ZMod 3329) * (2285 * (169 * 169 * 169))
          + (ai.val : ZMod 3329) * (bi.val : ZMod 3329) * (2285 * (169 * 169 * 169))
          + (aj.val : ZMod 3329) * (bj.val : ZMod 3329) * (zeta.val : ZMod 3329) * (169 * 169 * 169) := by
    ring
  have h_collapse : ((2285 : ZMod 3329)) * (169 * 169 * 169) = 169 * 169 := by decide
  rw [h_expand, h_collapse]
  ring

set_option maxHeartbeats 400000 in
/-- Odd-half version of `mont_reduce_even_fe_eq`. -/
theorem L2_8c.mont_reduce_odd_fe_eq
    (out r : Std.I32) (ai bi aj bj : Std.I16)
    (h_zmod : ((r.val * (2 ^ 16 : Int)) : ZMod 3329)
      = ((out.val * (2 ^ 16 : Int)
            + ai.val * bj.val * (2 ^ 16 : Int)
            + aj.val * bi.val * (2 ^ 16 : Int)) : ZMod 3329)) :
    Spec.mont_reduce_pure (lift_fe_int r.val)
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          (Spec.mont_reduce_pure (lift_fe_int out.val))
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (lift_fe_mont ai) (lift_fe_mont bj))
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (lift_fe_mont aj) (lift_fe_mont bi))) := by
  rw [mont_reduce_pure_lift_fe_int]
  set s : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
      (Spec.mont_reduce_pure (lift_fe_int out.val))
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont ai) (lift_fe_mont bj))
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont aj) (lift_fe_mont bi))) with hs_def
  have h_canon : s.val.val < 3329 := by
    have h_cs := libcrux_iot_ml_kem.Spec.Pure.Canonical_add_pure
      (Spec.mont_reduce_pure (lift_fe_int out.val))
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont ai) (lift_fe_mont bj))
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont aj) (lift_fe_mont bi)))
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at h_cs
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cs
    exact h_cs
  have h_round_trip : feOfZMod (zmodOfFE s) = s :=
    feOfZMod_zmodOfFE_of_canonical s h_canon
  have h_zmod_s : zmodOfFE s
      = (out.val : ZMod 3329) * 169 * 169
        + ((ai.val : ZMod 3329) * 169 * ((bj.val : ZMod 3329) * 169)
          + (aj.val : ZMod 3329) * 169 * ((bi.val : ZMod 3329) * 169)) := by
    simp only [hs_def,
      L2_8c.zmodOfFE_add_pure,
      L2_8c.zmodOfFE_mont_reduce_lift_fe_int,
      L2_8c.zmodOfFE_mul_pure,
      L2_8c.zmodOfFE_lift_fe_mont]
  rw [← h_round_trip, h_zmod_s]
  congr 1
  have h_inv : ((2285 : ZMod 3329)) * 169 = 1 := by decide
  -- Multiply h_zmod by 169^3 on both sides; cast (2^16 : Int) : ZMod q = 2285;
  -- collapse 2285*169 = 1 to leave 169^2 multipliers.
  have h_mul_169_cubed :
      (r.val : ZMod 3329) * (2^16 : Int) * 169 * 169 * 169
        = ((out.val : ZMod 3329) * (2^16 : Int)
            + (ai.val : ZMod 3329) * (bj.val : ZMod 3329) * (2^16 : Int)
            + (aj.val : ZMod 3329) * (bi.val : ZMod 3329) * (2^16 : Int)) * 169 * 169 * 169 := by
    have := h_zmod
    push_cast at this ⊢
    rw [this]
  have h_2_16 : ((2^16 : Int) : ZMod 3329) = 2285 := by decide
  rw [h_2_16] at h_mul_169_cubed
  have h_lhs :
      (r.val : ZMod 3329) * 169 * 169
        = (r.val : ZMod 3329) * 2285 * 169 * 169 * 169 := by
    have : (r.val : ZMod 3329) * 169 * 169 = (r.val : ZMod 3329) * (2285 * 169) * 169 * 169 := by
      rw [h_inv]; ring
    rw [this]; ring
  rw [h_lhs, h_mul_169_cubed]
  have : ((out.val : ZMod 3329) * 2285
            + (ai.val : ZMod 3329) * (bj.val : ZMod 3329) * 2285
            + (aj.val : ZMod 3329) * (bi.val : ZMod 3329) * 2285)
          * 169 * 169 * 169
        = (out.val : ZMod 3329) * (2285 * (169 * 169 * 169))
          + (ai.val : ZMod 3329) * (bj.val : ZMod 3329) * (2285 * (169 * 169 * 169))
          + (aj.val : ZMod 3329) * (bi.val : ZMod 3329) * (2285 * (169 * 169 * 169)) := by
    ring
  rw [this]
  rw [show ((2285 : ZMod 3329)) * (169 * 169 * 169) = 169 * 169 from by decide]
  ring

/-- Bound-propagation step for the L2.8c (and L2.8d) chained binomial
    composition: given a per-pair-update relation between `prev` and
    `next` slices (untouched lanes equal, touched lanes bounded), and
    a universal bound on `prev`, conclude the universal bound on `next`.

    Refactored from the 8-fold 16-way `interval_cases` boilerplate in
    the original L2.8c body. Each step now uses a 4-arg invocation
    instead of a 20-line case split. Also reusable by L2.8d cache
    variants (same impl structure: 8 binomial-pair updates). -/
theorem L2_8c.bnd_universal_step
    (prev next : Aeneas.Std.Slice Std.I32) (i : Nat) (hi : i < 8)
    (h_prev_universal : ∀ k : Fin 16,
      (prev.val[k.val]!).val.natAbs ≤ 2^30 + 2^25)
    (h_unc : ∀ k : Nat, k < 16 → k ≠ 2 * i → k ≠ 2 * i + 1 →
      next.val[k]! = prev.val[k]!)
    (h_at_even : (next.val[2 * i]!).val.natAbs ≤ 2^30 + 2^25)
    (h_at_odd : (next.val[2 * i + 1]!).val.natAbs ≤ 2^30 + 2^25) :
    ∀ k : Fin 16, (next.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 := by
  intro k
  by_cases h1 : k.val = 2 * i
  · rw [show k.val = 2 * i from h1]; exact h_at_even
  · by_cases h2 : k.val = 2 * i + 1
    · rw [show k.val = 2 * i + 1 from h2]; exact h_at_odd
    · rw [h_unc k.val k.isLt h1 h2]; exact h_prev_universal k

set_option maxHeartbeats 8000000 in
/-- Per-pair Triple for `accumulating_ntt_multiply_binomials`. Models the
    impl's per-pair contribution to the accumulator: reads `a[2i], a[2i+1]`,
    `b[2i], b[2i+1]`, multiplies + Montgomery-reduces to form an even and
    odd I32 delta, then `wrapping_add`s onto `out[2i], out[2i+1]`.

    POST exposes:
    - `r.length = 16` (Slice.update preserves length);
    - Untouched-lane preservation outside `{2i, 2i+1}`;
    - Relative bound: `|r.val[2i]!| ≤ |out.val[2i]!| + 2^25` (and 2i+1);
    - FE equation: the Mont-domain per-pair update agrees with
      `add (mont_reduce_pure old) (add (mul a₀_m b₀_m) (mul (mul a₁_m b₁_m) zeta_m))`
      for the even half, and the odd-half analog.

    Helper for L2.8c — 8 chained applications give
    `accumulating_ntt_multiply_fc`. -/
theorem accumulating_ntt_multiply_binomials_fc
    (a b : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i : Std.Usize)
    (out : Aeneas.Std.Slice Std.I32)
    (h_i : i.val < 8)
    (h_out_len : out.length = 16)
    (h_a : ∀ j : Fin 16, (a.elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_b : ∀ j : Fin 16, (b.elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_zeta : zeta.val.natAbs ≤ 1664)
    (h_out_bnd : ∀ k : Fin 16, (out.val[k.val]!).val.natAbs ≤ 2^30 + 2^25) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials
      a b zeta i out
    ⦃ ⇓ r => ⌜ r.length = 16
                ∧ (∀ k : Nat, k < 16 → k ≠ 2 * i.val → k ≠ 2 * i.val + 1 →
                    r.val[k]! = out.val[k]!)
                ∧ (r.val[2 * i.val]!).val.natAbs
                    ≤ (out.val[2 * i.val]!).val.natAbs + 2^25
                ∧ (r.val[2 * i.val + 1]!).val.natAbs
                    ≤ (out.val[2 * i.val + 1]!).val.natAbs + 2^25
                ∧ Spec.mont_reduce_pure (lift_fe_int (r.val[2 * i.val]!).val)
                    = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                        (Spec.mont_reduce_pure (lift_fe_int (out.val[2 * i.val]!).val))
                        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                            (lift_fe_mont (a.elements.val[2 * i.val]!))
                            (lift_fe_mont (b.elements.val[2 * i.val]!)))
                          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                              (lift_fe_mont (a.elements.val[2 * i.val + 1]!))
                              (lift_fe_mont (b.elements.val[2 * i.val + 1]!)))
                            (lift_fe_mont zeta)))
                ∧ Spec.mont_reduce_pure (lift_fe_int (r.val[2 * i.val + 1]!).val)
                    = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                        (Spec.mont_reduce_pure (lift_fe_int (out.val[2 * i.val + 1]!).val))
                        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                            (lift_fe_mont (a.elements.val[2 * i.val]!))
                            (lift_fe_mont (b.elements.val[2 * i.val + 1]!)))
                          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                            (lift_fe_mont (a.elements.val[2 * i.val + 1]!))
                            (lift_fe_mont (b.elements.val[2 * i.val]!)))) ⌝ ⦄ := by
  -- ===== Setup =====
  have h_2i_lt : 2 * i.val < 16 := by omega
  have h_2i1_lt : 2 * i.val + 1 < 16 := by omega
  have h_a_len : a.elements.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length a
  have h_b_len : b.elements.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length b
  have h_out_val_len : out.val.length = 16 := h_out_len
  -- Set up bound abbreviations.
  set ai_v : Std.I16 := a.elements.val[2 * i.val]! with hai_def
  set bi_v : Std.I16 := b.elements.val[2 * i.val]! with hbi_def
  set aj_v : Std.I16 := a.elements.val[2 * i.val + 1]! with haj_def
  set bj_v : Std.I16 := b.elements.val[2 * i.val + 1]! with hbj_def
  have h_ai : ai_v.val.natAbs ≤ 3328 := h_a ⟨2 * i.val, h_2i_lt⟩
  have h_bi : bi_v.val.natAbs ≤ 3328 := h_b ⟨2 * i.val, h_2i_lt⟩
  have h_aj : aj_v.val.natAbs ≤ 3328 := h_a ⟨2 * i.val + 1, h_2i1_lt⟩
  have h_bj : bj_v.val.natAbs ≤ 3328 := h_b ⟨2 * i.val + 1, h_2i1_lt⟩
  set old_e : Std.I32 := out.val[2 * i.val]! with hoe_def
  set old_o : Std.I32 := out.val[2 * i.val + 1]! with hoo_def
  have h_old_e_bnd : old_e.val.natAbs ≤ 2^30 + 2^25 := h_out_bnd ⟨2 * i.val, h_2i_lt⟩
  have h_old_o_bnd : old_o.val.natAbs ≤ 2^30 + 2^25 := h_out_bnd ⟨2 * i.val + 1, h_2i1_lt⟩
  -- ===== Index arithmetic =====
  obtain ⟨i1, h_i1_eq, h_i1_val⟩ :=
    usize_mul_ok_eq_fc 2#usize i (by scalar_tac)
  have h_i1_val' : i1.val = 2 * i.val := by
    rw [h_i1_val]; rfl
  obtain ⟨i2, h_i2_eq, h_i2_val⟩ :=
    usize_add_ok_eq_fc i1 1#usize (by scalar_tac)
  have h_i2_val' : i2.val = 2 * i.val + 1 := by
    rw [h_i2_val, h_i1_val']; rfl
  -- ===== Reads (with index_usize_ok_eq) =====
  have h_read_ai :
      Aeneas.Std.Array.index_usize a.elements i1 = .ok ai_v := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a.elements i1
      (by rw [h_a_len, h_i1_val']; exact h_2i_lt)
    rw [h, h_i1_val']
  have h_read_bi :
      Aeneas.Std.Array.index_usize b.elements i1 = .ok bi_v := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq b.elements i1
      (by rw [h_b_len, h_i1_val']; exact h_2i_lt)
    rw [h, h_i1_val']
  have h_read_aj :
      Aeneas.Std.Array.index_usize a.elements i2 = .ok aj_v := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a.elements i2
      (by rw [h_a_len, h_i2_val']; exact h_2i1_lt)
    rw [h, h_i2_val']
  have h_read_bj :
      Aeneas.Std.Array.index_usize b.elements i2 = .ok bj_v := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq b.elements i2
      (by rw [h_b_len, h_i2_val']; exact h_2i1_lt)
    rw [h, h_i2_val']
  -- ===== as_i32 casts =====
  set ai32 : Std.I32 := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 ai_v with hai32_def
  set bi32 : Std.I32 := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 bi_v with hbi32_def
  set aj32 : Std.I32 := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 aj_v with haj32_def
  set bj32 : Std.I32 := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 bj_v with hbj32_def
  set zeta32 : Std.I32 := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 zeta with hzeta32_def
  have h_ai32_val : ai32.val = ai_v.val := L2_8c.cast_I32_val ai_v
  have h_bi32_val : bi32.val = bi_v.val := L2_8c.cast_I32_val bi_v
  have h_aj32_val : aj32.val = aj_v.val := L2_8c.cast_I32_val aj_v
  have h_bj32_val : bj32.val = bj_v.val := L2_8c.cast_I32_val bj_v
  have h_zeta32_val : zeta32.val = zeta.val := L2_8c.cast_I32_val zeta
  -- as_i32 → .ok cast.
  have h_as_ai : libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 ai_v = .ok ai32 :=
    L2_8c.as_i32_val_eq ai_v
  have h_as_bi : libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 bi_v = .ok bi32 :=
    L2_8c.as_i32_val_eq bi_v
  have h_as_aj : libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 aj_v = .ok aj32 :=
    L2_8c.as_i32_val_eq aj_v
  have h_as_bj : libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 bj_v = .ok bj32 :=
    L2_8c.as_i32_val_eq bj_v
  have h_as_zeta : libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 zeta = .ok zeta32 :=
    L2_8c.as_i32_val_eq zeta
  -- ===== Step: ai_bi = wrapping_mul ai32 bi32, value = ai.val * bi.val =====
  set ai_bi : Std.I32 := Aeneas.Std.I32.wrapping_mul ai32 bi32 with habi_def
  have h_ai_bi_eq : CoreModels.core.num.I32.wrapping_mul ai32 bi32 = .ok ai_bi :=
    L2_8c.cm_wrapping_mul_i32_ok_eq ai32 bi32
  have h_ai_bi_val : ai_bi.val = ai_v.val * bi_v.val := by
    have h_bnd : (ai32.val * bi32.val).natAbs < 2^31 := by
      rw [h_ai32_val, h_bi32_val]
      have h := Int.natAbs_mul ai_v.val bi_v.val
      have : ai_v.val.natAbs * bi_v.val.natAbs ≤ 3328 * 3328 := by
        exact Nat.mul_le_mul h_ai h_bi
      rw [h]
      have : (3328 * 3328 : Nat) < 2^31 := by decide
      omega
    have := L2_8c.wrapping_mul_i32_no_overflow ai32 bi32 h_bnd
    rw [this, h_ai32_val, h_bi32_val]
  -- ===== Step: bj_zeta_ = wrapping_mul bj32 zeta32, value = bj.val * zeta.val =====
  set bj_zeta_ : Std.I32 := Aeneas.Std.I32.wrapping_mul bj32 zeta32 with hbjz_def
  have h_bj_zeta_eq : CoreModels.core.num.I32.wrapping_mul bj32 zeta32 = .ok bj_zeta_ :=
    L2_8c.cm_wrapping_mul_i32_ok_eq bj32 zeta32
  have h_bj_zeta_val : bj_zeta_.val = bj_v.val * zeta.val := by
    have h_bnd : (bj32.val * zeta32.val).natAbs < 2^31 := by
      rw [h_bj32_val, h_zeta32_val]
      rw [Int.natAbs_mul]
      have h_mul : bj_v.val.natAbs * zeta.val.natAbs ≤ 3328 * 1664 :=
        Nat.mul_le_mul h_bj h_zeta
      have : (3328 * 1664 : Nat) < 2^31 := by decide
      omega
    have := L2_8c.wrapping_mul_i32_no_overflow bj32 zeta32 h_bnd
    rw [this, h_bj32_val, h_zeta32_val]
  -- ===== Step: bj_zeta = montgomery_reduce_element bj_zeta_, |bj_zeta| ≤ 4993 =====
  have h_bj_zeta_pre : bj_zeta_.val.natAbs ≤ 2^16 * 3328 := by
    rw [h_bj_zeta_val]
    rw [Int.natAbs_mul]
    have h_mul : bj_v.val.natAbs * zeta.val.natAbs ≤ 3328 * 1664 :=
      Nat.mul_le_mul h_bj h_zeta
    have : (3328 * 1664 : Nat) ≤ 2^16 * 3328 := by decide
    omega
  obtain ⟨bj_zeta, h_bj_zeta_ok, h_bj_zeta_bnd, h_bj_zeta_lift⟩ :=
    triple_exists_ok_fc (montgomery_reduce_element_fc bj_zeta_ h_bj_zeta_pre)
  -- Also recover the legacy modq form: bj_zeta * 2^16 ≡ bj_zeta_ (mod q).
  -- We get it via the legacy spec.
  have h_bj_zeta_pre' : bj_zeta_.val.natAbs ≤ 3328 * 2^16 := by
    rw [show (3328 * 2^16 : Nat) = 2^16 * 3328 from by decide]; exact h_bj_zeta_pre
  obtain ⟨bj_zeta', h_bj_zeta_ok', _h_bnd', _h_tight, h_bj_zeta_modq⟩ :=
    triple_exists_ok_fc
      (libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.montgomery_reduce_element_spec bj_zeta_ h_bj_zeta_pre')
  have h_bj_zeta_eq2 : bj_zeta = bj_zeta' := by
    have h_both : (Result.ok bj_zeta : Result _) = Result.ok bj_zeta' := by
      rw [← h_bj_zeta_ok, h_bj_zeta_ok']
    cases h_both; rfl
  -- ===== Step: aj_bj_zeta = wrapping_mul aj32 (as_i32 bj_zeta), value = aj.val * bj_zeta.val =====
  set bj_zeta32 : Std.I32 :=
    Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 bj_zeta with hbjz32_def
  have h_bj_zeta32_val : bj_zeta32.val = bj_zeta.val := L2_8c.cast_I32_val bj_zeta
  have h_as_bj_zeta : libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 bj_zeta
      = .ok bj_zeta32 := L2_8c.as_i32_val_eq bj_zeta
  set aj_bj_zeta : Std.I32 := Aeneas.Std.I32.wrapping_mul aj32 bj_zeta32 with habjz_def
  have h_aj_bj_zeta_eq : CoreModels.core.num.I32.wrapping_mul aj32 bj_zeta32 = .ok aj_bj_zeta :=
    L2_8c.cm_wrapping_mul_i32_ok_eq aj32 bj_zeta32
  have h_aj_bj_zeta_val : aj_bj_zeta.val = aj_v.val * bj_zeta.val := by
    have h_bnd : (aj32.val * bj_zeta32.val).natAbs < 2^31 := by
      rw [h_aj32_val, h_bj_zeta32_val, Int.natAbs_mul]
      have h_mul : aj_v.val.natAbs * bj_zeta.val.natAbs ≤ 3328 * (3328 + 1665) :=
        Nat.mul_le_mul h_aj h_bj_zeta_bnd
      have : (3328 * (3328 + 1665) : Nat) < 2^31 := by decide
      omega
    have := L2_8c.wrapping_mul_i32_no_overflow aj32 bj_zeta32 h_bnd
    rw [this, h_aj32_val, h_bj_zeta32_val]
  -- ===== Step: ai_bi_aj_bj = wrapping_add ai_bi aj_bj_zeta =====
  set ai_bi_aj_bj : Std.I32 := Aeneas.Std.I32.wrapping_add ai_bi aj_bj_zeta with hsum_e_def
  have h_sum_e_eq : CoreModels.core.num.I32.wrapping_add ai_bi aj_bj_zeta = .ok ai_bi_aj_bj :=
    L2_8c.cm_wrapping_add_i32_ok_eq ai_bi aj_bj_zeta
  -- Even-delta bound: |ai*bi + aj*bj_zeta| ≤ 3328² + 3328·4993 ≤ 2^25 (precise: ~28M < 33.5M).
  have h_sum_e_bnd : (ai_bi.val + aj_bj_zeta.val).natAbs ≤ 3328 * 3328 + 3328 * (3328 + 1665) := by
    rw [h_ai_bi_val, h_aj_bj_zeta_val]
    have h_e1 : (ai_v.val * bi_v.val).natAbs ≤ 3328 * 3328 := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul h_ai h_bi
    have h_e2 : (aj_v.val * bj_zeta.val).natAbs ≤ 3328 * (3328 + 1665) := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul h_aj h_bj_zeta_bnd
    have h_tri : ((ai_v.val * bi_v.val) + (aj_v.val * bj_zeta.val)).natAbs
                  ≤ (ai_v.val * bi_v.val).natAbs + (aj_v.val * bj_zeta.val).natAbs :=
      Int.natAbs_add_le _ _
    omega
  have h_sum_e_val : ai_bi_aj_bj.val = ai_bi.val + aj_bj_zeta.val := by
    have h_bnd : (ai_bi.val + aj_bj_zeta.val).natAbs < 2^31 := by
      have h_le : (3328 * 3328 + 3328 * (3328 + 1665) : Nat) < 2^31 := by decide
      omega
    exact L2_8c.wrapping_add_i32_no_overflow ai_bi aj_bj_zeta h_bnd
  -- Bound the delta_even by 2^25:
  have h_delta_e_bnd : ai_bi_aj_bj.val.natAbs ≤ 2^25 := by
    rw [h_sum_e_val]
    have : (3328 * 3328 + 3328 * (3328 + 1665) : Nat) ≤ 2^25 := by decide
    omega
  -- ===== Step: ai_bj = wrapping_mul ai32 bj32, value = ai*bj =====
  set ai_bj_p : Std.I32 := Aeneas.Std.I32.wrapping_mul ai32 bj32 with haibj_def
  have h_ai_bj_eq : CoreModels.core.num.I32.wrapping_mul ai32 bj32 = .ok ai_bj_p :=
    L2_8c.cm_wrapping_mul_i32_ok_eq ai32 bj32
  have h_ai_bj_val : ai_bj_p.val = ai_v.val * bj_v.val := by
    have h_bnd : (ai32.val * bj32.val).natAbs < 2^31 := by
      rw [h_ai32_val, h_bj32_val, Int.natAbs_mul]
      have h_mul : ai_v.val.natAbs * bj_v.val.natAbs ≤ 3328 * 3328 :=
        Nat.mul_le_mul h_ai h_bj
      have : (3328 * 3328 : Nat) < 2^31 := by decide
      omega
    have := L2_8c.wrapping_mul_i32_no_overflow ai32 bj32 h_bnd
    rw [this, h_ai32_val, h_bj32_val]
  -- ===== Step: aj_bi = wrapping_mul aj32 bi32 =====
  set aj_bi_p : Std.I32 := Aeneas.Std.I32.wrapping_mul aj32 bi32 with hajbi_def
  have h_aj_bi_eq : CoreModels.core.num.I32.wrapping_mul aj32 bi32 = .ok aj_bi_p :=
    L2_8c.cm_wrapping_mul_i32_ok_eq aj32 bi32
  have h_aj_bi_val : aj_bi_p.val = aj_v.val * bi_v.val := by
    have h_bnd : (aj32.val * bi32.val).natAbs < 2^31 := by
      rw [h_aj32_val, h_bi32_val, Int.natAbs_mul]
      have h_mul : aj_v.val.natAbs * bi_v.val.natAbs ≤ 3328 * 3328 :=
        Nat.mul_le_mul h_aj h_bi
      have : (3328 * 3328 : Nat) < 2^31 := by decide
      omega
    have := L2_8c.wrapping_mul_i32_no_overflow aj32 bi32 h_bnd
    rw [this, h_aj32_val, h_bi32_val]
  -- ===== Step: ai_bj_aj_bi = wrapping_add ai_bj aj_bi, value = ai*bj + aj*bi =====
  set ai_bj_aj_bi : Std.I32 := Aeneas.Std.I32.wrapping_add ai_bj_p aj_bi_p with hsum_o_def
  have h_sum_o_eq : CoreModels.core.num.I32.wrapping_add ai_bj_p aj_bi_p = .ok ai_bj_aj_bi :=
    L2_8c.cm_wrapping_add_i32_ok_eq ai_bj_p aj_bi_p
  have h_sum_o_bnd : (ai_bj_p.val + aj_bi_p.val).natAbs ≤ 2 * 3328 * 3328 := by
    rw [h_ai_bj_val, h_aj_bi_val]
    have h_e1 : (ai_v.val * bj_v.val).natAbs ≤ 3328 * 3328 := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul h_ai h_bj
    have h_e2 : (aj_v.val * bi_v.val).natAbs ≤ 3328 * 3328 := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul h_aj h_bi
    have h_tri := Int.natAbs_add_le (ai_v.val * bj_v.val) (aj_v.val * bi_v.val)
    omega
  have h_sum_o_val : ai_bj_aj_bi.val = ai_bj_p.val + aj_bi_p.val := by
    have h_bnd : (ai_bj_p.val + aj_bi_p.val).natAbs < 2^31 := by
      have : (2 * 3328 * 3328 : Nat) < 2^31 := by decide
      omega
    exact L2_8c.wrapping_add_i32_no_overflow ai_bj_p aj_bi_p h_bnd
  have h_delta_o_bnd : ai_bj_aj_bi.val.natAbs ≤ 2^25 := by
    rw [h_sum_o_val]
    have : (2 * 3328 * 3328 : Nat) ≤ 2^25 := by decide
    omega
  -- ===== Slice reads + writes for `out` =====
  -- Step: i10 = out[i1] (= old_e at i1.val = 2*i.val).
  have h_read_old_e : Aeneas.Std.Slice.index_usize out i1 = .ok old_e := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq out i1
      (by rw [h_out_val_len, h_i1_val']; exact h_2i_lt)
    rw [h, h_i1_val']
  -- Step: i11 = wrapping_add old_e ai_bi_aj_bj (the new lane 2i value).
  set new_e : Std.I32 := Aeneas.Std.I32.wrapping_add old_e ai_bi_aj_bj with hne_def
  have h_new_e_eq : CoreModels.core.num.I32.wrapping_add old_e ai_bi_aj_bj = .ok new_e :=
    L2_8c.cm_wrapping_add_i32_ok_eq old_e ai_bi_aj_bj
  -- new_e.val = old_e.val + delta_e (no overflow: |old_e| ≤ 2^30, |delta_e| ≤ 2^25).
  have h_new_e_val : new_e.val = old_e.val + ai_bi_aj_bj.val := by
    have h_bnd : (old_e.val + ai_bi_aj_bj.val).natAbs < 2^31 := by
      have h_tri := Int.natAbs_add_le old_e.val ai_bi_aj_bj.val
      have : (2^30 + 2^25 + 2^25 : Nat) < 2^31 := by decide
      omega
    exact L2_8c.wrapping_add_i32_no_overflow old_e ai_bi_aj_bj h_bnd
  have h_new_e_bnd : new_e.val.natAbs ≤ old_e.val.natAbs + 2^25 := by
    rw [h_new_e_val]
    have h_tri := Int.natAbs_add_le old_e.val ai_bi_aj_bj.val
    omega
  -- Step: out1 = Slice.update out i1 new_e (= out.set i1 new_e).
  have h_upd_e : Aeneas.Std.Slice.update out i1 new_e = .ok (out.set i1 new_e) := by
    have hT := Aeneas.Std.Slice.update_spec out i1 new_e (by rw [h_out_len, h_i1_val']; exact h_2i_lt)
    obtain ⟨v', h_eq, h_v'⟩ := Aeneas.Std.WP.spec_imp_exists hT
    rw [h_eq, h_v']
  set out1 : Aeneas.Std.Slice Std.I32 := out.set i1 new_e with hout1_def
  -- The impl computes `i12 = i1 + 1#usize` again (extracted as identical
  -- to i2). After `simp only [h_i2_eq]` in the body composition, all four
  -- `i1 + 1#usize` occurrences collapse to i2. So we state subsequent
  -- reads/writes directly with i2.
  have h_out1_len : out1.length = 16 := by simp [hout1_def]; exact h_out_len
  have h_out1_val_len : out1.val.length = 16 := h_out1_len
  have h_old_o_in_out1 : out1.val[i2.val]! = old_o := by
    have h_set_val : out1.val = out.val.set i1.val new_e := by
      simp [hout1_def, Aeneas.Std.Slice.set_val_eq]
    have h_ne : 2 * i.val + 1 ≠ i1.val := by rw [h_i1_val']; omega
    have h_lt : 2 * i.val + 1 < out.val.length := by rw [h_out_val_len]; exact h_2i1_lt
    rw [h_set_val, h_i2_val', hoo_def]
    have h_lt_set : 2 * i.val + 1 < (out.val.set i1.val new_e).length := by
      rw [List.length_set]; exact h_lt
    rw [getElem!_pos (out.val.set i1.val new_e) (2 * i.val + 1) h_lt_set]
    rw [getElem!_pos out.val (2 * i.val + 1) h_lt]
    rw [List.getElem_set_ne (Ne.symm h_ne)]
  have h_read_old_o : Aeneas.Std.Slice.index_usize out1 i2 = .ok old_o := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq out1 i2
      (by rw [h_out1_val_len, h_i2_val']; exact h_2i1_lt)
    rw [h, h_old_o_in_out1]
  -- Step: i14 = wrapping_add old_o ai_bj_aj_bi (new lane 2i+1 value).
  set new_o : Std.I32 := Aeneas.Std.I32.wrapping_add old_o ai_bj_aj_bi with hno_def
  have h_new_o_eq : CoreModels.core.num.I32.wrapping_add old_o ai_bj_aj_bi = .ok new_o :=
    L2_8c.cm_wrapping_add_i32_ok_eq old_o ai_bj_aj_bi
  have h_new_o_val : new_o.val = old_o.val + ai_bj_aj_bi.val := by
    have h_bnd : (old_o.val + ai_bj_aj_bi.val).natAbs < 2^31 := by
      have h_tri := Int.natAbs_add_le old_o.val ai_bj_aj_bi.val
      have : (2^30 + 2^25 + 2^25 : Nat) < 2^31 := by decide
      omega
    exact L2_8c.wrapping_add_i32_no_overflow old_o ai_bj_aj_bi h_bnd
  have h_new_o_bnd : new_o.val.natAbs ≤ old_o.val.natAbs + 2^25 := by
    rw [h_new_o_val]
    have h_tri := Int.natAbs_add_le old_o.val ai_bj_aj_bi.val
    omega
  have h_upd_o : Aeneas.Std.Slice.update out1 i2 new_o = .ok (out1.set i2 new_o) := by
    have hT := Aeneas.Std.Slice.update_spec out1 i2 new_o
      (by rw [h_out1_len, h_i2_val']; exact h_2i1_lt)
    obtain ⟨v', h_eq, h_v'⟩ := Aeneas.Std.WP.spec_imp_exists hT
    rw [h_eq, h_v']
  set out2 : Aeneas.Std.Slice Std.I32 := out1.set i2 new_o with hout2_def
  -- ===== Compose the monadic chain =====
  -- The four `i1 + 1#usize` invocations all yield i2 (same Lean expression).
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials
        a b zeta i out = .ok out2 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials
    simp only [h_i1_eq, h_i2_eq, h_read_ai, h_read_bi, h_read_aj, h_read_bj,
               h_as_ai, h_as_bi, h_as_aj, h_as_bj, h_as_zeta, h_as_bj_zeta,
               h_ai_bi_eq, h_bj_zeta_eq, h_bj_zeta_ok, h_aj_bj_zeta_eq,
               h_sum_e_eq, h_ai_bj_eq, h_aj_bi_eq, h_sum_o_eq,
               h_read_old_e, h_new_e_eq, h_upd_e,
               h_read_old_o, h_new_o_eq, h_upd_o,
               Aeneas.Std.bind_tc_ok]
  apply triple_of_ok_fc h_body
  -- ===== POST: 6-conjunct =====
  -- Useful: out2.val unfolding.
  have h_out2_val : out2.val = (out.val.set i1.val new_e).set i2.val new_o := by
    show ((out.set i1 new_e).set i2 new_o).val = _
    rw [Aeneas.Std.Slice.set_val_eq, Aeneas.Std.Slice.set_val_eq]
  have h_out2_len : out2.length = 16 := by
    show ((out.set i1 new_e).set i2 new_o).length = 16
    rw [Aeneas.Std.Slice.set_length, Aeneas.Std.Slice.set_length]; exact h_out_len
  have h_out2_val_len : out2.val.length = 16 := h_out2_len
  -- Out2 at 2*i (= i1.val) = new_e. Out2 at 2*i+1 (= i2.val) = new_o.
  have h_out2_at_2i : out2.val[2 * i.val]! = new_e := by
    rw [h_out2_val, ← h_i1_val']
    have h_lt_out : i1.val < out.val.length := by rw [h_out_val_len, h_i1_val']; exact h_2i_lt
    have h_lt1 : i1.val < (out.val.set i1.val new_e).length := by
      rw [List.length_set]; exact h_lt_out
    have h_lt2 : i1.val < ((out.val.set i1.val new_e).set i2.val new_o).length := by
      rw [List.length_set]; exact h_lt1
    rw [getElem!_pos ((out.val.set i1.val new_e).set i2.val new_o) i1.val h_lt2]
    rw [List.getElem_set_ne (by rw [h_i2_val', h_i1_val']; omega)]
    rw [List.getElem_set_self]
  have h_out2_at_2i1 : out2.val[2 * i.val + 1]! = new_o := by
    rw [h_out2_val, ← h_i2_val']
    have h_lt_out : i2.val < out.val.length := by rw [h_out_val_len, h_i2_val']; exact h_2i1_lt
    have h_lt1 : i2.val < (out.val.set i1.val new_e).length := by
      rw [List.length_set]; exact h_lt_out
    have h_lt2 : i2.val < ((out.val.set i1.val new_e).set i2.val new_o).length := by
      rw [List.length_set]; exact h_lt1
    rw [getElem!_pos ((out.val.set i1.val new_e).set i2.val new_o) i2.val h_lt2]
    rw [List.getElem_set_self]
  -- Untouched: for k ∉ {2i, 2i+1}, out2.val[k]! = out.val[k]!.
  have h_out2_untouched : ∀ k : Nat, k < 16 → k ≠ 2 * i.val → k ≠ 2 * i.val + 1 →
      out2.val[k]! = out.val[k]! := by
    intro k hk hki hkj
    rw [h_out2_val]
    have h_lt_out : k < out.val.length := by rw [h_out_val_len]; exact hk
    have h_lt1 : k < (out.val.set i1.val new_e).length := by rw [List.length_set]; exact h_lt_out
    have h_lt2 : k < ((out.val.set i1.val new_e).set i2.val new_o).length := by
      rw [List.length_set]; exact h_lt1
    rw [getElem!_pos ((out.val.set i1.val new_e).set i2.val new_o) k h_lt2]
    rw [getElem!_pos out.val k h_lt_out]
    rw [List.getElem_set_ne (by rw [h_i2_val']; omega)]
    rw [List.getElem_set_ne (by rw [h_i1_val']; omega)]
  -- Now produce the 6-conjunct.
  refine ⟨h_out2_len, ?_, ?_, ?_, ?_, ?_⟩
  · -- Untouched lanes.
    exact h_out2_untouched
  · -- Bound at 2*i.
    rw [h_out2_at_2i]
    -- new_e.val.natAbs ≤ old_e.val.natAbs + 2^25; old_e = out.val[2*i]!.
    rw [hoe_def] at h_new_e_bnd
    exact h_new_e_bnd
  · -- Bound at 2*i+1.
    rw [h_out2_at_2i1]
    rw [hoo_def] at h_new_o_bnd
    exact h_new_o_bnd
  · -- FE eq (even half).
    rw [h_out2_at_2i, hoe_def]
    -- Goal: mont_reduce_pure (lift_fe_int new_e.val) = ...
    -- Convert modq form `bj_zeta'.val ≡ bj_zeta_.val * 169` into ZMod eq.
    have h_modq_cast : ((bj_zeta'.val : Int) : ZMod 3329)
        = ((bj_zeta_.val * 169 : Int) : ZMod 3329) :=
      modq_eq_cast_zmod _ _ h_bj_zeta_modq
    rw [h_bj_zeta_eq2.symm] at h_modq_cast
    rw [h_bj_zeta_val] at h_modq_cast
    push_cast at h_modq_cast
    -- h_modq_cast : (bj_zeta.val : ZMod 3329) = (bj_v.val : ZMod q) * zeta.val * 169.
    apply L2_8c.mont_reduce_even_fe_eq
      (out := out.val[2 * i.val]!) (r := new_e)
      (ai := ai_v) (bi := bi_v) (aj := aj_v) (bj := bj_v) (zeta := zeta)
    -- Goal: (new_e.val * 2^16 : ZMod q) = (out * 2^16 + ai*bi*2^16 + aj*bj*zeta : ZMod q).
    rw [← hoe_def, h_new_e_val, h_sum_e_val, h_ai_bi_val, h_aj_bj_zeta_val]
    push_cast
    -- LHS: (old_e + ai*bi + aj*bj_zeta) * 2^16 in ZMod q.
    -- Use h_modq_cast to substitute bj_zeta.val = bj.val * zeta.val * 169.
    rw [h_modq_cast]
    -- 2^16 * 169 ≡ 1 (mod q), so 2285 * 169 = 1 in ZMod q.
    have h_inv : ((2285 : ZMod 3329)) * 169 = 1 := by decide
    -- Algebraic identity: (old + ai*bi + aj*(bj*zeta*169)) * 2285
    --                    = old*2285 + ai*bi*2285 + aj*bj*zeta*(2285*169)
    --                    = old*2285 + ai*bi*2285 + aj*bj*zeta.
    calc ((old_e.val : ZMod 3329) + ((ai_v.val : ZMod 3329) * (bi_v.val : ZMod 3329)
          + (aj_v.val : ZMod 3329) * ((bj_v.val : ZMod 3329) * (zeta.val : ZMod 3329) * 169)))
            * 2285
        = (old_e.val : ZMod 3329) * 2285
          + (ai_v.val : ZMod 3329) * (bi_v.val : ZMod 3329) * 2285
          + (aj_v.val : ZMod 3329) * (bj_v.val : ZMod 3329) * (zeta.val : ZMod 3329)
              * (2285 * 169) := by ring
      _ = (old_e.val : ZMod 3329) * 2285
          + (ai_v.val : ZMod 3329) * (bi_v.val : ZMod 3329) * 2285
          + (aj_v.val : ZMod 3329) * (bj_v.val : ZMod 3329) * (zeta.val : ZMod 3329) := by
            rw [h_inv]; ring
  · -- FE eq (odd half).
    rw [h_out2_at_2i1, hoo_def]
    apply L2_8c.mont_reduce_odd_fe_eq
      (out := out.val[2 * i.val + 1]!) (r := new_o)
      (ai := ai_v) (bi := bi_v) (aj := aj_v) (bj := bj_v)
    rw [← hoo_def, h_new_o_val, h_sum_o_val, h_ai_bj_val, h_aj_bi_val]
    push_cast
    ring


set_option maxHeartbeats 4000000 in
/-- L2.8 — `vector.portable.ntt.accumulating_ntt_multiply`: base-case
    NTT-domain multiply on a 16-lane vector chunk.

    The impl chains 8
    `accumulating_ntt_multiply_binomials` calls, each accumulating one
    coefficient pair via the degree-2 polynomial multiply mod (X²−ζ²).
    The 4 input zetas yield 8 effective zetas with alternating
    positive/negative signs across consecutive pair positions.

    POST defers algebraic shape to `ntt_multiply_base_case_post`.
    Preconditions: input chunks canonical (`natAbs ≤ 3328`), zetas
    bounded by the table range (`natAbs ≤ 1664`), accumulator slice
    length 16 (so the 8 pair indices 0..15 are all in range), AND
    each accumulator lane bounded by `2^30` (wrap-protection for the
    8 `wrapping_add` calls — per-lane delta is ≤ 2^25 so output stays
    well within I32 range; `2^30` headroom supports ~32 chained calls).

    POST adds a relative bound conjunct (`|r[k]| ≤ |out[k]| + 2^25`)
    so callers (L6.3, then L7) can chain L2.8 invocations without
    losing track of the accumulator's I32 bound. Mirrors the inverse-NTT bound-infra cascade (see
    `[[project_inverse_ntt_bound_infra_asymmetry]]`).

    [F*-port: Vector.Portable.Ntt.ntt_multiply_binomials + ntt_multiply
     (lines 432-584; Chunk.fst:587-625 commute lemma). F*-pre:
     vector/portable/ntt.rs:339-345 — each accumulator lane within
     i32 range.] -/
@[spec]
theorem accumulating_ntt_multiply_fc
    (lhs rhs : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Aeneas.Std.Slice Std.I32)
    (zeta0 zeta1 zeta2 zeta3 : Std.I16)
    (h_out_len : out.length = 16)
    (h_lhs : ∀ j : Fin 16, (lhs.elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_rhs : ∀ j : Fin 16, (rhs.elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_zeta0 : zeta0.val.natAbs ≤ 1664)
    (h_zeta1 : zeta1.val.natAbs ≤ 1664)
    (h_zeta2 : zeta2.val.natAbs ≤ 1664)
    (h_zeta3 : zeta3.val.natAbs ≤ 1664)
    (h_out_bnd : ∀ k : Fin 16, (out.val[k.val]!).val.natAbs ≤ 2^30) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply
      lhs rhs out zeta0 zeta1 zeta2 zeta3
    ⦃ ⇓ r => ⌜ r.length = 16 ∧
              (∀ k : Fin 16, (r.val[k.val]!).val.natAbs
                              ≤ (out.val[k.val]!).val.natAbs + 2^25) ∧
              ntt_multiply_base_case_post lhs rhs
                zeta0 zeta1 zeta2 zeta3 out r ⌝ ⦄ := by
  have h_zeta_within (z : Std.I16) (hz : z.val.natAbs ≤ 1664) :
      z.val.natAbs ≤ 2^15 - 1 := by omega
  have h_n0_val := L2_8c.wrapping_neg_val_eq zeta0 (h_zeta_within _ h_zeta0)
  have h_n1_val := L2_8c.wrapping_neg_val_eq zeta1 (h_zeta_within _ h_zeta1)
  have h_n2_val := L2_8c.wrapping_neg_val_eq zeta2 (h_zeta_within _ h_zeta2)
  have h_n3_val := L2_8c.wrapping_neg_val_eq zeta3 (h_zeta_within _ h_zeta3)
  set nzeta0 : Std.I16 := Aeneas.Std.I16.wrapping_sub (0#i16) zeta0 with hn0_def
  set nzeta1 : Std.I16 := Aeneas.Std.I16.wrapping_sub (0#i16) zeta1 with hn1_def
  set nzeta2 : Std.I16 := Aeneas.Std.I16.wrapping_sub (0#i16) zeta2 with hn2_def
  set nzeta3 : Std.I16 := Aeneas.Std.I16.wrapping_sub (0#i16) zeta3 with hn3_def
  have h_nz0_bnd : nzeta0.val.natAbs ≤ 1664 := by rw [h_n0_val]; omega
  have h_nz1_bnd : nzeta1.val.natAbs ≤ 1664 := by rw [h_n1_val]; omega
  have h_nz2_bnd : nzeta2.val.natAbs ≤ 1664 := by rw [h_n2_val]; omega
  have h_nz3_bnd : nzeta3.val.natAbs ≤ 1664 := by rw [h_n3_val]; omega
  have h_n0_fe : lift_fe_mont nzeta0
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta0) :=
    L2_8c.lift_fe_mont_neg_pure_eq zeta0 nzeta0 (h_zeta_within _ h_zeta0) h_n0_val
  have h_n1_fe : lift_fe_mont nzeta1
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta1) :=
    L2_8c.lift_fe_mont_neg_pure_eq zeta1 nzeta1 (h_zeta_within _ h_zeta1) h_n1_val
  have h_n2_fe : lift_fe_mont nzeta2
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta2) :=
    L2_8c.lift_fe_mont_neg_pure_eq zeta2 nzeta2 (h_zeta_within _ h_zeta2) h_n2_val
  have h_n3_fe : lift_fe_mont nzeta3
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta3) :=
    L2_8c.lift_fe_mont_neg_pure_eq zeta3 nzeta3 (h_zeta_within _ h_zeta3) h_n3_val
  have h_wn0 : core.num.I16.wrapping_neg zeta0 = .ok nzeta0 :=
    L2_8c.cm_wrapping_neg_i16_ok_eq zeta0
  have h_wn1 : core.num.I16.wrapping_neg zeta1 = .ok nzeta1 :=
    L2_8c.cm_wrapping_neg_i16_ok_eq zeta1
  have h_wn2 : core.num.I16.wrapping_neg zeta2 = .ok nzeta2 :=
    L2_8c.cm_wrapping_neg_i16_ok_eq zeta2
  have h_wn3 : core.num.I16.wrapping_neg zeta3 = .ok nzeta3 :=
    L2_8c.cm_wrapping_neg_i16_ok_eq zeta3
  have h_cz0 : libcrux_secrets.traits.Classify.Blanket.classify zeta0 = .ok zeta0 :=
    L2_8c.classify_ok_eq zeta0
  have h_cnz0 : libcrux_secrets.traits.Classify.Blanket.classify nzeta0 = .ok nzeta0 :=
    L2_8c.classify_ok_eq nzeta0
  have h_cz1 : libcrux_secrets.traits.Classify.Blanket.classify zeta1 = .ok zeta1 :=
    L2_8c.classify_ok_eq zeta1
  have h_cnz1 : libcrux_secrets.traits.Classify.Blanket.classify nzeta1 = .ok nzeta1 :=
    L2_8c.classify_ok_eq nzeta1
  have h_cz2 : libcrux_secrets.traits.Classify.Blanket.classify zeta2 = .ok zeta2 :=
    L2_8c.classify_ok_eq zeta2
  have h_cnz2 : libcrux_secrets.traits.Classify.Blanket.classify nzeta2 = .ok nzeta2 :=
    L2_8c.classify_ok_eq nzeta2
  have h_cz3 : libcrux_secrets.traits.Classify.Blanket.classify zeta3 = .ok zeta3 :=
    L2_8c.classify_ok_eq zeta3
  have h_cnz3 : libcrux_secrets.traits.Classify.Blanket.classify nzeta3 = .ok nzeta3 :=
    L2_8c.classify_ok_eq nzeta3
  have h_out_bnd_universal : ∀ k : Fin 16, (out.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 := by
    intro k; have := h_out_bnd k; omega
  -- Call 0: pair 0 with zeta0 (touches lanes 0, 1).
  obtain ⟨r0, h_r0_eq, h_r0_len, h_r0_unc, h_r0_bnd_e, h_r0_bnd_o,
          h_r0_fe_e, h_r0_fe_o⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_fc lhs rhs zeta0 0#usize out
        (by decide) h_out_len h_lhs h_rhs h_zeta0 h_out_bnd_universal)
  have h_src_at_even : out.val[0]! = out.val[0]! := rfl
  have h_src_at_odd : out.val[1]! = out.val[1]! := rfl
  have h_r0_at_even : (r0.val[0]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (0#usize : Std.Usize).val : Nat) = 0 := by decide
    have h_b := h_r0_bnd_e
    rw [h_eq] at h_b
    rw [h_src_at_even] at h_b
    have h_out_le := h_out_bnd ⟨0, by decide⟩
    simp only at h_out_le; omega
  have h_r0_at_odd : (r0.val[1]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (0#usize : Std.Usize).val + 1 : Nat) = 1 := by decide
    have h_b := h_r0_bnd_o
    rw [h_eq] at h_b
    rw [h_src_at_odd] at h_b
    have h_out_le := h_out_bnd ⟨1, by decide⟩
    simp only at h_out_le; omega
  have h_r0_unc' : ∀ k : Nat, k < 16 → k ≠ 0 → k ≠ 1 →
      r0.val[k]! = out.val[k]! := by
    intro k hk hke hko
    have h_eq_e : (2 * (0#usize : Std.Usize).val : Nat) = 0 := by decide
    have h_eq_o : (2 * (0#usize : Std.Usize).val + 1 : Nat) = 1 := by decide
    apply h_r0_unc k hk
    · rw [h_eq_e]; exact hke
    · rw [h_eq_o]; exact hko
  have h_r0_bnd_universal : ∀ k : Fin 16, (r0.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step out r0 0 (by decide) h_out_bnd_universal
      h_r0_unc' h_r0_at_even h_r0_at_odd

  -- Call 1: pair 1 with nzeta0 (touches lanes 2, 3).
  obtain ⟨r1, h_r1_eq, h_r1_len, h_r1_unc, h_r1_bnd_e, h_r1_bnd_o,
          h_r1_fe_e, h_r1_fe_o⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_fc lhs rhs nzeta0 1#usize r0
        (by decide) h_r0_len h_lhs h_rhs h_nz0_bnd h_r0_bnd_universal)
  have h_src_at_even : r0.val[2]! = out.val[2]! := by
    rw [h_r0_unc' 2 (by decide) (by decide) (by decide)]
  have h_src_at_odd : r0.val[3]! = out.val[3]! := by
    rw [h_r0_unc' 3 (by decide) (by decide) (by decide)]
  have h_r1_at_even : (r1.val[2]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (1#usize : Std.Usize).val : Nat) = 2 := by decide
    have h_b := h_r1_bnd_e
    rw [h_eq] at h_b
    rw [h_src_at_even] at h_b
    have h_out_le := h_out_bnd ⟨2, by decide⟩
    simp only at h_out_le; omega
  have h_r1_at_odd : (r1.val[3]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (1#usize : Std.Usize).val + 1 : Nat) = 3 := by decide
    have h_b := h_r1_bnd_o
    rw [h_eq] at h_b
    rw [h_src_at_odd] at h_b
    have h_out_le := h_out_bnd ⟨3, by decide⟩
    simp only at h_out_le; omega
  have h_r1_unc' : ∀ k : Nat, k < 16 → k ≠ 2 → k ≠ 3 →
      r1.val[k]! = r0.val[k]! := by
    intro k hk hke hko
    have h_eq_e : (2 * (1#usize : Std.Usize).val : Nat) = 2 := by decide
    have h_eq_o : (2 * (1#usize : Std.Usize).val + 1 : Nat) = 3 := by decide
    apply h_r1_unc k hk
    · rw [h_eq_e]; exact hke
    · rw [h_eq_o]; exact hko
  have h_r1_bnd_universal : ∀ k : Fin 16, (r1.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r0 r1 1 (by decide) h_r0_bnd_universal
      h_r1_unc' h_r1_at_even h_r1_at_odd

  -- Call 2: pair 2 with zeta1 (touches lanes 4, 5).
  obtain ⟨r2, h_r2_eq, h_r2_len, h_r2_unc, h_r2_bnd_e, h_r2_bnd_o,
          h_r2_fe_e, h_r2_fe_o⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_fc lhs rhs zeta1 2#usize r1
        (by decide) h_r1_len h_lhs h_rhs h_zeta1 h_r1_bnd_universal)
  have h_src_at_even : r1.val[4]! = out.val[4]! := by
    rw [h_r1_unc' 4 (by decide) (by decide) (by decide)]
    rw [h_r0_unc' 4 (by decide) (by decide) (by decide)]
  have h_src_at_odd : r1.val[5]! = out.val[5]! := by
    rw [h_r1_unc' 5 (by decide) (by decide) (by decide)]
    rw [h_r0_unc' 5 (by decide) (by decide) (by decide)]
  have h_r2_at_even : (r2.val[4]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (2#usize : Std.Usize).val : Nat) = 4 := by decide
    have h_b := h_r2_bnd_e
    rw [h_eq] at h_b
    rw [h_src_at_even] at h_b
    have h_out_le := h_out_bnd ⟨4, by decide⟩
    simp only at h_out_le; omega
  have h_r2_at_odd : (r2.val[5]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (2#usize : Std.Usize).val + 1 : Nat) = 5 := by decide
    have h_b := h_r2_bnd_o
    rw [h_eq] at h_b
    rw [h_src_at_odd] at h_b
    have h_out_le := h_out_bnd ⟨5, by decide⟩
    simp only at h_out_le; omega
  have h_r2_unc' : ∀ k : Nat, k < 16 → k ≠ 4 → k ≠ 5 →
      r2.val[k]! = r1.val[k]! := by
    intro k hk hke hko
    have h_eq_e : (2 * (2#usize : Std.Usize).val : Nat) = 4 := by decide
    have h_eq_o : (2 * (2#usize : Std.Usize).val + 1 : Nat) = 5 := by decide
    apply h_r2_unc k hk
    · rw [h_eq_e]; exact hke
    · rw [h_eq_o]; exact hko
  have h_r2_bnd_universal : ∀ k : Fin 16, (r2.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r1 r2 2 (by decide) h_r1_bnd_universal
      h_r2_unc' h_r2_at_even h_r2_at_odd

  -- Call 3: pair 3 with nzeta1 (touches lanes 6, 7).
  obtain ⟨r3, h_r3_eq, h_r3_len, h_r3_unc, h_r3_bnd_e, h_r3_bnd_o,
          h_r3_fe_e, h_r3_fe_o⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_fc lhs rhs nzeta1 3#usize r2
        (by decide) h_r2_len h_lhs h_rhs h_nz1_bnd h_r2_bnd_universal)
  have h_src_at_even : r2.val[6]! = out.val[6]! := by
    rw [h_r2_unc' 6 (by decide) (by decide) (by decide)]
    rw [h_r1_unc' 6 (by decide) (by decide) (by decide)]
    rw [h_r0_unc' 6 (by decide) (by decide) (by decide)]
  have h_src_at_odd : r2.val[7]! = out.val[7]! := by
    rw [h_r2_unc' 7 (by decide) (by decide) (by decide)]
    rw [h_r1_unc' 7 (by decide) (by decide) (by decide)]
    rw [h_r0_unc' 7 (by decide) (by decide) (by decide)]
  have h_r3_at_even : (r3.val[6]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (3#usize : Std.Usize).val : Nat) = 6 := by decide
    have h_b := h_r3_bnd_e
    rw [h_eq] at h_b
    rw [h_src_at_even] at h_b
    have h_out_le := h_out_bnd ⟨6, by decide⟩
    simp only at h_out_le; omega
  have h_r3_at_odd : (r3.val[7]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (3#usize : Std.Usize).val + 1 : Nat) = 7 := by decide
    have h_b := h_r3_bnd_o
    rw [h_eq] at h_b
    rw [h_src_at_odd] at h_b
    have h_out_le := h_out_bnd ⟨7, by decide⟩
    simp only at h_out_le; omega
  have h_r3_unc' : ∀ k : Nat, k < 16 → k ≠ 6 → k ≠ 7 →
      r3.val[k]! = r2.val[k]! := by
    intro k hk hke hko
    have h_eq_e : (2 * (3#usize : Std.Usize).val : Nat) = 6 := by decide
    have h_eq_o : (2 * (3#usize : Std.Usize).val + 1 : Nat) = 7 := by decide
    apply h_r3_unc k hk
    · rw [h_eq_e]; exact hke
    · rw [h_eq_o]; exact hko
  have h_r3_bnd_universal : ∀ k : Fin 16, (r3.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r2 r3 3 (by decide) h_r2_bnd_universal
      h_r3_unc' h_r3_at_even h_r3_at_odd

  -- Call 4: pair 4 with zeta2 (touches lanes 8, 9).
  obtain ⟨r4, h_r4_eq, h_r4_len, h_r4_unc, h_r4_bnd_e, h_r4_bnd_o,
          h_r4_fe_e, h_r4_fe_o⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_fc lhs rhs zeta2 4#usize r3
        (by decide) h_r3_len h_lhs h_rhs h_zeta2 h_r3_bnd_universal)
  have h_src_at_even : r3.val[8]! = out.val[8]! := by
    rw [h_r3_unc' 8 (by decide) (by decide) (by decide)]
    rw [h_r2_unc' 8 (by decide) (by decide) (by decide)]
    rw [h_r1_unc' 8 (by decide) (by decide) (by decide)]
    rw [h_r0_unc' 8 (by decide) (by decide) (by decide)]
  have h_src_at_odd : r3.val[9]! = out.val[9]! := by
    rw [h_r3_unc' 9 (by decide) (by decide) (by decide)]
    rw [h_r2_unc' 9 (by decide) (by decide) (by decide)]
    rw [h_r1_unc' 9 (by decide) (by decide) (by decide)]
    rw [h_r0_unc' 9 (by decide) (by decide) (by decide)]
  have h_r4_at_even : (r4.val[8]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (4#usize : Std.Usize).val : Nat) = 8 := by decide
    have h_b := h_r4_bnd_e
    rw [h_eq] at h_b
    rw [h_src_at_even] at h_b
    have h_out_le := h_out_bnd ⟨8, by decide⟩
    simp only at h_out_le; omega
  have h_r4_at_odd : (r4.val[9]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (4#usize : Std.Usize).val + 1 : Nat) = 9 := by decide
    have h_b := h_r4_bnd_o
    rw [h_eq] at h_b
    rw [h_src_at_odd] at h_b
    have h_out_le := h_out_bnd ⟨9, by decide⟩
    simp only at h_out_le; omega
  have h_r4_unc' : ∀ k : Nat, k < 16 → k ≠ 8 → k ≠ 9 →
      r4.val[k]! = r3.val[k]! := by
    intro k hk hke hko
    have h_eq_e : (2 * (4#usize : Std.Usize).val : Nat) = 8 := by decide
    have h_eq_o : (2 * (4#usize : Std.Usize).val + 1 : Nat) = 9 := by decide
    apply h_r4_unc k hk
    · rw [h_eq_e]; exact hke
    · rw [h_eq_o]; exact hko
  have h_r4_bnd_universal : ∀ k : Fin 16, (r4.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r3 r4 4 (by decide) h_r3_bnd_universal
      h_r4_unc' h_r4_at_even h_r4_at_odd

  -- Call 5: pair 5 with nzeta2 (touches lanes 10, 11).
  obtain ⟨r5, h_r5_eq, h_r5_len, h_r5_unc, h_r5_bnd_e, h_r5_bnd_o,
          h_r5_fe_e, h_r5_fe_o⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_fc lhs rhs nzeta2 5#usize r4
        (by decide) h_r4_len h_lhs h_rhs h_nz2_bnd h_r4_bnd_universal)
  have h_src_at_even : r4.val[10]! = out.val[10]! := by
    rw [h_r4_unc' 10 (by decide) (by decide) (by decide)]
    rw [h_r3_unc' 10 (by decide) (by decide) (by decide)]
    rw [h_r2_unc' 10 (by decide) (by decide) (by decide)]
    rw [h_r1_unc' 10 (by decide) (by decide) (by decide)]
    rw [h_r0_unc' 10 (by decide) (by decide) (by decide)]
  have h_src_at_odd : r4.val[11]! = out.val[11]! := by
    rw [h_r4_unc' 11 (by decide) (by decide) (by decide)]
    rw [h_r3_unc' 11 (by decide) (by decide) (by decide)]
    rw [h_r2_unc' 11 (by decide) (by decide) (by decide)]
    rw [h_r1_unc' 11 (by decide) (by decide) (by decide)]
    rw [h_r0_unc' 11 (by decide) (by decide) (by decide)]
  have h_r5_at_even : (r5.val[10]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (5#usize : Std.Usize).val : Nat) = 10 := by decide
    have h_b := h_r5_bnd_e
    rw [h_eq] at h_b
    rw [h_src_at_even] at h_b
    have h_out_le := h_out_bnd ⟨10, by decide⟩
    simp only at h_out_le; omega
  have h_r5_at_odd : (r5.val[11]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (5#usize : Std.Usize).val + 1 : Nat) = 11 := by decide
    have h_b := h_r5_bnd_o
    rw [h_eq] at h_b
    rw [h_src_at_odd] at h_b
    have h_out_le := h_out_bnd ⟨11, by decide⟩
    simp only at h_out_le; omega
  have h_r5_unc' : ∀ k : Nat, k < 16 → k ≠ 10 → k ≠ 11 →
      r5.val[k]! = r4.val[k]! := by
    intro k hk hke hko
    have h_eq_e : (2 * (5#usize : Std.Usize).val : Nat) = 10 := by decide
    have h_eq_o : (2 * (5#usize : Std.Usize).val + 1 : Nat) = 11 := by decide
    apply h_r5_unc k hk
    · rw [h_eq_e]; exact hke
    · rw [h_eq_o]; exact hko
  have h_r5_bnd_universal : ∀ k : Fin 16, (r5.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r4 r5 5 (by decide) h_r4_bnd_universal
      h_r5_unc' h_r5_at_even h_r5_at_odd

  -- Call 6: pair 6 with zeta3 (touches lanes 12, 13).
  obtain ⟨r6, h_r6_eq, h_r6_len, h_r6_unc, h_r6_bnd_e, h_r6_bnd_o,
          h_r6_fe_e, h_r6_fe_o⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_fc lhs rhs zeta3 6#usize r5
        (by decide) h_r5_len h_lhs h_rhs h_zeta3 h_r5_bnd_universal)
  have h_src_at_even : r5.val[12]! = out.val[12]! := by
    rw [h_r5_unc' 12 (by decide) (by decide) (by decide)]
    rw [h_r4_unc' 12 (by decide) (by decide) (by decide)]
    rw [h_r3_unc' 12 (by decide) (by decide) (by decide)]
    rw [h_r2_unc' 12 (by decide) (by decide) (by decide)]
    rw [h_r1_unc' 12 (by decide) (by decide) (by decide)]
    rw [h_r0_unc' 12 (by decide) (by decide) (by decide)]
  have h_src_at_odd : r5.val[13]! = out.val[13]! := by
    rw [h_r5_unc' 13 (by decide) (by decide) (by decide)]
    rw [h_r4_unc' 13 (by decide) (by decide) (by decide)]
    rw [h_r3_unc' 13 (by decide) (by decide) (by decide)]
    rw [h_r2_unc' 13 (by decide) (by decide) (by decide)]
    rw [h_r1_unc' 13 (by decide) (by decide) (by decide)]
    rw [h_r0_unc' 13 (by decide) (by decide) (by decide)]
  have h_r6_at_even : (r6.val[12]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (6#usize : Std.Usize).val : Nat) = 12 := by decide
    have h_b := h_r6_bnd_e
    rw [h_eq] at h_b
    rw [h_src_at_even] at h_b
    have h_out_le := h_out_bnd ⟨12, by decide⟩
    simp only at h_out_le; omega
  have h_r6_at_odd : (r6.val[13]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (6#usize : Std.Usize).val + 1 : Nat) = 13 := by decide
    have h_b := h_r6_bnd_o
    rw [h_eq] at h_b
    rw [h_src_at_odd] at h_b
    have h_out_le := h_out_bnd ⟨13, by decide⟩
    simp only at h_out_le; omega
  have h_r6_unc' : ∀ k : Nat, k < 16 → k ≠ 12 → k ≠ 13 →
      r6.val[k]! = r5.val[k]! := by
    intro k hk hke hko
    have h_eq_e : (2 * (6#usize : Std.Usize).val : Nat) = 12 := by decide
    have h_eq_o : (2 * (6#usize : Std.Usize).val + 1 : Nat) = 13 := by decide
    apply h_r6_unc k hk
    · rw [h_eq_e]; exact hke
    · rw [h_eq_o]; exact hko
  have h_r6_bnd_universal : ∀ k : Fin 16, (r6.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r5 r6 6 (by decide) h_r5_bnd_universal
      h_r6_unc' h_r6_at_even h_r6_at_odd

  -- Call 7: pair 7 with nzeta3 (touches lanes 14, 15).
  obtain ⟨r7, h_r7_eq, h_r7_len, h_r7_unc, h_r7_bnd_e, h_r7_bnd_o,
          h_r7_fe_e, h_r7_fe_o⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_fc lhs rhs nzeta3 7#usize r6
        (by decide) h_r6_len h_lhs h_rhs h_nz3_bnd h_r6_bnd_universal)
  have h_src_at_even : r6.val[14]! = out.val[14]! := by
    rw [h_r6_unc' 14 (by decide) (by decide) (by decide)]
    rw [h_r5_unc' 14 (by decide) (by decide) (by decide)]
    rw [h_r4_unc' 14 (by decide) (by decide) (by decide)]
    rw [h_r3_unc' 14 (by decide) (by decide) (by decide)]
    rw [h_r2_unc' 14 (by decide) (by decide) (by decide)]
    rw [h_r1_unc' 14 (by decide) (by decide) (by decide)]
    rw [h_r0_unc' 14 (by decide) (by decide) (by decide)]
  have h_src_at_odd : r6.val[15]! = out.val[15]! := by
    rw [h_r6_unc' 15 (by decide) (by decide) (by decide)]
    rw [h_r5_unc' 15 (by decide) (by decide) (by decide)]
    rw [h_r4_unc' 15 (by decide) (by decide) (by decide)]
    rw [h_r3_unc' 15 (by decide) (by decide) (by decide)]
    rw [h_r2_unc' 15 (by decide) (by decide) (by decide)]
    rw [h_r1_unc' 15 (by decide) (by decide) (by decide)]
    rw [h_r0_unc' 15 (by decide) (by decide) (by decide)]
  have h_r7_at_even : (r7.val[14]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (7#usize : Std.Usize).val : Nat) = 14 := by decide
    have h_b := h_r7_bnd_e
    rw [h_eq] at h_b
    rw [h_src_at_even] at h_b
    have h_out_le := h_out_bnd ⟨14, by decide⟩
    simp only at h_out_le; omega
  have h_r7_at_odd : (r7.val[15]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (7#usize : Std.Usize).val + 1 : Nat) = 15 := by decide
    have h_b := h_r7_bnd_o
    rw [h_eq] at h_b
    rw [h_src_at_odd] at h_b
    have h_out_le := h_out_bnd ⟨15, by decide⟩
    simp only at h_out_le; omega
  have h_r7_unc' : ∀ k : Nat, k < 16 → k ≠ 14 → k ≠ 15 →
      r7.val[k]! = r6.val[k]! := by
    intro k hk hke hko
    have h_eq_e : (2 * (7#usize : Std.Usize).val : Nat) = 14 := by decide
    have h_eq_o : (2 * (7#usize : Std.Usize).val + 1 : Nat) = 15 := by decide
    apply h_r7_unc k hk
    · rw [h_eq_e]; exact hke
    · rw [h_eq_o]; exact hko
  have h_r7_bnd_universal : ∀ k : Fin 16, (r7.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r6 r7 7 (by decide) h_r6_bnd_universal
      h_r7_unc' h_r7_at_even h_r7_at_odd

  -- Compose the monadic body.
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply
        lhs rhs out zeta0 zeta1 zeta2 zeta3 = .ok r7 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply
    simp only [h_wn0, h_wn1, h_wn2, h_wn3,
               h_cz0, h_cnz0, h_cz1, h_cnz1, h_cz2, h_cnz2, h_cz3, h_cnz3,
               h_r0_eq, h_r1_eq, h_r2_eq, h_r3_eq,
               h_r4_eq, h_r5_eq, h_r6_eq, h_r7_eq,
               Aeneas.Std.bind_tc_ok]
  apply triple_of_ok_fc h_body
  -- POST: 3-conjunct.
  refine ⟨h_r7_len, ?_, ?_⟩
  · -- Relative bound: ∀ k, r7.val[k]!.natAbs ≤ out.val[k]!.natAbs + 2^25.
    -- Each lane is touched at most once → bound is +2^25 above out.
    -- Build via unc-chains + per-pair touched bounds.
    -- Strategy: 16-way case split.
    intro k
    rcases k with ⟨k, hk⟩
    -- Walk back to find which call (if any) touched this lane.
    interval_cases k
    -- Lane 0: touched by call 0 (i=0, even).
    · have h_r7_at_0 : r7.val[0]! = r0.val[0]! := by
        rw [h_r7_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 0 (by decide) (by decide) (by decide)]
      rw [h_r7_at_0]
      have h_eq : (2 * (0#usize : Std.Usize).val : Nat) = 0 := by decide
      have h_b := h_r0_bnd_e
      rw [h_eq] at h_b
      -- Source for call 0 is `out`, so h_src_at_even = rfl, no rewrite needed.
      exact h_b
    -- Lane 1: touched by call 0 (i=0, odd).
    · have h_r7_at_1 : r7.val[1]! = r0.val[1]! := by
        rw [h_r7_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 1 (by decide) (by decide) (by decide)]
      rw [h_r7_at_1]
      have h_eq : (2 * (0#usize : Std.Usize).val + 1 : Nat) = 1 := by decide
      have h_b := h_r0_bnd_o
      rw [h_eq] at h_b
      exact h_b
    -- Lane 2: touched by call 1 (i=1, even). Source for call 1 was r0, but r0.val[2]! = out.val[2]!.
    · have h_r7_at_2 : r7.val[2]! = r1.val[2]! := by
        rw [h_r7_unc' 2 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 2 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 2 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 2 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 2 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 2 (by decide) (by decide) (by decide)]
      rw [h_r7_at_2]
      have h_eq : (2 * (1#usize : Std.Usize).val : Nat) = 2 := by decide
      have h_b := h_r1_bnd_e
      rw [h_eq] at h_b
      -- h_b : r1.val[2]!.natAbs ≤ r0.val[2]!.natAbs + 2^25.
      -- Need: r1.val[2]!.natAbs ≤ out.val[2]!.natAbs + 2^25.
      -- r0.val[2]! = out.val[2]! (lane 2 fresh for call 0).
      have h_r0_at_2 : r0.val[2]! = out.val[2]! := by
        rw [h_r0_unc' 2 (by decide) (by decide) (by decide)]
      rw [h_r0_at_2] at h_b
      exact h_b
    -- Lane 3: touched by call 1 (i=1, odd).
    · have h_r7_at_3 : r7.val[3]! = r1.val[3]! := by
        rw [h_r7_unc' 3 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 3 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 3 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 3 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 3 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 3 (by decide) (by decide) (by decide)]
      rw [h_r7_at_3]
      have h_eq : (2 * (1#usize : Std.Usize).val + 1 : Nat) = 3 := by decide
      have h_b := h_r1_bnd_o
      rw [h_eq] at h_b
      have h_r0_at_3 : r0.val[3]! = out.val[3]! := by
        rw [h_r0_unc' 3 (by decide) (by decide) (by decide)]
      rw [h_r0_at_3] at h_b
      exact h_b
    -- Lane 4: touched by call 2 (i=2, even).
    · have h_r7_at_4 : r7.val[4]! = r2.val[4]! := by
        rw [h_r7_unc' 4 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 4 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 4 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 4 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 4 (by decide) (by decide) (by decide)]
      rw [h_r7_at_4]
      have h_eq : (2 * (2#usize : Std.Usize).val : Nat) = 4 := by decide
      have h_b := h_r2_bnd_e
      rw [h_eq] at h_b
      have h_r1_at_4 : r1.val[4]! = out.val[4]! := by
        rw [h_r1_unc' 4 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 4 (by decide) (by decide) (by decide)]
      rw [h_r1_at_4] at h_b
      exact h_b
    -- Lane 5: touched by call 2 (i=2, odd).
    · have h_r7_at_5 : r7.val[5]! = r2.val[5]! := by
        rw [h_r7_unc' 5 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 5 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 5 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 5 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 5 (by decide) (by decide) (by decide)]
      rw [h_r7_at_5]
      have h_eq : (2 * (2#usize : Std.Usize).val + 1 : Nat) = 5 := by decide
      have h_b := h_r2_bnd_o
      rw [h_eq] at h_b
      have h_r1_at_5 : r1.val[5]! = out.val[5]! := by
        rw [h_r1_unc' 5 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 5 (by decide) (by decide) (by decide)]
      rw [h_r1_at_5] at h_b
      exact h_b
    -- Lane 6: touched by call 3 (i=3, even).
    · have h_r7_at_6 : r7.val[6]! = r3.val[6]! := by
        rw [h_r7_unc' 6 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 6 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 6 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 6 (by decide) (by decide) (by decide)]
      rw [h_r7_at_6]
      have h_eq : (2 * (3#usize : Std.Usize).val : Nat) = 6 := by decide
      have h_b := h_r3_bnd_e
      rw [h_eq] at h_b
      have h_r2_at_6 : r2.val[6]! = out.val[6]! := by
        rw [h_r2_unc' 6 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 6 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 6 (by decide) (by decide) (by decide)]
      rw [h_r2_at_6] at h_b
      exact h_b
    -- Lane 7: touched by call 3 (i=3, odd).
    · have h_r7_at_7 : r7.val[7]! = r3.val[7]! := by
        rw [h_r7_unc' 7 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 7 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 7 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 7 (by decide) (by decide) (by decide)]
      rw [h_r7_at_7]
      have h_eq : (2 * (3#usize : Std.Usize).val + 1 : Nat) = 7 := by decide
      have h_b := h_r3_bnd_o
      rw [h_eq] at h_b
      have h_r2_at_7 : r2.val[7]! = out.val[7]! := by
        rw [h_r2_unc' 7 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 7 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 7 (by decide) (by decide) (by decide)]
      rw [h_r2_at_7] at h_b
      exact h_b
    -- Lane 8.
    · have h_r7_at_8 : r7.val[8]! = r4.val[8]! := by
        rw [h_r7_unc' 8 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 8 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 8 (by decide) (by decide) (by decide)]
      rw [h_r7_at_8]
      have h_eq : (2 * (4#usize : Std.Usize).val : Nat) = 8 := by decide
      have h_b := h_r4_bnd_e
      rw [h_eq] at h_b
      have h_r3_at_8 : r3.val[8]! = out.val[8]! := by
        rw [h_r3_unc' 8 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 8 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 8 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 8 (by decide) (by decide) (by decide)]
      rw [h_r3_at_8] at h_b
      exact h_b
    -- Lane 9.
    · have h_r7_at_9 : r7.val[9]! = r4.val[9]! := by
        rw [h_r7_unc' 9 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 9 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 9 (by decide) (by decide) (by decide)]
      rw [h_r7_at_9]
      have h_eq : (2 * (4#usize : Std.Usize).val + 1 : Nat) = 9 := by decide
      have h_b := h_r4_bnd_o
      rw [h_eq] at h_b
      have h_r3_at_9 : r3.val[9]! = out.val[9]! := by
        rw [h_r3_unc' 9 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 9 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 9 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 9 (by decide) (by decide) (by decide)]
      rw [h_r3_at_9] at h_b
      exact h_b
    -- Lane 10.
    · have h_r7_at_10 : r7.val[10]! = r5.val[10]! := by
        rw [h_r7_unc' 10 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 10 (by decide) (by decide) (by decide)]
      rw [h_r7_at_10]
      have h_eq : (2 * (5#usize : Std.Usize).val : Nat) = 10 := by decide
      have h_b := h_r5_bnd_e
      rw [h_eq] at h_b
      have h_r4_at_10 : r4.val[10]! = out.val[10]! := by
        rw [h_r4_unc' 10 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 10 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 10 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 10 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 10 (by decide) (by decide) (by decide)]
      rw [h_r4_at_10] at h_b
      exact h_b
    -- Lane 11.
    · have h_r7_at_11 : r7.val[11]! = r5.val[11]! := by
        rw [h_r7_unc' 11 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 11 (by decide) (by decide) (by decide)]
      rw [h_r7_at_11]
      have h_eq : (2 * (5#usize : Std.Usize).val + 1 : Nat) = 11 := by decide
      have h_b := h_r5_bnd_o
      rw [h_eq] at h_b
      have h_r4_at_11 : r4.val[11]! = out.val[11]! := by
        rw [h_r4_unc' 11 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 11 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 11 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 11 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 11 (by decide) (by decide) (by decide)]
      rw [h_r4_at_11] at h_b
      exact h_b
    -- Lane 12.
    · have h_r7_at_12 : r7.val[12]! = r6.val[12]! := by
        rw [h_r7_unc' 12 (by decide) (by decide) (by decide)]
      rw [h_r7_at_12]
      have h_eq : (2 * (6#usize : Std.Usize).val : Nat) = 12 := by decide
      have h_b := h_r6_bnd_e
      rw [h_eq] at h_b
      have h_r5_at_12 : r5.val[12]! = out.val[12]! := by
        rw [h_r5_unc' 12 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 12 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 12 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 12 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 12 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 12 (by decide) (by decide) (by decide)]
      rw [h_r5_at_12] at h_b
      exact h_b
    -- Lane 13.
    · have h_r7_at_13 : r7.val[13]! = r6.val[13]! := by
        rw [h_r7_unc' 13 (by decide) (by decide) (by decide)]
      rw [h_r7_at_13]
      have h_eq : (2 * (6#usize : Std.Usize).val + 1 : Nat) = 13 := by decide
      have h_b := h_r6_bnd_o
      rw [h_eq] at h_b
      have h_r5_at_13 : r5.val[13]! = out.val[13]! := by
        rw [h_r5_unc' 13 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 13 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 13 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 13 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 13 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 13 (by decide) (by decide) (by decide)]
      rw [h_r5_at_13] at h_b
      exact h_b
    -- Lane 14: touched by call 7 (i=7, even).
    · have h_eq : (2 * (7#usize : Std.Usize).val : Nat) = 14 := by decide
      have h_b := h_r7_bnd_e
      rw [h_eq] at h_b
      have h_r6_at_14 : r6.val[14]! = out.val[14]! := by
        rw [h_r6_unc' 14 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 14 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 14 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 14 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 14 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 14 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 14 (by decide) (by decide) (by decide)]
      rw [h_r6_at_14] at h_b
      exact h_b
    -- Lane 15.
    · have h_eq : (2 * (7#usize : Std.Usize).val + 1 : Nat) = 15 := by decide
      have h_b := h_r7_bnd_o
      rw [h_eq] at h_b
      have h_r6_at_15 : r6.val[15]! = out.val[15]! := by
        rw [h_r6_unc' 15 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 15 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 15 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 15 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 15 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 15 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 15 (by decide) (by decide) (by decide)]
      rw [h_r6_at_15] at h_b
      exact h_b
  · -- ntt_multiply_base_case_post: per-lane FE equation.
    unfold ntt_multiply_base_case_post ntt_multiply_base_case_alg
    apply Subtype.ext
    have h_lhs_val : (Spec.chunk_reducing_from_i32_array_pure r7).val
        = (List.range 16).map (fun i => Spec.mont_reduce_pure (lift_fe_int (r7.val[i]!).val)) := by
      unfold Spec.chunk_reducing_from_i32_array_pure; rfl
    have h_rhs_val : (Spec.chunk_add_pure
                        (Spec.chunk_reducing_from_i32_array_pure out)
                        (Spec.ntt_multiply_pure_no_acc
                          (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                          (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                          (lift_fe_mont zeta2) (lift_fe_mont zeta3))).val
        = (List.range 16).map (fun i =>
            libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              ((Spec.chunk_reducing_from_i32_array_pure out).val[i]!)
              ((Spec.ntt_multiply_pure_no_acc
                  (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                  (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                  (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[i]!)) := by
      unfold Spec.chunk_add_pure; rfl
    rw [h_lhs_val, h_rhs_val]
    apply List.ext_getElem
    · simp
    · intro k hk1 hk2
      have hk : k < 16 := by simp at hk1; exact hk1
      rw [List.getElem_map, List.getElem_map, List.getElem_range]
      interval_cases k
      · -- Lane 0: touched by call 0 (zeta0, even).
        have h_r7_at_lane : r7.val[0]! = r0.val[0]! := by
          rw [h_r7_unc' 0 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 0 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 0 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 0 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 0 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 0 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_fe := h_r0_fe_e
        simp only [
                   show (2 * (0#usize : Std.Usize).val : Nat) = 0 from by decide] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[0]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[0]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[0]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[0]!)
                  ((lift_chunk_mont rhs).val[0]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[1]!)
                    ((lift_chunk_mont rhs).val[1]!))
                  (lift_fe_mont zeta0)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_0 : (lift_chunk_mont lhs).val[0]!
            = lift_fe_mont (lhs.elements.val[0]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[0]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 0 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 0 (by rw [h_l]; decide)]
        have h_lcm_lhs_1 : (lift_chunk_mont lhs).val[1]!
            = lift_fe_mont (lhs.elements.val[1]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[1]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 1 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 1 (by rw [h_l]; decide)]
        have h_lcm_rhs_0 : (lift_chunk_mont rhs).val[0]!
            = lift_fe_mont (rhs.elements.val[0]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[0]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 0 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 0 (by rw [h_l]; decide)]
        have h_lcm_rhs_1 : (lift_chunk_mont rhs).val[1]!
            = lift_fe_mont (rhs.elements.val[1]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[1]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 1 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 1 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_0, h_lcm_lhs_1, h_lcm_rhs_0, h_lcm_rhs_1]
      · -- Lane 1: touched by call 0 (zeta0, odd).
        have h_r7_at_lane : r7.val[1]! = r0.val[1]! := by
          rw [h_r7_unc' 1 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 1 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 1 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 1 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 1 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 1 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_fe := h_r0_fe_o
        simp only [
                   show (2 * (0#usize : Std.Usize).val : Nat) = 0 from by decide] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[1]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[1]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[1]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[0]!)
                  ((lift_chunk_mont rhs).val[1]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[1]!)
                  ((lift_chunk_mont rhs).val[0]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_0 : (lift_chunk_mont lhs).val[0]!
            = lift_fe_mont (lhs.elements.val[0]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[0]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 0 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 0 (by rw [h_l]; decide)]
        have h_lcm_lhs_1 : (lift_chunk_mont lhs).val[1]!
            = lift_fe_mont (lhs.elements.val[1]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[1]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 1 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 1 (by rw [h_l]; decide)]
        have h_lcm_rhs_0 : (lift_chunk_mont rhs).val[0]!
            = lift_fe_mont (rhs.elements.val[0]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[0]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 0 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 0 (by rw [h_l]; decide)]
        have h_lcm_rhs_1 : (lift_chunk_mont rhs).val[1]!
            = lift_fe_mont (rhs.elements.val[1]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[1]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 1 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 1 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_0, h_lcm_lhs_1, h_lcm_rhs_0, h_lcm_rhs_1]
      · -- Lane 2: touched by call 1 (nzeta0, even).
        have h_r7_at_lane : r7.val[2]! = r1.val[2]! := by
          rw [h_r7_unc' 2 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 2 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 2 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 2 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 2 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 2 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r0.val[2]! = out.val[2]! := by
          rw [h_r0_unc' 2 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r0.val[3]! = out.val[3]! := by
          rw [h_r0_unc' 3 (by decide) (by decide) (by decide)]
        have h_fe := h_r1_fe_e
        simp only [
                   show (2 * (1#usize : Std.Usize).val : Nat) = 2 from by decide] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_n0_fe] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[2]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[2]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[2]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[2]!)
                  ((lift_chunk_mont rhs).val[2]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[3]!)
                    ((lift_chunk_mont rhs).val[3]!))
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta0))) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_2 : (lift_chunk_mont lhs).val[2]!
            = lift_fe_mont (lhs.elements.val[2]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[2]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 2 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 2 (by rw [h_l]; decide)]
        have h_lcm_lhs_3 : (lift_chunk_mont lhs).val[3]!
            = lift_fe_mont (lhs.elements.val[3]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[3]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 3 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 3 (by rw [h_l]; decide)]
        have h_lcm_rhs_2 : (lift_chunk_mont rhs).val[2]!
            = lift_fe_mont (rhs.elements.val[2]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[2]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 2 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 2 (by rw [h_l]; decide)]
        have h_lcm_rhs_3 : (lift_chunk_mont rhs).val[3]!
            = lift_fe_mont (rhs.elements.val[3]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[3]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 3 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 3 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_2, h_lcm_lhs_3, h_lcm_rhs_2, h_lcm_rhs_3]
      · -- Lane 3: touched by call 1 (nzeta0, odd).
        have h_r7_at_lane : r7.val[3]! = r1.val[3]! := by
          rw [h_r7_unc' 3 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 3 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 3 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 3 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 3 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 3 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r0.val[2]! = out.val[2]! := by
          rw [h_r0_unc' 2 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r0.val[3]! = out.val[3]! := by
          rw [h_r0_unc' 3 (by decide) (by decide) (by decide)]
        have h_fe := h_r1_fe_o
        simp only [
                   show (2 * (1#usize : Std.Usize).val : Nat) = 2 from by decide] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[3]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[3]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[3]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[2]!)
                  ((lift_chunk_mont rhs).val[3]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[3]!)
                  ((lift_chunk_mont rhs).val[2]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_2 : (lift_chunk_mont lhs).val[2]!
            = lift_fe_mont (lhs.elements.val[2]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[2]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 2 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 2 (by rw [h_l]; decide)]
        have h_lcm_lhs_3 : (lift_chunk_mont lhs).val[3]!
            = lift_fe_mont (lhs.elements.val[3]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[3]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 3 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 3 (by rw [h_l]; decide)]
        have h_lcm_rhs_2 : (lift_chunk_mont rhs).val[2]!
            = lift_fe_mont (rhs.elements.val[2]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[2]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 2 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 2 (by rw [h_l]; decide)]
        have h_lcm_rhs_3 : (lift_chunk_mont rhs).val[3]!
            = lift_fe_mont (rhs.elements.val[3]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[3]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 3 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 3 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_2, h_lcm_lhs_3, h_lcm_rhs_2, h_lcm_rhs_3]
      · -- Lane 4: touched by call 2 (zeta1, even).
        have h_r7_at_lane : r7.val[4]! = r2.val[4]! := by
          rw [h_r7_unc' 4 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 4 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 4 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 4 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 4 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r1.val[4]! = out.val[4]! := by
          rw [h_r1_unc' 4 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 4 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r1.val[5]! = out.val[5]! := by
          rw [h_r1_unc' 5 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 5 (by decide) (by decide) (by decide)]
        have h_fe := h_r2_fe_e
        simp only [
                   show (2 * (2#usize : Std.Usize).val : Nat) = 4 from by decide] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[4]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[4]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[4]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[4]!)
                  ((lift_chunk_mont rhs).val[4]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[5]!)
                    ((lift_chunk_mont rhs).val[5]!))
                  (lift_fe_mont zeta1)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_4 : (lift_chunk_mont lhs).val[4]!
            = lift_fe_mont (lhs.elements.val[4]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[4]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 4 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 4 (by rw [h_l]; decide)]
        have h_lcm_lhs_5 : (lift_chunk_mont lhs).val[5]!
            = lift_fe_mont (lhs.elements.val[5]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[5]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 5 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 5 (by rw [h_l]; decide)]
        have h_lcm_rhs_4 : (lift_chunk_mont rhs).val[4]!
            = lift_fe_mont (rhs.elements.val[4]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[4]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 4 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 4 (by rw [h_l]; decide)]
        have h_lcm_rhs_5 : (lift_chunk_mont rhs).val[5]!
            = lift_fe_mont (rhs.elements.val[5]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[5]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 5 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 5 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_4, h_lcm_lhs_5, h_lcm_rhs_4, h_lcm_rhs_5]
      · -- Lane 5: touched by call 2 (zeta1, odd).
        have h_r7_at_lane : r7.val[5]! = r2.val[5]! := by
          rw [h_r7_unc' 5 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 5 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 5 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 5 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 5 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r1.val[4]! = out.val[4]! := by
          rw [h_r1_unc' 4 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 4 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r1.val[5]! = out.val[5]! := by
          rw [h_r1_unc' 5 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 5 (by decide) (by decide) (by decide)]
        have h_fe := h_r2_fe_o
        simp only [
                   show (2 * (2#usize : Std.Usize).val : Nat) = 4 from by decide] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[5]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[5]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[5]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[4]!)
                  ((lift_chunk_mont rhs).val[5]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[5]!)
                  ((lift_chunk_mont rhs).val[4]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_4 : (lift_chunk_mont lhs).val[4]!
            = lift_fe_mont (lhs.elements.val[4]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[4]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 4 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 4 (by rw [h_l]; decide)]
        have h_lcm_lhs_5 : (lift_chunk_mont lhs).val[5]!
            = lift_fe_mont (lhs.elements.val[5]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[5]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 5 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 5 (by rw [h_l]; decide)]
        have h_lcm_rhs_4 : (lift_chunk_mont rhs).val[4]!
            = lift_fe_mont (rhs.elements.val[4]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[4]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 4 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 4 (by rw [h_l]; decide)]
        have h_lcm_rhs_5 : (lift_chunk_mont rhs).val[5]!
            = lift_fe_mont (rhs.elements.val[5]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[5]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 5 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 5 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_4, h_lcm_lhs_5, h_lcm_rhs_4, h_lcm_rhs_5]
      · -- Lane 6: touched by call 3 (nzeta1, even).
        have h_r7_at_lane : r7.val[6]! = r3.val[6]! := by
          rw [h_r7_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 6 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r2.val[6]! = out.val[6]! := by
          rw [h_r2_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 6 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r2.val[7]! = out.val[7]! := by
          rw [h_r2_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 7 (by decide) (by decide) (by decide)]
        have h_fe := h_r3_fe_e
        simp only [
                   show (2 * (3#usize : Std.Usize).val : Nat) = 6 from by decide] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_n1_fe] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[6]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[6]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[6]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[6]!)
                  ((lift_chunk_mont rhs).val[6]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[7]!)
                    ((lift_chunk_mont rhs).val[7]!))
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta1))) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_6 : (lift_chunk_mont lhs).val[6]!
            = lift_fe_mont (lhs.elements.val[6]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[6]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 6 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 6 (by rw [h_l]; decide)]
        have h_lcm_lhs_7 : (lift_chunk_mont lhs).val[7]!
            = lift_fe_mont (lhs.elements.val[7]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[7]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 7 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 7 (by rw [h_l]; decide)]
        have h_lcm_rhs_6 : (lift_chunk_mont rhs).val[6]!
            = lift_fe_mont (rhs.elements.val[6]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[6]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 6 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 6 (by rw [h_l]; decide)]
        have h_lcm_rhs_7 : (lift_chunk_mont rhs).val[7]!
            = lift_fe_mont (rhs.elements.val[7]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[7]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 7 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 7 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_6, h_lcm_lhs_7, h_lcm_rhs_6, h_lcm_rhs_7]
      · -- Lane 7: touched by call 3 (nzeta1, odd).
        have h_r7_at_lane : r7.val[7]! = r3.val[7]! := by
          rw [h_r7_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 7 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r2.val[6]! = out.val[6]! := by
          rw [h_r2_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 6 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r2.val[7]! = out.val[7]! := by
          rw [h_r2_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 7 (by decide) (by decide) (by decide)]
        have h_fe := h_r3_fe_o
        simp only [
                   show (2 * (3#usize : Std.Usize).val : Nat) = 6 from by decide] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[7]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[7]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[7]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[6]!)
                  ((lift_chunk_mont rhs).val[7]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[7]!)
                  ((lift_chunk_mont rhs).val[6]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_6 : (lift_chunk_mont lhs).val[6]!
            = lift_fe_mont (lhs.elements.val[6]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[6]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 6 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 6 (by rw [h_l]; decide)]
        have h_lcm_lhs_7 : (lift_chunk_mont lhs).val[7]!
            = lift_fe_mont (lhs.elements.val[7]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[7]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 7 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 7 (by rw [h_l]; decide)]
        have h_lcm_rhs_6 : (lift_chunk_mont rhs).val[6]!
            = lift_fe_mont (rhs.elements.val[6]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[6]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 6 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 6 (by rw [h_l]; decide)]
        have h_lcm_rhs_7 : (lift_chunk_mont rhs).val[7]!
            = lift_fe_mont (rhs.elements.val[7]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[7]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 7 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 7 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_6, h_lcm_lhs_7, h_lcm_rhs_6, h_lcm_rhs_7]
      · -- Lane 8: touched by call 4 (zeta2, even).
        have h_r7_at_lane : r7.val[8]! = r4.val[8]! := by
          rw [h_r7_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 8 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r3.val[8]! = out.val[8]! := by
          rw [h_r3_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 8 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r3.val[9]! = out.val[9]! := by
          rw [h_r3_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 9 (by decide) (by decide) (by decide)]
        have h_fe := h_r4_fe_e
        simp only [
                   show (2 * (4#usize : Std.Usize).val : Nat) = 8 from by decide] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[8]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[8]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[8]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[8]!)
                  ((lift_chunk_mont rhs).val[8]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[9]!)
                    ((lift_chunk_mont rhs).val[9]!))
                  (lift_fe_mont zeta2)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_8 : (lift_chunk_mont lhs).val[8]!
            = lift_fe_mont (lhs.elements.val[8]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[8]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 8 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 8 (by rw [h_l]; decide)]
        have h_lcm_lhs_9 : (lift_chunk_mont lhs).val[9]!
            = lift_fe_mont (lhs.elements.val[9]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[9]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 9 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 9 (by rw [h_l]; decide)]
        have h_lcm_rhs_8 : (lift_chunk_mont rhs).val[8]!
            = lift_fe_mont (rhs.elements.val[8]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[8]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 8 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 8 (by rw [h_l]; decide)]
        have h_lcm_rhs_9 : (lift_chunk_mont rhs).val[9]!
            = lift_fe_mont (rhs.elements.val[9]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[9]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 9 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 9 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_8, h_lcm_lhs_9, h_lcm_rhs_8, h_lcm_rhs_9]
      · -- Lane 9: touched by call 4 (zeta2, odd).
        have h_r7_at_lane : r7.val[9]! = r4.val[9]! := by
          rw [h_r7_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 9 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r3.val[8]! = out.val[8]! := by
          rw [h_r3_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 8 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r3.val[9]! = out.val[9]! := by
          rw [h_r3_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 9 (by decide) (by decide) (by decide)]
        have h_fe := h_r4_fe_o
        simp only [
                   show (2 * (4#usize : Std.Usize).val : Nat) = 8 from by decide] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[9]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[9]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[9]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[8]!)
                  ((lift_chunk_mont rhs).val[9]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[9]!)
                  ((lift_chunk_mont rhs).val[8]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_8 : (lift_chunk_mont lhs).val[8]!
            = lift_fe_mont (lhs.elements.val[8]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[8]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 8 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 8 (by rw [h_l]; decide)]
        have h_lcm_lhs_9 : (lift_chunk_mont lhs).val[9]!
            = lift_fe_mont (lhs.elements.val[9]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[9]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 9 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 9 (by rw [h_l]; decide)]
        have h_lcm_rhs_8 : (lift_chunk_mont rhs).val[8]!
            = lift_fe_mont (rhs.elements.val[8]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[8]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 8 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 8 (by rw [h_l]; decide)]
        have h_lcm_rhs_9 : (lift_chunk_mont rhs).val[9]!
            = lift_fe_mont (rhs.elements.val[9]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[9]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 9 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 9 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_8, h_lcm_lhs_9, h_lcm_rhs_8, h_lcm_rhs_9]
      · -- Lane 10: touched by call 5 (nzeta2, even).
        have h_r7_at_lane : r7.val[10]! = r5.val[10]! := by
          rw [h_r7_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 10 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r4.val[10]! = out.val[10]! := by
          rw [h_r4_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 10 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r4.val[11]! = out.val[11]! := by
          rw [h_r4_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 11 (by decide) (by decide) (by decide)]
        have h_fe := h_r5_fe_e
        simp only [
                   show (2 * (5#usize : Std.Usize).val : Nat) = 10 from by decide] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_n2_fe] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[10]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[10]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[10]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[10]!)
                  ((lift_chunk_mont rhs).val[10]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[11]!)
                    ((lift_chunk_mont rhs).val[11]!))
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta2))) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_10 : (lift_chunk_mont lhs).val[10]!
            = lift_fe_mont (lhs.elements.val[10]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[10]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 10 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 10 (by rw [h_l]; decide)]
        have h_lcm_lhs_11 : (lift_chunk_mont lhs).val[11]!
            = lift_fe_mont (lhs.elements.val[11]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[11]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 11 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 11 (by rw [h_l]; decide)]
        have h_lcm_rhs_10 : (lift_chunk_mont rhs).val[10]!
            = lift_fe_mont (rhs.elements.val[10]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[10]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 10 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 10 (by rw [h_l]; decide)]
        have h_lcm_rhs_11 : (lift_chunk_mont rhs).val[11]!
            = lift_fe_mont (rhs.elements.val[11]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[11]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 11 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 11 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_10, h_lcm_lhs_11, h_lcm_rhs_10, h_lcm_rhs_11]
      · -- Lane 11: touched by call 5 (nzeta2, odd).
        have h_r7_at_lane : r7.val[11]! = r5.val[11]! := by
          rw [h_r7_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 11 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r4.val[10]! = out.val[10]! := by
          rw [h_r4_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 10 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r4.val[11]! = out.val[11]! := by
          rw [h_r4_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 11 (by decide) (by decide) (by decide)]
        have h_fe := h_r5_fe_o
        simp only [
                   show (2 * (5#usize : Std.Usize).val : Nat) = 10 from by decide] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[11]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[11]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[11]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[10]!)
                  ((lift_chunk_mont rhs).val[11]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[11]!)
                  ((lift_chunk_mont rhs).val[10]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_10 : (lift_chunk_mont lhs).val[10]!
            = lift_fe_mont (lhs.elements.val[10]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[10]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 10 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 10 (by rw [h_l]; decide)]
        have h_lcm_lhs_11 : (lift_chunk_mont lhs).val[11]!
            = lift_fe_mont (lhs.elements.val[11]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[11]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 11 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 11 (by rw [h_l]; decide)]
        have h_lcm_rhs_10 : (lift_chunk_mont rhs).val[10]!
            = lift_fe_mont (rhs.elements.val[10]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[10]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 10 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 10 (by rw [h_l]; decide)]
        have h_lcm_rhs_11 : (lift_chunk_mont rhs).val[11]!
            = lift_fe_mont (rhs.elements.val[11]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[11]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 11 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 11 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_10, h_lcm_lhs_11, h_lcm_rhs_10, h_lcm_rhs_11]
      · -- Lane 12: touched by call 6 (zeta3, even).
        have h_r7_at_lane : r7.val[12]! = r6.val[12]! := by
          rw [h_r7_unc' 12 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r5.val[12]! = out.val[12]! := by
          rw [h_r5_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 12 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r5.val[13]! = out.val[13]! := by
          rw [h_r5_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 13 (by decide) (by decide) (by decide)]
        have h_fe := h_r6_fe_e
        simp only [
                   show (2 * (6#usize : Std.Usize).val : Nat) = 12 from by decide] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[12]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[12]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[12]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[12]!)
                  ((lift_chunk_mont rhs).val[12]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[13]!)
                    ((lift_chunk_mont rhs).val[13]!))
                  (lift_fe_mont zeta3)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_12 : (lift_chunk_mont lhs).val[12]!
            = lift_fe_mont (lhs.elements.val[12]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[12]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 12 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 12 (by rw [h_l]; decide)]
        have h_lcm_lhs_13 : (lift_chunk_mont lhs).val[13]!
            = lift_fe_mont (lhs.elements.val[13]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[13]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 13 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 13 (by rw [h_l]; decide)]
        have h_lcm_rhs_12 : (lift_chunk_mont rhs).val[12]!
            = lift_fe_mont (rhs.elements.val[12]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[12]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 12 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 12 (by rw [h_l]; decide)]
        have h_lcm_rhs_13 : (lift_chunk_mont rhs).val[13]!
            = lift_fe_mont (rhs.elements.val[13]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[13]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 13 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 13 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_12, h_lcm_lhs_13, h_lcm_rhs_12, h_lcm_rhs_13]
      · -- Lane 13: touched by call 6 (zeta3, odd).
        have h_r7_at_lane : r7.val[13]! = r6.val[13]! := by
          rw [h_r7_unc' 13 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r5.val[12]! = out.val[12]! := by
          rw [h_r5_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 12 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r5.val[13]! = out.val[13]! := by
          rw [h_r5_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 13 (by decide) (by decide) (by decide)]
        have h_fe := h_r6_fe_o
        simp only [
                   show (2 * (6#usize : Std.Usize).val : Nat) = 12 from by decide] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[13]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[13]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[13]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[12]!)
                  ((lift_chunk_mont rhs).val[13]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[13]!)
                  ((lift_chunk_mont rhs).val[12]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_12 : (lift_chunk_mont lhs).val[12]!
            = lift_fe_mont (lhs.elements.val[12]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[12]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 12 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 12 (by rw [h_l]; decide)]
        have h_lcm_lhs_13 : (lift_chunk_mont lhs).val[13]!
            = lift_fe_mont (lhs.elements.val[13]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[13]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 13 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 13 (by rw [h_l]; decide)]
        have h_lcm_rhs_12 : (lift_chunk_mont rhs).val[12]!
            = lift_fe_mont (rhs.elements.val[12]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[12]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 12 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 12 (by rw [h_l]; decide)]
        have h_lcm_rhs_13 : (lift_chunk_mont rhs).val[13]!
            = lift_fe_mont (rhs.elements.val[13]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[13]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 13 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 13 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_12, h_lcm_lhs_13, h_lcm_rhs_12, h_lcm_rhs_13]
      · -- Lane 14: touched by call 7 (nzeta3, even).
        have h_src_at_even : r6.val[14]! = out.val[14]! := by
          rw [h_r6_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 14 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r6.val[15]! = out.val[15]! := by
          rw [h_r6_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 15 (by decide) (by decide) (by decide)]
        have h_fe := h_r7_fe_e
        simp only [
                   show (2 * (7#usize : Std.Usize).val : Nat) = 14 from by decide] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_n3_fe] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[14]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[14]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[14]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[14]!)
                  ((lift_chunk_mont rhs).val[14]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[15]!)
                    ((lift_chunk_mont rhs).val[15]!))
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta3))) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_14 : (lift_chunk_mont lhs).val[14]!
            = lift_fe_mont (lhs.elements.val[14]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[14]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 14 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 14 (by rw [h_l]; decide)]
        have h_lcm_lhs_15 : (lift_chunk_mont lhs).val[15]!
            = lift_fe_mont (lhs.elements.val[15]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[15]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 15 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 15 (by rw [h_l]; decide)]
        have h_lcm_rhs_14 : (lift_chunk_mont rhs).val[14]!
            = lift_fe_mont (rhs.elements.val[14]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[14]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 14 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 14 (by rw [h_l]; decide)]
        have h_lcm_rhs_15 : (lift_chunk_mont rhs).val[15]!
            = lift_fe_mont (rhs.elements.val[15]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[15]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 15 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 15 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_14, h_lcm_lhs_15, h_lcm_rhs_14, h_lcm_rhs_15]
      · -- Lane 15: touched by call 7 (nzeta3, odd).
        have h_src_at_even : r6.val[14]! = out.val[14]! := by
          rw [h_r6_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 14 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r6.val[15]! = out.val[15]! := by
          rw [h_r6_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 15 (by decide) (by decide) (by decide)]
        have h_fe := h_r7_fe_o
        simp only [
                   show (2 * (7#usize : Std.Usize).val : Nat) = 14 from by decide] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[15]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[15]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[15]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[14]!)
                  ((lift_chunk_mont rhs).val[15]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[15]!)
                  ((lift_chunk_mont rhs).val[14]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_14 : (lift_chunk_mont lhs).val[14]!
            = lift_fe_mont (lhs.elements.val[14]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[14]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 14 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 14 (by rw [h_l]; decide)]
        have h_lcm_lhs_15 : (lift_chunk_mont lhs).val[15]!
            = lift_fe_mont (lhs.elements.val[15]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[15]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 15 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 15 (by rw [h_l]; decide)]
        have h_lcm_rhs_14 : (lift_chunk_mont rhs).val[14]!
            = lift_fe_mont (rhs.elements.val[14]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[14]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 14 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 14 (by rw [h_l]; decide)]
        have h_lcm_rhs_15 : (lift_chunk_mont rhs).val[15]!
            = lift_fe_mont (rhs.elements.val[15]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[15]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 15 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 15 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_14, h_lcm_lhs_15, h_lcm_rhs_14, h_lcm_rhs_15]


/-! ## §L2.8d — Cache-variant Triple statements (fill_cache + use_cache).

    The impl provides two siblings of `accumulating_ntt_multiply` that
    factor out the per-pair Mont-reduced `b·zeta` products into a
    16-lane cache vector:
      • `_fill_cache`: behaves identically to `accumulating_ntt_multiply`
        on the accumulator slice AND writes `mont_reduce(b[2i+1]·zeta_i)`
        into `cache[i]` for each pair i ∈ Fin 8 (cache slots 8..15
        untouched).
      • `_use_cache`: skips the per-pair Mont reduction by reading the
        cached I16 directly. Requires a cache pre-condition asserting
        each cache slot equals the Mont-reduced `b·zeta` product for
        the corresponding effective zeta.

    Composition pattern (matrix-row reuse): `_fill_cache(A, B, _, _, zetas)`
    sets the cache, then multiple `_use_cache(A', B, _, cache)` calls reuse
    it with different first operands and the same `B`/zeta structure. -/

/-- Effective per-pair zeta for the 8 binomial calls in a chunk: pair
    `2j` uses `zetaJ`, pair `2j+1` uses `neg_pure zetaJ` (the bit-side
    `wrapping_neg` projected through `lift_fe_mont`). Used to express
    the cache POST predicate at the FE-projection level. -/
noncomputable def Spec.effective_zeta_fe
    (i : Fin 8)
    (z0 z1 z2 z3 : hacspec_ml_kem.parameters.FieldElement) :
    hacspec_ml_kem.parameters.FieldElement :=
  if i.val = 0 then z0
  else if i.val = 1 then libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure z0
  else if i.val = 2 then z1
  else if i.val = 3 then libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure z1
  else if i.val = 4 then z2
  else if i.val = 5 then libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure z2
  else if i.val = 6 then z3
  else libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure z3

/-- Cache POST predicate shared between `_fill_cache` (as output cache
    POST) and `_use_cache` (as input cache PRE). For each pair `i ∈ Fin 8`:
      • `cache[i]` is canonical (`natAbs ≤ 3328`) — Mont reduction always
        produces values in this range; and
      • `lift_fe_mont cache[i] = mul_pure (lift_fe_mont rhs[2i+1])
                                          (effective_zeta_fe i z0 z1 z2 z3)`
        — i.e., the cache slot at pair `i` represents the FE product
        of `rhs`'s odd-lane operand and the pair's effective zeta. -/
noncomputable def Spec.ntt_multiply_cache_post
    (rhs : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta0 zeta1 zeta2 zeta3 : Std.I16)
    (cache : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Prop :=
  ∀ i : Fin 8,
    (cache.elements.val[i.val]!).val.natAbs ≤ 3328
    ∧ lift_fe_mont (cache.elements.val[i.val]!)
        = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (lift_fe_mont (rhs.elements.val[2 * i.val + 1]!))
            (Spec.effective_zeta_fe i
              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
              (lift_fe_mont zeta2) (lift_fe_mont zeta3))

/-! ### L2.8d — helper lemmas (sibling-adapt of L2.8c).

    Three new helpers extend the L2_8c.* infrastructure for the
    cache-variant Triples:
      • `L2_8d.lift_fe_mont_of_mont_reduce_modq` — translates the modq
        relation from `montgomery_reduce_element_spec` (`r * 2^16 ≡ x * y`)
        to a `lift_fe_mont r = mul_pure (lift_fe_mont x) (lift_fe_mont y)`
        equation (the fill-cache POST cache equation).
      • `L2_8d.mont_reduce_even_fe_eq_cache` and
        `L2_8d.mont_reduce_odd_fe_eq_cache` — Mont-domain FE equation
        builders for the use_cache per-pair Triple. Differ from
        `L2_8c.mont_reduce_{even,odd}_fe_eq` by carrying a symbolic
        cache-lane I16 in the RHS instead of an explicit `bj * zeta`
        product. -/

/-- Mont-reduced product → FE-projection bridge. If `r` is the
    Montgomery reduction of `x.val * y.val` (so `r.val * 2^16 ≡
    x.val * y.val (mod q)`), then `lift_fe_mont r = mul_pure
    (lift_fe_mont x) (lift_fe_mont y)`. Used by `_fill_cache` per-pair
    Triple to discharge the cache POST equation. -/
theorem L2_8d.lift_fe_mont_of_mont_reduce_modq
    (r x y : Std.I16)
    (h_canon : r.val.natAbs ≤ 3328)
    (h_zmod : ((r.val : Int) : ZMod 3329) * (2^16 : Int)
                = ((x.val : Int) : ZMod 3329) * ((y.val : Int) : ZMod 3329)) :
    lift_fe_mont r
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont x) (lift_fe_mont y) := by
  -- LHS: feOfZMod ((r.val : ZMod q) * 169).
  -- Set up s := mul_pure (lift_fe_mont x) (lift_fe_mont y); s is canonical, so
  -- the goal collapses (after round-trip) to a ZMod q equation.
  set s : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
      (lift_fe_mont x) (lift_fe_mont y) with hs_def
  -- Express s.val.val < 3329 via Canonical_mul_pure.
  have h_canon_s : s.val.val < 3329 := by
    have h_cm := libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure
      (lift_fe_mont x) (lift_fe_mont y)
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at h_cm
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cm
    exact h_cm
  have h_round_trip : feOfZMod (zmodOfFE s) = s :=
    feOfZMod_zmodOfFE_of_canonical s h_canon_s
  -- zmodOfFE s = (x.val : ZMod q) * 169 * ((y.val : ZMod q) * 169).
  have h_zmod_s : zmodOfFE s
      = ((x.val : Int) : ZMod 3329) * 169 * (((y.val : Int) : ZMod 3329) * 169) := by
    rw [hs_def, L2_8c.zmodOfFE_mul_pure, L2_8c.zmodOfFE_lift_fe_mont,
        L2_8c.zmodOfFE_lift_fe_mont]
  -- Now reduce LHS to feOfZMod ((r.val : ZMod q) * 169).
  have h_lhs : lift_fe_mont r = feOfZMod (((r.val : Int) : ZMod 3329) * 169) := by
    unfold lift_fe_mont i16_to_spec_fe_mont; rfl
  rw [h_lhs, ← h_round_trip, h_zmod_s]
  congr 1
  -- Goal: (r.val : Int : ZMod q) * 169 = (x.val : ZMod q) * 169 * (y.val : ZMod q) * 169.
  -- From h_zmod: r * 2^16 = x * y in ZMod q.
  -- Multiply by 169² on both sides: r * (2^16 * 169) * 169 = x * y * 169 * 169.
  -- 2^16 * 169 ≡ 1 (since 2^16 ≡ 2285 and 2285 * 169 = 1 in ZMod q).
  have h_inv : ((2285 : ZMod 3329)) * 169 = 1 := by decide
  have h_2_16 : ((2^16 : Int) : ZMod 3329) = 2285 := by decide
  -- Multiply h_zmod by 169 on both sides.
  have h_mul_169 :
      ((r.val : Int) : ZMod 3329) * (2^16 : Int) * 169
        = ((x.val : Int) : ZMod 3329) * ((y.val : Int) : ZMod 3329) * 169 := by
    rw [h_zmod]
  rw [h_2_16] at h_mul_169
  -- LHS rewrite: r * 169 = r * 2285 * 169 * 169 (since 2285 * 169 = 1).
  have h_lhs :
      ((r.val : Int) : ZMod 3329) * 169
        = ((r.val : Int) : ZMod 3329) * 2285 * 169 * 169 := by
    have : ((r.val : Int) : ZMod 3329) * 169 = ((r.val : Int) : ZMod 3329) * (2285 * 169) * 169 := by
      rw [h_inv]; ring
    rw [this]; ring
  rw [h_lhs]
  -- Now: r * 2285 * 169 * 169 = (x * y) * 169 * 169 from h_mul_169 (multiplied by 169 again).
  have h_mul_169_squared :
      ((r.val : Int) : ZMod 3329) * 2285 * 169 * 169
        = ((x.val : Int) : ZMod 3329) * ((y.val : Int) : ZMod 3329) * 169 * 169 := by
    have step : ((r.val : Int) : ZMod 3329) * 2285 * 169 * 169
              = (((r.val : Int) : ZMod 3329) * 2285 * 169) * 169 := by ring
    rw [step, h_mul_169]
  rw [h_mul_169_squared]
  ring

/-- Associativity of `Spec.Pure.FieldElement.mul_pure` (Mont-domain product
    in ZMod q). Used to reshape use_cache per-pair FE equations from
    `mul a (mul b c)` form (cache lane = mul rhs zeta) to `mul (mul a b) c`
    form to match the L2.8c per-pair FE shape. -/
theorem L2_8d.mul_pure_assoc
    (a b c : hacspec_ml_kem.parameters.FieldElement) :
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure a
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure b c)
    = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure a b) c := by
  -- Both sides are canonical; use round-trip + ZMod commutativity.
  set lhs : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure a
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure b c) with hlhs
  set rhs : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure a b) c with hrhs
  have h_canon_lhs : lhs.val.val < 3329 := by
    have h_cm := libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure a
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure b c)
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at h_cm
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cm; exact h_cm
  have h_canon_rhs : rhs.val.val < 3329 := by
    have h_cm := libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure a b) c
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at h_cm
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cm; exact h_cm
  have h_rt_lhs : feOfZMod (zmodOfFE lhs) = lhs :=
    feOfZMod_zmodOfFE_of_canonical lhs h_canon_lhs
  have h_rt_rhs : feOfZMod (zmodOfFE rhs) = rhs :=
    feOfZMod_zmodOfFE_of_canonical rhs h_canon_rhs
  have h_zmod_eq : zmodOfFE lhs = zmodOfFE rhs := by
    rw [hlhs, hrhs]
    rw [L2_8c.zmodOfFE_mul_pure, L2_8c.zmodOfFE_mul_pure,
        L2_8c.zmodOfFE_mul_pure, L2_8c.zmodOfFE_mul_pure]
    ring
  rw [← h_rt_lhs, ← h_rt_rhs, h_zmod_eq]

set_option maxHeartbeats 400000 in
/-- Use-cache variant of `L2_8c.mont_reduce_even_fe_eq`: the per-pair
    cache lane appears symbolically (as an I16 `c`) in the RHS via
    `lift_fe_mont c`, in place of the `bj * zeta` product. Same Mont-
    inversion algebra (`2285 * 169 ≡ 1 (mod q)`). -/
theorem L2_8d.mont_reduce_even_fe_eq_cache
    (out r : Std.I32) (ai bi aj c : Std.I16)
    (h_zmod : ((r.val * (2 ^ 16 : Int)) : ZMod 3329)
      = ((out.val * (2 ^ 16 : Int) + ai.val * bi.val * (2 ^ 16 : Int)
            + aj.val * c.val * (2 ^ 16 : Int)) : ZMod 3329)) :
    Spec.mont_reduce_pure (lift_fe_int r.val)
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          (Spec.mont_reduce_pure (lift_fe_int out.val))
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (lift_fe_mont ai) (lift_fe_mont bi))
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (lift_fe_mont aj) (lift_fe_mont c))) := by
  rw [mont_reduce_pure_lift_fe_int]
  set s : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
      (Spec.mont_reduce_pure (lift_fe_int out.val))
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont ai) (lift_fe_mont bi))
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont aj) (lift_fe_mont c))) with hs_def
  have h_canon : s.val.val < 3329 := by
    have h_cs := libcrux_iot_ml_kem.Spec.Pure.Canonical_add_pure
      (Spec.mont_reduce_pure (lift_fe_int out.val))
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont ai) (lift_fe_mont bi))
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont aj) (lift_fe_mont c)))
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at h_cs
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cs
    exact h_cs
  have h_round_trip : feOfZMod (zmodOfFE s) = s :=
    feOfZMod_zmodOfFE_of_canonical s h_canon
  have h_zmod_s : zmodOfFE s
      = (out.val : ZMod 3329) * 169 * 169
        + ((ai.val : ZMod 3329) * 169 * ((bi.val : ZMod 3329) * 169)
          + (aj.val : ZMod 3329) * 169 * ((c.val : ZMod 3329) * 169)) := by
    simp only [hs_def,
      L2_8c.zmodOfFE_add_pure,
      L2_8c.zmodOfFE_mont_reduce_lift_fe_int,
      L2_8c.zmodOfFE_mul_pure,
      L2_8c.zmodOfFE_lift_fe_mont]
  rw [← h_round_trip, h_zmod_s]
  congr 1
  have h_inv : ((2285 : ZMod 3329)) * 169 = 1 := by decide
  have h_mul_169_cubed :
      (r.val : ZMod 3329) * (2^16 : Int) * 169 * 169 * 169
        = ((out.val : ZMod 3329) * (2^16 : Int)
            + (ai.val : ZMod 3329) * (bi.val : ZMod 3329) * (2^16 : Int)
            + (aj.val : ZMod 3329) * (c.val : ZMod 3329) * (2^16 : Int)) * 169 * 169 * 169 := by
    have := h_zmod
    push_cast at this ⊢
    rw [this]
  have h_2_16 : ((2^16 : Int) : ZMod 3329) = 2285 := by decide
  rw [h_2_16] at h_mul_169_cubed
  have h_lhs :
      (r.val : ZMod 3329) * 169 * 169
        = (r.val : ZMod 3329) * 2285 * 169 * 169 * 169 := by
    have : (r.val : ZMod 3329) * 169 * 169 = (r.val : ZMod 3329) * (2285 * 169) * 169 * 169 := by
      rw [h_inv]; ring
    rw [this]; ring
  rw [h_lhs, h_mul_169_cubed]
  have h_expand : ((out.val : ZMod 3329) * 2285
            + (ai.val : ZMod 3329) * (bi.val : ZMod 3329) * 2285
            + (aj.val : ZMod 3329) * (c.val : ZMod 3329) * 2285)
          * 169 * 169 * 169
        = (out.val : ZMod 3329) * (2285 * (169 * 169 * 169))
          + (ai.val : ZMod 3329) * (bi.val : ZMod 3329) * (2285 * (169 * 169 * 169))
          + (aj.val : ZMod 3329) * (c.val : ZMod 3329) * (2285 * (169 * 169 * 169)) := by
    ring
  have h_collapse : ((2285 : ZMod 3329)) * (169 * 169 * 169) = 169 * 169 := by decide
  rw [h_expand, h_collapse]
  ring

set_option maxHeartbeats 400000 in
/-- Odd-half analog of `L2_8d.mont_reduce_even_fe_eq_cache`. -/
theorem L2_8d.mont_reduce_odd_fe_eq_cache
    (out r : Std.I32) (ai bi aj bj : Std.I16)
    (h_zmod : ((r.val * (2 ^ 16 : Int)) : ZMod 3329)
      = ((out.val * (2 ^ 16 : Int)
            + ai.val * bj.val * (2 ^ 16 : Int)
            + aj.val * bi.val * (2 ^ 16 : Int)) : ZMod 3329)) :
    Spec.mont_reduce_pure (lift_fe_int r.val)
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          (Spec.mont_reduce_pure (lift_fe_int out.val))
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (lift_fe_mont ai) (lift_fe_mont bj))
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (lift_fe_mont aj) (lift_fe_mont bi))) :=
  -- The odd-half equation has no cache lane (the cached
  -- `mont_reduce(b·zeta)` only enters the even-half product); it is
  -- identical to `L2_8c.mont_reduce_odd_fe_eq`.
  L2_8c.mont_reduce_odd_fe_eq out r ai bi aj bj h_zmod

set_option maxHeartbeats 8000000 in
/-- Per-pair Triple for `accumulating_ntt_multiply_binomials_fill_cache`.
    Sibling of `accumulating_ntt_multiply_binomials_fc`: same 7 POST
    conjuncts on the slice output, plus 3 POST conjuncts on the cache
    output describing the per-pair Mont-reduced `b[2i+1]·zeta` write
    at slot `i`. -/
theorem accumulating_ntt_multiply_binomials_fill_cache_fc
    (a b : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta : Std.I16) (i : Std.Usize)
    (out : Aeneas.Std.Slice Std.I32)
    (cache : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_i : i.val < 8)
    (h_out_len : out.length = 16)
    (h_a : ∀ j : Fin 16, (a.elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_b : ∀ j : Fin 16, (b.elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_zeta : zeta.val.natAbs ≤ 1664)
    (h_out_bnd : ∀ k : Fin 16, (out.val[k.val]!).val.natAbs ≤ 2^30 + 2^25) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
      a b zeta i out cache
    ⦃ ⇓ p => ⌜ p.1.length = 16
                ∧ (∀ k : Nat, k < 16 → k ≠ 2 * i.val → k ≠ 2 * i.val + 1 →
                    p.1.val[k]! = out.val[k]!)
                ∧ (p.1.val[2 * i.val]!).val.natAbs
                    ≤ (out.val[2 * i.val]!).val.natAbs + 2^25
                ∧ (p.1.val[2 * i.val + 1]!).val.natAbs
                    ≤ (out.val[2 * i.val + 1]!).val.natAbs + 2^25
                ∧ Spec.mont_reduce_pure (lift_fe_int (p.1.val[2 * i.val]!).val)
                    = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                        (Spec.mont_reduce_pure (lift_fe_int (out.val[2 * i.val]!).val))
                        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                            (lift_fe_mont (a.elements.val[2 * i.val]!))
                            (lift_fe_mont (b.elements.val[2 * i.val]!)))
                          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                              (lift_fe_mont (a.elements.val[2 * i.val + 1]!))
                              (lift_fe_mont (b.elements.val[2 * i.val + 1]!)))
                            (lift_fe_mont zeta)))
                ∧ Spec.mont_reduce_pure (lift_fe_int (p.1.val[2 * i.val + 1]!).val)
                    = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                        (Spec.mont_reduce_pure (lift_fe_int (out.val[2 * i.val + 1]!).val))
                        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                            (lift_fe_mont (a.elements.val[2 * i.val]!))
                            (lift_fe_mont (b.elements.val[2 * i.val + 1]!)))
                          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                            (lift_fe_mont (a.elements.val[2 * i.val + 1]!))
                            (lift_fe_mont (b.elements.val[2 * i.val]!))))
                ∧ (p.2.elements.val[i.val]!).val.natAbs ≤ 3328
                ∧ lift_fe_mont (p.2.elements.val[i.val]!)
                    = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                        (lift_fe_mont (b.elements.val[2 * i.val + 1]!))
                        (lift_fe_mont zeta)
                ∧ (∀ k : Nat, k < 16 → k ≠ i.val →
                    p.2.elements.val[k]! = cache.elements.val[k]!) ⌝ ⦄ := by
  -- ===== Setup (identical to L2.8c binomials_fc) =====
  have h_2i_lt : 2 * i.val < 16 := by omega
  have h_2i1_lt : 2 * i.val + 1 < 16 := by omega
  have h_a_len : a.elements.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length a
  have h_b_len : b.elements.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length b
  have h_cache_len : cache.elements.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length cache
  have h_out_val_len : out.val.length = 16 := h_out_len
  set ai_v : Std.I16 := a.elements.val[2 * i.val]! with hai_def
  set bi_v : Std.I16 := b.elements.val[2 * i.val]! with hbi_def
  set aj_v : Std.I16 := a.elements.val[2 * i.val + 1]! with haj_def
  set bj_v : Std.I16 := b.elements.val[2 * i.val + 1]! with hbj_def
  have h_ai : ai_v.val.natAbs ≤ 3328 := h_a ⟨2 * i.val, h_2i_lt⟩
  have h_bi : bi_v.val.natAbs ≤ 3328 := h_b ⟨2 * i.val, h_2i_lt⟩
  have h_aj : aj_v.val.natAbs ≤ 3328 := h_a ⟨2 * i.val + 1, h_2i1_lt⟩
  have h_bj : bj_v.val.natAbs ≤ 3328 := h_b ⟨2 * i.val + 1, h_2i1_lt⟩
  set old_e : Std.I32 := out.val[2 * i.val]! with hoe_def
  set old_o : Std.I32 := out.val[2 * i.val + 1]! with hoo_def
  have h_old_e_bnd : old_e.val.natAbs ≤ 2^30 + 2^25 := h_out_bnd ⟨2 * i.val, h_2i_lt⟩
  have h_old_o_bnd : old_o.val.natAbs ≤ 2^30 + 2^25 := h_out_bnd ⟨2 * i.val + 1, h_2i1_lt⟩
  -- ===== Index arithmetic =====
  obtain ⟨i1, h_i1_eq, h_i1_val⟩ :=
    usize_mul_ok_eq_fc 2#usize i (by scalar_tac)
  have h_i1_val' : i1.val = 2 * i.val := by
    rw [h_i1_val]; rfl
  obtain ⟨i2, h_i2_eq, h_i2_val⟩ :=
    usize_add_ok_eq_fc i1 1#usize (by scalar_tac)
  have h_i2_val' : i2.val = 2 * i.val + 1 := by
    rw [h_i2_val, h_i1_val']; rfl
  -- ===== Reads (with index_usize_ok_eq) =====
  have h_read_ai :
      Aeneas.Std.Array.index_usize a.elements i1 = .ok ai_v := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a.elements i1
      (by rw [h_a_len, h_i1_val']; exact h_2i_lt)
    rw [h, h_i1_val']
  have h_read_bi :
      Aeneas.Std.Array.index_usize b.elements i1 = .ok bi_v := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq b.elements i1
      (by rw [h_b_len, h_i1_val']; exact h_2i_lt)
    rw [h, h_i1_val']
  have h_read_aj :
      Aeneas.Std.Array.index_usize a.elements i2 = .ok aj_v := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a.elements i2
      (by rw [h_a_len, h_i2_val']; exact h_2i1_lt)
    rw [h, h_i2_val']
  have h_read_bj :
      Aeneas.Std.Array.index_usize b.elements i2 = .ok bj_v := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq b.elements i2
      (by rw [h_b_len, h_i2_val']; exact h_2i1_lt)
    rw [h, h_i2_val']
  -- ===== as_i32 casts =====
  set ai32 : Std.I32 := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 ai_v with hai32_def
  set bi32 : Std.I32 := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 bi_v with hbi32_def
  set aj32 : Std.I32 := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 aj_v with haj32_def
  set bj32 : Std.I32 := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 bj_v with hbj32_def
  set zeta32 : Std.I32 := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 zeta with hzeta32_def
  have h_ai32_val : ai32.val = ai_v.val := L2_8c.cast_I32_val ai_v
  have h_bi32_val : bi32.val = bi_v.val := L2_8c.cast_I32_val bi_v
  have h_aj32_val : aj32.val = aj_v.val := L2_8c.cast_I32_val aj_v
  have h_bj32_val : bj32.val = bj_v.val := L2_8c.cast_I32_val bj_v
  have h_zeta32_val : zeta32.val = zeta.val := L2_8c.cast_I32_val zeta
  have h_as_ai : libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 ai_v = .ok ai32 :=
    L2_8c.as_i32_val_eq ai_v
  have h_as_bi : libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 bi_v = .ok bi32 :=
    L2_8c.as_i32_val_eq bi_v
  have h_as_aj : libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 aj_v = .ok aj32 :=
    L2_8c.as_i32_val_eq aj_v
  have h_as_bj : libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 bj_v = .ok bj32 :=
    L2_8c.as_i32_val_eq bj_v
  have h_as_zeta : libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 zeta = .ok zeta32 :=
    L2_8c.as_i32_val_eq zeta
  -- ===== Step: ai_bi = wrapping_mul ai32 bi32 =====
  set ai_bi : Std.I32 := Aeneas.Std.I32.wrapping_mul ai32 bi32 with habi_def
  have h_ai_bi_eq : CoreModels.core.num.I32.wrapping_mul ai32 bi32 = .ok ai_bi :=
    L2_8c.cm_wrapping_mul_i32_ok_eq ai32 bi32
  have h_ai_bi_val : ai_bi.val = ai_v.val * bi_v.val := by
    have h_bnd : (ai32.val * bi32.val).natAbs < 2^31 := by
      rw [h_ai32_val, h_bi32_val]
      have h := Int.natAbs_mul ai_v.val bi_v.val
      have : ai_v.val.natAbs * bi_v.val.natAbs ≤ 3328 * 3328 := by
        exact Nat.mul_le_mul h_ai h_bi
      rw [h]
      have : (3328 * 3328 : Nat) < 2^31 := by decide
      omega
    have := L2_8c.wrapping_mul_i32_no_overflow ai32 bi32 h_bnd
    rw [this, h_ai32_val, h_bi32_val]
  -- ===== Step: bj_zeta_ = wrapping_mul bj32 zeta32 =====
  set bj_zeta_ : Std.I32 := Aeneas.Std.I32.wrapping_mul bj32 zeta32 with hbjz_def
  have h_bj_zeta_eq : CoreModels.core.num.I32.wrapping_mul bj32 zeta32 = .ok bj_zeta_ :=
    L2_8c.cm_wrapping_mul_i32_ok_eq bj32 zeta32
  have h_bj_zeta_val : bj_zeta_.val = bj_v.val * zeta.val := by
    have h_bnd : (bj32.val * zeta32.val).natAbs < 2^31 := by
      rw [h_bj32_val, h_zeta32_val]
      rw [Int.natAbs_mul]
      have h_mul : bj_v.val.natAbs * zeta.val.natAbs ≤ 3328 * 1664 :=
        Nat.mul_le_mul h_bj h_zeta
      have : (3328 * 1664 : Nat) < 2^31 := by decide
      omega
    have := L2_8c.wrapping_mul_i32_no_overflow bj32 zeta32 h_bnd
    rw [this, h_bj32_val, h_zeta32_val]
  -- ===== Step: bj_zeta = montgomery_reduce_element bj_zeta_ =====
  have h_bj_zeta_pre : bj_zeta_.val.natAbs ≤ 2^16 * 3328 := by
    rw [h_bj_zeta_val]
    rw [Int.natAbs_mul]
    have h_mul : bj_v.val.natAbs * zeta.val.natAbs ≤ 3328 * 1664 :=
      Nat.mul_le_mul h_bj h_zeta
    have : (3328 * 1664 : Nat) ≤ 2^16 * 3328 := by decide
    omega
  obtain ⟨bj_zeta, h_bj_zeta_ok, h_bj_zeta_bnd, h_bj_zeta_lift⟩ :=
    triple_exists_ok_fc (montgomery_reduce_element_fc bj_zeta_ h_bj_zeta_pre)
  have h_bj_zeta_pre' : bj_zeta_.val.natAbs ≤ 3328 * 2^16 := by
    rw [show (3328 * 2^16 : Nat) = 2^16 * 3328 from by decide]; exact h_bj_zeta_pre
  obtain ⟨bj_zeta', h_bj_zeta_ok', _h_bnd', h_tight_imp, h_bj_zeta_modq⟩ :=
    triple_exists_ok_fc
      (libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.montgomery_reduce_element_spec bj_zeta_ h_bj_zeta_pre')
  have h_bj_zeta_eq2 : bj_zeta = bj_zeta' := by
    have h_both : (Result.ok bj_zeta : Result _) = Result.ok bj_zeta' := by
      rw [← h_bj_zeta_ok, h_bj_zeta_ok']
    cases h_both; rfl
  -- Tight canonical bound for the cache POST: |bj * zeta| ≤ 3328 * 1664 ≤ 3328 * 2^15
  -- discharges the conditional in `montgomery_reduce_element_spec`.
  have h_bj_zeta_tight_pre : bj_zeta_.val.natAbs ≤ 3328 * 2^15 := by
    rw [h_bj_zeta_val, Int.natAbs_mul]
    have h_mul : bj_v.val.natAbs * zeta.val.natAbs ≤ 3328 * 1664 :=
      Nat.mul_le_mul h_bj h_zeta
    have h_le : (3328 * 1664 : Nat) ≤ 3328 * 2^15 := by decide
    omega
  have h_bj_zeta_canon : bj_zeta.val.natAbs ≤ 3328 := by
    rw [h_bj_zeta_eq2]; exact h_tight_imp h_bj_zeta_tight_pre
  -- ===== Cache write step (NEW): Array.update cache.elements i bj_zeta = .ok (cache.set i bj_zeta) =====
  have h_upd_cache :
      Aeneas.Std.Array.update cache.elements i bj_zeta
        = .ok (cache.elements.set i bj_zeta) :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_update_ok_eq cache.elements i bj_zeta
      (by rw [h_cache_len]; exact (by omega : i.val < 16))
  set cache_new : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    { elements := cache.elements.set i bj_zeta } with hcn_def
  -- ===== Step: aj_bj_zeta = wrapping_mul aj32 (as_i32 bj_zeta) =====
  set bj_zeta32 : Std.I32 :=
    Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 bj_zeta with hbjz32_def
  have h_bj_zeta32_val : bj_zeta32.val = bj_zeta.val := L2_8c.cast_I32_val bj_zeta
  have h_as_bj_zeta : libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 bj_zeta
      = .ok bj_zeta32 := L2_8c.as_i32_val_eq bj_zeta
  set aj_bj_zeta : Std.I32 := Aeneas.Std.I32.wrapping_mul aj32 bj_zeta32 with habjz_def
  have h_aj_bj_zeta_eq : CoreModels.core.num.I32.wrapping_mul aj32 bj_zeta32 = .ok aj_bj_zeta :=
    L2_8c.cm_wrapping_mul_i32_ok_eq aj32 bj_zeta32
  have h_aj_bj_zeta_val : aj_bj_zeta.val = aj_v.val * bj_zeta.val := by
    have h_bnd : (aj32.val * bj_zeta32.val).natAbs < 2^31 := by
      rw [h_aj32_val, h_bj_zeta32_val, Int.natAbs_mul]
      have h_mul : aj_v.val.natAbs * bj_zeta.val.natAbs ≤ 3328 * (3328 + 1665) :=
        Nat.mul_le_mul h_aj h_bj_zeta_bnd
      have : (3328 * (3328 + 1665) : Nat) < 2^31 := by decide
      omega
    have := L2_8c.wrapping_mul_i32_no_overflow aj32 bj_zeta32 h_bnd
    rw [this, h_aj32_val, h_bj_zeta32_val]
  -- ===== Step: ai_bi_aj_bj = wrapping_add ai_bi aj_bj_zeta =====
  set ai_bi_aj_bj : Std.I32 := Aeneas.Std.I32.wrapping_add ai_bi aj_bj_zeta with hsum_e_def
  have h_sum_e_eq : CoreModels.core.num.I32.wrapping_add ai_bi aj_bj_zeta = .ok ai_bi_aj_bj :=
    L2_8c.cm_wrapping_add_i32_ok_eq ai_bi aj_bj_zeta
  have h_sum_e_bnd : (ai_bi.val + aj_bj_zeta.val).natAbs ≤ 3328 * 3328 + 3328 * (3328 + 1665) := by
    rw [h_ai_bi_val, h_aj_bj_zeta_val]
    have h_e1 : (ai_v.val * bi_v.val).natAbs ≤ 3328 * 3328 := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul h_ai h_bi
    have h_e2 : (aj_v.val * bj_zeta.val).natAbs ≤ 3328 * (3328 + 1665) := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul h_aj h_bj_zeta_bnd
    have h_tri : ((ai_v.val * bi_v.val) + (aj_v.val * bj_zeta.val)).natAbs
                  ≤ (ai_v.val * bi_v.val).natAbs + (aj_v.val * bj_zeta.val).natAbs :=
      Int.natAbs_add_le _ _
    omega
  have h_sum_e_val : ai_bi_aj_bj.val = ai_bi.val + aj_bj_zeta.val := by
    have h_bnd : (ai_bi.val + aj_bj_zeta.val).natAbs < 2^31 := by
      have h_le : (3328 * 3328 + 3328 * (3328 + 1665) : Nat) < 2^31 := by decide
      omega
    exact L2_8c.wrapping_add_i32_no_overflow ai_bi aj_bj_zeta h_bnd
  have h_delta_e_bnd : ai_bi_aj_bj.val.natAbs ≤ 2^25 := by
    rw [h_sum_e_val]
    have : (3328 * 3328 + 3328 * (3328 + 1665) : Nat) ≤ 2^25 := by decide
    omega
  -- ===== Step: ai_bj = wrapping_mul ai32 bj32 =====
  set ai_bj_p : Std.I32 := Aeneas.Std.I32.wrapping_mul ai32 bj32 with haibj_def
  have h_ai_bj_eq : CoreModels.core.num.I32.wrapping_mul ai32 bj32 = .ok ai_bj_p :=
    L2_8c.cm_wrapping_mul_i32_ok_eq ai32 bj32
  have h_ai_bj_val : ai_bj_p.val = ai_v.val * bj_v.val := by
    have h_bnd : (ai32.val * bj32.val).natAbs < 2^31 := by
      rw [h_ai32_val, h_bj32_val, Int.natAbs_mul]
      have h_mul : ai_v.val.natAbs * bj_v.val.natAbs ≤ 3328 * 3328 :=
        Nat.mul_le_mul h_ai h_bj
      have : (3328 * 3328 : Nat) < 2^31 := by decide
      omega
    have := L2_8c.wrapping_mul_i32_no_overflow ai32 bj32 h_bnd
    rw [this, h_ai32_val, h_bj32_val]
  -- ===== Step: aj_bi = wrapping_mul aj32 bi32 =====
  set aj_bi_p : Std.I32 := Aeneas.Std.I32.wrapping_mul aj32 bi32 with hajbi_def
  have h_aj_bi_eq : CoreModels.core.num.I32.wrapping_mul aj32 bi32 = .ok aj_bi_p :=
    L2_8c.cm_wrapping_mul_i32_ok_eq aj32 bi32
  have h_aj_bi_val : aj_bi_p.val = aj_v.val * bi_v.val := by
    have h_bnd : (aj32.val * bi32.val).natAbs < 2^31 := by
      rw [h_aj32_val, h_bi32_val, Int.natAbs_mul]
      have h_mul : aj_v.val.natAbs * bi_v.val.natAbs ≤ 3328 * 3328 :=
        Nat.mul_le_mul h_aj h_bi
      have : (3328 * 3328 : Nat) < 2^31 := by decide
      omega
    have := L2_8c.wrapping_mul_i32_no_overflow aj32 bi32 h_bnd
    rw [this, h_aj32_val, h_bi32_val]
  -- ===== Step: ai_bj_aj_bi = wrapping_add ai_bj aj_bi =====
  set ai_bj_aj_bi : Std.I32 := Aeneas.Std.I32.wrapping_add ai_bj_p aj_bi_p with hsum_o_def
  have h_sum_o_eq : CoreModels.core.num.I32.wrapping_add ai_bj_p aj_bi_p = .ok ai_bj_aj_bi :=
    L2_8c.cm_wrapping_add_i32_ok_eq ai_bj_p aj_bi_p
  have h_sum_o_bnd : (ai_bj_p.val + aj_bi_p.val).natAbs ≤ 2 * 3328 * 3328 := by
    rw [h_ai_bj_val, h_aj_bi_val]
    have h_e1 : (ai_v.val * bj_v.val).natAbs ≤ 3328 * 3328 := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul h_ai h_bj
    have h_e2 : (aj_v.val * bi_v.val).natAbs ≤ 3328 * 3328 := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul h_aj h_bi
    have h_tri := Int.natAbs_add_le (ai_v.val * bj_v.val) (aj_v.val * bi_v.val)
    omega
  have h_sum_o_val : ai_bj_aj_bi.val = ai_bj_p.val + aj_bi_p.val := by
    have h_bnd : (ai_bj_p.val + aj_bi_p.val).natAbs < 2^31 := by
      have : (2 * 3328 * 3328 : Nat) < 2^31 := by decide
      omega
    exact L2_8c.wrapping_add_i32_no_overflow ai_bj_p aj_bi_p h_bnd
  have h_delta_o_bnd : ai_bj_aj_bi.val.natAbs ≤ 2^25 := by
    rw [h_sum_o_val]
    have : (2 * 3328 * 3328 : Nat) ≤ 2^25 := by decide
    omega
  -- ===== Slice reads + writes for `out` =====
  have h_read_old_e : Aeneas.Std.Slice.index_usize out i1 = .ok old_e := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq out i1
      (by rw [h_out_val_len, h_i1_val']; exact h_2i_lt)
    rw [h, h_i1_val']
  set new_e : Std.I32 := Aeneas.Std.I32.wrapping_add old_e ai_bi_aj_bj with hne_def
  have h_new_e_eq : CoreModels.core.num.I32.wrapping_add old_e ai_bi_aj_bj = .ok new_e :=
    L2_8c.cm_wrapping_add_i32_ok_eq old_e ai_bi_aj_bj
  have h_new_e_val : new_e.val = old_e.val + ai_bi_aj_bj.val := by
    have h_bnd : (old_e.val + ai_bi_aj_bj.val).natAbs < 2^31 := by
      have h_tri := Int.natAbs_add_le old_e.val ai_bi_aj_bj.val
      have : (2^30 + 2^25 + 2^25 : Nat) < 2^31 := by decide
      omega
    exact L2_8c.wrapping_add_i32_no_overflow old_e ai_bi_aj_bj h_bnd
  have h_new_e_bnd : new_e.val.natAbs ≤ old_e.val.natAbs + 2^25 := by
    rw [h_new_e_val]
    have h_tri := Int.natAbs_add_le old_e.val ai_bi_aj_bj.val
    omega
  have h_upd_e : Aeneas.Std.Slice.update out i1 new_e = .ok (out.set i1 new_e) := by
    have hT := Aeneas.Std.Slice.update_spec out i1 new_e (by rw [h_out_len, h_i1_val']; exact h_2i_lt)
    obtain ⟨v', h_eq, h_v'⟩ := Aeneas.Std.WP.spec_imp_exists hT
    rw [h_eq, h_v']
  set out1 : Aeneas.Std.Slice Std.I32 := out.set i1 new_e with hout1_def
  have h_out1_len : out1.length = 16 := by simp [hout1_def]; exact h_out_len
  have h_out1_val_len : out1.val.length = 16 := h_out1_len
  have h_old_o_in_out1 : out1.val[i2.val]! = old_o := by
    have h_set_val : out1.val = out.val.set i1.val new_e := by
      simp [hout1_def, Aeneas.Std.Slice.set_val_eq]
    have h_ne : 2 * i.val + 1 ≠ i1.val := by rw [h_i1_val']; omega
    have h_lt : 2 * i.val + 1 < out.val.length := by rw [h_out_val_len]; exact h_2i1_lt
    rw [h_set_val, h_i2_val', hoo_def]
    have h_lt_set : 2 * i.val + 1 < (out.val.set i1.val new_e).length := by
      rw [List.length_set]; exact h_lt
    rw [getElem!_pos (out.val.set i1.val new_e) (2 * i.val + 1) h_lt_set]
    rw [getElem!_pos out.val (2 * i.val + 1) h_lt]
    rw [List.getElem_set_ne (Ne.symm h_ne)]
  have h_read_old_o : Aeneas.Std.Slice.index_usize out1 i2 = .ok old_o := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq out1 i2
      (by rw [h_out1_val_len, h_i2_val']; exact h_2i1_lt)
    rw [h, h_old_o_in_out1]
  set new_o : Std.I32 := Aeneas.Std.I32.wrapping_add old_o ai_bj_aj_bi with hno_def
  have h_new_o_eq : CoreModels.core.num.I32.wrapping_add old_o ai_bj_aj_bi = .ok new_o :=
    L2_8c.cm_wrapping_add_i32_ok_eq old_o ai_bj_aj_bi
  have h_new_o_val : new_o.val = old_o.val + ai_bj_aj_bi.val := by
    have h_bnd : (old_o.val + ai_bj_aj_bi.val).natAbs < 2^31 := by
      have h_tri := Int.natAbs_add_le old_o.val ai_bj_aj_bi.val
      have : (2^30 + 2^25 + 2^25 : Nat) < 2^31 := by decide
      omega
    exact L2_8c.wrapping_add_i32_no_overflow old_o ai_bj_aj_bi h_bnd
  have h_new_o_bnd : new_o.val.natAbs ≤ old_o.val.natAbs + 2^25 := by
    rw [h_new_o_val]
    have h_tri := Int.natAbs_add_le old_o.val ai_bj_aj_bi.val
    omega
  have h_upd_o : Aeneas.Std.Slice.update out1 i2 new_o = .ok (out1.set i2 new_o) := by
    have hT := Aeneas.Std.Slice.update_spec out1 i2 new_o
      (by rw [h_out1_len, h_i2_val']; exact h_2i1_lt)
    obtain ⟨v', h_eq, h_v'⟩ := Aeneas.Std.WP.spec_imp_exists hT
    rw [h_eq, h_v']
  set out2 : Aeneas.Std.Slice Std.I32 := out1.set i2 new_o with hout2_def
  -- ===== Compose the monadic body =====
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
        a b zeta i out cache = .ok (out2, cache_new) := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
    simp only [h_i1_eq, h_i2_eq, h_read_ai, h_read_bi, h_read_aj, h_read_bj,
               h_as_ai, h_as_bi, h_as_aj, h_as_bj, h_as_zeta, h_as_bj_zeta,
               h_ai_bi_eq, h_bj_zeta_eq, h_bj_zeta_ok, h_upd_cache, h_aj_bj_zeta_eq,
               h_sum_e_eq, h_ai_bj_eq, h_aj_bi_eq, h_sum_o_eq,
               h_read_old_e, h_new_e_eq, h_upd_e,
               h_read_old_o, h_new_o_eq, h_upd_o,
               Aeneas.Std.bind_tc_ok]
    rfl
  apply triple_of_ok_fc h_body
  -- ===== POST: 10-conjunct =====
  -- out2 unfolding (same as L2.8c).
  have h_out2_val : out2.val = (out.val.set i1.val new_e).set i2.val new_o := by
    show ((out.set i1 new_e).set i2 new_o).val = _
    rw [Aeneas.Std.Slice.set_val_eq, Aeneas.Std.Slice.set_val_eq]
  have h_out2_len : out2.length = 16 := by
    show ((out.set i1 new_e).set i2 new_o).length = 16
    rw [Aeneas.Std.Slice.set_length, Aeneas.Std.Slice.set_length]; exact h_out_len
  have h_out2_val_len : out2.val.length = 16 := h_out2_len
  have h_out2_at_2i : out2.val[2 * i.val]! = new_e := by
    rw [h_out2_val, ← h_i1_val']
    have h_lt_out : i1.val < out.val.length := by rw [h_out_val_len, h_i1_val']; exact h_2i_lt
    have h_lt1 : i1.val < (out.val.set i1.val new_e).length := by
      rw [List.length_set]; exact h_lt_out
    have h_lt2 : i1.val < ((out.val.set i1.val new_e).set i2.val new_o).length := by
      rw [List.length_set]; exact h_lt1
    rw [getElem!_pos ((out.val.set i1.val new_e).set i2.val new_o) i1.val h_lt2]
    rw [List.getElem_set_ne (by rw [h_i2_val', h_i1_val']; omega)]
    rw [List.getElem_set_self]
  have h_out2_at_2i1 : out2.val[2 * i.val + 1]! = new_o := by
    rw [h_out2_val, ← h_i2_val']
    have h_lt_out : i2.val < out.val.length := by rw [h_out_val_len, h_i2_val']; exact h_2i1_lt
    have h_lt1 : i2.val < (out.val.set i1.val new_e).length := by
      rw [List.length_set]; exact h_lt_out
    have h_lt2 : i2.val < ((out.val.set i1.val new_e).set i2.val new_o).length := by
      rw [List.length_set]; exact h_lt1
    rw [getElem!_pos ((out.val.set i1.val new_e).set i2.val new_o) i2.val h_lt2]
    rw [List.getElem_set_self]
  have h_out2_untouched : ∀ k : Nat, k < 16 → k ≠ 2 * i.val → k ≠ 2 * i.val + 1 →
      out2.val[k]! = out.val[k]! := by
    intro k hk hki hkj
    rw [h_out2_val]
    have h_lt_out : k < out.val.length := by rw [h_out_val_len]; exact hk
    have h_lt1 : k < (out.val.set i1.val new_e).length := by rw [List.length_set]; exact h_lt_out
    have h_lt2 : k < ((out.val.set i1.val new_e).set i2.val new_o).length := by
      rw [List.length_set]; exact h_lt1
    rw [getElem!_pos ((out.val.set i1.val new_e).set i2.val new_o) k h_lt2]
    rw [getElem!_pos out.val k h_lt_out]
    rw [List.getElem_set_ne (by rw [h_i2_val']; omega)]
    rw [List.getElem_set_ne (by rw [h_i1_val']; omega)]
  -- ===== Cache POST conjuncts =====
  -- cache_new.elements.val = cache.elements.val.set i.val bj_zeta.
  have h_cache_new_val :
      cache_new.elements.val = cache.elements.val.set i.val bj_zeta := by
    simp [hcn_def, Aeneas.Std.Array.set_val_eq]
  have h_cache_val_len : cache.elements.val.length = 16 := h_cache_len
  have h_cache_at_i : cache_new.elements.val[i.val]! = bj_zeta := by
    rw [h_cache_new_val]
    have h_lt : i.val < cache.elements.val.length := by rw [h_cache_val_len]; omega
    have h_lt_set : i.val < (cache.elements.val.set i.val bj_zeta).length := by
      rw [List.length_set]; exact h_lt
    rw [getElem!_pos (cache.elements.val.set i.val bj_zeta) i.val h_lt_set]
    rw [List.getElem_set_self]
  have h_cache_untouched : ∀ k : Nat, k < 16 → k ≠ i.val →
      cache_new.elements.val[k]! = cache.elements.val[k]! := by
    intro k hk hki
    rw [h_cache_new_val]
    have h_lt : k < cache.elements.val.length := by rw [h_cache_val_len]; exact hk
    have h_lt_set : k < (cache.elements.val.set i.val bj_zeta).length := by
      rw [List.length_set]; exact h_lt
    rw [getElem!_pos (cache.elements.val.set i.val bj_zeta) k h_lt_set]
    rw [getElem!_pos cache.elements.val k h_lt]
    rw [List.getElem_set_ne (Ne.symm hki)]
  -- The cache POST FE-equation conjunct: lift_fe_mont bj_zeta = mul (lift bj) (lift zeta).
  have h_cache_fe :
      lift_fe_mont bj_zeta
        = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (lift_fe_mont bj_v) (lift_fe_mont zeta) := by
    -- Convert h_bj_zeta_modq to ZMod equation and invoke the helper.
    have h_modq_cast : ((bj_zeta'.val : Int) : ZMod 3329)
        = ((bj_zeta_.val * 169 : Int) : ZMod 3329) :=
      modq_eq_cast_zmod _ _ h_bj_zeta_modq
    rw [h_bj_zeta_eq2.symm] at h_modq_cast
    rw [h_bj_zeta_val] at h_modq_cast
    push_cast at h_modq_cast
    -- h_modq_cast : (bj_zeta.val : ZMod q) = (bj.val * zeta.val * 169 : ZMod q).
    apply L2_8d.lift_fe_mont_of_mont_reduce_modq bj_zeta bj_v zeta h_bj_zeta_canon
    -- Goal: ((bj_zeta.val : Int) : ZMod q) * 2^16 = (bj.val : ZMod q) * (zeta.val : ZMod q).
    push_cast
    rw [h_modq_cast]
    -- Goal: bj * zeta * 169 * 2^16 = bj * zeta. Use 2^16 * 169 = 1.
    have h_inv : ((2285 : ZMod 3329)) * 169 = 1 := by decide
    rw [show (((bj_v.val : Int) : ZMod 3329) * ((zeta.val : Int) : ZMod 3329) * 169) * 2285
              = ((bj_v.val : Int) : ZMod 3329) * ((zeta.val : Int) : ZMod 3329) * (169 * 2285)
            from by ring]
    rw [show ((169 : ZMod 3329) * 2285) = (2285 * 169 : ZMod 3329) from by ring]
    rw [h_inv]
    ring
  -- ===== Assemble the 10-conjunct POST =====
  -- Note: target POST mentions `p.2.elements.val[k]!` (where p = (out2, cache_new)),
  -- which is `cache_new.elements.val[k]!`. The tight canonical bound for the
  -- cache POST was established above as `h_bj_zeta_canon`.
  refine ⟨h_out2_len, h_out2_untouched, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Bound at 2*i.
    rw [h_out2_at_2i, hoe_def] at *
    rw [h_out2_at_2i]
    rw [hoe_def] at h_new_e_bnd
    exact h_new_e_bnd
  · -- Bound at 2*i+1.
    rw [h_out2_at_2i1]
    rw [hoo_def] at h_new_o_bnd
    exact h_new_o_bnd
  · -- FE eq (even half) — identical algebra to L2.8c binomials_fc.
    rw [h_out2_at_2i, hoe_def]
    have h_modq_cast : ((bj_zeta'.val : Int) : ZMod 3329)
        = ((bj_zeta_.val * 169 : Int) : ZMod 3329) :=
      modq_eq_cast_zmod _ _ h_bj_zeta_modq
    rw [h_bj_zeta_eq2.symm] at h_modq_cast
    rw [h_bj_zeta_val] at h_modq_cast
    push_cast at h_modq_cast
    apply L2_8c.mont_reduce_even_fe_eq
      (out := out.val[2 * i.val]!) (r := new_e)
      (ai := ai_v) (bi := bi_v) (aj := aj_v) (bj := bj_v) (zeta := zeta)
    rw [← hoe_def, h_new_e_val, h_sum_e_val, h_ai_bi_val, h_aj_bj_zeta_val]
    push_cast
    rw [h_modq_cast]
    have h_inv : ((2285 : ZMod 3329)) * 169 = 1 := by decide
    calc ((old_e.val : ZMod 3329) + ((ai_v.val : ZMod 3329) * (bi_v.val : ZMod 3329)
          + (aj_v.val : ZMod 3329) * ((bj_v.val : ZMod 3329) * (zeta.val : ZMod 3329) * 169)))
            * 2285
        = (old_e.val : ZMod 3329) * 2285
          + (ai_v.val : ZMod 3329) * (bi_v.val : ZMod 3329) * 2285
          + (aj_v.val : ZMod 3329) * (bj_v.val : ZMod 3329) * (zeta.val : ZMod 3329)
              * (2285 * 169) := by ring
      _ = (old_e.val : ZMod 3329) * 2285
          + (ai_v.val : ZMod 3329) * (bi_v.val : ZMod 3329) * 2285
          + (aj_v.val : ZMod 3329) * (bj_v.val : ZMod 3329) * (zeta.val : ZMod 3329) := by
            rw [h_inv]; ring
  · -- FE eq (odd half).
    rw [h_out2_at_2i1, hoo_def]
    apply L2_8c.mont_reduce_odd_fe_eq
      (out := out.val[2 * i.val + 1]!) (r := new_o)
      (ai := ai_v) (bi := bi_v) (aj := aj_v) (bj := bj_v)
    rw [← hoo_def, h_new_o_val, h_sum_o_val, h_ai_bj_val, h_aj_bi_val]
    push_cast
    ring
  · -- Cache canonicity at slot i.
    rw [h_cache_at_i]; exact h_bj_zeta_canon
  · -- Cache FE-equation at slot i.
    rw [h_cache_at_i, hbj_def]; exact h_cache_fe
  · -- Cache unchanged outside slot i.
    exact h_cache_untouched

set_option maxHeartbeats 8000000 in
/-- Per-pair Triple for `accumulating_ntt_multiply_binomials_use_cache`.
    Reads `cache[i]` (an I16) in place of the per-pair Mont-reduced
    `b[2i+1]·zeta`. The cache PRE conjunct asserts canonicity
    (`|cache[i].val| ≤ 3328`); the FE equation for the even half
    leaves the cached lane symbolic (the outer use_cache Triple
    rewrites it using the cache PRE FE equation). -/
theorem accumulating_ntt_multiply_binomials_use_cache_fc
    (a b : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (i : Std.Usize)
    (out : Aeneas.Std.Slice Std.I32)
    (cache : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_i : i.val < 8)
    (h_out_len : out.length = 16)
    (h_a : ∀ j : Fin 16, (a.elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_b : ∀ j : Fin 16, (b.elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_cache_i : (cache.elements.val[i.val]!).val.natAbs ≤ 3328)
    (h_out_bnd : ∀ k : Fin 16, (out.val[k.val]!).val.natAbs ≤ 2^30 + 2^25) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_use_cache
      a b i out cache
    ⦃ ⇓ r => ⌜ r.length = 16
                ∧ (∀ k : Nat, k < 16 → k ≠ 2 * i.val → k ≠ 2 * i.val + 1 →
                    r.val[k]! = out.val[k]!)
                ∧ (r.val[2 * i.val]!).val.natAbs
                    ≤ (out.val[2 * i.val]!).val.natAbs + 2^25
                ∧ (r.val[2 * i.val + 1]!).val.natAbs
                    ≤ (out.val[2 * i.val + 1]!).val.natAbs + 2^25
                ∧ Spec.mont_reduce_pure (lift_fe_int (r.val[2 * i.val]!).val)
                    = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                        (Spec.mont_reduce_pure (lift_fe_int (out.val[2 * i.val]!).val))
                        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                            (lift_fe_mont (a.elements.val[2 * i.val]!))
                            (lift_fe_mont (b.elements.val[2 * i.val]!)))
                          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                            (lift_fe_mont (a.elements.val[2 * i.val + 1]!))
                            (lift_fe_mont (cache.elements.val[i.val]!))))
                ∧ Spec.mont_reduce_pure (lift_fe_int (r.val[2 * i.val + 1]!).val)
                    = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                        (Spec.mont_reduce_pure (lift_fe_int (out.val[2 * i.val + 1]!).val))
                        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                            (lift_fe_mont (a.elements.val[2 * i.val]!))
                            (lift_fe_mont (b.elements.val[2 * i.val + 1]!)))
                          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                            (lift_fe_mont (a.elements.val[2 * i.val + 1]!))
                            (lift_fe_mont (b.elements.val[2 * i.val]!)))) ⌝ ⦄ := by
  -- ===== Setup =====
  have h_2i_lt : 2 * i.val < 16 := by omega
  have h_2i1_lt : 2 * i.val + 1 < 16 := by omega
  have h_a_len : a.elements.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length a
  have h_b_len : b.elements.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length b
  have h_cache_len : cache.elements.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length cache
  have h_out_val_len : out.val.length = 16 := h_out_len
  set ai_v : Std.I16 := a.elements.val[2 * i.val]! with hai_def
  set bi_v : Std.I16 := b.elements.val[2 * i.val]! with hbi_def
  set aj_v : Std.I16 := a.elements.val[2 * i.val + 1]! with haj_def
  set bj_v : Std.I16 := b.elements.val[2 * i.val + 1]! with hbj_def
  set c_v : Std.I16 := cache.elements.val[i.val]! with hcv_def
  have h_ai : ai_v.val.natAbs ≤ 3328 := h_a ⟨2 * i.val, h_2i_lt⟩
  have h_bi : bi_v.val.natAbs ≤ 3328 := h_b ⟨2 * i.val, h_2i_lt⟩
  have h_aj : aj_v.val.natAbs ≤ 3328 := h_a ⟨2 * i.val + 1, h_2i1_lt⟩
  have h_bj : bj_v.val.natAbs ≤ 3328 := h_b ⟨2 * i.val + 1, h_2i1_lt⟩
  have h_cv : c_v.val.natAbs ≤ 3328 := h_cache_i
  set old_e : Std.I32 := out.val[2 * i.val]! with hoe_def
  set old_o : Std.I32 := out.val[2 * i.val + 1]! with hoo_def
  have h_old_e_bnd : old_e.val.natAbs ≤ 2^30 + 2^25 := h_out_bnd ⟨2 * i.val, h_2i_lt⟩
  have h_old_o_bnd : old_o.val.natAbs ≤ 2^30 + 2^25 := h_out_bnd ⟨2 * i.val + 1, h_2i1_lt⟩
  -- ===== Index arithmetic =====
  obtain ⟨i1, h_i1_eq, h_i1_val⟩ :=
    usize_mul_ok_eq_fc 2#usize i (by scalar_tac)
  have h_i1_val' : i1.val = 2 * i.val := by
    rw [h_i1_val]; rfl
  obtain ⟨i2, h_i2_eq, h_i2_val⟩ :=
    usize_add_ok_eq_fc i1 1#usize (by scalar_tac)
  have h_i2_val' : i2.val = 2 * i.val + 1 := by
    rw [h_i2_val, h_i1_val']; rfl
  -- ===== Reads (with index_usize_ok_eq) =====
  have h_read_ai :
      Aeneas.Std.Array.index_usize a.elements i1 = .ok ai_v := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a.elements i1
      (by rw [h_a_len, h_i1_val']; exact h_2i_lt)
    rw [h, h_i1_val']
  have h_read_bi :
      Aeneas.Std.Array.index_usize b.elements i1 = .ok bi_v := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq b.elements i1
      (by rw [h_b_len, h_i1_val']; exact h_2i_lt)
    rw [h, h_i1_val']
  have h_read_aj :
      Aeneas.Std.Array.index_usize a.elements i2 = .ok aj_v := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a.elements i2
      (by rw [h_a_len, h_i2_val']; exact h_2i1_lt)
    rw [h, h_i2_val']
  have h_read_bj :
      Aeneas.Std.Array.index_usize b.elements i2 = .ok bj_v := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq b.elements i2
      (by rw [h_b_len, h_i2_val']; exact h_2i1_lt)
    rw [h, h_i2_val']
  have h_read_cv :
      Aeneas.Std.Array.index_usize cache.elements i = .ok c_v := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq cache.elements i
      (by rw [h_cache_len]; exact (by omega : i.val < 16))
    rw [h]
  -- ===== as_i32 casts =====
  set ai32 : Std.I32 := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 ai_v with hai32_def
  set bi32 : Std.I32 := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 bi_v with hbi32_def
  set aj32 : Std.I32 := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 aj_v with haj32_def
  set bj32 : Std.I32 := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 bj_v with hbj32_def
  set c32 : Std.I32 := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 c_v with hc32_def
  have h_ai32_val : ai32.val = ai_v.val := L2_8c.cast_I32_val ai_v
  have h_bi32_val : bi32.val = bi_v.val := L2_8c.cast_I32_val bi_v
  have h_aj32_val : aj32.val = aj_v.val := L2_8c.cast_I32_val aj_v
  have h_bj32_val : bj32.val = bj_v.val := L2_8c.cast_I32_val bj_v
  have h_c32_val : c32.val = c_v.val := L2_8c.cast_I32_val c_v
  have h_as_ai : libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 ai_v = .ok ai32 :=
    L2_8c.as_i32_val_eq ai_v
  have h_as_bi : libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 bi_v = .ok bi32 :=
    L2_8c.as_i32_val_eq bi_v
  have h_as_aj : libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 aj_v = .ok aj32 :=
    L2_8c.as_i32_val_eq aj_v
  have h_as_bj : libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 bj_v = .ok bj32 :=
    L2_8c.as_i32_val_eq bj_v
  have h_as_cv : libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 c_v = .ok c32 :=
    L2_8c.as_i32_val_eq c_v
  -- ===== Step: ai_bi = wrapping_mul ai32 bi32 =====
  set ai_bi : Std.I32 := Aeneas.Std.I32.wrapping_mul ai32 bi32 with habi_def
  have h_ai_bi_eq : CoreModels.core.num.I32.wrapping_mul ai32 bi32 = .ok ai_bi :=
    L2_8c.cm_wrapping_mul_i32_ok_eq ai32 bi32
  have h_ai_bi_val : ai_bi.val = ai_v.val * bi_v.val := by
    have h_bnd : (ai32.val * bi32.val).natAbs < 2^31 := by
      rw [h_ai32_val, h_bi32_val]
      have h := Int.natAbs_mul ai_v.val bi_v.val
      have : ai_v.val.natAbs * bi_v.val.natAbs ≤ 3328 * 3328 := by
        exact Nat.mul_le_mul h_ai h_bi
      rw [h]
      have : (3328 * 3328 : Nat) < 2^31 := by decide
      omega
    have := L2_8c.wrapping_mul_i32_no_overflow ai32 bi32 h_bnd
    rw [this, h_ai32_val, h_bi32_val]
  -- ===== Step: aj_bj_zeta = wrapping_mul aj32 c32 (uses cache directly) =====
  set aj_bj_zeta : Std.I32 := Aeneas.Std.I32.wrapping_mul aj32 c32 with habjz_def
  have h_aj_bj_zeta_eq : CoreModels.core.num.I32.wrapping_mul aj32 c32 = .ok aj_bj_zeta :=
    L2_8c.cm_wrapping_mul_i32_ok_eq aj32 c32
  have h_aj_bj_zeta_val : aj_bj_zeta.val = aj_v.val * c_v.val := by
    have h_bnd : (aj32.val * c32.val).natAbs < 2^31 := by
      rw [h_aj32_val, h_c32_val, Int.natAbs_mul]
      have h_mul : aj_v.val.natAbs * c_v.val.natAbs ≤ 3328 * 3328 :=
        Nat.mul_le_mul h_aj h_cv
      have : (3328 * 3328 : Nat) < 2^31 := by decide
      omega
    have := L2_8c.wrapping_mul_i32_no_overflow aj32 c32 h_bnd
    rw [this, h_aj32_val, h_c32_val]
  -- ===== Step: ai_bi_aj_bj = wrapping_add ai_bi aj_bj_zeta =====
  set ai_bi_aj_bj : Std.I32 := Aeneas.Std.I32.wrapping_add ai_bi aj_bj_zeta with hsum_e_def
  have h_sum_e_eq : CoreModels.core.num.I32.wrapping_add ai_bi aj_bj_zeta = .ok ai_bi_aj_bj :=
    L2_8c.cm_wrapping_add_i32_ok_eq ai_bi aj_bj_zeta
  have h_sum_e_bnd : (ai_bi.val + aj_bj_zeta.val).natAbs ≤ 2 * 3328 * 3328 := by
    rw [h_ai_bi_val, h_aj_bj_zeta_val]
    have h_e1 : (ai_v.val * bi_v.val).natAbs ≤ 3328 * 3328 := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul h_ai h_bi
    have h_e2 : (aj_v.val * c_v.val).natAbs ≤ 3328 * 3328 := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul h_aj h_cv
    have h_tri : ((ai_v.val * bi_v.val) + (aj_v.val * c_v.val)).natAbs
                  ≤ (ai_v.val * bi_v.val).natAbs + (aj_v.val * c_v.val).natAbs :=
      Int.natAbs_add_le _ _
    omega
  have h_sum_e_val : ai_bi_aj_bj.val = ai_bi.val + aj_bj_zeta.val := by
    have h_bnd : (ai_bi.val + aj_bj_zeta.val).natAbs < 2^31 := by
      have : (2 * 3328 * 3328 : Nat) < 2^31 := by decide
      omega
    exact L2_8c.wrapping_add_i32_no_overflow ai_bi aj_bj_zeta h_bnd
  have h_delta_e_bnd : ai_bi_aj_bj.val.natAbs ≤ 2^25 := by
    rw [h_sum_e_val]
    have : (2 * 3328 * 3328 : Nat) ≤ 2^25 := by decide
    omega
  -- ===== Step: ai_bj = wrapping_mul ai32 bj32 =====
  set ai_bj_p : Std.I32 := Aeneas.Std.I32.wrapping_mul ai32 bj32 with haibj_def
  have h_ai_bj_eq : CoreModels.core.num.I32.wrapping_mul ai32 bj32 = .ok ai_bj_p :=
    L2_8c.cm_wrapping_mul_i32_ok_eq ai32 bj32
  have h_ai_bj_val : ai_bj_p.val = ai_v.val * bj_v.val := by
    have h_bnd : (ai32.val * bj32.val).natAbs < 2^31 := by
      rw [h_ai32_val, h_bj32_val, Int.natAbs_mul]
      have h_mul : ai_v.val.natAbs * bj_v.val.natAbs ≤ 3328 * 3328 :=
        Nat.mul_le_mul h_ai h_bj
      have : (3328 * 3328 : Nat) < 2^31 := by decide
      omega
    have := L2_8c.wrapping_mul_i32_no_overflow ai32 bj32 h_bnd
    rw [this, h_ai32_val, h_bj32_val]
  -- ===== Step: aj_bi = wrapping_mul aj32 bi32 =====
  set aj_bi_p : Std.I32 := Aeneas.Std.I32.wrapping_mul aj32 bi32 with hajbi_def
  have h_aj_bi_eq : CoreModels.core.num.I32.wrapping_mul aj32 bi32 = .ok aj_bi_p :=
    L2_8c.cm_wrapping_mul_i32_ok_eq aj32 bi32
  have h_aj_bi_val : aj_bi_p.val = aj_v.val * bi_v.val := by
    have h_bnd : (aj32.val * bi32.val).natAbs < 2^31 := by
      rw [h_aj32_val, h_bi32_val, Int.natAbs_mul]
      have h_mul : aj_v.val.natAbs * bi_v.val.natAbs ≤ 3328 * 3328 :=
        Nat.mul_le_mul h_aj h_bi
      have : (3328 * 3328 : Nat) < 2^31 := by decide
      omega
    have := L2_8c.wrapping_mul_i32_no_overflow aj32 bi32 h_bnd
    rw [this, h_aj32_val, h_bi32_val]
  -- ===== Step: ai_bj_aj_bi = wrapping_add ai_bj aj_bi =====
  set ai_bj_aj_bi : Std.I32 := Aeneas.Std.I32.wrapping_add ai_bj_p aj_bi_p with hsum_o_def
  have h_sum_o_eq : CoreModels.core.num.I32.wrapping_add ai_bj_p aj_bi_p = .ok ai_bj_aj_bi :=
    L2_8c.cm_wrapping_add_i32_ok_eq ai_bj_p aj_bi_p
  have h_sum_o_bnd : (ai_bj_p.val + aj_bi_p.val).natAbs ≤ 2 * 3328 * 3328 := by
    rw [h_ai_bj_val, h_aj_bi_val]
    have h_e1 : (ai_v.val * bj_v.val).natAbs ≤ 3328 * 3328 := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul h_ai h_bj
    have h_e2 : (aj_v.val * bi_v.val).natAbs ≤ 3328 * 3328 := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul h_aj h_bi
    have h_tri := Int.natAbs_add_le (ai_v.val * bj_v.val) (aj_v.val * bi_v.val)
    omega
  have h_sum_o_val : ai_bj_aj_bi.val = ai_bj_p.val + aj_bi_p.val := by
    have h_bnd : (ai_bj_p.val + aj_bi_p.val).natAbs < 2^31 := by
      have : (2 * 3328 * 3328 : Nat) < 2^31 := by decide
      omega
    exact L2_8c.wrapping_add_i32_no_overflow ai_bj_p aj_bi_p h_bnd
  have h_delta_o_bnd : ai_bj_aj_bi.val.natAbs ≤ 2^25 := by
    rw [h_sum_o_val]
    have : (2 * 3328 * 3328 : Nat) ≤ 2^25 := by decide
    omega
  -- ===== Slice reads + writes for `out` =====
  have h_read_old_e : Aeneas.Std.Slice.index_usize out i1 = .ok old_e := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq out i1
      (by rw [h_out_val_len, h_i1_val']; exact h_2i_lt)
    rw [h, h_i1_val']
  set new_e : Std.I32 := Aeneas.Std.I32.wrapping_add old_e ai_bi_aj_bj with hne_def
  have h_new_e_eq : CoreModels.core.num.I32.wrapping_add old_e ai_bi_aj_bj = .ok new_e :=
    L2_8c.cm_wrapping_add_i32_ok_eq old_e ai_bi_aj_bj
  have h_new_e_val : new_e.val = old_e.val + ai_bi_aj_bj.val := by
    have h_bnd : (old_e.val + ai_bi_aj_bj.val).natAbs < 2^31 := by
      have h_tri := Int.natAbs_add_le old_e.val ai_bi_aj_bj.val
      have : (2^30 + 2^25 + 2^25 : Nat) < 2^31 := by decide
      omega
    exact L2_8c.wrapping_add_i32_no_overflow old_e ai_bi_aj_bj h_bnd
  have h_new_e_bnd : new_e.val.natAbs ≤ old_e.val.natAbs + 2^25 := by
    rw [h_new_e_val]
    have h_tri := Int.natAbs_add_le old_e.val ai_bi_aj_bj.val
    omega
  have h_upd_e : Aeneas.Std.Slice.update out i1 new_e = .ok (out.set i1 new_e) := by
    have hT := Aeneas.Std.Slice.update_spec out i1 new_e (by rw [h_out_len, h_i1_val']; exact h_2i_lt)
    obtain ⟨v', h_eq, h_v'⟩ := Aeneas.Std.WP.spec_imp_exists hT
    rw [h_eq, h_v']
  set out1 : Aeneas.Std.Slice Std.I32 := out.set i1 new_e with hout1_def
  have h_out1_len : out1.length = 16 := by simp [hout1_def]; exact h_out_len
  have h_out1_val_len : out1.val.length = 16 := h_out1_len
  have h_old_o_in_out1 : out1.val[i2.val]! = old_o := by
    have h_set_val : out1.val = out.val.set i1.val new_e := by
      simp [hout1_def, Aeneas.Std.Slice.set_val_eq]
    have h_ne : 2 * i.val + 1 ≠ i1.val := by rw [h_i1_val']; omega
    have h_lt : 2 * i.val + 1 < out.val.length := by rw [h_out_val_len]; exact h_2i1_lt
    rw [h_set_val, h_i2_val', hoo_def]
    have h_lt_set : 2 * i.val + 1 < (out.val.set i1.val new_e).length := by
      rw [List.length_set]; exact h_lt
    rw [getElem!_pos (out.val.set i1.val new_e) (2 * i.val + 1) h_lt_set]
    rw [getElem!_pos out.val (2 * i.val + 1) h_lt]
    rw [List.getElem_set_ne (Ne.symm h_ne)]
  have h_read_old_o : Aeneas.Std.Slice.index_usize out1 i2 = .ok old_o := by
    have h := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq out1 i2
      (by rw [h_out1_val_len, h_i2_val']; exact h_2i1_lt)
    rw [h, h_old_o_in_out1]
  set new_o : Std.I32 := Aeneas.Std.I32.wrapping_add old_o ai_bj_aj_bi with hno_def
  have h_new_o_eq : CoreModels.core.num.I32.wrapping_add old_o ai_bj_aj_bi = .ok new_o :=
    L2_8c.cm_wrapping_add_i32_ok_eq old_o ai_bj_aj_bi
  have h_new_o_val : new_o.val = old_o.val + ai_bj_aj_bi.val := by
    have h_bnd : (old_o.val + ai_bj_aj_bi.val).natAbs < 2^31 := by
      have h_tri := Int.natAbs_add_le old_o.val ai_bj_aj_bi.val
      have : (2^30 + 2^25 + 2^25 : Nat) < 2^31 := by decide
      omega
    exact L2_8c.wrapping_add_i32_no_overflow old_o ai_bj_aj_bi h_bnd
  have h_new_o_bnd : new_o.val.natAbs ≤ old_o.val.natAbs + 2^25 := by
    rw [h_new_o_val]
    have h_tri := Int.natAbs_add_le old_o.val ai_bj_aj_bi.val
    omega
  have h_upd_o : Aeneas.Std.Slice.update out1 i2 new_o = .ok (out1.set i2 new_o) := by
    have hT := Aeneas.Std.Slice.update_spec out1 i2 new_o
      (by rw [h_out1_len, h_i2_val']; exact h_2i1_lt)
    obtain ⟨v', h_eq, h_v'⟩ := Aeneas.Std.WP.spec_imp_exists hT
    rw [h_eq, h_v']
  set out2 : Aeneas.Std.Slice Std.I32 := out1.set i2 new_o with hout2_def
  -- ===== Compose monadic body =====
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_use_cache
        a b i out cache = .ok out2 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_use_cache
    simp only [h_i1_eq, h_i2_eq, h_read_ai, h_read_bi, h_read_aj, h_read_bj, h_read_cv,
               h_as_ai, h_as_bi, h_as_aj, h_as_bj, h_as_cv,
               h_ai_bi_eq, h_aj_bj_zeta_eq,
               h_sum_e_eq, h_ai_bj_eq, h_aj_bi_eq, h_sum_o_eq,
               h_read_old_e, h_new_e_eq, h_upd_e,
               h_read_old_o, h_new_o_eq, h_upd_o,
               Aeneas.Std.bind_tc_ok]
  apply triple_of_ok_fc h_body
  -- ===== POST: 7-conjunct =====
  have h_out2_val : out2.val = (out.val.set i1.val new_e).set i2.val new_o := by
    show ((out.set i1 new_e).set i2 new_o).val = _
    rw [Aeneas.Std.Slice.set_val_eq, Aeneas.Std.Slice.set_val_eq]
  have h_out2_len : out2.length = 16 := by
    show ((out.set i1 new_e).set i2 new_o).length = 16
    rw [Aeneas.Std.Slice.set_length, Aeneas.Std.Slice.set_length]; exact h_out_len
  have h_out2_val_len : out2.val.length = 16 := h_out2_len
  have h_out2_at_2i : out2.val[2 * i.val]! = new_e := by
    rw [h_out2_val, ← h_i1_val']
    have h_lt_out : i1.val < out.val.length := by rw [h_out_val_len, h_i1_val']; exact h_2i_lt
    have h_lt1 : i1.val < (out.val.set i1.val new_e).length := by
      rw [List.length_set]; exact h_lt_out
    have h_lt2 : i1.val < ((out.val.set i1.val new_e).set i2.val new_o).length := by
      rw [List.length_set]; exact h_lt1
    rw [getElem!_pos ((out.val.set i1.val new_e).set i2.val new_o) i1.val h_lt2]
    rw [List.getElem_set_ne (by rw [h_i2_val', h_i1_val']; omega)]
    rw [List.getElem_set_self]
  have h_out2_at_2i1 : out2.val[2 * i.val + 1]! = new_o := by
    rw [h_out2_val, ← h_i2_val']
    have h_lt_out : i2.val < out.val.length := by rw [h_out_val_len, h_i2_val']; exact h_2i1_lt
    have h_lt1 : i2.val < (out.val.set i1.val new_e).length := by
      rw [List.length_set]; exact h_lt_out
    have h_lt2 : i2.val < ((out.val.set i1.val new_e).set i2.val new_o).length := by
      rw [List.length_set]; exact h_lt1
    rw [getElem!_pos ((out.val.set i1.val new_e).set i2.val new_o) i2.val h_lt2]
    rw [List.getElem_set_self]
  have h_out2_untouched : ∀ k : Nat, k < 16 → k ≠ 2 * i.val → k ≠ 2 * i.val + 1 →
      out2.val[k]! = out.val[k]! := by
    intro k hk hki hkj
    rw [h_out2_val]
    have h_lt_out : k < out.val.length := by rw [h_out_val_len]; exact hk
    have h_lt1 : k < (out.val.set i1.val new_e).length := by rw [List.length_set]; exact h_lt_out
    have h_lt2 : k < ((out.val.set i1.val new_e).set i2.val new_o).length := by
      rw [List.length_set]; exact h_lt1
    rw [getElem!_pos ((out.val.set i1.val new_e).set i2.val new_o) k h_lt2]
    rw [getElem!_pos out.val k h_lt_out]
    rw [List.getElem_set_ne (by rw [h_i2_val']; omega)]
    rw [List.getElem_set_ne (by rw [h_i1_val']; omega)]
  refine ⟨h_out2_len, h_out2_untouched, ?_, ?_, ?_, ?_⟩
  · rw [h_out2_at_2i]
    rw [hoe_def] at h_new_e_bnd
    exact h_new_e_bnd
  · rw [h_out2_at_2i1]
    rw [hoo_def] at h_new_o_bnd
    exact h_new_o_bnd
  · -- FE eq (even half) with symbolic cache lane.
    rw [h_out2_at_2i, hoe_def]
    apply L2_8d.mont_reduce_even_fe_eq_cache
      (out := out.val[2 * i.val]!) (r := new_e)
      (ai := ai_v) (bi := bi_v) (aj := aj_v) (c := c_v)
    rw [← hoe_def, h_new_e_val, h_sum_e_val, h_ai_bi_val, h_aj_bj_zeta_val]
    push_cast
    ring
  · -- FE eq (odd half) — same as L2.8c.
    rw [h_out2_at_2i1, hoo_def]
    apply L2_8d.mont_reduce_odd_fe_eq_cache
      (out := out.val[2 * i.val + 1]!) (r := new_o)
      (ai := ai_v) (bi := bi_v) (aj := aj_v) (bj := bj_v)
    rw [← hoo_def, h_new_o_val, h_sum_o_val, h_ai_bj_val, h_aj_bi_val]
    push_cast
    ring

set_option maxHeartbeats 16000000 in
/-- L2.8d — `vector.portable.ntt.accumulating_ntt_multiply_fill_cache`:
    cache-filling variant. The impl chains 8
    `accumulating_ntt_multiply_binomials_fill_cache` calls; each
    behaves like the base `_binomials` (per-pair degree-2 polynomial
    multiply mod (X²−ζ²)) but additionally writes the Mont-reduced
    `b[2i+1]·zeta_i` into `cache[i]`.

    POST shape mirrors `accumulating_ntt_multiply_fc` (length + relative
    bound + `ntt_multiply_base_case_post` on the output slice) AND adds
    a cache-side POST: each of the 8 cache slots stores the FE-projected
    `mul_pure rhs[2i+1] zeta_eff_i` and is canonical; lanes 8..15 of
    the cache are preserved from the input.

    Sibling adaptation of L2.8c reusing `L2_8c.*` infrastructure. -/
@[spec]
theorem accumulating_ntt_multiply_fill_cache_fc
    (lhs rhs : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Aeneas.Std.Slice Std.I32)
    (cache : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta0 zeta1 zeta2 zeta3 : Std.I16)
    (h_out_len : out.length = 16)
    (h_lhs : ∀ j : Fin 16, (lhs.elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_rhs : ∀ j : Fin 16, (rhs.elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_zeta0 : zeta0.val.natAbs ≤ 1664)
    (h_zeta1 : zeta1.val.natAbs ≤ 1664)
    (h_zeta2 : zeta2.val.natAbs ≤ 1664)
    (h_zeta3 : zeta3.val.natAbs ≤ 1664)
    (h_out_bnd : ∀ k : Fin 16, (out.val[k.val]!).val.natAbs ≤ 2^30) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_fill_cache
      lhs rhs out cache zeta0 zeta1 zeta2 zeta3
    ⦃ ⇓ p => ⌜ p.1.length = 16 ∧
              (∀ k : Fin 16, (p.1.val[k.val]!).val.natAbs
                              ≤ (out.val[k.val]!).val.natAbs + 2^25) ∧
              ntt_multiply_base_case_post lhs rhs
                zeta0 zeta1 zeta2 zeta3 out p.1 ∧
              Spec.ntt_multiply_cache_post rhs
                zeta0 zeta1 zeta2 zeta3 p.2 ∧
              (∀ k : Nat, k < 16 → 8 ≤ k →
                p.2.elements.val[k]! = cache.elements.val[k]!) ⌝ ⦄ := by
  have h_zeta_within (z : Std.I16) (hz : z.val.natAbs ≤ 1664) :
      z.val.natAbs ≤ 2^15 - 1 := by omega
  have h_n0_val := L2_8c.wrapping_neg_val_eq zeta0 (h_zeta_within _ h_zeta0)
  have h_n1_val := L2_8c.wrapping_neg_val_eq zeta1 (h_zeta_within _ h_zeta1)
  have h_n2_val := L2_8c.wrapping_neg_val_eq zeta2 (h_zeta_within _ h_zeta2)
  have h_n3_val := L2_8c.wrapping_neg_val_eq zeta3 (h_zeta_within _ h_zeta3)
  set nzeta0 : Std.I16 := Aeneas.Std.I16.wrapping_sub (0#i16) zeta0 with hn0_def
  set nzeta1 : Std.I16 := Aeneas.Std.I16.wrapping_sub (0#i16) zeta1 with hn1_def
  set nzeta2 : Std.I16 := Aeneas.Std.I16.wrapping_sub (0#i16) zeta2 with hn2_def
  set nzeta3 : Std.I16 := Aeneas.Std.I16.wrapping_sub (0#i16) zeta3 with hn3_def
  have h_nz0_bnd : nzeta0.val.natAbs ≤ 1664 := by rw [h_n0_val]; omega
  have h_nz1_bnd : nzeta1.val.natAbs ≤ 1664 := by rw [h_n1_val]; omega
  have h_nz2_bnd : nzeta2.val.natAbs ≤ 1664 := by rw [h_n2_val]; omega
  have h_nz3_bnd : nzeta3.val.natAbs ≤ 1664 := by rw [h_n3_val]; omega
  have h_n0_fe : lift_fe_mont nzeta0
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta0) :=
    L2_8c.lift_fe_mont_neg_pure_eq zeta0 nzeta0 (h_zeta_within _ h_zeta0) h_n0_val
  have h_n1_fe : lift_fe_mont nzeta1
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta1) :=
    L2_8c.lift_fe_mont_neg_pure_eq zeta1 nzeta1 (h_zeta_within _ h_zeta1) h_n1_val
  have h_n2_fe : lift_fe_mont nzeta2
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta2) :=
    L2_8c.lift_fe_mont_neg_pure_eq zeta2 nzeta2 (h_zeta_within _ h_zeta2) h_n2_val
  have h_n3_fe : lift_fe_mont nzeta3
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta3) :=
    L2_8c.lift_fe_mont_neg_pure_eq zeta3 nzeta3 (h_zeta_within _ h_zeta3) h_n3_val
  have h_wn0 : core.num.I16.wrapping_neg zeta0 = .ok nzeta0 :=
    L2_8c.cm_wrapping_neg_i16_ok_eq zeta0
  have h_wn1 : core.num.I16.wrapping_neg zeta1 = .ok nzeta1 :=
    L2_8c.cm_wrapping_neg_i16_ok_eq zeta1
  have h_wn2 : core.num.I16.wrapping_neg zeta2 = .ok nzeta2 :=
    L2_8c.cm_wrapping_neg_i16_ok_eq zeta2
  have h_wn3 : core.num.I16.wrapping_neg zeta3 = .ok nzeta3 :=
    L2_8c.cm_wrapping_neg_i16_ok_eq zeta3
  have h_cz0 : libcrux_secrets.traits.Classify.Blanket.classify zeta0 = .ok zeta0 :=
    L2_8c.classify_ok_eq zeta0
  have h_cnz0 : libcrux_secrets.traits.Classify.Blanket.classify nzeta0 = .ok nzeta0 :=
    L2_8c.classify_ok_eq nzeta0
  have h_cz1 : libcrux_secrets.traits.Classify.Blanket.classify zeta1 = .ok zeta1 :=
    L2_8c.classify_ok_eq zeta1
  have h_cnz1 : libcrux_secrets.traits.Classify.Blanket.classify nzeta1 = .ok nzeta1 :=
    L2_8c.classify_ok_eq nzeta1
  have h_cz2 : libcrux_secrets.traits.Classify.Blanket.classify zeta2 = .ok zeta2 :=
    L2_8c.classify_ok_eq zeta2
  have h_cnz2 : libcrux_secrets.traits.Classify.Blanket.classify nzeta2 = .ok nzeta2 :=
    L2_8c.classify_ok_eq nzeta2
  have h_cz3 : libcrux_secrets.traits.Classify.Blanket.classify zeta3 = .ok zeta3 :=
    L2_8c.classify_ok_eq zeta3
  have h_cnz3 : libcrux_secrets.traits.Classify.Blanket.classify nzeta3 = .ok nzeta3 :=
    L2_8c.classify_ok_eq nzeta3
  have h_out_bnd_universal : ∀ k : Fin 16, (out.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 := by
    intro k; have := h_out_bnd k; omega
  have h_cache_len : cache.elements.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length cache
  -- ===== 8 chained calls — each returns (r{i}, cache_out{i}) =====
  -- Call 0: pair 0 with zeta0 (touches lanes 0, 1; writes cache[0]).
  obtain ⟨p0, h_p0_eq, h_r0_len, h_r0_unc, h_r0_bnd_e, h_r0_bnd_o,
          h_r0_fe_e, h_r0_fe_o, h_c0_canon, h_c0_fe, h_c0_unc⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_fill_cache_fc lhs rhs zeta0 0#usize out cache
        (by decide) h_out_len h_lhs h_rhs h_zeta0 h_out_bnd_universal)
  set r0 : Aeneas.Std.Slice Std.I32 := p0.1 with hr0_def
  set cache0 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector := p0.2
    with hc0_def
  have h_r0_at_even : (r0.val[0]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (0#usize : Std.Usize).val : Nat) = 0 := by decide
    have h_b := h_r0_bnd_e
    rw [h_eq] at h_b
    have h_out_le := h_out_bnd ⟨0, by decide⟩
    simp only at h_out_le; omega
  have h_r0_at_odd : (r0.val[1]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (0#usize : Std.Usize).val + 1 : Nat) = 1 := by decide
    have h_b := h_r0_bnd_o
    rw [h_eq] at h_b
    have h_out_le := h_out_bnd ⟨1, by decide⟩
    simp only at h_out_le; omega
  have h_r0_unc' : ∀ k : Nat, k < 16 → k ≠ 0 → k ≠ 1 →
      r0.val[k]! = out.val[k]! := by
    intro k hk hke hko
    have h_eq_e : (2 * (0#usize : Std.Usize).val : Nat) = 0 := by decide
    have h_eq_o : (2 * (0#usize : Std.Usize).val + 1 : Nat) = 1 := by decide
    apply h_r0_unc k hk
    · rw [h_eq_e]; exact hke
    · rw [h_eq_o]; exact hko
  have h_c0_unc' : ∀ k : Nat, k < 16 → k ≠ 0 →
      cache0.elements.val[k]! = cache.elements.val[k]! := by
    intro k hk hki
    apply h_c0_unc k hk
    show k ≠ (0#usize : Std.Usize).val; rw [show (0#usize : Std.Usize).val = 0 from rfl]; exact hki
  have h_r0_bnd_universal : ∀ k : Fin 16, (r0.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step out r0 0 (by decide) h_out_bnd_universal
      h_r0_unc' h_r0_at_even h_r0_at_odd

  -- Call 1: pair 1 with nzeta0 (touches lanes 2, 3; writes cache[1]).
  obtain ⟨p1, h_p1_eq, h_r1_len, h_r1_unc, h_r1_bnd_e, h_r1_bnd_o,
          h_r1_fe_e, h_r1_fe_o, h_c1_canon, h_c1_fe, h_c1_unc⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_fill_cache_fc lhs rhs nzeta0 1#usize r0 cache0
        (by decide) h_r0_len h_lhs h_rhs h_nz0_bnd h_r0_bnd_universal)
  set r1 : Aeneas.Std.Slice Std.I32 := p1.1 with hr1_def
  set cache1 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector := p1.2
    with hc1_def
  have h_r1_at_even : (r1.val[2]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (1#usize : Std.Usize).val : Nat) = 2 := by decide
    have h_b := h_r1_bnd_e
    rw [h_eq] at h_b
    have h_r0_eq2 : r0.val[2]! = out.val[2]! := h_r0_unc' 2 (by decide) (by decide) (by decide)
    rw [h_r0_eq2] at h_b
    have h_out_le := h_out_bnd ⟨2, by decide⟩
    simp only at h_out_le; omega
  have h_r1_at_odd : (r1.val[3]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (1#usize : Std.Usize).val + 1 : Nat) = 3 := by decide
    have h_b := h_r1_bnd_o
    rw [h_eq] at h_b
    have h_r0_eq3 : r0.val[3]! = out.val[3]! := h_r0_unc' 3 (by decide) (by decide) (by decide)
    rw [h_r0_eq3] at h_b
    have h_out_le := h_out_bnd ⟨3, by decide⟩
    simp only at h_out_le; omega
  have h_r1_unc' : ∀ k : Nat, k < 16 → k ≠ 2 → k ≠ 3 →
      r1.val[k]! = r0.val[k]! := by
    intro k hk hke hko
    have h_eq_e : (2 * (1#usize : Std.Usize).val : Nat) = 2 := by decide
    have h_eq_o : (2 * (1#usize : Std.Usize).val + 1 : Nat) = 3 := by decide
    apply h_r1_unc k hk
    · rw [h_eq_e]; exact hke
    · rw [h_eq_o]; exact hko
  have h_c1_unc' : ∀ k : Nat, k < 16 → k ≠ 1 →
      cache1.elements.val[k]! = cache0.elements.val[k]! := by
    intro k hk hki
    apply h_c1_unc k hk
    show k ≠ (1#usize : Std.Usize).val; rw [show (1#usize : Std.Usize).val = 1 from rfl]; exact hki
  have h_r1_bnd_universal : ∀ k : Fin 16, (r1.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r0 r1 1 (by decide) h_r0_bnd_universal
      h_r1_unc' h_r1_at_even h_r1_at_odd

  -- Call 2: pair 2 with zeta1 (touches lanes 4, 5; writes cache[2]).
  obtain ⟨p2, h_p2_eq, h_r2_len, h_r2_unc, h_r2_bnd_e, h_r2_bnd_o,
          h_r2_fe_e, h_r2_fe_o, h_c2_canon, h_c2_fe, h_c2_unc⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_fill_cache_fc lhs rhs zeta1 2#usize r1 cache1
        (by decide) h_r1_len h_lhs h_rhs h_zeta1 h_r1_bnd_universal)
  set r2 : Aeneas.Std.Slice Std.I32 := p2.1 with hr2_def
  set cache2 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector := p2.2
    with hc2_def
  have h_r2_at_even : (r2.val[4]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (2#usize : Std.Usize).val : Nat) = 4 := by decide
    have h_b := h_r2_bnd_e
    rw [h_eq] at h_b
    have h_r1_eq4 : r1.val[4]! = out.val[4]! := by
      rw [h_r1_unc' 4 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 4 (by decide) (by decide) (by decide)]
    rw [h_r1_eq4] at h_b
    have h_out_le := h_out_bnd ⟨4, by decide⟩
    simp only at h_out_le; omega
  have h_r2_at_odd : (r2.val[5]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (2#usize : Std.Usize).val + 1 : Nat) = 5 := by decide
    have h_b := h_r2_bnd_o
    rw [h_eq] at h_b
    have h_r1_eq5 : r1.val[5]! = out.val[5]! := by
      rw [h_r1_unc' 5 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 5 (by decide) (by decide) (by decide)]
    rw [h_r1_eq5] at h_b
    have h_out_le := h_out_bnd ⟨5, by decide⟩
    simp only at h_out_le; omega
  have h_r2_unc' : ∀ k : Nat, k < 16 → k ≠ 4 → k ≠ 5 →
      r2.val[k]! = r1.val[k]! := by
    intro k hk hke hko
    have h_eq_e : (2 * (2#usize : Std.Usize).val : Nat) = 4 := by decide
    have h_eq_o : (2 * (2#usize : Std.Usize).val + 1 : Nat) = 5 := by decide
    apply h_r2_unc k hk
    · rw [h_eq_e]; exact hke
    · rw [h_eq_o]; exact hko
  have h_c2_unc' : ∀ k : Nat, k < 16 → k ≠ 2 →
      cache2.elements.val[k]! = cache1.elements.val[k]! := by
    intro k hk hki
    apply h_c2_unc k hk
    show k ≠ (2#usize : Std.Usize).val; rw [show (2#usize : Std.Usize).val = 2 from rfl]; exact hki
  have h_r2_bnd_universal : ∀ k : Fin 16, (r2.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r1 r2 2 (by decide) h_r1_bnd_universal
      h_r2_unc' h_r2_at_even h_r2_at_odd

  -- Call 3: pair 3 with nzeta1 (touches lanes 6, 7; writes cache[3]).
  obtain ⟨p3, h_p3_eq, h_r3_len, h_r3_unc, h_r3_bnd_e, h_r3_bnd_o,
          h_r3_fe_e, h_r3_fe_o, h_c3_canon, h_c3_fe, h_c3_unc⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_fill_cache_fc lhs rhs nzeta1 3#usize r2 cache2
        (by decide) h_r2_len h_lhs h_rhs h_nz1_bnd h_r2_bnd_universal)
  set r3 : Aeneas.Std.Slice Std.I32 := p3.1 with hr3_def
  set cache3 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector := p3.2
    with hc3_def
  have h_r3_at_even : (r3.val[6]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (3#usize : Std.Usize).val : Nat) = 6 := by decide
    have h_b := h_r3_bnd_e
    rw [h_eq] at h_b
    have h_r2_eq6 : r2.val[6]! = out.val[6]! := by
      rw [h_r2_unc' 6 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 6 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 6 (by decide) (by decide) (by decide)]
    rw [h_r2_eq6] at h_b
    have h_out_le := h_out_bnd ⟨6, by decide⟩
    simp only at h_out_le; omega
  have h_r3_at_odd : (r3.val[7]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (3#usize : Std.Usize).val + 1 : Nat) = 7 := by decide
    have h_b := h_r3_bnd_o
    rw [h_eq] at h_b
    have h_r2_eq7 : r2.val[7]! = out.val[7]! := by
      rw [h_r2_unc' 7 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 7 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 7 (by decide) (by decide) (by decide)]
    rw [h_r2_eq7] at h_b
    have h_out_le := h_out_bnd ⟨7, by decide⟩
    simp only at h_out_le; omega
  have h_r3_unc' : ∀ k : Nat, k < 16 → k ≠ 6 → k ≠ 7 →
      r3.val[k]! = r2.val[k]! := by
    intro k hk hke hko
    have h_eq_e : (2 * (3#usize : Std.Usize).val : Nat) = 6 := by decide
    have h_eq_o : (2 * (3#usize : Std.Usize).val + 1 : Nat) = 7 := by decide
    apply h_r3_unc k hk
    · rw [h_eq_e]; exact hke
    · rw [h_eq_o]; exact hko
  have h_c3_unc' : ∀ k : Nat, k < 16 → k ≠ 3 →
      cache3.elements.val[k]! = cache2.elements.val[k]! := by
    intro k hk hki
    apply h_c3_unc k hk
    show k ≠ (3#usize : Std.Usize).val; rw [show (3#usize : Std.Usize).val = 3 from rfl]; exact hki
  have h_r3_bnd_universal : ∀ k : Fin 16, (r3.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r2 r3 3 (by decide) h_r2_bnd_universal
      h_r3_unc' h_r3_at_even h_r3_at_odd

  -- Call 4: pair 4 with zeta2 (touches lanes 8, 9; writes cache[4]).
  obtain ⟨p4, h_p4_eq, h_r4_len, h_r4_unc, h_r4_bnd_e, h_r4_bnd_o,
          h_r4_fe_e, h_r4_fe_o, h_c4_canon, h_c4_fe, h_c4_unc⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_fill_cache_fc lhs rhs zeta2 4#usize r3 cache3
        (by decide) h_r3_len h_lhs h_rhs h_zeta2 h_r3_bnd_universal)
  set r4 : Aeneas.Std.Slice Std.I32 := p4.1 with hr4_def
  set cache4 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector := p4.2
    with hc4_def
  have h_r4_at_even : (r4.val[8]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (4#usize : Std.Usize).val : Nat) = 8 := by decide
    have h_b := h_r4_bnd_e
    rw [h_eq] at h_b
    have h_r3_eq8 : r3.val[8]! = out.val[8]! := by
      rw [h_r3_unc' 8 (by decide) (by decide) (by decide)]
      rw [h_r2_unc' 8 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 8 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 8 (by decide) (by decide) (by decide)]
    rw [h_r3_eq8] at h_b
    have h_out_le := h_out_bnd ⟨8, by decide⟩
    simp only at h_out_le; omega
  have h_r4_at_odd : (r4.val[9]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (4#usize : Std.Usize).val + 1 : Nat) = 9 := by decide
    have h_b := h_r4_bnd_o
    rw [h_eq] at h_b
    have h_r3_eq9 : r3.val[9]! = out.val[9]! := by
      rw [h_r3_unc' 9 (by decide) (by decide) (by decide)]
      rw [h_r2_unc' 9 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 9 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 9 (by decide) (by decide) (by decide)]
    rw [h_r3_eq9] at h_b
    have h_out_le := h_out_bnd ⟨9, by decide⟩
    simp only at h_out_le; omega
  have h_r4_unc' : ∀ k : Nat, k < 16 → k ≠ 8 → k ≠ 9 →
      r4.val[k]! = r3.val[k]! := by
    intro k hk hke hko
    have h_eq_e : (2 * (4#usize : Std.Usize).val : Nat) = 8 := by decide
    have h_eq_o : (2 * (4#usize : Std.Usize).val + 1 : Nat) = 9 := by decide
    apply h_r4_unc k hk
    · rw [h_eq_e]; exact hke
    · rw [h_eq_o]; exact hko
  have h_c4_unc' : ∀ k : Nat, k < 16 → k ≠ 4 →
      cache4.elements.val[k]! = cache3.elements.val[k]! := by
    intro k hk hki
    apply h_c4_unc k hk
    show k ≠ (4#usize : Std.Usize).val; rw [show (4#usize : Std.Usize).val = 4 from rfl]; exact hki
  have h_r4_bnd_universal : ∀ k : Fin 16, (r4.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r3 r4 4 (by decide) h_r3_bnd_universal
      h_r4_unc' h_r4_at_even h_r4_at_odd

  -- Call 5: pair 5 with nzeta2 (touches lanes 10, 11; writes cache[5]).
  obtain ⟨p5, h_p5_eq, h_r5_len, h_r5_unc, h_r5_bnd_e, h_r5_bnd_o,
          h_r5_fe_e, h_r5_fe_o, h_c5_canon, h_c5_fe, h_c5_unc⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_fill_cache_fc lhs rhs nzeta2 5#usize r4 cache4
        (by decide) h_r4_len h_lhs h_rhs h_nz2_bnd h_r4_bnd_universal)
  set r5 : Aeneas.Std.Slice Std.I32 := p5.1 with hr5_def
  set cache5 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector := p5.2
    with hc5_def
  have h_r5_at_even : (r5.val[10]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (5#usize : Std.Usize).val : Nat) = 10 := by decide
    have h_b := h_r5_bnd_e
    rw [h_eq] at h_b
    have h_r4_eq10 : r4.val[10]! = out.val[10]! := by
      rw [h_r4_unc' 10 (by decide) (by decide) (by decide)]
      rw [h_r3_unc' 10 (by decide) (by decide) (by decide)]
      rw [h_r2_unc' 10 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 10 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 10 (by decide) (by decide) (by decide)]
    rw [h_r4_eq10] at h_b
    have h_out_le := h_out_bnd ⟨10, by decide⟩
    simp only at h_out_le; omega
  have h_r5_at_odd : (r5.val[11]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (5#usize : Std.Usize).val + 1 : Nat) = 11 := by decide
    have h_b := h_r5_bnd_o
    rw [h_eq] at h_b
    have h_r4_eq11 : r4.val[11]! = out.val[11]! := by
      rw [h_r4_unc' 11 (by decide) (by decide) (by decide)]
      rw [h_r3_unc' 11 (by decide) (by decide) (by decide)]
      rw [h_r2_unc' 11 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 11 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 11 (by decide) (by decide) (by decide)]
    rw [h_r4_eq11] at h_b
    have h_out_le := h_out_bnd ⟨11, by decide⟩
    simp only at h_out_le; omega
  have h_r5_unc' : ∀ k : Nat, k < 16 → k ≠ 10 → k ≠ 11 →
      r5.val[k]! = r4.val[k]! := by
    intro k hk hke hko
    have h_eq_e : (2 * (5#usize : Std.Usize).val : Nat) = 10 := by decide
    have h_eq_o : (2 * (5#usize : Std.Usize).val + 1 : Nat) = 11 := by decide
    apply h_r5_unc k hk
    · rw [h_eq_e]; exact hke
    · rw [h_eq_o]; exact hko
  have h_c5_unc' : ∀ k : Nat, k < 16 → k ≠ 5 →
      cache5.elements.val[k]! = cache4.elements.val[k]! := by
    intro k hk hki
    apply h_c5_unc k hk
    show k ≠ (5#usize : Std.Usize).val; rw [show (5#usize : Std.Usize).val = 5 from rfl]; exact hki
  have h_r5_bnd_universal : ∀ k : Fin 16, (r5.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r4 r5 5 (by decide) h_r4_bnd_universal
      h_r5_unc' h_r5_at_even h_r5_at_odd

  -- Call 6: pair 6 with zeta3 (touches lanes 12, 13; writes cache[6]).
  obtain ⟨p6, h_p6_eq, h_r6_len, h_r6_unc, h_r6_bnd_e, h_r6_bnd_o,
          h_r6_fe_e, h_r6_fe_o, h_c6_canon, h_c6_fe, h_c6_unc⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_fill_cache_fc lhs rhs zeta3 6#usize r5 cache5
        (by decide) h_r5_len h_lhs h_rhs h_zeta3 h_r5_bnd_universal)
  set r6 : Aeneas.Std.Slice Std.I32 := p6.1 with hr6_def
  set cache6 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector := p6.2
    with hc6_def
  have h_r6_at_even : (r6.val[12]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (6#usize : Std.Usize).val : Nat) = 12 := by decide
    have h_b := h_r6_bnd_e
    rw [h_eq] at h_b
    have h_r5_eq12 : r5.val[12]! = out.val[12]! := by
      rw [h_r5_unc' 12 (by decide) (by decide) (by decide)]
      rw [h_r4_unc' 12 (by decide) (by decide) (by decide)]
      rw [h_r3_unc' 12 (by decide) (by decide) (by decide)]
      rw [h_r2_unc' 12 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 12 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 12 (by decide) (by decide) (by decide)]
    rw [h_r5_eq12] at h_b
    have h_out_le := h_out_bnd ⟨12, by decide⟩
    simp only at h_out_le; omega
  have h_r6_at_odd : (r6.val[13]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (6#usize : Std.Usize).val + 1 : Nat) = 13 := by decide
    have h_b := h_r6_bnd_o
    rw [h_eq] at h_b
    have h_r5_eq13 : r5.val[13]! = out.val[13]! := by
      rw [h_r5_unc' 13 (by decide) (by decide) (by decide)]
      rw [h_r4_unc' 13 (by decide) (by decide) (by decide)]
      rw [h_r3_unc' 13 (by decide) (by decide) (by decide)]
      rw [h_r2_unc' 13 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 13 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 13 (by decide) (by decide) (by decide)]
    rw [h_r5_eq13] at h_b
    have h_out_le := h_out_bnd ⟨13, by decide⟩
    simp only at h_out_le; omega
  have h_r6_unc' : ∀ k : Nat, k < 16 → k ≠ 12 → k ≠ 13 →
      r6.val[k]! = r5.val[k]! := by
    intro k hk hke hko
    have h_eq_e : (2 * (6#usize : Std.Usize).val : Nat) = 12 := by decide
    have h_eq_o : (2 * (6#usize : Std.Usize).val + 1 : Nat) = 13 := by decide
    apply h_r6_unc k hk
    · rw [h_eq_e]; exact hke
    · rw [h_eq_o]; exact hko
  have h_c6_unc' : ∀ k : Nat, k < 16 → k ≠ 6 →
      cache6.elements.val[k]! = cache5.elements.val[k]! := by
    intro k hk hki
    apply h_c6_unc k hk
    show k ≠ (6#usize : Std.Usize).val; rw [show (6#usize : Std.Usize).val = 6 from rfl]; exact hki
  have h_r6_bnd_universal : ∀ k : Fin 16, (r6.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r5 r6 6 (by decide) h_r5_bnd_universal
      h_r6_unc' h_r6_at_even h_r6_at_odd

  -- Call 7: pair 7 with nzeta3 (touches lanes 14, 15; writes cache[7]).
  obtain ⟨p7, h_p7_eq, h_r7_len, h_r7_unc, h_r7_bnd_e, h_r7_bnd_o,
          h_r7_fe_e, h_r7_fe_o, h_c7_canon, h_c7_fe, h_c7_unc⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_fill_cache_fc lhs rhs nzeta3 7#usize r6 cache6
        (by decide) h_r6_len h_lhs h_rhs h_nz3_bnd h_r6_bnd_universal)
  set r7 : Aeneas.Std.Slice Std.I32 := p7.1 with hr7_def
  set cache7 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector := p7.2
    with hc7_def
  have h_r7_at_even : (r7.val[14]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (7#usize : Std.Usize).val : Nat) = 14 := by decide
    have h_b := h_r7_bnd_e
    rw [h_eq] at h_b
    have h_r6_eq14 : r6.val[14]! = out.val[14]! := by
      rw [h_r6_unc' 14 (by decide) (by decide) (by decide)]
      rw [h_r5_unc' 14 (by decide) (by decide) (by decide)]
      rw [h_r4_unc' 14 (by decide) (by decide) (by decide)]
      rw [h_r3_unc' 14 (by decide) (by decide) (by decide)]
      rw [h_r2_unc' 14 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 14 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 14 (by decide) (by decide) (by decide)]
    rw [h_r6_eq14] at h_b
    have h_out_le := h_out_bnd ⟨14, by decide⟩
    simp only at h_out_le; omega
  have h_r7_at_odd : (r7.val[15]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (7#usize : Std.Usize).val + 1 : Nat) = 15 := by decide
    have h_b := h_r7_bnd_o
    rw [h_eq] at h_b
    have h_r6_eq15 : r6.val[15]! = out.val[15]! := by
      rw [h_r6_unc' 15 (by decide) (by decide) (by decide)]
      rw [h_r5_unc' 15 (by decide) (by decide) (by decide)]
      rw [h_r4_unc' 15 (by decide) (by decide) (by decide)]
      rw [h_r3_unc' 15 (by decide) (by decide) (by decide)]
      rw [h_r2_unc' 15 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 15 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 15 (by decide) (by decide) (by decide)]
    rw [h_r6_eq15] at h_b
    have h_out_le := h_out_bnd ⟨15, by decide⟩
    simp only at h_out_le; omega
  have h_r7_unc' : ∀ k : Nat, k < 16 → k ≠ 14 → k ≠ 15 →
      r7.val[k]! = r6.val[k]! := by
    intro k hk hke hko
    have h_eq_e : (2 * (7#usize : Std.Usize).val : Nat) = 14 := by decide
    have h_eq_o : (2 * (7#usize : Std.Usize).val + 1 : Nat) = 15 := by decide
    apply h_r7_unc k hk
    · rw [h_eq_e]; exact hke
    · rw [h_eq_o]; exact hko
  have h_c7_unc' : ∀ k : Nat, k < 16 → k ≠ 7 →
      cache7.elements.val[k]! = cache6.elements.val[k]! := by
    intro k hk hki
    apply h_c7_unc k hk
    show k ≠ (7#usize : Std.Usize).val; rw [show (7#usize : Std.Usize).val = 7 from rfl]; exact hki

  -- Compose the monadic body.
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_fill_cache
        lhs rhs out cache zeta0 zeta1 zeta2 zeta3 = .ok (r7, cache7) := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_fill_cache
    -- The result of each call is `pK = (rK, cacheK)`. The impl binds these as
    -- `let (outK, cacheK) ← ...`, which expects a destructured pattern.
    -- Convert the .ok pK into the destructured form via pair eta.
    have h_p0_eq' :
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs zeta0 0#usize out cache = .ok (r0, cache0) := by
      rw [h_p0_eq]
    have h_p1_eq' :
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs nzeta0 1#usize r0 cache0 = .ok (r1, cache1) := by
      rw [h_p1_eq]
    have h_p2_eq' :
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs zeta1 2#usize r1 cache1 = .ok (r2, cache2) := by
      rw [h_p2_eq]
    have h_p3_eq' :
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs nzeta1 3#usize r2 cache2 = .ok (r3, cache3) := by
      rw [h_p3_eq]
    have h_p4_eq' :
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs zeta2 4#usize r3 cache3 = .ok (r4, cache4) := by
      rw [h_p4_eq]
    have h_p5_eq' :
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs nzeta2 5#usize r4 cache4 = .ok (r5, cache5) := by
      rw [h_p5_eq]
    have h_p6_eq' :
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs zeta3 6#usize r5 cache5 = .ok (r6, cache6) := by
      rw [h_p6_eq]
    have h_p7_eq' :
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs nzeta3 7#usize r6 cache6 = .ok (r7, cache7) := by
      rw [h_p7_eq]
    rw [h_wn0]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_wn1]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_wn2]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_wn3]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_cz0]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_p0_eq']
    simp only [Aeneas.Std.bind_tc_ok]
    change (do
      let i1 ← libcrux_secrets.traits.Classify.Blanket.classify nzeta0
      let (out2, cache2) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i1 1#usize r0 cache0
      let i2 ← libcrux_secrets.traits.Classify.Blanket.classify zeta1
      let (out3, cache3) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i2 2#usize out2 cache2
      let i3 ← libcrux_secrets.traits.Classify.Blanket.classify nzeta1
      let (out4, cache4) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i3 3#usize out3 cache3
      let i4 ← libcrux_secrets.traits.Classify.Blanket.classify zeta2
      let (out5, cache5) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i4 4#usize out4 cache4
      let i5 ← libcrux_secrets.traits.Classify.Blanket.classify nzeta2
      let (out6, cache6) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i5 5#usize out5 cache5
      let i6 ← libcrux_secrets.traits.Classify.Blanket.classify zeta3
      let (out7, cache7) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i6 6#usize out6 cache6
      let i7 ← libcrux_secrets.traits.Classify.Blanket.classify nzeta3
      libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
        lhs rhs i7 7#usize out7 cache7) = .ok (r7, cache7)
    rw [h_cnz0]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_p1_eq']
    simp only [Aeneas.Std.bind_tc_ok]
    change (do
      let i2 ← libcrux_secrets.traits.Classify.Blanket.classify zeta1
      let (out3, cache3) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i2 2#usize r1 cache1
      let i3 ← libcrux_secrets.traits.Classify.Blanket.classify nzeta1
      let (out4, cache4) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i3 3#usize out3 cache3
      let i4 ← libcrux_secrets.traits.Classify.Blanket.classify zeta2
      let (out5, cache5) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i4 4#usize out4 cache4
      let i5 ← libcrux_secrets.traits.Classify.Blanket.classify nzeta2
      let (out6, cache6) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i5 5#usize out5 cache5
      let i6 ← libcrux_secrets.traits.Classify.Blanket.classify zeta3
      let (out7, cache7) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i6 6#usize out6 cache6
      let i7 ← libcrux_secrets.traits.Classify.Blanket.classify nzeta3
      libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
        lhs rhs i7 7#usize out7 cache7) = .ok (r7, cache7)
    rw [h_cz1]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_p2_eq']
    simp only [Aeneas.Std.bind_tc_ok]
    change (do
      let i3 ← libcrux_secrets.traits.Classify.Blanket.classify nzeta1
      let (out4, cache4) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i3 3#usize r2 cache2
      let i4 ← libcrux_secrets.traits.Classify.Blanket.classify zeta2
      let (out5, cache5) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i4 4#usize out4 cache4
      let i5 ← libcrux_secrets.traits.Classify.Blanket.classify nzeta2
      let (out6, cache6) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i5 5#usize out5 cache5
      let i6 ← libcrux_secrets.traits.Classify.Blanket.classify zeta3
      let (out7, cache7) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i6 6#usize out6 cache6
      let i7 ← libcrux_secrets.traits.Classify.Blanket.classify nzeta3
      libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
        lhs rhs i7 7#usize out7 cache7) = .ok (r7, cache7)
    rw [h_cnz1]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_p3_eq']
    simp only [Aeneas.Std.bind_tc_ok]
    change (do
      let i4 ← libcrux_secrets.traits.Classify.Blanket.classify zeta2
      let (out5, cache5) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i4 4#usize r3 cache3
      let i5 ← libcrux_secrets.traits.Classify.Blanket.classify nzeta2
      let (out6, cache6) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i5 5#usize out5 cache5
      let i6 ← libcrux_secrets.traits.Classify.Blanket.classify zeta3
      let (out7, cache7) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i6 6#usize out6 cache6
      let i7 ← libcrux_secrets.traits.Classify.Blanket.classify nzeta3
      libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
        lhs rhs i7 7#usize out7 cache7) = .ok (r7, cache7)
    rw [h_cz2]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_p4_eq']
    simp only [Aeneas.Std.bind_tc_ok]
    change (do
      let i5 ← libcrux_secrets.traits.Classify.Blanket.classify nzeta2
      let (out6, cache6) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i5 5#usize r4 cache4
      let i6 ← libcrux_secrets.traits.Classify.Blanket.classify zeta3
      let (out7, cache7) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i6 6#usize out6 cache6
      let i7 ← libcrux_secrets.traits.Classify.Blanket.classify nzeta3
      libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
        lhs rhs i7 7#usize out7 cache7) = .ok (r7, cache7)
    rw [h_cnz2]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_p5_eq']
    simp only [Aeneas.Std.bind_tc_ok]
    change (do
      let i6 ← libcrux_secrets.traits.Classify.Blanket.classify zeta3
      let (out7, cache7) ←
        libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
          lhs rhs i6 6#usize r5 cache5
      let i7 ← libcrux_secrets.traits.Classify.Blanket.classify nzeta3
      libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_binomials_fill_cache
        lhs rhs i7 7#usize out7 cache7) = .ok (r7, cache7)
    rw [h_cz3]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_p6_eq']
    simp only [Aeneas.Std.bind_tc_ok]
    rw [h_cnz3]; simp only [Aeneas.Std.bind_tc_ok]
    exact h_p7_eq'
  apply triple_of_ok_fc h_body
  -- ===== POST: 5-conjunct =====
  refine ⟨h_r7_len, ?_, ?_, ?_, ?_⟩
  · -- Relative bound: ∀ k, r7.val[k]!.natAbs ≤ out.val[k]!.natAbs + 2^25.
    intro k
    rcases k with ⟨k, hk⟩
    interval_cases k
    · have h_r7_at_0 : r7.val[0]! = r0.val[0]! := by
        rw [h_r7_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 0 (by decide) (by decide) (by decide)]
      rw [h_r7_at_0]
      have h_eq : (2 * (0#usize : Std.Usize).val : Nat) = 0 := by decide
      have h_b := h_r0_bnd_e
      rw [h_eq] at h_b
      exact h_b
    · have h_r7_at_1 : r7.val[1]! = r0.val[1]! := by
        rw [h_r7_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 1 (by decide) (by decide) (by decide)]
      rw [h_r7_at_1]
      have h_eq : (2 * (0#usize : Std.Usize).val + 1 : Nat) = 1 := by decide
      have h_b := h_r0_bnd_o
      rw [h_eq] at h_b
      exact h_b
    · have h_r7_at_2 : r7.val[2]! = r1.val[2]! := by
        rw [h_r7_unc' 2 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 2 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 2 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 2 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 2 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 2 (by decide) (by decide) (by decide)]
      rw [h_r7_at_2]
      have h_eq : (2 * (1#usize : Std.Usize).val : Nat) = 2 := by decide
      have h_b := h_r1_bnd_e
      rw [h_eq] at h_b
      have h_r0_at_2 : r0.val[2]! = out.val[2]! := by
        rw [h_r0_unc' 2 (by decide) (by decide) (by decide)]
      rw [h_r0_at_2] at h_b
      exact h_b
    · have h_r7_at_3 : r7.val[3]! = r1.val[3]! := by
        rw [h_r7_unc' 3 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 3 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 3 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 3 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 3 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 3 (by decide) (by decide) (by decide)]
      rw [h_r7_at_3]
      have h_eq : (2 * (1#usize : Std.Usize).val + 1 : Nat) = 3 := by decide
      have h_b := h_r1_bnd_o
      rw [h_eq] at h_b
      have h_r0_at_3 : r0.val[3]! = out.val[3]! := by
        rw [h_r0_unc' 3 (by decide) (by decide) (by decide)]
      rw [h_r0_at_3] at h_b
      exact h_b
    · have h_r7_at_4 : r7.val[4]! = r2.val[4]! := by
        rw [h_r7_unc' 4 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 4 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 4 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 4 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 4 (by decide) (by decide) (by decide)]
      rw [h_r7_at_4]
      have h_eq : (2 * (2#usize : Std.Usize).val : Nat) = 4 := by decide
      have h_b := h_r2_bnd_e
      rw [h_eq] at h_b
      have h_r1_at_4 : r1.val[4]! = out.val[4]! := by
        rw [h_r1_unc' 4 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 4 (by decide) (by decide) (by decide)]
      rw [h_r1_at_4] at h_b
      exact h_b
    · have h_r7_at_5 : r7.val[5]! = r2.val[5]! := by
        rw [h_r7_unc' 5 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 5 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 5 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 5 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 5 (by decide) (by decide) (by decide)]
      rw [h_r7_at_5]
      have h_eq : (2 * (2#usize : Std.Usize).val + 1 : Nat) = 5 := by decide
      have h_b := h_r2_bnd_o
      rw [h_eq] at h_b
      have h_r1_at_5 : r1.val[5]! = out.val[5]! := by
        rw [h_r1_unc' 5 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 5 (by decide) (by decide) (by decide)]
      rw [h_r1_at_5] at h_b
      exact h_b
    · have h_r7_at_6 : r7.val[6]! = r3.val[6]! := by
        rw [h_r7_unc' 6 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 6 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 6 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 6 (by decide) (by decide) (by decide)]
      rw [h_r7_at_6]
      have h_eq : (2 * (3#usize : Std.Usize).val : Nat) = 6 := by decide
      have h_b := h_r3_bnd_e
      rw [h_eq] at h_b
      have h_r2_at_6 : r2.val[6]! = out.val[6]! := by
        rw [h_r2_unc' 6 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 6 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 6 (by decide) (by decide) (by decide)]
      rw [h_r2_at_6] at h_b
      exact h_b
    · have h_r7_at_7 : r7.val[7]! = r3.val[7]! := by
        rw [h_r7_unc' 7 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 7 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 7 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 7 (by decide) (by decide) (by decide)]
      rw [h_r7_at_7]
      have h_eq : (2 * (3#usize : Std.Usize).val + 1 : Nat) = 7 := by decide
      have h_b := h_r3_bnd_o
      rw [h_eq] at h_b
      have h_r2_at_7 : r2.val[7]! = out.val[7]! := by
        rw [h_r2_unc' 7 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 7 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 7 (by decide) (by decide) (by decide)]
      rw [h_r2_at_7] at h_b
      exact h_b
    · have h_r7_at_8 : r7.val[8]! = r4.val[8]! := by
        rw [h_r7_unc' 8 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 8 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 8 (by decide) (by decide) (by decide)]
      rw [h_r7_at_8]
      have h_eq : (2 * (4#usize : Std.Usize).val : Nat) = 8 := by decide
      have h_b := h_r4_bnd_e
      rw [h_eq] at h_b
      have h_r3_at_8 : r3.val[8]! = out.val[8]! := by
        rw [h_r3_unc' 8 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 8 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 8 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 8 (by decide) (by decide) (by decide)]
      rw [h_r3_at_8] at h_b
      exact h_b
    · have h_r7_at_9 : r7.val[9]! = r4.val[9]! := by
        rw [h_r7_unc' 9 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 9 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 9 (by decide) (by decide) (by decide)]
      rw [h_r7_at_9]
      have h_eq : (2 * (4#usize : Std.Usize).val + 1 : Nat) = 9 := by decide
      have h_b := h_r4_bnd_o
      rw [h_eq] at h_b
      have h_r3_at_9 : r3.val[9]! = out.val[9]! := by
        rw [h_r3_unc' 9 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 9 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 9 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 9 (by decide) (by decide) (by decide)]
      rw [h_r3_at_9] at h_b
      exact h_b
    · have h_r7_at_10 : r7.val[10]! = r5.val[10]! := by
        rw [h_r7_unc' 10 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 10 (by decide) (by decide) (by decide)]
      rw [h_r7_at_10]
      have h_eq : (2 * (5#usize : Std.Usize).val : Nat) = 10 := by decide
      have h_b := h_r5_bnd_e
      rw [h_eq] at h_b
      have h_r4_at_10 : r4.val[10]! = out.val[10]! := by
        rw [h_r4_unc' 10 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 10 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 10 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 10 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 10 (by decide) (by decide) (by decide)]
      rw [h_r4_at_10] at h_b
      exact h_b
    · have h_r7_at_11 : r7.val[11]! = r5.val[11]! := by
        rw [h_r7_unc' 11 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 11 (by decide) (by decide) (by decide)]
      rw [h_r7_at_11]
      have h_eq : (2 * (5#usize : Std.Usize).val + 1 : Nat) = 11 := by decide
      have h_b := h_r5_bnd_o
      rw [h_eq] at h_b
      have h_r4_at_11 : r4.val[11]! = out.val[11]! := by
        rw [h_r4_unc' 11 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 11 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 11 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 11 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 11 (by decide) (by decide) (by decide)]
      rw [h_r4_at_11] at h_b
      exact h_b
    · have h_r7_at_12 : r7.val[12]! = r6.val[12]! := by
        rw [h_r7_unc' 12 (by decide) (by decide) (by decide)]
      rw [h_r7_at_12]
      have h_eq : (2 * (6#usize : Std.Usize).val : Nat) = 12 := by decide
      have h_b := h_r6_bnd_e
      rw [h_eq] at h_b
      have h_r5_at_12 : r5.val[12]! = out.val[12]! := by
        rw [h_r5_unc' 12 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 12 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 12 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 12 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 12 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 12 (by decide) (by decide) (by decide)]
      rw [h_r5_at_12] at h_b
      exact h_b
    · have h_r7_at_13 : r7.val[13]! = r6.val[13]! := by
        rw [h_r7_unc' 13 (by decide) (by decide) (by decide)]
      rw [h_r7_at_13]
      have h_eq : (2 * (6#usize : Std.Usize).val + 1 : Nat) = 13 := by decide
      have h_b := h_r6_bnd_o
      rw [h_eq] at h_b
      have h_r5_at_13 : r5.val[13]! = out.val[13]! := by
        rw [h_r5_unc' 13 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 13 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 13 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 13 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 13 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 13 (by decide) (by decide) (by decide)]
      rw [h_r5_at_13] at h_b
      exact h_b
    · have h_eq : (2 * (7#usize : Std.Usize).val : Nat) = 14 := by decide
      have h_b := h_r7_bnd_e
      rw [h_eq] at h_b
      have h_r6_at_14 : r6.val[14]! = out.val[14]! := by
        rw [h_r6_unc' 14 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 14 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 14 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 14 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 14 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 14 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 14 (by decide) (by decide) (by decide)]
      rw [h_r6_at_14] at h_b
      exact h_b
    · have h_eq : (2 * (7#usize : Std.Usize).val + 1 : Nat) = 15 := by decide
      have h_b := h_r7_bnd_o
      rw [h_eq] at h_b
      have h_r6_at_15 : r6.val[15]! = out.val[15]! := by
        rw [h_r6_unc' 15 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 15 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 15 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 15 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 15 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 15 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 15 (by decide) (by decide) (by decide)]
      rw [h_r6_at_15] at h_b
      exact h_b
  · -- ntt_multiply_base_case_post: per-lane FE equation.
    unfold ntt_multiply_base_case_post ntt_multiply_base_case_alg
    apply Subtype.ext
    have h_lhs_val : (Spec.chunk_reducing_from_i32_array_pure r7).val
        = (List.range 16).map (fun i => Spec.mont_reduce_pure (lift_fe_int (r7.val[i]!).val)) := by
      unfold Spec.chunk_reducing_from_i32_array_pure; rfl
    have h_rhs_val : (Spec.chunk_add_pure
                        (Spec.chunk_reducing_from_i32_array_pure out)
                        (Spec.ntt_multiply_pure_no_acc
                          (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                          (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                          (lift_fe_mont zeta2) (lift_fe_mont zeta3))).val
        = (List.range 16).map (fun i =>
            libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              ((Spec.chunk_reducing_from_i32_array_pure out).val[i]!)
              ((Spec.ntt_multiply_pure_no_acc
                  (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                  (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                  (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[i]!)) := by
      unfold Spec.chunk_add_pure; rfl
    rw [h_lhs_val, h_rhs_val]
    apply List.ext_getElem
    · simp
    · intro k hk1 hk2
      have hk : k < 16 := by simp at hk1; exact hk1
      rw [List.getElem_map, List.getElem_map, List.getElem_range]
      interval_cases k
      · -- Lane 0: touched by call 0 (zeta0, even).
        have h_r7_at_lane : r7.val[0]! = r0.val[0]! := by
          rw [h_r7_unc' 0 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 0 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 0 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 0 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 0 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 0 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_fe := h_r0_fe_e
        simp only [
                   show (2 * (0#usize : Std.Usize).val : Nat) = 0 from by decide] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[0]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[0]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[0]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[0]!)
                  ((lift_chunk_mont rhs).val[0]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[1]!)
                    ((lift_chunk_mont rhs).val[1]!))
                  (lift_fe_mont zeta0)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_0 : (lift_chunk_mont lhs).val[0]!
            = lift_fe_mont (lhs.elements.val[0]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[0]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 0 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 0 (by rw [h_l]; decide)]
        have h_lcm_lhs_1 : (lift_chunk_mont lhs).val[1]!
            = lift_fe_mont (lhs.elements.val[1]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[1]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 1 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 1 (by rw [h_l]; decide)]
        have h_lcm_rhs_0 : (lift_chunk_mont rhs).val[0]!
            = lift_fe_mont (rhs.elements.val[0]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[0]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 0 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 0 (by rw [h_l]; decide)]
        have h_lcm_rhs_1 : (lift_chunk_mont rhs).val[1]!
            = lift_fe_mont (rhs.elements.val[1]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[1]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 1 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 1 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_0, h_lcm_lhs_1, h_lcm_rhs_0, h_lcm_rhs_1]
      · -- Lane 1: touched by call 0 (zeta0, odd).
        have h_r7_at_lane : r7.val[1]! = r0.val[1]! := by
          rw [h_r7_unc' 1 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 1 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 1 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 1 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 1 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 1 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_fe := h_r0_fe_o
        simp only [
                   show (2 * (0#usize : Std.Usize).val : Nat) = 0 from by decide] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[1]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[1]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[1]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[0]!)
                  ((lift_chunk_mont rhs).val[1]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[1]!)
                  ((lift_chunk_mont rhs).val[0]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_0 : (lift_chunk_mont lhs).val[0]!
            = lift_fe_mont (lhs.elements.val[0]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[0]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 0 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 0 (by rw [h_l]; decide)]
        have h_lcm_lhs_1 : (lift_chunk_mont lhs).val[1]!
            = lift_fe_mont (lhs.elements.val[1]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[1]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 1 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 1 (by rw [h_l]; decide)]
        have h_lcm_rhs_0 : (lift_chunk_mont rhs).val[0]!
            = lift_fe_mont (rhs.elements.val[0]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[0]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 0 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 0 (by rw [h_l]; decide)]
        have h_lcm_rhs_1 : (lift_chunk_mont rhs).val[1]!
            = lift_fe_mont (rhs.elements.val[1]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[1]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 1 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 1 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_0, h_lcm_lhs_1, h_lcm_rhs_0, h_lcm_rhs_1]
      · -- Lane 2: touched by call 1 (nzeta0, even).
        have h_r7_at_lane : r7.val[2]! = r1.val[2]! := by
          rw [h_r7_unc' 2 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 2 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 2 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 2 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 2 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 2 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r0.val[2]! = out.val[2]! := by
          rw [h_r0_unc' 2 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r0.val[3]! = out.val[3]! := by
          rw [h_r0_unc' 3 (by decide) (by decide) (by decide)]
        have h_fe := h_r1_fe_e
        simp only [
                   show (2 * (1#usize : Std.Usize).val : Nat) = 2 from by decide] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_n0_fe] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[2]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[2]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[2]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[2]!)
                  ((lift_chunk_mont rhs).val[2]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[3]!)
                    ((lift_chunk_mont rhs).val[3]!))
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta0))) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_2 : (lift_chunk_mont lhs).val[2]!
            = lift_fe_mont (lhs.elements.val[2]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[2]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 2 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 2 (by rw [h_l]; decide)]
        have h_lcm_lhs_3 : (lift_chunk_mont lhs).val[3]!
            = lift_fe_mont (lhs.elements.val[3]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[3]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 3 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 3 (by rw [h_l]; decide)]
        have h_lcm_rhs_2 : (lift_chunk_mont rhs).val[2]!
            = lift_fe_mont (rhs.elements.val[2]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[2]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 2 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 2 (by rw [h_l]; decide)]
        have h_lcm_rhs_3 : (lift_chunk_mont rhs).val[3]!
            = lift_fe_mont (rhs.elements.val[3]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[3]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 3 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 3 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_2, h_lcm_lhs_3, h_lcm_rhs_2, h_lcm_rhs_3]
      · -- Lane 3: touched by call 1 (nzeta0, odd).
        have h_r7_at_lane : r7.val[3]! = r1.val[3]! := by
          rw [h_r7_unc' 3 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 3 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 3 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 3 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 3 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 3 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r0.val[2]! = out.val[2]! := by
          rw [h_r0_unc' 2 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r0.val[3]! = out.val[3]! := by
          rw [h_r0_unc' 3 (by decide) (by decide) (by decide)]
        have h_fe := h_r1_fe_o
        simp only [
                   show (2 * (1#usize : Std.Usize).val : Nat) = 2 from by decide] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[3]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[3]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[3]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[2]!)
                  ((lift_chunk_mont rhs).val[3]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[3]!)
                  ((lift_chunk_mont rhs).val[2]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_2 : (lift_chunk_mont lhs).val[2]!
            = lift_fe_mont (lhs.elements.val[2]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[2]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 2 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 2 (by rw [h_l]; decide)]
        have h_lcm_lhs_3 : (lift_chunk_mont lhs).val[3]!
            = lift_fe_mont (lhs.elements.val[3]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[3]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 3 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 3 (by rw [h_l]; decide)]
        have h_lcm_rhs_2 : (lift_chunk_mont rhs).val[2]!
            = lift_fe_mont (rhs.elements.val[2]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[2]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 2 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 2 (by rw [h_l]; decide)]
        have h_lcm_rhs_3 : (lift_chunk_mont rhs).val[3]!
            = lift_fe_mont (rhs.elements.val[3]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[3]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 3 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 3 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_2, h_lcm_lhs_3, h_lcm_rhs_2, h_lcm_rhs_3]
      · -- Lane 4: touched by call 2 (zeta1, even).
        have h_r7_at_lane : r7.val[4]! = r2.val[4]! := by
          rw [h_r7_unc' 4 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 4 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 4 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 4 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 4 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r1.val[4]! = out.val[4]! := by
          rw [h_r1_unc' 4 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 4 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r1.val[5]! = out.val[5]! := by
          rw [h_r1_unc' 5 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 5 (by decide) (by decide) (by decide)]
        have h_fe := h_r2_fe_e
        simp only [
                   show (2 * (2#usize : Std.Usize).val : Nat) = 4 from by decide] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[4]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[4]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[4]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[4]!)
                  ((lift_chunk_mont rhs).val[4]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[5]!)
                    ((lift_chunk_mont rhs).val[5]!))
                  (lift_fe_mont zeta1)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_4 : (lift_chunk_mont lhs).val[4]!
            = lift_fe_mont (lhs.elements.val[4]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[4]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 4 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 4 (by rw [h_l]; decide)]
        have h_lcm_lhs_5 : (lift_chunk_mont lhs).val[5]!
            = lift_fe_mont (lhs.elements.val[5]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[5]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 5 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 5 (by rw [h_l]; decide)]
        have h_lcm_rhs_4 : (lift_chunk_mont rhs).val[4]!
            = lift_fe_mont (rhs.elements.val[4]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[4]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 4 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 4 (by rw [h_l]; decide)]
        have h_lcm_rhs_5 : (lift_chunk_mont rhs).val[5]!
            = lift_fe_mont (rhs.elements.val[5]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[5]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 5 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 5 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_4, h_lcm_lhs_5, h_lcm_rhs_4, h_lcm_rhs_5]
      · -- Lane 5: touched by call 2 (zeta1, odd).
        have h_r7_at_lane : r7.val[5]! = r2.val[5]! := by
          rw [h_r7_unc' 5 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 5 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 5 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 5 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 5 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r1.val[4]! = out.val[4]! := by
          rw [h_r1_unc' 4 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 4 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r1.val[5]! = out.val[5]! := by
          rw [h_r1_unc' 5 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 5 (by decide) (by decide) (by decide)]
        have h_fe := h_r2_fe_o
        simp only [
                   show (2 * (2#usize : Std.Usize).val : Nat) = 4 from by decide] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[5]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[5]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[5]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[4]!)
                  ((lift_chunk_mont rhs).val[5]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[5]!)
                  ((lift_chunk_mont rhs).val[4]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_4 : (lift_chunk_mont lhs).val[4]!
            = lift_fe_mont (lhs.elements.val[4]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[4]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 4 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 4 (by rw [h_l]; decide)]
        have h_lcm_lhs_5 : (lift_chunk_mont lhs).val[5]!
            = lift_fe_mont (lhs.elements.val[5]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[5]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 5 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 5 (by rw [h_l]; decide)]
        have h_lcm_rhs_4 : (lift_chunk_mont rhs).val[4]!
            = lift_fe_mont (rhs.elements.val[4]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[4]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 4 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 4 (by rw [h_l]; decide)]
        have h_lcm_rhs_5 : (lift_chunk_mont rhs).val[5]!
            = lift_fe_mont (rhs.elements.val[5]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[5]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 5 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 5 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_4, h_lcm_lhs_5, h_lcm_rhs_4, h_lcm_rhs_5]
      · -- Lane 6: touched by call 3 (nzeta1, even).
        have h_r7_at_lane : r7.val[6]! = r3.val[6]! := by
          rw [h_r7_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 6 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r2.val[6]! = out.val[6]! := by
          rw [h_r2_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 6 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r2.val[7]! = out.val[7]! := by
          rw [h_r2_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 7 (by decide) (by decide) (by decide)]
        have h_fe := h_r3_fe_e
        simp only [
                   show (2 * (3#usize : Std.Usize).val : Nat) = 6 from by decide] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_n1_fe] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[6]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[6]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[6]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[6]!)
                  ((lift_chunk_mont rhs).val[6]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[7]!)
                    ((lift_chunk_mont rhs).val[7]!))
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta1))) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_6 : (lift_chunk_mont lhs).val[6]!
            = lift_fe_mont (lhs.elements.val[6]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[6]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 6 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 6 (by rw [h_l]; decide)]
        have h_lcm_lhs_7 : (lift_chunk_mont lhs).val[7]!
            = lift_fe_mont (lhs.elements.val[7]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[7]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 7 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 7 (by rw [h_l]; decide)]
        have h_lcm_rhs_6 : (lift_chunk_mont rhs).val[6]!
            = lift_fe_mont (rhs.elements.val[6]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[6]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 6 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 6 (by rw [h_l]; decide)]
        have h_lcm_rhs_7 : (lift_chunk_mont rhs).val[7]!
            = lift_fe_mont (rhs.elements.val[7]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[7]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 7 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 7 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_6, h_lcm_lhs_7, h_lcm_rhs_6, h_lcm_rhs_7]
      · -- Lane 7: touched by call 3 (nzeta1, odd).
        have h_r7_at_lane : r7.val[7]! = r3.val[7]! := by
          rw [h_r7_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 7 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r2.val[6]! = out.val[6]! := by
          rw [h_r2_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 6 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r2.val[7]! = out.val[7]! := by
          rw [h_r2_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 7 (by decide) (by decide) (by decide)]
        have h_fe := h_r3_fe_o
        simp only [
                   show (2 * (3#usize : Std.Usize).val : Nat) = 6 from by decide] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[7]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[7]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[7]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[6]!)
                  ((lift_chunk_mont rhs).val[7]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[7]!)
                  ((lift_chunk_mont rhs).val[6]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_6 : (lift_chunk_mont lhs).val[6]!
            = lift_fe_mont (lhs.elements.val[6]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[6]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 6 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 6 (by rw [h_l]; decide)]
        have h_lcm_lhs_7 : (lift_chunk_mont lhs).val[7]!
            = lift_fe_mont (lhs.elements.val[7]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[7]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 7 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 7 (by rw [h_l]; decide)]
        have h_lcm_rhs_6 : (lift_chunk_mont rhs).val[6]!
            = lift_fe_mont (rhs.elements.val[6]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[6]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 6 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 6 (by rw [h_l]; decide)]
        have h_lcm_rhs_7 : (lift_chunk_mont rhs).val[7]!
            = lift_fe_mont (rhs.elements.val[7]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[7]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 7 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 7 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_6, h_lcm_lhs_7, h_lcm_rhs_6, h_lcm_rhs_7]
      · -- Lane 8: touched by call 4 (zeta2, even).
        have h_r7_at_lane : r7.val[8]! = r4.val[8]! := by
          rw [h_r7_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 8 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r3.val[8]! = out.val[8]! := by
          rw [h_r3_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 8 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r3.val[9]! = out.val[9]! := by
          rw [h_r3_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 9 (by decide) (by decide) (by decide)]
        have h_fe := h_r4_fe_e
        simp only [
                   show (2 * (4#usize : Std.Usize).val : Nat) = 8 from by decide] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[8]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[8]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[8]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[8]!)
                  ((lift_chunk_mont rhs).val[8]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[9]!)
                    ((lift_chunk_mont rhs).val[9]!))
                  (lift_fe_mont zeta2)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_8 : (lift_chunk_mont lhs).val[8]!
            = lift_fe_mont (lhs.elements.val[8]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[8]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 8 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 8 (by rw [h_l]; decide)]
        have h_lcm_lhs_9 : (lift_chunk_mont lhs).val[9]!
            = lift_fe_mont (lhs.elements.val[9]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[9]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 9 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 9 (by rw [h_l]; decide)]
        have h_lcm_rhs_8 : (lift_chunk_mont rhs).val[8]!
            = lift_fe_mont (rhs.elements.val[8]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[8]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 8 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 8 (by rw [h_l]; decide)]
        have h_lcm_rhs_9 : (lift_chunk_mont rhs).val[9]!
            = lift_fe_mont (rhs.elements.val[9]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[9]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 9 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 9 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_8, h_lcm_lhs_9, h_lcm_rhs_8, h_lcm_rhs_9]
      · -- Lane 9: touched by call 4 (zeta2, odd).
        have h_r7_at_lane : r7.val[9]! = r4.val[9]! := by
          rw [h_r7_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 9 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r3.val[8]! = out.val[8]! := by
          rw [h_r3_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 8 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r3.val[9]! = out.val[9]! := by
          rw [h_r3_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 9 (by decide) (by decide) (by decide)]
        have h_fe := h_r4_fe_o
        simp only [
                   show (2 * (4#usize : Std.Usize).val : Nat) = 8 from by decide] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[9]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[9]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[9]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[8]!)
                  ((lift_chunk_mont rhs).val[9]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[9]!)
                  ((lift_chunk_mont rhs).val[8]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_8 : (lift_chunk_mont lhs).val[8]!
            = lift_fe_mont (lhs.elements.val[8]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[8]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 8 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 8 (by rw [h_l]; decide)]
        have h_lcm_lhs_9 : (lift_chunk_mont lhs).val[9]!
            = lift_fe_mont (lhs.elements.val[9]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[9]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 9 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 9 (by rw [h_l]; decide)]
        have h_lcm_rhs_8 : (lift_chunk_mont rhs).val[8]!
            = lift_fe_mont (rhs.elements.val[8]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[8]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 8 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 8 (by rw [h_l]; decide)]
        have h_lcm_rhs_9 : (lift_chunk_mont rhs).val[9]!
            = lift_fe_mont (rhs.elements.val[9]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[9]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 9 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 9 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_8, h_lcm_lhs_9, h_lcm_rhs_8, h_lcm_rhs_9]
      · -- Lane 10: touched by call 5 (nzeta2, even).
        have h_r7_at_lane : r7.val[10]! = r5.val[10]! := by
          rw [h_r7_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 10 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r4.val[10]! = out.val[10]! := by
          rw [h_r4_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 10 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r4.val[11]! = out.val[11]! := by
          rw [h_r4_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 11 (by decide) (by decide) (by decide)]
        have h_fe := h_r5_fe_e
        simp only [
                   show (2 * (5#usize : Std.Usize).val : Nat) = 10 from by decide] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_n2_fe] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[10]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[10]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[10]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[10]!)
                  ((lift_chunk_mont rhs).val[10]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[11]!)
                    ((lift_chunk_mont rhs).val[11]!))
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta2))) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_10 : (lift_chunk_mont lhs).val[10]!
            = lift_fe_mont (lhs.elements.val[10]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[10]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 10 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 10 (by rw [h_l]; decide)]
        have h_lcm_lhs_11 : (lift_chunk_mont lhs).val[11]!
            = lift_fe_mont (lhs.elements.val[11]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[11]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 11 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 11 (by rw [h_l]; decide)]
        have h_lcm_rhs_10 : (lift_chunk_mont rhs).val[10]!
            = lift_fe_mont (rhs.elements.val[10]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[10]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 10 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 10 (by rw [h_l]; decide)]
        have h_lcm_rhs_11 : (lift_chunk_mont rhs).val[11]!
            = lift_fe_mont (rhs.elements.val[11]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[11]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 11 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 11 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_10, h_lcm_lhs_11, h_lcm_rhs_10, h_lcm_rhs_11]
      · -- Lane 11: touched by call 5 (nzeta2, odd).
        have h_r7_at_lane : r7.val[11]! = r5.val[11]! := by
          rw [h_r7_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 11 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r4.val[10]! = out.val[10]! := by
          rw [h_r4_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 10 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r4.val[11]! = out.val[11]! := by
          rw [h_r4_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 11 (by decide) (by decide) (by decide)]
        have h_fe := h_r5_fe_o
        simp only [
                   show (2 * (5#usize : Std.Usize).val : Nat) = 10 from by decide] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[11]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[11]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[11]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[10]!)
                  ((lift_chunk_mont rhs).val[11]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[11]!)
                  ((lift_chunk_mont rhs).val[10]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_10 : (lift_chunk_mont lhs).val[10]!
            = lift_fe_mont (lhs.elements.val[10]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[10]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 10 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 10 (by rw [h_l]; decide)]
        have h_lcm_lhs_11 : (lift_chunk_mont lhs).val[11]!
            = lift_fe_mont (lhs.elements.val[11]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[11]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 11 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 11 (by rw [h_l]; decide)]
        have h_lcm_rhs_10 : (lift_chunk_mont rhs).val[10]!
            = lift_fe_mont (rhs.elements.val[10]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[10]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 10 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 10 (by rw [h_l]; decide)]
        have h_lcm_rhs_11 : (lift_chunk_mont rhs).val[11]!
            = lift_fe_mont (rhs.elements.val[11]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[11]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 11 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 11 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_10, h_lcm_lhs_11, h_lcm_rhs_10, h_lcm_rhs_11]
      · -- Lane 12: touched by call 6 (zeta3, even).
        have h_r7_at_lane : r7.val[12]! = r6.val[12]! := by
          rw [h_r7_unc' 12 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r5.val[12]! = out.val[12]! := by
          rw [h_r5_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 12 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r5.val[13]! = out.val[13]! := by
          rw [h_r5_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 13 (by decide) (by decide) (by decide)]
        have h_fe := h_r6_fe_e
        simp only [
                   show (2 * (6#usize : Std.Usize).val : Nat) = 12 from by decide] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[12]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[12]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[12]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[12]!)
                  ((lift_chunk_mont rhs).val[12]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[13]!)
                    ((lift_chunk_mont rhs).val[13]!))
                  (lift_fe_mont zeta3)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_12 : (lift_chunk_mont lhs).val[12]!
            = lift_fe_mont (lhs.elements.val[12]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[12]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 12 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 12 (by rw [h_l]; decide)]
        have h_lcm_lhs_13 : (lift_chunk_mont lhs).val[13]!
            = lift_fe_mont (lhs.elements.val[13]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[13]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 13 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 13 (by rw [h_l]; decide)]
        have h_lcm_rhs_12 : (lift_chunk_mont rhs).val[12]!
            = lift_fe_mont (rhs.elements.val[12]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[12]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 12 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 12 (by rw [h_l]; decide)]
        have h_lcm_rhs_13 : (lift_chunk_mont rhs).val[13]!
            = lift_fe_mont (rhs.elements.val[13]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[13]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 13 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 13 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_12, h_lcm_lhs_13, h_lcm_rhs_12, h_lcm_rhs_13]
      · -- Lane 13: touched by call 6 (zeta3, odd).
        have h_r7_at_lane : r7.val[13]! = r6.val[13]! := by
          rw [h_r7_unc' 13 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r5.val[12]! = out.val[12]! := by
          rw [h_r5_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 12 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r5.val[13]! = out.val[13]! := by
          rw [h_r5_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 13 (by decide) (by decide) (by decide)]
        have h_fe := h_r6_fe_o
        simp only [
                   show (2 * (6#usize : Std.Usize).val : Nat) = 12 from by decide] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[13]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[13]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[13]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[12]!)
                  ((lift_chunk_mont rhs).val[13]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[13]!)
                  ((lift_chunk_mont rhs).val[12]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_12 : (lift_chunk_mont lhs).val[12]!
            = lift_fe_mont (lhs.elements.val[12]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[12]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 12 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 12 (by rw [h_l]; decide)]
        have h_lcm_lhs_13 : (lift_chunk_mont lhs).val[13]!
            = lift_fe_mont (lhs.elements.val[13]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[13]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 13 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 13 (by rw [h_l]; decide)]
        have h_lcm_rhs_12 : (lift_chunk_mont rhs).val[12]!
            = lift_fe_mont (rhs.elements.val[12]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[12]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 12 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 12 (by rw [h_l]; decide)]
        have h_lcm_rhs_13 : (lift_chunk_mont rhs).val[13]!
            = lift_fe_mont (rhs.elements.val[13]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[13]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 13 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 13 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_12, h_lcm_lhs_13, h_lcm_rhs_12, h_lcm_rhs_13]
      · -- Lane 14: touched by call 7 (nzeta3, even).
        have h_src_at_even : r6.val[14]! = out.val[14]! := by
          rw [h_r6_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 14 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r6.val[15]! = out.val[15]! := by
          rw [h_r6_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 15 (by decide) (by decide) (by decide)]
        have h_fe := h_r7_fe_e
        simp only [
                   show (2 * (7#usize : Std.Usize).val : Nat) = 14 from by decide] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_n3_fe] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[14]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[14]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[14]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[14]!)
                  ((lift_chunk_mont rhs).val[14]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[15]!)
                    ((lift_chunk_mont rhs).val[15]!))
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta3))) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_14 : (lift_chunk_mont lhs).val[14]!
            = lift_fe_mont (lhs.elements.val[14]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[14]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 14 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 14 (by rw [h_l]; decide)]
        have h_lcm_lhs_15 : (lift_chunk_mont lhs).val[15]!
            = lift_fe_mont (lhs.elements.val[15]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[15]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 15 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 15 (by rw [h_l]; decide)]
        have h_lcm_rhs_14 : (lift_chunk_mont rhs).val[14]!
            = lift_fe_mont (rhs.elements.val[14]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[14]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 14 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 14 (by rw [h_l]; decide)]
        have h_lcm_rhs_15 : (lift_chunk_mont rhs).val[15]!
            = lift_fe_mont (rhs.elements.val[15]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[15]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 15 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 15 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_14, h_lcm_lhs_15, h_lcm_rhs_14, h_lcm_rhs_15]
      · -- Lane 15: touched by call 7 (nzeta3, odd).
        have h_src_at_even : r6.val[14]! = out.val[14]! := by
          rw [h_r6_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 14 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r6.val[15]! = out.val[15]! := by
          rw [h_r6_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 15 (by decide) (by decide) (by decide)]
        have h_fe := h_r7_fe_o
        simp only [
                   show (2 * (7#usize : Std.Usize).val : Nat) = 14 from by decide] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[15]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[15]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[15]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[14]!)
                  ((lift_chunk_mont rhs).val[15]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[15]!)
                  ((lift_chunk_mont rhs).val[14]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_14 : (lift_chunk_mont lhs).val[14]!
            = lift_fe_mont (lhs.elements.val[14]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[14]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 14 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 14 (by rw [h_l]; decide)]
        have h_lcm_lhs_15 : (lift_chunk_mont lhs).val[15]!
            = lift_fe_mont (lhs.elements.val[15]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[15]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 15 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 15 (by rw [h_l]; decide)]
        have h_lcm_rhs_14 : (lift_chunk_mont rhs).val[14]!
            = lift_fe_mont (rhs.elements.val[14]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[14]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 14 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 14 (by rw [h_l]; decide)]
        have h_lcm_rhs_15 : (lift_chunk_mont rhs).val[15]!
            = lift_fe_mont (rhs.elements.val[15]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[15]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 15 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 15 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_14, h_lcm_lhs_15, h_lcm_rhs_14, h_lcm_rhs_15]
  · -- Spec.ntt_multiply_cache_post — cache POST: 8 conjuncts (one per pair).
    intro i
    -- For each pair index i, the cache7 lane at slot i.val equals cache_i lane at slot i.val
    -- (since calls i+1..7 write different slots). Conclude via h_c{j}_unc' chain + the
    -- per-pair canonicity + FE-equation conjuncts h_c{j}_canon, h_c{j}_fe.
    rcases i with ⟨i, hi⟩
    -- Normalise (J#usize).val = J in the per-pair canonicity/FE hypotheses.
    have h_uv0 : (0#usize : Std.Usize).val = 0 := rfl
    have h_uv1 : (1#usize : Std.Usize).val = 1 := rfl
    have h_uv2 : (2#usize : Std.Usize).val = 2 := rfl
    have h_uv3 : (3#usize : Std.Usize).val = 3 := rfl
    have h_uv4 : (4#usize : Std.Usize).val = 4 := rfl
    have h_uv5 : (5#usize : Std.Usize).val = 5 := rfl
    have h_uv6 : (6#usize : Std.Usize).val = 6 := rfl
    have h_uv7 : (7#usize : Std.Usize).val = 7 := rfl
    -- Index-arithmetic normalisations on (2 * (J#usize).val + 1).
    interval_cases i
    · -- Pair 0: cache7[0] = cache0[0] (calls 1..7 don't touch slot 0).
      have h_chain : cache7.elements.val[0]! = cache0.elements.val[0]! := by
        rw [h_c7_unc' 0 (by decide) (by decide)]
        rw [h_c6_unc' 0 (by decide) (by decide)]
        rw [h_c5_unc' 0 (by decide) (by decide)]
        rw [h_c4_unc' 0 (by decide) (by decide)]
        rw [h_c3_unc' 0 (by decide) (by decide)]
        rw [h_c2_unc' 0 (by decide) (by decide)]
        rw [h_c1_unc' 0 (by decide) (by decide)]
      refine ⟨?_, ?_⟩
      · -- canonical: cache0[0] ≤ 3328.
        rw [show ((⟨0, hi⟩ : Fin 8) : Fin 8).val = 0 from rfl, h_chain]
        rw [h_uv0] at h_c0_canon; exact h_c0_canon
      · -- FE eq: lift_fe_mont cache7[0] = mul_pure (lift_fe_mont rhs[1]) (zeta0_fe).
        rw [show ((⟨0, hi⟩ : Fin 8) : Fin 8).val = 0 from rfl, h_chain]
        rw [h_uv0] at h_c0_fe; rw [h_c0_fe]
        -- effective_zeta_fe ⟨0, _⟩ ... = zeta0_fe.
        show _ = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (lift_fe_mont (rhs.elements.val[2 * 0 + 1]!))
                  (Spec.effective_zeta_fe ⟨0, hi⟩
                    (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                    (lift_fe_mont zeta2) (lift_fe_mont zeta3))
        unfold Spec.effective_zeta_fe; simp
    · -- Pair 1: cache7[1] = cache1[1].
      have h_chain : cache7.elements.val[1]! = cache1.elements.val[1]! := by
        rw [h_c7_unc' 1 (by decide) (by decide)]
        rw [h_c6_unc' 1 (by decide) (by decide)]
        rw [h_c5_unc' 1 (by decide) (by decide)]
        rw [h_c4_unc' 1 (by decide) (by decide)]
        rw [h_c3_unc' 1 (by decide) (by decide)]
        rw [h_c2_unc' 1 (by decide) (by decide)]
      refine ⟨?_, ?_⟩
      · rw [show ((⟨1, hi⟩ : Fin 8) : Fin 8).val = 1 from rfl, h_chain]
        rw [h_uv1] at h_c1_canon; exact h_c1_canon
      · rw [show ((⟨1, hi⟩ : Fin 8) : Fin 8).val = 1 from rfl, h_chain]
        rw [h_uv1] at h_c1_fe; rw [h_c1_fe, h_n0_fe]
        show _ = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (lift_fe_mont (rhs.elements.val[2 * 1 + 1]!))
                  (Spec.effective_zeta_fe ⟨1, hi⟩
                    (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                    (lift_fe_mont zeta2) (lift_fe_mont zeta3))
        unfold Spec.effective_zeta_fe; simp
    · -- Pair 2: cache7[2] = cache2[2].
      have h_chain : cache7.elements.val[2]! = cache2.elements.val[2]! := by
        rw [h_c7_unc' 2 (by decide) (by decide)]
        rw [h_c6_unc' 2 (by decide) (by decide)]
        rw [h_c5_unc' 2 (by decide) (by decide)]
        rw [h_c4_unc' 2 (by decide) (by decide)]
        rw [h_c3_unc' 2 (by decide) (by decide)]
      refine ⟨?_, ?_⟩
      · rw [show ((⟨2, hi⟩ : Fin 8) : Fin 8).val = 2 from rfl, h_chain]
        rw [h_uv2] at h_c2_canon; exact h_c2_canon
      · rw [show ((⟨2, hi⟩ : Fin 8) : Fin 8).val = 2 from rfl, h_chain]
        rw [h_uv2] at h_c2_fe; rw [h_c2_fe]
        show _ = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (lift_fe_mont (rhs.elements.val[2 * 2 + 1]!))
                  (Spec.effective_zeta_fe ⟨2, hi⟩
                    (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                    (lift_fe_mont zeta2) (lift_fe_mont zeta3))
        unfold Spec.effective_zeta_fe; simp
    · -- Pair 3: cache7[3] = cache3[3].
      have h_chain : cache7.elements.val[3]! = cache3.elements.val[3]! := by
        rw [h_c7_unc' 3 (by decide) (by decide)]
        rw [h_c6_unc' 3 (by decide) (by decide)]
        rw [h_c5_unc' 3 (by decide) (by decide)]
        rw [h_c4_unc' 3 (by decide) (by decide)]
      refine ⟨?_, ?_⟩
      · rw [show ((⟨3, hi⟩ : Fin 8) : Fin 8).val = 3 from rfl, h_chain]
        rw [h_uv3] at h_c3_canon; exact h_c3_canon
      · rw [show ((⟨3, hi⟩ : Fin 8) : Fin 8).val = 3 from rfl, h_chain]
        rw [h_uv3] at h_c3_fe; rw [h_c3_fe, h_n1_fe]
        show _ = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (lift_fe_mont (rhs.elements.val[2 * 3 + 1]!))
                  (Spec.effective_zeta_fe ⟨3, hi⟩
                    (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                    (lift_fe_mont zeta2) (lift_fe_mont zeta3))
        unfold Spec.effective_zeta_fe; simp
    · -- Pair 4: cache7[4] = cache4[4].
      have h_chain : cache7.elements.val[4]! = cache4.elements.val[4]! := by
        rw [h_c7_unc' 4 (by decide) (by decide)]
        rw [h_c6_unc' 4 (by decide) (by decide)]
        rw [h_c5_unc' 4 (by decide) (by decide)]
      refine ⟨?_, ?_⟩
      · rw [show ((⟨4, hi⟩ : Fin 8) : Fin 8).val = 4 from rfl, h_chain]
        rw [h_uv4] at h_c4_canon; exact h_c4_canon
      · rw [show ((⟨4, hi⟩ : Fin 8) : Fin 8).val = 4 from rfl, h_chain]
        rw [h_uv4] at h_c4_fe; rw [h_c4_fe]
        show _ = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (lift_fe_mont (rhs.elements.val[2 * 4 + 1]!))
                  (Spec.effective_zeta_fe ⟨4, hi⟩
                    (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                    (lift_fe_mont zeta2) (lift_fe_mont zeta3))
        unfold Spec.effective_zeta_fe; simp
    · -- Pair 5: cache7[5] = cache5[5].
      have h_chain : cache7.elements.val[5]! = cache5.elements.val[5]! := by
        rw [h_c7_unc' 5 (by decide) (by decide)]
        rw [h_c6_unc' 5 (by decide) (by decide)]
      refine ⟨?_, ?_⟩
      · rw [show ((⟨5, hi⟩ : Fin 8) : Fin 8).val = 5 from rfl, h_chain]
        rw [h_uv5] at h_c5_canon; exact h_c5_canon
      · rw [show ((⟨5, hi⟩ : Fin 8) : Fin 8).val = 5 from rfl, h_chain]
        rw [h_uv5] at h_c5_fe; rw [h_c5_fe, h_n2_fe]
        show _ = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (lift_fe_mont (rhs.elements.val[2 * 5 + 1]!))
                  (Spec.effective_zeta_fe ⟨5, hi⟩
                    (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                    (lift_fe_mont zeta2) (lift_fe_mont zeta3))
        unfold Spec.effective_zeta_fe; simp
    · -- Pair 6: cache7[6] = cache6[6].
      have h_chain : cache7.elements.val[6]! = cache6.elements.val[6]! := by
        rw [h_c7_unc' 6 (by decide) (by decide)]
      refine ⟨?_, ?_⟩
      · rw [show ((⟨6, hi⟩ : Fin 8) : Fin 8).val = 6 from rfl, h_chain]
        rw [h_uv6] at h_c6_canon; exact h_c6_canon
      · rw [show ((⟨6, hi⟩ : Fin 8) : Fin 8).val = 6 from rfl, h_chain]
        rw [h_uv6] at h_c6_fe; rw [h_c6_fe]
        show _ = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (lift_fe_mont (rhs.elements.val[2 * 6 + 1]!))
                  (Spec.effective_zeta_fe ⟨6, hi⟩
                    (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                    (lift_fe_mont zeta2) (lift_fe_mont zeta3))
        unfold Spec.effective_zeta_fe; simp
    · -- Pair 7: cache7[7] (last call wrote slot 7).
      refine ⟨?_, ?_⟩
      · rw [show ((⟨7, hi⟩ : Fin 8) : Fin 8).val = 7 from rfl]
        rw [h_uv7] at h_c7_canon; exact h_c7_canon
      · rw [show ((⟨7, hi⟩ : Fin 8) : Fin 8).val = 7 from rfl]
        rw [h_uv7] at h_c7_fe; rw [h_c7_fe, h_n3_fe]
        show _ = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (lift_fe_mont (rhs.elements.val[2 * 7 + 1]!))
                  (Spec.effective_zeta_fe ⟨7, hi⟩
                    (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                    (lift_fe_mont zeta2) (lift_fe_mont zeta3))
        unfold Spec.effective_zeta_fe; simp
  · -- Lanes 8..15: untouched.
    intro k hk h8
    -- cache7[k] = cache6[k] = cache5[k] = cache4[k] = cache3[k] = cache2[k] = cache1[k] = cache0[k] = cache[k]
    -- since each cacheJ.unc' k holds whenever k ≠ J.
    have hk_ne_7 : k ≠ 7 := by omega
    have hk_ne_6 : k ≠ 6 := by omega
    have hk_ne_5 : k ≠ 5 := by omega
    have hk_ne_4 : k ≠ 4 := by omega
    have hk_ne_3 : k ≠ 3 := by omega
    have hk_ne_2 : k ≠ 2 := by omega
    have hk_ne_1 : k ≠ 1 := by omega
    have hk_ne_0 : k ≠ 0 := by omega
    rw [h_c7_unc' k hk hk_ne_7]
    rw [h_c6_unc' k hk hk_ne_6]
    rw [h_c5_unc' k hk hk_ne_5]
    rw [h_c4_unc' k hk hk_ne_4]
    rw [h_c3_unc' k hk hk_ne_3]
    rw [h_c2_unc' k hk hk_ne_2]
    rw [h_c1_unc' k hk hk_ne_1]
    rw [h_c0_unc' k hk hk_ne_0]

set_option maxHeartbeats 16000000 in
/-- L2.8d — `vector.portable.ntt.accumulating_ntt_multiply_use_cache`:
    cache-using variant. The impl chains 8
    `accumulating_ntt_multiply_binomials_use_cache` calls; each reads
    `cache[i]` instead of recomputing `mont_reduce(b[2i+1]·zeta_i)`.

    POST identical to `accumulating_ntt_multiply_fc` (the four zetas
    are ghost arguments — they appear only in the cache PRE-condition
    and the POST's `ntt_multiply_base_case_post`, NOT in the impl call).
    Compose with `accumulating_ntt_multiply_fill_cache_fc`: discharge
    the cache PRE from a prior `_fill_cache` POST's cache conjunct. -/
@[spec]
theorem accumulating_ntt_multiply_use_cache_fc
    (lhs rhs : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Aeneas.Std.Slice Std.I32)
    (cache : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta0 zeta1 zeta2 zeta3 : Std.I16)
    (h_out_len : out.length = 16)
    (h_lhs : ∀ j : Fin 16, (lhs.elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_rhs : ∀ j : Fin 16, (rhs.elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_zeta0 : zeta0.val.natAbs ≤ 1664)
    (h_zeta1 : zeta1.val.natAbs ≤ 1664)
    (h_zeta2 : zeta2.val.natAbs ≤ 1664)
    (h_zeta3 : zeta3.val.natAbs ≤ 1664)
    (h_out_bnd : ∀ k : Fin 16, (out.val[k.val]!).val.natAbs ≤ 2^30)
    (h_cache : Spec.ntt_multiply_cache_post rhs zeta0 zeta1 zeta2 zeta3 cache) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_use_cache
      lhs rhs out cache
    ⦃ ⇓ r => ⌜ r.length = 16 ∧
              (∀ k : Fin 16, (r.val[k.val]!).val.natAbs
                              ≤ (out.val[k.val]!).val.natAbs + 2^25) ∧
              ntt_multiply_base_case_post lhs rhs
                zeta0 zeta1 zeta2 zeta3 out r ⌝ ⦄ := by
  have h_cache_canon : ∀ i : Fin 8,
      (cache.elements.val[i.val]!).val.natAbs ≤ 3328 := fun i => (h_cache i).1
  have h_cache_fe : ∀ i : Fin 8,
      lift_fe_mont (cache.elements.val[i.val]!)
        = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (lift_fe_mont (rhs.elements.val[2 * i.val + 1]!))
            (Spec.effective_zeta_fe i
              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
              (lift_fe_mont zeta2) (lift_fe_mont zeta3)) := fun i => (h_cache i).2
  have h_out_bnd_universal : ∀ k : Fin 16, (out.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 := by
    intro k; have := h_out_bnd k; omega
  -- Cache FE-equations specialised at each pair index 0..7 (Spec.effective_zeta_fe
  -- collapses to the appropriate zeta_j or neg_pure zeta_j).
  have h_cache0_fe : lift_fe_mont (cache.elements.val[0]!)
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont (rhs.elements.val[1]!)) (lift_fe_mont zeta0) := by
    have h := h_cache_fe ⟨0, by decide⟩
    rw [show ((⟨0, by decide⟩ : Fin 8) : Fin 8).val = 0 from rfl] at h
    rw [h]; unfold Spec.effective_zeta_fe; simp
  have h_cache1_fe : lift_fe_mont (cache.elements.val[1]!)
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont (rhs.elements.val[3]!))
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta0)) := by
    have h := h_cache_fe ⟨1, by decide⟩
    rw [show ((⟨1, by decide⟩ : Fin 8) : Fin 8).val = 1 from rfl] at h
    rw [h]; unfold Spec.effective_zeta_fe; simp
  have h_cache2_fe : lift_fe_mont (cache.elements.val[2]!)
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont (rhs.elements.val[5]!)) (lift_fe_mont zeta1) := by
    have h := h_cache_fe ⟨2, by decide⟩
    rw [show ((⟨2, by decide⟩ : Fin 8) : Fin 8).val = 2 from rfl] at h
    rw [h]; unfold Spec.effective_zeta_fe; simp
  have h_cache3_fe : lift_fe_mont (cache.elements.val[3]!)
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont (rhs.elements.val[7]!))
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta1)) := by
    have h := h_cache_fe ⟨3, by decide⟩
    rw [show ((⟨3, by decide⟩ : Fin 8) : Fin 8).val = 3 from rfl] at h
    rw [h]; unfold Spec.effective_zeta_fe; simp
  have h_cache4_fe : lift_fe_mont (cache.elements.val[4]!)
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont (rhs.elements.val[9]!)) (lift_fe_mont zeta2) := by
    have h := h_cache_fe ⟨4, by decide⟩
    rw [show ((⟨4, by decide⟩ : Fin 8) : Fin 8).val = 4 from rfl] at h
    rw [h]; unfold Spec.effective_zeta_fe; simp
  have h_cache5_fe : lift_fe_mont (cache.elements.val[5]!)
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont (rhs.elements.val[11]!))
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta2)) := by
    have h := h_cache_fe ⟨5, by decide⟩
    rw [show ((⟨5, by decide⟩ : Fin 8) : Fin 8).val = 5 from rfl] at h
    rw [h]; unfold Spec.effective_zeta_fe; simp
  have h_cache6_fe : lift_fe_mont (cache.elements.val[6]!)
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont (rhs.elements.val[13]!)) (lift_fe_mont zeta3) := by
    have h := h_cache_fe ⟨6, by decide⟩
    rw [show ((⟨6, by decide⟩ : Fin 8) : Fin 8).val = 6 from rfl] at h
    rw [h]; unfold Spec.effective_zeta_fe; simp
  have h_cache7_fe : lift_fe_mont (cache.elements.val[7]!)
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont (rhs.elements.val[15]!))
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta3)) := by
    have h := h_cache_fe ⟨7, by decide⟩
    rw [show ((⟨7, by decide⟩ : Fin 8) : Fin 8).val = 7 from rfl] at h
    rw [h]; unfold Spec.effective_zeta_fe; simp
  -- ===== 8 chained calls =====
  -- Call 0:
  obtain ⟨r0, h_r0_eq, h_r0_len, h_r0_unc, h_r0_bnd_e, h_r0_bnd_o, h_r0_fe_e, h_r0_fe_o⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_use_cache_fc lhs rhs 0#usize out cache
        (by decide) h_out_len h_lhs h_rhs (h_cache_canon ⟨0, by decide⟩)
        h_out_bnd_universal)
  have h_r0_at_even : (r0.val[0]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (0#usize : Std.Usize).val : Nat) = 0 := by decide
    have h_b := h_r0_bnd_e; rw [h_eq] at h_b
    have h_out_le := h_out_bnd ⟨0, by decide⟩; simp only at h_out_le; omega
  have h_r0_at_odd : (r0.val[1]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (0#usize : Std.Usize).val + 1 : Nat) = 1 := by decide
    have h_b := h_r0_bnd_o; rw [h_eq] at h_b
    have h_out_le := h_out_bnd ⟨1, by decide⟩; simp only at h_out_le; omega
  have h_r0_unc' : ∀ k : Nat, k < 16 → k ≠ 0 → k ≠ 1 →
      r0.val[k]! = out.val[k]! := by
    intro k hk hke hko
    apply h_r0_unc k hk
    · show k ≠ 2 * (0#usize : Std.Usize).val; rw [show (0#usize : Std.Usize).val = 0 from rfl]; omega
    · show k ≠ 2 * (0#usize : Std.Usize).val + 1; rw [show (0#usize : Std.Usize).val = 0 from rfl]; omega
  have h_r0_bnd_universal : ∀ k : Fin 16, (r0.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step out r0 0 (by decide) h_out_bnd_universal
      h_r0_unc' h_r0_at_even h_r0_at_odd
  -- Call 1:
  obtain ⟨r1, h_r1_eq, h_r1_len, h_r1_unc, h_r1_bnd_e, h_r1_bnd_o, h_r1_fe_e, h_r1_fe_o⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_use_cache_fc lhs rhs 1#usize r0 cache
        (by decide) h_r0_len h_lhs h_rhs (h_cache_canon ⟨1, by decide⟩)
        h_r0_bnd_universal)
  have h_r1_at_even : (r1.val[2]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (1#usize : Std.Usize).val : Nat) = 2 := by decide
    have h_b := h_r1_bnd_e; rw [h_eq] at h_b
    have h_r0_eq2 : r0.val[2]! = out.val[2]! := h_r0_unc' 2 (by decide) (by decide) (by decide)
    rw [h_r0_eq2] at h_b
    have h_out_le := h_out_bnd ⟨2, by decide⟩; simp only at h_out_le; omega
  have h_r1_at_odd : (r1.val[3]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (1#usize : Std.Usize).val + 1 : Nat) = 3 := by decide
    have h_b := h_r1_bnd_o; rw [h_eq] at h_b
    have h_r0_eq3 : r0.val[3]! = out.val[3]! := h_r0_unc' 3 (by decide) (by decide) (by decide)
    rw [h_r0_eq3] at h_b
    have h_out_le := h_out_bnd ⟨3, by decide⟩; simp only at h_out_le; omega
  have h_r1_unc' : ∀ k : Nat, k < 16 → k ≠ 2 → k ≠ 3 →
      r1.val[k]! = r0.val[k]! := by
    intro k hk hke hko
    apply h_r1_unc k hk
    · show k ≠ 2 * (1#usize : Std.Usize).val; rw [show (1#usize : Std.Usize).val = 1 from rfl]; omega
    · show k ≠ 2 * (1#usize : Std.Usize).val + 1; rw [show (1#usize : Std.Usize).val = 1 from rfl]; omega
  have h_r1_bnd_universal : ∀ k : Fin 16, (r1.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r0 r1 1 (by decide) h_r0_bnd_universal
      h_r1_unc' h_r1_at_even h_r1_at_odd
  -- Call 2:
  obtain ⟨r2, h_r2_eq, h_r2_len, h_r2_unc, h_r2_bnd_e, h_r2_bnd_o, h_r2_fe_e, h_r2_fe_o⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_use_cache_fc lhs rhs 2#usize r1 cache
        (by decide) h_r1_len h_lhs h_rhs (h_cache_canon ⟨2, by decide⟩)
        h_r1_bnd_universal)
  have h_r2_at_even : (r2.val[4]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (2#usize : Std.Usize).val : Nat) = 4 := by decide
    have h_b := h_r2_bnd_e; rw [h_eq] at h_b
    have h_r1_eq4 : r1.val[4]! = out.val[4]! := by
      rw [h_r1_unc' 4 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 4 (by decide) (by decide) (by decide)]
    rw [h_r1_eq4] at h_b
    have h_out_le := h_out_bnd ⟨4, by decide⟩; simp only at h_out_le; omega
  have h_r2_at_odd : (r2.val[5]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (2#usize : Std.Usize).val + 1 : Nat) = 5 := by decide
    have h_b := h_r2_bnd_o; rw [h_eq] at h_b
    have h_r1_eq5 : r1.val[5]! = out.val[5]! := by
      rw [h_r1_unc' 5 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 5 (by decide) (by decide) (by decide)]
    rw [h_r1_eq5] at h_b
    have h_out_le := h_out_bnd ⟨5, by decide⟩; simp only at h_out_le; omega
  have h_r2_unc' : ∀ k : Nat, k < 16 → k ≠ 4 → k ≠ 5 →
      r2.val[k]! = r1.val[k]! := by
    intro k hk hke hko
    apply h_r2_unc k hk
    · show k ≠ 2 * (2#usize : Std.Usize).val; rw [show (2#usize : Std.Usize).val = 2 from rfl]; omega
    · show k ≠ 2 * (2#usize : Std.Usize).val + 1; rw [show (2#usize : Std.Usize).val = 2 from rfl]; omega
  have h_r2_bnd_universal : ∀ k : Fin 16, (r2.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r1 r2 2 (by decide) h_r1_bnd_universal
      h_r2_unc' h_r2_at_even h_r2_at_odd
  -- Call 3:
  obtain ⟨r3, h_r3_eq, h_r3_len, h_r3_unc, h_r3_bnd_e, h_r3_bnd_o, h_r3_fe_e, h_r3_fe_o⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_use_cache_fc lhs rhs 3#usize r2 cache
        (by decide) h_r2_len h_lhs h_rhs (h_cache_canon ⟨3, by decide⟩)
        h_r2_bnd_universal)
  have h_r3_at_even : (r3.val[6]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (3#usize : Std.Usize).val : Nat) = 6 := by decide
    have h_b := h_r3_bnd_e; rw [h_eq] at h_b
    have h_r2_eq6 : r2.val[6]! = out.val[6]! := by
      rw [h_r2_unc' 6 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 6 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 6 (by decide) (by decide) (by decide)]
    rw [h_r2_eq6] at h_b
    have h_out_le := h_out_bnd ⟨6, by decide⟩; simp only at h_out_le; omega
  have h_r3_at_odd : (r3.val[7]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (3#usize : Std.Usize).val + 1 : Nat) = 7 := by decide
    have h_b := h_r3_bnd_o; rw [h_eq] at h_b
    have h_r2_eq7 : r2.val[7]! = out.val[7]! := by
      rw [h_r2_unc' 7 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 7 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 7 (by decide) (by decide) (by decide)]
    rw [h_r2_eq7] at h_b
    have h_out_le := h_out_bnd ⟨7, by decide⟩; simp only at h_out_le; omega
  have h_r3_unc' : ∀ k : Nat, k < 16 → k ≠ 6 → k ≠ 7 →
      r3.val[k]! = r2.val[k]! := by
    intro k hk hke hko
    apply h_r3_unc k hk
    · show k ≠ 2 * (3#usize : Std.Usize).val; rw [show (3#usize : Std.Usize).val = 3 from rfl]; omega
    · show k ≠ 2 * (3#usize : Std.Usize).val + 1; rw [show (3#usize : Std.Usize).val = 3 from rfl]; omega
  have h_r3_bnd_universal : ∀ k : Fin 16, (r3.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r2 r3 3 (by decide) h_r2_bnd_universal
      h_r3_unc' h_r3_at_even h_r3_at_odd
  -- Call 4:
  obtain ⟨r4, h_r4_eq, h_r4_len, h_r4_unc, h_r4_bnd_e, h_r4_bnd_o, h_r4_fe_e, h_r4_fe_o⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_use_cache_fc lhs rhs 4#usize r3 cache
        (by decide) h_r3_len h_lhs h_rhs (h_cache_canon ⟨4, by decide⟩)
        h_r3_bnd_universal)
  have h_r4_at_even : (r4.val[8]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (4#usize : Std.Usize).val : Nat) = 8 := by decide
    have h_b := h_r4_bnd_e; rw [h_eq] at h_b
    have h_r3_eq8 : r3.val[8]! = out.val[8]! := by
      rw [h_r3_unc' 8 (by decide) (by decide) (by decide)]
      rw [h_r2_unc' 8 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 8 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 8 (by decide) (by decide) (by decide)]
    rw [h_r3_eq8] at h_b
    have h_out_le := h_out_bnd ⟨8, by decide⟩; simp only at h_out_le; omega
  have h_r4_at_odd : (r4.val[9]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (4#usize : Std.Usize).val + 1 : Nat) = 9 := by decide
    have h_b := h_r4_bnd_o; rw [h_eq] at h_b
    have h_r3_eq9 : r3.val[9]! = out.val[9]! := by
      rw [h_r3_unc' 9 (by decide) (by decide) (by decide)]
      rw [h_r2_unc' 9 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 9 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 9 (by decide) (by decide) (by decide)]
    rw [h_r3_eq9] at h_b
    have h_out_le := h_out_bnd ⟨9, by decide⟩; simp only at h_out_le; omega
  have h_r4_unc' : ∀ k : Nat, k < 16 → k ≠ 8 → k ≠ 9 →
      r4.val[k]! = r3.val[k]! := by
    intro k hk hke hko
    apply h_r4_unc k hk
    · show k ≠ 2 * (4#usize : Std.Usize).val; rw [show (4#usize : Std.Usize).val = 4 from rfl]; omega
    · show k ≠ 2 * (4#usize : Std.Usize).val + 1; rw [show (4#usize : Std.Usize).val = 4 from rfl]; omega
  have h_r4_bnd_universal : ∀ k : Fin 16, (r4.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r3 r4 4 (by decide) h_r3_bnd_universal
      h_r4_unc' h_r4_at_even h_r4_at_odd
  -- Call 5:
  obtain ⟨r5, h_r5_eq, h_r5_len, h_r5_unc, h_r5_bnd_e, h_r5_bnd_o, h_r5_fe_e, h_r5_fe_o⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_use_cache_fc lhs rhs 5#usize r4 cache
        (by decide) h_r4_len h_lhs h_rhs (h_cache_canon ⟨5, by decide⟩)
        h_r4_bnd_universal)
  have h_r5_at_even : (r5.val[10]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (5#usize : Std.Usize).val : Nat) = 10 := by decide
    have h_b := h_r5_bnd_e; rw [h_eq] at h_b
    have h_r4_eq10 : r4.val[10]! = out.val[10]! := by
      rw [h_r4_unc' 10 (by decide) (by decide) (by decide)]
      rw [h_r3_unc' 10 (by decide) (by decide) (by decide)]
      rw [h_r2_unc' 10 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 10 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 10 (by decide) (by decide) (by decide)]
    rw [h_r4_eq10] at h_b
    have h_out_le := h_out_bnd ⟨10, by decide⟩; simp only at h_out_le; omega
  have h_r5_at_odd : (r5.val[11]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (5#usize : Std.Usize).val + 1 : Nat) = 11 := by decide
    have h_b := h_r5_bnd_o; rw [h_eq] at h_b
    have h_r4_eq11 : r4.val[11]! = out.val[11]! := by
      rw [h_r4_unc' 11 (by decide) (by decide) (by decide)]
      rw [h_r3_unc' 11 (by decide) (by decide) (by decide)]
      rw [h_r2_unc' 11 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 11 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 11 (by decide) (by decide) (by decide)]
    rw [h_r4_eq11] at h_b
    have h_out_le := h_out_bnd ⟨11, by decide⟩; simp only at h_out_le; omega
  have h_r5_unc' : ∀ k : Nat, k < 16 → k ≠ 10 → k ≠ 11 →
      r5.val[k]! = r4.val[k]! := by
    intro k hk hke hko
    apply h_r5_unc k hk
    · show k ≠ 2 * (5#usize : Std.Usize).val; rw [show (5#usize : Std.Usize).val = 5 from rfl]; omega
    · show k ≠ 2 * (5#usize : Std.Usize).val + 1; rw [show (5#usize : Std.Usize).val = 5 from rfl]; omega
  have h_r5_bnd_universal : ∀ k : Fin 16, (r5.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r4 r5 5 (by decide) h_r4_bnd_universal
      h_r5_unc' h_r5_at_even h_r5_at_odd
  -- Call 6:
  obtain ⟨r6, h_r6_eq, h_r6_len, h_r6_unc, h_r6_bnd_e, h_r6_bnd_o, h_r6_fe_e, h_r6_fe_o⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_use_cache_fc lhs rhs 6#usize r5 cache
        (by decide) h_r5_len h_lhs h_rhs (h_cache_canon ⟨6, by decide⟩)
        h_r5_bnd_universal)
  have h_r6_at_even : (r6.val[12]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (6#usize : Std.Usize).val : Nat) = 12 := by decide
    have h_b := h_r6_bnd_e; rw [h_eq] at h_b
    have h_r5_eq12 : r5.val[12]! = out.val[12]! := by
      rw [h_r5_unc' 12 (by decide) (by decide) (by decide)]
      rw [h_r4_unc' 12 (by decide) (by decide) (by decide)]
      rw [h_r3_unc' 12 (by decide) (by decide) (by decide)]
      rw [h_r2_unc' 12 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 12 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 12 (by decide) (by decide) (by decide)]
    rw [h_r5_eq12] at h_b
    have h_out_le := h_out_bnd ⟨12, by decide⟩; simp only at h_out_le; omega
  have h_r6_at_odd : (r6.val[13]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (6#usize : Std.Usize).val + 1 : Nat) = 13 := by decide
    have h_b := h_r6_bnd_o; rw [h_eq] at h_b
    have h_r5_eq13 : r5.val[13]! = out.val[13]! := by
      rw [h_r5_unc' 13 (by decide) (by decide) (by decide)]
      rw [h_r4_unc' 13 (by decide) (by decide) (by decide)]
      rw [h_r3_unc' 13 (by decide) (by decide) (by decide)]
      rw [h_r2_unc' 13 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 13 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 13 (by decide) (by decide) (by decide)]
    rw [h_r5_eq13] at h_b
    have h_out_le := h_out_bnd ⟨13, by decide⟩; simp only at h_out_le; omega
  have h_r6_unc' : ∀ k : Nat, k < 16 → k ≠ 12 → k ≠ 13 →
      r6.val[k]! = r5.val[k]! := by
    intro k hk hke hko
    apply h_r6_unc k hk
    · show k ≠ 2 * (6#usize : Std.Usize).val; rw [show (6#usize : Std.Usize).val = 6 from rfl]; omega
    · show k ≠ 2 * (6#usize : Std.Usize).val + 1; rw [show (6#usize : Std.Usize).val = 6 from rfl]; omega
  have h_r6_bnd_universal : ∀ k : Fin 16, (r6.val[k.val]!).val.natAbs ≤ 2^30 + 2^25 :=
    L2_8c.bnd_universal_step r5 r6 6 (by decide) h_r5_bnd_universal
      h_r6_unc' h_r6_at_even h_r6_at_odd
  -- Call 7:
  obtain ⟨r7, h_r7_eq, h_r7_len, h_r7_unc, h_r7_bnd_e, h_r7_bnd_o, h_r7_fe_e, h_r7_fe_o⟩ :=
    triple_exists_ok_fc
      (accumulating_ntt_multiply_binomials_use_cache_fc lhs rhs 7#usize r6 cache
        (by decide) h_r6_len h_lhs h_rhs (h_cache_canon ⟨7, by decide⟩)
        h_r6_bnd_universal)
  have h_r7_at_even : (r7.val[14]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (7#usize : Std.Usize).val : Nat) = 14 := by decide
    have h_b := h_r7_bnd_e; rw [h_eq] at h_b
    have h_r6_eq14 : r6.val[14]! = out.val[14]! := by
      rw [h_r6_unc' 14 (by decide) (by decide) (by decide)]
      rw [h_r5_unc' 14 (by decide) (by decide) (by decide)]
      rw [h_r4_unc' 14 (by decide) (by decide) (by decide)]
      rw [h_r3_unc' 14 (by decide) (by decide) (by decide)]
      rw [h_r2_unc' 14 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 14 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 14 (by decide) (by decide) (by decide)]
    rw [h_r6_eq14] at h_b
    have h_out_le := h_out_bnd ⟨14, by decide⟩; simp only at h_out_le; omega
  have h_r7_at_odd : (r7.val[15]!).val.natAbs ≤ 2^30 + 2^25 := by
    have h_eq : (2 * (7#usize : Std.Usize).val + 1 : Nat) = 15 := by decide
    have h_b := h_r7_bnd_o; rw [h_eq] at h_b
    have h_r6_eq15 : r6.val[15]! = out.val[15]! := by
      rw [h_r6_unc' 15 (by decide) (by decide) (by decide)]
      rw [h_r5_unc' 15 (by decide) (by decide) (by decide)]
      rw [h_r4_unc' 15 (by decide) (by decide) (by decide)]
      rw [h_r3_unc' 15 (by decide) (by decide) (by decide)]
      rw [h_r2_unc' 15 (by decide) (by decide) (by decide)]
      rw [h_r1_unc' 15 (by decide) (by decide) (by decide)]
      rw [h_r0_unc' 15 (by decide) (by decide) (by decide)]
    rw [h_r6_eq15] at h_b
    have h_out_le := h_out_bnd ⟨15, by decide⟩; simp only at h_out_le; omega
  have h_r7_unc' : ∀ k : Nat, k < 16 → k ≠ 14 → k ≠ 15 →
      r7.val[k]! = r6.val[k]! := by
    intro k hk hke hko
    apply h_r7_unc k hk
    · show k ≠ 2 * (7#usize : Std.Usize).val; rw [show (7#usize : Std.Usize).val = 7 from rfl]; omega
    · show k ≠ 2 * (7#usize : Std.Usize).val + 1; rw [show (7#usize : Std.Usize).val = 7 from rfl]; omega
  -- ===== Pre-rewrite each h_r{i}_fe_e to L2.8c form =====
  -- h_r{i}_fe_e (even) has the shape:
  --   mont_reduce_pure (lift_fe_int r{i}[2j].val) = add_pure (mr prev[2j]) (add_pure
  --     (mul_pure (lift lhs[2j]) (lift rhs[2j])) (mul_pure (lift lhs[2j+1]) c_m))
  -- where c_m = lift_fe_mont cache[j.val]. Using h_cache{j}_fe + mul_pure_assoc:
  --   mul_pure (lift lhs[2j+1]) c_m = mul_pure (lift lhs[2j+1]) (mul_pure (lift rhs[2j+1]) zeta_eff)
  --                                 = mul_pure (mul_pure (lift lhs[2j+1]) (lift rhs[2j+1])) zeta_eff.
  -- That's the L2.8c shape.
  have h_uv0 : (0#usize : Std.Usize).val = 0 := rfl
  have h_uv1 : (1#usize : Std.Usize).val = 1 := rfl
  have h_uv2 : (2#usize : Std.Usize).val = 2 := rfl
  have h_uv3 : (3#usize : Std.Usize).val = 3 := rfl
  have h_uv4 : (4#usize : Std.Usize).val = 4 := rfl
  have h_uv5 : (5#usize : Std.Usize).val = 5 := rfl
  have h_uv6 : (6#usize : Std.Usize).val = 6 := rfl
  have h_uv7 : (7#usize : Std.Usize).val = 7 := rfl
  rw [h_uv0] at h_r0_fe_e h_r0_fe_o
  rw [h_uv1] at h_r1_fe_e h_r1_fe_o
  rw [h_uv2] at h_r2_fe_e h_r2_fe_o
  rw [h_uv3] at h_r3_fe_e h_r3_fe_o
  rw [h_uv4] at h_r4_fe_e h_r4_fe_o
  rw [h_uv5] at h_r5_fe_e h_r5_fe_o
  rw [h_uv6] at h_r6_fe_e h_r6_fe_o
  rw [h_uv7] at h_r7_fe_e h_r7_fe_o
  rw [h_cache0_fe, L2_8d.mul_pure_assoc] at h_r0_fe_e
  rw [h_cache1_fe, L2_8d.mul_pure_assoc] at h_r1_fe_e
  rw [h_cache2_fe, L2_8d.mul_pure_assoc] at h_r2_fe_e
  rw [h_cache3_fe, L2_8d.mul_pure_assoc] at h_r3_fe_e
  rw [h_cache4_fe, L2_8d.mul_pure_assoc] at h_r4_fe_e
  rw [h_cache5_fe, L2_8d.mul_pure_assoc] at h_r5_fe_e
  rw [h_cache6_fe, L2_8d.mul_pure_assoc] at h_r6_fe_e
  rw [h_cache7_fe, L2_8d.mul_pure_assoc] at h_r7_fe_e
  -- After rewrite: h_r{i}_fe_e matches L2.8c per-pair FE shape with effective zeta.
  -- Now h_n0_fe..h_n3_fe are unbound. Set their identity by way of synthesis from
  -- effective_zeta_fe.
  have h_n0_fe :
    (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta0))
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta0) := rfl
  have h_n1_fe :
    (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta1))
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta1) := rfl
  have h_n2_fe :
    (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta2))
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta2) := rfl
  have h_n3_fe :
    (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta3))
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta3) := rfl
  -- Compose monadic body.
  have h_body :
      libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_use_cache
        lhs rhs out cache = .ok r7 := by
    unfold libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_use_cache
    simp only [h_r0_eq, h_r1_eq, h_r2_eq, h_r3_eq,
               h_r4_eq, h_r5_eq, h_r6_eq, h_r7_eq,
               Aeneas.Std.bind_tc_ok]
  apply triple_of_ok_fc h_body
  -- POST: 3-conjunct.
  refine ⟨h_r7_len, ?_, ?_⟩
  · -- Relative bound (same 16-way enumeration as L2.8c).
    intro k
    rcases k with ⟨k, hk⟩
    interval_cases k
    · have h_r7_at_0 : r7.val[0]! = r0.val[0]! := by
        rw [h_r7_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 0 (by decide) (by decide) (by decide)]
      rw [h_r7_at_0]
      have h_b := h_r0_bnd_e
      rw [show (2 * (0#usize : Std.Usize).val : Nat) = 0 from by decide] at h_b
      exact h_b
    · have h_r7_at_1 : r7.val[1]! = r0.val[1]! := by
        rw [h_r7_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 1 (by decide) (by decide) (by decide)]
      rw [h_r7_at_1]
      have h_b := h_r0_bnd_o
      rw [show (2 * (0#usize : Std.Usize).val + 1 : Nat) = 1 from by decide] at h_b
      exact h_b
    · have h_r7_at_2 : r7.val[2]! = r1.val[2]! := by
        rw [h_r7_unc' 2 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 2 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 2 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 2 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 2 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 2 (by decide) (by decide) (by decide)]
      rw [h_r7_at_2]
      have h_b := h_r1_bnd_e
      rw [show (2 * (1#usize : Std.Usize).val : Nat) = 2 from by decide] at h_b
      have h_r0_at_2 : r0.val[2]! = out.val[2]! := h_r0_unc' 2 (by decide) (by decide) (by decide)
      rw [h_r0_at_2] at h_b
      exact h_b
    · have h_r7_at_3 : r7.val[3]! = r1.val[3]! := by
        rw [h_r7_unc' 3 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 3 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 3 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 3 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 3 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 3 (by decide) (by decide) (by decide)]
      rw [h_r7_at_3]
      have h_b := h_r1_bnd_o
      rw [show (2 * (1#usize : Std.Usize).val + 1 : Nat) = 3 from by decide] at h_b
      have h_r0_at_3 : r0.val[3]! = out.val[3]! := h_r0_unc' 3 (by decide) (by decide) (by decide)
      rw [h_r0_at_3] at h_b
      exact h_b
    · have h_r7_at_4 : r7.val[4]! = r2.val[4]! := by
        rw [h_r7_unc' 4 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 4 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 4 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 4 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 4 (by decide) (by decide) (by decide)]
      rw [h_r7_at_4]
      have h_b := h_r2_bnd_e
      rw [show (2 * (2#usize : Std.Usize).val : Nat) = 4 from by decide] at h_b
      have h_r1_at_4 : r1.val[4]! = out.val[4]! := by
        rw [h_r1_unc' 4 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 4 (by decide) (by decide) (by decide)]
      rw [h_r1_at_4] at h_b
      exact h_b
    · have h_r7_at_5 : r7.val[5]! = r2.val[5]! := by
        rw [h_r7_unc' 5 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 5 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 5 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 5 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 5 (by decide) (by decide) (by decide)]
      rw [h_r7_at_5]
      have h_b := h_r2_bnd_o
      rw [show (2 * (2#usize : Std.Usize).val + 1 : Nat) = 5 from by decide] at h_b
      have h_r1_at_5 : r1.val[5]! = out.val[5]! := by
        rw [h_r1_unc' 5 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 5 (by decide) (by decide) (by decide)]
      rw [h_r1_at_5] at h_b
      exact h_b
    · have h_r7_at_6 : r7.val[6]! = r3.val[6]! := by
        rw [h_r7_unc' 6 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 6 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 6 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 6 (by decide) (by decide) (by decide)]
      rw [h_r7_at_6]
      have h_b := h_r3_bnd_e
      rw [show (2 * (3#usize : Std.Usize).val : Nat) = 6 from by decide] at h_b
      have h_r2_at_6 : r2.val[6]! = out.val[6]! := by
        rw [h_r2_unc' 6 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 6 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 6 (by decide) (by decide) (by decide)]
      rw [h_r2_at_6] at h_b
      exact h_b
    · have h_r7_at_7 : r7.val[7]! = r3.val[7]! := by
        rw [h_r7_unc' 7 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 7 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 7 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 7 (by decide) (by decide) (by decide)]
      rw [h_r7_at_7]
      have h_b := h_r3_bnd_o
      rw [show (2 * (3#usize : Std.Usize).val + 1 : Nat) = 7 from by decide] at h_b
      have h_r2_at_7 : r2.val[7]! = out.val[7]! := by
        rw [h_r2_unc' 7 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 7 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 7 (by decide) (by decide) (by decide)]
      rw [h_r2_at_7] at h_b
      exact h_b
    · have h_r7_at_8 : r7.val[8]! = r4.val[8]! := by
        rw [h_r7_unc' 8 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 8 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 8 (by decide) (by decide) (by decide)]
      rw [h_r7_at_8]
      have h_b := h_r4_bnd_e
      rw [show (2 * (4#usize : Std.Usize).val : Nat) = 8 from by decide] at h_b
      have h_r3_at_8 : r3.val[8]! = out.val[8]! := by
        rw [h_r3_unc' 8 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 8 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 8 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 8 (by decide) (by decide) (by decide)]
      rw [h_r3_at_8] at h_b
      exact h_b
    · have h_r7_at_9 : r7.val[9]! = r4.val[9]! := by
        rw [h_r7_unc' 9 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 9 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 9 (by decide) (by decide) (by decide)]
      rw [h_r7_at_9]
      have h_b := h_r4_bnd_o
      rw [show (2 * (4#usize : Std.Usize).val + 1 : Nat) = 9 from by decide] at h_b
      have h_r3_at_9 : r3.val[9]! = out.val[9]! := by
        rw [h_r3_unc' 9 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 9 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 9 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 9 (by decide) (by decide) (by decide)]
      rw [h_r3_at_9] at h_b
      exact h_b
    · have h_r7_at_10 : r7.val[10]! = r5.val[10]! := by
        rw [h_r7_unc' 10 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 10 (by decide) (by decide) (by decide)]
      rw [h_r7_at_10]
      have h_b := h_r5_bnd_e
      rw [show (2 * (5#usize : Std.Usize).val : Nat) = 10 from by decide] at h_b
      have h_r4_at_10 : r4.val[10]! = out.val[10]! := by
        rw [h_r4_unc' 10 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 10 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 10 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 10 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 10 (by decide) (by decide) (by decide)]
      rw [h_r4_at_10] at h_b
      exact h_b
    · have h_r7_at_11 : r7.val[11]! = r5.val[11]! := by
        rw [h_r7_unc' 11 (by decide) (by decide) (by decide)]
        rw [h_r6_unc' 11 (by decide) (by decide) (by decide)]
      rw [h_r7_at_11]
      have h_b := h_r5_bnd_o
      rw [show (2 * (5#usize : Std.Usize).val + 1 : Nat) = 11 from by decide] at h_b
      have h_r4_at_11 : r4.val[11]! = out.val[11]! := by
        rw [h_r4_unc' 11 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 11 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 11 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 11 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 11 (by decide) (by decide) (by decide)]
      rw [h_r4_at_11] at h_b
      exact h_b
    · have h_r7_at_12 : r7.val[12]! = r6.val[12]! := by
        rw [h_r7_unc' 12 (by decide) (by decide) (by decide)]
      rw [h_r7_at_12]
      have h_b := h_r6_bnd_e
      rw [show (2 * (6#usize : Std.Usize).val : Nat) = 12 from by decide] at h_b
      have h_r5_at_12 : r5.val[12]! = out.val[12]! := by
        rw [h_r5_unc' 12 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 12 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 12 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 12 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 12 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 12 (by decide) (by decide) (by decide)]
      rw [h_r5_at_12] at h_b
      exact h_b
    · have h_r7_at_13 : r7.val[13]! = r6.val[13]! := by
        rw [h_r7_unc' 13 (by decide) (by decide) (by decide)]
      rw [h_r7_at_13]
      have h_b := h_r6_bnd_o
      rw [show (2 * (6#usize : Std.Usize).val + 1 : Nat) = 13 from by decide] at h_b
      have h_r5_at_13 : r5.val[13]! = out.val[13]! := by
        rw [h_r5_unc' 13 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 13 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 13 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 13 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 13 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 13 (by decide) (by decide) (by decide)]
      rw [h_r5_at_13] at h_b
      exact h_b
    · have h_b := h_r7_bnd_e
      rw [show (2 * (7#usize : Std.Usize).val : Nat) = 14 from by decide] at h_b
      have h_r6_at_14 : r6.val[14]! = out.val[14]! := by
        rw [h_r6_unc' 14 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 14 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 14 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 14 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 14 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 14 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 14 (by decide) (by decide) (by decide)]
      rw [h_r6_at_14] at h_b
      exact h_b
    · have h_b := h_r7_bnd_o
      rw [show (2 * (7#usize : Std.Usize).val + 1 : Nat) = 15 from by decide] at h_b
      have h_r6_at_15 : r6.val[15]! = out.val[15]! := by
        rw [h_r6_unc' 15 (by decide) (by decide) (by decide)]
        rw [h_r5_unc' 15 (by decide) (by decide) (by decide)]
        rw [h_r4_unc' 15 (by decide) (by decide) (by decide)]
        rw [h_r3_unc' 15 (by decide) (by decide) (by decide)]
        rw [h_r2_unc' 15 (by decide) (by decide) (by decide)]
        rw [h_r1_unc' 15 (by decide) (by decide) (by decide)]
        rw [h_r0_unc' 15 (by decide) (by decide) (by decide)]
      rw [h_r6_at_15] at h_b
      exact h_b
  · -- ntt_multiply_base_case_post: per-lane FE equation.
    unfold ntt_multiply_base_case_post ntt_multiply_base_case_alg
    apply Subtype.ext
    have h_lhs_val : (Spec.chunk_reducing_from_i32_array_pure r7).val
        = (List.range 16).map (fun i => Spec.mont_reduce_pure (lift_fe_int (r7.val[i]!).val)) := by
      unfold Spec.chunk_reducing_from_i32_array_pure; rfl
    have h_rhs_val : (Spec.chunk_add_pure
                        (Spec.chunk_reducing_from_i32_array_pure out)
                        (Spec.ntt_multiply_pure_no_acc
                          (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                          (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                          (lift_fe_mont zeta2) (lift_fe_mont zeta3))).val
        = (List.range 16).map (fun i =>
            libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              ((Spec.chunk_reducing_from_i32_array_pure out).val[i]!)
              ((Spec.ntt_multiply_pure_no_acc
                  (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                  (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                  (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[i]!)) := by
      unfold Spec.chunk_add_pure; rfl
    rw [h_lhs_val, h_rhs_val]
    apply List.ext_getElem
    · simp
    · intro k hk1 hk2
      have hk : k < 16 := by simp at hk1; exact hk1
      rw [List.getElem_map, List.getElem_map, List.getElem_range]
      interval_cases k
      · -- Lane 0: touched by call 0 (zeta0, even).
        have h_r7_at_lane : r7.val[0]! = r0.val[0]! := by
          rw [h_r7_unc' 0 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 0 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 0 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 0 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 0 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 0 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 0 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_fe := h_r0_fe_e
        simp only [] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[0]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[0]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[0]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[0]!)
                  ((lift_chunk_mont rhs).val[0]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[1]!)
                    ((lift_chunk_mont rhs).val[1]!))
                  (lift_fe_mont zeta0)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_0 : (lift_chunk_mont lhs).val[0]!
            = lift_fe_mont (lhs.elements.val[0]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[0]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 0 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 0 (by rw [h_l]; decide)]
        have h_lcm_lhs_1 : (lift_chunk_mont lhs).val[1]!
            = lift_fe_mont (lhs.elements.val[1]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[1]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 1 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 1 (by rw [h_l]; decide)]
        have h_lcm_rhs_0 : (lift_chunk_mont rhs).val[0]!
            = lift_fe_mont (rhs.elements.val[0]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[0]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 0 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 0 (by rw [h_l]; decide)]
        have h_lcm_rhs_1 : (lift_chunk_mont rhs).val[1]!
            = lift_fe_mont (rhs.elements.val[1]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[1]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 1 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 1 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_0, h_lcm_lhs_1, h_lcm_rhs_0, h_lcm_rhs_1]
      · -- Lane 1: touched by call 0 (zeta0, odd).
        have h_r7_at_lane : r7.val[1]! = r0.val[1]! := by
          rw [h_r7_unc' 1 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 1 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 1 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 1 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 1 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 1 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 1 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_fe := h_r0_fe_o
        simp only [] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[1]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[1]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[1]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[0]!)
                  ((lift_chunk_mont rhs).val[1]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[1]!)
                  ((lift_chunk_mont rhs).val[0]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_0 : (lift_chunk_mont lhs).val[0]!
            = lift_fe_mont (lhs.elements.val[0]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[0]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 0 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 0 (by rw [h_l]; decide)]
        have h_lcm_lhs_1 : (lift_chunk_mont lhs).val[1]!
            = lift_fe_mont (lhs.elements.val[1]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[1]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 1 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 1 (by rw [h_l]; decide)]
        have h_lcm_rhs_0 : (lift_chunk_mont rhs).val[0]!
            = lift_fe_mont (rhs.elements.val[0]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[0]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 0 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 0 (by rw [h_l]; decide)]
        have h_lcm_rhs_1 : (lift_chunk_mont rhs).val[1]!
            = lift_fe_mont (rhs.elements.val[1]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[1]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 1 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 1 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_0, h_lcm_lhs_1, h_lcm_rhs_0, h_lcm_rhs_1]
      · -- Lane 2: touched by call 1 (nzeta0, even).
        have h_r7_at_lane : r7.val[2]! = r1.val[2]! := by
          rw [h_r7_unc' 2 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 2 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 2 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 2 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 2 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 2 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r0.val[2]! = out.val[2]! := by
          rw [h_r0_unc' 2 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r0.val[3]! = out.val[3]! := by
          rw [h_r0_unc' 3 (by decide) (by decide) (by decide)]
        have h_fe := h_r1_fe_e
        simp only [] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_n0_fe] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[2]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[2]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[2]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[2]!)
                  ((lift_chunk_mont rhs).val[2]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[3]!)
                    ((lift_chunk_mont rhs).val[3]!))
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta0))) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_2 : (lift_chunk_mont lhs).val[2]!
            = lift_fe_mont (lhs.elements.val[2]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[2]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 2 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 2 (by rw [h_l]; decide)]
        have h_lcm_lhs_3 : (lift_chunk_mont lhs).val[3]!
            = lift_fe_mont (lhs.elements.val[3]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[3]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 3 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 3 (by rw [h_l]; decide)]
        have h_lcm_rhs_2 : (lift_chunk_mont rhs).val[2]!
            = lift_fe_mont (rhs.elements.val[2]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[2]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 2 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 2 (by rw [h_l]; decide)]
        have h_lcm_rhs_3 : (lift_chunk_mont rhs).val[3]!
            = lift_fe_mont (rhs.elements.val[3]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[3]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 3 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 3 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_2, h_lcm_lhs_3, h_lcm_rhs_2, h_lcm_rhs_3]
      · -- Lane 3: touched by call 1 (nzeta0, odd).
        have h_r7_at_lane : r7.val[3]! = r1.val[3]! := by
          rw [h_r7_unc' 3 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 3 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 3 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 3 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 3 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 3 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r0.val[2]! = out.val[2]! := by
          rw [h_r0_unc' 2 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r0.val[3]! = out.val[3]! := by
          rw [h_r0_unc' 3 (by decide) (by decide) (by decide)]
        have h_fe := h_r1_fe_o
        simp only [] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[3]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[3]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[3]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[2]!)
                  ((lift_chunk_mont rhs).val[3]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[3]!)
                  ((lift_chunk_mont rhs).val[2]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_2 : (lift_chunk_mont lhs).val[2]!
            = lift_fe_mont (lhs.elements.val[2]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[2]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 2 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 2 (by rw [h_l]; decide)]
        have h_lcm_lhs_3 : (lift_chunk_mont lhs).val[3]!
            = lift_fe_mont (lhs.elements.val[3]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[3]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 3 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 3 (by rw [h_l]; decide)]
        have h_lcm_rhs_2 : (lift_chunk_mont rhs).val[2]!
            = lift_fe_mont (rhs.elements.val[2]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[2]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 2 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 2 (by rw [h_l]; decide)]
        have h_lcm_rhs_3 : (lift_chunk_mont rhs).val[3]!
            = lift_fe_mont (rhs.elements.val[3]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[3]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 3 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 3 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_2, h_lcm_lhs_3, h_lcm_rhs_2, h_lcm_rhs_3]
      · -- Lane 4: touched by call 2 (zeta1, even).
        have h_r7_at_lane : r7.val[4]! = r2.val[4]! := by
          rw [h_r7_unc' 4 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 4 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 4 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 4 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 4 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r1.val[4]! = out.val[4]! := by
          rw [h_r1_unc' 4 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 4 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r1.val[5]! = out.val[5]! := by
          rw [h_r1_unc' 5 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 5 (by decide) (by decide) (by decide)]
        have h_fe := h_r2_fe_e
        simp only [] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[4]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[4]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[4]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[4]!)
                  ((lift_chunk_mont rhs).val[4]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[5]!)
                    ((lift_chunk_mont rhs).val[5]!))
                  (lift_fe_mont zeta1)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_4 : (lift_chunk_mont lhs).val[4]!
            = lift_fe_mont (lhs.elements.val[4]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[4]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 4 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 4 (by rw [h_l]; decide)]
        have h_lcm_lhs_5 : (lift_chunk_mont lhs).val[5]!
            = lift_fe_mont (lhs.elements.val[5]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[5]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 5 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 5 (by rw [h_l]; decide)]
        have h_lcm_rhs_4 : (lift_chunk_mont rhs).val[4]!
            = lift_fe_mont (rhs.elements.val[4]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[4]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 4 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 4 (by rw [h_l]; decide)]
        have h_lcm_rhs_5 : (lift_chunk_mont rhs).val[5]!
            = lift_fe_mont (rhs.elements.val[5]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[5]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 5 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 5 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_4, h_lcm_lhs_5, h_lcm_rhs_4, h_lcm_rhs_5]
      · -- Lane 5: touched by call 2 (zeta1, odd).
        have h_r7_at_lane : r7.val[5]! = r2.val[5]! := by
          rw [h_r7_unc' 5 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 5 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 5 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 5 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 5 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r1.val[4]! = out.val[4]! := by
          rw [h_r1_unc' 4 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 4 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r1.val[5]! = out.val[5]! := by
          rw [h_r1_unc' 5 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 5 (by decide) (by decide) (by decide)]
        have h_fe := h_r2_fe_o
        simp only [] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[5]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[5]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[5]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[4]!)
                  ((lift_chunk_mont rhs).val[5]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[5]!)
                  ((lift_chunk_mont rhs).val[4]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_4 : (lift_chunk_mont lhs).val[4]!
            = lift_fe_mont (lhs.elements.val[4]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[4]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 4 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 4 (by rw [h_l]; decide)]
        have h_lcm_lhs_5 : (lift_chunk_mont lhs).val[5]!
            = lift_fe_mont (lhs.elements.val[5]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[5]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 5 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 5 (by rw [h_l]; decide)]
        have h_lcm_rhs_4 : (lift_chunk_mont rhs).val[4]!
            = lift_fe_mont (rhs.elements.val[4]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[4]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 4 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 4 (by rw [h_l]; decide)]
        have h_lcm_rhs_5 : (lift_chunk_mont rhs).val[5]!
            = lift_fe_mont (rhs.elements.val[5]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[5]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 5 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 5 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_4, h_lcm_lhs_5, h_lcm_rhs_4, h_lcm_rhs_5]
      · -- Lane 6: touched by call 3 (nzeta1, even).
        have h_r7_at_lane : r7.val[6]! = r3.val[6]! := by
          rw [h_r7_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 6 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r2.val[6]! = out.val[6]! := by
          rw [h_r2_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 6 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r2.val[7]! = out.val[7]! := by
          rw [h_r2_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 7 (by decide) (by decide) (by decide)]
        have h_fe := h_r3_fe_e
        simp only [] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_n1_fe] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[6]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[6]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[6]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[6]!)
                  ((lift_chunk_mont rhs).val[6]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[7]!)
                    ((lift_chunk_mont rhs).val[7]!))
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta1))) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_6 : (lift_chunk_mont lhs).val[6]!
            = lift_fe_mont (lhs.elements.val[6]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[6]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 6 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 6 (by rw [h_l]; decide)]
        have h_lcm_lhs_7 : (lift_chunk_mont lhs).val[7]!
            = lift_fe_mont (lhs.elements.val[7]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[7]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 7 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 7 (by rw [h_l]; decide)]
        have h_lcm_rhs_6 : (lift_chunk_mont rhs).val[6]!
            = lift_fe_mont (rhs.elements.val[6]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[6]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 6 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 6 (by rw [h_l]; decide)]
        have h_lcm_rhs_7 : (lift_chunk_mont rhs).val[7]!
            = lift_fe_mont (rhs.elements.val[7]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[7]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 7 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 7 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_6, h_lcm_lhs_7, h_lcm_rhs_6, h_lcm_rhs_7]
      · -- Lane 7: touched by call 3 (nzeta1, odd).
        have h_r7_at_lane : r7.val[7]! = r3.val[7]! := by
          rw [h_r7_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 7 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r2.val[6]! = out.val[6]! := by
          rw [h_r2_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 6 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 6 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r2.val[7]! = out.val[7]! := by
          rw [h_r2_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 7 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 7 (by decide) (by decide) (by decide)]
        have h_fe := h_r3_fe_o
        simp only [] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[7]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[7]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[7]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[6]!)
                  ((lift_chunk_mont rhs).val[7]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[7]!)
                  ((lift_chunk_mont rhs).val[6]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_6 : (lift_chunk_mont lhs).val[6]!
            = lift_fe_mont (lhs.elements.val[6]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[6]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 6 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 6 (by rw [h_l]; decide)]
        have h_lcm_lhs_7 : (lift_chunk_mont lhs).val[7]!
            = lift_fe_mont (lhs.elements.val[7]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[7]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 7 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 7 (by rw [h_l]; decide)]
        have h_lcm_rhs_6 : (lift_chunk_mont rhs).val[6]!
            = lift_fe_mont (rhs.elements.val[6]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[6]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 6 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 6 (by rw [h_l]; decide)]
        have h_lcm_rhs_7 : (lift_chunk_mont rhs).val[7]!
            = lift_fe_mont (rhs.elements.val[7]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[7]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 7 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 7 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_6, h_lcm_lhs_7, h_lcm_rhs_6, h_lcm_rhs_7]
      · -- Lane 8: touched by call 4 (zeta2, even).
        have h_r7_at_lane : r7.val[8]! = r4.val[8]! := by
          rw [h_r7_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 8 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r3.val[8]! = out.val[8]! := by
          rw [h_r3_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 8 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r3.val[9]! = out.val[9]! := by
          rw [h_r3_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 9 (by decide) (by decide) (by decide)]
        have h_fe := h_r4_fe_e
        simp only [] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[8]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[8]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[8]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[8]!)
                  ((lift_chunk_mont rhs).val[8]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[9]!)
                    ((lift_chunk_mont rhs).val[9]!))
                  (lift_fe_mont zeta2)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_8 : (lift_chunk_mont lhs).val[8]!
            = lift_fe_mont (lhs.elements.val[8]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[8]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 8 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 8 (by rw [h_l]; decide)]
        have h_lcm_lhs_9 : (lift_chunk_mont lhs).val[9]!
            = lift_fe_mont (lhs.elements.val[9]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[9]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 9 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 9 (by rw [h_l]; decide)]
        have h_lcm_rhs_8 : (lift_chunk_mont rhs).val[8]!
            = lift_fe_mont (rhs.elements.val[8]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[8]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 8 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 8 (by rw [h_l]; decide)]
        have h_lcm_rhs_9 : (lift_chunk_mont rhs).val[9]!
            = lift_fe_mont (rhs.elements.val[9]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[9]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 9 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 9 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_8, h_lcm_lhs_9, h_lcm_rhs_8, h_lcm_rhs_9]
      · -- Lane 9: touched by call 4 (zeta2, odd).
        have h_r7_at_lane : r7.val[9]! = r4.val[9]! := by
          rw [h_r7_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 9 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r3.val[8]! = out.val[8]! := by
          rw [h_r3_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 8 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 8 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r3.val[9]! = out.val[9]! := by
          rw [h_r3_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 9 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 9 (by decide) (by decide) (by decide)]
        have h_fe := h_r4_fe_o
        simp only [] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[9]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[9]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[9]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[8]!)
                  ((lift_chunk_mont rhs).val[9]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[9]!)
                  ((lift_chunk_mont rhs).val[8]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_8 : (lift_chunk_mont lhs).val[8]!
            = lift_fe_mont (lhs.elements.val[8]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[8]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 8 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 8 (by rw [h_l]; decide)]
        have h_lcm_lhs_9 : (lift_chunk_mont lhs).val[9]!
            = lift_fe_mont (lhs.elements.val[9]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[9]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 9 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 9 (by rw [h_l]; decide)]
        have h_lcm_rhs_8 : (lift_chunk_mont rhs).val[8]!
            = lift_fe_mont (rhs.elements.val[8]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[8]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 8 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 8 (by rw [h_l]; decide)]
        have h_lcm_rhs_9 : (lift_chunk_mont rhs).val[9]!
            = lift_fe_mont (rhs.elements.val[9]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[9]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 9 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 9 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_8, h_lcm_lhs_9, h_lcm_rhs_8, h_lcm_rhs_9]
      · -- Lane 10: touched by call 5 (nzeta2, even).
        have h_r7_at_lane : r7.val[10]! = r5.val[10]! := by
          rw [h_r7_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 10 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r4.val[10]! = out.val[10]! := by
          rw [h_r4_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 10 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r4.val[11]! = out.val[11]! := by
          rw [h_r4_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 11 (by decide) (by decide) (by decide)]
        have h_fe := h_r5_fe_e
        simp only [] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_n2_fe] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[10]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[10]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[10]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[10]!)
                  ((lift_chunk_mont rhs).val[10]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[11]!)
                    ((lift_chunk_mont rhs).val[11]!))
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta2))) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_10 : (lift_chunk_mont lhs).val[10]!
            = lift_fe_mont (lhs.elements.val[10]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[10]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 10 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 10 (by rw [h_l]; decide)]
        have h_lcm_lhs_11 : (lift_chunk_mont lhs).val[11]!
            = lift_fe_mont (lhs.elements.val[11]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[11]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 11 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 11 (by rw [h_l]; decide)]
        have h_lcm_rhs_10 : (lift_chunk_mont rhs).val[10]!
            = lift_fe_mont (rhs.elements.val[10]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[10]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 10 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 10 (by rw [h_l]; decide)]
        have h_lcm_rhs_11 : (lift_chunk_mont rhs).val[11]!
            = lift_fe_mont (rhs.elements.val[11]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[11]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 11 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 11 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_10, h_lcm_lhs_11, h_lcm_rhs_10, h_lcm_rhs_11]
      · -- Lane 11: touched by call 5 (nzeta2, odd).
        have h_r7_at_lane : r7.val[11]! = r5.val[11]! := by
          rw [h_r7_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r6_unc' 11 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r4.val[10]! = out.val[10]! := by
          rw [h_r4_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 10 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 10 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r4.val[11]! = out.val[11]! := by
          rw [h_r4_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 11 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 11 (by decide) (by decide) (by decide)]
        have h_fe := h_r5_fe_o
        simp only [] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[11]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[11]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[11]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[10]!)
                  ((lift_chunk_mont rhs).val[11]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[11]!)
                  ((lift_chunk_mont rhs).val[10]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_10 : (lift_chunk_mont lhs).val[10]!
            = lift_fe_mont (lhs.elements.val[10]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[10]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 10 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 10 (by rw [h_l]; decide)]
        have h_lcm_lhs_11 : (lift_chunk_mont lhs).val[11]!
            = lift_fe_mont (lhs.elements.val[11]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[11]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 11 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 11 (by rw [h_l]; decide)]
        have h_lcm_rhs_10 : (lift_chunk_mont rhs).val[10]!
            = lift_fe_mont (rhs.elements.val[10]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[10]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 10 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 10 (by rw [h_l]; decide)]
        have h_lcm_rhs_11 : (lift_chunk_mont rhs).val[11]!
            = lift_fe_mont (rhs.elements.val[11]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[11]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 11 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 11 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_10, h_lcm_lhs_11, h_lcm_rhs_10, h_lcm_rhs_11]
      · -- Lane 12: touched by call 6 (zeta3, even).
        have h_r7_at_lane : r7.val[12]! = r6.val[12]! := by
          rw [h_r7_unc' 12 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r5.val[12]! = out.val[12]! := by
          rw [h_r5_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 12 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r5.val[13]! = out.val[13]! := by
          rw [h_r5_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 13 (by decide) (by decide) (by decide)]
        have h_fe := h_r6_fe_e
        simp only [] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[12]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[12]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[12]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[12]!)
                  ((lift_chunk_mont rhs).val[12]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[13]!)
                    ((lift_chunk_mont rhs).val[13]!))
                  (lift_fe_mont zeta3)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_12 : (lift_chunk_mont lhs).val[12]!
            = lift_fe_mont (lhs.elements.val[12]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[12]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 12 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 12 (by rw [h_l]; decide)]
        have h_lcm_lhs_13 : (lift_chunk_mont lhs).val[13]!
            = lift_fe_mont (lhs.elements.val[13]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[13]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 13 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 13 (by rw [h_l]; decide)]
        have h_lcm_rhs_12 : (lift_chunk_mont rhs).val[12]!
            = lift_fe_mont (rhs.elements.val[12]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[12]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 12 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 12 (by rw [h_l]; decide)]
        have h_lcm_rhs_13 : (lift_chunk_mont rhs).val[13]!
            = lift_fe_mont (rhs.elements.val[13]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[13]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 13 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 13 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_12, h_lcm_lhs_13, h_lcm_rhs_12, h_lcm_rhs_13]
      · -- Lane 13: touched by call 6 (zeta3, odd).
        have h_r7_at_lane : r7.val[13]! = r6.val[13]! := by
          rw [h_r7_unc' 13 (by decide) (by decide) (by decide)]
        rw [h_r7_at_lane]
        have h_src_at_even : r5.val[12]! = out.val[12]! := by
          rw [h_r5_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 12 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 12 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r5.val[13]! = out.val[13]! := by
          rw [h_r5_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 13 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 13 (by decide) (by decide) (by decide)]
        have h_fe := h_r6_fe_o
        simp only [] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[13]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[13]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[13]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[12]!)
                  ((lift_chunk_mont rhs).val[13]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[13]!)
                  ((lift_chunk_mont rhs).val[12]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_12 : (lift_chunk_mont lhs).val[12]!
            = lift_fe_mont (lhs.elements.val[12]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[12]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 12 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 12 (by rw [h_l]; decide)]
        have h_lcm_lhs_13 : (lift_chunk_mont lhs).val[13]!
            = lift_fe_mont (lhs.elements.val[13]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[13]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 13 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 13 (by rw [h_l]; decide)]
        have h_lcm_rhs_12 : (lift_chunk_mont rhs).val[12]!
            = lift_fe_mont (rhs.elements.val[12]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[12]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 12 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 12 (by rw [h_l]; decide)]
        have h_lcm_rhs_13 : (lift_chunk_mont rhs).val[13]!
            = lift_fe_mont (rhs.elements.val[13]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[13]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 13 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 13 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_12, h_lcm_lhs_13, h_lcm_rhs_12, h_lcm_rhs_13]
      · -- Lane 14: touched by call 7 (nzeta3, even).
        have h_src_at_even : r6.val[14]! = out.val[14]! := by
          rw [h_r6_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 14 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r6.val[15]! = out.val[15]! := by
          rw [h_r6_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 15 (by decide) (by decide) (by decide)]
        have h_fe := h_r7_fe_e
        simp only [] at h_fe
        rw [h_src_at_even] at h_fe
        rw [h_n3_fe] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[14]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[14]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[14]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[14]!)
                  ((lift_chunk_mont rhs).val[14]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((lift_chunk_mont lhs).val[15]!)
                    ((lift_chunk_mont rhs).val[15]!))
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe_mont zeta3))) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_14 : (lift_chunk_mont lhs).val[14]!
            = lift_fe_mont (lhs.elements.val[14]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[14]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 14 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 14 (by rw [h_l]; decide)]
        have h_lcm_lhs_15 : (lift_chunk_mont lhs).val[15]!
            = lift_fe_mont (lhs.elements.val[15]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[15]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 15 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 15 (by rw [h_l]; decide)]
        have h_lcm_rhs_14 : (lift_chunk_mont rhs).val[14]!
            = lift_fe_mont (rhs.elements.val[14]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[14]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 14 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 14 (by rw [h_l]; decide)]
        have h_lcm_rhs_15 : (lift_chunk_mont rhs).val[15]!
            = lift_fe_mont (rhs.elements.val[15]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[15]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 15 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 15 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_14, h_lcm_lhs_15, h_lcm_rhs_14, h_lcm_rhs_15]
      · -- Lane 15: touched by call 7 (nzeta3, odd).
        have h_src_at_even : r6.val[14]! = out.val[14]! := by
          rw [h_r6_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 14 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 14 (by decide) (by decide) (by decide)]
        have h_src_at_odd : r6.val[15]! = out.val[15]! := by
          rw [h_r6_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r5_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r4_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r3_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r2_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r1_unc' 15 (by decide) (by decide) (by decide)]
          rw [h_r0_unc' 15 (by decide) (by decide) (by decide)]
        have h_fe := h_r7_fe_o
        simp only [] at h_fe
        rw [h_src_at_odd] at h_fe
        rw [h_fe]
        have h_red_out : (Spec.chunk_reducing_from_i32_array_pure out).val[15]!
            = Spec.mont_reduce_pure (lift_fe_int (out.val[15]!).val) := by
          unfold Spec.chunk_reducing_from_i32_array_pure
          rfl
        rw [h_red_out]
        have h_red_no_acc : (Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont lhs) (lift_chunk_mont rhs)
                              (lift_fe_mont zeta0) (lift_fe_mont zeta1)
                              (lift_fe_mont zeta2) (lift_fe_mont zeta3)).val[15]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[14]!)
                  ((lift_chunk_mont rhs).val[15]!))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk_mont lhs).val[15]!)
                  ((lift_chunk_mont rhs).val[14]!)) := by
          unfold Spec.ntt_multiply_pure_no_acc
          rfl
        rw [h_red_no_acc]
        have h_lcm_lhs_14 : (lift_chunk_mont lhs).val[14]!
            = lift_fe_mont (lhs.elements.val[14]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[14]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 14 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 14 (by rw [h_l]; decide)]
        have h_lcm_lhs_15 : (lift_chunk_mont lhs).val[15]!
            = lift_fe_mont (lhs.elements.val[15]!) := by
          unfold lift_chunk_mont
          have h_l : lhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
          show (lhs.elements.val.map lift_fe_mont)[15]! = _
          have h_ml : (lhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (lhs.elements.val.map lift_fe_mont) 15 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos lhs.elements.val 15 (by rw [h_l]; decide)]
        have h_lcm_rhs_14 : (lift_chunk_mont rhs).val[14]!
            = lift_fe_mont (rhs.elements.val[14]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[14]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 14 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 14 (by rw [h_l]; decide)]
        have h_lcm_rhs_15 : (lift_chunk_mont rhs).val[15]!
            = lift_fe_mont (rhs.elements.val[15]!) := by
          unfold lift_chunk_mont
          have h_l : rhs.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
          show (rhs.elements.val.map lift_fe_mont)[15]! = _
          have h_ml : (rhs.elements.val.map lift_fe_mont).length = 16 := by
            rw [List.length_map]; exact h_l
          rw [getElem!_pos (rhs.elements.val.map lift_fe_mont) 15 (by rw [h_ml]; decide)]
          rw [List.getElem_map]
          rw [getElem!_pos rhs.elements.val 15 (by rw [h_l]; decide)]
        rw [h_lcm_lhs_14, h_lcm_lhs_15, h_lcm_rhs_14, h_lcm_rhs_15]


/-- Algebraic POST predicate for the L6.3 polynomial-level NTT
    multiply. Relates the resulting I32 accumulator array `r` to the
    polynomial inputs and the initial accumulator state via a per-chunk
    × per-lane equation in Mont-domain `FieldElement` space:

      `mont_reduce_pure (lift_fe_int r[16j+ℓ])`
        `= mont_reduce_pure (lift_fe_int accumulator[16j+ℓ])`
          `+ no_acc_product j ℓ`

    where the per-chunk product `no_acc_product j ℓ` is the ℓ-th lane
    of `Spec.ntt_multiply_pure_no_acc` applied to Mont-domain lifts of
    the j-th coefficient vectors and the four zetas at
    `Spec.zeta_at (64 + 4j + {0,1,2,3})`.

    Composes the L2.8 per-chunk POST (`ntt_multiply_base_case_post`)
    via the chunk_add_pure decomposition baked into
    `ntt_multiply_base_case_alg`: at each j ∈ 0..15, applying L2.8 to
    the 16-lane window `[16j..16(j+1)]` gives the per-chunk equation
    `chunk_reducing_from_i32_array_pure r_chunk =
      chunk_add_pure (chunk_reducing_from_i32_array_pure acc_chunk)
                     (ntt_multiply_pure_no_acc ...)`,
    which extracts per-lane to the equation above (since
    `chunk_reducing_from_i32_array_pure x .val[ℓ] = mont_reduce_pure
    (lift_fe_int (x.val[ℓ]!).val)` definitionally). -/
noncomputable def accumulating_ntt_multiply_poly_post
    (myself rhs : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (accumulator r : Std.Array Std.I32 256#usize) : Prop :=
  ∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
    Spec.mont_reduce_pure (lift_fe_int (r.val[16 * j + ℓ]!).val)
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          (Spec.mont_reduce_pure (lift_fe_int (accumulator.val[16 * j + ℓ]!).val))
          ((Spec.ntt_multiply_pure_no_acc
              (lift_chunk_mont (myself.coefficients.val[j]!))
              (lift_chunk_mont (rhs.coefficients.val[j]!))
              (Spec.zeta_at (64 + 4 * j))
              (Spec.zeta_at (64 + 4 * j + 1))
              (Spec.zeta_at (64 + 4 * j + 2))
              (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!)

namespace UseCacheFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Step-local accumulator: 256-lane `I32` array. -/
abbrev Acc := Std.Array Std.I32 256#usize

abbrev Poly :=
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- FC loop invariant for `accumulating_ntt_multiply_loop`. Per-lane:
    * (a) Touched chunks (`j < k`): per-lane FC equation against L2.8's
          `Spec.ntt_multiply_pure_no_acc` plus initial accumulator.
    * (b) Chunks `j ≥ k`: per-lane unchanged from `acc_init`.
    * (c) Universal: per-lane bound — `|acc[n]| ≤ |acc_init[n]| + 2^25`
          for touched lanes; `acc[n] = acc_init[n]` (hence bound 0) for
          untouched. We encode the bound directly over all lanes since
          (c) ⇒ touched case bound. -/
def inv (myself rhs : Poly) (acc_init : Acc) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    (∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
      Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val)
        = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))
            ((Spec.ntt_multiply_pure_no_acc
                (lift_chunk_mont (myself.coefficients.val[j]!))
                (lift_chunk_mont (rhs.coefficients.val[j]!))
                (Spec.zeta_at (64 + 4 * j))
                (Spec.zeta_at (64 + 4 * j + 1))
                (Spec.zeta_at (64 + 4 * j + 2))
                (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 → ∀ ℓ : Nat, ℓ < 16 →
        acc.val[16 * j + ℓ]! = acc_init.val[16 * j + ℓ]!)
    ∧ (∀ n : Nat, n < 256 →
        (acc.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + 2^25))

/-- Step-post for `loop_range_spec_usize`. -/
def step_post (myself rhs : Poly) (acc_init : Acc) (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv myself rhs acc_init iter'.start acc').holds
  | .done y => (inv myself rhs acc_init 16#usize y).holds

end UseCacheFC

/-- Array sub-slice extraction via `index_mut` over a `Range Usize`,
    in `.ok`-form. Mirrors `slice_index_range_ok_eq_fc` but for
    `Std.Array`: routes through `Array.to_slice_mut` to obtain a
    sub-slice `s` plus a write-back closure satisfying
    `(back s').val = a.val.setSlice! r.start.val s'.val` whenever `s'`
    has length `r.end.val - r.start.val`. -/
theorem array_index_mut_range_ok_eq_fc
    {T : Type} {N : Std.Usize} (a : Std.Array T N)
    (r : CoreModels.core.ops.range.Range Std.Usize)
    (h0 : r.start.val ≤ r.end.val) (h1 : r.end.val ≤ a.val.length) :
    ∃ (s : Slice T) (back : Slice T → Std.Array T N),
      core.Array.Insts.CoreOpsIndexIndexMut.index_mut
        (core.Slice.Insts.CoreOpsIndexIndexMut
          (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T))
        a { start := r.start, «end» := r.end } = .ok (s, back)
      ∧ s.val = a.val.slice r.start.val r.end.val
      ∧ s.val.length = r.end.val - r.start.val
      ∧ (∀ s' : Slice T, s'.val.length = r.end.val - r.start.val →
          (back s').val = a.val.setSlice! r.start.val s'.val) := by
  -- Unfold the Array-level index_mut to the to_slice_mut + slice index_mut composition.
  set a_slice : Slice T := Aeneas.Std.Array.to_slice a with ha_slice_def
  have h_a_slice_val : a_slice.val = a.val :=
    Aeneas.Std.Array.val_to_slice a
  have h_a_slice_len : a_slice.val.length = a.val.length := by rw [h_a_slice_val]
  have h1' : r.end.val ≤ a_slice.val.length := by rw [h_a_slice_len]; exact h1
  -- Slice-level index_mut over the same range.
  have hT := libcrux_iot_ml_kem.Util.SliceSpecs.core_models_Slice_Insts_index_mut_RangeUsize_spec
              (T := T) a_slice
              ({ start := r.start, «end» := r.end } : CoreModels.core.ops.range.Range Std.Usize)
              h0 h1'
  obtain ⟨p, h_p_eq, h_p_post⟩ := triple_exists_ok_fc hT
  obtain ⟨h_p_val, h_p_len, h_p_back⟩ := h_p_post
  -- The Array-level closure: fun o => Array.from_slice a (slice_back o).
  refine ⟨p.1, fun o => Aeneas.Std.Array.from_slice a (p.2 o), ?_, ?_, ?_, ?_⟩
  · -- The Array index_mut reduces to `do let (s, back) ← Slice.index_mut ...; ok (s, ...)`.
    unfold core.Array.Insts.CoreOpsIndexIndexMut.index_mut
    -- to_slice_mut := (to_slice a, from_slice a).
    show (do
            let p ← core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
              (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T)
              a_slice { start := r.start, «end» := r.end }
            .ok (p.1, fun o => Aeneas.Std.Array.from_slice a (p.2 o)))
          = .ok (p.1, fun o => Aeneas.Std.Array.from_slice a (p.2 o))
    rw [h_p_eq]; rfl
  · -- Sub-slice val.
    rw [h_p_val]; rw [h_a_slice_val]
  · -- Sub-slice length.
    exact h_p_len
  · -- Write-back: `(from_slice a (slice_back s')).val = a.val.setSlice! r.start.val s'.val`.
    intro s' hs'_len
    have h_back_val : (p.2 s').val = a_slice.val.setSlice! r.start.val s'.val := h_p_back s'
    have h_back_len : (p.2 s').val.length = N.val := by
      rw [h_back_val, h_a_slice_val, List.length_setSlice!]
      exact Std.Array.length_eq a
    have h_from_slice_val :
        (Aeneas.Std.Array.from_slice a (p.2 s')).val = (p.2 s').val :=
      Aeneas.Std.Array.from_slice_val a (p.2 s') h_back_len
    rw [h_from_slice_val, h_back_val, h_a_slice_val]

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for
    `polynomial.PolynomialRingElement.accumulating_ntt_multiply`. -/
theorem accumulating_ntt_multiply_poly_step_lemma_fc
    (myself rhs : UseCacheFC.Poly) (acc_init : UseCacheFC.Acc)
    (h_self : ∀ i : Fin 16, ∀ j : Fin 16,
        ((myself.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_rhs : ∀ i : Fin 16, ∀ j : Fin 16,
        ((rhs.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_acc_bnd : ∀ n : Fin 256, (acc_init.val[n.val]!).val.natAbs ≤ 2^30)
    (acc : UseCacheFC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (UseCacheFC.inv myself rhs acc_init k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_loop.body
      (vectortraitsOperationsInst := portable_ops_inst) myself rhs
      { start := k, «end» := 16#usize } acc
    ⦃ ⇓ r => ⌜ UseCacheFC.step_post myself rhs acc_init k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_acc_len : acc.val.length = 256 :=
    (Std.Array.length_eq acc)
  have h_acc_init_len : acc_init.val.length = 256 :=
    (Std.Array.length_eq acc_init)
  have h_self_coef_len : myself.coefficients.length = 16 :=
    Std.Array.length_eq _
  have h_rhs_coef_len : rhs.coefficients.length = 16 :=
    Std.Array.length_eq _
  obtain ⟨h_acc_done, h_acc_undone, h_acc_bnd_rel⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- `Some i = k` branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s_iter, hs_val_eq, h_iter_some⟩ :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_some_eq k h_lt
    -- (1) t := self.coefficients[k] and t1 := rhs.coefficients[k].
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      myself.coefficients.val[k.val]! with ht_def
    set t1 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      rhs.coefficients.val[k.val]! with ht1_def
    have h_idx_t : Aeneas.Std.Array.index_usize myself.coefficients k = .ok t :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq myself.coefficients k
        (by rw [h_self_coef_len]; exact hk_16)
    have h_idx_t1 : Aeneas.Std.Array.index_usize rhs.coefficients k = .ok t1 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq rhs.coefficients k
        (by rw [h_rhs_coef_len]; exact hk_16)
    -- (2) i1 := k * 16, i2 := k + 1, i3 := i2 * 16.
    have hi1_max : k.val * (16#usize : Std.Usize).val ≤ Std.Usize.max := by
      have hk_15 : k.val ≤ 15 := by omega
      have hum : (16#usize : Std.Usize).val = 16 := rfl
      rw [hum]
      have h1 : k.val * 16 ≤ 15 * 16 := Nat.mul_le_mul_right 16 hk_15
      have : (15 * 16 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i1, hi1_eq, hi1_val⟩ := usize_mul_ok_eq_fc k 16#usize hi1_max
    have hi1_val_eq : i1.val = 16 * k.val := by
      have hum : (16#usize : Std.Usize).val = 16 := rfl
      rw [hi1_val, hum]; omega
    have hi2_max : k.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      have hk_15 : k.val ≤ 15 := by omega
      have hum : (1#usize : Std.Usize).val = 1 := rfl
      rw [hum]
      have : (16 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i2, hi2_eq, hi2_val⟩ := usize_add_ok_eq_fc k 1#usize hi2_max
    have hi2_val_eq : i2.val = k.val + 1 := by
      have hum : (1#usize : Std.Usize).val = 1 := rfl
      rw [hi2_val, hum]
    have hi3_max : i2.val * (16#usize : Std.Usize).val ≤ Std.Usize.max := by
      have hum : (16#usize : Std.Usize).val = 16 := rfl
      rw [hum, hi2_val_eq]
      have : k.val + 1 ≤ 16 := by omega
      have h1 : (k.val + 1) * 16 ≤ 16 * 16 := Nat.mul_le_mul_right 16 this
      have : (16 * 16 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i3, hi3_eq, hi3_val⟩ := usize_mul_ok_eq_fc i2 16#usize hi3_max
    have hi3_val_eq : i3.val = 16 * (k.val + 1) := by
      have hum : (16#usize : Std.Usize).val = 16 := rfl
      rw [hi3_val, hi2_val_eq, hum]; omega
    -- (3) Sub-slice via Array index_mut RangeUsize.
    have h0_le : i1.val ≤ i3.val := by rw [hi1_val_eq, hi3_val_eq]; omega
    have hi3_le : i3.val ≤ acc.val.length := by
      rw [h_acc_len, hi3_val_eq]
      have : k.val + 1 ≤ 16 := by omega
      have h1 : 16 * (k.val + 1) ≤ 16 * 16 := Nat.mul_le_mul_left _ this
      omega
    obtain ⟨s, back, h_imt_eq, h_s_val_eq, h_s_len_eq, h_back_eq⟩ :=
      array_index_mut_range_ok_eq_fc acc
        ({ start := i1, «end» := i3 } : CoreModels.core.ops.range.Range Std.Usize)
        h0_le hi3_le
    have h_s_len16 : s.length = 16 := by
      show s.val.length = 16
      rw [h_s_len_eq]
      show i3.val - i1.val = 16
      rw [hi3_val_eq, hi1_val_eq]; omega
    -- Per-lane lookup: s.val[ℓ]! = acc.val[16*k + ℓ]!.
    have h_s_lane : ∀ ℓ : Nat, ℓ < 16 →
        s.val[ℓ]! = acc.val[16 * k.val + ℓ]! := by
      intro ℓ hℓ
      rw [h_s_val_eq]
      have h_idx_lt : i1.val + ℓ < i3.val := by
        rw [hi1_val_eq, hi3_val_eq]; omega
      have h_bnd : i3.val ≤ acc.val.length ∧ i1.val + ℓ < i3.val := ⟨hi3_le, h_idx_lt⟩
      rw [List.getElem!_slice i1.val i3.val ℓ acc.val h_bnd]
      rw [hi1_val_eq]
    -- The lanes [16k, 16(k+1)) are untouched in `acc` (j ≥ k).
    have h_s_lane_init : ∀ ℓ : Nat, ℓ < 16 →
        s.val[ℓ]! = acc_init.val[16 * k.val + ℓ]! := by
      intro ℓ hℓ
      rw [h_s_lane ℓ hℓ]
      exact h_acc_undone k.val (Nat.le_refl _) hk_16 ℓ hℓ
    -- (4) Per-lane bound on `s` (≤ 2^30 from h_acc_bnd).
    have h_s_bnd : ∀ k' : Fin 16, (s.val[k'.val]!).val.natAbs ≤ 2^30 := by
      intro k'
      rw [h_s_lane_init k'.val k'.isLt]
      have h_lt : 16 * k.val + k'.val < 256 := by
        have : k.val ≤ 15 := by omega
        have hk' : k'.val < 16 := k'.isLt
        have : 16 * k.val ≤ 16 * 15 := Nat.mul_le_mul_left 16 this
        omega
      exact h_acc_bnd ⟨16 * k.val + k'.val, h_lt⟩
    -- (5) Read 4 zetas via polynomial.zeta_eq_ok_fc.
    have hi4_max : (4#usize : Std.Usize).val * k.val ≤ Std.Usize.max := by
      have hk_15 : k.val ≤ 15 := by omega
      have hum : (4#usize : Std.Usize).val = 4 := rfl
      rw [hum]
      have : 4 * k.val ≤ 4 * 15 := Nat.mul_le_mul_left 4 hk_15
      have : (4 * 15 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i4, hi4_eq, hi4_val⟩ := usize_mul_ok_eq_fc 4#usize k hi4_max
    have hi4_val_eq : i4.val = 4 * k.val := by
      have hum : (4#usize : Std.Usize).val = 4 := rfl
      rw [hi4_val, hum]
    have hi5_max : (64#usize : Std.Usize).val + i4.val ≤ Std.Usize.max := by
      have hum : (64#usize : Std.Usize).val = 64 := rfl
      rw [hum, hi4_val_eq]
      have hk_15 : k.val ≤ 15 := by omega
      have : 4 * k.val ≤ 4 * 15 := Nat.mul_le_mul_left 4 hk_15
      have : (64 + 4 * 15 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    -- i5..i14 are 4 add-then-zeta sequences.
    obtain ⟨i5, hi5_eq, hi5_val⟩ := usize_add_ok_eq_fc 64#usize i4 hi5_max
    have hi5_val_eq : i5.val = 64 + 4 * k.val := by
      have hum : (64#usize : Std.Usize).val = 64 := rfl
      rw [hi5_val, hum, hi4_val_eq]
    have hi5_lt_128 : i5.val < 128 := by rw [hi5_val_eq]; omega
    obtain ⟨z0, hz0_eq, hz0_post⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc i5 hi5_lt_128)
    obtain ⟨hz0_val_eq, hz0_bnd, hz0_lift⟩ := hz0_post
    -- i8 := i5 + 1 (since i7 = i5 after the duplicate `64 + i4` rewrite).
    have hi8_max : i5.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      have hum : (1#usize : Std.Usize).val = 1 := rfl
      rw [hum, hi5_val_eq]
      have hk_15 : k.val ≤ 15 := by omega
      have : (64 + 4 * 15 + 1 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i8, hi8_eq, hi8_val⟩ := usize_add_ok_eq_fc i5 1#usize hi8_max
    have hi8_val_eq : i8.val = 64 + 4 * k.val + 1 := by
      have hum : (1#usize : Std.Usize).val = 1 := rfl
      rw [hi8_val, hi5_val_eq, hum]
    have hi8_lt_128 : i8.val < 128 := by rw [hi8_val_eq]; omega
    obtain ⟨z1, hz1_eq, hz1_post⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc i8 hi8_lt_128)
    obtain ⟨hz1_val_eq, hz1_bnd, hz1_lift⟩ := hz1_post
    have hi11_max : i5.val + (2#usize : Std.Usize).val ≤ Std.Usize.max := by
      have hum : (2#usize : Std.Usize).val = 2 := rfl
      rw [hum, hi5_val_eq]
      have hk_15 : k.val ≤ 15 := by omega
      have : (64 + 4 * 15 + 2 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i11, hi11_eq, hi11_val⟩ := usize_add_ok_eq_fc i5 2#usize hi11_max
    have hi11_val_eq : i11.val = 64 + 4 * k.val + 2 := by
      have hum : (2#usize : Std.Usize).val = 2 := rfl
      rw [hi11_val, hi5_val_eq, hum]
    have hi11_lt_128 : i11.val < 128 := by rw [hi11_val_eq]; omega
    obtain ⟨z2, hz2_eq, hz2_post⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc i11 hi11_lt_128)
    obtain ⟨hz2_val_eq, hz2_bnd, hz2_lift⟩ := hz2_post
    have hi14_max : i5.val + (3#usize : Std.Usize).val ≤ Std.Usize.max := by
      have hum : (3#usize : Std.Usize).val = 3 := rfl
      rw [hum, hi5_val_eq]
      have hk_15 : k.val ≤ 15 := by omega
      have : (64 + 4 * 15 + 3 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i14, hi14_eq, hi14_val⟩ := usize_add_ok_eq_fc i5 3#usize hi14_max
    have hi14_val_eq : i14.val = 64 + 4 * k.val + 3 := by
      have hum : (3#usize : Std.Usize).val = 3 := rfl
      rw [hi14_val, hi5_val_eq, hum]
    have hi14_lt_128 : i14.val < 128 := by rw [hi14_val_eq]; omega
    obtain ⟨z3, hz3_eq, hz3_post⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc i14 hi14_lt_128)
    obtain ⟨hz3_val_eq, hz3_bnd, hz3_lift⟩ := hz3_post
    -- (6) Apply L2.8 to get s1 satisfying ntt_multiply_base_case_post + bound.
    have h_t_lhs : ∀ j : Fin 16, (t.elements.val[j.val]!).val.natAbs ≤ 3328 := by
      intro j
      exact h_self ⟨k.val, hk_16⟩ j
    have h_t1_rhs : ∀ j : Fin 16, (t1.elements.val[j.val]!).val.natAbs ≤ 3328 := by
      intro j
      exact h_rhs ⟨k.val, hk_16⟩ j
    obtain ⟨s1, h_s1_eq, h_s1_len, h_s1_bnd, h_s1_post⟩ :=
      triple_exists_ok_fc
        (accumulating_ntt_multiply_fc t t1 s z0 z1 z2 z3 h_s_len16
          h_t_lhs h_t1_rhs hz0_bnd hz1_bnd hz2_bnd hz3_bnd h_s_bnd)
    -- s1's bound vs s lanes (s.val[k'] = acc_init[16k+k']).
    have h_s1_bnd_abs : ∀ k' : Nat, k' < 16 →
        (s1.val[k']!).val.natAbs ≤ (acc_init.val[16 * k.val + k']!).val.natAbs + 2^25 := by
      intro k' hk'
      have h_step_bnd := h_s1_bnd ⟨k', hk'⟩
      simp only at h_step_bnd
      rw [h_s_lane_init k' hk'] at h_step_bnd
      exact h_step_bnd
    -- (7) Compose acc1 := back s1.
    set acc1 : UseCacheFC.Acc := back s1 with hacc1_def
    have h_acc1_val : acc1.val = acc.val.setSlice! i1.val s1.val :=
      h_back_eq s1 (by show s1.val.length = i3.val - i1.val; rw [← h_s_len_eq];
                       show s1.length = s.length; rw [h_s1_len, h_s_len16])
    have h_acc1_len : acc1.val.length = 256 := by
      rw [h_acc1_val, List.length_setSlice!, h_acc_len]
    -- (8) Per-lane lookup of acc1 in the touched window: acc1[16k+ℓ] = s1[ℓ].
    have h_acc1_in : ∀ ℓ : Nat, ℓ < 16 →
        acc1.val[16 * k.val + ℓ]! = s1.val[ℓ]! := by
      intro ℓ hℓ
      rw [h_acc1_val]
      have h_get : (acc.val.setSlice! i1.val s1.val)[16 * k.val + ℓ]!
                    = s1.val[(16 * k.val + ℓ) - i1.val]! := by
        apply List.getElem!_setSlice!_middle
        refine ⟨?_, ?_, ?_⟩
        · rw [hi1_val_eq]; omega
        · rw [hi1_val_eq]
          have h_sub' : 16 * k.val + ℓ - 16 * k.val = ℓ := by omega
          rw [h_sub']
          show ℓ < s1.val.length
          have h_s1' : s1.val.length = 16 := h_s1_len
          rw [h_s1']; exact hℓ
        · rw [h_acc_len]
          have hk_15' : k.val ≤ 15 := by omega
          have h1 : 16 * k.val ≤ 16 * 15 := Nat.mul_le_mul_left 16 hk_15'
          omega
      rw [h_get]
      have h_sub : (16 * k.val + ℓ) - i1.val = ℓ := by
        rw [hi1_val_eq]; omega
      rw [h_sub]
    -- Outside the window: acc1[n] = acc[n].
    have h_acc1_out : ∀ n : Nat, n < 256 →
        (n < 16 * k.val ∨ 16 * (k.val + 1) ≤ n) →
        acc1.val[n]! = acc.val[n]! := by
      intro n hn hcases
      rw [h_acc1_val]
      rcases hcases with hlt | hge
      · -- n < 16 * k.val = i1.val.
        apply List.getElem!_setSlice!_prefix
        rw [hi1_val_eq]; exact hlt
      · -- 16 * (k.val + 1) ≤ n.
        apply List.getElem!_setSlice!_suffix
        rw [hi1_val_eq]
        have h_s1' : s1.val.length = 16 := h_s1_len
        rw [h_s1']
        have h_eq16 : 16 * k.val + 16 = 16 * (k.val + 1) := by ring
        rw [h_eq16]; exact hge
    -- (9) Body equation: the impl reduces to .ok (cont (..., acc1)).
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) myself rhs
          { start := k, «end» := 16#usize } acc
        = .ok (ControlFlow.cont (({ start := s_iter, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize), acc1)) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_loop.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp only [Aeneas.Std.bind_tc_ok]
      show ((do
              let t' ← Aeneas.Std.Array.index_usize myself.coefficients k
              let t1' ← Aeneas.Std.Array.index_usize rhs.coefficients k
              let i1' ← (k * 16#usize : Result Std.Usize)
              let i2' ← k + 1#usize
              let i3' ← i2' * 16#usize
              let (s', index_mut_back) ←
                core.Array.Insts.CoreOpsIndexIndexMut.index_mut
                  (core.Slice.Insts.CoreOpsIndexIndexMut
                    (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                      Std.I32)) acc { start := i1', «end» := i3' }
              let i4' ← 4#usize * k
              let i5' ← 64#usize + i4'
              let i6' ← libcrux_iot_ml_kem.polynomial.zeta i5'
              let i7' ← 64#usize + i4'
              let i8' ← i7' + 1#usize
              let i9' ← libcrux_iot_ml_kem.polynomial.zeta i8'
              let i10' ← 64#usize + i4'
              let i11' ← i10' + 2#usize
              let i12' ← libcrux_iot_ml_kem.polynomial.zeta i11'
              let i13' ← 64#usize + i4'
              let i14' ← i13' + 3#usize
              let i15' ← libcrux_iot_ml_kem.polynomial.zeta i14'
              let s1' ←
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations.accumulating_ntt_multiply
                  t' t1' s' i6' i9' i12' i15'
              .ok (ControlFlow.cont (({ start := s_iter, «end» := 16#usize }
                          : CoreModels.core.ops.range.Range Std.Usize), index_mut_back s1')))
            : Result _) = _
      rw [h_idx_t]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_t1]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi1_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi2_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi3_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi4_eq]; simp only [Aeneas.Std.bind_tc_ok]
      -- rw [hi5_eq] rewrites all four occurrences of `64#usize + i4` to `.ok i5`.
      rw [hi5_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hz0_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi8_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hz1_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi11_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hz2_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi14_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hz3_eq]; simp only [Aeneas.Std.bind_tc_ok]
      -- Now we have `vectortraitsOperationsInst.accumulating_ntt_multiply t t1 s z0 z1 z2 z3`.
      -- For portable_ops_inst, this reduces definitionally to vector.portable.ntt.acc_ntt_mult.
      show ((do
              let s1' ←
                libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply
                  t t1 s z0 z1 z2 z3
              .ok (ControlFlow.cont (({ start := s_iter, «end» := 16#usize }
                          : CoreModels.core.ops.range.Range Std.Usize), back s1')))
            : Result _) = _
      rw [h_s1_eq]
      rfl
    apply triple_of_ok_fc h_body
    show UseCacheFC.step_post myself rhs acc_init k
      (.cont (({ start := s_iter, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize), acc1))
    unfold UseCacheFC.step_post
    refine ⟨h_lt, rfl, hs_val_eq, ?_⟩
    show (UseCacheFC.inv myself rhs acc_init s_iter acc1).holds
    -- Build the three invariant conjuncts.
    have h_inv_pure :
        (∀ j : Nat, j < s_iter.val → ∀ ℓ : Nat, ℓ < 16 →
          Spec.mont_reduce_pure (lift_fe_int (acc1.val[16 * j + ℓ]!).val)
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))
                ((Spec.ntt_multiply_pure_no_acc
                    (lift_chunk_mont (myself.coefficients.val[j]!))
                    (lift_chunk_mont (rhs.coefficients.val[j]!))
                    (Spec.zeta_at (64 + 4 * j))
                    (Spec.zeta_at (64 + 4 * j + 1))
                    (Spec.zeta_at (64 + 4 * j + 2))
                    (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
        ∧ (∀ j : Nat, s_iter.val ≤ j → j < 16 → ∀ ℓ : Nat, ℓ < 16 →
            acc1.val[16 * j + ℓ]! = acc_init.val[16 * j + ℓ]!)
        ∧ (∀ n : Nat, n < 256 →
            (acc1.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + 2^25) := by
      refine ⟨?_, ?_, ?_⟩
      · -- (a) Touched-chunk FC.
        intro j hj ℓ hℓ
        rw [hs_val_eq] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k: chunk unchanged in acc, FC from inv.
          have h_in_range : 16 * j + ℓ < 16 * k.val := by
            have h1 : 16 * j + 16 ≤ 16 * k.val := by
              have : j + 1 ≤ k.val := by omega
              have : 16 * (j + 1) ≤ 16 * k.val := Nat.mul_le_mul_left 16 this
              omega
            omega
          have h_lt_256 : 16 * j + ℓ < 256 := by
            have : k.val ≤ 15 := by omega
            have : 16 * k.val ≤ 16 * 15 := Nat.mul_le_mul_left 16 this
            omega
          have h_acc1_eq_acc : acc1.val[16 * j + ℓ]! = acc.val[16 * j + ℓ]! :=
            h_acc1_out (16 * j + ℓ) h_lt_256 (Or.inl h_in_range)
          rw [h_acc1_eq_acc]
          exact h_acc_done j hj_lt_k ℓ hℓ
        · -- j = k: chunk = s1; unfold L2.8 POST.
          subst hj_eq_k
          rw [h_acc1_in ℓ hℓ]
          -- h_s1_post : ntt_multiply_base_case_post t t1 z0 z1 z2 z3 s s1.
          -- = Spec.chunk_reducing_from_i32_array_pure s1
          --   = ntt_multiply_base_case_alg ... (Spec.chunk_reducing_from_i32_array_pure s).
          unfold ntt_multiply_base_case_post at h_s1_post
          -- Per-lane unfold: (chunk_reducing_from_i32_array_pure s1).val[ℓ]
          --   = mont_reduce_pure (lift_fe_int s1.val[ℓ]!.val).
          -- And ntt_multiply_base_case_alg = chunk_add_pure ... (...).
          have h_lhs_val_eq :
              (Spec.chunk_reducing_from_i32_array_pure s1).val[ℓ]!
                = Spec.mont_reduce_pure (lift_fe_int (s1.val[ℓ]!).val) := by
            unfold Spec.chunk_reducing_from_i32_array_pure
            show ((List.range 16).map (fun i =>
                    Spec.mont_reduce_pure (lift_fe_int (s1.val[i]!).val)))[ℓ]! = _
            have h_len : ((List.range 16).map (fun i =>
                Spec.mont_reduce_pure (lift_fe_int (s1.val[i]!).val))).length = 16 := by simp
            rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
            rw [List.getElem_map, List.getElem_range]
          have h_rhs_val_eq :
              (ntt_multiply_base_case_alg
                (lift_chunk_mont t) (lift_chunk_mont t1)
                (lift_fe_mont z0) (lift_fe_mont z1)
                (lift_fe_mont z2) (lift_fe_mont z3)
                (Spec.chunk_reducing_from_i32_array_pure s)).val[ℓ]!
                = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                    ((Spec.chunk_reducing_from_i32_array_pure s).val[ℓ]!)
                    ((Spec.ntt_multiply_pure_no_acc
                        (lift_chunk_mont t) (lift_chunk_mont t1)
                        (lift_fe_mont z0) (lift_fe_mont z1)
                        (lift_fe_mont z2) (lift_fe_mont z3)).val[ℓ]!) := by
            unfold ntt_multiply_base_case_alg Spec.chunk_add_pure
            show ((List.range 16).map (fun i =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                ((Spec.chunk_reducing_from_i32_array_pure s).val[i]!)
                ((Spec.ntt_multiply_pure_no_acc
                  (lift_chunk_mont t) (lift_chunk_mont t1)
                  (lift_fe_mont z0) (lift_fe_mont z1)
                  (lift_fe_mont z2) (lift_fe_mont z3)).val[i]!)))[ℓ]! = _
            have h_len : ((List.range 16).map (fun i =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                ((Spec.chunk_reducing_from_i32_array_pure s).val[i]!)
                ((Spec.ntt_multiply_pure_no_acc
                  (lift_chunk_mont t) (lift_chunk_mont t1)
                  (lift_fe_mont z0) (lift_fe_mont z1)
                  (lift_fe_mont z2) (lift_fe_mont z3)).val[i]!))).length = 16 := by simp
            rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
            rw [List.getElem_map, List.getElem_range]
          have h_s_chunk_val :
              (Spec.chunk_reducing_from_i32_array_pure s).val[ℓ]!
                = Spec.mont_reduce_pure (lift_fe_int (s.val[ℓ]!).val) := by
            unfold Spec.chunk_reducing_from_i32_array_pure
            show ((List.range 16).map (fun i =>
                    Spec.mont_reduce_pure (lift_fe_int (s.val[i]!).val)))[ℓ]! = _
            have h_len : ((List.range 16).map (fun i =>
                Spec.mont_reduce_pure (lift_fe_int (s.val[i]!).val))).length = 16 := by simp
            rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
            rw [List.getElem_map, List.getElem_range]
          have h_chunk_eq :
              Spec.mont_reduce_pure (lift_fe_int (s1.val[ℓ]!).val)
                = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                    (Spec.mont_reduce_pure (lift_fe_int (s.val[ℓ]!).val))
                    ((Spec.ntt_multiply_pure_no_acc
                        (lift_chunk_mont t) (lift_chunk_mont t1)
                        (lift_fe_mont z0) (lift_fe_mont z1)
                        (lift_fe_mont z2) (lift_fe_mont z3)).val[ℓ]!) := by
            have h_eq : (Spec.chunk_reducing_from_i32_array_pure s1).val[ℓ]!
                  = (ntt_multiply_base_case_alg
                      (lift_chunk_mont t) (lift_chunk_mont t1)
                      (lift_fe_mont z0) (lift_fe_mont z1)
                      (lift_fe_mont z2) (lift_fe_mont z3)
                      (Spec.chunk_reducing_from_i32_array_pure s)).val[ℓ]! := by
              rw [h_s1_post]
            rw [h_lhs_val_eq] at h_eq
            rw [h_rhs_val_eq] at h_eq
            rw [h_s_chunk_val] at h_eq
            exact h_eq
          rw [h_chunk_eq]
          -- Now substitute s.val[ℓ]! = acc_init.val[16*k+ℓ]!.
          rw [h_s_lane_init ℓ hℓ]
          -- Match zeta indices.
          rw [hz0_lift, hz1_lift, hz2_lift, hz3_lift]
          rw [hi5_val_eq, hi8_val_eq, hi11_val_eq, hi14_val_eq]
      · -- (b) Untouched chunks: j ≥ k+1.
        intro j hj_ge hj_lt ℓ hℓ
        rw [hs_val_eq] at hj_ge
        have h_n_lt_256 : 16 * j + ℓ < 256 := by
          have : j ≤ 15 := by omega
          have : 16 * j ≤ 16 * 15 := Nat.mul_le_mul_left 16 this
          omega
        have h_ge_range : 16 * (k.val + 1) ≤ 16 * j + ℓ := by
          have : k.val + 1 ≤ j := hj_ge
          have : 16 * (k.val + 1) ≤ 16 * j := Nat.mul_le_mul_left 16 this
          omega
        have h_acc1_eq_acc : acc1.val[16 * j + ℓ]! = acc.val[16 * j + ℓ]! :=
          h_acc1_out (16 * j + ℓ) h_n_lt_256 (Or.inr h_ge_range)
        rw [h_acc1_eq_acc]
        exact h_acc_undone j (by omega) hj_lt ℓ hℓ
      · -- (c) Universal bound.
        intro n hn
        by_cases hcase : 16 * k.val ≤ n ∧ n < 16 * (k.val + 1)
        · -- Inside the touched window.
          obtain ⟨hge, hlt⟩ := hcase
          have hn_decomp : n = 16 * k.val + (n - 16 * k.val) := by omega
          have hn_off_lt : n - 16 * k.val < 16 := by omega
          have h_acc1_n : acc1.val[n]! = s1.val[n - 16 * k.val]! := by
            conv_lhs => rw [hn_decomp]
            exact h_acc1_in (n - 16 * k.val) hn_off_lt
          rw [h_acc1_n]
          have h_bnd_at_off := h_s1_bnd_abs (n - 16 * k.val) hn_off_lt
          have h_acc_init_n : acc_init.val[16 * k.val + (n - 16 * k.val)]!
                              = acc_init.val[n]! := by
            congr 1; omega
          rw [h_acc_init_n] at h_bnd_at_off
          exact h_bnd_at_off
        · -- Outside the touched window.
          have h_outside : n < 16 * k.val ∨ 16 * (k.val + 1) ≤ n := by
            by_contra hc
            push Not at hc
            exact hcase ⟨hc.1, hc.2⟩
          have h_acc1_eq_acc : acc1.val[n]! = acc.val[n]! :=
            h_acc1_out n hn h_outside
          rw [h_acc1_eq_acc]
          exact h_acc_bnd_rel n hn
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ 16, done.
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) myself rhs
          { start := k, «end» := 16#usize } acc
        = .ok (ControlFlow.done acc) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_loop.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    apply triple_of_ok_fc h_body
    show UseCacheFC.step_post myself rhs acc_init k (.done acc)
    unfold UseCacheFC.step_post
    show (UseCacheFC.inv myself rhs acc_init 16#usize acc).holds
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        (∀ j : Nat, j < (16#usize : Std.Usize).val → ∀ ℓ : Nat, ℓ < 16 →
          Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val)
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))
                ((Spec.ntt_multiply_pure_no_acc
                    (lift_chunk_mont (myself.coefficients.val[j]!))
                    (lift_chunk_mont (rhs.coefficients.val[j]!))
                    (Spec.zeta_at (64 + 4 * j))
                    (Spec.zeta_at (64 + 4 * j + 1))
                    (Spec.zeta_at (64 + 4 * j + 2))
                    (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 → ∀ ℓ : Nat, ℓ < 16 →
            acc.val[16 * j + ℓ]! = acc_init.val[16 * j + ℓ]!)
        ∧ (∀ n : Nat, n < 256 →
            (acc.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + 2^25) := by
      refine ⟨?_, ?_, ?_⟩
      · intro j hj ℓ hℓ; rw [h16] at hj
        apply h_acc_done j _ ℓ hℓ; rw [hk_eq]; exact hj
      · intro j hj_ge hj_lt ℓ hℓ
        rw [h16] at hj_ge
        apply h_acc_undone j _ hj_lt ℓ hℓ; rw [hk_eq]; exact hj_ge
      · intro n hn; exact h_acc_bnd_rel n hn
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 4000000 in
/-- L6.3 — `polynomial.PolynomialRingElement.accumulating_ntt_multiply`:
    polynomial-level NTT-domain multiply. Wraps L2.8 across all 16
    vector chunks, computing the running sum into a 256-element I32
    accumulator (one degree-2 polynomial multiply per chunk).

    The impl iterates 16 times over
    `vectortraitsOperationsInst.accumulating_ntt_multiply`, slicing
    the accumulator as `[i*16 .. (i+1)*16]` per iteration and reading
    zetas from `polynomial.zeta(64 + 4i + {0,1,2,3})`.

    POST defers algebraic shape to `accumulating_ntt_multiply_poly_post`.
    Preconditions: input polys canonical (all coefficients
    `natAbs ≤ 3328`), AND each accumulator lane bounded by `2^30`
    (propagates to the L2.8 per-chunk PRE — each L2.8 call's `out`
    slice is the corresponding 16-lane window into `accumulator`).

    POST adds a relative bound conjunct (`|r[n]| ≤ |accumulator[n]| +
    2^25`) propagating L2.8's relative bound through the 16-iter
    chunk loop. Each of the 256 lanes is updated exactly once (one
    binomial step per lane), so the per-lane delta is bounded by
    a single L2.8 step's growth. Mirrors the inverse-NTT
    bound-infra cascade.

    [F*-port: Libcrux_ml_kem.Polynomial.ntt_multiply (Polynomial.fst:
     853-915). WARNING: upstream `lemma_ntt_multiply_chunk_commutes`
     (Chunk.fst:1311) is `assume val` — Lean must PROVE the
     per-vector wrap (L6.3a sub-unit).] -/
@[spec]
theorem accumulating_ntt_multiply_poly_fc
    (myself rhs : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (accumulator : Std.Array Std.I32 256#usize)
    (h_self : ∀ i : Fin 16, ∀ j : Fin 16,
        ((myself.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_rhs : ∀ i : Fin 16, ∀ j : Fin 16,
        ((rhs.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_acc_bnd : ∀ n : Fin 256, (accumulator.val[n.val]!).val.natAbs ≤ 2^30) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply
      (vectortraitsOperationsInst := portable_ops_inst)
      myself rhs accumulator
    ⦃ ⇓ r => ⌜ (∀ n : Fin 256, (r.val[n.val]!).val.natAbs
                                ≤ (accumulator.val[n.val]!).val.natAbs + 2^25) ∧
              accumulating_ntt_multiply_poly_post
                myself rhs accumulator r ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply
  have h_vre : libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
                = .ok (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
    rfl
  rw [h_vre]; simp only [Aeneas.Std.bind_tc_ok]
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_loop
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) myself rhs iter1 acc1)
      (β := UseCacheFC.Acc)
      accumulator
      0#usize 16#usize
      (UseCacheFC.inv myself rhs accumulator)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (by
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, ?_⟩
        · intro j hj; exact absurd hj (Nat.not_lt_zero j)
        · intro _ _ _ _ _; trivial
        · intro n _; omega)
      ?_)
  · -- Post entailment: at k = 16, derive the locked POST.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (UseCacheFC.inv myself rhs accumulator 16#usize r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    have h_inv :
        (∀ j : Nat, j < (16#usize : Std.Usize).val → ∀ ℓ : Nat, ℓ < 16 →
          Spec.mont_reduce_pure (lift_fe_int (r.val[16 * j + ℓ]!).val)
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (Spec.mont_reduce_pure (lift_fe_int (accumulator.val[16 * j + ℓ]!).val))
                ((Spec.ntt_multiply_pure_no_acc
                    (lift_chunk_mont (myself.coefficients.val[j]!))
                    (lift_chunk_mont (rhs.coefficients.val[j]!))
                    (Spec.zeta_at (64 + 4 * j))
                    (Spec.zeta_at (64 + 4 * j + 1))
                    (Spec.zeta_at (64 + 4 * j + 2))
                    (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 → ∀ ℓ : Nat, ℓ < 16 →
            r.val[16 * j + ℓ]! = accumulator.val[16 * j + ℓ]!)
        ∧ (∀ n : Nat, n < 256 →
            (r.val[n]!).val.natAbs ≤ (accumulator.val[n]!).val.natAbs + 2^25) := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
             UseCacheFC.inv] using h_inv_holds
    obtain ⟨h_done, _h_undone, h_bnd⟩ := h_inv
    refine ⟨?_, ?_⟩
    · intro n; exact h_bnd n.val n.isLt
    · unfold accumulating_ntt_multiply_poly_post
      intro j hj ℓ hℓ
      have h16' : (16#usize : Std.Usize).val = 16 := rfl
      exact h_done j (by rw [h16']; exact hj) ℓ hℓ
  · -- Step entailment.
    intro acc k _h_ge h_le hinv
    have h_step :=
      accumulating_ntt_multiply_poly_step_lemma_fc myself rhs accumulator
        h_self h_rhs h_acc_bnd acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : UseCacheFC.step_post myself rhs accumulator k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [UseCacheFC.step_post] using hP
    · have hP : UseCacheFC.step_post myself rhs accumulator k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [UseCacheFC.step_post] using hP

/-! ## §L6.3c — Cache-variant polynomial-level Triple statements.

    Polynomial wrappers around L2.8d (`accumulating_ntt_multiply_fill_cache_fc`
    and `accumulating_ntt_multiply_use_cache_fc`). The impl loops over the
    16 chunks, dispatching each through the vector-level cache variant.

    Composition pattern (matrix-row reuse): `_fill_cache(A, B, _, _, cache)` sets
    the polynomial cache (16 chunks × 8 cache slots each), then multiple
    `_use_cache(A', B, _, _, cache)` calls reuse it with different first
    operands and the same `B`. This is the matrix `Aᵀ · r` and `A · s`
    pattern in L7.1 / L7.2 / L7.3.

    Cache POST predicate composes with the vector-level
    `Spec.ntt_multiply_cache_post` chunk-by-chunk: each of the 16 chunks
    of `cache.coefficients` stores per-pair `b·zeta` Mont-reduced products
    for that chunk's effective zetas at table positions
    `64 + 4j + {0,1,2,3}`. -/

/-- Polynomial-level cache POST predicate. For each chunk `j ∈ Fin 16` and
    each pair `i ∈ Fin 8`: `cache.coefficients[j].elements[i]` stores the
    Mont-reduced product `rhs.coefficients[j].elements[2i+1] · zeta_eff_i`
    where the four base zetas for chunk `j` are
    `Spec.zeta_at (64 + 4j + {0,1,2,3})`. Composes with the vector-level
    `Spec.ntt_multiply_cache_post` per chunk. -/
noncomputable def accumulating_ntt_multiply_poly_cache_post
    (rhs cache : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                   libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Prop :=
  ∀ j : Fin 16, ∀ i : Fin 8,
    ((cache.coefficients.val[j.val]!).elements.val[i.val]!).val.natAbs ≤ 3328
    ∧ lift_fe_mont ((cache.coefficients.val[j.val]!).elements.val[i.val]!)
        = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (lift_fe_mont ((rhs.coefficients.val[j.val]!).elements.val[2 * i.val + 1]!))
            (Spec.effective_zeta_fe i
              (Spec.zeta_at (64 + 4 * j.val))
              (Spec.zeta_at (64 + 4 * j.val + 1))
              (Spec.zeta_at (64 + 4 * j.val + 2))
              (Spec.zeta_at (64 + 4 * j.val + 3)))

namespace FillCacheFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

abbrev Acc := UseCacheFC.Acc
abbrev Poly := UseCacheFC.Poly

/-- 5-conjunct invariant for the fill_cache loop. -/
def inv (myself rhs : Poly) (acc_init : Acc) (cache_init : Poly) :
    Std.Usize → Acc → Poly → Result Prop :=
  fun k acc cache => pure (
    (∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
      Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val)
        = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))
            ((Spec.ntt_multiply_pure_no_acc
                (lift_chunk_mont (myself.coefficients.val[j]!))
                (lift_chunk_mont (rhs.coefficients.val[j]!))
                (Spec.zeta_at (64 + 4 * j))
                (Spec.zeta_at (64 + 4 * j + 1))
                (Spec.zeta_at (64 + 4 * j + 2))
                (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 → ∀ ℓ : Nat, ℓ < 16 →
        acc.val[16 * j + ℓ]! = acc_init.val[16 * j + ℓ]!)
    ∧ (∀ n : Nat, n < 256 →
        (acc.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + 2^25)
    ∧ (∀ j : Nat, j < k.val →
        Spec.ntt_multiply_cache_post
          (rhs.coefficients.val[j]!)
          libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * j]!
          libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * j + 1]!
          libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * j + 2]!
          libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * j + 3]!
          (cache.coefficients.val[j]!))
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        cache.coefficients.val[j]! = cache_init.coefficients.val[j]!))

/-- Step-post for `loop_range_spec_usize` over (acc, cache). -/
def step_post (myself rhs : Poly) (acc_init : Acc) (cache_init : Poly)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc × Poly) (Acc × Poly)) :
    Prop :=
  match r with
  | .cont (iter', acc', cache') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv myself rhs acc_init cache_init iter'.start acc' cache').holds
  | .done y => (inv myself rhs acc_init cache_init 16#usize y.1 y.2).holds

end FillCacheFC

-- Memory hygiene (rule 1 / SKILL §5.7 Idiom 2). Heavy POST predicates and
-- the namespace's `inv` / `step_post` are made locally irreducible across
-- the step lemma + outer Triple so that elaboration of
-- `apply triple_of_ok_fc h_body` (step) and `apply Std.Do.Triple.of_entails_right`
-- (outer) does not whnf-explode through the 5-conjunct invariant body or
-- the nested `∀ i : Fin 8` cache POST.
section L6_3c_fill_irreducible
attribute [local irreducible] Spec.ntt_multiply_cache_post
attribute [local irreducible] accumulating_ntt_multiply_poly_cache_post
attribute [local irreducible] ntt_multiply_base_case_post
attribute [local irreducible] Spec.chunk_reducing_from_i32_array_pure
attribute [local irreducible] lift_chunk_mont
attribute [local irreducible] Spec.ntt_multiply_pure_no_acc
attribute [local irreducible] ntt_multiply_base_case_alg
attribute [local irreducible] Spec.effective_zeta_fe

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for `_fill_cache` polynomial loop. Mirrors
    `accumulating_ntt_multiply_poly_step_lemma_fc` (L6.3 base,)
    but threads BOTH `acc` and `cache` through the ControlFlow. -/
theorem accumulating_ntt_multiply_fill_cache_poly_step_lemma_fc
    (myself rhs : FillCacheFC.Poly) (acc_init : FillCacheFC.Acc)
    (cache_init : FillCacheFC.Poly)
    (h_self : ∀ i : Fin 16, ∀ j : Fin 16,
        ((myself.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_rhs : ∀ i : Fin 16, ∀ j : Fin 16,
        ((rhs.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_acc_bnd : ∀ n : Fin 256, (acc_init.val[n.val]!).val.natAbs ≤ 2^30)
    (acc : FillCacheFC.Acc) (cache : FillCacheFC.Poly)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (FillCacheFC.inv myself rhs acc_init cache_init k acc cache).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_fill_cache_loop.body
      (vectortraitsOperationsInst := portable_ops_inst) myself rhs
      { start := k, «end» := 16#usize } acc cache
    ⦃ ⇓ r => ⌜ FillCacheFC.step_post myself rhs acc_init cache_init k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_acc_len : acc.val.length = 256 := Std.Array.length_eq acc
  have h_acc_init_len : acc_init.val.length = 256 := Std.Array.length_eq acc_init
  have h_self_coef_len : myself.coefficients.length = 16 := Std.Array.length_eq _
  have h_rhs_coef_len : rhs.coefficients.length = 16 := Std.Array.length_eq _
  have h_cache_coef_len : cache.coefficients.length = 16 := Std.Array.length_eq _
  have h_cache_init_coef_len : cache_init.coefficients.length = 16 := Std.Array.length_eq _
  obtain ⟨h_acc_done, h_acc_undone, h_acc_bnd_rel, h_cache_done, h_cache_undone⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_fill_cache_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- `Some i = k` branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s_iter, hs_val_eq, h_iter_some⟩ :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_some_eq k h_lt
    -- (1) t := self.coefficients[k] and t1 := rhs.coefficients[k].
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      myself.coefficients.val[k.val]! with ht_def
    set t1 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      rhs.coefficients.val[k.val]! with ht1_def
    have h_idx_t : Aeneas.Std.Array.index_usize myself.coefficients k = .ok t :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq myself.coefficients k
        (by rw [h_self_coef_len]; exact hk_16)
    have h_idx_t1 : Aeneas.Std.Array.index_usize rhs.coefficients k = .ok t1 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq rhs.coefficients k
        (by rw [h_rhs_coef_len]; exact hk_16)
    -- (2) i1 := k * 16, i2 := k + 1, i3 := i2 * 16.
    have hi1_max : k.val * (16#usize : Std.Usize).val ≤ Std.Usize.max := by
      have hk_15 : k.val ≤ 15 := by omega
      have hum : (16#usize : Std.Usize).val = 16 := rfl
      rw [hum]
      have h1 : k.val * 16 ≤ 15 * 16 := Nat.mul_le_mul_right 16 hk_15
      have : (15 * 16 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i1, hi1_eq, hi1_val⟩ := usize_mul_ok_eq_fc k 16#usize hi1_max
    have hi1_val_eq : i1.val = 16 * k.val := by
      have hum : (16#usize : Std.Usize).val = 16 := rfl
      rw [hi1_val, hum]; omega
    have hi2_max : k.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      have hk_15 : k.val ≤ 15 := by omega
      have hum : (1#usize : Std.Usize).val = 1 := rfl
      rw [hum]
      have : (16 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i2, hi2_eq, hi2_val⟩ := usize_add_ok_eq_fc k 1#usize hi2_max
    have hi2_val_eq : i2.val = k.val + 1 := by
      have hum : (1#usize : Std.Usize).val = 1 := rfl
      rw [hi2_val, hum]
    have hi3_max : i2.val * (16#usize : Std.Usize).val ≤ Std.Usize.max := by
      have hum : (16#usize : Std.Usize).val = 16 := rfl
      rw [hum, hi2_val_eq]
      have : k.val + 1 ≤ 16 := by omega
      have h1 : (k.val + 1) * 16 ≤ 16 * 16 := Nat.mul_le_mul_right 16 this
      have : (16 * 16 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i3, hi3_eq, hi3_val⟩ := usize_mul_ok_eq_fc i2 16#usize hi3_max
    have hi3_val_eq : i3.val = 16 * (k.val + 1) := by
      have hum : (16#usize : Std.Usize).val = 16 := rfl
      rw [hi3_val, hi2_val_eq, hum]; omega
    -- (3) Sub-slice via Array index_mut RangeUsize.
    have h0_le : i1.val ≤ i3.val := by rw [hi1_val_eq, hi3_val_eq]; omega
    have hi3_le : i3.val ≤ acc.val.length := by
      rw [h_acc_len, hi3_val_eq]
      have : k.val + 1 ≤ 16 := by omega
      have h1 : 16 * (k.val + 1) ≤ 16 * 16 := Nat.mul_le_mul_left _ this
      omega
    obtain ⟨s, back, h_imt_eq, h_s_val_eq, h_s_len_eq, h_back_eq⟩ :=
      array_index_mut_range_ok_eq_fc acc
        ({ start := i1, «end» := i3 } : CoreModels.core.ops.range.Range Std.Usize)
        h0_le hi3_le
    have h_s_len16 : s.length = 16 := by
      show s.val.length = 16
      rw [h_s_len_eq]
      show i3.val - i1.val = 16
      rw [hi3_val_eq, hi1_val_eq]; omega
    have h_s_lane : ∀ ℓ : Nat, ℓ < 16 →
        s.val[ℓ]! = acc.val[16 * k.val + ℓ]! := by
      intro ℓ hℓ
      rw [h_s_val_eq]
      have h_idx_lt : i1.val + ℓ < i3.val := by
        rw [hi1_val_eq, hi3_val_eq]; omega
      have h_bnd : i3.val ≤ acc.val.length ∧ i1.val + ℓ < i3.val := ⟨hi3_le, h_idx_lt⟩
      rw [List.getElem!_slice i1.val i3.val ℓ acc.val h_bnd]
      rw [hi1_val_eq]
    have h_s_lane_init : ∀ ℓ : Nat, ℓ < 16 →
        s.val[ℓ]! = acc_init.val[16 * k.val + ℓ]! := by
      intro ℓ hℓ
      rw [h_s_lane ℓ hℓ]
      exact h_acc_undone k.val (Nat.le_refl _) hk_16 ℓ hℓ
    -- (4) Per-lane bound on s (≤ 2^30 from h_acc_bnd).
    have h_s_bnd : ∀ k' : Fin 16, (s.val[k'.val]!).val.natAbs ≤ 2^30 := by
      intro k'
      rw [h_s_lane_init k'.val k'.isLt]
      have h_lt : 16 * k.val + k'.val < 256 := by
        have : k.val ≤ 15 := by omega
        have hk' : k'.val < 16 := k'.isLt
        have : 16 * k.val ≤ 16 * 15 := Nat.mul_le_mul_left 16 this
        omega
      exact h_acc_bnd ⟨16 * k.val + k'.val, h_lt⟩
    -- (3') Cache-chunk extract via `Array.index_mut_usize cache.coefficients k`.
    set t2 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      cache.coefficients.val[k.val]! with ht2_def
    have h_imt_cache : Aeneas.Std.Array.index_mut_usize cache.coefficients k
        = .ok (t2, cache.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      have h_idx : Aeneas.Std.Array.index_usize cache.coefficients k
          = .ok (cache.coefficients.val[k.val]!) :=
        libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq cache.coefficients k
          (by rw [h_cache_coef_len]; exact hk_16)
      rw [h_idx]; rfl
    -- (5) Read 4 zetas via polynomial.zeta_fc.
    have hi4_max : (4#usize : Std.Usize).val * k.val ≤ Std.Usize.max := by
      have hk_15 : k.val ≤ 15 := by omega
      have hum : (4#usize : Std.Usize).val = 4 := rfl
      rw [hum]
      have : 4 * k.val ≤ 4 * 15 := Nat.mul_le_mul_left 4 hk_15
      have : (4 * 15 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i4, hi4_eq, hi4_val⟩ := usize_mul_ok_eq_fc 4#usize k hi4_max
    have hi4_val_eq : i4.val = 4 * k.val := by
      have hum : (4#usize : Std.Usize).val = 4 := rfl
      rw [hi4_val, hum]
    have hi5_max : (64#usize : Std.Usize).val + i4.val ≤ Std.Usize.max := by
      have hum : (64#usize : Std.Usize).val = 64 := rfl
      rw [hum, hi4_val_eq]
      have hk_15 : k.val ≤ 15 := by omega
      have : 4 * k.val ≤ 4 * 15 := Nat.mul_le_mul_left 4 hk_15
      have : (64 + 4 * 15 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i5, hi5_eq, hi5_val⟩ := usize_add_ok_eq_fc 64#usize i4 hi5_max
    have hi5_val_eq : i5.val = 64 + 4 * k.val := by
      have hum : (64#usize : Std.Usize).val = 64 := rfl
      rw [hi5_val, hum, hi4_val_eq]
    have hi5_lt_128 : i5.val < 128 := by rw [hi5_val_eq]; omega
    obtain ⟨z0, hz0_eq, hz0_post⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc i5 hi5_lt_128)
    obtain ⟨hz0_val_eq, hz0_bnd, hz0_lift⟩ := hz0_post
    have hi8_max : i5.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      have hum : (1#usize : Std.Usize).val = 1 := rfl
      rw [hum, hi5_val_eq]
      have hk_15 : k.val ≤ 15 := by omega
      have : (64 + 4 * 15 + 1 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i8, hi8_eq, hi8_val⟩ := usize_add_ok_eq_fc i5 1#usize hi8_max
    have hi8_val_eq : i8.val = 64 + 4 * k.val + 1 := by
      have hum : (1#usize : Std.Usize).val = 1 := rfl
      rw [hi8_val, hi5_val_eq, hum]
    have hi8_lt_128 : i8.val < 128 := by rw [hi8_val_eq]; omega
    obtain ⟨z1, hz1_eq, hz1_post⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc i8 hi8_lt_128)
    obtain ⟨hz1_val_eq, hz1_bnd, hz1_lift⟩ := hz1_post
    have hi11_max : i5.val + (2#usize : Std.Usize).val ≤ Std.Usize.max := by
      have hum : (2#usize : Std.Usize).val = 2 := rfl
      rw [hum, hi5_val_eq]
      have hk_15 : k.val ≤ 15 := by omega
      have : (64 + 4 * 15 + 2 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i11, hi11_eq, hi11_val⟩ := usize_add_ok_eq_fc i5 2#usize hi11_max
    have hi11_val_eq : i11.val = 64 + 4 * k.val + 2 := by
      have hum : (2#usize : Std.Usize).val = 2 := rfl
      rw [hi11_val, hi5_val_eq, hum]
    have hi11_lt_128 : i11.val < 128 := by rw [hi11_val_eq]; omega
    obtain ⟨z2, hz2_eq, hz2_post⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc i11 hi11_lt_128)
    obtain ⟨hz2_val_eq, hz2_bnd, hz2_lift⟩ := hz2_post
    have hi14_max : i5.val + (3#usize : Std.Usize).val ≤ Std.Usize.max := by
      have hum : (3#usize : Std.Usize).val = 3 := rfl
      rw [hum, hi5_val_eq]
      have hk_15 : k.val ≤ 15 := by omega
      have : (64 + 4 * 15 + 3 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i14, hi14_eq, hi14_val⟩ := usize_add_ok_eq_fc i5 3#usize hi14_max
    have hi14_val_eq : i14.val = 64 + 4 * k.val + 3 := by
      have hum : (3#usize : Std.Usize).val = 3 := rfl
      rw [hi14_val, hi5_val_eq, hum]
    have hi14_lt_128 : i14.val < 128 := by rw [hi14_val_eq]; omega
    obtain ⟨z3, hz3_eq, hz3_post⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc i14 hi14_lt_128)
    obtain ⟨hz3_val_eq, hz3_bnd, hz3_lift⟩ := hz3_post
    -- (6) Apply L2.8d to get (s1, cache_chunk1).
    have h_t_lhs : ∀ j : Fin 16, (t.elements.val[j.val]!).val.natAbs ≤ 3328 := by
      intro j; exact h_self ⟨k.val, hk_16⟩ j
    have h_t1_rhs : ∀ j : Fin 16, (t1.elements.val[j.val]!).val.natAbs ≤ 3328 := by
      intro j; exact h_rhs ⟨k.val, hk_16⟩ j
    obtain ⟨p_pair, h_p_eq, h_s1_len, h_s1_bnd, h_s1_post, h_cache_chunk_post, h_cache_chunk_unc⟩ :=
      triple_exists_ok_fc
        (accumulating_ntt_multiply_fill_cache_fc t t1 s t2 z0 z1 z2 z3 h_s_len16
          h_t_lhs h_t1_rhs hz0_bnd hz1_bnd hz2_bnd hz3_bnd h_s_bnd)
    set s1 : Aeneas.Std.Slice Std.I32 := p_pair.1 with hs1_def
    set cache_chunk1 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      p_pair.2 with hcc1_def
    -- s1's bound vs s lanes.
    have h_s1_bnd_abs : ∀ k' : Nat, k' < 16 →
        (s1.val[k']!).val.natAbs ≤ (acc_init.val[16 * k.val + k']!).val.natAbs + 2^25 := by
      intro k' hk'
      have h_step_bnd := h_s1_bnd ⟨k', hk'⟩
      simp only at h_step_bnd
      rw [h_s_lane_init k' hk'] at h_step_bnd
      exact h_step_bnd
    -- (7) Compose acc1 := back s1.
    set acc1 : FillCacheFC.Acc := back s1 with hacc1_def
    have h_acc1_val : acc1.val = acc.val.setSlice! i1.val s1.val :=
      h_back_eq s1 (by show s1.val.length = i3.val - i1.val; rw [← h_s_len_eq];
                       show s1.length = s.length; rw [h_s1_len, h_s_len16])
    have h_acc1_len : acc1.val.length = 256 := by
      rw [h_acc1_val, List.length_setSlice!, h_acc_len]
    have h_acc1_in : ∀ ℓ : Nat, ℓ < 16 →
        acc1.val[16 * k.val + ℓ]! = s1.val[ℓ]! := by
      intro ℓ hℓ
      rw [h_acc1_val]
      have h_get : (acc.val.setSlice! i1.val s1.val)[16 * k.val + ℓ]!
                    = s1.val[(16 * k.val + ℓ) - i1.val]! := by
        apply List.getElem!_setSlice!_middle
        refine ⟨?_, ?_, ?_⟩
        · rw [hi1_val_eq]; omega
        · rw [hi1_val_eq]
          have h_sub' : 16 * k.val + ℓ - 16 * k.val = ℓ := by omega
          rw [h_sub']
          show ℓ < s1.val.length
          have h_s1' : s1.val.length = 16 := h_s1_len
          rw [h_s1']; exact hℓ
        · rw [h_acc_len]
          have hk_15' : k.val ≤ 15 := by omega
          have h1 : 16 * k.val ≤ 16 * 15 := Nat.mul_le_mul_left 16 hk_15'
          omega
      rw [h_get]
      have h_sub : (16 * k.val + ℓ) - i1.val = ℓ := by
        rw [hi1_val_eq]; omega
      rw [h_sub]
    have h_acc1_out : ∀ n : Nat, n < 256 →
        (n < 16 * k.val ∨ 16 * (k.val + 1) ≤ n) →
        acc1.val[n]! = acc.val[n]! := by
      intro n hn hcases
      rw [h_acc1_val]
      rcases hcases with hlt | hge
      · apply List.getElem!_setSlice!_prefix
        rw [hi1_val_eq]; exact hlt
      · apply List.getElem!_setSlice!_suffix
        rw [hi1_val_eq]
        have h_s1' : s1.val.length = 16 := h_s1_len
        rw [h_s1']
        have h_eq16 : 16 * k.val + 16 = 16 * (k.val + 1) := by ring
        rw [h_eq16]; exact hge
    -- (7') Compose cache1 := { coefficients := cache.coefficients.set k cache_chunk1 }.
    set cache1 : FillCacheFC.Poly :=
      { coefficients := cache.coefficients.set k cache_chunk1 } with hcache1_def
    have h_cache1_at : cache1.coefficients.val[k.val]! = cache_chunk1 := by
      show (cache.coefficients.set k cache_chunk1).val[k.val]! = cache_chunk1
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq cache.coefficients k k.val cache_chunk1
          ⟨rfl, by rw [h_cache_coef_len]; exact hk_16⟩
    have h_cache1_ne : ∀ j : Nat, j ≠ k.val →
        cache1.coefficients.val[j]! = cache.coefficients.val[j]! := by
      intro j hj
      show (cache.coefficients.set k cache_chunk1).val[j]! = cache.coefficients.val[j]!
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_ne cache.coefficients k j cache_chunk1
          (fun h => hj h.symm)
    -- (9) Body equation.
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_fill_cache_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) myself rhs
          { start := k, «end» := 16#usize } acc cache
        = .ok (ControlFlow.cont (({ start := s_iter, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize), acc1, cache1)) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_fill_cache_loop.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp only [Aeneas.Std.bind_tc_ok]
      show ((do
              let t' ← Aeneas.Std.Array.index_usize myself.coefficients k
              let t1' ← Aeneas.Std.Array.index_usize rhs.coefficients k
              let i1' ← (k * 16#usize : Result Std.Usize)
              let i2' ← k + 1#usize
              let i3' ← i2' * 16#usize
              let (s', index_mut_back) ←
                core.Array.Insts.CoreOpsIndexIndexMut.index_mut
                  (core.Slice.Insts.CoreOpsIndexIndexMut
                    (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                      Std.I32)) acc { start := i1', «end» := i3' }
              let (t2', index_mut_back1) ← Aeneas.Std.Array.index_mut_usize cache.coefficients k
              let i4' ← 4#usize * k
              let i5' ← 64#usize + i4'
              let i6' ← libcrux_iot_ml_kem.polynomial.zeta i5'
              let i7' ← 64#usize + i4'
              let i8' ← i7' + 1#usize
              let i9' ← libcrux_iot_ml_kem.polynomial.zeta i8'
              let i10' ← 64#usize + i4'
              let i11' ← i10' + 2#usize
              let i12' ← libcrux_iot_ml_kem.polynomial.zeta i11'
              let i13' ← 64#usize + i4'
              let i14' ← i13' + 3#usize
              let i15' ← libcrux_iot_ml_kem.polynomial.zeta i14'
              let p ←
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations.accumulating_ntt_multiply_fill_cache
                  t' t1' s' t2' i6' i9' i12' i15'
              .ok (ControlFlow.cont (({ start := s_iter, «end» := 16#usize }
                          : CoreModels.core.ops.range.Range Std.Usize), index_mut_back p.1,
                          ({ coefficients := index_mut_back1 p.2 }
                            : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            : Result _) = _
      rw [h_idx_t]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_t1]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi1_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi2_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi3_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_cache]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi4_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi5_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hz0_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi8_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hz1_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi11_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hz2_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi14_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hz3_eq]; simp only [Aeneas.Std.bind_tc_ok]
      show ((do
              let p ←
                libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_fill_cache
                  t t1 s t2 z0 z1 z2 z3
              .ok (ControlFlow.cont (({ start := s_iter, «end» := 16#usize }
                          : CoreModels.core.ops.range.Range Std.Usize), back p.1,
                          ({ coefficients := cache.coefficients.set k p.2 }
                            : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            : Result _) = _
      rw [h_p_eq]
      rfl
    apply triple_of_ok_fc h_body
    show FillCacheFC.step_post myself rhs acc_init cache_init k
      (.cont (({ start := s_iter, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize), acc1, cache1))
    unfold FillCacheFC.step_post
    refine ⟨h_lt, rfl, hs_val_eq, ?_⟩
    show (FillCacheFC.inv myself rhs acc_init cache_init s_iter acc1 cache1).holds
    unfold FillCacheFC.inv
    -- Build the five invariant conjuncts.
    have h_inv_pure :
        (∀ j : Nat, j < s_iter.val → ∀ ℓ : Nat, ℓ < 16 →
          Spec.mont_reduce_pure (lift_fe_int (acc1.val[16 * j + ℓ]!).val)
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))
                ((Spec.ntt_multiply_pure_no_acc
                    (lift_chunk_mont (myself.coefficients.val[j]!))
                    (lift_chunk_mont (rhs.coefficients.val[j]!))
                    (Spec.zeta_at (64 + 4 * j))
                    (Spec.zeta_at (64 + 4 * j + 1))
                    (Spec.zeta_at (64 + 4 * j + 2))
                    (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
        ∧ (∀ j : Nat, s_iter.val ≤ j → j < 16 → ∀ ℓ : Nat, ℓ < 16 →
            acc1.val[16 * j + ℓ]! = acc_init.val[16 * j + ℓ]!)
        ∧ (∀ n : Nat, n < 256 →
            (acc1.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + 2^25)
        ∧ (∀ j : Nat, j < s_iter.val →
            Spec.ntt_multiply_cache_post
              (rhs.coefficients.val[j]!)
              libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * j]!
              libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * j + 1]!
              libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * j + 2]!
              libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * j + 3]!
              (cache1.coefficients.val[j]!))
        ∧ (∀ j : Nat, s_iter.val ≤ j → j < 16 →
            cache1.coefficients.val[j]! = cache_init.coefficients.val[j]!) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- (a) Touched-chunk FC.
        intro j hj ℓ hℓ
        rw [hs_val_eq] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · have h_in_range : 16 * j + ℓ < 16 * k.val := by
            have h1 : 16 * j + 16 ≤ 16 * k.val := by
              have : j + 1 ≤ k.val := by omega
              have : 16 * (j + 1) ≤ 16 * k.val := Nat.mul_le_mul_left 16 this
              omega
            omega
          have h_lt_256 : 16 * j + ℓ < 256 := by
            have : k.val ≤ 15 := by omega
            have : 16 * k.val ≤ 16 * 15 := Nat.mul_le_mul_left 16 this
            omega
          have h_acc1_eq_acc : acc1.val[16 * j + ℓ]! = acc.val[16 * j + ℓ]! :=
            h_acc1_out (16 * j + ℓ) h_lt_256 (Or.inl h_in_range)
          rw [h_acc1_eq_acc]
          exact h_acc_done j hj_lt_k ℓ hℓ
        · subst hj_eq_k
          rw [h_acc1_in ℓ hℓ]
          unfold ntt_multiply_base_case_post at h_s1_post
          have h_lhs_val_eq :
              (Spec.chunk_reducing_from_i32_array_pure s1).val[ℓ]!
                = Spec.mont_reduce_pure (lift_fe_int (s1.val[ℓ]!).val) :=
            Spec.chunk_reducing_from_i32_array_pure_lane_eq s1 ℓ hℓ
          have h_s_chunk_val :
              (Spec.chunk_reducing_from_i32_array_pure s).val[ℓ]!
                = Spec.mont_reduce_pure (lift_fe_int (s.val[ℓ]!).val) :=
            Spec.chunk_reducing_from_i32_array_pure_lane_eq s ℓ hℓ
          have h_rhs_val_eq :
              (ntt_multiply_base_case_alg
                (lift_chunk_mont t) (lift_chunk_mont t1)
                (lift_fe_mont z0) (lift_fe_mont z1)
                (lift_fe_mont z2) (lift_fe_mont z3)
                (Spec.chunk_reducing_from_i32_array_pure s)).val[ℓ]!
                = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                    ((Spec.chunk_reducing_from_i32_array_pure s).val[ℓ]!)
                    ((Spec.ntt_multiply_pure_no_acc
                        (lift_chunk_mont t) (lift_chunk_mont t1)
                        (lift_fe_mont z0) (lift_fe_mont z1)
                        (lift_fe_mont z2) (lift_fe_mont z3)).val[ℓ]!) := by
            unfold ntt_multiply_base_case_alg
            exact Spec.chunk_add_pure_lane_eq _ _ ℓ hℓ
          have h_chunk_eq :
              Spec.mont_reduce_pure (lift_fe_int (s1.val[ℓ]!).val)
                = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                    (Spec.mont_reduce_pure (lift_fe_int (s.val[ℓ]!).val))
                    ((Spec.ntt_multiply_pure_no_acc
                        (lift_chunk_mont t) (lift_chunk_mont t1)
                        (lift_fe_mont z0) (lift_fe_mont z1)
                        (lift_fe_mont z2) (lift_fe_mont z3)).val[ℓ]!) := by
            have h_eq : (Spec.chunk_reducing_from_i32_array_pure s1).val[ℓ]!
                  = (ntt_multiply_base_case_alg
                      (lift_chunk_mont t) (lift_chunk_mont t1)
                      (lift_fe_mont z0) (lift_fe_mont z1)
                      (lift_fe_mont z2) (lift_fe_mont z3)
                      (Spec.chunk_reducing_from_i32_array_pure s)).val[ℓ]! := by
              rw [h_s1_post]
            rw [h_lhs_val_eq] at h_eq
            rw [h_rhs_val_eq] at h_eq
            rw [h_s_chunk_val] at h_eq
            exact h_eq
          rw [h_chunk_eq]
          rw [h_s_lane_init ℓ hℓ]
          rw [hz0_lift, hz1_lift, hz2_lift, hz3_lift]
          rw [hi5_val_eq, hi8_val_eq, hi11_val_eq, hi14_val_eq]
      · -- (b) Untouched acc chunks.
        intro j hj_ge hj_lt ℓ hℓ
        rw [hs_val_eq] at hj_ge
        have h_n_lt_256 : 16 * j + ℓ < 256 := by
          have : j ≤ 15 := by omega
          have : 16 * j ≤ 16 * 15 := Nat.mul_le_mul_left 16 this
          omega
        have h_ge_range : 16 * (k.val + 1) ≤ 16 * j + ℓ := by
          have : k.val + 1 ≤ j := hj_ge
          have : 16 * (k.val + 1) ≤ 16 * j := Nat.mul_le_mul_left 16 this
          omega
        have h_acc1_eq_acc : acc1.val[16 * j + ℓ]! = acc.val[16 * j + ℓ]! :=
          h_acc1_out (16 * j + ℓ) h_n_lt_256 (Or.inr h_ge_range)
        rw [h_acc1_eq_acc]
        exact h_acc_undone j (by omega) hj_lt ℓ hℓ
      · -- (c) Universal acc bound.
        intro n hn
        by_cases hcase : 16 * k.val ≤ n ∧ n < 16 * (k.val + 1)
        · obtain ⟨hge, hlt⟩ := hcase
          have hn_decomp : n = 16 * k.val + (n - 16 * k.val) := by omega
          have hn_off_lt : n - 16 * k.val < 16 := by omega
          have h_acc1_n : acc1.val[n]! = s1.val[n - 16 * k.val]! := by
            conv_lhs => rw [hn_decomp]
            exact h_acc1_in (n - 16 * k.val) hn_off_lt
          rw [h_acc1_n]
          have h_bnd_at_off := h_s1_bnd_abs (n - 16 * k.val) hn_off_lt
          have h_acc_init_n : acc_init.val[16 * k.val + (n - 16 * k.val)]!
                              = acc_init.val[n]! := by
            congr 1; omega
          rw [h_acc_init_n] at h_bnd_at_off
          exact h_bnd_at_off
        · have h_outside : n < 16 * k.val ∨ 16 * (k.val + 1) ≤ n := by
            by_contra hc
            push Not at hc
            exact hcase ⟨hc.1, hc.2⟩
          have h_acc1_eq_acc : acc1.val[n]! = acc.val[n]! :=
            h_acc1_out n hn h_outside
          rw [h_acc1_eq_acc]
          exact h_acc_bnd_rel n hn
      · -- (d) Cache touched chunks.
        intro j hj
        rw [hs_val_eq] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k.val: cache1[j] = cache[j], use h_cache_done.
          have hj_ne : j ≠ k.val := by omega
          rw [h_cache1_ne j hj_ne]
          exact h_cache_done j hj_lt_k
        · -- j = k.val: cache1[k.val] = cache_chunk1, use h_cache_chunk_post.
          subst hj_eq_k
          rw [h_cache1_at]
          -- h_cache_chunk_post : Spec.ntt_multiply_cache_post t1 z0 z1 z2 z3 cache_chunk1.
          -- z0 = ZETAS_TIMES_MONTGOMERY_R[i5.val]! and i5.val = 64 + 4*k.val, etc.
          have hz0_id : z0 = libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * k.val]! := by
            rw [hz0_val_eq, hi5_val_eq]
          have hz1_id : z1 = libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * k.val + 1]! := by
            rw [hz1_val_eq, hi8_val_eq]
          have hz2_id : z2 = libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * k.val + 2]! := by
            rw [hz2_val_eq, hi11_val_eq]
          have hz3_id : z3 = libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * k.val + 3]! := by
            rw [hz3_val_eq, hi14_val_eq]
          rw [← hz0_id, ← hz1_id, ← hz2_id, ← hz3_id]
          exact h_cache_chunk_post
      · -- (e) Cache untouched.
        intro j hj_ge hj_lt
        rw [hs_val_eq] at hj_ge
        have hj_ne : j ≠ k.val := by omega
        rw [h_cache1_ne j hj_ne]
        exact h_cache_undone j (by omega) hj_lt
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ 16, done.
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_fill_cache_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) myself rhs
          { start := k, «end» := 16#usize } acc cache
        = .ok (ControlFlow.done (acc, cache)) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_fill_cache_loop.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    apply triple_of_ok_fc h_body
    show FillCacheFC.step_post myself rhs acc_init cache_init k (.done (acc, cache))
    unfold FillCacheFC.step_post
    show (FillCacheFC.inv myself rhs acc_init cache_init 16#usize acc cache).holds
    unfold FillCacheFC.inv
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        (∀ j : Nat, j < (16#usize : Std.Usize).val → ∀ ℓ : Nat, ℓ < 16 →
          Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val)
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))
                ((Spec.ntt_multiply_pure_no_acc
                    (lift_chunk_mont (myself.coefficients.val[j]!))
                    (lift_chunk_mont (rhs.coefficients.val[j]!))
                    (Spec.zeta_at (64 + 4 * j))
                    (Spec.zeta_at (64 + 4 * j + 1))
                    (Spec.zeta_at (64 + 4 * j + 2))
                    (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 → ∀ ℓ : Nat, ℓ < 16 →
            acc.val[16 * j + ℓ]! = acc_init.val[16 * j + ℓ]!)
        ∧ (∀ n : Nat, n < 256 →
            (acc.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + 2^25)
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val →
            Spec.ntt_multiply_cache_post
              (rhs.coefficients.val[j]!)
              libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * j]!
              libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * j + 1]!
              libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * j + 2]!
              libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * j + 3]!
              (cache.coefficients.val[j]!))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            cache.coefficients.val[j]! = cache_init.coefficients.val[j]!) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro j hj ℓ hℓ; rw [h16] at hj
        apply h_acc_done j _ ℓ hℓ; rw [hk_eq]; exact hj
      · intro j hj_ge hj_lt ℓ hℓ
        rw [h16] at hj_ge
        apply h_acc_undone j _ hj_lt ℓ hℓ; rw [hk_eq]; exact hj_ge
      · intro n hn; exact h_acc_bnd_rel n hn
      · intro j hj; rw [h16] at hj
        apply h_cache_done j _; rw [hk_eq]; exact hj
      · intro j hj_ge hj_lt
        rw [h16] at hj_ge
        apply h_cache_undone j _ hj_lt; rw [hk_eq]; exact hj_ge
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

/-- L6.3c — `polynomial.PolynomialRingElement.accumulating_ntt_multiply_fill_cache`:
    polynomial wrapper of `accumulating_ntt_multiply_fill_cache_fc`. Loops
    over the 16 chunks; per chunk j it dispatches the L2.8d
    `_fill_cache` variant with chunk `j`'s zetas
    (`polynomial.zeta (64+4j+{0,1,2,3})`) and the chunk's mutable cache slot
    (`cache.coefficients[j]`).

    POST shape mirrors L6.3 (length + relative accumulator bound +
    `accumulating_ntt_multiply_poly_post`) AND adds a polynomial-level
    cache POST (`accumulating_ntt_multiply_poly_cache_post`) asserting
    that each cache chunk stores the per-pair Mont-reduced
    `b·zeta` products for its effective zetas. -/
@[spec]
theorem accumulating_ntt_multiply_fill_cache_poly_fc
    (myself rhs cache : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (accumulator : Std.Array Std.I32 256#usize)
    (h_self : ∀ i : Fin 16, ∀ j : Fin 16,
        ((myself.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_rhs : ∀ i : Fin 16, ∀ j : Fin 16,
        ((rhs.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_acc_bnd : ∀ n : Fin 256, (accumulator.val[n.val]!).val.natAbs ≤ 2^30) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_fill_cache
      (vectortraitsOperationsInst := portable_ops_inst)
      myself rhs accumulator cache
    ⦃ ⇓ p => ⌜ (∀ n : Fin 256, (p.1.val[n.val]!).val.natAbs
                                ≤ (accumulator.val[n.val]!).val.natAbs + 2^25) ∧
              accumulating_ntt_multiply_poly_post
                myself rhs accumulator p.1 ∧
              accumulating_ntt_multiply_poly_cache_post rhs p.2 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_fill_cache
  have h_vre : libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
                = .ok (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
    rfl
  rw [h_vre]; simp only [Aeneas.Std.bind_tc_ok]
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_fill_cache_loop
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, p) =>
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_fill_cache_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) myself rhs iter1 p.1 p.2)
      (β := FillCacheFC.Acc × FillCacheFC.Poly)
      (accumulator, cache)
      0#usize 16#usize
      (fun k p => FillCacheFC.inv myself rhs accumulator cache k p.1 p.2)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (by
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro j hj; exact absurd hj (Nat.not_lt_zero j)
        · intro _ _ _ _ _; trivial
        · intro n _; omega
        · intro j hj; exact absurd hj (Nat.not_lt_zero j)
        · intro _ _ _; trivial)
      ?_)
  · -- Post entailment at k = 16: derive the locked POST.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (FillCacheFC.inv myself rhs accumulator cache 16#usize r.1 r.2).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    obtain ⟨h_done, _h_undone, h_bnd, h_cache_done, _h_cache_undone⟩ := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_holds
    refine ⟨?_, ?_, ?_⟩
    · intro n; exact h_bnd n.val n.isLt
    · unfold accumulating_ntt_multiply_poly_post
      intro j hj ℓ hℓ
      have h16' : (16#usize : Std.Usize).val = 16 := rfl
      exact h_done j (by rw [h16']; exact hj) ℓ hℓ
    · -- accumulating_ntt_multiply_poly_cache_post: bridge chunk-level cache POST to poly-level.
      show accumulating_ntt_multiply_poly_cache_post rhs r.2
      unfold accumulating_ntt_multiply_poly_cache_post
      intro j_fin i_fin
      have h16' : (16#usize : Std.Usize).val = 16 := rfl
      have h_chunk := h_cache_done j_fin.val (by rw [h16']; exact j_fin.isLt)
      -- h_chunk : Spec.ntt_multiply_cache_post (rhs.coefficients[j]!) ZETAS[64+4j+0..3]! (r.2.coefficients[j]!)
      unfold Spec.ntt_multiply_cache_post at h_chunk
      exact h_chunk i_fin
  · -- Step entailment.
    intro p k _h_ge h_le hinv
    have h_step := accumulating_ntt_multiply_fill_cache_poly_step_lemma_fc
      myself rhs accumulator cache h_self h_rhs h_acc_bnd p.1 p.2 k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc_cache⟩ | y
    · have hP : FillCacheFC.step_post myself rhs accumulator cache k
                  (.cont (iter', acc_cache.1, acc_cache.2)) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [FillCacheFC.step_post] using hP
    · have hP : FillCacheFC.step_post myself rhs accumulator cache k (.done (y.1, y.2)) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [FillCacheFC.step_post] using hP

end L6_3c_fill_irreducible

-- Memory hygiene (rule 1 / SKILL §5.7 Idiom 2). Same irreducible-attribute
-- discipline as the L6.3c.fill section, applied to the read-only `_use_cache`
-- step lemma + outer Triple. We REUSE `UseCacheFC.inv` / `UseCacheFC.step_post`
-- (cache is closure-captured, not threaded), so neither is added to the
-- irreducible list (this would break the `simpa` destructure of `h_inv`).
section L6_3c_use_irreducible
attribute [local irreducible] Spec.ntt_multiply_cache_post
attribute [local irreducible] accumulating_ntt_multiply_poly_cache_post
attribute [local irreducible] ntt_multiply_base_case_post
attribute [local irreducible] Spec.chunk_reducing_from_i32_array_pure
attribute [local irreducible] lift_chunk_mont
attribute [local irreducible] Spec.ntt_multiply_pure_no_acc
attribute [local irreducible] ntt_multiply_base_case_alg
attribute [local irreducible] Spec.effective_zeta_fe

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for `_use_cache` polynomial loop. Mirrors
    `accumulating_ntt_multiply_poly_step_lemma_fc` (L6.3 base) but accepts
    a read-only `cache` parameter (closure-captured in the body) together
    with the polynomial-level cache PRE `h_cache`. Cache is unchanged, so
    the carrier is `UseCacheFC.Acc` and the invariant is the L6.3 base 3-tuple. -/
theorem accumulating_ntt_multiply_use_cache_poly_step_lemma_fc
    (myself rhs : UseCacheFC.Poly) (cache : UseCacheFC.Poly)
    (acc_init : UseCacheFC.Acc)
    (h_self : ∀ i : Fin 16, ∀ j : Fin 16,
        ((myself.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_rhs : ∀ i : Fin 16, ∀ j : Fin 16,
        ((rhs.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_acc_bnd : ∀ n : Fin 256, (acc_init.val[n.val]!).val.natAbs ≤ 2^30)
    (h_cache : accumulating_ntt_multiply_poly_cache_post rhs cache)
    (acc : UseCacheFC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (UseCacheFC.inv myself rhs acc_init k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_use_cache_loop.body
      (vectortraitsOperationsInst := portable_ops_inst) myself rhs cache
      { start := k, «end» := 16#usize } acc
    ⦃ ⇓ r => ⌜ UseCacheFC.step_post myself rhs acc_init k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_acc_len : acc.val.length = 256 := Std.Array.length_eq acc
  have h_acc_init_len : acc_init.val.length = 256 := Std.Array.length_eq acc_init
  have h_self_coef_len : myself.coefficients.length = 16 := Std.Array.length_eq _
  have h_rhs_coef_len : rhs.coefficients.length = 16 := Std.Array.length_eq _
  have h_cache_coef_len : cache.coefficients.length = 16 := Std.Array.length_eq _
  obtain ⟨h_acc_done, h_acc_undone, h_acc_bnd_rel⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_use_cache_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- `Some i = k` branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s_iter, hs_val_eq, h_iter_some⟩ :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_some_eq k h_lt
    -- (1) t := self.coefficients[k] and t1 := rhs.coefficients[k].
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      myself.coefficients.val[k.val]! with ht_def
    set t1 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      rhs.coefficients.val[k.val]! with ht1_def
    have h_idx_t : Aeneas.Std.Array.index_usize myself.coefficients k = .ok t :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq myself.coefficients k
        (by rw [h_self_coef_len]; exact hk_16)
    have h_idx_t1 : Aeneas.Std.Array.index_usize rhs.coefficients k = .ok t1 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq rhs.coefficients k
        (by rw [h_rhs_coef_len]; exact hk_16)
    -- (2) i1 := k * 16, i2 := k + 1, i3 := i2 * 16.
    have hi1_max : k.val * (16#usize : Std.Usize).val ≤ Std.Usize.max := by
      have hk_15 : k.val ≤ 15 := by omega
      have hum : (16#usize : Std.Usize).val = 16 := rfl
      rw [hum]
      have h1 : k.val * 16 ≤ 15 * 16 := Nat.mul_le_mul_right 16 hk_15
      have : (15 * 16 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i1, hi1_eq, hi1_val⟩ := usize_mul_ok_eq_fc k 16#usize hi1_max
    have hi1_val_eq : i1.val = 16 * k.val := by
      have hum : (16#usize : Std.Usize).val = 16 := rfl
      rw [hi1_val, hum]; omega
    have hi2_max : k.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      have hk_15 : k.val ≤ 15 := by omega
      have hum : (1#usize : Std.Usize).val = 1 := rfl
      rw [hum]
      have : (16 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i2, hi2_eq, hi2_val⟩ := usize_add_ok_eq_fc k 1#usize hi2_max
    have hi2_val_eq : i2.val = k.val + 1 := by
      have hum : (1#usize : Std.Usize).val = 1 := rfl
      rw [hi2_val, hum]
    have hi3_max : i2.val * (16#usize : Std.Usize).val ≤ Std.Usize.max := by
      have hum : (16#usize : Std.Usize).val = 16 := rfl
      rw [hum, hi2_val_eq]
      have : k.val + 1 ≤ 16 := by omega
      have h1 : (k.val + 1) * 16 ≤ 16 * 16 := Nat.mul_le_mul_right 16 this
      have : (16 * 16 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i3, hi3_eq, hi3_val⟩ := usize_mul_ok_eq_fc i2 16#usize hi3_max
    have hi3_val_eq : i3.val = 16 * (k.val + 1) := by
      have hum : (16#usize : Std.Usize).val = 16 := rfl
      rw [hi3_val, hi2_val_eq, hum]; omega
    -- (3) Sub-slice via Array index_mut RangeUsize.
    have h0_le : i1.val ≤ i3.val := by rw [hi1_val_eq, hi3_val_eq]; omega
    have hi3_le : i3.val ≤ acc.val.length := by
      rw [h_acc_len, hi3_val_eq]
      have : k.val + 1 ≤ 16 := by omega
      have h1 : 16 * (k.val + 1) ≤ 16 * 16 := Nat.mul_le_mul_left _ this
      omega
    obtain ⟨s, back, h_imt_eq, h_s_val_eq, h_s_len_eq, h_back_eq⟩ :=
      array_index_mut_range_ok_eq_fc acc
        ({ start := i1, «end» := i3 } : CoreModels.core.ops.range.Range Std.Usize)
        h0_le hi3_le
    have h_s_len16 : s.length = 16 := by
      show s.val.length = 16
      rw [h_s_len_eq]
      show i3.val - i1.val = 16
      rw [hi3_val_eq, hi1_val_eq]; omega
    have h_s_lane : ∀ ℓ : Nat, ℓ < 16 →
        s.val[ℓ]! = acc.val[16 * k.val + ℓ]! := by
      intro ℓ hℓ
      rw [h_s_val_eq]
      have h_idx_lt : i1.val + ℓ < i3.val := by
        rw [hi1_val_eq, hi3_val_eq]; omega
      have h_bnd : i3.val ≤ acc.val.length ∧ i1.val + ℓ < i3.val := ⟨hi3_le, h_idx_lt⟩
      rw [List.getElem!_slice i1.val i3.val ℓ acc.val h_bnd]
      rw [hi1_val_eq]
    have h_s_lane_init : ∀ ℓ : Nat, ℓ < 16 →
        s.val[ℓ]! = acc_init.val[16 * k.val + ℓ]! := by
      intro ℓ hℓ
      rw [h_s_lane ℓ hℓ]
      exact h_acc_undone k.val (Nat.le_refl _) hk_16 ℓ hℓ
    -- (4) Per-lane bound on s (≤ 2^30 from h_acc_bnd).
    have h_s_bnd : ∀ k' : Fin 16, (s.val[k'.val]!).val.natAbs ≤ 2^30 := by
      intro k'
      rw [h_s_lane_init k'.val k'.isLt]
      have h_lt : 16 * k.val + k'.val < 256 := by
        have : k.val ≤ 15 := by omega
        have hk' : k'.val < 16 := k'.isLt
        have : 16 * k.val ≤ 16 * 15 := Nat.mul_le_mul_left 16 this
        omega
      exact h_acc_bnd ⟨16 * k.val + k'.val, h_lt⟩
    -- (3') Cache-chunk extract via `Array.index_usize cache.coefficients k`
    -- (single-element READ — `_use_cache` does not mutate the cache).
    set t2 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      cache.coefficients.val[k.val]! with ht2_def
    have h_idx_t2 : Aeneas.Std.Array.index_usize cache.coefficients k = .ok t2 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq cache.coefficients k
        (by rw [h_cache_coef_len]; exact hk_16)
    -- (5) The four zetas: derived from the cache PRE at chunk k, without
    -- calling `polynomial.zeta_fc` (the impl does NOT read zetas here).
    set z0 : Std.I16 :=
      libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * k.val]! with hz0_def
    set z1 : Std.I16 :=
      libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * k.val + 1]! with hz1_def
    set z2 : Std.I16 :=
      libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * k.val + 2]! with hz2_def
    set z3 : Std.I16 :=
      libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.val[64 + 4 * k.val + 3]! with hz3_def
    have hz0_bnd : z0.val.natAbs ≤ 1664 := ZETAS_bound (64 + 4 * k.val) (by omega)
    have hz1_bnd : z1.val.natAbs ≤ 1664 := ZETAS_bound (64 + 4 * k.val + 1) (by omega)
    have hz2_bnd : z2.val.natAbs ≤ 1664 := ZETAS_bound (64 + 4 * k.val + 2) (by omega)
    have hz3_bnd : z3.val.natAbs ≤ 1664 := ZETAS_bound (64 + 4 * k.val + 3) (by omega)
    have hz0_lift : lift_fe_mont z0 = Spec.zeta_at (64 + 4 * k.val) := rfl
    have hz1_lift : lift_fe_mont z1 = Spec.zeta_at (64 + 4 * k.val + 1) := rfl
    have hz2_lift : lift_fe_mont z2 = Spec.zeta_at (64 + 4 * k.val + 2) := rfl
    have hz3_lift : lift_fe_mont z3 = Spec.zeta_at (64 + 4 * k.val + 3) := rfl
    -- (6) Derive the per-chunk vector-level cache POST from the poly-level PRE.
    have h_cache_chunk : Spec.ntt_multiply_cache_post t1 z0 z1 z2 z3 t2 := by
      unfold accumulating_ntt_multiply_poly_cache_post at h_cache
      unfold Spec.ntt_multiply_cache_post
      intro i_fin
      have h := h_cache ⟨k.val, hk_16⟩ i_fin
      -- h : ((cache.coefficients.val[k.val]!).elements.val[i_fin.val]!).val.natAbs ≤ 3328
      --     ∧ lift_fe_mont (...) = mul_pure (lift_fe_mont rhs[..]) (effective_zeta_fe i_fin ...)
      -- where the effective zetas use `Spec.zeta_at (64+4*k.val+m)` — which by
      -- `hz_m_lift` (`rfl`) equals `lift_fe_mont z_m`.
      exact h
    -- (7) Apply L2.8d use_cache to get s1 satisfying ntt_multiply_base_case_post.
    have h_t_lhs : ∀ j : Fin 16, (t.elements.val[j.val]!).val.natAbs ≤ 3328 := by
      intro j; exact h_self ⟨k.val, hk_16⟩ j
    have h_t1_rhs : ∀ j : Fin 16, (t1.elements.val[j.val]!).val.natAbs ≤ 3328 := by
      intro j; exact h_rhs ⟨k.val, hk_16⟩ j
    obtain ⟨s1, h_s1_eq, h_s1_len, h_s1_bnd, h_s1_post⟩ :=
      triple_exists_ok_fc
        (accumulating_ntt_multiply_use_cache_fc t t1 s t2 z0 z1 z2 z3 h_s_len16
          h_t_lhs h_t1_rhs hz0_bnd hz1_bnd hz2_bnd hz3_bnd h_s_bnd h_cache_chunk)
    -- s1's bound vs s lanes (s.val[k'] = acc_init[16k+k']).
    have h_s1_bnd_abs : ∀ k' : Nat, k' < 16 →
        (s1.val[k']!).val.natAbs ≤ (acc_init.val[16 * k.val + k']!).val.natAbs + 2^25 := by
      intro k' hk'
      have h_step_bnd := h_s1_bnd ⟨k', hk'⟩
      simp only at h_step_bnd
      rw [h_s_lane_init k' hk'] at h_step_bnd
      exact h_step_bnd
    -- (8) Compose acc1 := back s1.
    set acc1 : UseCacheFC.Acc := back s1 with hacc1_def
    have h_acc1_val : acc1.val = acc.val.setSlice! i1.val s1.val :=
      h_back_eq s1 (by show s1.val.length = i3.val - i1.val; rw [← h_s_len_eq];
                       show s1.length = s.length; rw [h_s1_len, h_s_len16])
    have h_acc1_len : acc1.val.length = 256 := by
      rw [h_acc1_val, List.length_setSlice!, h_acc_len]
    have h_acc1_in : ∀ ℓ : Nat, ℓ < 16 →
        acc1.val[16 * k.val + ℓ]! = s1.val[ℓ]! := by
      intro ℓ hℓ
      rw [h_acc1_val]
      have h_get : (acc.val.setSlice! i1.val s1.val)[16 * k.val + ℓ]!
                    = s1.val[(16 * k.val + ℓ) - i1.val]! := by
        apply List.getElem!_setSlice!_middle
        refine ⟨?_, ?_, ?_⟩
        · rw [hi1_val_eq]; omega
        · rw [hi1_val_eq]
          have h_sub' : 16 * k.val + ℓ - 16 * k.val = ℓ := by omega
          rw [h_sub']
          show ℓ < s1.val.length
          have h_s1' : s1.val.length = 16 := h_s1_len
          rw [h_s1']; exact hℓ
        · rw [h_acc_len]
          have hk_15' : k.val ≤ 15 := by omega
          have h1 : 16 * k.val ≤ 16 * 15 := Nat.mul_le_mul_left 16 hk_15'
          omega
      rw [h_get]
      have h_sub : (16 * k.val + ℓ) - i1.val = ℓ := by
        rw [hi1_val_eq]; omega
      rw [h_sub]
    have h_acc1_out : ∀ n : Nat, n < 256 →
        (n < 16 * k.val ∨ 16 * (k.val + 1) ≤ n) →
        acc1.val[n]! = acc.val[n]! := by
      intro n hn hcases
      rw [h_acc1_val]
      rcases hcases with hlt | hge
      · apply List.getElem!_setSlice!_prefix
        rw [hi1_val_eq]; exact hlt
      · apply List.getElem!_setSlice!_suffix
        rw [hi1_val_eq]
        have h_s1' : s1.val.length = 16 := h_s1_len
        rw [h_s1']
        have h_eq16 : 16 * k.val + 16 = 16 * (k.val + 1) := by ring
        rw [h_eq16]; exact hge
    -- (9) Body equation: the impl reduces to .ok (cont (..., acc1)).
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_use_cache_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) myself rhs cache
          { start := k, «end» := 16#usize } acc
        = .ok (ControlFlow.cont (({ start := s_iter, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize), acc1)) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_use_cache_loop.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp only [Aeneas.Std.bind_tc_ok]
      show ((do
              let t' ← Aeneas.Std.Array.index_usize myself.coefficients k
              let t1' ← Aeneas.Std.Array.index_usize rhs.coefficients k
              let i1' ← (k * 16#usize : Result Std.Usize)
              let i2' ← k + 1#usize
              let i3' ← i2' * 16#usize
              let (s', index_mut_back) ←
                core.Array.Insts.CoreOpsIndexIndexMut.index_mut
                  (core.Slice.Insts.CoreOpsIndexIndexMut
                    (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                      Std.I32)) acc { start := i1', «end» := i3' }
              let t2' ← Aeneas.Std.Array.index_usize cache.coefficients k
              let s1' ←
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations.accumulating_ntt_multiply_use_cache
                  t' t1' s' t2'
              .ok (ControlFlow.cont (({ start := s_iter, «end» := 16#usize }
                          : CoreModels.core.ops.range.Range Std.Usize), index_mut_back s1')))
            : Result _) = _
      rw [h_idx_t]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_t1]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi1_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi2_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi3_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_t2]; simp only [Aeneas.Std.bind_tc_ok]
      show ((do
              let s1' ←
                libcrux_iot_ml_kem.vector.portable.ntt.accumulating_ntt_multiply_use_cache
                  t t1 s t2
              .ok (ControlFlow.cont (({ start := s_iter, «end» := 16#usize }
                          : CoreModels.core.ops.range.Range Std.Usize), back s1')))
            : Result _) = _
      rw [h_s1_eq]
      rfl
    apply triple_of_ok_fc h_body
    show UseCacheFC.step_post myself rhs acc_init k
      (.cont (({ start := s_iter, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize), acc1))
    unfold UseCacheFC.step_post
    refine ⟨h_lt, rfl, hs_val_eq, ?_⟩
    show (UseCacheFC.inv myself rhs acc_init s_iter acc1).holds
    -- Build the three invariant conjuncts (same shape as L6.3 base).
    have h_inv_pure :
        (∀ j : Nat, j < s_iter.val → ∀ ℓ : Nat, ℓ < 16 →
          Spec.mont_reduce_pure (lift_fe_int (acc1.val[16 * j + ℓ]!).val)
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))
                ((Spec.ntt_multiply_pure_no_acc
                    (lift_chunk_mont (myself.coefficients.val[j]!))
                    (lift_chunk_mont (rhs.coefficients.val[j]!))
                    (Spec.zeta_at (64 + 4 * j))
                    (Spec.zeta_at (64 + 4 * j + 1))
                    (Spec.zeta_at (64 + 4 * j + 2))
                    (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
        ∧ (∀ j : Nat, s_iter.val ≤ j → j < 16 → ∀ ℓ : Nat, ℓ < 16 →
            acc1.val[16 * j + ℓ]! = acc_init.val[16 * j + ℓ]!)
        ∧ (∀ n : Nat, n < 256 →
            (acc1.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + 2^25) := by
      refine ⟨?_, ?_, ?_⟩
      · -- (a) Touched-chunk FC.
        intro j hj ℓ hℓ
        rw [hs_val_eq] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · have h_in_range : 16 * j + ℓ < 16 * k.val := by
            have h1 : 16 * j + 16 ≤ 16 * k.val := by
              have : j + 1 ≤ k.val := by omega
              have : 16 * (j + 1) ≤ 16 * k.val := Nat.mul_le_mul_left 16 this
              omega
            omega
          have h_lt_256 : 16 * j + ℓ < 256 := by
            have : k.val ≤ 15 := by omega
            have : 16 * k.val ≤ 16 * 15 := Nat.mul_le_mul_left 16 this
            omega
          have h_acc1_eq_acc : acc1.val[16 * j + ℓ]! = acc.val[16 * j + ℓ]! :=
            h_acc1_out (16 * j + ℓ) h_lt_256 (Or.inl h_in_range)
          rw [h_acc1_eq_acc]
          exact h_acc_done j hj_lt_k ℓ hℓ
        · subst hj_eq_k
          rw [h_acc1_in ℓ hℓ]
          unfold ntt_multiply_base_case_post at h_s1_post
          have h_lhs_val_eq :
              (Spec.chunk_reducing_from_i32_array_pure s1).val[ℓ]!
                = Spec.mont_reduce_pure (lift_fe_int (s1.val[ℓ]!).val) :=
            Spec.chunk_reducing_from_i32_array_pure_lane_eq s1 ℓ hℓ
          have h_s_chunk_val :
              (Spec.chunk_reducing_from_i32_array_pure s).val[ℓ]!
                = Spec.mont_reduce_pure (lift_fe_int (s.val[ℓ]!).val) :=
            Spec.chunk_reducing_from_i32_array_pure_lane_eq s ℓ hℓ
          have h_rhs_val_eq :
              (ntt_multiply_base_case_alg
                (lift_chunk_mont t) (lift_chunk_mont t1)
                (lift_fe_mont z0) (lift_fe_mont z1)
                (lift_fe_mont z2) (lift_fe_mont z3)
                (Spec.chunk_reducing_from_i32_array_pure s)).val[ℓ]!
                = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                    ((Spec.chunk_reducing_from_i32_array_pure s).val[ℓ]!)
                    ((Spec.ntt_multiply_pure_no_acc
                        (lift_chunk_mont t) (lift_chunk_mont t1)
                        (lift_fe_mont z0) (lift_fe_mont z1)
                        (lift_fe_mont z2) (lift_fe_mont z3)).val[ℓ]!) := by
            unfold ntt_multiply_base_case_alg
            exact Spec.chunk_add_pure_lane_eq _ _ ℓ hℓ
          have h_chunk_eq :
              Spec.mont_reduce_pure (lift_fe_int (s1.val[ℓ]!).val)
                = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                    (Spec.mont_reduce_pure (lift_fe_int (s.val[ℓ]!).val))
                    ((Spec.ntt_multiply_pure_no_acc
                        (lift_chunk_mont t) (lift_chunk_mont t1)
                        (lift_fe_mont z0) (lift_fe_mont z1)
                        (lift_fe_mont z2) (lift_fe_mont z3)).val[ℓ]!) := by
            have h_eq : (Spec.chunk_reducing_from_i32_array_pure s1).val[ℓ]!
                  = (ntt_multiply_base_case_alg
                      (lift_chunk_mont t) (lift_chunk_mont t1)
                      (lift_fe_mont z0) (lift_fe_mont z1)
                      (lift_fe_mont z2) (lift_fe_mont z3)
                      (Spec.chunk_reducing_from_i32_array_pure s)).val[ℓ]! := by
              rw [h_s1_post]
            rw [h_lhs_val_eq] at h_eq
            rw [h_rhs_val_eq] at h_eq
            rw [h_s_chunk_val] at h_eq
            exact h_eq
          rw [h_chunk_eq]
          rw [h_s_lane_init ℓ hℓ]
          rw [hz0_lift, hz1_lift, hz2_lift, hz3_lift]
      · -- (b) Untouched acc chunks.
        intro j hj_ge hj_lt ℓ hℓ
        rw [hs_val_eq] at hj_ge
        have h_n_lt_256 : 16 * j + ℓ < 256 := by
          have : j ≤ 15 := by omega
          have : 16 * j ≤ 16 * 15 := Nat.mul_le_mul_left 16 this
          omega
        have h_ge_range : 16 * (k.val + 1) ≤ 16 * j + ℓ := by
          have : k.val + 1 ≤ j := hj_ge
          have : 16 * (k.val + 1) ≤ 16 * j := Nat.mul_le_mul_left 16 this
          omega
        have h_acc1_eq_acc : acc1.val[16 * j + ℓ]! = acc.val[16 * j + ℓ]! :=
          h_acc1_out (16 * j + ℓ) h_n_lt_256 (Or.inr h_ge_range)
        rw [h_acc1_eq_acc]
        exact h_acc_undone j (by omega) hj_lt ℓ hℓ
      · -- (c) Universal acc bound.
        intro n hn
        by_cases hcase : 16 * k.val ≤ n ∧ n < 16 * (k.val + 1)
        · obtain ⟨hge, hlt⟩ := hcase
          have hn_decomp : n = 16 * k.val + (n - 16 * k.val) := by omega
          have hn_off_lt : n - 16 * k.val < 16 := by omega
          have h_acc1_n : acc1.val[n]! = s1.val[n - 16 * k.val]! := by
            conv_lhs => rw [hn_decomp]
            exact h_acc1_in (n - 16 * k.val) hn_off_lt
          rw [h_acc1_n]
          have h_bnd_at_off := h_s1_bnd_abs (n - 16 * k.val) hn_off_lt
          have h_acc_init_n : acc_init.val[16 * k.val + (n - 16 * k.val)]!
                              = acc_init.val[n]! := by
            congr 1; omega
          rw [h_acc_init_n] at h_bnd_at_off
          exact h_bnd_at_off
        · have h_outside : n < 16 * k.val ∨ 16 * (k.val + 1) ≤ n := by
            by_contra hc
            push Not at hc
            exact hcase ⟨hc.1, hc.2⟩
          have h_acc1_eq_acc : acc1.val[n]! = acc.val[n]! :=
            h_acc1_out n hn h_outside
          rw [h_acc1_eq_acc]
          exact h_acc_bnd_rel n hn
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ 16, done.
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_use_cache_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) myself rhs cache
          { start := k, «end» := 16#usize } acc
        = .ok (ControlFlow.done acc) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_use_cache_loop.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    apply triple_of_ok_fc h_body
    show UseCacheFC.step_post myself rhs acc_init k (.done acc)
    unfold UseCacheFC.step_post
    show (UseCacheFC.inv myself rhs acc_init 16#usize acc).holds
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        (∀ j : Nat, j < (16#usize : Std.Usize).val → ∀ ℓ : Nat, ℓ < 16 →
          Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val)
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))
                ((Spec.ntt_multiply_pure_no_acc
                    (lift_chunk_mont (myself.coefficients.val[j]!))
                    (lift_chunk_mont (rhs.coefficients.val[j]!))
                    (Spec.zeta_at (64 + 4 * j))
                    (Spec.zeta_at (64 + 4 * j + 1))
                    (Spec.zeta_at (64 + 4 * j + 2))
                    (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 → ∀ ℓ : Nat, ℓ < 16 →
            acc.val[16 * j + ℓ]! = acc_init.val[16 * j + ℓ]!)
        ∧ (∀ n : Nat, n < 256 →
            (acc.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + 2^25) := by
      refine ⟨?_, ?_, ?_⟩
      · intro j hj ℓ hℓ; rw [h16] at hj
        apply h_acc_done j _ ℓ hℓ; rw [hk_eq]; exact hj
      · intro j hj_ge hj_lt ℓ hℓ
        rw [h16] at hj_ge
        apply h_acc_undone j _ hj_lt ℓ hℓ; rw [hk_eq]; exact hj_ge
      · intro n hn; exact h_acc_bnd_rel n hn
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

/-- L6.3c — `polynomial.PolynomialRingElement.accumulating_ntt_multiply_use_cache`:
    polynomial wrapper of `accumulating_ntt_multiply_use_cache_fc`. The cache
    is read-only here; the PRE asserts the cache satisfies
    `accumulating_ntt_multiply_poly_cache_post` (so each chunk's vector-level
    cache PRE is dischargeable from the `Spec.ntt_multiply_cache_post`
    extraction at that chunk's effective zetas).

    POST identical to L6.3 base (length + relative bound +
    `accumulating_ntt_multiply_poly_post`); no cache POST conjunct since
    `_use_cache` does not write to the cache. -/
@[spec]
theorem accumulating_ntt_multiply_use_cache_poly_fc
    (myself rhs cache : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (accumulator : Std.Array Std.I32 256#usize)
    (h_self : ∀ i : Fin 16, ∀ j : Fin 16,
        ((myself.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_rhs : ∀ i : Fin 16, ∀ j : Fin 16,
        ((rhs.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_acc_bnd : ∀ n : Fin 256, (accumulator.val[n.val]!).val.natAbs ≤ 2^30)
    (h_cache : accumulating_ntt_multiply_poly_cache_post rhs cache) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_use_cache
      (vectortraitsOperationsInst := portable_ops_inst)
      myself rhs accumulator cache
    ⦃ ⇓ r => ⌜ (∀ n : Fin 256, (r.val[n.val]!).val.natAbs
                                ≤ (accumulator.val[n.val]!).val.natAbs + 2^25) ∧
              accumulating_ntt_multiply_poly_post
                myself rhs accumulator r ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_use_cache
  have h_vre : libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
                = .ok (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
    rfl
  rw [h_vre]; simp only [Aeneas.Std.bind_tc_ok]
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_use_cache_loop
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_use_cache_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) myself rhs cache iter1 acc1)
      (β := UseCacheFC.Acc)
      accumulator
      0#usize 16#usize
      (UseCacheFC.inv myself rhs accumulator)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (by
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, ?_⟩
        · intro j hj; exact absurd hj (Nat.not_lt_zero j)
        · intro _ _ _ _ _; trivial
        · intro n _; omega)
      ?_)
  · -- Post entailment at k = 16: derive the locked POST.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (UseCacheFC.inv myself rhs accumulator 16#usize r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    obtain ⟨h_done, _h_undone, h_bnd⟩ := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_holds
    refine ⟨?_, ?_⟩
    · intro n; exact h_bnd n.val n.isLt
    · unfold accumulating_ntt_multiply_poly_post
      intro j hj ℓ hℓ
      have h16' : (16#usize : Std.Usize).val = 16 := rfl
      exact h_done j (by rw [h16']; exact hj) ℓ hℓ
  · -- Step entailment.
    intro acc k _h_ge h_le hinv
    have h_step := accumulating_ntt_multiply_use_cache_poly_step_lemma_fc
      myself rhs cache accumulator h_self h_rhs h_acc_bnd h_cache acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : UseCacheFC.step_post myself rhs accumulator k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [UseCacheFC.step_post] using hP
    · have hP : UseCacheFC.step_post myself rhs accumulator k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [UseCacheFC.step_post] using hP

end L6_3c_use_irreducible


end libcrux_iot_ml_kem.Polynomial.NttMultiply