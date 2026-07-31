/-
  # `Spec/HacspecBridge.lean` — hand spec ↔ extracted hacspec bridge (poly layer)

  The poly-layer impl FCs (`Polynomial/Arithmetic.lean::{add_fc,subtract_fc}`,
  `Polynomial/NttArith.lean::ntt_multiply_montgomery_fc`) post the impl result equal
  (through `lift_poly`) to the HAND spec `Spec.Pure.{poly_add,poly_sub,poly_pointwise_mul}`.

  This file proves the HAND spec equals the machine-EXTRACTED `hacspec_ml_dsa.*` spec
  (`HacspecMlDsa.Extraction.Funs`), so the extracted spec — not the hand spec — is the
  trusted reference. The bridge is a CLEAN-`Z_q` identity: each extracted `poly_*` is a
  `createi 256` over a closure that, on lane `k`, computes `mod_q (a[k] ±* b[k] : i64)`,
  and `mod_q` is the canonical residue map, so lifting (`((·).val : Zq)`) makes it the
  lane-wise `Z_q` op.

  Structure (mirrors ml-kem's `Util/CreateI.lean` + the hacspec bridge lemmas):
    (1) `createi_pure_eq` — port of the ml-kem pure-closure `createi` equation.
    (2) `lift_res` / `canonI32` / `lift_poly_res` + round-trip + injectivity.
    (3) `mod_q_eq` — the residue keystone (`mod_q` succeeds ∀ i64, output in `[0,Q)`,
        residue class preserved).
    (4) `poly_{add,sub,pointwise_mul}_bridge` — hand spec = extracted spec.
    (5) `poly_{add,sub,pointwise_mul}_hacspec_eq` plain lemmas (consume the impl-FC post).
-/
import LibcruxIotMlDsa.Spec.Lift
import LibcruxIotMlDsa.Util.SliceSpecs
import HacspecMlDsa.Extraction.Funs

open CoreModels Aeneas Aeneas.Std Result Std.Do

namespace libcrux_iot_ml_dsa.Spec.HacspecBridge
open libcrux_iot_ml_dsa.Spec
open libcrux_iot_ml_dsa.Spec.Parameters
open libcrux_iot_ml_dsa.Spec.Lift
open libcrux_iot_ml_dsa.Util.SliceSpecs

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## (1) `createi` machinery — port of ml-kem `Util/CreateI.lean`. -/

/-- Per-element foldlM evaluation for pure closures (private aux). -/
private theorem createi_foldlM_pure_aux
    {T F : Type}
    (inst : CoreModels.core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (l : List Nat) (acc : List T)
    (hpure : ∀ k ∈ l,
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    l.foldlM
      (fun (s : List T × F) (i : Nat) => do
        let (v, f') ← inst.call_mut s.2 ⟨BitVec.ofNat _ i⟩
        Result.ok (s.1 ++ [v], f'))
      (acc, c) = .ok (acc ++ l.map f, c) := by
  induction l generalizing acc with
  | nil =>
      simp only [List.foldlM_nil, List.map_nil, List.append_nil]
      rfl
  | cons h t ih =>
      have hh : inst.call_mut c ⟨BitVec.ofNat _ h⟩ = .ok (f h, c) :=
        hpure h List.mem_cons_self
      have ht : ∀ k ∈ t, inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) :=
        fun k hk => hpure k (List.mem_cons_of_mem _ hk)
      have hih := ih (acc ++ [f h]) ht
      simp only [List.foldlM_cons, hh, bind_tc_ok, List.map_cons]
      rw [hih]
      simp [List.append_assoc]

/-- Lean-level equation for `hacspec_ml_dsa.createi` over pure closures. Verbatim
    port of ml-kem's `createi_pure_eq` (bodies identical: `core.array.from_fn`). -/
theorem createi_pure_eq
    {T F : Type} (N : Std.Usize)
    (inst : CoreModels.core.ops.function.Fn F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      inst.FnMutInst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    hacspec_ml_dsa.createi N inst c =
      .ok ⟨(List.range N.val).map f,
           by simp [List.length_map, List.length_range]⟩ := by
  have hf : ∀ k ∈ List.range N.val,
      inst.FnMutInst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) := by
    intro k hk; exact hpure k (List.mem_range.mp hk)
  have h_fold :=
    createi_foldlM_pure_aux inst.FnMutInst c f (List.range N.val) [] hf
  simp only [List.nil_append] at h_fold
  unfold hacspec_ml_dsa.createi core.array.from_fn rust_primitives.slice.array_from_fn
  split
  · rename_i e heq
    rw [h_fold] at heq; exact absurd heq (by simp)
  · rename_i heq
    rw [h_fold] at heq; exact absurd heq (by simp)
  · rename_i result heq
    rw [h_fold] at heq
    have hres : result = ((List.range N.val).map f, c) :=
      (Result.ok.inj heq).symm
    subst hres
    rfl

/-! ## (2) lift + canon — the `Array I32 256` ↔ `SpecPoly` bridge. -/

/-- Lift a 256-cell `i32` array to a clean `Z_q` `SpecPoly` (each cell read mod `q`).
    Used on the EXTRACTED-spec carrier (`hacspec_ml_dsa` polys are `Array I32 256`). -/
def lift_res (p : Aeneas.Std.Array Std.I32 256#usize) : Pure.SpecPoly :=
  Pure.build (fun i => ((p.val[i]!).val : Zq))

/-- `(lift_res p)[i]! = (p[i].val : Zq)` for `i < 256` (via `Pure.build_getElem`). -/
theorem lift_res_getElem (p : Aeneas.Std.Array Std.I32 256#usize) (i : Nat) (hi : i < 256) :
    (lift_res p)[i]! = ((p.val[i]!).val : Zq) := by
  unfold lift_res
  rw [Pure.build_getElem _ i hi]

/-- The `[0,Q)` Int residue `z.val` lands in I32 range (`Q ≤ 2³¹−1`). -/
private theorem canonI32_bounds (z : Zq) :
    -2 ^ (IScalarTy.I32.numBits - 1) ≤ (z.val : Int)
      ∧ (z.val : Int) < 2 ^ (IScalarTy.I32.numBits - 1) := by
  have h1 : z.val < 8380417 := ZMod.val_lt z
  have hnb : IScalarTy.I32.numBits = 32 := rfl
  rw [hnb]
  refine ⟨?_, ?_⟩
  · have hnn : (0 : Int) ≤ (z.val : Int) := Int.natCast_nonneg _
    have hp : (0 : Int) ≤ 2 ^ (32 - 1) := by norm_num
    omega
  · have hlt : (z.val : Int) < (8380417 : Int) := by exact_mod_cast h1
    have hp : (8380417 : Int) ≤ 2 ^ (32 - 1) := by norm_num
    omega

/-- The canonical `i32` whose `.val` is the canonical residue `z.val` (`∈ [0,Q)`). -/
def canonI32 (z : Zq) : Std.I32 :=
  Std.I32.ofIntCore (z.val : Int) (canonI32_bounds z)

/-- `(canonI32 z).val = (z.val : Int)`. -/
theorem canonI32_val (z : Zq) : (canonI32 z).val = (z.val : Int) :=
  Std.I32.ofInt_val_eq _

/-- `canonI32 z` is canonical: `0 ≤ .val < Q`. -/
theorem canonI32_canonical (z : Zq) :
    0 ≤ (canonI32 z).val ∧ (canonI32 z).val < (Q : Int) := by
  rw [canonI32_val]
  have h := ZMod.val_lt z
  refine ⟨Int.natCast_nonneg _, ?_⟩
  have hlt : (z.val : Int) < (8380417 : Int) := by exact_mod_cast h
  have hQ : (Q : Int) = 8380417 := by norm_num [Q]
  rw [hQ]; exact hlt

/-- `canonI32` round-trips through `lift_res`'s per-cell read: `((canonI32 z).val : Zq) = z`. -/
theorem canonI32_lift (z : Zq) : (((canonI32 z).val : Int) : Zq) = z := by
  rw [canonI32_val]
  push_cast
  exact ZMod.natCast_zmod_val z

/-- Materialize a `lift_poly`'d ring element back as an `Array I32 256` (each clean
    `Z_q` coefficient re-encoded canonically via `canonI32`). The right inverse of
    `lift_res` on the image of `lift_poly`. -/
def lift_poly_res
    (re : libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
            libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) :
    Aeneas.Std.Array Std.I32 256#usize :=
  ⟨(List.range 256).map (fun i => canonI32 ((lift_poly re)[i]!)),
   by simp [List.length_map, List.length_range]⟩

/-- The underlying list of `lift_poly_res re` indexes to `canonI32 ((lift_poly re)[i]!)`. -/
private theorem lift_poly_res_getElem
    (re : libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
            libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (i : Nat) (hi : i < 256) :
    (lift_poly_res re).val[i]! = canonI32 ((lift_poly re)[i]!) := by
  show ((List.range 256).map (fun i => canonI32 ((lift_poly re)[i]!)))[i]! = _
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- Round-trip: lifting the canonical re-encoding recovers `lift_poly`. -/
theorem lift_res_lift_poly_res
    (re : libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
            libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) :
    lift_res (lift_poly_res re) = lift_poly re := by
  unfold lift_res lift_poly
  apply Pure.build_congr
  intro i hi
  -- LHS cell: `((lift_poly_res re).val[i]!).val : Zq`; rewrite the index then round-trip.
  rw [lift_poly_res_getElem re i hi, canonI32_lift]
  -- Now: `(lift_poly re)[i]! = liftZ (...)` which is exactly `Pure.build_getElem` on `lift_poly`.
  show (lift_poly re)[i]! = liftZ ((re.simd_units.val[i / 8]!).values.val[i % 8]!).val
  unfold lift_poly
  rw [Pure.build_getElem _ i hi]

/-- `lift_res` is injective on canonical (`[0,Q)` per-cell) `Array I32 256`s: equal lifts
    ⟹ equal arrays. Used to identify the `mod_q`-`.ok` result with `lift_poly_res r`. -/
theorem lift_res_inj
    (p p' : Aeneas.Std.Array Std.I32 256#usize)
    (hp : ∀ i, i < 256 → 0 ≤ p.val[i]!.val ∧ p.val[i]!.val < (Q : Int))
    (hp' : ∀ i, i < 256 → 0 ≤ p'.val[i]!.val ∧ p'.val[i]!.val < (Q : Int))
    (h : lift_res p = lift_res p') :
    p = p' := by
  -- Per-index `(p[i].val : Zq) = (p'[i].val : Zq)`.
  have hidx : ∀ i, i < 256 → ((p.val[i]!).val : Zq) = ((p'.val[i]!).val : Zq) := by
    intro i hi
    have := congrArg (fun (a : Pure.SpecPoly) => a[i]!) h
    simp only at this
    rwa [lift_res_getElem p i hi, lift_res_getElem p' i hi] at this
  -- canonical bounds + same residue ⟹ equal Int vals.
  have hval : ∀ i, i < 256 → p.val[i]!.val = p'.val[i]!.val := by
    intro i hi
    have hzq := hidx i hi
    obtain ⟨hlo, hhi⟩ := hp i hi
    obtain ⟨hlo', hhi'⟩ := hp' i hi
    -- lift the ZMod equality to a Nat equality of `.toNat`s, both `< Q`.
    have hcast : ((p.val[i]!).val.toNat : Zq) = ((p'.val[i]!).val.toNat : Zq) := by
      have e1 : ((p.val[i]!).val.toNat : Int) = (p.val[i]!).val := Int.toNat_of_nonneg hlo
      have e2 : ((p'.val[i]!).val.toNat : Int) = (p'.val[i]!).val := Int.toNat_of_nonneg hlo'
      have := hzq
      rw [← e1, ← e2] at this
      exact_mod_cast this
    -- `ZMod.val` injective on `[0,Q)` Nats.
    have hb1 : (p.val[i]!).val.toNat < Q := by
      have : (p.val[i]!).val.toNat < (Q : Int).toNat := by
        rw [Int.toNat_lt_toNat (by exact_mod_cast (by decide : (0:Int) < (8380417:Int)))]
        · exact hhi
      simpa using this
    have hb2 : (p'.val[i]!).val.toNat < Q := by
      have : (p'.val[i]!).val.toNat < (Q : Int).toNat := by
        rw [Int.toNat_lt_toNat (by exact_mod_cast (by decide : (0:Int) < (8380417:Int)))]
        · exact hhi'
      simpa using this
    have hnat : (p.val[i]!).val.toNat = (p'.val[i]!).val.toNat := by
      have hv1 := ZMod.val_natCast_of_lt hb1
      have hv2 := ZMod.val_natCast_of_lt hb2
      have := congrArg ZMod.val hcast
      rw [hv1, hv2] at this
      exact this
    have e1 : ((p.val[i]!).val.toNat : Int) = (p.val[i]!).val := Int.toNat_of_nonneg hlo
    have e2 : ((p'.val[i]!).val.toNat : Int) = (p'.val[i]!).val := Int.toNat_of_nonneg hlo'
    rw [← e1, ← e2, hnat]
  -- Array ext (Subtype on `.val`): equal lengths (256) + per-index `.val` of the `I32`s.
  apply Subtype.ext
  have hlen : p.val.length = p'.val.length := by
    rw [p.property, p'.property]
  apply List.ext_getElem hlen
  intro i hi1 hi2
  have hi256 : i < 256 := by
    have : p.val.length = 256 := p.property
    rw [this] at hi1; exact hi1
  -- turn `getElem` into `getElem!` (lists with proofs).
  have hg1 : p.val[i] = p.val[i]! := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi1]; rfl
  have hg2 : p'.val[i] = p'.val[i]! := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi2]; rfl
  rw [hg1, hg2]
  apply Aeneas.Std.IScalar.eq_of_val_eq
  exact hval i hi256

/-! ## (3) `mod_q` residue keystone.

`hacspec_ml_dsa.arithmetic.mod_q x` casts `x : i64` mod `Q` (truncated rem, sign of
dividend, so `∈ (−Q, Q)` ⊂ I32), then `+Q` when negative — landing in `[0, Q)` with no
overflow. The residue class mod `q` is preserved (`tmod` then optional `+Q`, and
`(Q : Zq) = 0`). Succeeds for ALL i64 `x`. -/

set_option maxHeartbeats 4000000 in
/-- **`mod_q` residue keystone.** `mod_q x` always succeeds; the result is the canonical
    `[0, Q)` residue of `x` (`(r.val : Zq) = (x.val : Zq)`, `0 ≤ r.val < Q`). -/
theorem mod_q_eq (x : Std.I64) :
    ∃ r : Std.I32, hacspec_ml_dsa.arithmetic.mod_q x = .ok r
      ∧ ((r.val : Int) : Zq) = ((x.val : Int) : Zq) ∧ 0 ≤ r.val ∧ r.val < (Q : Int) := by
  unfold hacspec_ml_dsa.arithmetic.mod_q
  set i : Std.I64 := Aeneas.Std.IScalar.cast .I64 hacspec_ml_dsa.parameters.Q with hi_def
  have hival : i.val = 8380417 := by rw [hi_def]; unfold hacspec_ml_dsa.parameters.Q; decide
  rw [show (Aeneas.Std.lift i : Result Std.I64) = .ok i from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  have hnz : i.val ≠ 0 := by rw [hival]; decide
  obtain ⟨i1, hi1_eq, hi1_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.rem_spec x hnz)
  rw [show (x % i : Result Std.I64) = .ok i1 from hi1_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hival] at hi1_val
  have habs : (i1.val).natAbs < 8380417 := by
    rw [hi1_val, Int.natAbs_tmod]; exact Nat.mod_lt _ (by decide)
  have hi1_bnd : -8380417 < i1.val ∧ i1.val < 8380417 := by omega
  have hcast_bnd :
      Aeneas.Std.IScalar.min .I32 ≤ i1.val ∧ i1.val ≤ Aeneas.Std.IScalar.max .I32 := by
    simp only [IScalar.min_IScalarTy_I32_eq, IScalar.max_IScalarTy_I32_eq, Aeneas.Std.I32.min,
      Aeneas.Std.I32.max, Aeneas.Std.I32.numBits, IScalarTy.I32_numBits_eq]
    omega
  obtain ⟨r0, hr0_eq, hr0_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.cast_inBounds_spec .I32 i1 hcast_bnd)
  rw [show (Aeneas.Std.lift (Aeneas.Std.IScalar.cast .I32 i1) : Result Std.I32) = .ok r0
        from hr0_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  have hres : ((i1.val : Int) : Zq) = ((x.val : Int) : Zq) := by
    rw [hi1_val, Int.tmod_def x.val 8380417]; push_cast; ring
  by_cases hneg : r0 < (0#i32 : Std.I32)
  · rw [if_pos hneg]
    have hr0_neg : r0.val < 0 := by rw [IScalar.lt_equiv] at hneg; simpa using hneg
    have hQval : (hacspec_ml_dsa.parameters.Q).val = 8380417 := by
      unfold hacspec_ml_dsa.parameters.Q; decide
    have hsum_min :
        Aeneas.Std.IScalar.min .I32 ≤ r0.val + (hacspec_ml_dsa.parameters.Q).val := by
      simp only [IScalar.min_IScalarTy_I32_eq, Aeneas.Std.I32.min, Aeneas.Std.I32.numBits,
        IScalarTy.I32_numBits_eq]
      rw [hQval, hr0_val]; omega
    have hsum_max :
        r0.val + (hacspec_ml_dsa.parameters.Q).val ≤ Aeneas.Std.IScalar.max .I32 := by
      simp only [IScalar.max_IScalarTy_I32_eq, Aeneas.Std.I32.max, Aeneas.Std.I32.numBits,
        IScalarTy.I32_numBits_eq]
      rw [hQval, hr0_val]; omega
    obtain ⟨r, hr_eq, hr_val⟩ :=
      Aeneas.Std.WP.spec_imp_exists
        (Aeneas.Std.IScalar.add_spec (x := r0) (y := hacspec_ml_dsa.parameters.Q)
          hsum_min hsum_max)
    refine ⟨r, hr_eq, ?_, ?_, ?_⟩
    · rw [hr_val, hQval, hr0_val]
      push_cast
      rw [add_zero]
      exact hres
    · rw [hr_val, hQval, hr0_val]; omega
    · rw [hr_val, hQval, hr0_val]
      have hQ : (Q : Int) = 8380417 := by norm_num [Q]
      rw [hQ]; omega
  · rw [if_neg hneg]
    have hr0_nonneg : 0 ≤ r0.val := by
      by_contra h
      simp only [not_le] at h
      exact hneg (by rw [IScalar.lt_equiv]; simpa using h)
    refine ⟨r0, rfl, ?_, hr0_nonneg, ?_⟩
    · rw [hr0_val]; exact hres
    · rw [hr0_val]
      have hQ : (Q : Int) = 8380417 := by norm_num [Q]
      rw [hQ]; omega

/-! ## (4) pure spec-bridges: hand spec = extracted spec.

Each `hacspec_ml_dsa.polynomial.poly_{add,sub,pointwise_mul}` is `createi 256` over a
closure that, on lane `k`, reads `a[k]`/`b[k]`, casts to i64, combines (`±`/`*`), and
applies `mod_q`. We feed `createi_pure_eq` the per-lane witness `f k = canonI32 ((lift_res
a)[k]! op (lift_res b)[k]!)`; the per-call equation is established by reducing the closure
and discharging the final `mod_q` with `mod_q_eq` + canonical uniqueness. -/

/-- `Array.index_usize a ⟨k⟩ = .ok (a[k]!)` for `k < 256` (avoids the `LoopHelper` import). -/
private theorem idx_ok (a : Aeneas.Std.Array Std.I32 256#usize) (k : Nat) (hk : k < 256) :
    Aeneas.Std.Array.index_usize a (⟨BitVec.ofNat _ k⟩ : Std.Usize) = .ok (a.val[k]!) := by
  have hk_us : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k := by
    show (BitVec.ofNat _ k).toNat = k
    rw [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have hbits : 2 ^ 16 ≤ 2 ^ UScalarTy.Usize.numBits :=
      Nat.pow_le_pow_right (by decide) (by
        show 16 ≤ System.Platform.numBits
        cases System.Platform.numBits_eq with
        | inl h => rw [h]; decide
        | inr h => rw [h]; decide)
    omega
  have hlen : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val < a.length := by
    rw [hk_us]; show k < a.val.length; rw [a.property]; exact hk
  have hT := Aeneas.Std.Array.index_usize_spec a (⟨BitVec.ofNat _ k⟩ : Std.Usize) hlen
  obtain ⟨v', hveq, hPv'⟩ := Aeneas.Std.WP.spec_imp_exists hT
  rw [hveq, hPv']
  simp only [hk_us]
  rw [getElem!_pos (a.val) k (by rw [a.property]; exact hk)]

/-- Sign-extending an `i32` to `i64` is always in-bounds; the `.val` is preserved. -/
private theorem cast_i64_ok (z : Std.I32) :
    ∃ w : Std.I64, Aeneas.Std.lift (Aeneas.Std.IScalar.cast .I64 z) = .ok w ∧ w.val = z.val := by
  have hb : Aeneas.Std.IScalar.min .I64 ≤ z.val ∧ z.val ≤ Aeneas.Std.IScalar.max .I64 := by
    have h1 := Aeneas.Std.IScalar.hBounds z
    simp only [IScalar.min_IScalarTy_I64_eq, IScalar.max_IScalarTy_I64_eq, Aeneas.Std.I64.min,
      Aeneas.Std.I64.max, Aeneas.Std.I64.numBits, IScalarTy.I64_numBits_eq,
      IScalarTy.I32_numBits_eq] at *
    omega
  obtain ⟨w, hweq, hwval⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.cast_inBounds_spec .I64 z hb)
  exact ⟨w, hweq, hwval⟩

/-- Canonical uniqueness: a canonical (`[0,Q)`) `i32` with residue `z` IS `canonI32 z`. -/
private theorem canonI32_eq_of_canonical (r : Std.I32) (z : Zq)
    (hlo : 0 ≤ r.val) (hhi : r.val < (Q : Int)) (hres : ((r.val : Int) : Zq) = z) :
    r = canonI32 z := by
  apply Aeneas.Std.IScalar.eq_of_val_eq
  rw [canonI32_val]
  -- reduce to `r.val = (z.val : Int)`.
  have hz : z = ((r.val.toNat : Nat) : Zq) := by
    rw [← hres]
    have e : ((r.val.toNat : Nat) : Int) = r.val := Int.toNat_of_nonneg hlo
    rw [← e]; push_cast; rfl
  have hrt : r.val.toNat < Q := by
    have : r.val.toNat < (Q : Int).toNat := by
      rw [Int.toNat_lt_toNat (by norm_num [Q])]; exact hhi
    simpa [Q] using this
  have hzv : z.val = r.val.toNat := by rw [hz]; exact ZMod.val_natCast_of_lt hrt
  rw [hzv]; exact (Int.toNat_of_nonneg hlo).symm

/-- Cell-canonicality of a `createi` result whose index fn is `canonI32 ∘ g`. -/
private theorem map_canonI32_canonical (g : Nat → Zq) (i : Nat) (hi : i < 256) :
    0 ≤ ((⟨(List.range 256).map (fun k => canonI32 (g k)), by
            simp [List.length_map, List.length_range]⟩
          : Aeneas.Std.Array Std.I32 256#usize).val[i]!).val
      ∧ ((⟨(List.range 256).map (fun k => canonI32 (g k)), by
            simp [List.length_map, List.length_range]⟩
          : Aeneas.Std.Array Std.I32 256#usize).val[i]!).val < (Q : Int) := by
  have hmap : ((List.range 256).map (fun k => canonI32 (g k)))[i]! = canonI32 (g i) := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl
  show 0 ≤ (((List.range 256).map (fun k => canonI32 (g k)))[i]!).val
    ∧ (((List.range 256).map (fun k => canonI32 (g k)))[i]!).val < (Q : Int)
  rw [hmap]
  exact canonI32_canonical (g i)

set_option maxHeartbeats 4000000 in
/-- **Hand-spec = extracted-spec for `poly_add`.** `hacspec_ml_dsa.polynomial.poly_add`
    succeeds, and its lift equals `Pure.poly_add` (lane-wise `+` in `Z_q`). -/
theorem poly_add_bridge (a b : Aeneas.Std.Array Std.I32 256#usize) :
    ∃ r, hacspec_ml_dsa.polynomial.poly_add a b = .ok r
      ∧ lift_res r = Pure.poly_add (lift_res a) (lift_res b)
      ∧ (∀ i, i < 256 → 0 ≤ r.val[i]!.val ∧ r.val[i]!.val < (Q : Int)) := by
  set f : Nat → Std.I32 :=
    fun k => canonI32 ((lift_res a)[k]! + (lift_res b)[k]!) with hf_def
  have hpure : ∀ k : Nat, k < (256#usize : Std.Usize).val →
      (hacspec_ml_dsa.polynomial.poly_add.closure.Insts.CoreOpsFunctionFnTupleUsizeI32
        : CoreModels.core.ops.function.Fn _ _ _).FnMutInst.call_mut
          (a, b) ⟨BitVec.ofNat _ k⟩ = .ok (f k, (a, b)) := by
    intro k hk
    have hk' : k < 256 := hk
    obtain ⟨wa, hwa_eq, hwa_val⟩ := cast_i64_ok (a.val[k]!)
    obtain ⟨wb, hwb_eq, hwb_val⟩ := cast_i64_ok (b.val[k]!)
    have ha := Aeneas.Std.IScalar.hBounds (a.val[k]!)
    have hbb := Aeneas.Std.IScalar.hBounds (b.val[k]!)
    simp only [IScalarTy.I32_numBits_eq] at ha hbb
    have hsum : ∃ s : Std.I64, (wa + wb : Result Std.I64) = .ok s ∧ s.val = wa.val + wb.val := by
      have hmin : Aeneas.Std.IScalar.min .I64 ≤ wa.val + wb.val := by
        simp only [IScalar.min_IScalarTy_I64_eq, Aeneas.Std.I64.min, Aeneas.Std.I64.numBits,
          IScalarTy.I64_numBits_eq, hwa_val, hwb_val]; omega
      have hmax : wa.val + wb.val ≤ Aeneas.Std.IScalar.max .I64 := by
        simp only [IScalar.max_IScalarTy_I64_eq, Aeneas.Std.I64.max, Aeneas.Std.I64.numBits,
          IScalarTy.I64_numBits_eq, hwa_val, hwb_val]; omega
      obtain ⟨s, hs_eq, hs_val⟩ :=
        Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.add_spec (x := wa) (y := wb) hmin hmax)
      exact ⟨s, hs_eq, hs_val⟩
    obtain ⟨s, hs_eq, hs_val⟩ := hsum
    obtain ⟨r, hr_eq, hr_res, hr_lo, hr_hi⟩ := mod_q_eq s
    have hr_fk : r = f k := by
      rw [hf_def]
      apply canonI32_eq_of_canonical r _ hr_lo hr_hi
      rw [hr_res, hs_val, hwa_val, hwb_val, lift_res_getElem a k hk', lift_res_getElem b k hk']
      push_cast; ring
    rw [hr_fk] at hr_eq
    show hacspec_ml_dsa.polynomial.poly_add.closure.Insts.CoreOpsFunctionFnMutTupleUsizeI32.call_mut
        (a, b) ⟨BitVec.ofNat _ k⟩ = .ok (f k, (a, b))
    unfold hacspec_ml_dsa.polynomial.poly_add.closure.Insts.CoreOpsFunctionFnMutTupleUsizeI32.call_mut
    unfold hacspec_ml_dsa.polynomial.poly_add.closure.Insts.CoreOpsFunctionFnTupleUsizeI32.call
    change (do
        let i ← (do
          let i ← Aeneas.Std.Array.index_usize a ⟨BitVec.ofNat _ k⟩
          let i1 ← Aeneas.Std.lift (Aeneas.Std.IScalar.cast .I64 i)
          let i2 ← Aeneas.Std.Array.index_usize b ⟨BitVec.ofNat _ k⟩
          let i3 ← Aeneas.Std.lift (Aeneas.Std.IScalar.cast .I64 i2)
          let i4 ← i1 + i3
          hacspec_ml_dsa.arithmetic.mod_q i4)
        Result.ok (i, (a, b)))
      = .ok (f k, (a, b))
    rw [idx_ok a k hk']; simp only [bind_tc_ok]
    rw [hwa_eq]; simp only [bind_tc_ok]
    rw [idx_ok b k hk']; simp only [bind_tc_ok]
    rw [hwb_eq]; simp only [bind_tc_ok]
    rw [hs_eq]; simp only [bind_tc_ok]
    rw [hr_eq]; rfl
  have heq := createi_pure_eq (T := Std.I32)
    (F := hacspec_ml_dsa.polynomial.poly_add.closure)
    256#usize
    hacspec_ml_dsa.polynomial.poly_add.closure.Insts.CoreOpsFunctionFnTupleUsizeI32
    (a, b) f hpure
  have heq' : hacspec_ml_dsa.polynomial.poly_add a b
      = .ok ⟨(List.range (256#usize : Std.Usize).val).map f,
             by simp [List.length_map, List.length_range]⟩ := by
    unfold hacspec_ml_dsa.polynomial.poly_add; exact heq
  refine ⟨_, heq', ?_, ?_⟩
  · -- `lift_res (createi result) = Pure.poly_add (lift_res a) (lift_res b)`.
    conv_lhs => unfold lift_res
    unfold Pure.poly_add
    apply Pure.build_congr
    intro i hi
    show (((⟨(List.range 256).map f, _⟩ : Aeneas.Std.Array Std.I32 256#usize).val[i]!).val : Zq) = _
    have hmap : ((List.range 256).map f)[i]! = f i := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl
    rw [hmap, hf_def, canonI32_lift]
  · intro i hi
    exact map_canonI32_canonical (fun k => (lift_res a)[k]! + (lift_res b)[k]!) i hi

set_option maxHeartbeats 4000000 in
/-- **Hand-spec = extracted-spec for `poly_sub`.** Clone of `poly_add_bridge` with `-`. -/
theorem poly_sub_bridge (a b : Aeneas.Std.Array Std.I32 256#usize) :
    ∃ r, hacspec_ml_dsa.polynomial.poly_sub a b = .ok r
      ∧ lift_res r = Pure.poly_sub (lift_res a) (lift_res b)
      ∧ (∀ i, i < 256 → 0 ≤ r.val[i]!.val ∧ r.val[i]!.val < (Q : Int)) := by
  set f : Nat → Std.I32 :=
    fun k => canonI32 ((lift_res a)[k]! - (lift_res b)[k]!) with hf_def
  have hpure : ∀ k : Nat, k < (256#usize : Std.Usize).val →
      (hacspec_ml_dsa.polynomial.poly_sub.closure.Insts.CoreOpsFunctionFnTupleUsizeI32
        : CoreModels.core.ops.function.Fn _ _ _).FnMutInst.call_mut
          (a, b) ⟨BitVec.ofNat _ k⟩ = .ok (f k, (a, b)) := by
    intro k hk
    have hk' : k < 256 := hk
    obtain ⟨wa, hwa_eq, hwa_val⟩ := cast_i64_ok (a.val[k]!)
    obtain ⟨wb, hwb_eq, hwb_val⟩ := cast_i64_ok (b.val[k]!)
    have ha := Aeneas.Std.IScalar.hBounds (a.val[k]!)
    have hbb := Aeneas.Std.IScalar.hBounds (b.val[k]!)
    simp only [IScalarTy.I32_numBits_eq] at ha hbb
    have hdiff : ∃ s : Std.I64, (wa - wb : Result Std.I64) = .ok s ∧ s.val = wa.val - wb.val := by
      have hmin : Aeneas.Std.IScalar.min .I64 ≤ wa.val - wb.val := by
        simp only [IScalar.min_IScalarTy_I64_eq, Aeneas.Std.I64.min, Aeneas.Std.I64.numBits,
          IScalarTy.I64_numBits_eq, hwa_val, hwb_val]; omega
      have hmax : wa.val - wb.val ≤ Aeneas.Std.IScalar.max .I64 := by
        simp only [IScalar.max_IScalarTy_I64_eq, Aeneas.Std.I64.max, Aeneas.Std.I64.numBits,
          IScalarTy.I64_numBits_eq, hwa_val, hwb_val]; omega
      obtain ⟨s, hs_eq, hs_val⟩ :=
        Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.sub_spec (x := wa) (y := wb) hmin hmax)
      exact ⟨s, hs_eq, hs_val⟩
    obtain ⟨s, hs_eq, hs_val⟩ := hdiff
    obtain ⟨r, hr_eq, hr_res, hr_lo, hr_hi⟩ := mod_q_eq s
    have hr_fk : r = f k := by
      rw [hf_def]
      apply canonI32_eq_of_canonical r _ hr_lo hr_hi
      rw [hr_res, hs_val, hwa_val, hwb_val, lift_res_getElem a k hk', lift_res_getElem b k hk']
      push_cast; ring
    rw [hr_fk] at hr_eq
    show hacspec_ml_dsa.polynomial.poly_sub.closure.Insts.CoreOpsFunctionFnMutTupleUsizeI32.call_mut
        (a, b) ⟨BitVec.ofNat _ k⟩ = .ok (f k, (a, b))
    unfold hacspec_ml_dsa.polynomial.poly_sub.closure.Insts.CoreOpsFunctionFnMutTupleUsizeI32.call_mut
    unfold hacspec_ml_dsa.polynomial.poly_sub.closure.Insts.CoreOpsFunctionFnTupleUsizeI32.call
    change (do
        let i ← (do
          let i ← Aeneas.Std.Array.index_usize a ⟨BitVec.ofNat _ k⟩
          let i1 ← Aeneas.Std.lift (Aeneas.Std.IScalar.cast .I64 i)
          let i2 ← Aeneas.Std.Array.index_usize b ⟨BitVec.ofNat _ k⟩
          let i3 ← Aeneas.Std.lift (Aeneas.Std.IScalar.cast .I64 i2)
          let i4 ← i1 - i3
          hacspec_ml_dsa.arithmetic.mod_q i4)
        Result.ok (i, (a, b)))
      = .ok (f k, (a, b))
    rw [idx_ok a k hk']; simp only [bind_tc_ok]
    rw [hwa_eq]; simp only [bind_tc_ok]
    rw [idx_ok b k hk']; simp only [bind_tc_ok]
    rw [hwb_eq]; simp only [bind_tc_ok]
    rw [hs_eq]; simp only [bind_tc_ok]
    rw [hr_eq]; rfl
  have heq := createi_pure_eq (T := Std.I32)
    (F := hacspec_ml_dsa.polynomial.poly_sub.closure)
    256#usize
    hacspec_ml_dsa.polynomial.poly_sub.closure.Insts.CoreOpsFunctionFnTupleUsizeI32
    (a, b) f hpure
  have heq' : hacspec_ml_dsa.polynomial.poly_sub a b
      = .ok ⟨(List.range (256#usize : Std.Usize).val).map f,
             by simp [List.length_map, List.length_range]⟩ := by
    unfold hacspec_ml_dsa.polynomial.poly_sub; exact heq
  refine ⟨_, heq', ?_, ?_⟩
  · conv_lhs => unfold lift_res
    unfold Pure.poly_sub
    apply Pure.build_congr
    intro i hi
    show (((⟨(List.range 256).map f, _⟩ : Aeneas.Std.Array Std.I32 256#usize).val[i]!).val : Zq) = _
    have hmap : ((List.range 256).map f)[i]! = f i := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl
    rw [hmap, hf_def, canonI32_lift]
  · intro i hi
    exact map_canonI32_canonical (fun k => (lift_res a)[k]! - (lift_res b)[k]!) i hi

set_option maxHeartbeats 4000000 in
/-- **Hand-spec = extracted-spec for `poly_pointwise_mul`.** Clone with `*`; the i64
    product of two i32s stays in range (`|i32|² < 2⁶²`). -/
theorem poly_pointwise_mul_bridge (a b : Aeneas.Std.Array Std.I32 256#usize) :
    ∃ r, hacspec_ml_dsa.polynomial.poly_pointwise_mul a b = .ok r
      ∧ lift_res r = Pure.poly_pointwise_mul (lift_res a) (lift_res b)
      ∧ (∀ i, i < 256 → 0 ≤ r.val[i]!.val ∧ r.val[i]!.val < (Q : Int)) := by
  set f : Nat → Std.I32 :=
    fun k => canonI32 ((lift_res a)[k]! * (lift_res b)[k]!) with hf_def
  have hpure : ∀ k : Nat, k < (256#usize : Std.Usize).val →
      (hacspec_ml_dsa.polynomial.poly_pointwise_mul.closure.Insts.CoreOpsFunctionFnTupleUsizeI32
        : CoreModels.core.ops.function.Fn _ _ _).FnMutInst.call_mut
          (a, b) ⟨BitVec.ofNat _ k⟩ = .ok (f k, (a, b)) := by
    intro k hk
    have hk' : k < 256 := hk
    obtain ⟨wa, hwa_eq, hwa_val⟩ := cast_i64_ok (a.val[k]!)
    obtain ⟨wb, hwb_eq, hwb_val⟩ := cast_i64_ok (b.val[k]!)
    have ha := Aeneas.Std.IScalar.hBounds (a.val[k]!)
    have hbb := Aeneas.Std.IScalar.hBounds (b.val[k]!)
    simp only [IScalarTy.I32_numBits_eq] at ha hbb
    have hprod : ∃ s : Std.I64, (wa * wb : Result Std.I64) = .ok s ∧ s.val = wa.val * wb.val := by
      have ha1 : -2147483648 ≤ wa.val := by rw [hwa_val]; omega
      have ha2 : wa.val ≤ 2147483647 := by rw [hwa_val]; omega
      have hb1 : -2147483648 ≤ wb.val := by rw [hwb_val]; omega
      have hb2 : wb.val ≤ 2147483647 := by rw [hwb_val]; omega
      have hprodlo : (-4611686018427387904 : Int) ≤ wa.val * wb.val := by nlinarith
      have hprodhi : wa.val * wb.val ≤ (4611686018427387904 : Int) := by nlinarith
      have hmin : Aeneas.Std.IScalar.min .I64 ≤ wa.val * wb.val := by
        simp only [IScalar.min_IScalarTy_I64_eq, Aeneas.Std.I64.min, Aeneas.Std.I64.numBits,
          IScalarTy.I64_numBits_eq]
        norm_num; omega
      have hmax : wa.val * wb.val ≤ Aeneas.Std.IScalar.max .I64 := by
        simp only [IScalar.max_IScalarTy_I64_eq, Aeneas.Std.I64.max, Aeneas.Std.I64.numBits,
          IScalarTy.I64_numBits_eq]
        norm_num; omega
      obtain ⟨s, hs_eq, hs_val⟩ :=
        Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.mul_spec (x := wa) (y := wb) hmin hmax)
      exact ⟨s, hs_eq, hs_val⟩
    obtain ⟨s, hs_eq, hs_val⟩ := hprod
    obtain ⟨r, hr_eq, hr_res, hr_lo, hr_hi⟩ := mod_q_eq s
    have hr_fk : r = f k := by
      rw [hf_def]
      apply canonI32_eq_of_canonical r _ hr_lo hr_hi
      rw [hr_res, hs_val, hwa_val, hwb_val, lift_res_getElem a k hk', lift_res_getElem b k hk']
      push_cast; ring
    rw [hr_fk] at hr_eq
    show hacspec_ml_dsa.polynomial.poly_pointwise_mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeI32.call_mut
        (a, b) ⟨BitVec.ofNat _ k⟩ = .ok (f k, (a, b))
    unfold hacspec_ml_dsa.polynomial.poly_pointwise_mul.closure.Insts.CoreOpsFunctionFnMutTupleUsizeI32.call_mut
    unfold hacspec_ml_dsa.polynomial.poly_pointwise_mul.closure.Insts.CoreOpsFunctionFnTupleUsizeI32.call
    change (do
        let i ← (do
          let i ← Aeneas.Std.Array.index_usize a ⟨BitVec.ofNat _ k⟩
          let i1 ← Aeneas.Std.lift (Aeneas.Std.IScalar.cast .I64 i)
          let i2 ← Aeneas.Std.Array.index_usize b ⟨BitVec.ofNat _ k⟩
          let i3 ← Aeneas.Std.lift (Aeneas.Std.IScalar.cast .I64 i2)
          let i4 ← i1 * i3
          hacspec_ml_dsa.arithmetic.mod_q i4)
        Result.ok (i, (a, b)))
      = .ok (f k, (a, b))
    rw [idx_ok a k hk']; simp only [bind_tc_ok]
    rw [hwa_eq]; simp only [bind_tc_ok]
    rw [idx_ok b k hk']; simp only [bind_tc_ok]
    rw [hwb_eq]; simp only [bind_tc_ok]
    rw [hs_eq]; simp only [bind_tc_ok]
    rw [hr_eq]; rfl
  have heq := createi_pure_eq (T := Std.I32)
    (F := hacspec_ml_dsa.polynomial.poly_pointwise_mul.closure)
    256#usize
    hacspec_ml_dsa.polynomial.poly_pointwise_mul.closure.Insts.CoreOpsFunctionFnTupleUsizeI32
    (a, b) f hpure
  have heq' : hacspec_ml_dsa.polynomial.poly_pointwise_mul a b
      = .ok ⟨(List.range (256#usize : Std.Usize).val).map f,
             by simp [List.length_map, List.length_range]⟩ := by
    unfold hacspec_ml_dsa.polynomial.poly_pointwise_mul; exact heq
  refine ⟨_, heq', ?_, ?_⟩
  · conv_lhs => unfold lift_res
    unfold Pure.poly_pointwise_mul
    apply Pure.build_congr
    intro i hi
    show (((⟨(List.range 256).map f, _⟩ : Aeneas.Std.Array Std.I32 256#usize).val[i]!).val : Zq) = _
    have hmap : ((List.range 256).map f)[i]! = f i := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl
    rw [hmap, hf_def, canonI32_lift]
  · intro i hi
    exact map_canonI32_canonical (fun k => (lift_res a)[k]! * (lift_res b)[k]!) i hi

/-! ## (5) hacspec-facing plain lemmas (consume the impl-FC post).

Each `_hacspec_eq` lemma takes the impl-FC conclusion (`lift_poly r = Pure.poly_op …`) and
concludes the extracted spec on the canonical re-encodings: `hacspec_ml_dsa…poly_op
(lift_poly_res self) (lift_poly_res rhs) = .ok (lift_poly_res r)`. The `_hacspec_fc` Triple
corollaries (composing `add_fc`/`subtract_fc`/`ntt_multiply_montgomery_fc`) live in
`Polynomial/HacspecFC.lean` where the impl FCs are in scope. -/

/-- `lift_poly_res` cells are canonical (`[0,Q)`) — they are `canonI32` re-encodings. -/
theorem lift_poly_res_canonical
    (re : libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
            libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (i : Nat) (hi : i < 256) :
    0 ≤ (lift_poly_res re).val[i]!.val ∧ (lift_poly_res re).val[i]!.val < (Q : Int) := by
  rw [lift_poly_res_getElem re i hi]
  exact canonI32_canonical _

/-- **`poly_add` hacspec corollary (plain).** From the impl-FC functional post
    (`lift_poly r = Pure.poly_add …`), the extracted `poly_add` on the canonical
    re-encodings returns `lift_poly_res r`. -/
theorem poly_add_hacspec_eq
    (self rhs r : libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
                    libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (h_impl : lift_poly r = Pure.poly_add (lift_poly self) (lift_poly rhs)) :
    hacspec_ml_dsa.polynomial.poly_add (lift_poly_res self) (lift_poly_res rhs)
      = .ok (lift_poly_res r) := by
  obtain ⟨r', hr'_eq, hr'_lift, hr'_bnd⟩ := poly_add_bridge (lift_poly_res self) (lift_poly_res rhs)
  rw [hr'_eq]
  congr 1
  apply lift_res_inj r' (lift_poly_res r) hr'_bnd
    (fun i hi => lift_poly_res_canonical r i hi)
  rw [hr'_lift, lift_res_lift_poly_res self, lift_res_lift_poly_res rhs, ← h_impl,
      lift_res_lift_poly_res r]

/-- **`poly_sub` hacspec corollary (plain).** -/
theorem poly_sub_hacspec_eq
    (self rhs r : libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
                    libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (h_impl : lift_poly r = Pure.poly_sub (lift_poly self) (lift_poly rhs)) :
    hacspec_ml_dsa.polynomial.poly_sub (lift_poly_res self) (lift_poly_res rhs)
      = .ok (lift_poly_res r) := by
  obtain ⟨r', hr'_eq, hr'_lift, hr'_bnd⟩ := poly_sub_bridge (lift_poly_res self) (lift_poly_res rhs)
  rw [hr'_eq]
  congr 1
  apply lift_res_inj r' (lift_poly_res r) hr'_bnd
    (fun i hi => lift_poly_res_canonical r i hi)
  rw [hr'_lift, lift_res_lift_poly_res self, lift_res_lift_poly_res rhs, ← h_impl,
      lift_res_lift_poly_res r]

/-- **`poly_pointwise_mul` hacspec corollary (plain).** -/
theorem poly_pointwise_mul_hacspec_eq
    (lhs rhs r : libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
                   libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (h_impl : lift_poly r = Pure.poly_pointwise_mul (lift_poly lhs) (lift_poly rhs)) :
    hacspec_ml_dsa.polynomial.poly_pointwise_mul (lift_poly_res lhs) (lift_poly_res rhs)
      = .ok (lift_poly_res r) := by
  obtain ⟨r', hr'_eq, hr'_lift, hr'_bnd⟩ :=
    poly_pointwise_mul_bridge (lift_poly_res lhs) (lift_poly_res rhs)
  rw [hr'_eq]
  congr 1
  apply lift_res_inj r' (lift_poly_res r) hr'_bnd
    (fun i hi => lift_poly_res_canonical r i hi)
  rw [hr'_lift, lift_res_lift_poly_res lhs, lift_res_lift_poly_res rhs, ← h_impl,
      lift_res_lift_poly_res r]

end libcrux_iot_ml_dsa.Spec.HacspecBridge
