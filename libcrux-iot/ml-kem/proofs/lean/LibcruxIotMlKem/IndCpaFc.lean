/-
  # `IndCpaFc.lean` — INC-2 lane 2a obligations for the `ind_cpa` (k-PKE) layer.

  The statement below was authored by the HELPER as a *low-distance binding* to the
  EXISTING `hacspec_ml_kem` model — nothing here invents a spec. It was dispatched to a
  PROVER as an obligation and is now CLOSED (INC-2a.1, 2026-08-19): zero sorries, axioms
  exactly `propext / Classical.choice / Quot.sound` — in particular NOT the A2 axiom, since
  its per-element leaf is the proved L5.7 `deserialize_to_uncompressed_ring_element_fc`.
  The statement itself is unchanged from the scaffold, byte for byte.

  Why a new file rather than another section of `SerializeFc.lean`: that file reached zero
  sorries and ~9000 lines, and its own line-numbered prose has already gone stale twice
  under insertion. A separate file also keeps the PROVER's writable surface to exactly the
  obligation being closed.

  ## Scope of THIS file (INC-2 lane 2a, see `plans/INC-2-scope.md`)
  The deterministic half of `ind_cpa`. The sampling half (lane 2b) is not extracted and is
  a separate project. `decrypt` / `decrypt_unpacked` are NOT here: they call
  `deserialize_then_decompress_u`, i.e. the `_u` family, which is unscaffolded pending a
  PRINCIPAL modelling decision (scope §5.1).
-/
import LibcruxIotMlKem.SerializeFc
import LibcruxIotMlKem.Util.Shared

-- Same open-set as `SerializeFc.lean`: the Triple notation `⦃ ⌜_⌝ ⦄ … ⦃ ⇓_ => ⌜_⌝ ⦄`
-- comes from `Std.Do`, and omitting it fails at the FIRST `⌜` with a bare
-- "unexpected token" — which is what a sketched statement looks like when it has never
-- been elaborated (readiness map A4).
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Util.Shared
-- The d=12 decode/length facts this file shares with SerializeFc are PUBLIC there as of
-- 2026-08-19 rather than copied here (they were, 11 of them). See Util/Shared.lean's header.
open libcrux_iot_ml_kem.SerializeFc
open libcrux_iot_ml_kem
open libcrux_iot_ml_kem.Spec
open libcrux_iot_ml_kem.Spec.Lift

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace libcrux_iot_ml_kem.IndCpaFc

/-! ## PROVER bank for INC-2a.1

    Two halves, mirroring L5.5 (`deserialize_ring_elements_reduced_fc`):

    * **SPEC side** (`spec_vector_decode_12_eq`): the hacspec `vector_decode_12 K` is a
      `createi K` whose closure slices the 384-byte window `[k*384, k*384+384)` — i.e.
      exactly `Spec.pk_chunk` — and `byte_decode`s it at `d = 12`. So the whole `createi`
      collapses to `Spec.t_as_ntt_from_public_key_pure`. NO bit-level reasoning enters:
      the only fact needed about the decode atom is that it SUCCEEDS on a 384-byte slice,
      and here that comes for free from the PROVED leaf L5.7
      (`deserialize_to_uncompressed_ring_element_fc`) rather than from a spec-side
      re-derivation — which is exactly the sense in which this obligation is easier than
      L5.5.
    * **IMPL side** (`dv_loop_fc`): a plain `for i in 0..K` with explicit slicing, so the
      combinator is `Util.LoopSpecs.loop_range_spec_usize`, NOT the `chunks_exact`
      family (`loop_chunks_exact_pk_spec` / `loop_chunks_exact_enumerate_spec` both
      describe `Enumerate (ChunksExact cs)` iterators, which this loop does not build —
      see the exemplar dispositions in the self-report). The invariant is the written
      prefix; the per-chunk leaf is L5.7.

    Everything in this section is `private`: the L5.5 bank it parallels is `private` in
    `SerializeFc.lean` and therefore unreachable from here, so the small plumbing bridges
    are restated, each marked with its `SerializeFc.lean` source. The two exceptions are
    `triple_exists_ok_fc` / `triple_of_ok_fc`, which DO have a public copy in the tree and
    are forwarded to it rather than restated. -/

section DVBank

open libcrux_iot_ml_kem.Util.LoopSpecs
open libcrux_iot_ml_kem.Util.CreateI

/-! ### Triple ↔ `Result` plumbing.

    These two are NOT restated: statement-identical copies are already PUBLIC and reachable
    from here at `Vector/Portable/Arithmetic/PerElement.lean:1399/1406`, so they are simply
    forwarded. (The tree carries NINE copies of this pair — `SerializeFc.lean:576/624`,
    `ComputeRingElementV/{FC:47,56, Impl:45}`, `ComputeVectorU/{FC:50,59, Impl:63,72}`,
    `ComputeMessage/{FC:36,45, Impl:46,56}`, `ComputeVectorU/Hacspec.lean:255/261` primed —
    all but the `PerElement` one `private`. Hoisting them into `Util/` is a tree-level task,
    but nothing forces a tenth copy here.)

    `holds_ok` below has no public copy anywhere, so it IS restated (`SerializeFc.lean:631`). -/




/-! ### `Usize` arithmetic bridges (`SerializeFc.lean:849/1470/1476/3719/3737`). -/






/-! ### `Slice` bridges (`SerializeFc.lean:3259/3266/3853/3858/4030/4037/4042`). -/








/-! ### The two `BYTES_PER_RING_ELEMENT` constants (`SerializeFc.lean:3746/3758`).
    Both are `irreducible`, so each needs its explicit unfolding. -/



/-! ### `Spec.pk_chunk` -/


/-- The explicit `[384i, 384(i+1))` window the IMPL slices IS `Spec.pk_chunk`. -/
private theorem window_eq_pk_chunk (secret_key : Slice Std.U8) (a b : Std.Usize) (i : Nat)
    (ha : a.val = i * 384) (hb : b.val = i * 384 + 384) :
    (⟨List.slice a.val b.val secret_key.val, by
        have := secret_key.val.slice_length_le a.val b.val; scalar_tac⟩ : Slice Std.U8)
      = Spec.pk_chunk secret_key i := by
  apply Subtype.ext
  show List.slice a.val b.val secret_key.val
      = (secret_key.val.drop (i * 384)).take 384
  unfold List.slice
  rw [ha, hb]
  congr 1
  omega

/-! ### The decode atom: `byte_decode_dyn` at `d = 12` never fails.

    `SerializeFc.lean`'s `byte_decode_dyn_12_ok` (:3779) proves this from its own
    spec-side bit bank (`byte_decode_generic_12_get` + `byte_decode_closure_eq`).
    Here it comes from the PROVED leaf L5.7 instead: L5.7 says the IMPL succeeds on
    every 384-byte slice AND that `byte_decode_dyn` agrees with it, so success of
    `byte_decode_dyn` is a corollary and no bit-level reasoning is needed at all.
    The array-shaped form the `vector_decode_12` closure calls is then pure
    plumbing (`byte_decode_dyn_12_arr`). -/

/-- `byte_decode_dyn b 12` IS the array-shaped `byte_decode 3072 · 12` on a 384-byte
    slice. Plumbing only (the `d.val = 12` branch of `byte_decode_dyn`). -/
private theorem byte_decode_dyn_12_arr (b : Slice Std.U8) (hb : b.val.length = 384) :
    hacspec_ml_kem.serialize.byte_decode_dyn b 12#usize
      = hacspec_ml_kem.serialize.byte_decode (D32 := 384#usize) 3072#usize
          (⟨b.val, by rw [hb]; scalar_tac⟩ : Std.Array Std.U8 384#usize) 12#usize := by
  have e2 : ((32#usize : Std.Usize) * (12#usize : Std.Usize) : Result Std.Usize)
      = .ok (384#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have hlen := slice_len_384 b hb
  have hl := slice_len_eq_384 b hb
  unfold hacspec_ml_kem.serialize.byte_decode_dyn
  simp only [hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT, Aeneas.Std.massert,
    le_refl, if_true, Aeneas.Std.bind_tc_ok, hlen, e2]
  show (do
      let r ←
        CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
          (384#usize : Std.Usize) b
      let a' ←
        CoreModels.core.result.Result.unwrap
          CoreModels.core.array.TryFromSliceError.Insts.CoreFmtDebug r
      hacspec_ml_kem.serialize.byte_decode (D32 := 384#usize) 3072#usize a' 12#usize) = _
  rw [show
      CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
          (384#usize : Std.Usize) b
        = .ok (CoreModels.core.result.Result.Ok
            (⟨b.val, by rw [hb]; scalar_tac⟩ : Std.Array Std.U8 384#usize)) from by
    unfold
      CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
    rw [dif_pos hl]]
  simp only [Aeneas.Std.bind_tc_ok, CoreModels.core.result.Result.unwrap]


/-! ### SPEC side — `vector_decode_12` IS the pure model. -/


/-- **The spec bridge.** The hacspec rank-K 12-bit decode is the pure model
    `Spec.t_as_ntt_from_public_key_pure`, i.e. `lift_t_as_ntt_from_public_key`
    (`SerializeFc.lean:3969`, with the `deserialize_ring_elements_reduced` wrapper
    peeled off — that def is literally `do vector_decode_12 RANK encoded`). -/
private theorem spec_vector_decode_12_eq (K : Std.Usize) (secret_key : Slice Std.U8)
    (h_sk : secret_key.val.length = K.val * 384) :
    hacspec_ml_kem.serialize.vector_decode_12 K secret_key
      = .ok (lift_t_as_ntt_from_public_key secret_key K) := by
  have hKmax : K.val * 384 ≤ Std.Usize.max := by
    rw [← h_sk]; exact secret_key.property
  obtain ⟨tot, htot_eq, htot_val⟩ :=
    usize_mul_ok_e K (384#usize : Std.Usize) (by scalar_tac)
  have htot_val' : tot.val = K.val * 384 := by rw [htot_val]; scalar_tac
  have hlen_eq : Aeneas.Std.Slice.len secret_key = tot := by
    apply Aeneas.Std.UScalar.eq_of_val_eq
    rw [Aeneas.Std.Slice.len_val, htot_val']
    exact h_sk
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
      (T := Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
      K
      (hacspec_ml_kem.serialize.vector_decode_12.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256
        K)
      secret_key
      (fun k => (Spec.t_as_ntt_from_public_key_pure secret_key K).val[k]!)
      (fun k hk => vector_decode_12_closure_eq K secret_key h_sk k hk)
  unfold hacspec_ml_kem.serialize.vector_decode_12
  rw [slice_len_gen secret_key]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hacspec_bpre]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [htot_eq]
  simp only [Aeneas.Std.bind_tc_ok, hlen_eq, Aeneas.Std.massert, if_true,
    hacspec_ml_kem.parameters.createi, hfn]
  congr 1
  apply Subtype.ext
  show (List.range K.val).map
        (fun k => (Spec.t_as_ntt_from_public_key_pure secret_key K).val[k]!)
      = (Spec.t_as_ntt_from_public_key_pure secret_key K).val
  have hval : (Spec.t_as_ntt_from_public_key_pure secret_key K).val.length = K.val :=
    (Spec.t_as_ntt_from_public_key_pure secret_key K).property
  refine List.ext_getElem (by simp [hval]) ?_
  intro n h1 h2
  rw [List.getElem_map, List.getElem_range]
  rw [getElem!_pos _ _ (by rw [hval]; simpa using h1)]

/-! ### IMPL side — the rank-K `0..K` range loop with explicit slicing.

    The combinator is `Util.LoopSpecs.loop_range_spec_usize`: the impl builds a plain
    `core.ops.range.Range Usize` iterator and slices `secret_key[384i .. 384(i+1)]` by
    hand, so neither `chunks_exact` exemplar applies. The invariant is the written
    prefix; no undone-cells conjunct is needed because the post only speaks about
    indices `< K`. -/



/-- Written-prefix invariant for the rank-K secret-key decode loop. The bound is
    `≤ 4095`, i.e. L5.7's own per-element post lifted pointwise — the impl's
    uncompressed decode runs no `cond_subtract_3329`, so `≤ 3328` would be FALSE
    (attained at an all-`0xFF` key). -/
private def dvInv (secret_key : Slice Std.U8) (K : Std.Usize) (k : Nat)
    (p : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)) : Prop :=
  p.length = K.val
  ∧ (∀ i : Nat, i < k →
      lift_poly (p.val[i]!) = (lift_t_as_ntt_from_public_key secret_key K).val[i]!)
  ∧ (∀ i : Nat, i < k → ∀ c : Nat, c < 16 → ∀ ℓ : Nat, ℓ < 16 →
      (((p.val[i]!).coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 4095)

/-- The `i`-th cell of the pure model IS the L5.7 decode of the `i`-th window. -/
private theorem pure_cell_eq (K : Std.Usize) (secret_key : Slice Std.U8) (i : Nat)
    (hi : i < K.val)
    (te : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hte : hacspec_ml_kem.serialize.byte_decode_dyn (Spec.pk_chunk secret_key i) 12#usize
        = .ok (lift_poly te)) :
    lift_poly te = (lift_t_as_ntt_from_public_key secret_key K).val[i]! := by
  show lift_poly te = ((List.range K.val).map (fun m =>
      match hacspec_ml_kem.serialize.byte_decode_dyn (Spec.pk_chunk secret_key m) 12#usize with
      | .ok q => q
      | _ => default))[i]!
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some, hte]

set_option maxHeartbeats 4000000 in
/-- The rank-K loop: after `K` iterations the written prefix covers every index `< K`. -/
private theorem dv_loop_fc (K : Std.Usize) (secret_key : Slice Std.U8)
    (h_sk : secret_key.val.length = K.val * 384)
    (out : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (h_out : out.length = K.val) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ind_cpa.deserialize_vector_loop
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := 0#usize, «end» := K } secret_key out
    ⦃ ⇓ p => ⌜ (Aeneas.Std.Result.ok (dvInv secret_key K K.val p)).holds ⌝ ⦄ := by
  have h384 : ((384#usize : Std.Usize)).val = 384 := rfl
  have h1 : ((1#usize : Std.Usize)).val = 1 := by scalar_tac
  have h0 : ((0#usize : Std.Usize)).val = 0 := by scalar_tac
  have hKmax : K.val * 384 ≤ Std.Usize.max := by rw [← h_sk]; exact secret_key.property
  unfold libcrux_iot_ml_kem.ind_cpa.deserialize_vector_loop
  refine loop_range_spec_usize _ out 0#usize K
    (fun i acc => .ok (dvInv secret_key K i.val acc))
    (by scalar_tac)
    ((holds_ok _).mpr ⟨h_out,
      by intro j hj; rw [h0] at hj; omega,
      by intro j hj; rw [h0] at hj; omega⟩) ?_
  intro acc i hge hle hinv
  obtain ⟨hacc_len, hacc_lift, hacc_bnd⟩ := (holds_ok _).mp hinv
  by_cases hlt : i.val < K.val
  · -- a full 384-byte window remains
    have hK1 : 1 ≤ K.val := by omega
    obtain ⟨s', hs'_val, hnext⟩ := iter_some_gen i K hlt
    obtain ⟨i2, hi2_eq, hi2_val⟩ :=
      usize_mul_ok_e i (384#usize : Std.Usize)
        (by rw [h384]; exact le_trans (Nat.mul_le_mul_right 384 (by omega)) hKmax)
    obtain ⟨i3, hi3_eq, hi3_val⟩ :=
      usize_add_ok_e i (1#usize : Std.Usize)
        (by rw [h1]
            exact le_trans (by omega : i.val + 1 ≤ K.val * 384) hKmax)
    obtain ⟨i4, hi4_eq, hi4_val⟩ :=
      usize_mul_ok_e i3 (384#usize : Std.Usize)
        (by rw [h384, hi3_val, h1]
            exact le_trans (Nat.mul_le_mul_right 384 (by omega)) hKmax)
    have hi2_val' : i2.val = i.val * 384 := by rw [hi2_val, h384]
    have hi4_val' : i4.val = i.val * 384 + 384 := by
      rw [hi4_val, hi3_val, h1, h384]; ring
    have hchunk_len : (Spec.pk_chunk secret_key i.val).val.length = 384 :=
      pk_chunk_len_384 secret_key K h_sk i.val hlt
    have hwin : i.val * 384 + 384 ≤ K.val * 384 := by
      calc i.val * 384 + 384 = (i.val + 1) * 384 := by ring
        _ ≤ K.val * 384 := Nat.mul_le_mul_right 384 (by omega)
    have hidx := slice_range_index_ok secret_key i2 i4
      (by rw [hi2_val', hi4_val']; omega) (by rw [hi4_val', h_sk]; exact hwin)
    rw [window_eq_pk_chunk secret_key i2 i4 i.val hi2_val' hi4_val'] at hidx
    have hacc_idx : i.val < acc.val.length := by
      have : acc.val.length = K.val := hacc_len
      omega
    -- L5.7, the PROVED per-element leaf
    obtain ⟨te, hte_eq, hte_dyn, hte_bnd⟩ :=
      triple_exists_ok_fc
        (libcrux_iot_ml_kem.SerializeFc.deserialize_to_uncompressed_ring_element_fc
          (Spec.pk_chunk secret_key i.val) (acc.val[i.val]!)
          (by simpa [Aeneas.Std.Slice.length] using hchunk_len))
    refine triple_of_ok_fc
      (v := .cont (({ start := s', «end» := K } : CoreModels.core.ops.range.Range Std.Usize),
                   Aeneas.Std.Slice.set acc i te)) ?_ ?_
    · show libcrux_iot_ml_kem.ind_cpa.deserialize_vector_loop.body
        portable_ops_inst secret_key
        ({ start := i, «end» := K } : CoreModels.core.ops.range.Range Std.Usize) acc = _
      unfold libcrux_iot_ml_kem.ind_cpa.deserialize_vector_loop.body
      rw [hnext]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [impl_bpre]
      simp only [Aeneas.Std.bind_tc_ok]
      -- The ONE place this proof spells out the machine-generated body (skill §4.1):
      -- `rw [hnext]` leaves a pattern-`let` on the iterator pair that no `dsimp` will
      -- zeta-reduce, so the reduced do-block is stated once, here.
      show (do
          let i2 ← i * (384#usize : Std.Usize)
          let i3 ← i + (1#usize : Std.Usize)
          let i4 ← i3 * (384#usize : Std.Usize)
          let s ← CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
            (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
            secret_key { start := i2, «end» := i4 }
          let (pre, index_mut_back) ← Aeneas.Std.Slice.index_mut_usize acc i
          let pre1 ← libcrux_iot_ml_kem.serialize.deserialize_to_uncompressed_ring_element
            portable_ops_inst s pre
          Result.ok (ControlFlow.cont
            (({ start := s', «end» := K } : CoreModels.core.ops.range.Range Std.Usize),
             index_mut_back pre1))) = _
      rw [hi2_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [hi3_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [hi4_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [hidx]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [slice_index_mut_ok acc i hacc_idx]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [hte_eq]
      rfl
    · refine ⟨hlt, rfl, hs'_val, (holds_ok _).mpr ⟨?_, ?_, ?_⟩⟩
      · rw [slice_set_length]; exact hacc_len
      · intro j hj
        rw [hs'_val] at hj
        have hjlen : j < acc.val.length := by
          have : acc.val.length = K.val := hacc_len
          omega
        rw [slice_set_get acc i te j hjlen]
        by_cases hji : j = i.val
        · rw [if_pos hji, hji]
          exact pure_cell_eq K secret_key i.val hlt te hte_dyn
        · rw [if_neg hji]
          exact hacc_lift j (by omega)
      · intro j hj c hc ℓ hℓ
        rw [hs'_val] at hj
        have hjlen : j < acc.val.length := by
          have : acc.val.length = K.val := hacc_len
          omega
        rw [slice_set_get acc i te j hjlen]
        by_cases hji : j = i.val
        · rw [if_pos hji]; exact hte_bnd c hc ℓ hℓ
        · rw [if_neg hji]; exact hacc_bnd j (by omega) c hc ℓ hℓ
  · -- i = K: the loop is done
    refine triple_of_ok_fc (v := .done acc) ?_ ?_
    · show libcrux_iot_ml_kem.ind_cpa.deserialize_vector_loop.body
        portable_ops_inst secret_key
        ({ start := i, «end» := K } : CoreModels.core.ops.range.Range Std.Usize) acc = _
      unfold libcrux_iot_ml_kem.ind_cpa.deserialize_vector_loop.body
      rw [iter_none_gen i K (by omega)]
      rfl
    · refine (holds_ok _).mpr ⟨hacc_len, ?_, ?_⟩
      · intro j hj; exact hacc_lift j (by omega)
      · intro j hj; exact hacc_bnd j (by omega)

/-- The written prefix at `k = K` IS `lift_vec_slice` (`SerializeFc.lean:4241`). -/
private theorem lift_vec_slice_of_dvInv (K : Std.Usize) (secret_key : Slice Std.U8)
    (p : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (h_lift : ∀ i : Nat, i < K.val →
        lift_poly (p.val[i]!) = (lift_t_as_ntt_from_public_key secret_key K).val[i]!) :
    lift_vec_slice p K = lift_t_as_ntt_from_public_key secret_key K := by
  apply Subtype.ext
  show (List.range K.val).map (fun i => lift_poly p.val[i]!)
      = (lift_t_as_ntt_from_public_key secret_key K).val
  have hlen : (lift_t_as_ntt_from_public_key secret_key K).val.length = K.val :=
    (lift_t_as_ntt_from_public_key secret_key K).property
  refine List.ext_getElem (by simp [hlen]) ?_
  intro n hn1 hn2
  rw [List.getElem_map, List.getElem_range]
  have hn : n < K.val := by simpa using hn1
  rw [h_lift n hn, getElem!_pos _ _ (by rw [hlen]; exact hn)]

end DVBank

/-- **INC-2a.1** — `ind_cpa.deserialize_vector`: the SECRET-KEY decode.

    `for i in 0..K { deserialize_to_uncompressed_ring_element(sk[384i .. 384(i+1)], &mut out[i]) }`
    — the K-fold assembly of L5.7, exactly as `deserialize_ring_elements_reduced_fc` (L5.5)
    is the K-fold assembly of the A2 leaf. It is STRICTLY EASIER than L5.5: its per-element
    leaf `deserialize_to_uncompressed_ring_element_fc` is a PROVED, axiom-clean theorem in
    `SerializeFc.lean`, where L5.5's leaf is the A2 axiom.

    ## Every hypothesis and conjunct below was MEASURED before it was written
    (probe: `references/mlkem-falsify-harness.lean` vocabulary, run against this tree)

    ## The post is the UPSTREAM `ensures`, transcribed — not a per-chunk restatement
    `libcrux-ml-kem/src/ind_cpa.rs` states this function's contract as ONE whole-vector
    equation, `vector_to_spec K secret_as_ntt == Hacspec_ml_kem.Serialize.vector_decode_12_ K
    secret_key`, so that is what is written here. A first draft stated it per chunk against
    `byte_decode_dyn (Spec.pk_chunk …) 12` — TRUE (measured, identically) but an invention,
    and rule 2 of the contract-transcription discipline exists to stop exactly that.
    Note `hacspec.deserialize_ring_elements_reduced` is DEFINED as `vector_decode_12`
    (`specs/ml-kem/src/serialize.rs:410`), so this post and L5.5's are the same shape
    against the same spec function — which is the precise sense in which this obligation is
    "L5.5 with a proved leaf instead of an axiom".

    * **No `is_rank` hypothesis, and none is needed** — verified at K = 0 and K = 5 as well
      as the three valid ranks.
    * **`h_out_len` and `h_sk_len` are the impl's own indexing preconditions**, transcribed,
      not invented.
    * **The bound is `≤ 4095`, and that is ATTAINED, not loose** — max lane over an
      all-`0xFF` secret key is exactly 4095. `≤ 3328` would be FALSE here. This is the
      SAME post L5.7 exports per element, lifted pointwise.
    * **The caller's `out` buffer is fully overwritten** — the post holds with the buffer
      poisoned four ways (random garbage; all-4095; all-32767; all-(-32768)), which is the
      hole the L5.5 audit found when it had only ever been tested zero-filled.
    * **Negative control fires**: asserting `≤ 4094` instead produces a counterexample, so
      an empty counterexample list means something.

    ## ⚠ COMPOSITION NOTE for whoever proves `decrypt` — read before using this
    `lift_poly` lands in `ZMod 3329`, so the impl's UNREDUCED decode and the spec's
    `deserialize_ring_elements_reduced` (which spec `decrypt` applies to `dk`) agree AS
    FIELD ELEMENTS — measured, they do. The difference is the REPRESENTATIVE: this obligation
    gives `≤ 4095`, while `compute_message_fc` requires `≤ 3328`
    (`Matrix/ComputeMessage/FC.lean`). So `decrypt` cannot chain this post into
    `compute_message` without either a reduction step or a strengthened bound. That gap is
    real and belongs to `decrypt`, NOT to this statement: strengthening the post here to
    `≤ 3328` would make it FALSE (4095 is attained). Recorded so the wall is met on paper
    rather than three rungs into a dispatch. -/
@[spec]
theorem deserialize_vector_fc
    (K : Std.Usize)
    (secret_key : Slice Std.U8)
    (secret_as_ntt : Slice
        (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (h_sk_len : secret_key.length = K.val * 384)
    (h_out_len : secret_as_ntt.length = K.val) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ind_cpa.deserialize_vector
      (vectortraitsOperationsInst := portable_ops_inst)
      K secret_key secret_as_ntt
    ⦃ ⇓ p => ⌜ p.length = K.val
                ∧ hacspec_ml_kem.serialize.vector_decode_12 K secret_key
                    = .ok (lift_vec_slice p K)
                ∧ (∀ i : Nat, i < K.val → ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
                    (((p.val[i]!).coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs
                      ≤ 4095) ⌝ ⦄ := by
  have h_sk : secret_key.val.length = K.val * 384 := h_sk_len
  obtain ⟨p, hp_eq, hp_holds⟩ :=
    triple_exists_ok_fc (dv_loop_fc K secret_key h_sk secret_as_ntt h_out_len)
  obtain ⟨hp_len, hp_lift, hp_bnd⟩ := (holds_ok _).mp hp_holds
  refine triple_of_ok_fc (v := p) ?_ ?_
  · unfold libcrux_iot_ml_kem.ind_cpa.deserialize_vector
    exact hp_eq
  · refine ⟨hp_len, ?_, hp_bnd⟩
    rw [lift_vec_slice_of_dvInv K secret_key p hp_lift]
    exact spec_vector_decode_12_eq K secret_key h_sk

/-! ## PROVER bank for INC-2a.2 — the ENCODE dual.

    Two halves again, mirroring the decode bank above:

    * **SPEC side** (`spec_serialize_secret_key_eq`): `serialize_secret_key T_SIZE` is a
      `createi T_SIZE` whose closure, at BYTE index `ℓ`, reads `vector[ℓ / 384]` and returns
      byte `ℓ % 384` of its `byte_encode … 12`. So the whole `createi` collapses to the pure
      byte model `encBy (key[ℓ / 384]) (ℓ % 384)`. No bit-level reasoning enters: the only
      fact needed about the encode atom is `SerializeFc.byte_encode_12_eq` (M-B(1)), which
      is PROVED.
    * **IMPL side** (`sv_loop_fc`): `for (i, re) in key.into_iter().enumerate()` with a
      mutable SUBSLICE write to `out[384i .. 384(i+1)]`. The iterator is
      `Enumerate (Iter Poly)`, NOT `Enumerate (ChunksExact U8)`, so neither
      `loop_chunks_exact_enumerate_spec` nor `loop_chunks_exact_pk_spec` applies; their
      SHAPE (suffix-aware induction on `n - count`) is copied into
      `loop_iter_enumerate_spec` below at the `Iter` instance. The per-element leaf is
      L5.6 `SerializeFc.serialize_uncompressed_ring_element_fc`. -/

section SVBank

open libcrux_iot_ml_kem.Util.CreateI

/-- The impl's polynomial type; it appears in every signature below. -/
private abbrev SPoly :=
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- The impl's 16-lane vector type (the `scratch` argument). -/
private abbrev SVec := libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-! ### `Usize` remainder bridge — the companion of `Util.Shared.usize_div_lit`,
    which the `serialize_secret_key` closure needs alongside it (`ℓ / 384`, `ℓ % 384`). -/

private theorem usize_rem_lit (x y z : Std.Usize) (hy : y.val ≠ 0)
    (hz : x.val % y.val = z.val) : (x % y : Result Std.Usize) = .ok z := by
  obtain ⟨r, hr_eq, hr_val, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.rem_bv_spec x hy)
  rw [hr_eq]
  congr 1
  exact Std.UScalar.eq_of_val_eq (by rw [hr_val, hz])

/-! ### The `Enumerate (Iter T)` iterator.

    `CoreModels.core.slice.iter.Iter T` is `rust_primitives.sequence.Seq T` is `Slice T`
    (two `def` unfoldings, both transparent), and its `next` pops the head through
    `seq_remove … 0`. These three lemmas are the `Iter`-instance analogues of
    `ComputeRingElementV.Impl.enumerate_chunks_next_{cont,done}`. -/

private abbrev EnumIter (T : Type) :=
  CoreModels.core.iter.adapters.enumerate.Enumerate (CoreModels.core.slice.iter.Iter T)

/-- `seq_remove … 0` on a non-empty sequence: the head, and the tail. -/
private theorem seq_remove_zero {T : Type} [Inhabited T] (rest : Slice T)
    (h_ne : 0 < rest.val.length) :
    CoreModels.rust_primitives.sequence.seq_remove rest (0#usize : Std.Usize)
      = .ok (rest.val[0]!, (⟨rest.val.drop 1, by
          have := rest.property
          simp only [List.length_drop]
          omega⟩ : Slice T)) := by
  have hlt : ((0#usize : Std.Usize)).val < rest.val.length := h_ne
  unfold CoreModels.rust_primitives.sequence.seq_remove
  rw [dif_pos hlt]
  have h1 : rest.val.get ⟨((0#usize : Std.Usize)).val, hlt⟩ = rest.val[0]! := by
    rw [List.get_eq_getElem, getElem!_pos rest.val 0 h_ne]
    rfl
  have h2 : rest.val.take ((0#usize : Std.Usize)).val
      ++ rest.val.drop (((0#usize : Std.Usize)).val + 1) = rest.val.drop 1 := by
    show rest.val.take 0 ++ rest.val.drop 1 = rest.val.drop 1
    simp
  simp only [h1]
  exact congrArg (fun s => Result.ok (rest.val[0]!, s)) (Subtype.ext h2)

/-- `Enumerate (Iter T)`'s `next` when at least one element remains. -/
private theorem enum_iter_next_cont {T : Type} [Inhabited T]
    (rest : Slice T) (cnt : Std.Usize)
    (h_ne : 0 < rest.val.length) (h_cnt : cnt.val + 1 ≤ Std.Usize.max) :
    ∃ (rest' : Slice T) (cnt' : Std.Usize),
      CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
          (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
          ({ iter := rest, count := cnt } : EnumIter T)
        = .ok (CoreModels.core.option.Option.Some (cnt, rest.val[0]!),
               ({ iter := rest', count := cnt' } : EnumIter T))
      ∧ cnt'.val = cnt.val + 1
      ∧ rest'.val.length = rest.val.length - 1
      ∧ (∀ ℓ : Nat, rest'.val[ℓ]! = rest.val[ℓ + 1]!) := by
  have h1 : ((1#usize : Std.Usize)).val = 1 := by scalar_tac
  obtain ⟨cnt', hcnt'_eq, hcnt'_val⟩ :=
    usize_add_ok_e cnt (1#usize : Std.Usize) (by rw [h1]; exact h_cnt)
  have hcnt'_val' : cnt'.val = cnt.val + 1 := by rw [hcnt'_val, h1]
  have hne : ¬ (Aeneas.Std.Slice.len rest = (0#usize : Std.Usize)) := by
    intro hc
    have hv : (Aeneas.Std.Slice.len rest).val = ((0#usize : Std.Usize)).val := by rw [hc]
    rw [Aeneas.Std.Slice.len_val] at hv
    have hv' : rest.val.length = ((0#usize : Std.Usize)).val := hv
    have h0 : ((0#usize : Std.Usize)).val = 0 := by scalar_tac
    omega
  refine ⟨⟨rest.val.drop 1, by
      have := rest.property
      simp only [List.length_drop]
      omega⟩, cnt', ?_, hcnt'_val', ?_, ?_⟩
  · show CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
        (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
        ({ iter := rest, count := cnt } : EnumIter T) = _
    unfold
      CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
    show (do
        let (o, t) ←
          CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
            (T := T) rest
        match o with
        | CoreModels.core.option.Option.Some a =>
          let i ← cnt + (1#usize : Std.Usize)
          Result.ok (CoreModels.core.option.Option.Some (cnt, a),
            ({ iter := t, count := i } : EnumIter T))
        | CoreModels.core.option.Option.None =>
          Result.ok (CoreModels.core.option.Option.None,
            ({ iter := t, count := cnt } : EnumIter T))) = _
    unfold CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
    unfold CoreModels.rust_primitives.sequence.seq_len
    simp only [Aeneas.Std.bind_tc_ok]
    rw [if_neg hne]
    rw [seq_remove_zero rest h_ne]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hcnt'_eq]
    rfl
  · show (rest.val.drop 1).length = rest.val.length - 1
    simp
  · intro ℓ
    show (rest.val.drop 1)[ℓ]! = rest.val[ℓ + 1]!
    by_cases hℓ : ℓ < (rest.val.drop 1).length
    · rw [getElem!_pos (rest.val.drop 1) ℓ hℓ]
      have hℓ' : ℓ + 1 < rest.val.length := by
        rw [List.length_drop] at hℓ; omega
      rw [getElem!_pos rest.val (ℓ + 1) hℓ', List.getElem_drop]
      congr 1
      omega
    · have hℓr : ¬ (ℓ + 1 < rest.val.length) := by
        rw [List.length_drop] at hℓ; omega
      rw [getElem!_neg (rest.val.drop 1) ℓ hℓ, getElem!_neg rest.val (ℓ + 1) hℓr]

/-- `Enumerate (Iter T)`'s `next` when the sequence is exhausted. -/
private theorem enum_iter_next_done {T : Type} [Inhabited T]
    (rest : Slice T) (cnt : Std.Usize) (h : rest.val.length = 0) :
    CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
        (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
        ({ iter := rest, count := cnt } : EnumIter T)
      = .ok (CoreModels.core.option.Option.None,
             ({ iter := rest, count := cnt } : EnumIter T)) := by
  have heq : Aeneas.Std.Slice.len rest = (0#usize : Std.Usize) := by
    refine Aeneas.Std.UScalar.eq_of_val_eq ?_
    rw [Aeneas.Std.Slice.len_val]
    show rest.val.length = ((0#usize : Std.Usize)).val
    rw [h]; scalar_tac
  show CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
      (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
      ({ iter := rest, count := cnt } : EnumIter T) = _
  unfold
    CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
  show (do
      let (o, t) ←
        CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
          (T := T) rest
      match o with
      | CoreModels.core.option.Option.Some a =>
        let i ← cnt + (1#usize : Std.Usize)
        Result.ok (CoreModels.core.option.Option.Some (cnt, a),
          ({ iter := t, count := i } : EnumIter T))
      | CoreModels.core.option.Option.None =>
        Result.ok (CoreModels.core.option.Option.None,
          ({ iter := t, count := cnt } : EnumIter T))) = _
  unfold CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
  unfold CoreModels.rust_primitives.sequence.seq_len
  simp only [Aeneas.Std.bind_tc_ok]
  rw [if_pos heq]
  rfl

/-! ### The loop Hoare spec at the `Iter` instance.

    Structurally `loop_chunks_exact_pk_spec` (K1, disposition COPIED): same induction on
    `n - count`, with the byte-suffix relation replaced by the ELEMENT-suffix relation
    `rest[ℓ] = full[k + ℓ]` — which this loop needs for the same reason, namely that the
    per-element leaf must be applied to `key[k]` and not to an unidentified `rest`. The three
    triple helpers are the `_chunks` helpers renamed. -/

section loop_iter_helpers

private abbrev ResultPSI := PostShape.except Error (PostShape.except PUnit PostShape.pure)

private theorem triple_noThrow_elim_iter {α : Type} {x : Result α}
    {Q : α → Assertion ResultPSI}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) {v : α} (hv : x = .ok v) :
    (Q v).down := by
  subst hv
  simpa [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PostCond.noThrow,
    Std.Do.PredTrans.apply] using h

private theorem triple_noThrow_exists_ok_iter {α : Type} {x : Result α}
    {Q : α → Assertion ResultPSI}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) : ∃ v, x = .ok v := by
  match x, h with
  | .ok v, _ => exact ⟨v, rfl⟩
  | .fail _, h => exact absurd h (by
      simp [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PostCond.noThrow, Std.Do.PredTrans.apply])
  | .div, h => exact absurd h (by
      simp [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PostCond.noThrow, Std.Do.PredTrans.apply])

end loop_iter_helpers

set_option maxHeartbeats 2000000 in
private theorem loop_iter_enumerate_spec {T β : Type} [Inhabited T]
    (body : (EnumIter T × β) → Result (ControlFlow (EnumIter T × β) β))
    (init : β) (full : Slice T) (n : Nat)
    (inv : Nat → β → Result Prop)
    (h_len : full.val.length = n)
    (h_init : (inv 0 init).holds)
    (h_step : ∀ (acc : β) (k : Nat) (rest : Slice T) (cnt : Std.Usize),
        k ≤ n → cnt.val = k → rest.val.length = n - k →
        (∀ ℓ : Nat, rest.val[ℓ]! = full.val[k + ℓ]!) →
        (inv k acc).holds →
        ⦃ ⌜ True ⌝ ⦄
        body (({ iter := rest, count := cnt } : EnumIter T), acc)
        ⦃ ⇓ r => match r with
          | .cont (it', acc') =>
              ⌜ k < n ∧ ∃ (rest' : Slice T) (cnt' : Std.Usize),
                  it' = ({ iter := rest', count := cnt' } : EnumIter T)
                  ∧ cnt'.val = k + 1
                  ∧ rest'.val.length = n - (k + 1)
                  ∧ (∀ ℓ : Nat, rest'.val[ℓ]! = full.val[(k + 1) + ℓ]!)
                  ∧ (inv (k + 1) acc').holds ⌝
          | .done y => ⌜ (inv n y).holds ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    loop body (({ iter := full, count := 0#usize } : EnumIter T), init)
    ⦃ ⇓ r => ⌜ (inv n r).holds ⌝ ⦄ := by
  suffices gen : ∀ (m : Nat) (acc : β) (rest : Slice T) (cnt : Std.Usize),
      n - cnt.val = m → cnt.val ≤ n →
      rest.val.length = n - cnt.val →
      (∀ ℓ : Nat, rest.val[ℓ]! = full.val[cnt.val + ℓ]!) →
      (inv cnt.val acc).holds →
      ⦃ ⌜ True ⌝ ⦄
      loop body (({ iter := rest, count := cnt } : EnumIter T), acc)
      ⦃ ⇓ r => ⌜ (inv n r).holds ⌝ ⦄ by
    have h0 : ((0#usize : Std.Usize)).val = 0 := rfl
    refine gen _ init full 0#usize rfl (by rw [h0]; exact Nat.zero_le _) ?_ ?_ ?_
    · rw [h0]; simpa using h_len
    · rw [h0]; intro ℓ; simp
    · rw [h0]; exact h_init
  intro m
  induction m with
  | zero =>
    intro acc rest cnt hm hcnt_le hlen hsuf hinv
    have hcnt_eq : cnt.val = n := by omega
    have hs := h_step acc cnt.val rest cnt hcnt_le rfl hlen hsuf hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok_iter hs
    have hpost := triple_noThrow_elim_iter hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .cont (it', acc') =>
      simp only at hpost
      exact absurd hpost.1 (by rw [hcnt_eq]; exact Nat.lt_irrefl _)
    | .done y =>
      simp only at hpost
      exact triple_of_ok_fc rfl hpost
  | succ m ih =>
    intro acc rest cnt hm hcnt_le hlen hsuf hinv
    have hs := h_step acc cnt.val rest cnt hcnt_le rfl hlen hsuf hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok_iter hs
    have hpost := triple_noThrow_elim_iter hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .done y =>
      simp only at hpost
      exact triple_of_ok_fc rfl hpost
    | .cont (it', acc') =>
      simp only at hpost
      obtain ⟨hlt, rest', cnt', hit', hcnt', hlen', hsuf', hinv'⟩ := hpost
      rw [hit']
      refine ih acc' rest' cnt' ?_ ?_ ?_ ?_ ?_
      · rw [hcnt']; omega
      · rw [hcnt']; omega
      · rw [hcnt']; exact hlen'
      · rw [hcnt']; exact hsuf'
      · rw [hcnt']; exact hinv'

/-! ### The pure byte model, and the two sides that agree on it.

    `encBy re j` is byte `j` of the `d = 12` packing of `re`, read off the SPEC function so
    that no private name from `SerializeFc.lean` has to be spelled here (`encByte` is
    `private` there). Both sides are then characterised against it:
    * the SPEC side by `SerializeFc.byte_encode_12_eq` (M-B(1)), by definition;
    * the IMPL side by `SerializeFc.byte_encode_into_12_eq` (M-B(2)) — the form L5.6's post
      is stated against — plus M-B(1) to identify the two. -/

private def encBy (re : SPoly) (j : Nat) : Std.U8 :=
  match hacspec_ml_kem.serialize.byte_encode 384#usize 3072#usize (lift_poly re) 12#usize with
  | .ok a => a.val[j]!
  | _ => 0#u8

/-- The `byte_encode_into` slice wrapper produces exactly `encBy re`. This is the ONE place
    the two K4/K11 encode exemplars are composed; everything downstream cites this. -/
private theorem encode_into_encBy (re : SPoly) (serialized : Slice Std.U8)
    (h_len : serialized.length = 384) :
    ∃ s : Slice Std.U8,
      hacspec_ml_kem.serialize.byte_encode_into (lift_poly re) 12#usize serialized = .ok s
      ∧ s.val.length = 384
      ∧ ∀ n : Nat, n < 384 → s.val[n]! = encBy re n := by
  obtain ⟨a, ha_eq, ha_get⟩ := libcrux_iot_ml_kem.SerializeFc.byte_encode_12_eq re
  obtain ⟨s, hs_eq, hs_len, hs_get⟩ :=
    libcrux_iot_ml_kem.SerializeFc.byte_encode_into_12_eq re serialized h_len
  refine ⟨s, hs_eq, hs_len, ?_⟩
  intro n hn
  refine Aeneas.Std.UScalar.eq_of_val_eq ?_
  rw [hs_get n hn]
  show _ = (encBy re n).val
  unfold encBy
  simp only [ha_eq]
  exact (ha_get n hn).symm

/-! ### SPEC side — `serialize_secret_key` IS the pure byte model.

    `createi T_SIZE` over a closure that, at byte `ℓ`, does `vector[ℓ / 384]` then
    `byte_encode … 12` then `[ℓ % 384]`. The `Fn`-vs-`FnMut` wrapper is the direct one, so
    the composer is `Util.CreateI.from_fn_pure_eq` (as on the decode side). -/

/-- The `serialize_secret_key` closure at byte index `ℓ`. -/
private theorem ssk_closure_eq (K T_SIZE : Std.Usize) (key : Std.Array SPoly K)
    (h_tsize : T_SIZE.val = K.val * 384) (ℓ : Nat) (hℓ : ℓ < T_SIZE.val) :
    (hacspec_ml_kem.serialize.serialize_secret_key.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
        K T_SIZE).call_mut (lift_vec key) (⟨BitVec.ofNat _ ℓ⟩ : Std.Usize)
      = .ok (encBy (key.val[ℓ / 384]!) (ℓ % 384), lift_vec key) := by
  have hTmax : T_SIZE.val ≤ Std.Usize.max := by scalar_tac
  have h384 : ((384#usize : Std.Usize)).val = 384 := rfl
  have hℓv : ((⟨BitVec.ofNat _ ℓ⟩ : Std.Usize)).val = ℓ :=
    usize_ofNat_val_le ℓ (by omega)
  have hdv : ((⟨BitVec.ofNat _ (ℓ / 384)⟩ : Std.Usize)).val = ℓ / 384 :=
    usize_ofNat_val_le _ (by omega)
  have hmv : ((⟨BitVec.ofNat _ (ℓ % 384)⟩ : Std.Usize)).val = ℓ % 384 :=
    usize_ofNat_val_le _ (by omega)
  have hdiv : ((⟨BitVec.ofNat _ ℓ⟩ : Std.Usize) / (384#usize : Std.Usize) : Result Std.Usize)
      = .ok (⟨BitVec.ofNat _ (ℓ / 384)⟩ : Std.Usize) :=
    usize_div_lit _ _ _ (by rw [h384]; omega) (by rw [hℓv, h384, hdv])
  have hrem : ((⟨BitVec.ofNat _ ℓ⟩ : Std.Usize) % (384#usize : Std.Usize) : Result Std.Usize)
      = .ok (⟨BitVec.ofNat _ (ℓ % 384)⟩ : Std.Usize) :=
    usize_rem_lit _ _ _ (by rw [h384]; omega) (by rw [hℓv, h384, hmv])
  -- `ℓ / 384 < K`, so the vector read succeeds and IS `lift_poly (key[ℓ / 384])`
  have hK : ℓ / 384 < K.val := by
    rw [h_tsize] at hℓ
    exact Nat.div_lt_of_lt_mul (by omega)
  have hkeylen : key.val.length = K.val := key.property
  have hlvlen : (lift_vec key).val.length = K.val := (lift_vec key).property
  have hcell : (lift_vec key).val[ℓ / 384]! = lift_poly (key.val[ℓ / 384]!) := by
    show (key.val.map lift_poly)[ℓ / 384]! = lift_poly (key.val[ℓ / 384]!)
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by rw [hkeylen]; exact hK)]
    simp only [Option.map_some, Option.getD_some]
    rw [getElem!_pos key.val (ℓ / 384) (by rw [hkeylen]; exact hK)]
  have hidx : Aeneas.Std.Array.index_usize (lift_vec key)
        (⟨BitVec.ofNat _ (ℓ / 384)⟩ : Std.Usize)
      = .ok (lift_poly (key.val[ℓ / 384]!)) := by
    rw [libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq
      (lift_vec key) (⟨BitVec.ofNat _ (ℓ / 384)⟩ : Std.Usize)
      (by rw [show (lift_vec key).length = K.val from hlvlen, hdv]; exact hK)]
    rw [hdv, hcell]
  -- the encode atom: M-B(1)
  obtain ⟨a, ha_eq, ha_get⟩ :=
    libcrux_iot_ml_kem.SerializeFc.byte_encode_12_eq (key.val[ℓ / 384]!)
  have halen : a.val.length = 384 := a.property
  have haidx : Aeneas.Std.Array.index_usize a (⟨BitVec.ofNat _ (ℓ % 384)⟩ : Std.Usize)
      = .ok (a.val[ℓ % 384]!) := by
    rw [libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq
      a (⟨BitVec.ofNat _ (ℓ % 384)⟩ : Std.Usize)
      (by rw [show a.length = 384 from halen, hmv]; omega)]
    rw [hmv]
  have hencBy : encBy (key.val[ℓ / 384]!) (ℓ % 384) = a.val[ℓ % 384]! := by
    unfold encBy
    simp only [ha_eq]
  show (hacspec_ml_kem.serialize.serialize_secret_key.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
      (RANK := K) (T_SIZE := T_SIZE) (lift_vec key) (⟨BitVec.ofNat _ ℓ⟩ : Std.Usize)) = _
  unfold
    hacspec_ml_kem.serialize.serialize_secret_key.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
  rw [hacspec_bpre]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hdiv]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hrem]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hidx]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [ha_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [haidx]
  simp only [Aeneas.Std.bind_tc_ok, hencBy]

/-- **The spec bridge.** The hacspec rank-K 12-bit encode of `key` is the pure byte model
    `encBy (key[ℓ / 384]) (ℓ % 384)` at every byte `ℓ`. -/
private theorem spec_serialize_secret_key_eq (K T_SIZE : Std.Usize) (key : Std.Array SPoly K)
    (h_tsize : T_SIZE.val = K.val * 384) :
    ∃ enc : Std.Array Std.U8 T_SIZE,
      hacspec_ml_kem.serialize.serialize_secret_key (RANK := K) T_SIZE (lift_vec key) = .ok enc
      ∧ ∀ ℓ : Nat, ℓ < T_SIZE.val → enc.val[ℓ]! = encBy (key.val[ℓ / 384]!) (ℓ % 384) := by
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq (T := Std.U8) T_SIZE
      (hacspec_ml_kem.serialize.serialize_secret_key.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
        K T_SIZE)
      (lift_vec key)
      (fun ℓ => encBy (key.val[ℓ / 384]!) (ℓ % 384))
      (fun ℓ hℓ => ssk_closure_eq K T_SIZE key h_tsize ℓ hℓ)
  refine ⟨⟨(List.range T_SIZE.val).map (fun m => encBy (key.val[m / 384]!) (m % 384)),
      by simp⟩, ?_, ?_⟩
  · unfold hacspec_ml_kem.serialize.serialize_secret_key
    simp only [hacspec_ml_kem.parameters.createi, hfn]
  · intro ℓ hℓ
    show ((List.range T_SIZE.val).map
        (fun m => encBy (key.val[m / 384]!) (m % 384)))[ℓ]! = _
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hℓ]
    simp only [Option.map_some, Option.getD_some]

/-! ### IMPL side — the enumerate loop with a mutable SUBSLICE write.

    `slice_index_mut_range_strict` is the K2 exemplar's write-back helper
    (`SerializeFc.lean:1407`, `private` there hence unreachable, so RESTATED here verbatim —
    it is the same statement and the same proof). `List.setSlice!` then gives the
    written-prefix / untouched-prefix algebra the invariant needs. -/


/-- The window arithmetic, in a CLEAN context. Inline `omega` on these goals inside
    `sv_loop_fc` blows `maxRecDepth`: the loop context carries `K * 384 ≤ Usize.max`, and
    any goal mentioning `K * 384` drags `Std.Usize.max` into omega's atom set (the
    closed-large-scalar pitfall, skill §6). Hoisting is the fix; a `maxRecDepth` bump
    would not be. -/
private theorem window_div_mod (k ℓ : Nat) (h1 : k * 384 ≤ ℓ) (h2 : ℓ < (k + 1) * 384) :
    ℓ / 384 = k ∧ ℓ % 384 = ℓ - k * 384 := ⟨by omega, by omega⟩

/-- Written-prefix invariant for the rank-K encode loop: after `k` iterations the first
    `384k` bytes of the output carry the pure byte model, and the length is preserved. The
    undone-cells conjunct is not needed because the post only speaks about `ℓ < 384K` and
    every one of those cells IS written. -/
private def svInv (K : Std.Usize) (key : Std.Array SPoly K) (k : Nat)
    (acc : Slice Std.U8 × SVec) : Prop :=
  acc.1.val.length = K.val * 384
  ∧ (∀ ℓ : Nat, ℓ < k * 384 → acc.1.val[ℓ]! = encBy (key.val[ℓ / 384]!) (ℓ % 384))

set_option maxHeartbeats 4000000 in
/-- The rank-K encode loop: after `K` iterations every byte `< 384K` is written. -/
private theorem sv_loop_fc (K : Std.Usize) (key : Std.Array SPoly K)
    (h_bnd : ∀ i : Nat, i < K.val → ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
        (((key.val[i]!).coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 3328)
    (out : Slice Std.U8) (scratch : SVec)
    (h_out : out.val.length = K.val * 384) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ind_cpa.serialize_vector_loop
      (vectortraitsOperationsInst := portable_ops_inst)
      ({ iter := Aeneas.Std.Array.to_slice key, count := 0#usize } : EnumIter SPoly)
      out scratch
    ⦃ ⇓ p => ⌜ (Aeneas.Std.Result.ok (svInv K key K.val p)).holds ⌝ ⦄ := by
  have h384 : ((384#usize : Std.Usize)).val = 384 := rfl
  have h1 : ((1#usize : Std.Usize)).val = 1 := by scalar_tac
  have hKmax : K.val * 384 ≤ Std.Usize.max := by rw [← h_out]; exact out.property
  have hkeylen : key.val.length = K.val := key.property
  have hKle : K.val ≤ K.val * 384 := Nat.le_mul_of_pos_right _ (by omega)
  unfold libcrux_iot_ml_kem.ind_cpa.serialize_vector_loop
  refine loop_iter_enumerate_spec _ (out, scratch) (Aeneas.Std.Array.to_slice key) K.val
    (fun k acc => .ok (svInv K key k acc))
    hkeylen
    ((holds_ok _).mpr ⟨h_out, by intro ℓ hℓ; omega⟩) ?_
  intro acc k rest cnt hk_le hcnt hlen hsuf hinv
  obtain ⟨hacc_len, hacc_get⟩ := (holds_ok _).mp hinv
  by_cases hlt : k < K.val
  · -- one polynomial remains
    have h_ne : 0 < rest.val.length := by rw [hlen]; omega
    have hcnt_bd : cnt.val + 1 ≤ Std.Usize.max := by rw [hcnt]; omega
    obtain ⟨rest', cnt', hnext, hcnt'_val, hrest'_len, hrest'_get⟩ :=
      enum_iter_next_cont rest cnt h_ne hcnt_bd
    have hre : rest.val[0]! = key.val[k]! := by
      have h := hsuf 0
      rw [h]; rfl
    obtain ⟨i2, hi2_eq, hi2_val⟩ := usize_mul_ok_e cnt (384#usize : Std.Usize)
      (by rw [h384, hcnt]; exact le_trans (Nat.mul_le_mul_right 384 (by omega)) hKmax)
    obtain ⟨i3, hi3_eq, hi3_val⟩ := usize_add_ok_e cnt (1#usize : Std.Usize)
      (by rw [h1]; exact hcnt_bd)
    obtain ⟨i4, hi4_eq, hi4_val⟩ := usize_mul_ok_e i3 (384#usize : Std.Usize)
      (by rw [h384, hi3_val, h1, hcnt]
          exact le_trans (Nat.mul_le_mul_right 384 (by omega)) hKmax)
    have hi2v : i2.val = k * 384 := by rw [hi2_val, h384, hcnt]
    have hi4v : i4.val = k * 384 + 384 := by
      rw [hi4_val, hi3_val, h1, h384, hcnt]; ring
    have hwin' : (k + 1) * 384 ≤ K.val * 384 := Nat.mul_le_mul_right 384 (by omega)
    have hwin : k * 384 + 384 ≤ K.val * 384 := by
      calc k * 384 + 384 = (k + 1) * 384 := by ring
        _ ≤ K.val * 384 := hwin'
    obtain ⟨sub, wb, hmut_eq, hsub_len, hwb⟩ :=
      slice_index_mut_range_strict acc.1 i2 i4 (by omega) (by rw [hacc_len]; omega)
    have hsub384 : sub.val.length = 384 := by rw [hsub_len, hi2v, hi4v]; omega
    -- L5.6, the PROVED per-element leaf
    obtain ⟨p, hp_eq, hp_enc⟩ :=
      triple_exists_ok_fc
        (libcrux_iot_ml_kem.SerializeFc.serialize_uncompressed_ring_element_fc
          (key.val[k]!) acc.2 sub (by simpa [Aeneas.Std.Slice.length] using hsub384)
          (fun c hc l hl => h_bnd k hlt c hc l hl))
    obtain ⟨senc, hsenc_eq, hsenc_len, hsenc_get⟩ :=
      encode_into_encBy (key.val[k]!) sub (by simpa [Aeneas.Std.Slice.length] using hsub384)
    rw [hsenc_eq] at hp_enc
    have hsp : senc = p.2 := Result.ok.inj hp_enc
    have hp2_len : p.2.val.length = 384 := by rw [← hsp]; exact hsenc_len
    have hp2_get : ∀ n : Nat, n < 384 → p.2.val[n]! = encBy (key.val[k]!) n := by
      intro n hn; rw [← hsp]; exact hsenc_get n hn
    have hwbv := hwb p.2 (by rw [hp2_len, hi2v, hi4v]; omega)
    refine triple_of_ok_fc
      (v := .cont (({ iter := rest', count := cnt' } : EnumIter SPoly), (wb p.2, p.1))) ?_ ?_
    · show libcrux_iot_ml_kem.ind_cpa.serialize_vector_loop.body
        portable_ops_inst ({ iter := rest, count := cnt } : EnumIter SPoly) acc.1 acc.2 = _
      unfold libcrux_iot_ml_kem.ind_cpa.serialize_vector_loop.body
      rw [hnext]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [impl_bpre]
      simp only [Aeneas.Std.bind_tc_ok]
      -- the machine-generated body, once, in reduced form (skill §4.1)
      show (do
          let i2' ← cnt * (384#usize : Std.Usize)
          let i3' ← cnt + (1#usize : Std.Usize)
          let i4' ← i3' * (384#usize : Std.Usize)
          let (s, index_mut_back) ←
            CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
              (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                Std.U8) acc.1 { start := i2', «end» := i4' }
          let (scratch1, s1) ←
            libcrux_iot_ml_kem.serialize.serialize_uncompressed_ring_element
              portable_ops_inst (rest.val[0]!) acc.2 s
          Result.ok (ControlFlow.cont
            (({ iter := rest', count := cnt' } : EnumIter SPoly),
             (index_mut_back s1, scratch1)))) = _
      rw [hi2_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [hi3_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [hi4_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [hmut_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [hre, hp_eq]
      rfl
    · refine ⟨hlt, rest', cnt', rfl, by rw [hcnt'_val, hcnt], by rw [hrest'_len, hlen]; omega,
        ?_, ?_⟩
      · intro ℓ
        rw [hrest'_get ℓ, hsuf (ℓ + 1)]
        congr 1
        omega
      · refine (holds_ok _).mpr ⟨?_, ?_⟩
        · show (wb p.2).val.length = K.val * 384
          rw [hwbv, List.length_setSlice!]
          exact hacc_len
        · intro ℓ hℓ
          show (wb p.2).val[ℓ]! = _
          rw [hwbv]
          by_cases hlk : ℓ < k * 384
          · rw [List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]
            exact hacc_get ℓ hlk
          · rw [List.getElem!_setSlice!_middle _ _ _ _
              ⟨by omega, by rw [hp2_len]; omega,
               by rw [hacc_len]; exact Nat.lt_of_lt_of_le hℓ hwin'⟩]
            rw [hi2v, hp2_get (ℓ - k * 384) (by omega)]
            obtain ⟨hdk, hmk⟩ := window_div_mod k ℓ (Nat.le_of_not_lt hlk) hℓ
            rw [hdk, hmk]
  · -- k = K: the loop is done
    have hkK : k = K.val := by omega
    have h_e : rest.val.length = 0 := by rw [hlen]; omega
    refine triple_of_ok_fc (v := .done acc) ?_ ?_
    · show libcrux_iot_ml_kem.ind_cpa.serialize_vector_loop.body
        portable_ops_inst ({ iter := rest, count := cnt } : EnumIter SPoly) acc.1 acc.2 = _
      unfold libcrux_iot_ml_kem.ind_cpa.serialize_vector_loop.body
      rw [enum_iter_next_done rest cnt h_e]
      rfl
    · refine (holds_ok _).mpr ⟨hacc_len, ?_⟩
      intro ℓ hℓ
      exact hacc_get ℓ (by rw [hkK]; exact hℓ)

end SVBank

/-- **INC-2a.2** — `ind_cpa.serialize_vector`: the ENCODE dual of `deserialize_vector_fc`.

    `for (i, re) in key.enumerate() { serialize_uncompressed_ring_element(re, scratch,
    &mut out[384i .. 384(i+1)]) }` — the K-fold assembly of **L5.6**
    (`serialize_uncompressed_ring_element_fc`), which is PROVED and axiom-clean.

    ## The post is the UPSTREAM `ensures`, transcribed
    `libcrux-ml-kem/src/ind_cpa.rs:154` states it as ONE whole-vector equation,
    `out_future == Hacspec_ml_kem.Serialize.serialize_secret_key $K ($K *! sz 384)
    (vector_to_spec $K $key)`, so that is the shape here — not a per-chunk restatement.
    (`deserialize_vector_fc` had to learn this the hard way: its first draft was stated per
    chunk, which was true and still an invention.)

    ## Falsification: coverage chosen by MEASUREMENT, and the reason it is not a sweep
    Encode evaluates ~37 s per case in the kernel — far more expensive than decode — so an
    exhaustive lane sweep is not affordable here and a first attempt at one was killed by a
    50-minute timeout. It is also not the right test: **the per-element encode math is
    already proved** by L5.6, which was itself falsified exhaustively over all 6657
    admissible lane values in Phase 1. What is NEW in this obligation is the K-FOLD
    PLUMBING, so the probe varies that and nothing else:
    * survives at K = 1, 2, 3 (random and sequential keys);
    * survives at the chunk-boundary extremes — all-0, all-3328, all-(−3328) at K = 2;
    * survives at K = 4 and at K = 5, so **no `is_rank` hypothesis is needed or stated**;
    * **NEGATIVE CONTROL FIRES**: with the bound dropped (lane 3400, the witness that makes
      L5.6 false) the check reports `EQ-MISMATCH`. `h_bnd` is load-bearing, not decorative.

    `T_SIZE` is a spec-side parameter with a defining hypothesis, exactly as L5.4 carries
    `C2_LEN`: the impl has no such argument, the spec function needs one. -/
@[spec]
theorem serialize_vector_fc
    (K T_SIZE : Std.Usize)
    (key : Std.Array
        (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (out : Slice Std.U8)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_out_len : out.length = K.val * 384)
    (h_tsize : T_SIZE.val = K.val * 384)
    -- ENCODE precondition. Machine-refuted without it: lane 3400 diverges (impl [72,13,0],
    -- spec [71,0,0]) — the same witness L5.6 records, reached independently here.
    (h_bnd : ∀ i : Nat, i < K.val → ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
        (((key.val[i]!).coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ind_cpa.serialize_vector
      (vectortraitsOperationsInst := portable_ops_inst) (K := K)
      key out scratch
    ⦃ ⇓ p => ⌜ ∃ enc : Std.Array Std.U8 T_SIZE,
                  hacspec_ml_kem.serialize.serialize_secret_key (RANK := K) T_SIZE
                      (Spec.Lift.lift_vec key)
                    = .ok enc
                  ∧ p.1.length = K.val * 384
                  ∧ ∀ ℓ : Nat, ℓ < K.val * 384 → p.1.val[ℓ]! = enc.val[ℓ]! ⌝ ⦄ := by
  have h_out' : out.val.length = K.val * 384 := h_out_len
  -- SPEC side: the hacspec `createi` IS the pure byte model.
  obtain ⟨enc, henc_eq, henc_get⟩ := spec_serialize_secret_key_eq K T_SIZE key h_tsize
  -- IMPL side: the enumerate loop writes that same model into every byte `< 384K`.
  obtain ⟨p, hp_eq, hp_holds⟩ :=
    triple_exists_ok_fc (sv_loop_fc K key h_bnd out scratch h_out')
  obtain ⟨hp_len, hp_get⟩ := (holds_ok _).mp hp_holds
  refine triple_of_ok_fc (v := p) ?_ ?_
  · -- `into_iter` (the `SharedAArray` delegate) and `enumerate` are both pure `ok`s
    have hred : libcrux_iot_ml_kem.ind_cpa.serialize_vector
          (vectortraitsOperationsInst := portable_ops_inst) (K := K) key out scratch
        = libcrux_iot_ml_kem.ind_cpa.serialize_vector_loop
            (vectortraitsOperationsInst := portable_ops_inst)
            ({ iter := Aeneas.Std.Array.to_slice key, count := 0#usize } : EnumIter SPoly)
            out scratch := rfl
    rw [hred]
    exact hp_eq
  · refine ⟨enc, henc_eq, hp_len, ?_⟩
    intro ℓ hℓ
    rw [hp_get ℓ hℓ, henc_get ℓ (by rw [h_tsize]; exact hℓ)]

/-! ## PROVER bank for INC-2a.3 (`serialize_public_key_mut`)

    **The locked statement of `serialize_public_key_mut_fc` is FALSE** — see the SPECREQ in
    that theorem's docstring. Everything in this section is the proof it *would* have, and
    `spkm_core` below IS that proof, carrying the two hypotheses the locked statement is
    missing (`h_K_pos`, `h_K_bnd`). When the statement is corrected, the top theorem is one
    application of `spkm_core`. -/

section SPKMBank

open libcrux_iot_ml_kem.Util.CreateI

/-! ### `Usize` / constant plumbing not already in `Util/Shared.lean`. -/

/-- `y ≤ x → x - y` succeeds. The `Sub` companion of `Util.Shared.usize_add_ok_e`. -/
private theorem usize_sub_ok_e (x y : Std.Usize) (h : y.val ≤ x.val) :
    ∃ z : Std.Usize, (x - y : Result Std.Usize) = .ok z ∧ z.val = x.val - y.val := by
  obtain ⟨z, hz, hv, _⟩ := Std.WP.spec_imp_exists (Std.UScalar.sub_bv_spec (x := x) (y := y) h)
  exact ⟨z, hz, hv⟩

/-- The impl-side `BITS_PER_RING_ELEMENT` reduces to `3072`. `Util.Shared`'s neighbours stop
    at `BYTES_PER_RING_ELEMENT = 384`; `ranked_bytes_per_ring_element` multiplies by the
    *bit* count first, which is exactly where the overflow gap lives. -/
private theorem impl_bits :
    (libcrux_iot_ml_kem.constants.BITS_PER_RING_ELEMENT : Result Std.Usize)
      = .ok (3072#usize : Std.Usize) := by
  unfold libcrux_iot_ml_kem.constants.BITS_PER_RING_ELEMENT
    libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
  exact usize_mul_lit (256#usize : Std.Usize) (12#usize : Std.Usize)
    (3072#usize : Std.Usize) (by scalar_tac) (by scalar_tac)

/-- `(k * 3072) / 8 = k * 384`, in a CLEAN context. Inline `omega` on this goal inside
    `ranked_bpre` blows `maxRecDepth`: that context carries `K * 3072 ≤ Usize.max`, and any
    `omega` there drags `Std.Usize.max` into the atom set (the closed-large-scalar pitfall,
    skill §6 — the same reason `window_div_mod` above is hoisted). Measured, not guessed:
    `by omega` in place failed exactly this way. -/
private theorem bits_div_8 (k : Nat) : k * 3072 / 8 = k * 384 := by omega

/-- `k * 384 ≤ k * 3072` without `omega`, for the same reason. -/
private theorem mul_384_le_3072 (k : Nat) : k * 384 ≤ k * 3072 :=
  Nat.mul_le_mul_left k (by norm_num)

/-- **The overflow seam.** `ranked_bytes_per_ring_element K` is `(K * 3072) / 8`, NOT
    `K * 384`: the `*` happens at the bit count and only then is divided by 8. So it needs
    `K * 3072 ≤ Usize.max`, which does NOT follow from `K * 384 + 32 ≤ Usize.max`. This is
    one of the two missing hypotheses of the locked statement. -/
private theorem ranked_bpre (K : Std.Usize) (hK : K.val * 3072 ≤ Std.Usize.max) :
    ∃ i : Std.Usize,
      libcrux_iot_ml_kem.constants.ranked_bytes_per_ring_element K = .ok i
      ∧ i.val = K.val * 384 := by
  have h3072 : ((3072#usize : Std.Usize)).val = 3072 := rfl
  have h8 : ((8#usize : Std.Usize)).val = 8 := rfl
  -- `K * 384 ≤ K * 3072 ≤ Usize.max`, hoisted so that `Usize.max` never meets `scalar_tac`
  -- on a goal that also mentions `K * 3072` (the closed-large-scalar pitfall, skill §6).
  have hKb : K.val * 384 ≤ Std.Usize.max := le_trans (mul_384_le_3072 K.val) hK
  obtain ⟨m, hm_eq, hm_val⟩ := usize_mul_ok_e K (3072#usize : Std.Usize) (by rw [h3072]; exact hK)
  have hmv : m.val = K.val * 3072 := by rw [hm_val, h3072]
  have hzv : ((⟨BitVec.ofNat _ (K.val * 384)⟩ : Std.Usize)).val = K.val * 384 :=
    usize_ofNat_val_le _ hKb
  refine ⟨⟨BitVec.ofNat _ (K.val * 384)⟩, ?_, hzv⟩
  unfold libcrux_iot_ml_kem.constants.ranked_bytes_per_ring_element
  rw [impl_bits]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hm_eq]
  exact usize_div_lit m (8#usize : Std.Usize) ⟨BitVec.ofNat _ (K.val * 384)⟩
    (by rw [h8]; exact Nat.succ_ne_zero 7)
    (by rw [hmv, h8, hzv]; exact bits_div_8 K.val)

/-! ### The `RangeFrom` mutable subslice — the tail-copy analogue of
    `Util.Shared.slice_index_mut_range_strict`. `&mut s[a..]` reads
    `Slice.subslice s ⟨a, len s⟩` and writes back through
    `HaxToRange.toRange {start := a} (len s) = ⟨a, len s⟩`, so the only side condition is
    `a < s.length` (the write-back range is non-empty). -/

private theorem slice_index_mut_rangefrom {T : Type} [Inhabited T]
    (s : Slice T) (a : Std.Usize) (h0 : a.val < s.val.length) :
    ∃ (ns : Slice T) (wb : Slice T → Slice T),
      CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
        (CoreModels.core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) s
        { start := a } = .ok (ns, wb)
      ∧ ns.val.length = s.val.length - a.val
      ∧ (∀ s' : Slice T, s'.val.length = s.val.length - a.val →
            (wb s').val = s.val.setSlice! a.val s'.val) := by
  have hlen : (Aeneas.Std.Slice.len s).val = s.val.length := Aeneas.Std.Slice.len_val s
  obtain ⟨ns, hns_eq, hns_val, hns_get⟩ :=
    Std.WP.spec_imp_exists
      (Aeneas.Std.Slice.subslice_spec s ⟨a, Aeneas.Std.Slice.len s⟩ (by scalar_tac) (by scalar_tac))
  have hns_len : ns.val.length = s.val.length - a.val := by
    rw [hns_val]
    show (List.slice a.val (Aeneas.Std.Slice.len s).val s.val).length = s.val.length - a.val
    rw [List.slice_length, hlen]; omega
  have hTR : HaxToRange.toRange ({ start := a }
        : CoreModels.core.ops.range.RangeFrom Std.Usize) (Aeneas.Std.Slice.len s)
      = ({ start := a, «end» := Aeneas.Std.Slice.len s }
          : Aeneas.Std.core.ops.range.Range Std.Usize) := rfl
  refine ⟨ns, (fun sub' =>
      match Aeneas.Std.Slice.update_subslice s
          (HaxToRange.toRange
            ({ start := a } : CoreModels.core.ops.range.RangeFrom Std.Usize)
            (Aeneas.Std.Slice.len s)) sub' with
      | .ok s'' => s''
      | _ => s), ?_, hns_len, ?_⟩
  · unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
    simp only
      [CoreModels.core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
       CoreModels.rust_primitives.slice.slice_length,
       CoreModels.rust_primitives.slice.slice_slice, Aeneas.Std.bind_tc_ok, hns_eq]
    rfl
  · intro s' hs'
    have hupd : Aeneas.Std.Slice.update_subslice s
        (HaxToRange.toRange ({ start := a }
            : CoreModels.core.ops.range.RangeFrom Std.Usize) (Aeneas.Std.Slice.len s)) s'
        = .ok ⟨s.val.setSlice! a.val s'.val, by scalar_tac⟩ := by
      rw [hTR]
      unfold Aeneas.Std.Slice.update_subslice
      rw [dif_pos ⟨by scalar_tac, by scalar_tac, by
        simpa [Aeneas.Std.Slice.length, hlen] using hs'⟩]
    simp only [hupd]

/-! ### SPEC side — `serialize_public_key` IS `encBy` on `[0, 384K)` and `seed` after.

    A `createi EK_SIZE` over a closure that BRANCHES on `ℓ < RANK * 384`: below, it is byte
    `ℓ % 384` of `byte_encode(t[ℓ / 384], 12)` — literally the `serialize_secret_key` closure,
    so `encBy` is reused unchanged; at or above, it is `seed_for_A[ℓ - 384K]`. -/

/-- The pure byte model of the whole public key: the encode model below `384K`, the seed
    above it. -/
private def pkBy (K : Std.Usize) (t : Std.Array SPoly K) (seed : Slice Std.U8) (ℓ : Nat) :
    Std.U8 :=
  if ℓ < K.val * 384 then encBy (t.val[ℓ / 384]!) (ℓ % 384)
  else seed.val[ℓ - K.val * 384]!

/-- The `serialize_public_key` closure at byte index `ℓ`. The `then` branch is `ssk_closure_eq`
    verbatim; only the `else` branch (the seed tail) is new. -/
private theorem spk_closure_eq (K EK_SIZE : Std.Usize) (t : Std.Array SPoly K)
    (seed : Slice Std.U8)
    (hKb : K.val * 384 ≤ Std.Usize.max)
    (h_ek : EK_SIZE.val = K.val * 384 + 32)
    (h_seed : seed.val.length = 32)
    (ℓ : Nat) (hℓ : ℓ < EK_SIZE.val) :
    (hacspec_ml_kem.serialize.serialize_public_key.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
        K EK_SIZE).call_mut
        ((Spec.Lift.lift_vec t, seed) :
          hacspec_ml_kem.serialize.serialize_public_key.closure K EK_SIZE)
        (⟨BitVec.ofNat _ ℓ⟩ : Std.Usize)
      = .ok (pkBy K t seed ℓ,
          ((Spec.Lift.lift_vec t, seed) :
            hacspec_ml_kem.serialize.serialize_public_key.closure K EK_SIZE)) := by
  have hEKmax : EK_SIZE.val ≤ Std.Usize.max := by scalar_tac
  have h384 : ((384#usize : Std.Usize)).val = 384 := rfl
  have hℓv : ((⟨BitVec.ofNat _ ℓ⟩ : Std.Usize)).val = ℓ := usize_ofNat_val_le ℓ (by omega)
  have hbv : ((⟨BitVec.ofNat _ (K.val * 384)⟩ : Std.Usize)).val = K.val * 384 :=
    usize_ofNat_val_le _ hKb
  have hi1 : (K * (384#usize : Std.Usize) : Result Std.Usize)
      = .ok (⟨BitVec.ofNat _ (K.val * 384)⟩ : Std.Usize) :=
    usize_mul_lit K (384#usize : Std.Usize) _ (by rw [h384, hbv]) (by rw [h384]; exact hKb)
  show (hacspec_ml_kem.serialize.serialize_public_key.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
      (RANK := K) (EK_SIZE := EK_SIZE) (Spec.Lift.lift_vec t, seed)
      (⟨BitVec.ofNat _ ℓ⟩ : Std.Usize)) = _
  unfold
    hacspec_ml_kem.serialize.serialize_public_key.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
  rw [hacspec_bpre]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hi1]
  simp only [Aeneas.Std.bind_tc_ok]
  -- The machine-generated closure body, once, with the `let (a, s) := (…, …)` destructuring
  -- discharged (skill §4.1): `dsimp`/`simp only []` do NOT iota-reduce it, `show` does.
  show (if (⟨BitVec.ofNat _ ℓ⟩ : Std.Usize) < (⟨BitVec.ofNat _ (K.val * 384)⟩ : Std.Usize) then
      (do
        let i2 ← (⟨BitVec.ofNat _ ℓ⟩ : Std.Usize) / (384#usize : Std.Usize)
        let j ← (⟨BitVec.ofNat _ ℓ⟩ : Std.Usize) % (384#usize : Std.Usize)
        let a1 ← Aeneas.Std.Array.index_usize (Spec.Lift.lift_vec t) i2
        let encoded ← hacspec_ml_kem.serialize.byte_encode (384#usize : Std.Usize)
            (3072#usize : Std.Usize) a1 (12#usize : Std.Usize)
        let i3 ← Aeneas.Std.Array.index_usize encoded j
        Result.ok (i3, ((Spec.Lift.lift_vec t, seed) :
          hacspec_ml_kem.serialize.serialize_public_key.closure K EK_SIZE)))
    else
      (do
        let i3 ← (⟨BitVec.ofNat _ ℓ⟩ : Std.Usize) - (⟨BitVec.ofNat _ (K.val * 384)⟩ : Std.Usize)
        let i4 ← Aeneas.Std.Slice.index_usize seed i3
        Result.ok (i4, ((Spec.Lift.lift_vec t, seed) :
          hacspec_ml_kem.serialize.serialize_public_key.closure K EK_SIZE)))) = _
  by_cases hlt : ℓ < K.val * 384
  · -- BELOW the tail: the `serialize_secret_key` closure, byte for byte.
    rw [if_pos (show (⟨BitVec.ofNat _ ℓ⟩ : Std.Usize)
        < (⟨BitVec.ofNat _ (K.val * 384)⟩ : Std.Usize) from by
      show ((⟨BitVec.ofNat _ ℓ⟩ : Std.Usize)).val < _
      rw [hℓv, hbv]; exact hlt)]
    have hdv : ((⟨BitVec.ofNat _ (ℓ / 384)⟩ : Std.Usize)).val = ℓ / 384 :=
      usize_ofNat_val_le _ (by omega)
    have hmv : ((⟨BitVec.ofNat _ (ℓ % 384)⟩ : Std.Usize)).val = ℓ % 384 :=
      usize_ofNat_val_le _ (by omega)
    have hdiv : ((⟨BitVec.ofNat _ ℓ⟩ : Std.Usize) / (384#usize : Std.Usize) : Result Std.Usize)
        = .ok (⟨BitVec.ofNat _ (ℓ / 384)⟩ : Std.Usize) :=
      usize_div_lit _ _ _ (by rw [h384]; omega) (by rw [hℓv, h384, hdv])
    have hrem : ((⟨BitVec.ofNat _ ℓ⟩ : Std.Usize) % (384#usize : Std.Usize) : Result Std.Usize)
        = .ok (⟨BitVec.ofNat _ (ℓ % 384)⟩ : Std.Usize) :=
      usize_rem_lit _ _ _ (by rw [h384]; omega) (by rw [hℓv, h384, hmv])
    have hK : ℓ / 384 < K.val := Nat.div_lt_of_lt_mul (by omega)
    have htlen : t.val.length = K.val := t.property
    have hlvlen : (Spec.Lift.lift_vec t).val.length = K.val := (Spec.Lift.lift_vec t).property
    have hcell : (Spec.Lift.lift_vec t).val[ℓ / 384]! = lift_poly (t.val[ℓ / 384]!) := by
      show (t.val.map lift_poly)[ℓ / 384]! = lift_poly (t.val[ℓ / 384]!)
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (by rw [htlen]; exact hK)]
      simp only [Option.map_some, Option.getD_some]
      rw [getElem!_pos t.val (ℓ / 384) (by rw [htlen]; exact hK)]
    have hidx : Aeneas.Std.Array.index_usize (Spec.Lift.lift_vec t)
          (⟨BitVec.ofNat _ (ℓ / 384)⟩ : Std.Usize)
        = .ok (lift_poly (t.val[ℓ / 384]!)) := by
      rw [libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq
        (Spec.Lift.lift_vec t) (⟨BitVec.ofNat _ (ℓ / 384)⟩ : Std.Usize)
        (by rw [show (Spec.Lift.lift_vec t).length = K.val from hlvlen, hdv]; exact hK)]
      rw [hdv, hcell]
    obtain ⟨a, ha_eq, ha_get⟩ :=
      libcrux_iot_ml_kem.SerializeFc.byte_encode_12_eq (t.val[ℓ / 384]!)
    have halen : a.val.length = 384 := a.property
    have haidx : Aeneas.Std.Array.index_usize a (⟨BitVec.ofNat _ (ℓ % 384)⟩ : Std.Usize)
        = .ok (a.val[ℓ % 384]!) := by
      rw [libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq
        a (⟨BitVec.ofNat _ (ℓ % 384)⟩ : Std.Usize)
        (by rw [show a.length = 384 from halen, hmv]; omega)]
      rw [hmv]
    have hpk : pkBy K t seed ℓ = a.val[ℓ % 384]! := by
      unfold pkBy encBy
      rw [if_pos hlt]
      simp only [ha_eq]
    rw [hdiv]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hrem]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hidx]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [ha_eq]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [haidx]
    simp only [Aeneas.Std.bind_tc_ok, hpk]
    rfl
  · -- THE TAIL: byte `ℓ - 384K` of the seed.
    rw [if_neg (show ¬ ((⟨BitVec.ofNat _ ℓ⟩ : Std.Usize)
        < (⟨BitVec.ofNat _ (K.val * 384)⟩ : Std.Usize)) from by
      show ¬ (((⟨BitVec.ofNat _ ℓ⟩ : Std.Usize)).val < _)
      rw [hℓv, hbv]; exact hlt)]
    obtain ⟨d, hd_eq, hd_val⟩ :=
      usize_sub_ok_e (⟨BitVec.ofNat _ ℓ⟩ : Std.Usize)
        (⟨BitVec.ofNat _ (K.val * 384)⟩ : Std.Usize) (by rw [hℓv, hbv]; omega)
    have hdv : d.val = ℓ - K.val * 384 := by rw [hd_val, hℓv, hbv]
    have hdlt : d.val < seed.val.length := by rw [hdv, h_seed]; omega
    have hsidx : Slice.index_usize seed d = .ok (seed.val[d.val]!) :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq
        seed d hdlt
    have hpk : pkBy K t seed ℓ = seed.val[d.val]! := by
      unfold pkBy
      rw [if_neg hlt, hdv]
    rw [hd_eq]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hsidx]
    simp only [Aeneas.Std.bind_tc_ok, hpk]
    rfl

/-- **The spec bridge for the public key.** `serialize_public_key` is `pkBy` at every byte. -/
private theorem spec_serialize_public_key_eq (K EK_SIZE : Std.Usize) (t : Std.Array SPoly K)
    (seed : Slice Std.U8)
    (hKb : K.val * 384 ≤ Std.Usize.max)
    (h_ek : EK_SIZE.val = K.val * 384 + 32)
    (h_seed : seed.val.length = 32) :
    ∃ enc : Std.Array Std.U8 EK_SIZE,
      hacspec_ml_kem.serialize.serialize_public_key (RANK := K) EK_SIZE
          (Spec.Lift.lift_vec t) seed = .ok enc
      ∧ ∀ ℓ : Nat, ℓ < EK_SIZE.val → enc.val[ℓ]! = pkBy K t seed ℓ := by
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq (T := Std.U8) EK_SIZE
      (hacspec_ml_kem.serialize.serialize_public_key.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
        K EK_SIZE)
      ((Spec.Lift.lift_vec t, seed) :
        hacspec_ml_kem.serialize.serialize_public_key.closure K EK_SIZE)
      (fun ℓ => pkBy K t seed ℓ)
      (fun ℓ hℓ => spk_closure_eq K EK_SIZE t seed hKb h_ek h_seed ℓ hℓ)
  refine ⟨⟨(List.range EK_SIZE.val).map (fun m => pkBy K t seed m), by simp⟩, ?_, ?_⟩
  · unfold hacspec_ml_kem.serialize.serialize_public_key
    simp only [hacspec_ml_kem.parameters.createi, hfn]
  · intro ℓ hℓ
    show ((List.range EK_SIZE.val).map (fun m => pkBy K t seed m))[ℓ]! = _
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hℓ]
    simp only [Option.map_some, Option.getD_some]

/-! ### IMPL side, and the proof the locked statement WOULD have.

    `spkm_core` is `serialize_public_key_mut_fc` plus the two hypotheses the locked statement
    is missing. It is a straight-line body walk: no loop, no bit algebra — `serialize_vector_fc`
    (row 1, proved) supplies the whole `[0, 384K)` half through its own post, and the tail is
    one `copy_from_slice` into `serialized[384K..]`. -/

/-! The layout arithmetic, hoisted CONTEXT-FREE. Every one of these was an inline `omega`
    first and every one blew `maxRecDepth`: `spkm_core`'s context carries
    `K * 3072 ≤ Usize.max`, so any `omega` there drags `Std.Usize.max` in (skill §6). Same
    fix as `window_div_mod` and `bits_div_8`, applied uniformly rather than one at a time. -/

private theorem pos_384 (k : Nat) (h : 0 < k) : 0 < k * 384 := by omega
private theorem le_384_32 (k : Nat) : k * 384 ≤ k * 384 + 32 := Nat.le_add_right _ _
private theorem lt_384_32 (k : Nat) : k * 384 < k * 384 + 32 := by omega
private theorem tail_len (k : Nat) : k * 384 + 32 - k * 384 = 32 := by omega
private theorem tail_idx (k ℓ : Nat) (h : ℓ < k * 384 + 32) : ℓ - k * 384 < 32 := by omega

/-- `copy_from_slice` on equal lengths returns the source. -/
private theorem copy_from_slice_ok (dst src : Slice Std.U8)
    (h : dst.val.length = src.val.length) :
    CoreModels.core.slice.Slice.copy_from_slice CoreModels.core.U8.Insts.CoreMarkerCopy dst src
      = .ok src := by
  unfold CoreModels.core.slice.Slice.copy_from_slice
  rw [if_pos (show Aeneas.Std.Slice.len dst = Aeneas.Std.Slice.len src from
    Aeneas.Std.UScalar.eq_of_val_eq (by
      rw [Aeneas.Std.Slice.len_val dst, Aeneas.Std.Slice.len_val src]; exact h))]

/-- **The banked proof of INC-2a.3.** Identical to the locked statement of
    `serialize_public_key_mut_fc` except for `h_K_pos` and `h_K_bnd`, the two hypotheses
    whose absence makes that statement false (see its docstring, SPECREQ INC-2a.3-A/B).
    When the statement is corrected, that theorem is one application of this one. -/
private theorem spkm_core
    (K PUBLIC_KEY_SIZE : Std.Usize)
    (t_as_ntt : Std.Array SPoly K)
    (seed_for_a : Slice Std.U8)
    (serialized : Slice Std.U8)
    (scratch : SVec)
    -- MISSING HYPOTHESIS #1: `serialized[0 .. 384K]` is an EMPTY range at `K = 0`, and
    -- `Slice.subslice` requires `start < end`. Machine-refuted at `K = 0`: `Error.panic`.
    (h_K_pos : 0 < K.val)
    -- MISSING HYPOTHESIS #2: `ranked_bytes_per_ring_element K` computes `(K * 3072) / 8`, so
    -- the multiplication overflows well before `K * 384 + 32` does. Machine-refuted at
    -- `K = 48038396025285290`: `Error.integerOverflow`.
    (h_K_bnd : K.val * 3072 ≤ Std.Usize.max)
    (h_seed_len : seed_for_a.length = 32)
    (h_pk_size : PUBLIC_KEY_SIZE.val = K.val * 384 + 32)
    (h_ser_len : serialized.length = PUBLIC_KEY_SIZE.val)
    (h_bnd : ∀ i : Nat, i < K.val → ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
        (((t_as_ntt.val[i]!).coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ind_cpa.serialize_public_key_mut
      (vectortraitsOperationsInst := portable_ops_inst) (K := K)
      PUBLIC_KEY_SIZE t_as_ntt seed_for_a serialized scratch
    ⦃ ⇓ p => ⌜ ∃ enc : Std.Array Std.U8 PUBLIC_KEY_SIZE,
                  hacspec_ml_kem.serialize.serialize_public_key (RANK := K) PUBLIC_KEY_SIZE
                      (Spec.Lift.lift_vec t_as_ntt) seed_for_a
                    = .ok enc
                  ∧ p.1.length = PUBLIC_KEY_SIZE.val
                  ∧ ∀ ℓ : Nat, ℓ < PUBLIC_KEY_SIZE.val → p.1.val[ℓ]! = enc.val[ℓ]! ⌝ ⦄ := by
  have h0v : ((0#usize : Std.Usize)).val = 0 := rfl
  have hKb : K.val * 384 ≤ Std.Usize.max := le_trans (mul_384_le_3072 K.val) h_K_bnd
  have hseed : seed_for_a.val.length = 32 := h_seed_len
  have hser : serialized.val.length = K.val * 384 + 32 := by
    show serialized.length = _
    rw [h_ser_len, h_pk_size]
  -- (1) the length constant, and (2) `&mut serialized[0 .. 384K]`
  obtain ⟨i, hi_eq, hi_val⟩ := ranked_bpre K h_K_bnd
  obtain ⟨s, wb, hmut_eq, hs_len, hwb⟩ :=
    slice_index_mut_range_strict serialized (0#usize : Std.Usize) i
      (by rw [h0v, hi_val]; exact pos_384 K.val h_K_pos)
      (by rw [hi_val, hser]; exact le_384_32 K.val)
  have hs384 : s.val.length = K.val * 384 := by rw [hs_len, h0v, hi_val, Nat.sub_zero]
  -- (3) L(row 1): `serialize_vector` writes the encode model into every byte `< 384K`
  obtain ⟨p1, hp1_eq, encv, hencv_eq, hp1_len, hp1_get⟩ :=
    triple_exists_ok_fc
      (serialize_vector_fc K i t_as_ntt s scratch hs384 hi_val h_bnd)
  obtain ⟨out1, scr1⟩ := p1
  -- identify `serialize_vector`'s spec-side witness with the pure byte model
  obtain ⟨enc2, henc2_eq, henc2_get⟩ := spec_serialize_secret_key_eq K i t_as_ntt hi_val
  have hencv : encv = enc2 := Result.ok.inj (hencv_eq.symm.trans henc2_eq)
  have hout1_len : out1.val.length = K.val * 384 := hp1_len
  have hout1_get : ∀ ℓ : Nat, ℓ < K.val * 384 →
      out1.val[ℓ]! = encBy (t_as_ntt.val[ℓ / 384]!) (ℓ % 384) := by
    intro ℓ hℓ
    rw [show out1.val[ℓ]! = encv.val[ℓ]! from hp1_get ℓ hℓ, hencv,
      henc2_get ℓ (by rw [hi_val]; exact hℓ)]
  -- (4) write-back of the encoded prefix
  have hwbv := hwb out1 (by rw [hout1_len, h0v, hi_val, Nat.sub_zero])
  have hser1_len : (wb out1).val.length = K.val * 384 + 32 := by
    rw [hwbv, List.length_setSlice!]; exact hser
  have hser1_get : ∀ ℓ : Nat, ℓ < K.val * 384 →
      (wb out1).val[ℓ]! = encBy (t_as_ntt.val[ℓ / 384]!) (ℓ % 384) := by
    intro ℓ hℓ
    rw [hwbv, List.getElem!_setSlice!_middle _ _ _ _
      ⟨by rw [h0v]; exact Nat.zero_le ℓ,
       by rw [hout1_len, h0v, Nat.sub_zero]; exact hℓ,
       by rw [hser]; exact Nat.lt_of_lt_of_le hℓ (le_384_32 K.val)⟩, h0v, Nat.sub_zero]
    exact hout1_get ℓ hℓ
  -- (5) the discarded `ct_declassify` read of `serialized1[0 .. 384K]`
  have hread : CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
      (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
      (wb out1) { start := (0#usize : Std.Usize), «end» := i } = .ok _ :=
    slice_range_index_ok (wb out1) (0#usize : Std.Usize) i
      (by rw [h0v, hi_val]; exact pos_384 K.val h_K_pos)
      (by rw [hi_val, hser1_len]; exact le_384_32 K.val)
  -- (6) `&mut serialized1[384K ..]`, and (7) the tail copy
  obtain ⟨s3, wb2, hmut2_eq, hs3_len, hwb2⟩ :=
    slice_index_mut_rangefrom (wb out1) i
      (by rw [hi_val, hser1_len]; exact lt_384_32 K.val)
  have hs3_32 : s3.val.length = 32 := by
    rw [hs3_len, hser1_len, hi_val]; exact tail_len K.val
  have hcp : CoreModels.core.slice.Slice.copy_from_slice
      CoreModels.core.U8.Insts.CoreMarkerCopy s3 seed_for_a = .ok seed_for_a :=
    copy_from_slice_ok s3 seed_for_a (by rw [hs3_32, hseed])
  have hwb2v := hwb2 seed_for_a (by rw [hseed, hser1_len, hi_val]; exact (tail_len K.val).symm)
  -- (8) the SPEC side
  obtain ⟨enc, henc_eq, henc_get⟩ :=
    spec_serialize_public_key_eq K PUBLIC_KEY_SIZE t_as_ntt seed_for_a hKb h_pk_size hseed
  refine triple_of_ok_fc (v := (wb2 seed_for_a, scr1)) ?_ ?_
  · unfold libcrux_iot_ml_kem.ind_cpa.serialize_public_key_mut
    -- The machine-generated body, once, in HAND-WRITTEN `do` form (skill §4.1). This is not
    -- cosmetic: the `let (s, index_mut_back) ← …` pattern binders come out of `unfold` as
    -- compiled matcher applications that neither `simp only [bind_tc_ok]` nor `dsimp` will
    -- iota-reduce, so every later `rw` fails under them. Re-stating the block makes the
    -- binders ours and each `rw` then lands.
    show (do
        let i' ← libcrux_iot_ml_kem.constants.ranked_bytes_per_ring_element K
        let (s', index_mut_back) ←
          CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
            (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
              Std.U8) serialized { start := (0#usize : Std.Usize), «end» := i' }
        let (s1, scratch1) ←
          libcrux_iot_ml_kem.ind_cpa.serialize_vector portable_ops_inst t_as_ntt s' scratch
        let s2 ← CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
          (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
          (index_mut_back s1) { start := (0#usize : Std.Usize), «end» := i' }
        let _ ← libcrux_secrets.mem_requests.ct_declassify s2
        let (s3', index_mut_back1) ←
          CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
            (CoreModels.core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
              Std.U8) (index_mut_back s1) { start := i' }
        let s4 ← CoreModels.core.slice.Slice.copy_from_slice
          CoreModels.core.U8.Insts.CoreMarkerCopy s3' seed_for_a
        Result.ok (index_mut_back1 s4, scratch1)) = _
    rw [hi_eq]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hmut_eq]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hp1_eq]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hread]
    simp only [libcrux_secrets.mem_requests.ct_declassify, Aeneas.Std.bind_tc_ok]
    rw [hmut2_eq]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hcp]
    rfl
  · refine ⟨enc, henc_eq, ?_, ?_⟩
    · show (wb2 seed_for_a).val.length = _
      rw [hwb2v, List.length_setSlice!, hser1_len, h_pk_size]
    · intro ℓ hℓ
      rw [h_pk_size] at hℓ
      rw [henc_get ℓ (by rw [h_pk_size]; exact hℓ)]
      show (wb2 seed_for_a).val[ℓ]! = _
      rw [hwb2v]
      unfold pkBy
      by_cases hlt : ℓ < K.val * 384
      · rw [if_pos hlt,
          List.getElem!_setSlice!_prefix _ _ _ _ (by rw [hi_val]; exact hlt)]
        exact hser1_get ℓ hlt
      · rw [if_neg hlt,
          List.getElem!_setSlice!_middle _ _ _ _
            ⟨by rw [hi_val]; exact Nat.le_of_not_lt hlt,
             by rw [hseed, hi_val]; exact tail_idx K.val ℓ hℓ,
             by rw [hser1_len]; exact hℓ⟩, hi_val]

/-! ### SPECREQ INC-2a.3, KERNEL-CHECKED (r2, 2026-08-19).

    r1 established both counterexamples by `#eval` on the extracted body and reported them
    as "machine-refuted". That is a computation, not a proof, and the driver's gate does not
    re-derive `#eval` output. The five lemmas below replace it with theorems, so the claim
    "this statement is false" now carries the same weight as any other result in this tree.
    Axioms: `propext / Classical.choice / Quot.sound`, i.e. NOT the `Util.SliceSpecs`
    empty-subslice axioms — which matters here more than usual, see `spkm_locked_false`. -/

/-- `x * y` fails with `integerOverflow` once the product exceeds `Usize.max`. `Usize.max`
    is kept SYMBOLIC throughout (`2 ^ numBits - 1`, never a literal), so nothing here is
    exposed to the closed-large-scalar pitfall (skill §6) — that is the whole reason
    counterexample B is stated as a symbolic bound rather than at r1's witness `K`. -/
private theorem usize_mul_overflow (x y : Std.Usize) (h : Std.Usize.max < x.val * y.val) :
    (x * y : Result Std.Usize) = .fail .integerOverflow := by
  have h1 : ¬ (Aeneas.Std.UScalar.check_bounds .Usize (x.val * y.val)) := by
    simp only [Aeneas.Std.UScalar.check_bounds, decide_eq_true_eq, Nat.not_lt]
    have hm : Std.Usize.max = 2 ^ Aeneas.Std.UScalarTy.Usize.numBits - 1 := by
      rw [← Aeneas.Std.UScalar.max_USize_eq, Aeneas.Std.UScalar.max]
    have hp : 0 < 2 ^ Aeneas.Std.UScalarTy.Usize.numBits := Nat.two_pow_pos _
    omega
  show Aeneas.Std.UScalar.mul x y = _
  unfold Aeneas.Std.UScalar.mul Aeneas.Std.UScalar.tryMk Aeneas.Std.UScalar.tryMkOpt
  rw [dif_neg h1]
  rfl

/-- **Counterexample B's seam.** `ranked_bytes_per_ring_element` multiplies at the BIT count
    (`K * 3072`) and only then divides by 8, so it overflows 8× sooner than `K * 384 + 32`
    does. The dual of `ranked_bpre`, which is the same computation on the succeeding side. -/
private theorem ranked_bpre_overflow (K : Std.Usize) (hK : Std.Usize.max < K.val * 3072) :
    libcrux_iot_ml_kem.constants.ranked_bytes_per_ring_element K = .fail .integerOverflow := by
  unfold libcrux_iot_ml_kem.constants.ranked_bytes_per_ring_element
  rw [impl_bits]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [usize_mul_overflow K (3072#usize : Std.Usize)
    (by show Std.Usize.max < K.val * ((3072#usize : Std.Usize)).val; exact hK)]
  rfl

/-- **Counterexample A's seam.** `&mut s[0 .. 0]`: `index_mut` reads through
    `Slice.subslice`, whose *definition* (`aeneas/Std/Slice.lean:293`) requires
    `start < end` and fails on the empty range. Note carefully that this is the DEFINITION,
    reached by `unfold` — it is NOT `Util.SliceSpecs.Slice.subslice_le_eq`, the axiom that
    asserts the opposite (see `spkm_locked_false`). -/
private theorem idx_mut_empty_fail {T : Type} (s : Slice T) (i : Std.Usize) (hi : i.val = 0) :
    CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
      (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T)
      s { start := 0#usize, «end» := i } = .fail .panic := by
  unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
  simp only [CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
    CoreModels.rust_primitives.slice.slice_slice]
  have hsub : Aeneas.Std.Slice.subslice s ⟨0#usize, i⟩ = .fail .panic := by
    unfold Aeneas.Std.Slice.subslice
    rw [if_neg (by show ¬ (((0#usize : Std.Usize)).val < i.val ∧ _); rw [hi]; omega)]
  rw [hsub]
  rfl

/-- **SPECREQ INC-2a.3-A, PROVED.** At `K = 0` the extracted `serialize_public_key_mut` fails
    for EVERY `PUBLIC_KEY_SIZE`, every `serialized`, every `seed_for_a`, every `scratch`, at
    every vector type — so no choice of the remaining arguments can rescue the Triple. -/
private theorem spkm_fail_at_K0 {V : Type}
    (inst : libcrux_iot_ml_kem.vector.traits.Operations V)
    (PUBLIC_KEY_SIZE : Std.Usize)
    (t_as_ntt : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement V) (0#usize))
    (seed_for_a serialized : Slice Std.U8) (scratch : V) :
    libcrux_iot_ml_kem.ind_cpa.serialize_public_key_mut (Vector := V) (K := 0#usize)
        PUBLIC_KEY_SIZE inst t_as_ntt seed_for_a serialized scratch
      = .fail .panic := by
  obtain ⟨i, hi_eq, hi_val⟩ := ranked_bpre (0#usize : Std.Usize) (by scalar_tac)
  have hi0 : i.val = 0 := by rw [hi_val]; scalar_tac
  unfold libcrux_iot_ml_kem.ind_cpa.serialize_public_key_mut
  rw [hi_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [idx_mut_empty_fail serialized i hi0]
  rfl

/-- **SPECREQ INC-2a.3-B, PROVED** to the same depth as A: once `K * 3072 > Usize.max` the
    function fails for every choice of the remaining arguments. What is NOT mechanised is
    the *witness* — a `Slice Std.U8` of length `K * 384 + 32` is a perfectly good term
    (`List.replicate`), but building it needs a case split on `Usize.numBits` and two
    ~20-digit literals, and it would add nothing: A already refutes the statement outright.
    B's job is narrower and this lemma discharges it in full — it shows `0 < K` ALONE does
    not repair the statement, so the minimal fix needs BOTH hypotheses (or `is_rank`). -/
private theorem spkm_fail_at_large_K {V : Type} {K : Std.Usize}
    (inst : libcrux_iot_ml_kem.vector.traits.Operations V)
    (PUBLIC_KEY_SIZE : Std.Usize)
    (t_as_ntt : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement V) K)
    (seed_for_a serialized : Slice Std.U8) (scratch : V)
    (hK : Std.Usize.max < K.val * 3072) :
    libcrux_iot_ml_kem.ind_cpa.serialize_public_key_mut (Vector := V) (K := K)
        PUBLIC_KEY_SIZE inst t_as_ntt seed_for_a serialized scratch
      = .fail .integerOverflow := by
  unfold libcrux_iot_ml_kem.ind_cpa.serialize_public_key_mut
  rw [ranked_bpre_overflow K hK]
  rfl

/-! #### The witnesses for A. All four locked hypotheses hold at them. -/

private def w32 : Slice Std.U8 := ⟨List.replicate 32 (0#u8), by simp; scalar_tac⟩
private def wT0 : Std.Array SPoly (0#usize) := ⟨[], by simp⟩
private def wV : SVec := ⟨⟨List.replicate 16 (0#i16), by simp⟩⟩

private theorem w32_len : w32.length = 32 := by
  show (List.replicate 32 (0#u8)).length = 32
  simp

/-- **THE REFUTATION.** The locked statement of `serialize_public_key_mut_fc`, ∀-closed over
    exactly its own binders and hypotheses, is FALSE — machine-checked, axioms
    `propext / Classical.choice / Quot.sound`.

    Read together with `spkm_core` (the same statement plus `h_K_pos` and `h_K_bnd`, PROVED),
    this is a completed decomposition: the obligation is true exactly on the hypotheses the
    scaffold dropped, and false without them. Nothing about the POST is weakened anywhere.

    ⚠ One caveat that is NOT about this row, and is the reason the docstring above is so
    insistent about which subslice fact each lemma uses. `Util.SliceSpecs` axiomatises
    `Slice.subslice s ⟨a,b⟩ = .ok _` for `a ≤ b` (`AENEAS-SUBSLICE-STRICT`), which
    contradicts `Slice.subslice`'s definition at `a = b` — so `False` is derivable from that
    axiom, and the locked statement is therefore *also* "provable" from it. The allowlist is
    what keeps that out: this refutation and `spkm_core` both stand clear of those axioms.
    Reported to the driver as a trust-boundary finding; it is not this row's to fix. -/
private theorem spkm_locked_false :
    ¬ (∀ (K PUBLIC_KEY_SIZE : Std.Usize) (t_as_ntt : Std.Array SPoly K)
         (seed_for_a serialized : Slice Std.U8) (scratch : SVec),
         seed_for_a.length = 32 →
         PUBLIC_KEY_SIZE.val = K.val * 384 + 32 →
         serialized.length = PUBLIC_KEY_SIZE.val →
         (∀ i : Nat, i < K.val → ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
             (((t_as_ntt.val[i]!).coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs
               ≤ 3328) →
         ⦃ ⌜ True ⌝ ⦄
         libcrux_iot_ml_kem.ind_cpa.serialize_public_key_mut
           (vectortraitsOperationsInst := portable_ops_inst) (K := K)
           PUBLIC_KEY_SIZE t_as_ntt seed_for_a serialized scratch
         ⦃ ⇓ p => ⌜ ∃ enc : Std.Array Std.U8 PUBLIC_KEY_SIZE,
                       hacspec_ml_kem.serialize.serialize_public_key (RANK := K) PUBLIC_KEY_SIZE
                           (Spec.Lift.lift_vec t_as_ntt) seed_for_a
                         = .ok enc
                       ∧ p.1.length = PUBLIC_KEY_SIZE.val
                       ∧ ∀ ℓ : Nat, ℓ < PUBLIC_KEY_SIZE.val →
                             p.1.val[ℓ]! = enc.val[ℓ]! ⌝ ⦄) := by
  intro h
  -- the witness: K = 0, PUBLIC_KEY_SIZE = 32, both slices 32 zero bytes, `h_bnd` vacuous
  have hT := h (0#usize) (32#usize) wT0 w32 w32 wV w32_len (by scalar_tac)
    (by rw [w32_len]; scalar_tac) (by intro i hi; exact absurd hi (by scalar_tac))
  obtain ⟨v, hv, _⟩ := triple_exists_ok_fc hT
  rw [spkm_fail_at_K0 portable_ops_inst (32#usize) wT0 w32 w32 wV] at hv
  exact absurd hv (by simp)

end SPKMBank

/-- **INC-2a.3** — `ind_cpa.serialize_public_key_mut`: concatenate `t̂` and `ρ`.

    `serialize_vector(t_as_ntt, &mut serialized[0..384K])` then
    `serialized[384K..].copy_from_slice(seed_for_a)`. So it is INC-2a.2 plus a tail copy.

    **This function is only extractable at all as of 2026-08-19.** It was in `OPAQUE` with
    no rationale because the Lean lane compiles without `--cfg hax`, which selected its
    `#[cfg(not(hax))]` body — the one calling `classify_ref_mut()`, a `&mut`-RETURNING
    method Aeneas cannot translate. Gating on `cfg(hax_compilation)` (the flag this lane
    does set) selects the intended body. See `plans/INC-2-scope.md` §8.

    Post transcribed from `libcrux-ml-kem/src/ind_cpa.rs:114`:
    `serialized_future == Hacspec_ml_kem.Serialize.serialize_public_key $K $PUBLIC_KEY_SIZE
    (vector_to_spec $K $t_as_ntt) $seed_for_a`.
    `h_seed_len` and `h_pk_size` are the upstream `requires`, transcribed; `is_rank` is NOT,
    for the same measured reason as INC-2a.2.

    ────────────────────────────────────────────────────────────────────────────────────────
    # SPECREQ INC-2a.3 — THIS STATEMENT IS FALSE AS LOCKED (PROVER, 2026-08-19)

    It is under-constrained in exactly two places, and BOTH are machine-refuted (`#eval` on
    the extracted impl, all four hypotheses satisfied at the witness). The obligation is
    otherwise true and PROVED: `spkm_core` above is this statement plus the two missing
    hypotheses, closed, axioms `propext / Classical.choice / Quot.sound`.

    Dropping `is_rank K` was right for INC-2a.2 (`serialize_vector`) — that body only ever
    computes `cnt * 384`, which the output length already bounds. It is NOT right here,
    because `serialize_public_key_mut` does two things `serialize_vector` does not.

    ## (A) `K = 0` — the empty mutable subslice. `Error.panic`.
    The body's second step is `&mut serialized[0 .. ranked_bytes_per_ring_element K]`. At
    `K = 0` that range is `[0, 0)`, and `Aeneas.Std.Slice.subslice` requires
    `start < end` — so `index_mut` fails and the program does not return.
    Witness, every hypothesis satisfied: `K = 0`, `PUBLIC_KEY_SIZE = 32`,
    `serialized = replicate 32 0u8` (`h_pk_size`, `h_ser_len` ✓), `seed_for_a = replicate 32
    0u8` (`h_seed_len` ✓), `t_as_ntt = ⟨[], rfl⟩` (`h_bnd` vacuous).
    Measured: `serialize_public_key_mut … = fail Error.panic`, localised to
    `core.Slice.Insts.CoreOpsIndexIndexMut.index_mut … {start := 0, end := 0}`, which alone
    also returns `fail Error.panic` (`end := 384` on the same slice returns `ok`, len 384).

    ## (B) large `K` — `ranked_bytes_per_ring_element` overflows. `Error.integerOverflow`.
    `constants.ranked_bytes_per_ring_element K` is NOT `K * 384`; it is
    `let i ← BITS_PER_RING_ELEMENT (= 3072); let i1 ← K * i; i1 / 8`.
    So it needs `K * 3072 ≤ Usize.max`, which is 8× stronger than anything `h_pk_size` +
    `h_ser_len` give (they give only `K * 384 + 32 ≤ Usize.max`).
    Witness on this 64-bit platform (`Usize.max = 18446744073709551615`):
    `K = 48038396025285290`, `PUBLIC_KEY_SIZE = K * 384 + 32 = 18446744073709551392`
    (`≤ Usize.max` ✓, so `h_pk_size`/`h_ser_len` are satisfiable), all coefficients `0`
    (`h_bnd` ✓). Then `K * 3072 = 147573952589676410880 > Usize.max` and
    `ranked_bytes_per_ring_element K = fail Error.integerOverflow`. Measured directly.

    ## Proposed fix — upstream `requires`, in preference order
    1. **Restore the upstream `is_rank`**, which upstream `ind_cpa.rs` does carry and which
       this scaffold dropped: `#[hax_lib::requires(is_rank::<K>())]`. `K ∈ {2,3,4}` kills
       both (A) and (B) at once, and is what the caller always satisfies.
    2. If a rank-generic statement is wanted (INC-2a.2 is one, legitimately), the MINIMAL
       transcription is the two facts the body actually needs:
       `#[hax_lib::requires(K > 0 && K * 3072 <= usize::MAX)]`
       i.e. in the Lean statement, two extra hypotheses
       `(h_K_pos : 0 < K.val)` and `(h_K_bnd : K.val * 3072 ≤ Std.Usize.max)`.
       These are exactly `spkm_core`'s, so option 2 closes in ONE line:
       `exact spkm_core K PUBLIC_KEY_SIZE t_as_ntt seed_for_a serialized scratch`
       `  h_K_pos h_K_bnd h_seed_len h_pk_size h_ser_len h_bnd`.

    ## What is NOT wrong
    The post itself. The tail conjunct and the length arithmetic — which the dispatch brief
    flagged as the residual risk, this being the one statement in the campaign to reach a
    prover without an evaluation pass — are both CORRECT: the `[0, 384K)` half is
    `serialize_vector_fc`'s post byte for byte, and the `[384K, PUBLIC_KEY_SIZE)` half is
    `seed_for_a[ℓ - 384K]`, matching the spec closure's `else` branch. Both are proved in
    `spkm_core`, which is a stronger check than any probe. Nothing in this SPECREQ asks for
    the post to be weakened.

    ## r2 (2026-08-19): the SPECREQ is now PROVED, not measured
    Everything above was established by `#eval`. It is now machine-checked, in the bank:
    `spkm_locked_false` is a theorem that the ∀-closure of THIS statement — its own binders,
    its own four hypotheses, its own post — is false, axioms `propext / Classical.choice /
    Quot.sound`. Supporting: `spkm_fail_at_K0` (A, for all remaining arguments),
    `spkm_fail_at_large_K` + `ranked_bpre_overflow` (B, symbolic in `Usize.max`, so B's
    ~20-digit witness is never evaluated), `idx_mut_empty_fail`, `usize_mul_overflow`.
    r1's verdict is confirmed in every particular; only the strength of the evidence changed.

    ## r2 trust-boundary finding — NOT this row's to fix, but it decides how to read this row
    `Util.SliceSpecs` (`AENEAS-SUBSLICE-STRICT`) axiomatises `Slice.subslice` / `update_subslice`
    / `Array.update_subslice` as SUCCEEDING for `start ≤ end`, while aeneas's definitions
    `fail` at `start = end`. Those axioms are therefore refutable in this very build — `False`
    follows from `Slice.subslice_le_eq` applied at `⟨0,0⟩` (checked). Consequences: (i) the
    locked statement is *also* derivable from them, so the axiom allowlist, not the proof
    search, is what makes this row's SPECREQ the honest answer; (ii) `spkm_core` and every
    lemma above deliberately go through the real strict `Slice.subslice_spec` (via
    `Util.Shared.slice_index_mut_range_strict`) and are clean; (iii) obligations elsewhere
    that DO list these axioms are vacuous — see the r2 self-report for the list. -/
@[spec]
theorem serialize_public_key_mut_fc
    (K PUBLIC_KEY_SIZE : Std.Usize)
    (t_as_ntt : Std.Array
        (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (seed_for_a : Slice Std.U8)
    (serialized : Slice Std.U8)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_seed_len : seed_for_a.length = 32)
    (h_pk_size : PUBLIC_KEY_SIZE.val = K.val * 384 + 32)
    (h_ser_len : serialized.length = PUBLIC_KEY_SIZE.val)
    (h_bnd : ∀ i : Nat, i < K.val → ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
        (((t_as_ntt.val[i]!).coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ind_cpa.serialize_public_key_mut
      (vectortraitsOperationsInst := portable_ops_inst) (K := K)
      PUBLIC_KEY_SIZE t_as_ntt seed_for_a serialized scratch
    ⦃ ⇓ p => ⌜ ∃ enc : Std.Array Std.U8 PUBLIC_KEY_SIZE,
                  hacspec_ml_kem.serialize.serialize_public_key (RANK := K) PUBLIC_KEY_SIZE
                      (Spec.Lift.lift_vec t_as_ntt) seed_for_a
                    = .ok enc
                  ∧ p.1.length = PUBLIC_KEY_SIZE.val
                  ∧ ∀ ℓ : Nat, ℓ < PUBLIC_KEY_SIZE.val → p.1.val[ℓ]! = enc.val[ℓ]! ⌝ ⦄ := by
  -- NOT PROVABLE: this statement is FALSE at `K = 0` and at `K * 3072 > Usize.max`, both
  -- machine-refuted. See SPECREQ INC-2a.3 in the docstring above. The proof it WOULD have is
  -- `spkm_core`, closed and axiom-clean; correcting the statement per option 1 or 2 of the
  -- SPECREQ turns this `sorry` into one application of it. The statement is left byte-for-byte
  -- as locked, per the freeze.
  sorry

end libcrux_iot_ml_kem.IndCpaFc
