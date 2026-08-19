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


private theorem triple_of_ok_fc {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ :=
  Vector.Portable.Arithmetic.PerElement.triple_of_ok_fc hx hp


/-! ### `Usize` arithmetic bridges (`SerializeFc.lean:849/1470/1476/3719/3737`). -/






/-! ### `Slice` bridges (`SerializeFc.lean:3259/3266/3853/3858/4030/4037/4042`). -/

private theorem slice_len_eq_384 (sl : Slice Std.U8) (h : sl.val.length = 384) :
    Aeneas.Std.Slice.len sl = (384#usize : Std.Usize) := by
  refine Aeneas.Std.UScalar.eq_of_val_eq ?_
  rw [Aeneas.Std.Slice.len_val]
  show sl.val.length = ((384#usize : Std.Usize)).val
  rw [h]; scalar_tac

private theorem slice_len_384 (sl : Slice Std.U8) (h : sl.val.length = 384) :
    CoreModels.core.slice.Slice.len sl = .ok (384#usize : Std.Usize) := by
  simp only [CoreModels.core.slice.Slice.len, slice_len_eq_384 sl h]
  rfl






/-! ### The two `BYTES_PER_RING_ELEMENT` constants (`SerializeFc.lean:3746/3758`).
    Both are `irreducible`, so each needs its explicit unfolding. -/

private theorem hacspec_bpre :
    (hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT : Result Std.Usize)
      = .ok (384#usize : Std.Usize) := by
  unfold hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT
    hacspec_ml_kem.parameters.BITS_PER_RING_ELEMENT
    hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT
  rw [usize_mul_lit (256#usize : Std.Usize) (12#usize : Std.Usize)
    (3072#usize : Std.Usize) (by scalar_tac) (by scalar_tac)]
  simp only [Aeneas.Std.bind_tc_ok]
  exact usize_div_lit _ _ _ (by scalar_tac) (by scalar_tac)

private theorem impl_bpre :
    (libcrux_iot_ml_kem.constants.BYTES_PER_RING_ELEMENT : Result Std.Usize)
      = .ok (384#usize : Std.Usize) := by
  unfold libcrux_iot_ml_kem.constants.BYTES_PER_RING_ELEMENT
    libcrux_iot_ml_kem.constants.BITS_PER_RING_ELEMENT
    libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
  rw [usize_mul_lit (256#usize : Std.Usize) (12#usize : Std.Usize)
    (3072#usize : Std.Usize) (by scalar_tac) (by scalar_tac)]
  simp only [Aeneas.Std.bind_tc_ok]
  exact usize_div_lit _ _ _ (by scalar_tac) (by scalar_tac)

/-! ### `Spec.pk_chunk` -/

/-- `Spec.pk_chunk` delivers a FULL 384-byte window at every `i < K`
    (`SerializeFc.lean:3726`). -/
private theorem pk_chunk_len_384 (secret_key : Slice Std.U8) (K : Std.Usize)
    (h_sk : secret_key.val.length = K.val * 384) (i : Nat) (hi : i < K.val) :
    (Spec.pk_chunk secret_key i).val.length = 384 := by
  show ((secret_key.val.drop (i * 384)).take 384).length = 384
  rw [List.length_take, List.length_drop, h_sk]
  have h : (i + 1) * 384 ≤ K.val * 384 := by apply Nat.mul_le_mul_right; omega
  omega

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

/-- **`byte_decode` at `d = 12` succeeds**, in both the slice and the array shape,
    with the SAME value. Same content as `SerializeFc.lean`'s same-named lemma, which is
    ALSO axiom-clean but is `private` and hence unreachable here; the gain of this copy is
    reachability plus cost — it is derived from the PROVED leaf L5.7 in four lines, where
    the original re-derives it spec-side through the ~60-line 12-bit bank. -/
private theorem byte_decode_dyn_12_ok (b : Slice Std.U8) (hb : b.val.length = 384) :
    ∃ q : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize,
      hacspec_ml_kem.serialize.byte_decode_dyn b 12#usize = .ok q
      ∧ hacspec_ml_kem.serialize.byte_decode (D32 := 384#usize) 3072#usize
          (⟨b.val, by rw [hb]; scalar_tac⟩ : Std.Array Std.U8 384#usize) 12#usize = .ok q := by
  obtain ⟨p, _, hdyn, _⟩ :=
    triple_exists_ok_fc
      (libcrux_iot_ml_kem.SerializeFc.deserialize_to_uncompressed_ring_element_fc b
        default (by simpa [Aeneas.Std.Slice.length] using hb))
  exact ⟨lift_poly p, hdyn, by rw [← byte_decode_dyn_12_arr b hb]; exact hdyn⟩

/-! ### SPEC side — `vector_decode_12` IS the pure model. -/

/-- The `vector_decode_12` closure at index `k` decodes exactly `Spec.pk_chunk sk k`,
    hence produces the `k`-th cell of the pure model (`SerializeFc.lean:3889`). -/
private theorem vector_decode_12_closure_eq (K : Std.Usize) (secret_key : Slice Std.U8)
    (h_sk : secret_key.val.length = K.val * 384) (k : Nat) (hk : k < K.val) :
    (hacspec_ml_kem.serialize.vector_decode_12.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256
        K).call_mut secret_key (⟨BitVec.ofNat _ k⟩ : Std.Usize)
      = .ok ((Spec.t_as_ntt_from_public_key_pure secret_key K).val[k]!, secret_key) := by
  have hk384' : k * 384 + 384 ≤ K.val * 384 := by
    have h : (k + 1) * 384 ≤ K.val * 384 := by apply Nat.mul_le_mul_right; omega
    calc k * 384 + 384 = (k + 1) * 384 := by ring
      _ ≤ K.val * 384 := h
  have hKmax : K.val * 384 ≤ Std.Usize.max := by
    rw [← h_sk]; exact secret_key.property
  have hk384 : k * 384 + 384 ≤ Std.Usize.max := le_trans hk384' hKmax
  have h384 : ((384#usize : Std.Usize)).val = 384 := rfl
  have hkval : ((⟨BitVec.ofNat _ k⟩ : Std.Usize)).val = k :=
    usize_ofNat_val_le k (le_trans (Nat.le_trans (Nat.le_mul_of_pos_right k (by omega))
      (Nat.le_add_right _ 384)) hk384)
  obtain ⟨st, hst_eq, hst_val⟩ :=
    usize_mul_ok_e (⟨BitVec.ofNat _ k⟩ : Std.Usize) (384#usize : Std.Usize)
      (by rw [hkval, h384]; exact le_trans (Nat.le_add_right _ 384) hk384)
  rw [hkval, h384] at hst_val
  obtain ⟨en, hen_eq, hen_val⟩ :=
    usize_add_ok_e st (384#usize : Std.Usize) (by rw [hst_val, h384]; exact hk384)
  have hen_val' : en.val = k * 384 + 384 := by
    rw [hen_val, hst_val, h384]
  have hchunk_len : (Spec.pk_chunk secret_key k).val.length = 384 :=
    pk_chunk_len_384 secret_key K h_sk k hk
  have hidx := slice_range_index_ok secret_key st en
    (by rw [hst_val, hen_val']; omega) (by rw [hen_val', h_sk]; exact hk384')
  rw [window_eq_pk_chunk secret_key st en k hst_val hen_val'] at hidx
  have htry :
      CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
          (384#usize : Std.Usize) (Spec.pk_chunk secret_key k)
        = .ok (CoreModels.core.result.Result.Ok
            (⟨(Spec.pk_chunk secret_key k).val, by rw [hchunk_len]; scalar_tac⟩ :
              Std.Array Std.U8 384#usize)) := by
    unfold
      CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
    rw [dif_pos (slice_len_eq_384 _ hchunk_len)]
  obtain ⟨q, hq_dyn, hq_arr⟩ := byte_decode_dyn_12_ok (Spec.pk_chunk secret_key k) hchunk_len
  have hcell : (Spec.t_as_ntt_from_public_key_pure secret_key K).val[k]! = q := by
    show ((List.range K.val).map (fun i =>
        match hacspec_ml_kem.serialize.byte_decode_dyn (Spec.pk_chunk secret_key i) 12#usize with
        | .ok p => p
        | _ => default))[k]! = q
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
    simp only [Option.map_some, Option.getD_some, hq_dyn]
  show (hacspec_ml_kem.serialize.vector_decode_12.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut
      (RANK := K) secret_key (⟨BitVec.ofNat _ k⟩ : Std.Usize)) = _
  unfold
    hacspec_ml_kem.serialize.vector_decode_12.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut
  rw [hacspec_bpre]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hst_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hen_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hidx]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [htry]
  simp only [Aeneas.Std.bind_tc_ok, CoreModels.core.result.Result.unwrap]
  rw [hq_arr]
  simp only [Aeneas.Std.bind_tc_ok, hcell]

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

/-- Generic-bound `Range.next` bridges, in the `Range.Insts…next` spelling the loop
    body uses. Thin wrappers over the PUBLIC `Ntt.Layer4PlusFC` versions (the
    `SerializeFc.lean:3272/3296` copies are `private`). -/
private theorem iter_some_gen (i e : Std.Usize) (h_lt : i.val < e.val) :
    ∃ s : Std.Usize, s.val = i.val + 1 ∧
      CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
          CoreModels.core.Usize.Insts.CoreIterRangeStep
          ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)
        = .ok (some i,
            ({ start := s, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)) := by
  obtain ⟨s, hs, heq⟩ := libcrux_iot_ml_kem.Ntt.Layer4PlusFC.iter_next_some_eq_gen i e h_lt
  exact ⟨s, hs, heq⟩

private theorem iter_none_gen (i e : Std.Usize) (h_ge : e.val ≤ i.val) :
    CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
        CoreModels.core.Usize.Insts.CoreIterRangeStep
        ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)
      = .ok ((none : Option Std.Usize),
          ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)) :=
  libcrux_iot_ml_kem.Ntt.Layer4PlusFC.iter_next_none_eq_gen i e h_ge

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
  sorry

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
    for the same measured reason as INC-2a.2. -/
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
  sorry

end libcrux_iot_ml_kem.IndCpaFc
