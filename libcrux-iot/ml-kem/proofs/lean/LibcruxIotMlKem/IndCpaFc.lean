/-
  # `IndCpaFc.lean` — INC-2 lane 2a obligations for the `ind_cpa` (k-PKE) layer.

  SCAFFOLD. The theorem below is `sorry`ed: it is an OBLIGATION the driver dispatches a
  PROVER to close, not a result. Authored by the HELPER as a *low-distance binding* to the
  EXISTING `hacspec_ml_kem` model — nothing here invents a spec.

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

-- Same open-set as `SerializeFc.lean`: the Triple notation `⦃ ⌜_⌝ ⦄ … ⦃ ⇓_ => ⌜_⌝ ⦄`
-- comes from `Std.Do`, and omitting it fails at the FIRST `⌜` with a bare
-- "unexpected token" — which is what a sketched statement looks like when it has never
-- been elaborated (readiness map A4).
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem
open libcrux_iot_ml_kem.Spec
open libcrux_iot_ml_kem.Spec.Lift

namespace libcrux_iot_ml_kem.IndCpaFc

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
  sorry

end libcrux_iot_ml_kem.IndCpaFc
