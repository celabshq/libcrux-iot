/-
  # `SerializeFc.lean` — INC-1 obligation stubs for the (de)serialize layer.

  SCAFFOLD ONLY. Every theorem below is `sorry`ed: these are the OBLIGATIONS the
  driver will dispatch a PROVER to close, not results. They are authored by the
  HELPER as a *low-distance binding* to the EXISTING `HacspecMlKem` model (skill
  §0.2) — nothing here invents a spec. The statements are NOT frozen until the
  PRINCIPAL approves them; the driver locks each signature at that point.

  Shape follows the tree's established convention (see `Matrix/ComputeAsPlusE.lean`,
  `Serialize.lean`): an mvcgen Triple whose post equates the hacspec model applied
  to `lift`ed inputs with `.ok` of the `lift`ed impl result.

      ⦃ ⌜pre⌝ ⦄  <impl call>  ⦃ ⇓ p => ⌜ <hacspec> (lift args…) = .ok (lift p…) ⌝ ⦄

  ## Scope of THIS file

  Only the bindings where the impl function and a hacspec function correspond
  1:1, so the statement is mechanical. Deliberately NOT scaffolded here, because
  each needs a PRINCIPAL decision rather than a transcription — see the campaign
  STATE.md (P7):

  * `compress_then_serialize_ring_element_u` / `deserialize_then_decompress_ring_element_u`
    — the impl works on ONE ring element; the hacspec `compress_then_serialize_u` /
    `deserialize_then_decompress_u` work on the WHOLE rank-K vector. Binding the
    per-element impl needs either a spec-side per-element projection or a
    whole-vector statement assembled from K impl calls. That is a modelling
    choice, not a transcription.
  * `compress_then_serialize_{4,5,10,11}` / `deserialize_then_decompress_{4,5,10,11}`
    — impl-internal specializations of a `d`-parametric operation. No named
    hacspec counterpart; the natural binding is
    `byte_encode_into (compress_d · d) ` / `byte_decode` at that `d`, i.e. step
    lemmas feeding the `_u`/`_v` apexes above. Their statement shape should be
    fixed together with the `_u` decision so the two compose.
  * `to_unsigned_field_modulus` — an impl-internal helper with no spec image.
-/

import LibcruxIotMlKem.Spec.Lift
import LibcruxIotMlKem.Serialize

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace libcrux_iot_ml_kem.SerializeFc

open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec.Lift
open libcrux_iot_ml_kem.Spec

/-! ## Message (de)serialization — `d = 1`, exact 1:1 with the hacspec model. -/

/-- L5.1 — `serialize.deserialize_then_decompress_message`.

    FIPS-203 message decode: 32 bytes → 256 coefficients, each bit `b` mapped to
    `Decompress_1(b)`. The hacspec counterpart takes the same fixed-size 32-byte
    array and returns the ring element directly, so the binding is exact: no
    length side conditions, no chunk indexing. -/
@[spec]
theorem deserialize_then_decompress_message_fc
    (serialized : Std.Array Std.U8 32#usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_message
      (vectortraitsOperationsInst := portable_ops_inst)
      serialized re
    ⦃ ⇓ p => ⌜ hacspec_ml_kem.serialize.deserialize_then_decompress_message serialized
                = .ok (lift_poly p) ⌝ ⦄ := by
  sorry

/-- L5.2 — `serialize.compress_then_serialize_message`.

    The encode direction of L5.1: `Compress_1` each coefficient, pack 256 bits
    into 32 bytes. The impl writes into a caller-provided `serialized` slice and
    threads a `scratch` vector, returning both; the hacspec returns a fresh
    32-byte array. The post therefore constrains the RETURNED slice `p.1`, and
    requires it to have message length. `scratch` is workspace and is
    deliberately unconstrained. -/
@[spec]
theorem compress_then_serialize_message_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (serialized : Slice Std.U8)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_len : serialized.length = 32) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.compress_then_serialize_message
      (vectortraitsOperationsInst := portable_ops_inst)
      re serialized scratch
    ⦃ ⇓ p => ⌜ ∃ out : Std.Array Std.U8 32#usize,
                  hacspec_ml_kem.serialize.compress_then_serialize_message (lift_poly re)
                    = .ok out
                  ∧ p.1.length = 32
                  ∧ ∀ ℓ : Nat, ℓ < 32 → p.1.val[ℓ]! = out.val[ℓ]! ⌝ ⦄ := by
  sorry

/-! ## Ciphertext component `v` — `d = dv`, exact 1:1 with the hacspec model. -/

/-- L5.3 — `serialize.deserialize_then_decompress_ring_element_v`.

    `ByteDecode_dv` then `Decompress_dv` over one ring element. The hacspec
    counterpart takes the same `(serialized, dv)` pair and returns the ring
    element, so the binding is exact. The impl's `K` is a rank parameter that does
    not appear in the spec side. -/
@[spec]
theorem deserialize_then_decompress_ring_element_v_fc
    (K V_COMPRESSION_FACTOR : Std.Usize)
    (serialized : Slice Std.U8)
    (output : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_v
      (vectortraitsOperationsInst := portable_ops_inst)
      K V_COMPRESSION_FACTOR serialized output
    ⦃ ⇓ p => ⌜ hacspec_ml_kem.serialize.deserialize_then_decompress_v
                  serialized V_COMPRESSION_FACTOR
                = .ok (lift_poly p) ⌝ ⦄ := by
  sorry

/-- L5.4 — `serialize.compress_then_serialize_ring_element_v`.

    The encode direction of L5.3: `Compress_dv` then `ByteEncode_dv`. The impl
    writes into the caller's `out` slice and threads `scratch`; the hacspec
    returns a fresh `Array U8 C2_LEN`. The post therefore compares the returned
    slice bytewise against the spec array, exactly as L5.2 does for the message.
    `V_SIZE` on the spec side is the impl's `C2_LEN`. -/
@[spec]
theorem compress_then_serialize_ring_element_v_fc
    (K V_COMPRESSION_FACTOR C2_LEN : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_len : out.length = C2_LEN.val) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_v
      (vectortraitsOperationsInst := portable_ops_inst)
      K V_COMPRESSION_FACTOR C2_LEN re out scratch
    ⦃ ⇓ p => ⌜ ∃ enc : Std.Array Std.U8 C2_LEN,
                  hacspec_ml_kem.serialize.compress_then_serialize_v
                      C2_LEN (lift_poly re) V_COMPRESSION_FACTOR
                    = .ok enc
                  ∧ p.1.length = C2_LEN.val
                  ∧ ∀ ℓ : Nat, ℓ < C2_LEN.val → p.1.val[ℓ]! = enc.val[ℓ]! ⌝ ⦄ := by
  sorry

/-! ## Public-key deserialization — exact 1:1 with the hacspec model. -/

/-- L5.5 — `serialize.deserialize_ring_elements_reduced`.

    Rank-K public-key decode: K consecutive 384-byte chunks, each `ByteDecode_12`
    then reduced to canonical residues. This is the vector-level apex that
    assembles `Serialize.deserialize_to_reduced_ring_element_fc` (currently the A2
    axiom) K times. The impl threads a caller-provided `deserialized_pk` slice and
    returns it; the spec returns a fresh rank-K array, so the impl result is
    compared through `lift_vec_slice`. -/
@[spec]
theorem deserialize_ring_elements_reduced_fc
    (K : Std.Usize)
    (public_key : Slice Std.U8)
    (deserialized_pk : Slice
        (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (h_pk_len : public_key.length = K.val * 384)
    (h_out_len : deserialized_pk.length = K.val) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_ring_elements_reduced
      (vectortraitsOperationsInst := portable_ops_inst)
      K public_key deserialized_pk
    ⦃ ⇓ p => ⌜ p.length = K.val
                ∧ hacspec_ml_kem.serialize.deserialize_ring_elements_reduced K public_key
                  = .ok (lift_vec_slice p K) ⌝ ⦄ := by
  sorry

/-! ## Uncompressed ring elements — `d = 12`, no compression step.

    `BITS_PER_COEFFICIENT = 12`, so these are plain `ByteEncode_12` / `ByteDecode_12`
    with no `Compress`/`Decompress` in the chain. The slice-shaped hacspec variants
    (`byte_encode_into`, `byte_decode_dyn`) match the impl's slice plumbing directly,
    so no container conversion is needed. -/

/-- L5.6 — `serialize.serialize_uncompressed_ring_element` (= `ByteEncode_12`).

    The impl returns `(scratch', serialized')`; the byte content of interest is
    `p.2`, which `byte_encode_into` produces from the same `out` slice. -/
@[spec]
theorem serialize_uncompressed_ring_element_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (serialized : Slice Std.U8)
    (h_len : serialized.length = 384) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.serialize_uncompressed_ring_element
      (vectortraitsOperationsInst := portable_ops_inst)
      re scratch serialized
    ⦃ ⇓ p => ⌜ hacspec_ml_kem.serialize.byte_encode_into (lift_poly re) 12#usize serialized
                = .ok p.2 ⌝ ⦄ := by
  sorry

/-- L5.7 — `serialize.deserialize_to_uncompressed_ring_element` (= `ByteDecode_12`).

    Sibling of L5.6 and of the A2 axiom `deserialize_to_reduced_ring_element_fc`;
    the difference from A2 is that this one does NOT apply the trailing
    `cond_subtract_3329` reduction, so no canonicality bound is claimed. -/
@[spec]
theorem deserialize_to_uncompressed_ring_element_fc
    (serialized : Slice Std.U8)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_len : serialized.length = 384) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_to_uncompressed_ring_element
      (vectortraitsOperationsInst := portable_ops_inst)
      serialized re
    ⦃ ⇓ p => ⌜ hacspec_ml_kem.serialize.byte_decode_dyn serialized 12#usize
                = .ok (lift_poly p) ⌝ ⦄ := by
  sorry

end libcrux_iot_ml_kem.SerializeFc
