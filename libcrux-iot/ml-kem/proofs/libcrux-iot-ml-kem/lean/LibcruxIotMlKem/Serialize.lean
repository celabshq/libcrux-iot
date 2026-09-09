/-
  # `Serialize.lean` — deferred leaf FC axiom for public-key deserialization.

  We verify the matrix operations without verifying the underlying
  `serialize.deserialize_to_reduced_ring_element` ring-element decoding.
  This axiom pins the contract: each 384-byte chunk of the public key
  deserialises to the `i`-th ring element of
  `Spec.t_as_ntt_from_public_key_pure` with canonical coefficients.
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

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace libcrux_iot_ml_kem.Serialize
open libcrux_iot_ml_kem.InvertNtt libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.NttMultiply libcrux_iot_ml_kem.Polynomial.PolyOpsFc libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec

/-- 16-iteration loop over 24-byte sub-chunks of `serialized`
    (one `BYTES_PER_RING_ELEMENT = 384` byte ring-element). Each chunk
    extracts 16 packed 12-bit coefficients via `deserialize_12`, then
    `cond_subtract_3329` produces canonical residues [0, 3328]. -/
@[spec]
axiom deserialize_to_reduced_ring_element_fc
    (public_key : Slice Std.U8) (K : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (i : Std.Usize)
    (h_pk_len : public_key.length = K.val * 384)
    (h_i : i.val < K.val)
    (chunk_bytes : Slice Std.U8)
    (h_chunk_len : chunk_bytes.length = 384)
    (h_chunk_eq : ∀ ℓ : Nat, ℓ < 384 →
        chunk_bytes.val[ℓ]! = public_key.val[i.val * 384 + ℓ]!) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_to_reduced_ring_element
      (vectortraitsOperationsInst := portable_ops_inst)
      chunk_bytes re
    ⦃ ⇓ p => ⌜ lift_poly p = (lift_t_as_ntt_from_public_key public_key K).val[i.val]!
                ∧ (∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
                    ((p.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 3328) ⌝ ⦄

end libcrux_iot_ml_kem.Serialize