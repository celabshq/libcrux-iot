/-
  # Comparator solution module

  [`comparator`](https://github.com/leanprover/comparator) is a trustworthy judge for
  Lean proofs: given a *challenge* module whose theorems are stated with `sorry`, and a
  *solution* module restating the same theorems with proofs, it checks (from a fresh
  `lean4export` of both, replayed through the kernel) that every listed solution theorem
  has exactly the challenge's statement and uses only the permitted axioms. This guards
  against a proof, human- or AI-written, that proves a subtly different statement.

  The challenge here is hax's own output: the generated
  `Extraction/ProofObligations.lean` states one `<fn>.spec.proof : <fn>.spec …` per Rust
  contract, each `:= by sorry`. That file is kept on disk but out of the build. This
  module is the solution: it restates, under the challenge's exact names and binders,
  the obligations that `Verification/ProofObligations.lean` discharges, and proves each
  by that discharge. `comparator.json` lists them; `./comparator.sh` runs the check.

  This module must NOT import `Extraction.ProofObligations` (the challenge), and the
  binder lists must be copied verbatim from it.
-/
import LibcruxIotSha3.Verification.ProofObligations

open CoreModels Aeneas Aeneas.Std Std.Do

namespace libcrux_iot_sha3

theorem sha224_ema.spec.proof (digest : Slice Std.U8) (payload : Slice Std.U8) :
    sha224_ema.spec digest payload :=
  Verification.sha224_ema_spec_proof digest payload

theorem sha256_ema.spec.proof (digest : Slice Std.U8) (payload : Slice Std.U8) :
    sha256_ema.spec digest payload :=
  Verification.sha256_ema_spec_proof digest payload

theorem sha384_ema.spec.proof (digest : Slice Std.U8) (payload : Slice Std.U8) :
    sha384_ema.spec digest payload :=
  Verification.sha384_ema_spec_proof digest payload

theorem sha512_ema.spec.proof (digest : Slice Std.U8) (payload : Slice Std.U8) :
    sha512_ema.spec digest payload :=
  Verification.sha512_ema_spec_proof digest payload

theorem shake128.spec.proof (BYTES : Std.Usize) (data : Slice Std.U8) :
    shake128.spec BYTES data :=
  Verification.shake128_spec_proof BYTES data

theorem shake256.spec.proof (BYTES : Std.Usize) (data : Slice Std.U8) :
    shake256.spec BYTES data :=
  Verification.shake256_spec_proof BYTES data

set_option linter.dupNamespace false in  -- the generated name repeats `keccak`
theorem keccak.keccak.spec.proof (RATE : Std.Usize) (DELIM : Std.U8)
    (data : Slice Std.U8) (out : Slice Std.U8) : keccak.keccak.spec RATE DELIM data out :=
  Verification.keccak_spec_proof RATE DELIM data out

end libcrux_iot_sha3
