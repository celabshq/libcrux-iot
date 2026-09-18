-- External function definitions for `libcrux-iot-sha3` (hand-written).
-- CoreModels supplies every model the extraction references, so what is left
-- here is the `libcrux_secrets` helpers, which no spec provides.
--
-- This file is also where the spec package enters the generated extraction's import
-- tree: hax emits `Extraction/FunsExternal.lean` as a one-line shim onto this file
-- and never adds spec imports of its own, so the `#[ensures]` clauses'
-- `hacspec_sha3_pedantic::bytes::*` are in scope in `Extraction/Specs.lean` only
-- because they are imported here.
import Aeneas
import CoreModels
import HacspecSha3Pedantic
import LibcruxIotSha3.Extraction.Types
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open libcrux_iot_sha3

noncomputable section

/-! `libcrux_secrets` helpers used by `libcrux-iot-sha3`. -/

namespace libcrux_secrets.traits.Classify.Blanket
def classify {T : Type} (a : T) : Aeneas.Std.RustM T := ok a
end libcrux_secrets.traits.Classify.Blanket

namespace libcrux_secrets

def U32.Insts.Libcrux_secretsIntCastOps.as_u64 (x : U32) : RustM U64 :=
  ok (UScalar.cast .U64 x)

def U64.Insts.Libcrux_secretsIntCastOps.as_u32 (x : U64) : RustM U32 :=
  ok (UScalar.cast .U32 x)

/-! EXPERIMENT: `declassify_ref` on a shared SLICE, needed once a spec names the
    hacspec (which takes `&[u8]`, not `&[U8]`). No-op identity, mirroring
    ml-dsa's `SharedAT` variant. -/

@[reducible] def traits.Scalar (_Self : Type) : Type := PUnit
@[reducible] def U8.Insts.Libcrux_secretsTraitsScalar : traits.Scalar Std.U8 :=
  PUnit.unit

def SharedASlice.Insts.Libcrux_secretsTraitsDeclassifyRefSharedASlice.declassify_ref
    {T : Type} (_inst : traits.Scalar T) (a : Aeneas.Std.Slice T) :
    Aeneas.Std.RustM (Aeneas.Std.Slice T) := ok a

/-- `declassify` by value through the blanket `impl<T> Declassify for T` (public
    integers: `U8 = u8`), used by the `shake128`/`shake256` contracts on their
    `[U8; BYTES]` result. No-op identity, like `declassify_ref` above. -/
def traits.Declassify.Blanket.declassify {T : Type} (x : T) : Aeneas.Std.RustM T := ok x

end libcrux_secrets
end

