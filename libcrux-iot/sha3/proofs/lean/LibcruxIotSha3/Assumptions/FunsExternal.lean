-- External function definitions for `libcrux-iot-sha3` (hand-written).
-- The shared `CoreModels.core.*` helpers (mutable-index selectors, `unwrap`,
-- `copy_from_slice`, `TryFromSliceError` `Debug`) live in the `HacspecSha3`
-- spec's `FunsExternal` and are reused from there (defining them here too would
-- clash when a proof file imports both). Only the `libcrux_secrets` helpers,
-- which the spec does not provide, are defined here.
import Aeneas
import CoreModels
import HacspecSha3
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

end libcrux_secrets
end
