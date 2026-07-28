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
open Result ControlFlow Error
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
def classify {T : Type} (a : T) : Aeneas.Std.Result T := ok a
end libcrux_secrets.traits.Classify.Blanket

namespace libcrux_secrets

def U32.Insts.Libcrux_secretsIntCastOps.as_u64 (x : U32) : Result U64 :=
  ok (UScalar.cast .U64 x)

def U64.Insts.Libcrux_secretsIntCastOps.as_u32 (x : U64) : Result U32 :=
  ok (UScalar.cast .U32 x)

end libcrux_secrets

end
