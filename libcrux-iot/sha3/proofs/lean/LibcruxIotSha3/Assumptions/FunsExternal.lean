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

end libcrux_secrets



/-- `hax_lib::loop_invariant!` marker. cargo-hax 0.4 emits calls to
    `hax_lib._internal_loop_invariant`, but neither hax-lean v0.3.12 nor the
    generated template declares it. The marker carries no computational content
    -- it is a proof hint -- so a no-op model is sound. Drop this once hax-lean
    ships the symbol. -/
axiom hax_lib._internal_loop_invariant
  {Into Inv State : Type} : Into → Inv → State → RustM Unit

end
