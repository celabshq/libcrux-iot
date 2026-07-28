-- External function definitions for `libcrux-iot-sha3` (hand-written).
-- Ported from the former `Missing.lean`: helpers the `-core-models-lib`
-- extraction references but that aeneas cannot generate on its own.
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

namespace CoreModels.core

/-! Helpers used by the `-core-models-lib` extraction of `libcrux-iot-sha3`
that aren't covered by `HacspecSha3.Missing` (which sets up the
slice/range/result/copy/Debug-`TryFromSliceError` machinery shared with
the upstream spec). -/

/-! Bridge from `RangeTo Usize` to Aeneas's native `SliceIndex` instance.
    Mirrors the `RangeUsize` / `RangeFromUsize` versions in
    `HacspecSha3.Missing`. -/

def ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice (T : Type) :
    Aeneas.Std.core.slice.index.SliceIndex
      (CoreModels.core.ops.range.RangeTo Usize) (Slice T) (Slice T) :=
  let toAeneas (r : CoreModels.core.ops.range.RangeTo Usize) :
      Aeneas.Std.core.ops.range.RangeTo Usize :=
    { «end» := r.«end» }
  { sealedInst := {}
    get := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeToUsizeSlice.get (toAeneas r) s
    get_mut := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeToUsizeSlice.get_mut (toAeneas r) s
    get_unchecked := fun _ _ => Result.fail Error.undef
    get_unchecked_mut := fun _ _ => Result.fail Error.undef
    index := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeToUsizeSlice.index (toAeneas r) s
    index_mut := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeToUsizeSlice.index_mut (toAeneas r) s }

/-! Trivial `Display` / `Debug` instances for `Usize` and `Array T N`,
    plus a `fmt.Arguments.new` stub. These are referenced by the
    extracted `keccak` panic-message format strings. -/

@[reducible] def Usize.Insts.CoreFmtDisplay : CoreModels.core.fmt.Display Usize :=
  { fmt := fun _ f => ok (CoreModels.core.result.Result.Ok (), f) }

@[reducible] def Usize.Insts.CoreFmtDebug : CoreModels.core.fmt.Debug Usize :=
  { dbg_fmt := fun _ f => ok (CoreModels.core.result.Result.Ok (), f) }

@[reducible] def Array.Insts.CoreFmtDebug
  {T : Type} (_N : Usize) (_elem : CoreModels.core.fmt.Debug T) :
  CoreModels.core.fmt.Debug (Array T _N) :=
  { dbg_fmt := fun _ f => ok (CoreModels.core.result.Result.Ok (), f) }

def fmt.Arguments.new
  {N M : Usize}
  (_ : Array U8 N)
  (_ : Array CoreModels.core.fmt.rt.Argument M) :
  Result CoreModels.core.fmt.Arguments :=
  ok ()

end CoreModels.core

/-! ## `libcrux_secrets` helpers used by `libcrux-iot-sha3`. -/

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
