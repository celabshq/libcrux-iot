-- Hand-written stubs for symbols that are missing in Aeneas or rust-core-models
import Aeneas
import CoreModels
import HacspecSha3
import HacspecMlKem.Missing

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result

noncomputable section

namespace CoreModels.core

def num.I16.wrapping_neg (x : Std.I16) : Result Std.I16 :=
  rust_primitives.arithmetic.wrapping_sub_i16 (0#i16) x

def cmRangeUsizeToAeneas (r : ops.range.Range Aeneas.Std.Usize) :
    Aeneas.Std.core.ops.range.Range Aeneas.Std.Usize :=
  { start := r.start, «end» := r.«end» }

end CoreModels.core

namespace CoreModels.core.slice.iter.ChunksExact.Insts

@[reducible] def CoreIterTraitsIteratorIteratorSharedASlice
    (T : Type) :
    CoreModels.core.iter.traits.iterator.Iterator
      (CoreModels.core.slice.iter.ChunksExact T) (Aeneas.Std.Slice T) :=
  { next := @CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next T }

def CoreIterTraitsIteratorIteratorSharedASlice.enumerate
    {T : Type} (it : CoreModels.core.slice.iter.ChunksExact T) :
    Aeneas.Std.Result
      (CoreModels.core.iter.adapters.enumerate.Enumerate
        (CoreModels.core.slice.iter.ChunksExact T)) :=
  Aeneas.Std.Result.ok { iter := it, count := 0#usize }

end CoreModels.core.slice.iter.ChunksExact.Insts

/-! ## `libcrux_secrets.*` integer-cast + classify/declassify stubs.
    `libcrux_secrets`-functions are not part of the extraction; we map
    them to identity functions on the underlying scalar types. -/

namespace libcrux_secrets.traits.Classify.Blanket
def classify {T : Type} (a : T) : Aeneas.Std.Result T := ok a
end libcrux_secrets.traits.Classify.Blanket

namespace libcrux_secrets.traits.Declassify.Blanket
def declassify {T : Type} (a : T) : Aeneas.Std.Result T := ok a
end libcrux_secrets.traits.Declassify.Blanket

namespace libcrux_secrets

/-! Cast stubs written in the upstream `declassify → cast → classify`
    shape so that downstream proofs can unfold the chain. -/

def I16.Insts.Libcrux_secretsIntCastOps.as_i16 (x : Std.I16) : Result Std.I16 := do
  let i ← traits.Declassify.Blanket.declassify x
  traits.Classify.Blanket.classify i

def I16.Insts.Libcrux_secretsIntCastOps.as_i32 (x : Std.I16) : Result Std.I32 := do
  let i ← traits.Declassify.Blanket.declassify x
  let i1 ← lift (Std.IScalar.cast .I32 i)
  traits.Classify.Blanket.classify i1

def I16.Insts.Libcrux_secretsIntCastOps.as_u16 (x : Std.I16) : Result Std.U16 := do
  let i ← traits.Declassify.Blanket.declassify x
  let i1 ← lift (Std.IScalar.hcast .U16 i)
  traits.Classify.Blanket.classify i1

def I16.Insts.Libcrux_secretsIntCastOps.as_u8 (x : Std.I16) : Result Std.U8 := do
  let i ← traits.Declassify.Blanket.declassify x
  let i1 ← lift (Std.IScalar.hcast .U8 i)
  traits.Classify.Blanket.classify i1

def I32.Insts.Libcrux_secretsIntCastOps.as_i16 (x : Std.I32) : Result Std.I16 := do
  let i ← traits.Declassify.Blanket.declassify x
  let i1 ← lift (Std.IScalar.cast .I16 i)
  traits.Classify.Blanket.classify i1

def U8.Insts.Libcrux_secretsIntCastOps.as_i16 (x : Std.U8) : Result Std.I16 := do
  let i ← traits.Declassify.Blanket.declassify x
  let i1 ← lift (Std.UScalar.hcast .I16 i)
  traits.Classify.Blanket.classify i1

def U16.Insts.Libcrux_secretsIntCastOps.as_i16 (x : Std.U16) : Result Std.I16 := do
  let i ← traits.Declassify.Blanket.declassify x
  let i1 ← lift (Std.UScalar.hcast .I16 i)
  traits.Classify.Blanket.classify i1

def U16.Insts.Libcrux_secretsIntCastOps.as_u64 (x : Std.U16) : Result Std.U64 := do
  let i ← traits.Declassify.Blanket.declassify x
  let i1 := Std.UScalar.cast .U64 i
  traits.Classify.Blanket.classify i1

def U32.Insts.Libcrux_secretsIntCastOps.as_i16 (x : Std.U32) : Result Std.I16 := do
  let i ← traits.Declassify.Blanket.declassify x
  let i1 ← lift (Std.UScalar.hcast .I16 i)
  traits.Classify.Blanket.classify i1

def U32.Insts.Libcrux_secretsIntCastOps.as_i32 (x : Std.U32) : Result Std.I32 := do
  let i ← traits.Declassify.Blanket.declassify x
  let i1 ← lift (Std.UScalar.hcast .I32 i)
  traits.Classify.Blanket.classify i1

def U64.Insts.Libcrux_secretsIntCastOps.as_u32 (x : Std.U64) : Result Std.U32 := do
  let i ← traits.Declassify.Blanket.declassify x
  let i1 := Std.UScalar.cast .U32 i
  traits.Classify.Blanket.classify i1

/-- `Scalar` marker trait (carries no methods we use); `PUnit` for shape. -/
@[reducible] def traits.Scalar (_Self : Type) : Type := PUnit
@[reducible] def U8.Insts.Libcrux_secretsTraitsScalar : traits.Scalar Std.U8 := PUnit.unit

/-- `classify_ref` on a shared slice — no-op (takes the marker + slice). -/
def SharedASlice.Insts.Libcrux_secretsTraitsClassifyRefSharedASlice.classify_ref
    {T : Type} (_inst : traits.Scalar T) (s : Aeneas.Std.Slice T) :
    Aeneas.Std.Result (Aeneas.Std.Slice T) := ok s

end libcrux_secrets

end
