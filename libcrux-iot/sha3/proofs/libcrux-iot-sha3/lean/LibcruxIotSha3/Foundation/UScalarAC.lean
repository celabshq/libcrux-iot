/-
  Project-local `Std.Associative` / `Std.Commutative`
  instances for `Std.UScalar.xor` / `and` / `or`.

  Aeneas registers projection laws (`UScalar.bv_xor` etc.) at
  `Aeneas/Std/Scalar/Bitwise.lean:274–281` but does **not** declare AC
  instances on `UScalar` itself, so `grind` cannot rotate
  `(a ^^^ b ^^^ c : Std.U64)` past `bv_xor`'s reach. We add those
  instances locally.
-/
import Aeneas.Std.Scalar.Bitwise

open Aeneas Aeneas.Std

instance {ty : Std.UScalarTy} : Std.Associative (α := Std.UScalar ty) (· ^^^ ·) :=
  ⟨fun a b c => by
    apply Std.UScalar.eq_equiv_bv_eq _ _ |>.mpr
    simp [Std.UScalar.bv_xor, BitVec.xor_assoc]⟩

instance {ty : Std.UScalarTy} : Std.Commutative (α := Std.UScalar ty) (· ^^^ ·) :=
  ⟨fun a b => by
    apply Std.UScalar.eq_equiv_bv_eq _ _ |>.mpr
    simp [Std.UScalar.bv_xor, BitVec.xor_comm]⟩

instance {ty : Std.UScalarTy} : Std.Associative (α := Std.UScalar ty) (· &&& ·) :=
  ⟨fun a b c => by
    apply Std.UScalar.eq_equiv_bv_eq _ _ |>.mpr
    simp [Std.UScalar.bv_and, BitVec.and_assoc]⟩

instance {ty : Std.UScalarTy} : Std.Commutative (α := Std.UScalar ty) (· &&& ·) :=
  ⟨fun a b => by
    apply Std.UScalar.eq_equiv_bv_eq _ _ |>.mpr
    simp [Std.UScalar.bv_and, BitVec.and_comm]⟩

instance {ty : Std.UScalarTy} : Std.Associative (α := Std.UScalar ty) (· ||| ·) :=
  ⟨fun a b c => by
    apply Std.UScalar.eq_equiv_bv_eq _ _ |>.mpr
    simp [Std.UScalar.bv_or, BitVec.or_assoc]⟩

instance {ty : Std.UScalarTy} : Std.Commutative (α := Std.UScalar ty) (· ||| ·) :=
  ⟨fun a b => by
    apply Std.UScalar.eq_equiv_bv_eq _ _ |>.mpr
    simp [Std.UScalar.bv_or, BitVec.or_comm]⟩
