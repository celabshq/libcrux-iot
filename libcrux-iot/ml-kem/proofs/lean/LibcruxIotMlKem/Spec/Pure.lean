/-
  # `Spec/Pure.lean` — Open Question I.7 resolution.

  The hacspec ML-KEM extraction (`HacspecMlKem.Extraction.Funs`) wraps
  every spec function in the Aeneas `Result` monad, even when the
  body is mathematically pure (no panic / divergence). The bit-side
  intermediate spec (`BitMlKem.Spec`) operates on `MontPoly =
  Vector (ZMod 3329) 256`, which is genuinely pure.

  Layer M.4 alg-equiv lemmas state equations of the form
    `bit_<op> (lift hacspec_input) = lift (Spec.<op>_pure hacspec_input)`
  where `Spec.<op>_pure` is the `Result`-stripped pure projection of
  the hacspec spec. This file defines those `_pure` aliases.

  arch plan §F.2 option (b): each alias is defined by pattern
  match on the `Result`. The companion **pure-projection side lemmas**
  of the form `Spec.<op> args = .ok (Spec.<op>_pure args)` pin the
  impl's `.ok` value to the projected `_pure` value. They are the
  equational input to `libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq` (the index-wise spec
  lifting `from_fn`) and to downstream M.2 commute lemmas — NOT
  standalone "panic-freedom" facts.

  ## Scope

  - Scalar `parameters.FieldElement.{add,sub,mul,neg}` get `_pure`
    aliases — they are used pointwise inside every `polynomial.*`
    closure in the hacspec extraction.
  - The three poly-level hacspec wrappers used by M.4 easy cluster
    (`polynomial.add_to_ring_element`, `polynomial.poly_barrett_reduce`,
    `polynomial.subtract_reduce`) get `_pure` aliases.

  ## Discipline

  - All `_pure` defs are `noncomputable` because the match-on-Result
    extraction does not reduce by `decide` for arbitrary inputs;
    callers reason about them via the side lemmas (TODO) or by
    direct `simp only [<op>_pure]` rewriting through M.4 proofs.
  - No Mathlib imports needed; this file lives above the M.1 barrier
    inheriting `ZMod 3329` transitively via `BitMlKem.Spec`.
-/
import LibcruxIotMlKem.Spec
import LibcruxIotMlKem.Util.CreateI

namespace libcrux_iot_ml_kem.Spec.Pure
open CoreModels Aeneas Aeneas.Std
open hacspec_ml_kem

/-! ## Default `FieldElement` (used as fall-through in `_pure` match). -/

/-- Canonical default for `parameters.FieldElement` — the zero element.
    Used as the fall-through branch in the `match` definitions below;
    chosen to be in canonical range so the lift through `zmodOfFE`
    gives `0 : ZMod 3329`. -/
def defaultFE : parameters.FieldElement := { val := (0#u16 : Std.U16) }

instance : Inhabited parameters.FieldElement := ⟨defaultFE⟩

/-! ## Scalar `_pure` aliases. -/

/-- Pure projection of `parameters.FieldElement.add`. The hacspec body
    computes `(self.val + other.val) % q` via U32 lifts; this `_pure`
    extracts the `.ok` value (see `FieldElement.add_eq_ok` below for
    the pure-projection side lemma pinning the result). -/
noncomputable def FieldElement.add_pure
    (self other : parameters.FieldElement) : parameters.FieldElement :=
  match parameters.FieldElement.add self other with
  | .ok r => r
  | _ => defaultFE

/-- Pure projection of `parameters.FieldElement.sub`. Mirrors
    `add_pure`; hacspec body computes `(self.val + q - other.val) % q`. -/
noncomputable def FieldElement.sub_pure
    (self other : parameters.FieldElement) : parameters.FieldElement :=
  match parameters.FieldElement.sub self other with
  | .ok r => r
  | _ => defaultFE

/-- Pure projection of `parameters.FieldElement.mul`. -/
noncomputable def FieldElement.mul_pure
    (self other : parameters.FieldElement) : parameters.FieldElement :=
  match parameters.FieldElement.mul self other with
  | .ok r => r
  | _ => defaultFE

/-- Pure projection of `parameters.FieldElement.neg`. -/
noncomputable def FieldElement.neg_pure
    (self : parameters.FieldElement) : parameters.FieldElement :=
  match parameters.FieldElement.neg self with
  | .ok r => r
  | _ => defaultFE

/-! ## Poly-level `_pure` aliases.

    These wrap the 256-coefficient Aeneas-`Array` results into a pure
    `SpecPoly = Vector parameters.FieldElement 256` via per-lane
    extraction. Downstream lifting through `libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq`
    pins each lane to its per-element `_pure` value; see the
    `polynomial.<op>_eq_ok` pure-projection side lemmas at the end of
    this file. -/

/-- Pure projection of `polynomial.add_to_ring_element`. -/
noncomputable def polynomial.add_to_ring_element_pure
    (lhs rhs : Std.Array parameters.FieldElement 256#usize) :
    Std.Array parameters.FieldElement 256#usize :=
  match hacspec_ml_kem.polynomial.add_to_ring_element lhs rhs with
  | .ok r => r
  | _ => lhs

/-- Pure projection of `polynomial.poly_barrett_reduce`. -/
noncomputable def polynomial.poly_barrett_reduce_pure
    (p : Std.Array parameters.FieldElement 256#usize) :
    Std.Array parameters.FieldElement 256#usize :=
  match hacspec_ml_kem.polynomial.poly_barrett_reduce p with
  | .ok r => r
  | _ => p

/-- Pure projection of `polynomial.subtract_reduce`. -/
noncomputable def polynomial.subtract_reduce_pure
    (a b : Std.Array parameters.FieldElement 256#usize) :
    Std.Array parameters.FieldElement 256#usize :=
  match hacspec_ml_kem.polynomial.subtract_reduce a b with
  | .ok r => r
  | _ => a

/-! ## FE-primitive pure-projection side lemmas.

    `add_eq_ok` and `mul_eq_ok` are UNCONDITIONALLY true because U32
    widening prevents overflow in both cases (`a.val + b.val < 2^17`,
    `a.val * b.val ≤ (2^16 - 1)² < 2^32`).

    `sub_eq_ok` and `neg_eq_ok` require a CANONICITY PRECONDITION
    `Canonical a := a.val.val < q`. The Aeneas extraction dropped the
    Rust source's `#[refine(val < FIELD_MODULUS)]` refinement on
    `parameters.FieldElement::new` (see `specs/ml-kem/src/parameters.rs:319`),
    leaving any `U16` admissible. Counterexamples for arbitrary U16
    (verified via `#eval`):
    * `sub ⟨0#u16⟩ ⟨65535#u16⟩ = .fail` (U32 underflow after `+ q`).
    * `neg ⟨65535#u16⟩ = .fail` (U16 underflow `q - val`, no widening).

    Audit of the 3 call-sites of `sub`/`neg` in the
    hacspec extraction confirms ALL callers feed canonical inputs:
    * `ntt.butterfly` and `invert_ntt.inv_butterfly` — inputs `a, b`
      assumed canonical by caller; `mul`'s output is always canonical
      by construction.
    * `ntt.base_case_multiply_n` — `neg fe` where `fe` is from the
      compile-time zetas table (all canonical).

    Canonicity is also the natural invariant of the bit-side lifts:
    `feOfZMod : ZMod 3329 → FieldElement` produces canonical FEs by
    construction (the lift packs `z.val < 3329 < 2^16` into a U16).

    Canonicity preservation lemmas (`Canonical_add_pure`,
    `Canonical_mul_pure`, etc.) are deferred to .2 when the
    poly-wrapper side lemmas need them; the U16-cast simp residue
    requires non-trivial unfolding that's better tackled with
    downstream context. -/

/-- A `parameters.FieldElement` is canonical iff its underlying U16
    holds a value strictly below the field modulus `q = 3329`. This
    is the invariant the Rust source maintains via
    `#[refine(val < FIELD_MODULUS)]` on `FieldElement::new` — the
    Aeneas extraction drops the refinement, so we carry canonicity
    as an explicit predicate.

    The bit-side lift `feOfZMod` produces canonical FEs by
    construction; downstream wrappers (`butterfly`, etc.) take
    canonical inputs and produce canonical outputs. -/
def Canonical (fe : parameters.FieldElement) : Prop :=
  fe.val.val < parameters.FIELD_MODULUS.val

private theorem uscalar_rem_ok_U32 (z m : Std.U32) (hm : m.val ≠ 0) :
    ∃ w : Std.U32, (z % m : Result Std.U32) = .ok w ∧ w.val = z.val % m.val := by
  have heq : (z % m : Result Std.U32) = Std.UScalar.rem z m := rfl
  unfold Std.UScalar.rem at heq
  simp [hm] at heq
  refine ⟨_, heq, ?_⟩
  show (BitVec.umod z.bv m.bv).toNat = z.val % m.val
  unfold BitVec.umod
  simp only [BitVec.toNat_ofNatLT]
  rfl

/-- U16 variant of `uscalar_rem_ok_U32` — used by `neg_eq_ok` whose
    `% q` step is at U16 width (no widening). -/
private theorem uscalar_rem_ok_U16 (z m : Std.U16) (hm : m.val ≠ 0) :
    ∃ w : Std.U16, (z % m : Result Std.U16) = .ok w ∧ w.val = z.val % m.val := by
  have heq : (z % m : Result Std.U16) = Std.UScalar.rem z m := rfl
  unfold Std.UScalar.rem at heq
  simp [hm] at heq
  refine ⟨_, heq, ?_⟩
  show (BitVec.umod z.bv m.bv).toNat = z.val % m.val
  unfold BitVec.umod
  simp only [BitVec.toNat_ofNatLT]
  rfl

/-- Pure-projection side lemma for `parameters.FieldElement.add` —
    unconditional over ALL `FieldElement` inputs (no canonicity
    precondition). The U32 widening bounds the sum strictly below
    `2^32` so every intermediate step is `.ok`. -/
theorem FieldElement.add_eq_ok (a b : parameters.FieldElement) :
    parameters.FieldElement.add a b = .ok (FieldElement.add_pure a b) := by
  unfold FieldElement.add_pure
  suffices h : ∃ r, parameters.FieldElement.add a b = .ok r by
    obtain ⟨r, hr⟩ := h; rw [hr]
  unfold parameters.FieldElement.add
  simp only [lift, bind_tc_ok]
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hae := Std.UScalar.add_equiv x y
  cases hxy : (x + y) with
  | ok z =>
    rw [hxy] at hae; simp at hae
    obtain ⟨_, _, _⟩ := hae
    have hmod_val :
        (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val = 3329 := by
      unfold parameters.FIELD_MODULUS; simp
    have hmod_ne :
        (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val ≠ 0 := by
      rw [hmod_val]; decide
    set m : Std.U32 := Std.UScalar.cast .U32 parameters.FIELD_MODULUS
    obtain ⟨w, hw_eq, _⟩ := uscalar_rem_ok_U32 z m hmod_ne
    simp only [bind_tc_ok, hw_eq]
    exact ⟨_, rfl⟩
  | fail e =>
    rw [hxy] at hae; simp [Std.UScalar.inBounds] at hae
    rw [hxval, hyval] at hae; omega
  | div => rw [hxy] at hae; exact hae.elim

/-- Pure-projection side lemma for `parameters.FieldElement.mul` —
    unconditional over ALL `FieldElement` inputs. The U32 widening
    bounds the product strictly below `2^32`. -/
theorem FieldElement.mul_eq_ok (a b : parameters.FieldElement) :
    parameters.FieldElement.mul a b = .ok (FieldElement.mul_pure a b) := by
  unfold FieldElement.mul_pure
  suffices h : ∃ r, parameters.FieldElement.mul a b = .ok r by
    obtain ⟨r, hr⟩ := h; rw [hr]
  unfold parameters.FieldElement.mul
  simp only [lift, bind_tc_ok]
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hae := Std.UScalar.mul_equiv x y
  have heqmul : (x * y : Result Std.U32) = Std.UScalar.mul x y := rfl
  cases hxy : (x * y : Result Std.U32) with
  | ok z =>
    rw [heqmul] at hxy; rw [hxy] at hae; simp at hae
    obtain ⟨_, _, _⟩ := hae
    have hmod_val :
        (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val = 3329 := by
      unfold parameters.FIELD_MODULUS; simp
    have hmod_ne :
        (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val ≠ 0 := by
      rw [hmod_val]; decide
    set m : Std.U32 := Std.UScalar.cast .U32 parameters.FIELD_MODULUS
    obtain ⟨w, hw_eq, _⟩ := uscalar_rem_ok_U32 z m hmod_ne
    simp only [bind_tc_ok, hw_eq]
    exact ⟨_, rfl⟩
  | fail e =>
    rw [heqmul] at hxy; rw [hxy] at hae
    simp only [Std.UScalar.max, Std.UScalarTy.numBits] at hae
    rw [hxval, hyval] at hae
    have : a.val.val * b.val.val < 2^32 := by
      have h1 : a.val.val * b.val.val ≤ (2^16 - 1) * (2^16 - 1) := by
        apply Nat.mul_le_mul <;> omega
      have heq : (2^16 - 1) * (2^16 - 1) = 2^32 - 2*2^16 + 1 := by decide
      omega
    omega
  | div => rw [heqmul] at hxy; rw [hxy] at hae; exact hae.elim

/-- Pure-projection side lemma for `parameters.FieldElement.sub` —
    valid only for CANONICAL inputs. The U32 sum `a.val + q` reaches
    `q + (q-1) < 2·q` without overflow (q = 3329), and the subsequent
    `% q` is well-defined since q ≠ 0.

    For non-canonical inputs the impl can `.fail` — see the doc block
    above and `parameters.FieldElement.sub ⟨0⟩ ⟨65535⟩` counterexample. -/
theorem FieldElement.sub_eq_ok (a b : parameters.FieldElement)
    (ha : Canonical a) (hb : Canonical b) :
    parameters.FieldElement.sub a b = .ok (FieldElement.sub_pure a b) := by
  unfold Canonical at ha hb
  unfold parameters.FIELD_MODULUS at ha hb
  simp at ha hb
  unfold FieldElement.sub_pure
  suffices h : ∃ r, parameters.FieldElement.sub a b = .ok r by
    obtain ⟨r, hr⟩ := h; rw [hr]
  unfold parameters.FieldElement.sub
  simp only [lift, bind_tc_ok]
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  set q : Std.U32 := Std.UScalar.cast .U32 parameters.FIELD_MODULUS
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hqval : q.val = 3329 := by
    show (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val = 3329
    unfold parameters.FIELD_MODULUS; simp
  have hae := Std.UScalar.add_equiv x q
  cases hxq : (x + q : Result Std.U32) with
  | ok s =>
    rw [hxq] at hae; simp at hae
    obtain ⟨_, hsval, _⟩ := hae
    simp only [bind_tc_ok]
    have hae2 := Std.UScalar.sub_equiv s y
    cases hsy : (s - y : Result Std.U32) with
    | ok u =>
      rw [hsy] at hae2; simp at hae2
      simp only [bind_tc_ok]
      have hq_ne : q.val ≠ 0 := by rw [hqval]; decide
      obtain ⟨w, hw_eq, _⟩ := uscalar_rem_ok_U32 u q hq_ne
      rw [hw_eq]; simp only [bind_tc_ok]
      exact ⟨_, rfl⟩
    | fail e =>
      rw [hsy] at hae2; simp [] at hae2
      rw [hsval, hxval, hqval, hyval] at hae2
      omega
    | div => rw [hsy] at hae2; exact hae2.elim
  | fail e =>
    rw [hxq] at hae; simp [Std.UScalar.inBounds] at hae
    rw [hxval, hqval] at hae
    omega
  | div => rw [hxq] at hae; exact hae.elim

/-- Pure-projection side lemma for `parameters.FieldElement.neg` —
    valid only for CANONICAL input. The impl computes `q - self.val`
    in U16 (NO widening), which only avoids underflow when
    `self.val ≤ q`. The subsequent `% q` is well-defined since q ≠ 0.

    For non-canonical inputs the impl can `.fail` — see the doc block
    above and `parameters.FieldElement.neg ⟨65535⟩` counterexample. -/
theorem FieldElement.neg_eq_ok (a : parameters.FieldElement)
    (ha : Canonical a) :
    parameters.FieldElement.neg a = .ok (FieldElement.neg_pure a) := by
  unfold Canonical at ha
  unfold parameters.FIELD_MODULUS at ha
  simp at ha
  unfold FieldElement.neg_pure
  suffices h : ∃ r, parameters.FieldElement.neg a = .ok r by
    obtain ⟨r, hr⟩ := h; rw [hr]
  unfold parameters.FieldElement.neg
  have hA := a.val.hBounds
  simp [Std.UScalarTy.numBits] at hA
  have hqval : (parameters.FIELD_MODULUS : Std.U16).val = 3329 := by
    unfold parameters.FIELD_MODULUS; simp
  have hae := Std.UScalar.sub_equiv (parameters.FIELD_MODULUS : Std.U16) a.val
  cases hqa : ((parameters.FIELD_MODULUS : Std.U16) - a.val : Result Std.U16) with
  | ok i =>
    rw [hqa] at hae; simp at hae
    obtain ⟨_, _, _⟩ := hae
    simp only [bind_tc_ok]
    have hq_ne : (parameters.FIELD_MODULUS : Std.U16).val ≠ 0 := by
      rw [hqval]; decide
    obtain ⟨w, hw_eq, _⟩ := uscalar_rem_ok_U16 i parameters.FIELD_MODULUS hq_ne
    rw [hw_eq]; simp only [bind_tc_ok]
    exact ⟨_, rfl⟩
  | fail e =>
    rw [hqa] at hae; simp [] at hae
    rw [hqval] at hae
    omega
  | div => rw [hqa] at hae; exact hae.elim

/-! ## Canonicity preservation lemmas.

    Each `Canonical_<op>_pure` shows the `_pure` projection produces a
    canonical FE. Proof shape (mirrors the corresponding `_eq_ok` side
    lemma): chain through the do-block via `<op>_equiv`, extract `w`
    from the final `% q` via `uscalar_rem_ok_U{32,16}`, then bound
    `(UScalar.cast .U16 w).val = w.val < 3329` via
    `Std.UScalar.cast_val_mod_pow_of_inBounds_eq`. -/

/-- Canonicity preservation for `FieldElement.add_pure`. Unconditional:
    the result is the modular reduction `(a.val + b.val) % q < q`.

    Proof strategy: rewrite `parameters.FieldElement.add` to `.ok`
    via `add_eq_ok`, unfold the do-block, case on the U32 `+`/`%`
    branches (the `.ok` branch fires by assumption; `.fail`/`.div`
    discharge via `add_equiv` + `omega`/`hae.elim`), and bound the
    final U16 cast through `cast_val_mod_pow_of_inBounds_eq`. -/
theorem Canonical_add_pure (a b : parameters.FieldElement) :
    Canonical (FieldElement.add_pure a b) := by
  have hadd : parameters.FieldElement.add a b = .ok (FieldElement.add_pure a b) :=
    FieldElement.add_eq_ok a b
  unfold parameters.FieldElement.add at hadd
  simp only [lift, bind_tc_ok] at hadd
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hae := Std.UScalar.add_equiv x y
  cases hxy : (x + y) with
  | ok z =>
    rw [hxy] at hae hadd; simp at hae
    obtain ⟨_, _, _⟩ := hae
    simp only [bind_tc_ok] at hadd
    have hmod_val :
        (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val = 3329 := by
      unfold parameters.FIELD_MODULUS; simp
    have hmod_ne :
        (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val ≠ 0 := by
      rw [hmod_val]; decide
    set m : Std.U32 := Std.UScalar.cast .U32 parameters.FIELD_MODULUS
    obtain ⟨w, hw_eq, hwval⟩ := uscalar_rem_ok_U32 z m hmod_ne
    rw [hw_eq] at hadd; simp only [bind_tc_ok] at hadd
    unfold parameters.FieldElement.new at hadd
    simp at hadd
    have hwbnd : w.val < 3329 := by
      rw [hwval, hmod_val]; exact Nat.mod_lt _ (by decide)
    have hwcast : (Std.UScalar.cast .U16 w).val = w.val := by
      apply Std.UScalar.cast_val_mod_pow_of_inBounds_eq
      simp [Std.UScalarTy.numBits]; omega
    unfold Canonical
    rw [← hadd]
    show (Std.UScalar.cast .U16 w).val < parameters.FIELD_MODULUS.val
    unfold parameters.FIELD_MODULUS
    simp
    rw [hwcast]; exact hwbnd
  | fail e =>
    rw [hxy] at hae; simp [Std.UScalar.inBounds] at hae
    rw [hxval, hyval] at hae; omega
  | div => rw [hxy] at hae; exact hae.elim

/-- Canonicity preservation for `FieldElement.mul_pure`. Unconditional.

    Proof strategy: same shape as `Canonical_add_pure` but using
    `mul_equiv` and the `mul`-impl's U32 product `% q`. The `.fail`
    branch's panic-impossibility follows from
    `a.val * b.val ≤ (2^16-1)^2 < 2^32`. -/
theorem Canonical_mul_pure (a b : parameters.FieldElement) :
    Canonical (FieldElement.mul_pure a b) := by
  have hmul : parameters.FieldElement.mul a b = .ok (FieldElement.mul_pure a b) :=
    FieldElement.mul_eq_ok a b
  unfold parameters.FieldElement.mul at hmul
  simp only [lift, bind_tc_ok] at hmul
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hae := Std.UScalar.mul_equiv x y
  have heqmul : (x * y : Result Std.U32) = Std.UScalar.mul x y := rfl
  cases hxy : (x * y : Result Std.U32) with
  | ok z =>
    rw [hxy] at hmul
    rw [heqmul] at hxy
    rw [hxy] at hae; simp at hae
    obtain ⟨_, _, _⟩ := hae
    simp only [bind_tc_ok] at hmul
    have hmod_val :
        (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val = 3329 := by
      unfold parameters.FIELD_MODULUS; simp
    have hmod_ne :
        (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val ≠ 0 := by
      rw [hmod_val]; decide
    set m : Std.U32 := Std.UScalar.cast .U32 parameters.FIELD_MODULUS
    obtain ⟨w, hw_eq, hwval⟩ := uscalar_rem_ok_U32 z m hmod_ne
    rw [hw_eq] at hmul; simp only [bind_tc_ok] at hmul
    unfold parameters.FieldElement.new at hmul
    simp at hmul
    have hwbnd : w.val < 3329 := by
      rw [hwval, hmod_val]; exact Nat.mod_lt _ (by decide)
    have hwcast : (Std.UScalar.cast .U16 w).val = w.val := by
      apply Std.UScalar.cast_val_mod_pow_of_inBounds_eq
      simp [Std.UScalarTy.numBits]; omega
    unfold Canonical
    rw [← hmul]
    show (Std.UScalar.cast .U16 w).val < parameters.FIELD_MODULUS.val
    unfold parameters.FIELD_MODULUS
    simp
    rw [hwcast]; exact hwbnd
  | fail e =>
    rw [heqmul] at hxy; rw [hxy] at hae
    simp only [Std.UScalar.max, Std.UScalarTy.numBits] at hae
    rw [hxval, hyval] at hae
    have : a.val.val * b.val.val < 2^32 := by
      have h1 : a.val.val * b.val.val ≤ (2^16 - 1) * (2^16 - 1) := by
        apply Nat.mul_le_mul <;> omega
      have heq : (2^16 - 1) * (2^16 - 1) = 2^32 - 2*2^16 + 1 := by decide
      omega
    omega
  | div => rw [heqmul] at hxy; rw [hxy] at hae; exact hae.elim

/-- Canonicity preservation for `FieldElement.sub_pure`. Requires both
    inputs canonical (the impl panics on non-canonical inputs — see
    `sub_eq_ok`'s precondition).

    Proof strategy: two-step do-block — first `x + q` (panic-impossible
    by `hb` canonical, since `x.val + q.val ≤ q.val + (q.val-1) < 2^32`),
    then `s - y` (panic-impossible by `hb` canonical, since
    `s.val = x.val + q.val ≥ q.val > y.val`), then `% q` and U16 cast
    as in `Canonical_add_pure`. -/
theorem Canonical_sub_pure (a b : parameters.FieldElement)
    (ha : Canonical a) (hb : Canonical b) :
    Canonical (FieldElement.sub_pure a b) := by
  have hsub : parameters.FieldElement.sub a b = .ok (FieldElement.sub_pure a b) :=
    FieldElement.sub_eq_ok a b ha hb
  unfold Canonical at ha hb
  unfold parameters.FIELD_MODULUS at ha hb
  simp at ha hb
  unfold parameters.FieldElement.sub at hsub
  simp only [lift, bind_tc_ok] at hsub
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  set q : Std.U32 := Std.UScalar.cast .U32 parameters.FIELD_MODULUS
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hqval : q.val = 3329 := by
    show (Std.UScalar.cast .U32 parameters.FIELD_MODULUS).val = 3329
    unfold parameters.FIELD_MODULUS; simp
  have hae := Std.UScalar.add_equiv x q
  cases hxq : (x + q : Result Std.U32) with
  | ok s =>
    rw [hxq] at hae hsub; simp at hae
    obtain ⟨_, hsval, _⟩ := hae
    simp only [bind_tc_ok] at hsub
    have hae2 := Std.UScalar.sub_equiv s y
    cases hsy : (s - y : Result Std.U32) with
    | ok u =>
      rw [hsy] at hae2 hsub; simp at hae2
      obtain ⟨_, _, _⟩ := hae2
      simp only [bind_tc_ok] at hsub
      have hq_ne : q.val ≠ 0 := by rw [hqval]; decide
      obtain ⟨w, hw_eq, hwval⟩ := uscalar_rem_ok_U32 u q hq_ne
      rw [hw_eq] at hsub; simp only [bind_tc_ok] at hsub
      unfold parameters.FieldElement.new at hsub
      simp at hsub
      have hwbnd : w.val < 3329 := by
        rw [hwval, hqval]; exact Nat.mod_lt _ (by decide)
      have hwcast : (Std.UScalar.cast .U16 w).val = w.val := by
        apply Std.UScalar.cast_val_mod_pow_of_inBounds_eq
        simp [Std.UScalarTy.numBits]; omega
      unfold Canonical
      rw [← hsub]
      show (Std.UScalar.cast .U16 w).val < parameters.FIELD_MODULUS.val
      unfold parameters.FIELD_MODULUS
      simp
      rw [hwcast]; exact hwbnd
    | fail e =>
      rw [hsy] at hae2; simp at hae2
      rw [hsval, hxval, hqval, hyval] at hae2
      omega
    | div => rw [hsy] at hae2; exact hae2.elim
  | fail e =>
    rw [hxq] at hae; simp [Std.UScalar.inBounds] at hae
    rw [hxval, hqval] at hae
    omega
  | div => rw [hxq] at hae; exact hae.elim

/-- Canonicity preservation for `FieldElement.neg_pure`. Requires
    the input canonical.

    Proof strategy: the impl does NOT widen to U32 — it computes
    `q - self.val` directly in U16 (panic-impossible by `ha`
    canonical, since `q.val > a.val.val`), then `% q` at U16 width
    via `uscalar_rem_ok_U16`. The output IS the U16 (no narrowing
    cast), so the canonical bound is direct from `hwbnd`. -/
theorem Canonical_neg_pure (a : parameters.FieldElement)
    (ha : Canonical a) :
    Canonical (FieldElement.neg_pure a) := by
  have hneg : parameters.FieldElement.neg a = .ok (FieldElement.neg_pure a) :=
    FieldElement.neg_eq_ok a ha
  unfold Canonical at ha
  unfold parameters.FIELD_MODULUS at ha
  simp at ha
  unfold parameters.FieldElement.neg at hneg
  have hA := a.val.hBounds
  simp [Std.UScalarTy.numBits] at hA
  have hqval : (parameters.FIELD_MODULUS : Std.U16).val = 3329 := by
    unfold parameters.FIELD_MODULUS; simp
  have hae := Std.UScalar.sub_equiv (parameters.FIELD_MODULUS : Std.U16) a.val
  cases hqa : ((parameters.FIELD_MODULUS : Std.U16) - a.val : Result Std.U16) with
  | ok i =>
    rw [hqa] at hae hneg; simp at hae
    obtain ⟨_, _, _⟩ := hae
    simp only [bind_tc_ok] at hneg
    have hq_ne : (parameters.FIELD_MODULUS : Std.U16).val ≠ 0 := by
      rw [hqval]; decide
    obtain ⟨w, hw_eq, hwval⟩ := uscalar_rem_ok_U16 i parameters.FIELD_MODULUS hq_ne
    rw [hw_eq] at hneg; simp only [bind_tc_ok] at hneg
    unfold parameters.FieldElement.new at hneg
    simp at hneg
    have hwbnd : w.val < 3329 := by
      rw [hwval, hqval]; exact Nat.mod_lt _ (by decide)
    unfold Canonical
    rw [← hneg]
    show w.val < parameters.FIELD_MODULUS.val
    unfold parameters.FIELD_MODULUS
    simp
    exact hwbnd
  | fail e =>
    rw [hqa] at hae; simp at hae
    rw [hqval] at hae
    omega
  | div => rw [hqa] at hae; exact hae.elim

/-! ## Poly-wrapper pure-projection side lemmas.

    Each `polynomial.<op>_eq_ok` pins the hacspec wrapper's `.ok` value to
    the projected `polynomial.<op>_pure` value, on the corresponding
    canonicity precondition (none for `add`, none for `poly_barrett_reduce`,
    per-element canonicity for both inputs to `subtract_reduce`). These
    are the input lemmas to `libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq` and to downstream M.2
    commute lemmas; 
    for why "panic-freedom" is the wrong framing. Proof shape:
    * Unfold the wrapper through `parameters.createi` to
      `core.array.from_fn`.
    * Apply `libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq` with `f` the
      pointwise pure projection.
    * Discharge the per-element closure obligation by unfolding
      `call_mut`/`call`, rewriting the leading `Array.index_usize` via
      `Std.Array.index_usize_spec`, and matching the rest of the body
      against the corresponding scalar `_eq_ok` lemma.
    * Conclude by unfolding the `_pure` projection and rewriting through
      the just-proved equation, reducing the match on `.ok`. -/

/-- Local helper: `Std.Array.index_usize` on a length-`n` array at index
    `i < n` returns `.ok v.val[i.val]!`. Mirrors `array_index_usize_ok_eq`
    in `Util.PortableVector` but avoids pulling that file's
    LoopSpecs/PortableVector chain through `SpecPure`. -/
private theorem array_index_usize_ok
    {α : Type u} {n : Std.Usize} [Inhabited α]
    (v : Std.Array α n) (i : Std.Usize) (h_bd : i.val < v.length) :
    Aeneas.Std.Array.index_usize v i = .ok (v.val[i.val]!) := by
  have hT := Aeneas.Std.Array.index_usize_spec v i h_bd
  have h_ex := Aeneas.Std.WP.spec_imp_exists hT
  obtain ⟨v', hveq, hPv'⟩ := h_ex
  rw [hveq, hPv', getElem!_pos]

/-- Pure-projection side lemma for `polynomial.add_to_ring_element` —
    unconditional over ALL inputs.

    Proof: unfold wrapper to `core.array.from_fn`; apply
    `from_fn_pure_eq` with the pointwise `FieldElement.add_pure`; the
    pointwise closure body is the inlined `FieldElement.add` body
    preceded by two `index_usize` ops — closed by `FieldElement.add_eq_ok`. -/
theorem polynomial.add_to_ring_element_eq_ok
    (lhs rhs : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    hacspec_ml_kem.polynomial.add_to_ring_element lhs rhs
      = .ok (polynomial.add_to_ring_element_pure lhs rhs) := by
  -- Step 1: pointwise function f.
  set f : Nat → parameters.FieldElement :=
    fun k => FieldElement.add_pure (lhs.val[k]!) (rhs.val[k]!) with hf_def
  -- Step 2: pointwise closure obligation.
  have hpure : ∀ k : Nat, k < (256#usize : Std.Usize).val →
      (hacspec_ml_kem.polynomial.add_to_ring_element.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement
        : CoreModels.core.ops.function.Fn _ _ _).FnMutInst.call_mut
            (lhs, rhs) ⟨BitVec.ofNat _ k⟩
        = .ok (f k, (lhs, rhs)) := by
    intro k hk
    have hk' : k < 256 := hk
    show polynomial.add_to_ring_element.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut
        (lhs, rhs) ⟨BitVec.ofNat _ k⟩ = .ok (f k, (lhs, rhs))
    unfold polynomial.add_to_ring_element.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut
    unfold polynomial.add_to_ring_element.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement.call
    -- Index-usize obligations.
    have hk_us : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k := by
      show (BitVec.ofNat _ k).toNat = k
      apply Nat.mod_eq_of_lt
      have : k < 2^System.Platform.numBits := by
        have hbits : 2^16 ≤ 2^System.Platform.numBits :=
          Nat.pow_le_pow_right (by decide) (by
            cases System.Platform.numBits_eq with
            | inl h => rw [h]; decide
            | inr h => rw [h]; decide)
        omega
      exact this
    have hlhs_len : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val < lhs.length := by
      rw [hk_us]; show k < lhs.val.length
      rw [lhs.property]; exact hk
    have hrhs_len : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val < rhs.length := by
      rw [hk_us]; show k < rhs.val.length
      rw [rhs.property]; exact hk
    have h_lhs_idx :
        Std.Array.index_usize lhs (⟨BitVec.ofNat _ k⟩ : Std.Usize)
          = .ok (lhs.val[k]!) := by
      rw [array_index_usize_ok lhs _ hlhs_len, hk_us]
    have h_rhs_idx :
        Std.Array.index_usize rhs (⟨BitVec.ofNat _ k⟩ : Std.Usize)
          = .ok (rhs.val[k]!) := by
      rw [array_index_usize_ok rhs _ hrhs_len, hk_us]
    -- The remainder of the closure body is exactly the body of
    -- `parameters.FieldElement.add lhs[k]! rhs[k]!`.
    have h_add :=
      FieldElement.add_eq_ok (lhs.val[k]!) (rhs.val[k]!)
    -- The outer wrapper has shape `do let fe ← (let (a, a1) := (lhs, rhs); inner_call); ok (fe, ...)`.
    -- Reduce the destructuring `let (a, a1) := (lhs, rhs)` to `a := lhs, a1 := rhs`.
    change (do
      let fe ← (do
        let fe ← Std.Array.index_usize lhs ⟨BitVec.ofNat _ k⟩
        let i ← lift (Std.UScalar.cast .U32 fe.val)
        let fe1 ← Std.Array.index_usize rhs ⟨BitVec.ofNat _ k⟩
        let i1 ← lift (Std.UScalar.cast .U32 fe1.val)
        let i2 ← i + i1
        let i3 ← lift (Std.UScalar.cast .U32 parameters.FIELD_MODULUS)
        let i4 ← i2 % i3
        let i5 ← lift (Std.UScalar.cast .U16 i4)
        parameters.FieldElement.new i5)
      Result.ok (fe, lhs, rhs)) = Result.ok (f k, lhs, rhs)
    -- Now rewrite the two `index_usize`s and use `add_eq_ok` to collapse the rest.
    rw [h_lhs_idx]; simp only [bind_tc_ok]
    rw [h_rhs_idx]; simp only [bind_tc_ok]
    unfold parameters.FieldElement.add at h_add
    rw [h_add]
    simp only [bind_tc_ok, hf_def]
  -- Step 3: chain through `from_fn_pure_eq` to get the wrapper equation.
  have h_from_fn :=
    libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
      (T := parameters.FieldElement)
      (F := polynomial.add_to_ring_element.closure)
      (N := 256#usize)
      (inst := polynomial.add_to_ring_element.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement)
      (c := (lhs, rhs))
      (f := f)
      hpure
  have h_wrap : hacspec_ml_kem.polynomial.add_to_ring_element lhs rhs
      = .ok ⟨(List.range (256#usize : Std.Usize).val).map f,
             by simp [List.length_map, List.length_range]⟩ := by
    unfold hacspec_ml_kem.polynomial.add_to_ring_element
    unfold hacspec_ml_kem.parameters.createi
    exact h_from_fn
  -- Step 4: reduce the `_pure` projection via the wrapper equation.
  rw [h_wrap]
  unfold polynomial.add_to_ring_element_pure
  rw [h_wrap]

/-- The pure-rem of a U16 by `parameters.FIELD_MODULUS` (= 3329 ≠ 0).
    A noncomputable wrapper extracting the `.ok` witness from
    `uscalar_rem_ok_U16`. Used as the pointwise function in
    `poly_barrett_reduce_eq_ok`. -/
private noncomputable def rem_q_U16 (z : Std.U16) : Std.U16 :=
  have hq_ne : (parameters.FIELD_MODULUS : Std.U16).val ≠ 0 := by
    unfold parameters.FIELD_MODULUS; decide
  Classical.choose (uscalar_rem_ok_U16 z parameters.FIELD_MODULUS hq_ne)

private theorem rem_q_U16_eq (z : Std.U16) :
    (z % parameters.FIELD_MODULUS : Result Std.U16) = .ok (rem_q_U16 z) := by
  have hq_ne : (parameters.FIELD_MODULUS : Std.U16).val ≠ 0 := by
    unfold parameters.FIELD_MODULUS; decide
  unfold rem_q_U16
  exact (Classical.choose_spec
    (uscalar_rem_ok_U16 z parameters.FIELD_MODULUS hq_ne)).1

/-- Pure-projection side lemma for `polynomial.poly_barrett_reduce` —
    unconditional over ALL inputs.

    Proof: unfold wrapper to `core.array.from_fn`; apply
    `from_fn_pure_eq` with `f k := ⟨rem_q_U16 (p.val[k]!).val⟩`. The
    pointwise closure body is `index_usize p k; (fe.val % q); new` — the
    `%` step is at U16 width (no widening) and `parameters.FIELD_MODULUS
    ≠ 0`, so `uscalar_rem_ok_U16` discharges it. -/
theorem polynomial.poly_barrett_reduce_eq_ok
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    hacspec_ml_kem.polynomial.poly_barrett_reduce p
      = .ok (polynomial.poly_barrett_reduce_pure p) := by
  -- Step 1: pointwise function f.
  set f : Nat → parameters.FieldElement :=
    fun k => { val := rem_q_U16 (p.val[k]!).val }
    with hf_def
  -- Step 2: pointwise closure obligation.
  have hpure : ∀ k : Nat, k < (256#usize : Std.Usize).val →
      (hacspec_ml_kem.polynomial.poly_barrett_reduce.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement
        : CoreModels.core.ops.function.Fn _ _ _).FnMutInst.call_mut
            p ⟨BitVec.ofNat _ k⟩
        = .ok (f k, p) := by
    intro k hk
    show polynomial.poly_barrett_reduce.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut
        p ⟨BitVec.ofNat _ k⟩ = .ok (f k, p)
    unfold polynomial.poly_barrett_reduce.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut
    unfold polynomial.poly_barrett_reduce.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement.call
    -- Index-usize obligation.
    have hk' : k < 256 := hk
    have hk_us : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k := by
      show (BitVec.ofNat _ k).toNat = k
      apply Nat.mod_eq_of_lt
      have : k < 2^System.Platform.numBits := by
        have hbits : 2^16 ≤ 2^System.Platform.numBits :=
          Nat.pow_le_pow_right (by decide) (by
            cases System.Platform.numBits_eq with
            | inl h => rw [h]; decide
            | inr h => rw [h]; decide)
        omega
      exact this
    have hp_len : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val < p.length := by
      rw [hk_us]; show k < p.val.length
      rw [p.property]; exact hk
    have h_p_idx :
        Std.Array.index_usize p (⟨BitVec.ofNat _ k⟩ : Std.Usize)
          = .ok (p.val[k]!) := by
      rw [array_index_usize_ok p _ hp_len, hk_us]
    -- Close the closure body: index, then rem, then new (returned inline).
    change (do
      let fe ← (do
        let fe ← Std.Array.index_usize p ⟨BitVec.ofNat _ k⟩
        let i ← (fe.val % parameters.FIELD_MODULUS : Result Std.U16)
        parameters.FieldElement.new i)
      Result.ok (fe, p)) = Result.ok (f k, p)
    rw [h_p_idx]; simp only [bind_tc_ok]
    rw [rem_q_U16_eq]; simp only [bind_tc_ok]
    unfold parameters.FieldElement.new
    simp only [bind_tc_ok, hf_def]
  -- Step 3: apply from_fn_pure_eq.
  have h_from_fn :=
    libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
      (T := parameters.FieldElement)
      (F := polynomial.poly_barrett_reduce.closure)
      (N := 256#usize)
      (inst := polynomial.poly_barrett_reduce.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement)
      (c := p)
      (f := f)
      hpure
  have h_wrap : hacspec_ml_kem.polynomial.poly_barrett_reduce p
      = .ok ⟨(List.range (256#usize : Std.Usize).val).map f,
             by simp [List.length_map, List.length_range]⟩ := by
    unfold hacspec_ml_kem.polynomial.poly_barrett_reduce
    unfold hacspec_ml_kem.parameters.createi
    exact h_from_fn
  -- Step 4: reduce the `_pure` projection via h_wrap.
  rw [h_wrap]
  unfold polynomial.poly_barrett_reduce_pure
  rw [h_wrap]

/-- Identity-on-canonical bridge for `polynomial.poly_barrett_reduce_pure`.

    When every lane of `p` is canonical (`p.val[k]!.val.val < q`), the pure
    projection is the identity: `poly_barrett_reduce_pure p = p`. Used by
    L6.1 FC close where the input is `lift_poly self` (canonical by
    `lift_fe`'s `feOfZMod` codomain). -/
theorem polynomial.poly_barrett_reduce_pure_id_of_canonical
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (hcan : ∀ k : Nat, k < 256 → Canonical (p.val[k]!)) :
    polynomial.poly_barrett_reduce_pure p = p := by
  -- Re-derive `h_wrap` with f := fun k => p.val[k]! (canonical identity).
  set f : Nat → parameters.FieldElement := fun k => p.val[k]! with hf_def
  have hpure : ∀ k : Nat, k < (256#usize : Std.Usize).val →
      (hacspec_ml_kem.polynomial.poly_barrett_reduce.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement
        : CoreModels.core.ops.function.Fn _ _ _).FnMutInst.call_mut
            p ⟨BitVec.ofNat _ k⟩
        = .ok (f k, p) := by
    intro k hk
    show polynomial.poly_barrett_reduce.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut
        p ⟨BitVec.ofNat _ k⟩ = .ok (f k, p)
    unfold polynomial.poly_barrett_reduce.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut
    unfold polynomial.poly_barrett_reduce.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement.call
    have hk' : k < 256 := hk
    have hk_us : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k := by
      show (BitVec.ofNat _ k).toNat = k
      apply Nat.mod_eq_of_lt
      have : k < 2^System.Platform.numBits := by
        have hbits : 2^16 ≤ 2^System.Platform.numBits :=
          Nat.pow_le_pow_right (by decide) (by
            cases System.Platform.numBits_eq with
            | inl h => rw [h]; decide
            | inr h => rw [h]; decide)
        omega
      exact this
    have hp_len : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val < p.length := by
      rw [hk_us]; show k < p.val.length
      rw [p.property]; exact hk
    have h_p_idx :
        Std.Array.index_usize p (⟨BitVec.ofNat _ k⟩ : Std.Usize)
          = .ok (p.val[k]!) := by
      rw [array_index_usize_ok p _ hp_len, hk_us]
    change (do
      let fe ← (do
        let fe ← Std.Array.index_usize p ⟨BitVec.ofNat _ k⟩
        let i ← (fe.val % parameters.FIELD_MODULUS : Result Std.U16)
        parameters.FieldElement.new i)
      Result.ok (fe, p)) = Result.ok (f k, p)
    rw [h_p_idx]; simp only [bind_tc_ok]
    rw [rem_q_U16_eq]; simp only [bind_tc_ok]
    unfold parameters.FieldElement.new
    simp only [bind_tc_ok]
    -- Goal: .ok ({ val := rem_q_U16 (p.val[k]!).val }, p) = .ok (f k, p).
    -- Build f k = p.val[k]! identity using canonicity.
    have hcank : Canonical (p.val[k]!) := hcan k hk'
    unfold Canonical at hcank
    have hq_val : parameters.FIELD_MODULUS.val = 3329 := by
      unfold parameters.FIELD_MODULUS; decide
    have hcank_int : (p.val[k]!).val.val < 3329 := by
      have : (p.val[k]!).val.val < parameters.FIELD_MODULUS.val := hcank
      rw [hq_val] at this; exact this
    -- rem_q_U16 (p.val[k]!).val .val = (p.val[k]!).val.val % 3329 = (p.val[k]!).val.val.
    have hq_ne : (parameters.FIELD_MODULUS : Std.U16).val ≠ 0 := by
      unfold parameters.FIELD_MODULUS; decide
    have h_rem_val : (rem_q_U16 (p.val[k]!).val).val = (p.val[k]!).val.val % 3329 := by
      have ⟨w, hw_eq, hw_val⟩ :=
        uscalar_rem_ok_U16 (p.val[k]!).val parameters.FIELD_MODULUS hq_ne
      have h_rem_eq := rem_q_U16_eq (p.val[k]!).val
      rw [hw_eq] at h_rem_eq
      have h_w_eq_rem : w = rem_q_U16 (p.val[k]!).val := Result.ok.inj h_rem_eq
      rw [← h_w_eq_rem, hw_val, hq_val]
    have h_rem_val_eq : (rem_q_U16 (p.val[k]!).val).val = (p.val[k]!).val.val :=
      h_rem_val.trans (Nat.mod_eq_of_lt hcank_int)
    -- The two U16s `rem_q_U16 (p.val[k]!).val` and `(p.val[k]!).val` have equal .val.
    -- Use Std.U16's @[ext] from .val equality, which goes via .bv equality.
    have h_u16_eq : rem_q_U16 (p.val[k]!).val = (p.val[k]!).val := by
      apply Std.U16.bv_eq_imp_eq
      -- .bv equality reduces to .val (= .bv.toNat) equality via BitVec.ext + width.
      show (rem_q_U16 (p.val[k]!).val).bv = ((p.val[k]!).val).bv
      apply BitVec.eq_of_toNat_eq
      show (rem_q_U16 (p.val[k]!).val).val = ((p.val[k]!).val).val
      exact h_rem_val_eq
    -- Plug in: ⟨rem_q_U16 (p.val[k]!).val⟩ = ⟨(p.val[k]!).val⟩ = p.val[k]! = f k.
    have h_fe_eq : ({ val := rem_q_U16 (p.val[k]!).val } : parameters.FieldElement) = f k := by
      rw [h_u16_eq, hf_def]
    rw [h_fe_eq]
  -- Apply from_fn_pure_eq with this f.
  have h_from_fn :=
    libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
      (T := parameters.FieldElement)
      (F := polynomial.poly_barrett_reduce.closure)
      (N := 256#usize)
      (inst := polynomial.poly_barrett_reduce.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement)
      (c := p)
      (f := f)
      hpure
  have h_wrap : hacspec_ml_kem.polynomial.poly_barrett_reduce p
      = .ok ⟨(List.range (256#usize : Std.Usize).val).map f,
             by simp [List.length_map, List.length_range]⟩ := by
    unfold hacspec_ml_kem.polynomial.poly_barrett_reduce
    unfold hacspec_ml_kem.parameters.createi
    exact h_from_fn
  -- Unfold _pure via h_wrap.
  unfold polynomial.poly_barrett_reduce_pure
  rw [h_wrap]
  -- Goal: ⟨(range 256).map f, _⟩ = p. Use Subtype.ext + list equality.
  apply Subtype.ext
  show (List.range 256).map f = p.val
  have h_p_len : p.val.length = 256 := p.property
  apply List.ext_getElem
  · simp [h_p_len]
  · intro k hk1 _hk2
    have hk : k < 256 := by
      have : k < (List.range 256).length := by simpa using hk1
      simpa using this
    rw [List.getElem_map, List.getElem_range]
    show f k = p.val[k]
    rw [hf_def]
    show p.val[k]! = p.val[k]
    -- Use getElem!_pos to align p.val[k]! with p.val[k]'_.
    exact getElem!_pos p.val k (by rw [h_p_len]; exact hk)

/-- Pure-projection side lemma for `polynomial.subtract_reduce` — valid
    for per-element CANONICAL inputs. The closure body inlines
    `parameters.FieldElement.sub`'s
    do-block (with a moved `index_usize a1 k` in the middle); after
    rewriting the two `index_usize` calls to `.ok` form, the remaining
    body IS the body of `parameters.FieldElement.sub (a.val[k]!) (a1.val[k]!)`
    so the per-element canonicity preconditions feed directly into
    `FieldElement.sub_eq_ok`. -/
theorem polynomial.subtract_reduce_eq_ok
    (a b : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (ha : ∀ k : Nat, k < 256 → Canonical (a.val[k]!))
    (hb : ∀ k : Nat, k < 256 → Canonical (b.val[k]!)) :
    hacspec_ml_kem.polynomial.subtract_reduce a b
      = .ok (polynomial.subtract_reduce_pure a b) := by
  -- Step 1: pointwise function f.
  set f : Nat → parameters.FieldElement :=
    fun k => FieldElement.sub_pure (a.val[k]!) (b.val[k]!) with hf_def
  -- Step 2: pointwise closure obligation.
  have hpure : ∀ k : Nat, k < (256#usize : Std.Usize).val →
      (hacspec_ml_kem.polynomial.subtract_reduce.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement
        : CoreModels.core.ops.function.Fn _ _ _).FnMutInst.call_mut
            (a, b) ⟨BitVec.ofNat _ k⟩
        = .ok (f k, (a, b)) := by
    intro k hk
    have hk' : k < 256 := hk
    show polynomial.subtract_reduce.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut
        (a, b) ⟨BitVec.ofNat _ k⟩ = .ok (f k, (a, b))
    unfold polynomial.subtract_reduce.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut
    unfold polynomial.subtract_reduce.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement.call
    -- Index-usize obligations.
    have hk_us : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k := by
      show (BitVec.ofNat _ k).toNat = k
      apply Nat.mod_eq_of_lt
      have : k < 2^System.Platform.numBits := by
        have hbits : 2^16 ≤ 2^System.Platform.numBits :=
          Nat.pow_le_pow_right (by decide) (by
            cases System.Platform.numBits_eq with
            | inl h => rw [h]; decide
            | inr h => rw [h]; decide)
        omega
      exact this
    have ha_len : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val < a.length := by
      rw [hk_us]; show k < a.val.length
      rw [a.property]; exact hk
    have hb_len : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val < b.length := by
      rw [hk_us]; show k < b.val.length
      rw [b.property]; exact hk
    have h_a_idx :
        Std.Array.index_usize a (⟨BitVec.ofNat _ k⟩ : Std.Usize)
          = .ok (a.val[k]!) := by
      rw [array_index_usize_ok a _ ha_len, hk_us]
    have h_b_idx :
        Std.Array.index_usize b (⟨BitVec.ofNat _ k⟩ : Std.Usize)
          = .ok (b.val[k]!) := by
      rw [array_index_usize_ok b _ hb_len, hk_us]
    -- The `sub_eq_ok` lemma needs canonicity of both operands.
    have h_sub :=
      FieldElement.sub_eq_ok (a.val[k]!) (b.val[k]!) (ha k hk') (hb k hk')
    unfold parameters.FieldElement.sub at h_sub
    -- The outer wrapper has shape `do let fe ← (let (x, y) := (a, b); inner_call); ok (fe, ...)`.
    -- Reduce the destructuring `let (x, y) := (a, b)`.
    change (do
      let fe ← (do
        let fe ← Std.Array.index_usize a ⟨BitVec.ofNat _ k⟩
        let i ← lift (Std.UScalar.cast .U32 fe.val)
        let i1 ← lift (Std.UScalar.cast .U32 parameters.FIELD_MODULUS)
        let i2 ← i + i1
        let fe1 ← Std.Array.index_usize b ⟨BitVec.ofNat _ k⟩
        let i3 ← lift (Std.UScalar.cast .U32 fe1.val)
        let i4 ← i2 - i3
        let i5 ← lift (Std.UScalar.cast .U32 parameters.FIELD_MODULUS)
        let i6 ← i4 % i5
        let i7 ← lift (Std.UScalar.cast .U16 i6)
        parameters.FieldElement.new i7)
      Result.ok (fe, a, b)) = Result.ok (f k, a, b)
    rw [h_a_idx]; simp only [bind_tc_ok]
    rw [h_b_idx]; simp only [bind_tc_ok]
    -- The inner block is now exactly the body of
    -- `parameters.FieldElement.sub (a.val[k]!) (b.val[k]!)` (with `b` re-ordered),
    -- which equals `.ok (sub_pure …)` by `h_sub`.
    rw [h_sub]
    simp only [bind_tc_ok, hf_def]
  -- Step 3: apply from_fn_pure_eq.
  have h_from_fn :=
    libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
      (T := parameters.FieldElement)
      (F := polynomial.subtract_reduce.closure)
      (N := 256#usize)
      (inst := polynomial.subtract_reduce.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement)
      (c := (a, b))
      (f := f)
      hpure
  have h_wrap : hacspec_ml_kem.polynomial.subtract_reduce a b
      = .ok ⟨(List.range (256#usize : Std.Usize).val).map f,
             by simp [List.length_map, List.length_range]⟩ := by
    unfold hacspec_ml_kem.polynomial.subtract_reduce
    unfold hacspec_ml_kem.parameters.createi
    exact h_from_fn
  -- Step 4: reduce the `_pure` projection via h_wrap.
  rw [h_wrap]
  unfold polynomial.subtract_reduce_pure
  rw [h_wrap]

end libcrux_iot_ml_kem.Spec.Pure