/-
  Spec-chain helpers and `Result Prop` plumbing.

  Provides:
  - `spec_round_step_at` and `spec_chain` (with `spec_chain_zero` /
    `spec_chain_succ`) — used by `AlgebraicEquiv.lean` to express
    the 24-round canonical post as a `Nat.fold` of single-round spec
    steps.
  - `pure_prop_holds` / `of_pure_prop_holds` — `(pure P : Result Prop).holds ↔ P`
    convenience lemmas used by `StructuralEquiv.lean` and the
    loop-invariant unpacking in `AlgebraicEquiv.lean`.

  The top-level equivalence is `Composition.keccakf1600_equiv_via_bit`
  (canonical `lift r_impl`, no `Balanced` precondition, via the
  time-varying `impl_swap_k` architecture). The I32 iterator +
  range-loop helpers live in `Foundation/I32LoopSpec.lean`.
-/
import LibcruxIotSha3.Foundation.SpecStep

open Aeneas Aeneas.Std Result ControlFlow Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Foundation

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-! ## Spec-chain helper

`spec_round_step_at` wraps `spec_round_step` for use inside the
`Nat.fold 24` chain in `keccakf1600_loop_post` / `keccakf1600_post_canonical`.
`spec_chain` packages the `Nat.fold` form. -/

def spec_round_step_at (round_idx : Nat) (st : Std.Array Std.U64 25#usize) :
    Result (Std.Array Std.U64 25#usize) :=
  if h : round_idx < 24 then spec_round_step st (roundOfNat round_idx (by omega))
  else .fail .panic

/-- `spec_chain n s_lift` applies `n` spec rounds (indices 0..n-1) to
    the lifted initial state `s_lift`. -/
def spec_chain (s_lift : Std.Array Std.U64 25#usize) (n : Nat) :
    Result (Std.Array Std.U64 25#usize) :=
  Nat.fold n (fun i _ acc => acc >>= fun st => spec_round_step_at i st) (pure s_lift)

theorem spec_chain_zero (s_lift : Std.Array Std.U64 25#usize) :
    spec_chain s_lift 0 = .ok s_lift := by
  rfl

theorem spec_chain_succ (s_lift : Std.Array Std.U64 25#usize) (n : Nat) :
    spec_chain s_lift (n + 1) =
      spec_chain s_lift n >>= fun st => spec_round_step_at n st := by
  unfold spec_chain
  rw [Nat.fold_succ]

/-! ## `pure P` ↔ `P` for `Result Prop`

Used by `StructuralEquiv.lean` and the loop-invariant unpacking
in `AlgebraicEquiv.lean`. -/

theorem pure_prop_holds {P : Prop} (h : P) : (pure P : Result Prop).holds := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp]
  intro _
  exact h

theorem of_pure_prop_holds {P : Prop} (h : (pure P : Result Prop).holds) : P := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp] at h
  exact h trivial

end libcrux_iot_sha3.Foundation
