/-
  Shared definitions for Keccak-f[1600] equivalence proofs.

  - `spec_round_step` / `roundOfNat` bundle the 5-step spec round used
    by the `Nat.fold 24` chain in `keccakf1600_post_canonical`.
  - `keccakf1600_post_canonical` is the top-level post shape used by
    `AlgebraicEquiv.lean`'s `keccakf1600_equiv_via_bit` and the
    hacspec coupling in `HacspecBridge.lean`.
  - `holds_chain_eq_ok` extracts a Result equation from a
    `(do C; pure (r = X)).holds` hypothesis.
-/
import LibcruxIotSha3.Foundation.RoundEquiv

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Foundation

/-- From a `.holds` claim of the form `(do let r ← C; pure (r = X)).holds`
    derive the underlying Result equation `C = .ok X`. -/
theorem holds_chain_eq_ok {α : Type} {C : Aeneas.Std.Result α} {X : α}
    (h : (do let r ← C; pure (r = X)).holds) : C = .ok X := by
  cases C
  all_goals simp_all [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp, PredTrans.apply, Functor.map,
                      Std.Do.SPred.down_pure]

/-! ## Spec-side one-round step (theta + rho + pi + chi + iota)

Bundles the 5-step spec round into a single function so we can talk
about iterating it. -/

def spec_round_step (state : Std.Array Std.U64 25#usize) (round : Std.Usize) :
    Result (Std.Array Std.U64 25#usize) := do
  let s_theta ← keccak_f.theta state
  let s_rho ← keccak_f.rho s_theta
  let s_pi ← keccak_f.pi s_rho
  let s_chi ← keccak_f.chi s_pi
  keccak_f.iota s_chi round

/-- Convert a `Nat` ≤ 24 to `Std.Usize`. Used in `keccakf1600_post_canonical`
    to bridge `Nat.fold` indices into the `Std.Usize` argument that
    `spec_round_step` requires. Since `24 < 2^32 ≤ 2^System.Platform.numBits`,
    the bound proof is trivial. -/
def roundOfNat (k : Nat) (h : k ≤ 24) : Std.Usize :=
  Std.UScalar.ofNatCore k (by
    have h24 : (24 : Nat) < 2 ^ Std.UScalarTy.Usize.numBits := by
      simp only [Std.UScalarTy.Usize_numBits_eq]
      rcases System.Platform.numBits_eq with hpn | hpn <;> rw [hpn] <;> decide
    omega)

/-! ## Top-level post: 24-fold spec round application

`keccakf1600_post_canonical` compares the 24-fold spec output against
the canonical `lift r_impl` (no swap). This is the statement proven
via the time-varying `impl_swap_k` architecture in
`AlgebraicEquiv.lean` — at round 24 (= round 0 mod 4) the polarity
cycle returns to `swZero`, so the spec output is read canonically. -/
@[irreducible]
def keccakf1600_post_canonical (s : state.KeccakState) (r_impl : state.KeccakState) : Prop :=
  (do
    let lifted_final ← Nat.fold 24
      (fun i h acc => acc >>= fun st => spec_round_step st (roundOfNat i (by omega)))
      (pure (lift s))
    pure (lifted_final = lift r_impl)).holds

end libcrux_iot_sha3.Foundation
