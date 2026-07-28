/-
  Per-round functional equivalence (impl-side `keccakf1600_round{N}_*`
  composed against the spec-side `keccak_f.theta ∘ keccak_f.rho ∘
  keccak_f.pi ∘ keccak_f.chi ∘ iota`).

  This file composes `theta_lift_spec` and `prc_lift_spec` (round 0)
  into a single Triple establishing the full per-round equivalence.

  ## Proof shape

  `round{0,1,2,3}_equiv_spec` each build at 16M heartbeats. The four
  proofs follow the same shape (one `hax_mvcgen`, side-goal `scalar_tac`
  chain, `unfold round{k}_post` + `casesm` + second `hax_mvcgen` +
  `simp_all`) and each is tagged `@[spec]` for the top-level composition.

  ### Key discipline (don't break)
  Each `round{k}_post` is declared `@[irreducible]`. This is load-bearing:
  without it, `hax_mvcgen` unfolds the post, sees the spec do-block
  `(do θ; ρ; π; χ; ι _ s.i).holds`, and recursively dispatches
  `theta_spec / rho_spec / …` *in addition to* the
  impl-side `theta_lift_spec + chain_spec` dispatches — blowing the
  heartbeat budget past 32M. With `@[irreducible]` the post stays
  opaque during impl-side mvcgen; we then unfold it and run a
  *second* `hax_mvcgen` (the spec do-block has the chain hypotheses
  already in scope from the first mvcgen, so the spec dispatch is
  cheap). See `feedback_irreducible_post_def_for_mvcgen` memory.

  ## Architecture

  - `theta_applied` + `@[spec] theta_spec` —
    pure semantics + auto-firing spec for `keccak_f.theta`.
    (NB: placed here, not in `PrcLift.lean`, so the @[spec] is only
    in scope for files that import RoundEquiv. Putting it in PrcLift
    pushed prc_lift_spec's mvcgen budget past 128M.)
  - `keccakf1600_round{k}_pi_rho_chi_chain` + `@[spec]` wrappers
    package `pi_rho_chi_1 ; pi_rho_chi_2` so the @[spec] matcher
    fires on a single named function in chain context.
  - `round{k}_post` (each `@[irreducible]`) names the spec-side
    `(do θ; ρ; π; χ; ι _ s.i).holds` predicate so `hax_mvcgen` does
    not recursively dispatch the 5 spec lemmas during impl
    advancement.

  ## Round dependencies

  Each `round{k}_equiv_spec` discharges via the underlying
  `theta_lift_spec_k` and `prc_lift_spec_k` lemmas (see
  `ThetaLiftRound{1,2,3}.lean`, `PrcLiftRound{1,2,3}.lean`). All four
  round specs are tagged `@[spec]` and consumed by the 24-round
  composition in `AlgebraicEquiv.lean`.
-/
import LibcruxIotSha3.Foundation.ThetaLift
import LibcruxIotSha3.Foundation.ThetaLiftRound1
import LibcruxIotSha3.Foundation.ThetaLiftRound2
import LibcruxIotSha3.Foundation.ThetaLiftRound3
import LibcruxIotSha3.Foundation.PrcLift
import LibcruxIotSha3.Foundation.PrcLiftRound1
import LibcruxIotSha3.Foundation.PrcLiftRound2
import LibcruxIotSha3.Foundation.PrcLiftRound3
import LibcruxIotSha3.Foundation.Lift
import Hax

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Foundation

set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

/-! ## Chain wrapper for round-0 πρχι

`prc_lift_spec` is keyed on a 2-call do-block `(do prc_1; prc_2)`,
which mvcgen's `@[spec]` matcher does not auto-fire in chain context.
Wrapping the two calls in a named function lets the `@[spec]` matcher
fire on the chain inside `round0_equiv_spec`. -/

def keccakf1600_round0_pi_rho_chi_chain (s : state.KeccakState) :
    Result state.KeccakState := do
  let r1 ← keccak.keccakf1600_round0_pi_rho_chi_1 0#usize s
  keccak.keccakf1600_round0_pi_rho_chi_2 r1

@[spec]
theorem keccakf1600_round0_pi_rho_chi_chain_spec
    (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccakf1600_round0_pi_rho_chi_chain s
    ⦃ ⇓ r_impl => ⌜
      (do let a1 ← keccak_f.rho (lift_theta_applied s)
          let a2 ← keccak_f.pi a1
          let a3 ← keccak_f.chi a2
          let r_spec ← keccak_f.iota a3 s.i
          pure (r_spec = lift_perm r_impl impl_perm impl_swap)).holds ⌝ ⦄ := by
  unfold keccakf1600_round0_pi_rho_chi_chain
  exact prc_lift_spec s hi

/-- Spec-chain claim for round 0 (opaque to `mvcgen`). Wrapping the
    spec do-block in this `def` prevents `mvcgen` from trying to
    advance `wp⟦keccak_f.theta (lift s)⟧` in the post during impl
    advancement. -/
@[irreducible]
def round0_post (s : state.KeccakState) (r_impl : state.KeccakState) : Prop :=
  (do
    let s_theta ← keccak_f.theta (lift s)
    let s_rho ← keccak_f.rho s_theta
    let s_pi ← keccak_f.pi s_rho
    let s_chi ← keccak_f.chi s_pi
    let r_spec ← keccak_f.iota s_chi s.i
    pure (r_spec = lift_perm r_impl impl_perm impl_swap)).holds

set_option maxHeartbeats 16000000 in
theorem round0_equiv_spec (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round0_theta s
        keccakf1600_round0_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜round0_post s r_impl⌝ ⦄ := by
  hax_mvcgen
  all_goals first
    | scalar_tac
    | (casesm* _ ∧ _; scalar_tac)
    | (unfold round0_post
       -- Spec post is now `(do θ; ρ; π; χ; ι _ s.i).holds`.
       -- Use the chain hypotheses (already in scope from mvcgen's
       -- dispatch of chain_spec) to thread through each spec.
       casesm* _ ∧ _
       hax_mvcgen
       all_goals first | scalar_tac | simp_all)

/-! ## Chain wrappers + round equivs for rounds 1, 2, 3

Each round's chain wrapper packages `pi_rho_chi_1; pi_rho_chi_2` so the
`@[spec]` matcher can fire on a single named function. The post chains
the round-k spec via `theta_lift_spec_k` (auto-firing on the theta call)
+ `prc_lift_spec_k` (auto-firing via the chain wrapper).
-/

def keccakf1600_round1_pi_rho_chi_chain (s : state.KeccakState) :
    Result state.KeccakState := do
  let r1 ← keccak.keccakf1600_round1_pi_rho_chi_1 0#usize s
  keccak.keccakf1600_round1_pi_rho_chi_2 r1

@[spec]
theorem keccakf1600_round1_pi_rho_chi_chain_spec
    (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccakf1600_round1_pi_rho_chi_chain s
    ⦃ ⇓ r_impl => ⌜
      (do let a1 ← keccak_f.rho
            (lift_theta_applied_perm s impl_perm (impl_swap_k 1))
          let a2 ← keccak_f.pi a1
          let a3 ← keccak_f.chi a2
          let r_spec ← keccak_f.iota a3 s.i
          pure (r_spec = lift_perm r_impl (impl_perm ∘ impl_perm) (impl_swap_k 2))).holds ⌝ ⦄ := by
  unfold keccakf1600_round1_pi_rho_chi_chain
  exact prc_lift_spec_1 s hi

def keccakf1600_round2_pi_rho_chi_chain (s : state.KeccakState) :
    Result state.KeccakState := do
  let r1 ← keccak.keccakf1600_round2_pi_rho_chi_1 0#usize s
  keccak.keccakf1600_round2_pi_rho_chi_2 r1

@[spec]
theorem keccakf1600_round2_pi_rho_chi_chain_spec
    (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccakf1600_round2_pi_rho_chi_chain s
    ⦃ ⇓ r_impl => ⌜
      (do let a1 ← keccak_f.rho
            (lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2))
          let a2 ← keccak_f.pi a1
          let a3 ← keccak_f.chi a2
          let r_spec ← keccak_f.iota a3 s.i
          pure (r_spec = lift_perm r_impl
            (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))).holds ⌝ ⦄ := by
  unfold keccakf1600_round2_pi_rho_chi_chain
  exact prc_lift_spec_2 s hi

def keccakf1600_round3_pi_rho_chi_chain (s : state.KeccakState) :
    Result state.KeccakState := do
  let r1 ← keccak.keccakf1600_round3_pi_rho_chi_1 0#usize s
  keccak.keccakf1600_round3_pi_rho_chi_2 r1

@[spec]
theorem keccakf1600_round3_pi_rho_chi_chain_spec
    (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccakf1600_round3_pi_rho_chi_chain s
    ⦃ ⇓ r_impl => ⌜
      (do let a1 ← keccak_f.rho
            (lift_theta_applied_perm s
              (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))
          let a2 ← keccak_f.pi a1
          let a3 ← keccak_f.chi a2
          let r_spec ← keccak_f.iota a3 s.i
          -- Round 3 output uses canonical `lift` (= `lift_perm _ id swZero`,
          -- via `impl_perm^[4] = id` and `impl_swap_k 4 = swZero`).
          pure (r_spec = Foundation.lift r_impl)).holds ⌝ ⦄ := by
  unfold keccakf1600_round3_pi_rho_chi_chain
  exact prc_lift_spec_3 s hi

/-- Spec-chain claim for round 1 (input s is the round-0 impl output, so
    the spec lift uses `impl_perm` permutation + `impl_swap_k 1`, where
    `impl_swap_k 1 = impl_swap`). Output uses `impl_swap_k 2`. -/
@[irreducible]
def round1_post (s : state.KeccakState) (r_impl : state.KeccakState) : Prop :=
  (do
    let s_theta ← keccak_f.theta (lift_perm s impl_perm (impl_swap_k 1))
    let s_rho ← keccak_f.rho s_theta
    let s_pi ← keccak_f.pi s_rho
    let s_chi ← keccak_f.chi s_pi
    let r_spec ← keccak_f.iota s_chi s.i
    pure (r_spec = lift_perm r_impl (impl_perm ∘ impl_perm) (impl_swap_k 2))).holds

set_option maxHeartbeats 16000000 in
theorem round1_equiv_spec (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round1_theta s
        keccakf1600_round1_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜round1_post s r_impl⌝ ⦄ := by
  hax_mvcgen
  all_goals first
    | scalar_tac
    | (casesm* _ ∧ _; scalar_tac)
    | (unfold round1_post
       casesm* _ ∧ _
       hax_mvcgen
       all_goals first | scalar_tac | simp_all)

@[irreducible]
def round2_post (s : state.KeccakState) (r_impl : state.KeccakState) : Prop :=
  (do
    let s_theta ← keccak_f.theta
      (lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2))
    let s_rho ← keccak_f.rho s_theta
    let s_pi ← keccak_f.pi s_rho
    let s_chi ← keccak_f.chi s_pi
    let r_spec ← keccak_f.iota s_chi s.i
    pure (r_spec = lift_perm r_impl (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))).holds

set_option maxHeartbeats 16000000 in
theorem round2_equiv_spec (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round2_theta s
        keccakf1600_round2_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜round2_post s r_impl⌝ ⦄ := by
  hax_mvcgen
  all_goals first
    | scalar_tac
    | (casesm* _ ∧ _; scalar_tac)
    | (unfold round2_post
       casesm* _ ∧ _
       hax_mvcgen
       all_goals first | scalar_tac | simp_all)

@[irreducible]
def round3_post (s : state.KeccakState) (r_impl : state.KeccakState) : Prop :=
  (do
    let s_theta ← keccak_f.theta
      (lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))
    let s_rho ← keccak_f.rho s_theta
    let s_pi ← keccak_f.pi s_rho
    let s_chi ← keccak_f.chi s_pi
    let r_spec ← keccak_f.iota s_chi s.i
    -- Output uses `impl_swap_k 4 = (fun _ => false)`, i.e. the canonical
    -- `lift` (after `impl_perm^[4] = id`). Equivalent to `lift r_impl`.
    pure (r_spec = Foundation.lift r_impl)).holds

set_option maxHeartbeats 16000000 in
theorem round3_equiv_spec (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round3_theta s
        keccakf1600_round3_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜round3_post s r_impl⌝ ⦄ := by
  hax_mvcgen
  all_goals first
    | scalar_tac
    | (casesm* _ ∧ _; scalar_tac)
    | (unfold round3_post
       casesm* _ ∧ _
       hax_mvcgen
       all_goals first | scalar_tac | simp_all)

/-! ## Triple combinators

Used by the round-chain compositions in `StructuralEquiv.lean` and
`AlgebraicEquiv.lean` to combine per-round algebraic posts with
i-increment facts and to lift pure-prop preconditions into proof-context
hypotheses. -/

/-- For `Result α` (a deterministic monad), if two Triples prove distinct
posts about the same computation, their conjunction also holds. -/
theorem triple_conj_post {α} {e : Aeneas.Std.Result α} {Q R : α → Prop}
    (hQ : ⦃⌜True⌝⦄ e ⦃⇓ r => ⌜Q r⌝⦄)
    (hR : ⦃⌜True⌝⦄ e ⦃⇓ r => ⌜R r⌝⦄) :
    ⦃⌜True⌝⦄ e ⦃⇓ r => ⌜Q r ∧ R r⌝⦄ := by
  cases e
  · simp_all [Std.Do.Triple, WP.wp, PredTrans.apply]
  · simp_all [Std.Do.Triple, WP.wp, PredTrans.apply]
  · simp_all [Std.Do.Triple, WP.wp, PredTrans.apply]

/-- Lift a pure-prop precondition `⌜P⌝` of a `Triple` into a Lean-level
hypothesis. -/
theorem triple_imp_intro {α} {e : Aeneas.Std.Result α} {P : Prop} {Q : α → Prop}
    (h : P → ⦃⌜True⌝⦄ e ⦃⇓ r => ⌜Q r⌝⦄) :
    ⦃⌜P⌝⦄ e ⦃⇓ r => ⌜Q r⌝⦄ := by
  cases e
  · simp_all [Std.Do.Triple, WP.wp, PredTrans.apply]
  · simp_all [Std.Do.Triple, WP.wp, PredTrans.apply]
  · simp_all [Std.Do.Triple, WP.wp, PredTrans.apply]

end libcrux_iot_sha3.Foundation
