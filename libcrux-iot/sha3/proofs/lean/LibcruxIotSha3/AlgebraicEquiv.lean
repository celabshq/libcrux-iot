/-
  Algebraic equivalence: the pure-Lean `bit_keccak_spec` (from
  `BitSpec/Spec.lean`) equals the hacspec 24-round application under
  the canonical lift, modulo a time-varying half-swap polarity.

  Outline:

  1. Per-round step functions `bit_round0..3 : KState → KState` (composing
     `theta + pi_rho_chi_1 + pi_rho_chi_2` per round).
  2. `bit_keccakf1600_4rounds_eq_chain` (`bit_keccakf1600_4rounds 0 s =
     bit_round3 (bit_round2 (bit_round1 (bit_round0 s)))`) — by `rfl`,
     since both sides unfold to the same 12-call let-chain.
  3. KState round-trip `KState.toAeneas (KState.fromAeneas s) = s` — bridges
     the structural equivalence's pure-Lean output back into the Aeneas
     universe for the spec equation. Needed at the top-level composition
     (`Composition/ViaBit.lean`).
  4. Time-varying `impl_swap_k` polarity tracking (see
     `Foundation/Lift.lean`) — a 4-cycle
     `swZero → impl_swap → sw2 → sw3 → swZero` that tracks the actual
     polarity layout at each round. Both ends of a 4-round chunk use
     `impl_swap_k 0 = impl_swap_k 4 = (fun _ => false)`, so the canonical
     lift threads through unconditionally — no `BalancedAt k` precondition
     required.
  5. Per-round algebraic correspondence theorems
     `bit_round{k}_alg_eq` (k ∈ {0,1,2,3}) — the load-bearing algebra.
     Each says (unconditionally, no state precondition)
     `spec_round_step (lift_perm s.toAeneas (impl_perm^[k]) (impl_swap_k k)) s.i`
     `  = .ok (lift_perm (bit_round{k} s).toAeneas (impl_perm^[k+1]) (impl_swap_k (k+1)))`.
  6. 4-round closure `bit_4rounds_alg_eq` — composes the 4 per-round
     identities through `Result.bind`. Uses `impl_perm_pow4_eq_id`
     to collapse `impl_perm^[4]` to `id` and `impl_swap_k 4 = impl_swap_k 0`
     to close the swap cycle at the group boundary.
  7. 24-round closure `bit_keccak_spec_alg_eq` — 6-iteration induction
     over `Nat.iterate (bit_keccakf1600_4rounds 0) 6`. Threads the
     `s.i.val = 4k` chain (for iota constants); no `BalancedAt`
     invariant needed.

  Composition with the structural equivalence (impl ≡ `bit_keccak_spec`)
  to produce a Triple on `keccak.keccakf1600` lives in
  `Composition/ViaBit.lean`.
-/
import LibcruxIotSha3.StructuralEquiv
import LibcruxIotSha3.Foundation.SpecChain

namespace libcrux_iot_sha3.Algebraic

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 libcrux_iot_sha3.Foundation
open libcrux_iot_sha3.BitSpec
open libcrux_iot_sha3.Structural

/-! ## Per-round step on `KState` (theta + pi_rho_chi_1 + pi_rho_chi_2). -/

@[inline] def bit_round0 (s : KState) : KState :=
  let s1 := bit_keccakf1600_round0_theta s
  let s2 := bit_keccakf1600_round0_pi_rho_chi_1 0#usize s1
  bit_keccakf1600_round0_pi_rho_chi_2 s2

@[inline] def bit_round1 (s : KState) : KState :=
  let s1 := bit_keccakf1600_round1_theta s
  let s2 := bit_keccakf1600_round1_pi_rho_chi_1 0#usize s1
  bit_keccakf1600_round1_pi_rho_chi_2 s2

@[inline] def bit_round2 (s : KState) : KState :=
  let s1 := bit_keccakf1600_round2_theta s
  let s2 := bit_keccakf1600_round2_pi_rho_chi_1 0#usize s1
  bit_keccakf1600_round2_pi_rho_chi_2 s2

@[inline] def bit_round3 (s : KState) : KState :=
  let s1 := bit_keccakf1600_round3_theta s
  let s2 := bit_keccakf1600_round3_pi_rho_chi_1 0#usize s1
  bit_keccakf1600_round3_pi_rho_chi_2 s2

/-- `bit_keccakf1600_4rounds 0 = bit_round3 ∘ bit_round2 ∘ bit_round1 ∘ bit_round0`. -/
theorem bit_keccakf1600_4rounds_eq_chain (s : KState) :
    bit_keccakf1600_4rounds 0#usize s
    = bit_round3 (bit_round2 (bit_round1 (bit_round0 s))) := by
  rfl

/-! ## KState ↔ state.KeccakState round-trip

    Required for the top-level composition: the structural equivalence's `keccakf1600_eq`
    outputs `KState.fromAeneas r = bit_keccak_spec (KState.fromAeneas s)`,
    and the algebraic equivalence's `bit_keccak_alg_eq` reads its input via `KState.toAeneas`.
    The bridge `KState.toAeneas (KState.fromAeneas s) = s` (for the cases
    where the input is the impl's initial state with well-formed lanes)
    closes the loop. -/

theorem stateArray25_toAeneas_fromAeneas
    (a : Aeneas.Std.Array lane.Lane2U32 25#usize) :
    stateArray25ToAeneas (stateArray25FromAeneas a) = a := by
  obtain ⟨vals, hlen⟩ := a
  apply Subtype.ext
  show ((vals.map Lane.fromAeneas).toArray.toList.map Lane.toAeneas) = vals
  rw [List.toList_toArray, List.map_map]
  rw [show (Lane.toAeneas ∘ Lane.fromAeneas) = id from
        funext (fun l => Lane.toAeneas_fromAeneas l)]
  exact List.map_id vals

theorem stateArray5_toAeneas_fromAeneas
    (a : Aeneas.Std.Array lane.Lane2U32 5#usize) :
    stateArray5ToAeneas (stateArray5FromAeneas a) = a := by
  obtain ⟨vals, hlen⟩ := a
  apply Subtype.ext
  show ((vals.map Lane.fromAeneas).toArray.toList.map Lane.toAeneas) = vals
  rw [List.toList_toArray, List.map_map]
  rw [show (Lane.toAeneas ∘ Lane.fromAeneas) = id from
        funext (fun l => Lane.toAeneas_fromAeneas l)]
  exact List.map_id vals

theorem KState.toAeneas_fromAeneas (s : state.KeccakState) :
    KState.toAeneas (KState.fromAeneas s) = s := by
  unfold KState.toAeneas KState.fromAeneas
  rcases s with ⟨st, c, d, i⟩
  refine state.KeccakState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, rfl⟩
  · exact stateArray25_toAeneas_fromAeneas st
  · exact stateArray5_toAeneas_fromAeneas c
  · exact stateArray5_toAeneas_fromAeneas d

/-- Reverse round-trip: `KState.fromAeneas (KState.toAeneas s) = s`.
    Used by the algebraic correspondence proofs to turn the structural equivalence's
    bit-side equation `KState.fromAeneas r_impl = bit_round{k} (KState.fromAeneas s.toAeneas)`
    into `bit_round{k} s` (collapsing the inner round-trip). -/
theorem KState.fromAeneas_toAeneas (s : KState) :
    KState.fromAeneas (KState.toAeneas s) = s := by
  cases s
  simp [KState.fromAeneas, KState.toAeneas, stateArray25FromAeneas, stateArray25ToAeneas,
        stateArray5FromAeneas, stateArray5ToAeneas, Lane.fromAeneas_toAeneas, List.map_map,
        Function.comp_def]
  refine ⟨?_, ?_, ?_⟩
  all_goals (obtain ⟨_, _⟩ := ‹Vector _ _›; rfl)

/-! ## Per-round `s.i` increments on the bit side

    Each `bit_round{k}` bumps `s.i` by 1 (the `_zeta1` sub-piece in
    `pi_rho_chi_1` is the only one that increments). Used to thread the
    `s.i.val = 4 * group_idx + k` chain across the 4-round group. -/

/-- Converting `(⟨s.i.bv + 1⟩ : Std.Usize).val` to `s.i.val + 1` under
    a tame upper bound on `s.i.val`. The structural `_i` lemmas in
    `StructuralEquiv.lean` give the bit-side increment in `⟨_ + 1⟩` form;
    this bridges to `.val + 1` form. -/
private theorem usize_succ_val (s : Aeneas.Std.Usize) (hi : s.val < 24) :
    (⟨s.bv + (1 : BitVec System.Platform.numBits)⟩ : Aeneas.Std.Usize).val = s.val + 1 := by
  show (s.bv + (1 : BitVec System.Platform.numBits)).toNat = s.val + 1
  have h32 : (32 : Nat) ≤ System.Platform.numBits := by
    have := System.Platform.numBits_eq; omega
  have hone : (1 : BitVec System.Platform.numBits).toNat = 1 := by
    have h1 : (1 : Nat) % 2 ^ System.Platform.numBits = 1 := by
      apply Nat.mod_eq_of_lt
      have : (2 : Nat) ^ 32 ≤ 2 ^ System.Platform.numBits :=
        Nat.pow_le_pow_right (by decide) h32
      omega
    simp [BitVec.toNat_ofNat, h1]
  rw [BitVec.toNat_add, hone]
  apply Nat.mod_eq_of_lt
  have hsv : s.bv.toNat = s.val := rfl
  have : (2 : Nat) ^ 32 ≤ 2 ^ System.Platform.numBits :=
    Nat.pow_le_pow_right (by decide) h32
  rw [hsv]; omega

theorem bit_round0_i (s : KState) (hi : s.i.val < 24) :
    (bit_round0 s).i.val = s.i.val + 1 := by
  unfold bit_round0
  rw [bit_keccakf1600_round0_pi_rho_chi_2_i,
      bit_keccakf1600_round0_pi_rho_chi_1_i,
      bit_keccakf1600_round0_theta_i]
  exact usize_succ_val s.i hi

theorem bit_round1_i (s : KState) (hi : s.i.val < 24) :
    (bit_round1 s).i.val = s.i.val + 1 := by
  unfold bit_round1
  rw [bit_keccakf1600_round1_pi_rho_chi_2_i,
      bit_keccakf1600_round1_pi_rho_chi_1_i,
      bit_keccakf1600_round1_theta_i]
  exact usize_succ_val s.i hi

theorem bit_round2_i (s : KState) (hi : s.i.val < 24) :
    (bit_round2 s).i.val = s.i.val + 1 := by
  unfold bit_round2
  rw [bit_keccakf1600_round2_pi_rho_chi_2_i,
      bit_keccakf1600_round2_pi_rho_chi_1_i,
      bit_keccakf1600_round2_theta_i]
  exact usize_succ_val s.i hi

theorem bit_round3_i (s : KState) (hi : s.i.val < 24) :
    (bit_round3 s).i.val = s.i.val + 1 := by
  unfold bit_round3
  rw [bit_keccakf1600_round3_pi_rho_chi_2_i,
      bit_keccakf1600_round3_pi_rho_chi_1_i,
      bit_keccakf1600_round3_theta_i]
  exact usize_succ_val s.i hi

/-! ## Time-varying polarity tracking (no `BalancedAt` precondition)

    Polarity is tracked by the time-varying `impl_swap_k` in
    `Foundation/Lift.lean`: a 4-cycle
    `swZero → impl_swap → sw2 → sw3 → swZero` that records the actual
    polarity layout at each round so the canonical lift recovers the
    spec U64.

    With `impl_swap_k`, the per-round identities hold **unconditionally**.
    Both the start and the end of a 4-round chunk use
    `impl_swap_k 0 = impl_swap_k 4 = (fun _ => false)`, so
    `lift_perm s id (impl_swap_k 0) = lift s` — the canonical lift
    threads cleanly through the 24-round chain with no `BalancedAt`. -/

/-! ## Per-round algebraic correspondence (unconditional).

    Statement shape (for k ∈ {0,1,2,3}):

    `spec_round_step (lift_perm s.toAeneas (impl_perm^[k]) (impl_swap_k k)) s.i`
    `  = .ok (lift_perm (bit_round{k} s).toAeneas (impl_perm^[k+1]) (impl_swap_k (k+1)))`

    The bit-side `bit_round{k}` propagates the time-varying polarity
    pattern; the canonical lift reads the impl-side state with the
    correct swap-set at each round. No precondition on the state. -/

/-! ### Generic extractors

    Each round's algebra proof uses the same pattern: combine the spec
    `round{k}_equiv_spec` Triple with the structural-side chain Triple
    `round{k}_full_bit_eq`, weaken the post into the goal Prop, and
    extract via `triple_imp_prop` (a Triple whose post is a
    `r`-independent Prop yields the Prop). -/

/-- From a Triple whose post is a `r`-independent Prop, derive the Prop.
    Works because in the `Result α` tower with `noThrow` post, `.fail`/`.div`
    cases force the post to hold vacuously *with `False`*, so the only way
    the Triple holds is via the success case satisfying `P`. -/
private theorem triple_imp_prop {α : Type} {C : Aeneas.Std.Result α} {P : Prop}
    (h : ⦃⌜True⌝⦄ C ⦃⇓ _ => ⌜P⌝⦄) : P := by
  cases C
  all_goals simp_all [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.apply, Std.Do.SPred.down_pure]

/-! ### Round-0 chain Triple (bit-side equivalence over the 3-step impl) -/

/-- Structural side bundled at the 3-step round-0 chain: the impl call
    `do { theta; prc_1; prc_2 }` on `s` produces some `r` such that
    `KState.fromAeneas r = bit_round0 (KState.fromAeneas s)`.

    Chains `keccakf1600_round0_theta_eq` + `..._pi_rho_chi_1_eq` +
    `..._pi_rho_chi_2_eq` via `Std.Do.Triple.bind`, threading
    `s_after_theta.i.val < 24` (derived from the bit-side post via
    `bit_keccakf1600_round0_theta_i`) into the `pi_rho_chi_1`
    precondition. -/
private theorem round0_full_bit_eq (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃⌜True⌝⦄
    (do let s1 ← keccak.keccakf1600_round0_theta s
        keccakf1600_round0_pi_rho_chi_chain s1)
    ⦃⇓ r => ⌜KState.fromAeneas r = bit_round0 (KState.fromAeneas s)⌝⦄ := by
  apply Std.Do.Triple.bind _ _ (keccakf1600_round0_theta_eq s)
  intro s1
  apply triple_imp_intro
  intro h_theta
  -- Derive s1.i = s.i from the bit-side equation + bit_keccakf1600_round0_theta_i.
  have h_s1_i : s1.i = s.i := by
    have h : (KState.fromAeneas s1).i = (bit_keccakf1600_round0_theta (KState.fromAeneas s)).i :=
      congrArg (·.i) h_theta
    rw [bit_keccakf1600_round0_theta_i] at h
    exact h
  unfold keccakf1600_round0_pi_rho_chi_chain
  apply Std.Do.Triple.bind _ _
    (keccakf1600_round0_pi_rho_chi_1_eq 0#usize s1 (by rw [h_s1_i]; exact hi))
  intro s2
  apply triple_imp_intro
  intro h_prc1
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_round0_pi_rho_chi_2_eq s2)
  rw [PostCond.entails_noThrow]
  intro r h_prc2
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_prc2 ⊢
  unfold bit_round0
  rw [h_prc2, h_prc1, h_theta]

/-- Round 0 algebraic equivalence (unconditional). Composes
    `round0_equiv_spec` (impl ⇔ spec `θ;ρ;π;χ;ι`) with the structural equivalence's
    bit-side chain Triple `round0_full_bit_eq`. Input convention is
    `impl_swap_k 0 = (fun _ => false)`, i.e. the canonical `lift`;
    output convention is `impl_swap_k 1 = impl_swap`, matching the
    existing `round0_post`. -/
theorem bit_round0_alg_eq (s : KState) (hi : s.i.val < 24) :
    spec_round_step (lift s.toAeneas) s.i
    = .ok (lift_perm (bit_round0 s).toAeneas impl_perm impl_swap) := by
  apply triple_imp_prop
  apply Std.Do.Triple.of_entails_right _
    (triple_conj_post (round0_equiv_spec s.toAeneas hi) (round0_full_bit_eq s.toAeneas hi))
  rw [PostCond.entails_noThrow]
  intro r ⟨h_round0_post, h_from_eq⟩
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_round0_post h_from_eq ⊢
  have h_r_eq : r = (bit_round0 s).toAeneas := by
    rw [← KState.toAeneas_fromAeneas r, h_from_eq, KState.fromAeneas_toAeneas]
  unfold round0_post at h_round0_post
  have h_spec_eq : spec_round_step (Foundation.lift s.toAeneas) s.toAeneas.i
                 = .ok (lift_perm r impl_perm impl_swap) := by
    -- Use `theta_spec`, `rho_spec`, `pi_spec`, `chi_spec` and the `iota` def
    -- to drive `spec_round_step` to `.ok`, then `holds_chain_eq_ok` on the
    -- final pure-eq form.
    unfold spec_round_step
    rw [result_eq_of_triple (theta_spec _)]
    simp only [bind_tc_ok]
    rw [result_eq_of_triple (rho_spec _)]
    simp only [bind_tc_ok]
    rw [result_eq_of_triple (pi_spec _)]
    simp only [bind_tc_ok]
    rw [result_eq_of_triple (chi_spec _)]
    simp only [bind_tc_ok]
    -- Now goal: `keccak_f.iota (chi_applied (pi_applied (rho_applied (theta_applied (lift s))))) s.i = .ok ...`
    -- The hypothesis h_round0_post is the same chain wrapped with `pure (r_spec = X)`.
    -- Apply the same rewrites on h_round0_post and extract via holds_chain_eq_ok.
    rw [result_eq_of_triple (theta_spec _)] at h_round0_post
    simp only [bind_tc_ok] at h_round0_post
    rw [result_eq_of_triple (rho_spec _)] at h_round0_post
    simp only [bind_tc_ok] at h_round0_post
    rw [result_eq_of_triple (pi_spec _)] at h_round0_post
    simp only [bind_tc_ok] at h_round0_post
    rw [result_eq_of_triple (chi_spec _)] at h_round0_post
    simp only [bind_tc_ok] at h_round0_post
    exact holds_chain_eq_ok h_round0_post
  show spec_round_step (Foundation.lift s.toAeneas) s.i
     = .ok (lift_perm (bit_round0 s).toAeneas impl_perm impl_swap)
  rw [show s.i = s.toAeneas.i from rfl, h_spec_eq, h_r_eq]

/-! ### Round-1 chain Triple (bit-side equivalence over the 3-step impl) -/

private theorem round1_full_bit_eq (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃⌜True⌝⦄
    (do let s1 ← keccak.keccakf1600_round1_theta s
        keccakf1600_round1_pi_rho_chi_chain s1)
    ⦃⇓ r => ⌜KState.fromAeneas r = bit_round1 (KState.fromAeneas s)⌝⦄ := by
  apply Std.Do.Triple.bind _ _ (keccakf1600_round1_theta_eq s)
  intro s1
  apply triple_imp_intro
  intro h_theta
  have h_s1_i : s1.i = s.i := by
    have h : (KState.fromAeneas s1).i = (bit_keccakf1600_round1_theta (KState.fromAeneas s)).i :=
      congrArg (·.i) h_theta
    rw [bit_keccakf1600_round1_theta_i] at h
    exact h
  unfold keccakf1600_round1_pi_rho_chi_chain
  apply Std.Do.Triple.bind _ _
    (keccakf1600_round1_pi_rho_chi_1_eq 0#usize s1 (by rw [h_s1_i]; exact hi))
  intro s2
  apply triple_imp_intro
  intro h_prc1
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_round1_pi_rho_chi_2_eq s2)
  rw [PostCond.entails_noThrow]
  intro r h_prc2
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_prc2 ⊢
  unfold bit_round1
  rw [h_prc2, h_prc1, h_theta]

/-- Round 1 algebraic equivalence (unconditional). Input convention
    `impl_swap_k 1 = impl_swap`, output `impl_swap_k 2`. -/
theorem bit_round1_alg_eq (s : KState) (hi : s.i.val < 24) :
    spec_round_step (lift_perm s.toAeneas impl_perm (impl_swap_k 1)) s.i
    = .ok (lift_perm (bit_round1 s).toAeneas (impl_perm ∘ impl_perm) (impl_swap_k 2)) := by
  apply triple_imp_prop
  apply Std.Do.Triple.of_entails_right _
    (triple_conj_post (round1_equiv_spec s.toAeneas hi) (round1_full_bit_eq s.toAeneas hi))
  rw [PostCond.entails_noThrow]
  intro r ⟨h_round1_post, h_from_eq⟩
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_round1_post h_from_eq ⊢
  have h_r_eq : r = (bit_round1 s).toAeneas := by
    rw [← KState.toAeneas_fromAeneas r, h_from_eq, KState.fromAeneas_toAeneas]
  unfold round1_post at h_round1_post
  have h_spec_eq : spec_round_step (lift_perm s.toAeneas impl_perm (impl_swap_k 1)) s.toAeneas.i
                 = .ok (lift_perm r (impl_perm ∘ impl_perm) (impl_swap_k 2)) := by
    unfold spec_round_step
    rw [result_eq_of_triple (theta_spec _)]; simp only [bind_tc_ok]
    rw [result_eq_of_triple (rho_spec _)]; simp only [bind_tc_ok]
    rw [result_eq_of_triple (pi_spec _)]; simp only [bind_tc_ok]
    rw [result_eq_of_triple (chi_spec _)]; simp only [bind_tc_ok]
    rw [result_eq_of_triple (theta_spec _)] at h_round1_post
    simp only [bind_tc_ok] at h_round1_post
    rw [result_eq_of_triple (rho_spec _)] at h_round1_post
    simp only [bind_tc_ok] at h_round1_post
    rw [result_eq_of_triple (pi_spec _)] at h_round1_post
    simp only [bind_tc_ok] at h_round1_post
    rw [result_eq_of_triple (chi_spec _)] at h_round1_post
    simp only [bind_tc_ok] at h_round1_post
    exact holds_chain_eq_ok h_round1_post
  show spec_round_step (lift_perm s.toAeneas impl_perm (impl_swap_k 1)) s.i
     = .ok (lift_perm (bit_round1 s).toAeneas (impl_perm ∘ impl_perm) (impl_swap_k 2))
  rw [show s.i = s.toAeneas.i from rfl, h_spec_eq, h_r_eq]

/-! ### Round-2 chain Triple (bit-side equivalence over the 3-step impl) -/

private theorem round2_full_bit_eq (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃⌜True⌝⦄
    (do let s1 ← keccak.keccakf1600_round2_theta s
        keccakf1600_round2_pi_rho_chi_chain s1)
    ⦃⇓ r => ⌜KState.fromAeneas r = bit_round2 (KState.fromAeneas s)⌝⦄ := by
  apply Std.Do.Triple.bind _ _ (keccakf1600_round2_theta_eq s)
  intro s1
  apply triple_imp_intro
  intro h_theta
  have h_s1_i : s1.i = s.i := by
    have h : (KState.fromAeneas s1).i = (bit_keccakf1600_round2_theta (KState.fromAeneas s)).i :=
      congrArg (·.i) h_theta
    rw [bit_keccakf1600_round2_theta_i] at h
    exact h
  unfold keccakf1600_round2_pi_rho_chi_chain
  apply Std.Do.Triple.bind _ _
    (keccakf1600_round2_pi_rho_chi_1_eq 0#usize s1 (by rw [h_s1_i]; exact hi))
  intro s2
  apply triple_imp_intro
  intro h_prc1
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_round2_pi_rho_chi_2_eq s2)
  rw [PostCond.entails_noThrow]
  intro r h_prc2
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_prc2 ⊢
  unfold bit_round2
  rw [h_prc2, h_prc1, h_theta]

/-- Round 2 algebraic equivalence (unconditional). Input `impl_swap_k 2`,
    output `impl_swap_k 3`. -/
theorem bit_round2_alg_eq (s : KState) (hi : s.i.val < 24) :
    spec_round_step
        (lift_perm s.toAeneas (impl_perm ∘ impl_perm) (impl_swap_k 2)) s.i
    = .ok (lift_perm (bit_round2 s).toAeneas
              (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) := by
  apply triple_imp_prop
  apply Std.Do.Triple.of_entails_right _
    (triple_conj_post (round2_equiv_spec s.toAeneas hi) (round2_full_bit_eq s.toAeneas hi))
  rw [PostCond.entails_noThrow]
  intro r ⟨h_round2_post, h_from_eq⟩
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_round2_post h_from_eq ⊢
  have h_r_eq : r = (bit_round2 s).toAeneas := by
    rw [← KState.toAeneas_fromAeneas r, h_from_eq, KState.fromAeneas_toAeneas]
  unfold round2_post at h_round2_post
  have h_spec_eq :
      spec_round_step (lift_perm s.toAeneas (impl_perm ∘ impl_perm) (impl_swap_k 2)) s.toAeneas.i
        = .ok (lift_perm r (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) := by
    unfold spec_round_step
    rw [result_eq_of_triple (theta_spec _)]; simp only [bind_tc_ok]
    rw [result_eq_of_triple (rho_spec _)]; simp only [bind_tc_ok]
    rw [result_eq_of_triple (pi_spec _)]; simp only [bind_tc_ok]
    rw [result_eq_of_triple (chi_spec _)]; simp only [bind_tc_ok]
    rw [result_eq_of_triple (theta_spec _)] at h_round2_post
    simp only [bind_tc_ok] at h_round2_post
    rw [result_eq_of_triple (rho_spec _)] at h_round2_post
    simp only [bind_tc_ok] at h_round2_post
    rw [result_eq_of_triple (pi_spec _)] at h_round2_post
    simp only [bind_tc_ok] at h_round2_post
    rw [result_eq_of_triple (chi_spec _)] at h_round2_post
    simp only [bind_tc_ok] at h_round2_post
    exact holds_chain_eq_ok h_round2_post
  show spec_round_step (lift_perm s.toAeneas (impl_perm ∘ impl_perm) (impl_swap_k 2)) s.i
     = .ok (lift_perm (bit_round2 s).toAeneas (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))
  rw [show s.i = s.toAeneas.i from rfl, h_spec_eq, h_r_eq]

/-! ### Round-3 chain Triple (bit-side equivalence over the 3-step impl) -/

private theorem round3_full_bit_eq (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃⌜True⌝⦄
    (do let s1 ← keccak.keccakf1600_round3_theta s
        keccakf1600_round3_pi_rho_chi_chain s1)
    ⦃⇓ r => ⌜KState.fromAeneas r = bit_round3 (KState.fromAeneas s)⌝⦄ := by
  apply Std.Do.Triple.bind _ _ (keccakf1600_round3_theta_eq s)
  intro s1
  apply triple_imp_intro
  intro h_theta
  have h_s1_i : s1.i = s.i := by
    have h : (KState.fromAeneas s1).i = (bit_keccakf1600_round3_theta (KState.fromAeneas s)).i :=
      congrArg (·.i) h_theta
    rw [bit_keccakf1600_round3_theta_i] at h
    exact h
  unfold keccakf1600_round3_pi_rho_chi_chain
  apply Std.Do.Triple.bind _ _
    (keccakf1600_round3_pi_rho_chi_1_eq 0#usize s1 (by rw [h_s1_i]; exact hi))
  intro s2
  apply triple_imp_intro
  intro h_prc1
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_round3_pi_rho_chi_2_eq s2)
  rw [PostCond.entails_noThrow]
  intro r h_prc2
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_prc2 ⊢
  unfold bit_round3
  rw [h_prc2, h_prc1, h_theta]

/-- Round 3 algebraic equivalence (unconditional). Input `impl_swap_k 3`,
    output `impl_swap_k 4 = (fun _ => false)`. With
    `impl_perm^[4] = id`, the output collapses to `lift (bit_round3 s).toAeneas`. -/
theorem bit_round3_alg_eq (s : KState) (hi : s.i.val < 24) :
    spec_round_step
        (lift_perm s.toAeneas (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) s.i
    = .ok (lift (bit_round3 s).toAeneas) := by
  apply triple_imp_prop
  apply Std.Do.Triple.of_entails_right _
    (triple_conj_post (round3_equiv_spec s.toAeneas hi) (round3_full_bit_eq s.toAeneas hi))
  rw [PostCond.entails_noThrow]
  intro r ⟨h_round3_post, h_from_eq⟩
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_round3_post h_from_eq ⊢
  have h_r_eq : r = (bit_round3 s).toAeneas := by
    rw [← KState.toAeneas_fromAeneas r, h_from_eq, KState.fromAeneas_toAeneas]
  unfold round3_post at h_round3_post
  have h_spec_eq :
      spec_round_step
          (lift_perm s.toAeneas (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) s.toAeneas.i
        = .ok (Foundation.lift r) := by
    unfold spec_round_step
    rw [result_eq_of_triple (theta_spec _)]; simp only [bind_tc_ok]
    rw [result_eq_of_triple (rho_spec _)]; simp only [bind_tc_ok]
    rw [result_eq_of_triple (pi_spec _)]; simp only [bind_tc_ok]
    rw [result_eq_of_triple (chi_spec _)]; simp only [bind_tc_ok]
    rw [result_eq_of_triple (theta_spec _)] at h_round3_post
    simp only [bind_tc_ok] at h_round3_post
    rw [result_eq_of_triple (rho_spec _)] at h_round3_post
    simp only [bind_tc_ok] at h_round3_post
    rw [result_eq_of_triple (pi_spec _)] at h_round3_post
    simp only [bind_tc_ok] at h_round3_post
    rw [result_eq_of_triple (chi_spec _)] at h_round3_post
    simp only [bind_tc_ok] at h_round3_post
    exact holds_chain_eq_ok h_round3_post
  show spec_round_step
          (lift_perm s.toAeneas (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) s.i
        = .ok (Foundation.lift (bit_round3 s).toAeneas)
  rw [show s.i = s.toAeneas.i from rfl, h_spec_eq, h_r_eq]

/-! ## 4-round closure (unconditional)

    Composes the 4 per-round algebraic identities via `Result.bind`
    associativity. Uses the i-increment chain to align iota constants.
    Start and end both use the canonical `lift` (since
    `impl_swap_k 0 = impl_swap_k 4 = (fun _ => false)`). -/

set_option maxHeartbeats 4000000 in
theorem bit_4rounds_alg_eq (s : KState) (hi : s.i.val + 4 ≤ 24) :
    (do
      let s1 ← spec_round_step (lift s.toAeneas) s.i
      let s2 ← spec_round_step s1 (roundOfNat (s.i.val + 1) (by omega))
      let s3 ← spec_round_step s2 (roundOfNat (s.i.val + 2) (by omega))
      spec_round_step s3 (roundOfNat (s.i.val + 3) (by omega)))
    = .ok (lift (bit_keccakf1600_4rounds 0#usize s).toAeneas) := by
  rw [bit_keccakf1600_4rounds_eq_chain]
  -- Round 0: input convention `impl_swap_k 0 = (fun _ => false)` ↔ `lift`.
  have h0 := bit_round0_alg_eq s (by omega)
  rw [h0]; simp only [Aeneas.Std.bind_tc_ok]
  -- Round 1: align iota constant via i-chain; input `impl_swap_k 1 = impl_swap`.
  have h_i0_val : (bit_round0 s).i.val = s.i.val + 1 := bit_round0_i s (by omega)
  have h_i1 : (bit_round0 s).i = roundOfNat (s.i.val + 1) (by omega) := by
    apply Std.UScalar.eq_of_val_eq
    rw [h_i0_val]
    unfold roundOfNat; rw [Std.UScalar.ofNatCore_val_eq]
  have h1 := bit_round1_alg_eq (bit_round0 s) (by rw [h_i0_val]; omega)
  -- `impl_swap_k 1 = impl_swap` (definitional via `impl_swap_k_one`).
  rw [show (impl_swap_k 1 : Fin 25 → Bool) = impl_swap from
        funext (fun L => impl_swap_k_one L)] at h1
  rw [← h_i1, h1]; simp only [Aeneas.Std.bind_tc_ok]
  -- Round 2
  have h_i1_val : (bit_round1 (bit_round0 s)).i.val = s.i.val + 2 := by
    rw [bit_round1_i _ (by rw [h_i0_val]; omega), h_i0_val]
  have h_i2 : (bit_round1 (bit_round0 s)).i = roundOfNat (s.i.val + 2) (by omega) := by
    apply Std.UScalar.eq_of_val_eq
    rw [h_i1_val]
    unfold roundOfNat; rw [Std.UScalar.ofNatCore_val_eq]
  have h2 := bit_round2_alg_eq (bit_round1 (bit_round0 s)) (by rw [h_i1_val]; omega)
  rw [← h_i2, h2]; simp only [Aeneas.Std.bind_tc_ok]
  -- Round 3: output uses `lift` (since `impl_swap_k 4 = false` and `impl_perm^[4] = id`).
  have h_i2_val : (bit_round2 (bit_round1 (bit_round0 s))).i.val = s.i.val + 3 := by
    rw [bit_round2_i _ (by rw [h_i1_val]; omega), h_i1_val]
  have h_i3 : (bit_round2 (bit_round1 (bit_round0 s))).i = roundOfNat (s.i.val + 3) (by omega) := by
    apply Std.UScalar.eq_of_val_eq
    rw [h_i2_val]
    unfold roundOfNat; rw [Std.UScalar.ofNatCore_val_eq]
  have h3 := bit_round3_alg_eq (bit_round2 (bit_round1 (bit_round0 s)))
    (by rw [h_i2_val]; omega)
  rw [← h_i3, h3]

set_option maxHeartbeats 2000000 in
/-- Index-parameterized variant of `bit_4rounds_alg_eq`. -/
theorem bit_4rounds_alg_eq_at (s : KState) (n : Nat) (h_n : n + 4 ≤ 24)
    (h_i : n = s.i.val) :
    (do
      let s1 ← spec_round_step (lift s.toAeneas)
                  (roundOfNat n (by omega))
      let s2 ← spec_round_step s1 (roundOfNat (n + 1) (by omega))
      let s3 ← spec_round_step s2 (roundOfNat (n + 2) (by omega))
      spec_round_step s3 (roundOfNat (n + 3) (by omega)))
    = .ok (lift (bit_keccakf1600_4rounds 0#usize s).toAeneas) := by
  subst h_i
  have h_chain := bit_4rounds_alg_eq s h_n
  have h_si_eq : roundOfNat s.i.val (by omega) = s.i := by
    apply Std.UScalar.eq_of_val_eq
    unfold roundOfNat; rw [Std.UScalar.ofNatCore_val_eq]
  rw [h_si_eq]
  exact h_chain

/-! ## i-increment for `bit_keccakf1600_4rounds` -/

theorem bit_keccakf1600_4rounds_i (s : KState) (hi : s.i.val + 4 ≤ 24) :
    (bit_keccakf1600_4rounds 0#usize s).i.val = s.i.val + 4 := by
  rw [bit_keccakf1600_4rounds_eq_chain]
  have h0 : (bit_round0 s).i.val = s.i.val + 1 := bit_round0_i s (by omega)
  have h1 : (bit_round1 (bit_round0 s)).i.val = s.i.val + 2 := by
    rw [bit_round1_i _ (by rw [h0]; omega), h0]
  have h2 : (bit_round2 (bit_round1 (bit_round0 s))).i.val = s.i.val + 3 := by
    rw [bit_round2_i _ (by rw [h1]; omega), h1]
  rw [bit_round3_i _ (by rw [h2]; omega), h2]

/-! ## 24-round closure (the top-level algebraic equivalence target)

    Induct over 6 iterations of `bit_keccakf1600_4rounds 0`, threading
    the `s.i.val = 4k` chain to align spec_round_step indices. -/

private theorem nat_iterate_i (s : KState) (h_i : s.i.val = 0) (k : Nat) (hk : k ≤ 6) :
    (Nat.iterate (bit_keccakf1600_4rounds 0#usize) k s).i.val = 4 * k := by
  induction k with
  | zero => simpa using h_i
  | succ n IH =>
    have hn : n ≤ 6 := by omega
    have hIH := IH hn
    rw [Function.iterate_succ_apply']
    rw [bit_keccakf1600_4rounds_i _ (by rw [hIH]; omega)]
    rw [hIH]; ring

set_option maxHeartbeats 4000000 in
/-- The 24-round algebraic closure on the pure-Lean side (unconditional).
    With the time-varying `impl_swap_k` cycle, no `BalancedAt`
    precondition is needed — both ends of each 4-round chunk use the
    canonical `lift` view. -/
theorem bit_keccak_spec_alg_eq (s : KState) (h_i : s.i = 0#usize) :
    spec_chain (lift s.toAeneas) 24
    = .ok (lift (Nat.iterate (bit_keccakf1600_4rounds 0#usize) 6 s).toAeneas) := by
  have h_i_val : s.i.val = 0 := by rw [h_i]; rfl
  suffices h : ∀ k ≤ 6,
      spec_chain (lift s.toAeneas) (4 * k)
      = .ok (lift (Nat.iterate (bit_keccakf1600_4rounds 0#usize) k s).toAeneas) by
    have h6 := h 6 (by omega)
    rw [show (24 : Nat) = 4 * 6 from rfl]; exact h6
  intro k hk
  induction k with
  | zero =>
    simp only [Nat.mul_zero, spec_chain_zero, Function.iterate_zero, id_eq]
  | succ n IH =>
    have hn : n ≤ 6 := by omega
    have IH' := IH hn
    rw [show 4 * (n + 1) = 4 * n + 4 from by ring]
    rw [show 4 * n + 4 = (4 * n + 3) + 1 from rfl, spec_chain_succ]
    rw [show 4 * n + 3 = (4 * n + 2) + 1 from rfl, spec_chain_succ]
    rw [show 4 * n + 2 = (4 * n + 1) + 1 from rfl, spec_chain_succ]
    rw [show 4 * n + 1 = 4 * n + 1 from rfl, spec_chain_succ]
    rw [IH']
    simp only [Aeneas.Std.bind_tc_ok]
    rw [Function.iterate_succ_apply']
    have h_acc_i_val : (Nat.iterate (bit_keccakf1600_4rounds 0#usize) n s).i.val = 4 * n :=
      nat_iterate_i s h_i_val n hn
    have h_acc_i_bnd : (Nat.iterate (bit_keccakf1600_4rounds 0#usize) n s).i.val + 4 ≤ 24 := by
      rw [h_acc_i_val]; omega
    set acc := Nat.iterate (bit_keccakf1600_4rounds 0#usize) n s
    have h_chain := bit_4rounds_alg_eq_at acc (4 * n) (by omega) h_acc_i_val.symm
    unfold spec_round_step_at
    simp only [show (4 * n + 1 + 1 : Nat) = 4 * n + 2 from rfl,
               show (4 * n + 1 + 1 + 1 : Nat) = 4 * n + 3 from rfl,
               dif_pos (show 4 * n < 24 by omega),
               dif_pos (show 4 * n + 1 < 24 by omega),
               dif_pos (show 4 * n + 2 < 24 by omega),
               dif_pos (show 4 * n + 3 < 24 by omega),
               bind_assoc]
    exact h_chain
end libcrux_iot_sha3.Algebraic
