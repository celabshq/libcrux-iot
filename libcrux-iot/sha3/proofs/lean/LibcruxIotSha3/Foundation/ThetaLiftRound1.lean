/-
  Round-1 θ lift spec.

  Round k's theta operates on a state in round-(k-1) layout. The spec
  side feeds in `lift_perm s (impl_perm^k) (impl_swap_k k)`. For k=1
  that's `lift_perm s impl_perm impl_swap` (since `impl_swap_k 1 = impl_swap`).
  Theta does not pi-permute, so the output is in the same
  `(impl_perm^k, impl_swap_k k)` layout as the input — encoded as
  `lift_theta_applied_perm` on the post-theta impl state, with the same
  `(p, sw)` arguments.

  ## Architecture (transcribed from `ThetaLiftDefs.lean` + `ThetaLift.lean`)

  - 10 per-c-cell sub-fn specs `theta_c_x{0..4}_z{0,1}_spec_1`: each
    reads 5 swap-aware `s.st` halves matching `impl_swap` at the
    `impl_perm`-image of the spec column's 5 indices.
  - `theta_d_spec_1` matches round 0 (theta_d reads s.c canonically).
  - `theta_comp_spec_local_1` chains all 11 sub-fn specs.
  - 25 `lift_perm_getElem_bv_*` peel lemmas exposing the swap-aware
    spec-input lane reads.
  - `theta_lift_spec_1` then closes with the same `Subtype.ext` +
    25-cell `congr` strategy as round 0, but on the `_perm`-shaped RHS.
-/
import LibcruxIotSha3.Foundation.ThetaLift

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Foundation

set_option mvcgen.warning false

attribute [local spec] Aeneas.Std.uncurry

attribute [local irreducible] spread_to_even lift_lane_bv

/-! ## Round-1 per-c-cell sub-function specs

Each round-1 `theta_c_x{X}_z{Z}` reads 5 `s.st` halves with a
swap-aware pattern: for spec column index X, the impl reads at
positions `impl_perm(5*X + i)` for `i ∈ [0..5]`, with the `Z`-th
half polarity adjusted by `impl_swap` at each position.

The XOR order below mirrors the impl read order so that mvcgen's
literal XOR chain matches structurally. -/

@[spec]
private theorem theta_c_x0_z0_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 0#usize ((s.c.val[0]!).set 0#usize
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[0]! ^^^
           s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
           s.st.val[4]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round1_theta_c_x0_z0

@[spec]
private theorem theta_c_x0_z1_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 0#usize ((s.c.val[0]!).set 1#usize
          (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[1]! ^^^
           s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
           s.st.val[4]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round1_theta_c_x0_z1

@[spec]
private theorem theta_c_x1_z0_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 1#usize ((s.c.val[1]!).set 0#usize
          (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[0]! ^^^
           s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[1]! ^^^
           s.st.val[9]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round1_theta_c_x1_z0

@[spec]
private theorem theta_c_x1_z1_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 1#usize ((s.c.val[1]!).set 1#usize
          (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[1]! ^^^
           s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[0]! ^^^
           s.st.val[9]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round1_theta_c_x1_z1

@[spec]
private theorem theta_c_x2_z0_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 2#usize ((s.c.val[2]!).set 0#usize
          (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
           s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[1]! ^^^
           s.st.val[14]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round1_theta_c_x2_z0

@[spec]
private theorem theta_c_x2_z1_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 2#usize ((s.c.val[2]!).set 1#usize
          (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
           s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[0]! ^^^
           s.st.val[14]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round1_theta_c_x2_z1

@[spec]
private theorem theta_c_x3_z0_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 3#usize ((s.c.val[3]!).set 0#usize
          (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[1]! ^^^
           s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[1]! ^^^
           s.st.val[19]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round1_theta_c_x3_z0

@[spec]
private theorem theta_c_x3_z1_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 3#usize ((s.c.val[3]!).set 1#usize
          (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[0]! ^^^
           s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[0]! ^^^
           s.st.val[19]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round1_theta_c_x3_z1

@[spec]
private theorem theta_c_x4_z0_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 4#usize ((s.c.val[4]!).set 0#usize
          (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[0]! ^^^
           s.st.val[24]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round1_theta_c_x4_z0

@[spec]
private theorem theta_c_x4_z1_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 4#usize ((s.c.val[4]!).set 1#usize
          (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[1]! ^^^
           s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[1]! ^^^
           s.st.val[24]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round1_theta_c_x4_z1

/-! Round-1 `theta_d` overwrites `s.d` from the existing `s.c` cells.
    Same control shape as round 0 (theta_d uses c-cells canonically). -/

set_option maxHeartbeats 1600000 in
@[spec]
private theorem theta_d_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_theta_d s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.c = s.c ∧
        r.d.val[0]!.val[0]! =
          s.c.val[4]!.val[0]! ^^^ rot32 s.c.val[1]!.val[1]! 1 ∧
        r.d.val[0]!.val[1]! =
          s.c.val[4]!.val[1]! ^^^ s.c.val[1]!.val[0]! ∧
        r.d.val[1]!.val[0]! =
          s.c.val[0]!.val[0]! ^^^ rot32 s.c.val[2]!.val[1]! 1 ∧
        r.d.val[1]!.val[1]! =
          s.c.val[0]!.val[1]! ^^^ s.c.val[2]!.val[0]! ∧
        r.d.val[2]!.val[0]! =
          s.c.val[1]!.val[0]! ^^^ rot32 s.c.val[3]!.val[1]! 1 ∧
        r.d.val[2]!.val[1]! =
          s.c.val[1]!.val[1]! ^^^ s.c.val[3]!.val[0]! ∧
        r.d.val[3]!.val[0]! =
          s.c.val[2]!.val[0]! ^^^ rot32 s.c.val[4]!.val[1]! 1 ∧
        r.d.val[3]!.val[1]! =
          s.c.val[2]!.val[1]! ^^^ s.c.val[4]!.val[0]! ∧
        r.d.val[4]!.val[0]! =
          s.c.val[3]!.val[0]! ^^^ rot32 s.c.val[0]!.val[1]! 1 ∧
        r.d.val[4]!.val[1]! =
          s.c.val[3]!.val[1]! ^^^ s.c.val[0]!.val[0]! ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_theta_d
  mvcgen
  all_goals first
    | scalar_tac
    | (refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
       (apply Std.U32.bv_eq_imp_eq
        simp_all [WP.uncurry', Std.Array.set_val_eq,
                  Std.UScalar.bv_xor, rot32]))

/-! ## Composed round-1 θ spec (impl side)

Chains the 11 sub-function specs to express each `r.d[x][z]` in terms
of the original `s.st` BitVec halves (with the round-1 swap-aware read
pattern). -/

set_option maxHeartbeats 4000000 in
theorem theta_comp_spec_local_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧
        -- d[0].z0 = c[4].z0 ⊕ rot(c[1].z1, 1)
        r.d.val[0]!.val[0]! =
          (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[0]! ^^^
           s.st.val[24]!.val[0]!) ^^^
          rot32 (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[1]! ^^^
                 s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[0]! ^^^
                 s.st.val[9]!.val[1]!) 1 ∧
        -- d[0].z1 = c[4].z1 ⊕ c[1].z0
        r.d.val[0]!.val[1]! =
          (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[1]! ^^^
           s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[1]! ^^^
           s.st.val[24]!.val[1]!) ^^^
          (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[0]! ^^^
           s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[1]! ^^^
           s.st.val[9]!.val[0]!) ∧
        -- d[1].z0 = c[0].z0 ⊕ rot(c[2].z1, 1)
        r.d.val[1]!.val[0]! =
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[0]! ^^^
           s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
           s.st.val[4]!.val[0]!) ^^^
          rot32 (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
                 s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[0]! ^^^
                 s.st.val[14]!.val[0]!) 1 ∧
        -- d[1].z1 = c[0].z1 ⊕ c[2].z0
        r.d.val[1]!.val[1]! =
          (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[1]! ^^^
           s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
           s.st.val[4]!.val[1]!) ^^^
          (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
           s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[1]! ^^^
           s.st.val[14]!.val[1]!) ∧
        -- d[2].z0 = c[1].z0 ⊕ rot(c[3].z1, 1)
        r.d.val[2]!.val[0]! =
          (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[0]! ^^^
           s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[1]! ^^^
           s.st.val[9]!.val[0]!) ^^^
          rot32 (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[0]! ^^^
                 s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[0]! ^^^
                 s.st.val[19]!.val[1]!) 1 ∧
        -- d[2].z1 = c[1].z1 ⊕ c[3].z0
        r.d.val[2]!.val[1]! =
          (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[1]! ^^^
           s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[0]! ^^^
           s.st.val[9]!.val[1]!) ^^^
          (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[1]! ^^^
           s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[1]! ^^^
           s.st.val[19]!.val[0]!) ∧
        -- d[3].z0 = c[2].z0 ⊕ rot(c[4].z1, 1)
        r.d.val[3]!.val[0]! =
          (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
           s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[1]! ^^^
           s.st.val[14]!.val[1]!) ^^^
          rot32 (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[1]! ^^^
                 s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[1]! ^^^
                 s.st.val[24]!.val[1]!) 1 ∧
        -- d[3].z1 = c[2].z1 ⊕ c[4].z0
        r.d.val[3]!.val[1]! =
          (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
           s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[0]! ^^^
           s.st.val[14]!.val[0]!) ^^^
          (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[0]! ^^^
           s.st.val[24]!.val[0]!) ∧
        -- d[4].z0 = c[3].z0 ⊕ rot(c[0].z1, 1)
        r.d.val[4]!.val[0]! =
          (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[1]! ^^^
           s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[1]! ^^^
           s.st.val[19]!.val[0]!) ^^^
          rot32 (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[1]! ^^^
                 s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
                 s.st.val[4]!.val[1]!) 1 ∧
        -- d[4].z1 = c[3].z1 ⊕ c[0].z0
        r.d.val[4]!.val[1]! =
          (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[0]! ^^^
           s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[0]! ^^^
           s.st.val[19]!.val[1]!) ^^^
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[0]! ^^^
           s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
           s.st.val[4]!.val[0]!) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_theta
  hax_mvcgen
  all_goals first
    | trivial
    | grind
    | simp_all

/-! ## Round-1 spec-input lane peel lemmas

Each `lift_perm_getElem_bv_k_1` exposes the spec-side input lane `k` as a
`lift_lane_bv` over the appropriate halves of `s.st[impl_perm k]`, with
half polarity selected by `impl_swap (impl_perm k)`. -/

/-! ## RHS-side rewriting: `lift_theta_applied_perm`'s `lift_lane_maybe_swap`
    cells at concrete `Fin 25` indices, mapped to the corresponding
    `lift_lane_bv` over halves of `s.st[impl_perm K]`. -/

private theorem lta_perm_bv_0_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 0).val]!) (impl_swap (impl_perm 0))).bv =
      lift_lane_bv ((s.st.val[0]!).val[0]!.bv) ((s.st.val[0]!).val[1]!.bv) := by
  have hp : (impl_perm 0).val = 0 := by decide
  have hsw : impl_swap (impl_perm 0) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_1_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 1).val]!) (impl_swap (impl_perm 1))).bv =
      lift_lane_bv ((s.st.val[2]!).val[1]!.bv) ((s.st.val[2]!).val[0]!.bv) := by
  have hp : (impl_perm 1).val = 2 := by decide
  have hsw : impl_swap (impl_perm 1) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_2_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 2).val]!) (impl_swap (impl_perm 2))).bv =
      lift_lane_bv ((s.st.val[4]!).val[0]!.bv) ((s.st.val[4]!).val[1]!.bv) := by
  have hp : (impl_perm 2).val = 4 := by decide
  have hsw : impl_swap (impl_perm 2) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_3_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 3).val]!) (impl_swap (impl_perm 3))).bv =
      lift_lane_bv ((s.st.val[1]!).val[0]!.bv) ((s.st.val[1]!).val[1]!.bv) := by
  have hp : (impl_perm 3).val = 1 := by decide
  have hsw : impl_swap (impl_perm 3) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_4_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 4).val]!) (impl_swap (impl_perm 4))).bv =
      lift_lane_bv ((s.st.val[3]!).val[1]!.bv) ((s.st.val[3]!).val[0]!.bv) := by
  have hp : (impl_perm 4).val = 3 := by decide
  have hsw : impl_swap (impl_perm 4) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_5_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 5).val]!) (impl_swap (impl_perm 5))).bv =
      lift_lane_bv ((s.st.val[6]!).val[0]!.bv) ((s.st.val[6]!).val[1]!.bv) := by
  have hp : (impl_perm 5).val = 6 := by decide
  have hsw : impl_swap (impl_perm 5) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_6_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 6).val]!) (impl_swap (impl_perm 6))).bv =
      lift_lane_bv ((s.st.val[8]!).val[1]!.bv) ((s.st.val[8]!).val[0]!.bv) := by
  have hp : (impl_perm 6).val = 8 := by decide
  have hsw : impl_swap (impl_perm 6) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_7_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 7).val]!) (impl_swap (impl_perm 7))).bv =
      lift_lane_bv ((s.st.val[5]!).val[1]!.bv) ((s.st.val[5]!).val[0]!.bv) := by
  have hp : (impl_perm 7).val = 5 := by decide
  have hsw : impl_swap (impl_perm 7) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_8_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 8).val]!) (impl_swap (impl_perm 8))).bv =
      lift_lane_bv ((s.st.val[7]!).val[0]!.bv) ((s.st.val[7]!).val[1]!.bv) := by
  have hp : (impl_perm 8).val = 7 := by decide
  have hsw : impl_swap (impl_perm 8) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_9_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 9).val]!) (impl_swap (impl_perm 9))).bv =
      lift_lane_bv ((s.st.val[9]!).val[0]!.bv) ((s.st.val[9]!).val[1]!.bv) := by
  have hp : (impl_perm 9).val = 9 := by decide
  have hsw : impl_swap (impl_perm 9) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_10_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 10).val]!) (impl_swap (impl_perm 10))).bv =
      lift_lane_bv ((s.st.val[12]!).val[1]!.bv) ((s.st.val[12]!).val[0]!.bv) := by
  have hp : (impl_perm 10).val = 12 := by decide
  have hsw : impl_swap (impl_perm 10) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_11_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 11).val]!) (impl_swap (impl_perm 11))).bv =
      lift_lane_bv ((s.st.val[14]!).val[1]!.bv) ((s.st.val[14]!).val[0]!.bv) := by
  have hp : (impl_perm 11).val = 14 := by decide
  have hsw : impl_swap (impl_perm 11) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_12_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 12).val]!) (impl_swap (impl_perm 12))).bv =
      lift_lane_bv ((s.st.val[11]!).val[0]!.bv) ((s.st.val[11]!).val[1]!.bv) := by
  have hp : (impl_perm 12).val = 11 := by decide
  have hsw : impl_swap (impl_perm 12) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_13_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 13).val]!) (impl_swap (impl_perm 13))).bv =
      lift_lane_bv ((s.st.val[13]!).val[1]!.bv) ((s.st.val[13]!).val[0]!.bv) := by
  have hp : (impl_perm 13).val = 13 := by decide
  have hsw : impl_swap (impl_perm 13) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_14_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 14).val]!) (impl_swap (impl_perm 14))).bv =
      lift_lane_bv ((s.st.val[10]!).val[0]!.bv) ((s.st.val[10]!).val[1]!.bv) := by
  have hp : (impl_perm 14).val = 10 := by decide
  have hsw : impl_swap (impl_perm 14) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_15_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 15).val]!) (impl_swap (impl_perm 15))).bv =
      lift_lane_bv ((s.st.val[18]!).val[1]!.bv) ((s.st.val[18]!).val[0]!.bv) := by
  have hp : (impl_perm 15).val = 18 := by decide
  have hsw : impl_swap (impl_perm 15) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_16_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 16).val]!) (impl_swap (impl_perm 16))).bv =
      lift_lane_bv ((s.st.val[15]!).val[0]!.bv) ((s.st.val[15]!).val[1]!.bv) := by
  have hp : (impl_perm 16).val = 15 := by decide
  have hsw : impl_swap (impl_perm 16) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_17_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 17).val]!) (impl_swap (impl_perm 17))).bv =
      lift_lane_bv ((s.st.val[17]!).val[1]!.bv) ((s.st.val[17]!).val[0]!.bv) := by
  have hp : (impl_perm 17).val = 17 := by decide
  have hsw : impl_swap (impl_perm 17) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_18_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 18).val]!) (impl_swap (impl_perm 18))).bv =
      lift_lane_bv ((s.st.val[19]!).val[0]!.bv) ((s.st.val[19]!).val[1]!.bv) := by
  have hp : (impl_perm 18).val = 19 := by decide
  have hsw : impl_swap (impl_perm 18) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_19_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 19).val]!) (impl_swap (impl_perm 19))).bv =
      lift_lane_bv ((s.st.val[16]!).val[1]!.bv) ((s.st.val[16]!).val[0]!.bv) := by
  have hp : (impl_perm 19).val = 16 := by decide
  have hsw : impl_swap (impl_perm 19) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_20_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 20).val]!) (impl_swap (impl_perm 20))).bv =
      lift_lane_bv ((s.st.val[24]!).val[0]!.bv) ((s.st.val[24]!).val[1]!.bv) := by
  have hp : (impl_perm 20).val = 24 := by decide
  have hsw : impl_swap (impl_perm 20) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_21_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 21).val]!) (impl_swap (impl_perm 21))).bv =
      lift_lane_bv ((s.st.val[21]!).val[0]!.bv) ((s.st.val[21]!).val[1]!.bv) := by
  have hp : (impl_perm 21).val = 21 := by decide
  have hsw : impl_swap (impl_perm 21) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_22_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 22).val]!) (impl_swap (impl_perm 22))).bv =
      lift_lane_bv ((s.st.val[23]!).val[0]!.bv) ((s.st.val[23]!).val[1]!.bv) := by
  have hp : (impl_perm 22).val = 23 := by decide
  have hsw : impl_swap (impl_perm 22) = false := by decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_23_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 23).val]!) (impl_swap (impl_perm 23))).bv =
      lift_lane_bv ((s.st.val[20]!).val[1]!.bv) ((s.st.val[20]!).val[0]!.bv) := by
  have hp : (impl_perm 23).val = 20 := by decide
  have hsw : impl_swap (impl_perm 23) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_24_1 (s : state.KeccakState) :
    (lift_lane_maybe_swap (s.st.val[(impl_perm 24).val]!) (impl_swap (impl_perm 24))).bv =
      lift_lane_bv ((s.st.val[22]!).val[1]!.bv) ((s.st.val[22]!).val[0]!.bv) := by
  have hp : (impl_perm 24).val = 22 := by decide
  have hsw : impl_swap (impl_perm 24) = true := by decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]

/-- Build a peel lemma for a specific k=0..24 with `impl_perm`+`impl_swap_k 1`.
    Each instance is closed by `lift_perm_getElem_bv_aux` followed by `decide`
    on the concrete `impl_perm`/`impl_swap`/`impl_swap_k` values. -/
private theorem lift_perm_getElem_bv_0_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(0 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[0]!).val[0]!.bv) ((s.st.val[0]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨0, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨0, by decide⟩)).val = 0 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨0, by decide⟩)) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_1_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(1 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[6]!).val[0]!.bv) ((s.st.val[6]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨1, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨1, by decide⟩)).val = 6 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨1, by decide⟩)) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_2_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(2 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[12]!).val[1]!.bv) ((s.st.val[12]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨2, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨2, by decide⟩)).val = 12 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨2, by decide⟩)) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_3_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(3 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[18]!).val[1]!.bv) ((s.st.val[18]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨3, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨3, by decide⟩)).val = 18 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨3, by decide⟩)) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_4_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(4 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[24]!).val[0]!.bv) ((s.st.val[24]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨4, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨4, by decide⟩)).val = 24 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨4, by decide⟩)) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_5_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(5 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[2]!).val[1]!.bv) ((s.st.val[2]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨5, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨5, by decide⟩)).val = 2 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨5, by decide⟩)) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_6_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(6 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[8]!).val[1]!.bv) ((s.st.val[8]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨6, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨6, by decide⟩)).val = 8 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨6, by decide⟩)) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_7_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(7 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[14]!).val[1]!.bv) ((s.st.val[14]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨7, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨7, by decide⟩)).val = 14 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨7, by decide⟩)) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_8_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(8 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[15]!).val[0]!.bv) ((s.st.val[15]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨8, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨8, by decide⟩)).val = 15 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨8, by decide⟩)) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_9_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(9 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[21]!).val[0]!.bv) ((s.st.val[21]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨9, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨9, by decide⟩)).val = 21 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨9, by decide⟩)) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_10_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(10 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[4]!).val[0]!.bv) ((s.st.val[4]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨10, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨10, by decide⟩)).val = 4 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨10, by decide⟩)) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_11_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(11 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[5]!).val[1]!.bv) ((s.st.val[5]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨11, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨11, by decide⟩)).val = 5 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨11, by decide⟩)) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_12_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(12 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[11]!).val[0]!.bv) ((s.st.val[11]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨12, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨12, by decide⟩)).val = 11 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨12, by decide⟩)) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_13_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(13 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[17]!).val[1]!.bv) ((s.st.val[17]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨13, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨13, by decide⟩)).val = 17 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨13, by decide⟩)) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_14_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(14 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[23]!).val[0]!.bv) ((s.st.val[23]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨14, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨14, by decide⟩)).val = 23 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨14, by decide⟩)) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_15_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(15 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[1]!).val[0]!.bv) ((s.st.val[1]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨15, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨15, by decide⟩)).val = 1 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨15, by decide⟩)) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_16_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(16 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[7]!).val[0]!.bv) ((s.st.val[7]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨16, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨16, by decide⟩)).val = 7 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨16, by decide⟩)) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_17_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(17 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[13]!).val[1]!.bv) ((s.st.val[13]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨17, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨17, by decide⟩)).val = 13 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨17, by decide⟩)) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_18_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(18 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[19]!).val[0]!.bv) ((s.st.val[19]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨18, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨18, by decide⟩)).val = 19 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨18, by decide⟩)) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_19_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(19 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[20]!).val[1]!.bv) ((s.st.val[20]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨19, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨19, by decide⟩)).val = 20 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨19, by decide⟩)) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_20_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(20 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[3]!).val[1]!.bv) ((s.st.val[3]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨20, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨20, by decide⟩)).val = 3 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨20, by decide⟩)) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_21_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(21 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[9]!).val[0]!.bv) ((s.st.val[9]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨21, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨21, by decide⟩)).val = 9 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨21, by decide⟩)) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_22_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(22 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[10]!).val[0]!.bv) ((s.st.val[10]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨22, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨22, by decide⟩)).val = 10 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨22, by decide⟩)) = false := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_23_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(23 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[16]!).val[1]!.bv) ((s.st.val[16]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨23, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨23, by decide⟩)).val = 16 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨23, by decide⟩)) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_24_1 (s : state.KeccakState) :
    ((↑(lift_perm s impl_perm (impl_swap_k 1)) : List Std.U64)[(24 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[22]!).val[1]!.bv) ((s.st.val[22]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s impl_perm (impl_swap_k 1) ⟨24, by decide⟩
  have hp : (impl_perm (transpose_perm ⟨24, by decide⟩)).val = 22 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨24, by decide⟩)) = true := by
    rw [impl_swap_k_one]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

/-! Round-1 θ lift spec. The infrastructure above (`lta_perm_bv_*_1`,
    `lift_perm_getElem_bv_*_1`, `lift_lane_maybe_swap_{true,false}_bv`)
    is in place. The 25-lane closure uses:
      - `lift_perm_getElem_bv_*_1` to expose LHS lane reads as `lift_lane_bv`
      - `impl_swap_k_one` to align swap-tracking
      - Direct unfolding of `lift_lane_maybe_swap`/`impl_perm`/`impl_swap`
      - `← lift_xor`, `← lift_td` to fold spec-side back to canonical lifts
      - `BitVec.rotateLeft_xor` + `bv_decide` to close XOR-AC residuals. -/


set_option maxHeartbeats 2000000 in
@[spec]
theorem theta_lift_spec_1 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round1_theta s
    ⦃ ⇓ r_impl => ⌜
      r_impl.i = s.i ∧
      (do
        let r_spec ← keccak_f.theta (lift_perm s impl_perm (impl_swap_k 1))
        pure (r_spec = lift_theta_applied_perm r_impl impl_perm (impl_swap_k 1))).holds ⌝ ⦄ := by
  apply Triple.of_entails_right _ (theta_comp_spec_local_1 s)
  rw [PostCond.entails_noThrow]
  intro r_impl hpost
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
  refine ⟨hpost.2.1, ?_⟩
  rw [show keccak_f.theta (lift_perm s impl_perm (impl_swap_k 1))
          = .ok (theta_applied (lift_perm s impl_perm (impl_swap_k 1))) from
        result_eq_of_triple (theta_spec _)]
  show ⦃⌜True⌝⦄ Result.ok _ ⦃PostCond.noThrow fun p => ⌜p⌝⦄
  simp [Std.Do.Triple, Std.Do.WP.wp]
  obtain ⟨hst, _, hd0z0, hd0z1, hd1z0, hd1z1, hd2z0, hd2z1,
          hd3z0, hd3z1, hd4z0, hd4z1⟩ := hpost
  apply Subtype.ext
  unfold theta_applied lift_theta_applied_perm
  show _ = List.ofFn _
  simp only [Std.Array.make, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
             Nat.zero_add, Nat.reduceAdd, hst]
  repeat' (first | rfl | (apply List.cons_eq_cons.mpr; refine ⟨?_, ?_⟩))
  all_goals (apply Std.U64.bv_eq_imp_eq)
  -- Rewrite `impl_swap_k 1` to `impl_swap`.
  all_goals simp only [impl_swap_k_one]
  -- Unfold `lift_lane_maybe_swap` and `lift_lane` to expose `s.st[(impl_perm K).val]!`.
  -- The if-then-else branches reduce at concrete Fin K via `decide := true`.
  all_goals
    simp (config := { decide := true }) only [
      lift_lane_maybe_swap, lift_lane,
      Std.UScalar.bv_xor,
      reduceIte]
  all_goals
    simp_all only [Std.UScalar.bv_xor, rot32]
  all_goals
    simp only [lift_perm_getElem_bv_0_1, lift_perm_getElem_bv_1_1, lift_perm_getElem_bv_2_1,
      lift_perm_getElem_bv_3_1, lift_perm_getElem_bv_4_1, lift_perm_getElem_bv_5_1,
      lift_perm_getElem_bv_6_1, lift_perm_getElem_bv_7_1, lift_perm_getElem_bv_8_1,
      lift_perm_getElem_bv_9_1, lift_perm_getElem_bv_10_1, lift_perm_getElem_bv_11_1,
      lift_perm_getElem_bv_12_1, lift_perm_getElem_bv_13_1, lift_perm_getElem_bv_14_1,
      lift_perm_getElem_bv_15_1, lift_perm_getElem_bv_16_1, lift_perm_getElem_bv_17_1,
      lift_perm_getElem_bv_18_1, lift_perm_getElem_bv_19_1, lift_perm_getElem_bv_20_1,
      lift_perm_getElem_bv_21_1, lift_perm_getElem_bv_22_1, lift_perm_getElem_bv_23_1,
      lift_perm_getElem_bv_24_1]
  -- Merge LHS `lift_lane_bv` chain into a single `lift_lane_bv (combined_X) (combined_Y)`
  -- to match the RHS shape. `← lift_xor` collapses `lift_lane_bv A B ^^^ lift_lane_bv C D`
  -- into `lift_lane_bv (A^^^C) (B^^^D)`; `← lift_td` collapses the rotated column chain.
  all_goals simp only [Std.UScalarTy.U64_numBits_eq, ← lift_xor, ← lift_td]
  -- Each cell is now `lift_lane_bv X Y = lift_lane_bv X' Y'` where X, X', Y, Y'
  -- are pure XOR chains over `s.st[K]!.val[J]!.bv` plus optional `.rotateLeft 1`,
  -- equal modulo XOR-AC. Split into two BV-32 sub-equalities, then close via bv_decide.
  all_goals first
    | rfl
    | apply congrArg₂ lift_lane_bv
  -- Distribute `.rotateLeft 1` over XOR (using local helper) on both sides, so
  -- LHS and RHS become pure flat XOR-chains over BV-32 atoms modulo XOR-AC.
  -- 50 BV-32 cells. Roughly half close cleanly via `ac_rfl` (the cells where
  -- `← lift_td` left both sides in matching `^^^`-over-rotateLeft form). The
  -- remaining 25 cells are stuck at the form
  --   `<lane> ^^^ (<col5> ^^^ (<col5_rot>).rotateLeft 1) = <lane> ^^^ (<col5'> ^^^ (<col5_rot'>).rotateLeft 1)`
  -- where col5/col5_rot vs col5'/col5_rot' differ only by XOR-AC reordering.
  -- `bv_decide` proves this in isolation (verified via `test_cell0_z0`) but
  -- inside the main proof's mvcgen-polluted context the SAT abstraction
  -- treats the whole BV-32 side as one opaque variable. The standard fix is
  -- 25 per-cell `bv_decide`-discharged BV-32 lemmas (see comment block above).
  -- Distribute `.rotateLeft 1` over XOR on BOTH sides. Iterate twice if needed.
  -- Distribute `.rotateLeft 1` over XOR on BOTH sides via iterated rewriting:
  -- `simp only` fully flattens both sides into pure XOR chains over BV-32 atoms.
  -- One pass distributes the outer rotateLeft; a second pass catches the
  -- inner-residual rotateLeft occurrences that `← lift_td` re-bundled. After
  -- distribution, each cell is `lhs ^^^ chain = lhs' ^^^ chain'` modulo XOR-AC.
  all_goals try simp only [rotateLeft1_xor_bv32]
  -- Three closure cases per BV-32 sub-goal:
  --   1. `ac_rfl`: both sides match modulo XOR-AC of `BitVec.xor` (uses the
  --      `Std.Associative`/`Std.Commutative` instances registered in core).
  --   2. `apply congrArg (HXor.hXor _); ac_rfl`: peel a shared lane-atom prefix
  --      that breaks `ac_rfl`'s associativity-canonicalisation, then close the
  --      remaining XOR chain by AC.
  --   3. `(2) + ← rotateLeft1_xor_bv32; ac_rfl`: same as (2) but combine the
  --      distributed `.rotateLeft 1` atoms back into a single rotated chain
  --      (handles the cells whose LHS got fully distributed but RHS kept the
  --      `(.. ^^^ ..).rotateLeft 1` form, or vice-versa).
  all_goals
    first | ac_rfl
          | (apply congrArg (HXor.hXor (α := BitVec 32) _); ac_rfl)
          | (apply congrArg (HXor.hXor (α := BitVec 32) _);
             try simp only [← rotateLeft1_xor_bv32]; ac_rfl)

end libcrux_iot_sha3.Foundation
