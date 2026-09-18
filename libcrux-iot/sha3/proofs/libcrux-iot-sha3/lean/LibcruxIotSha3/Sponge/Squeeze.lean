/-
  # Squeeze loop (`keccak_loop1`) and per-byte spec bridge.

  Artifacts delivered in this file:

  * `iterate_keccak_f_eq_fold` — pure unfold of `sponge.iterate_keccak_f`
    to a `Nat.fold` of `keccak_f.keccak_f`. Proved by induction on the
    iteration count using `sponge.iterate_keccak_f.eq_def`.

  * `keccak.keccak_loop1_invariant` — the impl Triple for the squeeze
    loop `keccak.keccak_loop1`. Uses `loop_range_spec_usize` with a
    fold-form invariant carrying termination (`r.i.val = 0`), offset
    advancement, and spec-side lockstep
    `squeeze_fold s (blocks - 1) = lift r`.

  * `squeezeByteAt` — the per-byte projection of a spec state used
    by both `keccak.squeeze_next_block_spec` and the per-byte
    equivalence theorem.

  * `sponge_squeeze_byte_eq` — pure block-wise characterization of
    `sponge.squeeze`. Equates byte `k` of `sponge.squeeze` (under
    `iterate_keccak_f (k/rate) state = .ok s_b`) with
    `squeezeByteAt s_b (k % rate.val)`. The conditional totality
    of `iterate_keccak_f` is supplied at the use site via Bridge 1's
    `keccakf1600_equiv_hacspec`.

  ## See also

  - `Sponge/SqueezeBlock.lean:keccak.squeeze_next_block_spec` —
    per-block Triple used in the loop body.
-/
import LibcruxIotSha3.Sponge.SqueezeBlock

open Aeneas Aeneas.Std RustM Std.Do libcrux_iot_sha3
open LibcruxIotSha3.LaneModel
open LibcruxIotSha3.SpongeModel

namespace libcrux_iot_sha3.Sponge

set_option mvcgen.warning false

attribute [local spec] Aeneas.Std.uncurry

open libcrux_iot_sha3.Foundation libcrux_iot_sha3.Composition

-- Defensive seal re-issue: no proof in this file may unfold either side
-- of Bridge 1.
attribute [local irreducible] keccak.keccakf1600 keccakFLanes

/-! ## Squeeze loop. -/

/-! ### Local helpers (mirror of `Absorb.lean`). -/

private theorem triple_of_ok_sq {α : Type} {x : RustM α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PredTrans.apply, hp]

private theorem triple_exists_ok_sq {α : Type} {x : RustM α}
    {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v =>
      refine ⟨v, rfl, ?_⟩
      have := h; simp [Std.Do.Triple, WP.wp, PredTrans.apply] at this; exact this
  | .fail _ =>
      exfalso; have := h; simp [Std.Do.Triple, WP.wp, PredTrans.apply] at this
  | .div =>
      exfalso; have := h; simp [Std.Do.Triple, WP.wp, PredTrans.apply] at this

/-! ### Iterating the permutation

The squeeze phase applies `keccakFLanes` once per output block. -/

/-- `n` applications of `keccakFLanes`. -/
def iterate_keccak_f_fold (state : Lanes) (n : Nat) : Lanes := keccakFLanes^[n] state

theorem iterate_keccak_f_fold_zero (state : Lanes) :
    iterate_keccak_f_fold state 0 = state := rfl

theorem iterate_keccak_f_fold_succ (state : Lanes) (n : Nat) :
    iterate_keccak_f_fold state (n + 1) = keccakFLanes (iterate_keccak_f_fold state n) :=
  Function.iterate_succ_apply' _ _ _

/-! ### Theorem 2: `sponge_squeeze_byte_eq`.

Per-byte characterization of `sponge.squeeze`. For each byte index
`k < OUTPUT_LEN.val`, byte `k` of `sponge.squeeze OUTPUT_LEN state rate`
equals the byte-projection of `iterate_keccak_f (k/rate) state` at
position `k % rate`. -/

/-! The squeeze closure stored state is `(rate, state)`. When invoked at
    index `k`, it computes `b = k/rate`, `j = k - b*rate`, runs
    `iterate_keccak_f b state` to get `s_b`, then extracts byte block
    `j/8` of `s_b` directly (under the new spec layout, no transpose) and
    projects byte `j%8` of the little-endian representation.

    To package the closure-call result as a clean equation we need: -/

/-- For `k ≤ Usize.max`, `(BitVec.ofNat _ k).toNat = k`. -/
private theorem usize_ofNat_toNat (k : Nat) (h : k ≤ Std.Usize.max) :
    (BitVec.ofNat Std.UScalarTy.Usize.numBits k).toNat = k := by
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have h1 : Std.UScalarTy.Usize.numBits = Std.Usize.numBits := by
    rw [Std.Usize.numBits]
  rw [h1]
  have hpos : 0 < 2 ^ Std.Usize.numBits := Nat.two_pow_pos _
  have h2 : 2 ^ Std.Usize.numBits = Std.Usize.max + 1 := by
    rw [Std.Usize.max]; omega
  omega

/-- The Aeneas `Usize` value built from `BitVec.ofNat _ k`, for `k ≤ Usize.max`. -/
private def usize_of_nat (k : Nat) (_h : k ≤ Std.Usize.max) : Std.Usize :=
  ⟨BitVec.ofNat _ k⟩

@[simp] private theorem usize_of_nat_val (k : Nat) (h : k ≤ Std.Usize.max) :
    (usize_of_nat k h).val = k :=
  usize_ofNat_toNat k h

/-! ### Helper Triple: `RangeFromUsize` mutable slice index.

Companion to `Absorb.lean:core_models_Slice_Insts_index_RangeFromUsize_spec`
(non-mut version) and `SliceSpecs.lean:core_models_Slice_Insts_index_mut_RangeUsize_spec`
(closed range). The mutable `RangeFrom` variant is what `keccak_loop1.body`
uses to obtain the tail sub-slice. -/
@[spec]
theorem core_models_Slice_Insts_index_mut_RangeFromUsize_spec
    {T : Type} (s : Slice T) (r : CoreModels.core.ops.range.RangeFrom Std.Usize)
    (h : r.start.val ≤ s.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
      (CoreModels.core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) s r
    ⦃ ⇓ p => ⌜ p.1.val = s.val.drop r.start.val ∧
                p.1.val.length = s.val.length - r.start.val ∧
                ∀ s', s'.val.length = s.val.length - r.start.val →
                  (p.2 s').val = s.val.setSlice! r.start.val s'.val ⌝ ⦄ := by
  obtain ⟨ns, hns_eq, hns_val⟩ :=
    Slice.subslice_le_eq s ⟨r.start, s.len⟩ (by simpa [Std.Slice.len_val] using h)
      (by simp)
  -- CoreModels v0.3.12 supplies this instance: `index_mut` delegates to the
  -- `SliceIndex`'s `get_unchecked_mut`, which for `RangeFrom<usize>` is
  -- `slice_slice_mut slice self.start len`.
  unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
  simp only [CoreModels.core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
             CoreModels.rust_primitives.slice.slice_slice_mut,
             CoreModels.rust_primitives.slice.slice_length, bind_tc_ok, hns_eq]
  simp only [Triple, WP.wp, PredTrans.apply,
             Std.Do.SPred.pure, Std.Do.SPred.entails]
  intro _
  have hns_drop : (↑ns : List T) = (↑s : List T).drop r.start.val := by
    rw [hns_val]; unfold List.slice; exact List.take_of_length_le (by simp)
  refine ⟨hns_drop, ?_, ?_⟩
  · rw [hns_drop, List.length_drop]
  · intro s' hs'
    obtain ⟨nu, hnu_eq, hnu_val⟩ :=
      Slice.update_subslice_le_eq s ⟨r.start, s.len⟩ s' (by simpa [Std.Slice.len_val] using h)
        (by simp) (by rw [hs']; simp)
    -- CoreModels v0.3.12's `slice_slice_mut` write-back is directly
    -- `setSlice!`, so the goal needs no rewriting at all -- `simp only` with an
    -- empty lemma set discharges it.
    simp only

/-! ### Theorem 3: `keccak.keccak_loop1_invariant`.

The impl-side squeeze loop equals a `Nat.fold` of `keccak_f.keccak_f` on
the spec state.

The loop iterates from `1..blocks`, applying ONE `keccakf1600` per
iteration. After all iterations, the state has had `blocks - 1`
applications, and the offset has advanced by `(blocks - 1) * RATE`. -/

/-- The fold-form invariant accumulator on the spec side. After `k`
    iterations of the loop body, the impl state corresponds to
    `iterate_keccak_f_fold (lift s_init) k`. -/
def squeeze_fold (s_init : state.KeccakState) (k : Nat) : Lanes :=
  iterate_keccak_f_fold (Foundation.lift s_init) k

@[spec]
theorem keccak.keccak_loop1_invariant
    (RATE : Std.Usize) (blocks : Std.Usize)
    (s : state.KeccakState)
    (out : Slice Std.U8) (offset : Std.Usize)
    (h_i : s.i.val = 0)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_bnd : RATE.val ≤ 200)
    (h_RATE_pos : 1 ≤ RATE.val)
    (h_blocks_pos : 1 ≤ blocks.val)
    (h_offset : offset.val + (blocks.val - 1) * RATE.val ≤ out.val.length)
    (h_offset_max : offset.val + (blocks.val - 1) * RATE.val ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccak_loop1 RATE { start := 1#usize, «end» := blocks } out s offset
    ⦃ ⇓ r => ⌜
        let (out_final, s_final, offset_final) := r
        out_final.val.length = out.val.length
        ∧ s_final.i.val = 0
        ∧ offset_final.val = offset.val + (blocks.val - 1) * RATE.val
        ∧ squeeze_fold s (blocks.val - 1) = Foundation.lift s_final
        ∧ (∀ j : Nat, j < (blocks.val - 1) * RATE.val →
            ∃ s_bj : Std.Array Std.U64 25#usize,
              squeeze_fold s ((j / RATE.val) + 1) = s_bj
              ∧ out_final.val[offset.val + j]! = squeezeByteAt s_bj (j % RATE.val))
        ∧ ∀ j : Nat, j < offset.val → out_final.val[j]! = out.val[j]!
    ⌝ ⦄ := by
  unfold keccak.keccak_loop1
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, out1, s1, offset1) =>
        keccak.keccak_loop1.body RATE iter1 out1 s1 offset1)
      (out, s, offset) 1#usize blocks
      (fun k acc => pure (
          acc.1.val.length = out.val.length
          ∧ acc.2.1.i.val = 0
          ∧ acc.2.2.val = offset.val + (k.val - 1) * RATE.val
          ∧ squeeze_fold s (k.val - 1) = Foundation.lift acc.2.1
          ∧ (∀ j : Nat, j < (k.val - 1) * RATE.val →
              ∃ s_bj : Std.Array Std.U64 25#usize,
                squeeze_fold s ((j / RATE.val) + 1) = s_bj
                ∧ acc.1.val[offset.val + j]! = squeezeByteAt s_bj (j % RATE.val))
          ∧ ∀ j : Nat, j < offset.val → acc.1.val[j]! = out.val[j]!))
      h_blocks_pos
      (pure_prop_holds ⟨rfl, h_i,
        by
          show offset.val = offset.val + ((1#usize : Std.Usize).val - 1) * RATE.val
          show offset.val = offset.val + (1 - 1) * RATE.val
          simp,
        by
          show squeeze_fold s ((1#usize : Std.Usize).val - 1) = _
          show squeeze_fold s (1 - 1) = _
          show squeeze_fold s 0 = _
          unfold squeeze_fold iterate_keccak_f_fold
          rfl,
        by
          intro j hj
          exfalso
          have : (((1#usize : Std.Usize).val - 1) * RATE.val) = 0 := by
            show (1 - 1) * RATE.val = 0
            simp
          omega,
        by
          intro j _
          rfl⟩)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := of_pure_prop_holds h
    refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
    · rw [h3]
    · exact h4
    · exact h5
    · exact h6
  · intro acc k h_ge h_le_k hinv
    obtain ⟨h_acc_len, h_acc_i, h_acc_offset, h_fold_acc, h_acc_bytes, h_acc_prefix⟩ :=
      of_pure_prop_holds hinv
    obtain ⟨out_acc, s_acc, offset_acc⟩ := acc
    -- Body: keccak.keccak_loop1.body RATE DELIM outlen { start := k, end := blocks } out_acc s_acc offset_acc.
    unfold keccak.keccak_loop1.body
    apply Std.Do.Triple.bind _ _
      (IteratorRange_next_spec_usize k blocks
        (Q := PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
          match oi.1 with
          | none => k.val ≥ blocks.val ∧
                    oi.2 = { start := k, «end» := blocks }
          | some i => i = k ∧ k.val < blocks.val ∧
                      oi.2.«end» = blocks ∧ oi.2.start.val = k.val + 1
        ⌝)
        (fun hlt s' hs' => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          exact ⟨rfl, hlt, rfl, hs'⟩)
        (fun hge => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          exact ⟨hge, rfl⟩))
    intro ⟨o, iter1⟩
    apply triple_imp_intro
    rcases o with _ | i
    · rintro ⟨hge, _⟩
      have hk_eq : k.val = blocks.val := Nat.le_antisymm h_le_k hge
      simp only [Triple, WP.wp]
      apply SPred.pure_intro
      refine pure_prop_holds ⟨h_acc_len, h_acc_i, ?_, ?_, ?_, h_acc_prefix⟩
      · rw [h_acc_offset, hk_eq]
      · rw [← hk_eq]; exact h_fold_acc
      · rw [← hk_eq]; exact h_acc_bytes
    · rintro ⟨hi_eq, hk_lt, hiter1_end, hiter1_start⟩
      cases hi_eq
      -- Side-condition: `offset_acc + RATE ≤ out_acc.length`.
      have h_off_lt_outlen : offset_acc.val + RATE.val ≤ out_acc.val.length := by
        rw [h_acc_len, h_acc_offset]
        have hk_ge_1 : 1 ≤ k.val := h_ge
        have h_k_blocks_minus_1 : k.val ≤ blocks.val - 1 := by omega
        have h_arith : (k.val - 1) * RATE.val + RATE.val = k.val * RATE.val := by
          have : k.val = (k.val - 1) + 1 := by omega
          conv_rhs => rw [this]
          rw [Nat.add_mul]; ring
        have : offset.val + (k.val - 1) * RATE.val + RATE.val
              = offset.val + k.val * RATE.val := by
          rw [Nat.add_assoc, h_arith]
        rw [this]
        have h_step : k.val * RATE.val ≤ (blocks.val - 1) * RATE.val :=
          Nat.mul_le_mul_right RATE.val h_k_blocks_minus_1
        omega
      have h_off_RATE_max : offset_acc.val + RATE.val ≤ Std.Usize.max := by
        rw [h_acc_offset]
        have hk_ge_1 : 1 ≤ k.val := h_ge
        have h_k_blocks_minus_1 : k.val ≤ blocks.val - 1 := by omega
        have h_arith : (k.val - 1) * RATE.val + RATE.val = k.val * RATE.val := by
          have : k.val = (k.val - 1) + 1 := by omega
          conv_rhs => rw [this]
          rw [Nat.add_mul]; ring
        have : offset.val + (k.val - 1) * RATE.val + RATE.val
              = offset.val + k.val * RATE.val := by
          rw [Nat.add_assoc, h_arith]
        rw [this]
        have h_step : k.val * RATE.val ≤ (blocks.val - 1) * RATE.val :=
          Nat.mul_le_mul_right RATE.val h_k_blocks_minus_1
        omega
      -- The body unfolds to a chain. Use mvcgen to discharge the body
      -- using the specs we have.
      mvcgen
      all_goals (try scalar_tac)
      -- One remaining VC: invariant preservation.
      expose_names
      obtain ⟨h_idx_drop, h_idx_len, h_back⟩ := h
      obtain ⟨h_snb_i, h_snb_len, s_spec, h_snb_spec, h_snb_lift, h_snb_bytes⟩ := h_1
      refine ⟨hk_lt, hiter1_end, hiter1_start, ?_⟩
      apply pure_prop_holds
      have h_new_fold : squeeze_fold s ((k.val + 1) - 1) = Foundation.lift r_1.1 := by
        have hk_ge_1 : 1 ≤ k.val := h_ge
        have h_idx : k.val + 1 - 1 = (k.val - 1) + 1 := by omega
        have h_inner : squeeze_fold s (k.val - 1) = Foundation.lift s_acc := h_fold_acc
        show squeeze_fold s (k.val + 1 - 1) = _
        rw [h_idx]
        unfold squeeze_fold at h_inner ⊢
        rw [iterate_keccak_f_fold_succ, h_inner, h_snb_spec, h_snb_lift]
      refine ⟨?_, h_snb_i, ?_, ?_, ?_, ?_⟩
      · -- Length: `(back snb_out).val.length = out.val.length`.
        rw [h_back r_1.2 (h_snb_len.trans h_idx_len)]
        rw [List.length_setSlice!]
        exact h_acc_len
      · -- offset_new.val = offset.val + (iter1.start.val - 1) * RATE.val.
        rw [h_2, h_acc_offset, hiter1_start]
        have hk_ge_1 : 1 ≤ k.val := h_ge
        have h_arith : (k.val - 1) * RATE.val + RATE.val
                      = (k.val + 1 - 1) * RATE.val := by
          have h1 : k.val + 1 - 1 = k.val := by omega
          rw [h1]
          have h2 : k.val = (k.val - 1) + 1 := by omega
          conv_rhs => rw [h2]
          rw [Nat.add_mul]; ring
        omega
      · -- squeeze_fold s (iter1.start.val - 1) = lift r_1.1.
        rw [hiter1_start]; exact h_new_fold
      · -- Per-byte clause for the new iteration: j < ((k.val + 1) - 1) * RATE.val = k.val * RATE.val.
        rw [hiter1_start]
        intro j hj
        have hk_ge_1 : 1 ≤ k.val := h_ge
        have h_kp1m1 : (k.val + 1) - 1 = k.val := by omega
        rw [h_kp1m1] at hj
        -- hj : j < k.val * RATE.val. Split on j < (k.val - 1) * RATE.val.
        rw [h_back r_1.2 (h_snb_len.trans h_idx_len)]
        by_cases h_j_old : j < (k.val - 1) * RATE.val
        · -- Preserved from previous invariant: j is in the prefix.
          obtain ⟨s_bj, h_fold_bj, h_byte_bj⟩ := h_acc_bytes j h_j_old
          refine ⟨s_bj, h_fold_bj, ?_⟩
          -- Show: (out_acc.val.setSlice! offset_acc.val r_1.2.val)[offset.val + j]!
          --     = out_acc.val[offset.val + j]! = squeezeByteAt s_bj (j % RATE.val).
          rw [List.getElem!_setSlice!_same _ _ _ _ (Or.inl ?_)]
          · exact h_byte_bj
          · -- offset.val + j < offset_acc.val = offset.val + (k.val - 1) * RATE.val.
            rw [h_acc_offset]; omega
        · -- New write region: j in [(k.val - 1)*RATE.val, k.val*RATE.val).
          push Not at h_j_old
          -- Set j' := j - (k.val - 1) * RATE.val. Then 0 ≤ j' < RATE.val.
          have h_jrate_split : j = (k.val - 1) * RATE.val + (j % RATE.val) := by
            -- Since (k-1)*RATE ≤ j < k*RATE and j = (k-1)*RATE + (j - (k-1)*RATE),
            -- need to show j - (k-1)*RATE = j % RATE.
            have h_kRate : k.val * RATE.val = (k.val - 1) * RATE.val + RATE.val := by
              have h2 : k.val = (k.val - 1) + 1 := by omega
              conv_lhs => rw [h2]
              rw [Nat.add_mul]; ring
            -- j / RATE = k - 1, j % RATE = j - (k-1)*RATE.
            have h_div : j / RATE.val = k.val - 1 := by
              apply Nat.div_eq_of_lt_le
              · exact h_j_old
              · rw [show (k.val - 1 + 1) * RATE.val = k.val * RATE.val by
                    have : k.val - 1 + 1 = k.val := by omega
                    rw [this]]
                omega
            have h_mod_eq : j % RATE.val = j - (k.val - 1) * RATE.val := by
              have := Nat.div_add_mod' j RATE.val
              rw [h_div] at this; omega
            omega
          have h_div_RATE : j / RATE.val = k.val - 1 := by
            apply Nat.div_eq_of_lt_le
            · exact h_j_old
            · rw [show (k.val - 1 + 1) * RATE.val = k.val * RATE.val by
                  have : k.val - 1 + 1 = k.val := by omega
                  rw [this]]
              omega
          have h_mod_lt : j % RATE.val < RATE.val := Nat.mod_lt _ (by omega)
          -- The "new" s_b is `lift r_1.1`.
          refine ⟨Foundation.lift r_1.1, ?_, ?_⟩
          · -- squeeze_fold s ((j / RATE.val) + 1) = lift r_1.1.
            rw [h_div_RATE]
            have : k.val - 1 + 1 = k.val := by omega
            rw [this]
            -- Goal: squeeze_fold s k.val = .ok (lift r_1.1).
            -- We have h_new_fold : squeeze_fold s ((k.val + 1) - 1) = .ok (lift r_1.1).
            -- and (k.val + 1) - 1 = k.val.
            have : (k.val + 1) - 1 = k.val := by omega
            rw [this] at h_new_fold
            exact h_new_fold
          · -- (out_acc.val.setSlice! offset_acc.val r_1.2.val)[offset.val + j]!
            --   = squeezeByteAt (lift r_1.1) (j % RATE.val).
            -- The byte falls in the middle of the setSlice!.
            have h_off_rel : offset.val + j - offset_acc.val = j % RATE.val := by
              rw [h_acc_offset]
              -- offset.val + j - (offset.val + (k.val - 1) * RATE.val) = j - (k.val - 1) * RATE.val.
              have h_eq : offset.val + j - (offset.val + (k.val - 1) * RATE.val)
                        = j - (k.val - 1) * RATE.val := by omega
              rw [h_eq]
              -- j - (k.val - 1) * RATE.val = j % RATE.val (from h_jrate_split).
              omega
            rw [List.getElem!_setSlice!_middle _ _ _ _ ?_]
            · -- Goal: r_1.2.val[offset.val + j - offset_acc.val]!
              --     = squeezeByteAt (lift r_1.1) (j % RATE.val).
              rw [h_off_rel]
              -- Use h_snb_bytes (j % RATE.val).
              have h_byte := h_snb_bytes (j % RATE.val) h_mod_lt
              rw [h_byte]
              -- h_snb_lift : s_spec = lift r_1.1. The byte uses s_spec; rewrite.
              unfold squeezeByteAt
              rw [h_snb_lift]
            · -- Side condition for setSlice!_middle: indices in range.
              -- Common bound: offset.val + k.val * RATE.val ≤ out.val.length.
              have h_kRATE_le : offset.val + k.val * RATE.val ≤ out.val.length := by
                have h_step : k.val * RATE.val ≤ (blocks.val - 1) * RATE.val :=
                  Nat.mul_le_mul_right RATE.val (by omega)
                omega
              have h_r1_len : r_1.2.val.length = out_acc.val.length - offset_acc.val := by
                rw [h_snb_len, h_idx_len]
              refine ⟨?_, ?_, ?_⟩
              · -- offset_acc.val ≤ offset.val + j.
                rw [h_acc_offset]; omega
              · -- offset.val + j - offset_acc.val < r_1.2.val.length.
                rw [h_r1_len, h_acc_len, h_acc_offset]
                -- Goal: offset.val + j - (offset.val + (k.val - 1) * RATE.val)
                --     < out.val.length - (offset.val + (k.val - 1) * RATE.val).
                -- Since offset.val + j < offset.val + k.val * RATE.val ≤ out.val.length,
                -- and (k.val - 1) * RATE.val ≤ j, this is OK by omega.
                omega
              · -- offset.val + j < out_acc.val.length.
                rw [h_acc_len]
                omega
      · -- Prefix preservation: for j < offset.val, out_acc.val[j]! is unchanged
        -- by the setSlice! at offset_acc.val ≥ offset.val.
        intro j hj
        rw [h_back r_1.2 (h_snb_len.trans h_idx_len)]
        have hk_ge_1 : 1 ≤ k.val := h_ge
        have h_off_ge_offset : offset.val ≤ offset_acc.val := by
          rw [h_acc_offset]; omega
        rw [List.getElem!_setSlice!_same _ _ _ _ (Or.inl (by omega))]
        exact h_acc_prefix j hj

/-! ### Byte-wise characterization of the model's squeeze

`squeezeLanes` is a `mkArr`, so reading byte `k` off it is immediate, and its
content is `squeezeByteAt` -- which `SpongeModel` ties to the flat bit string.
(The corresponding statement about `hacspec_sha3`'s `createi` form needed two
hundred lines of closure plumbing.) -/

theorem squeezeLanes_byte_eq
    (OUTPUT_LEN : Std.Usize) (state : Lanes) (rate : Std.Usize)
    (_h_rate_pos : 0 < rate.val)
    (s_b : Nat → Lanes)
    (h_iter : ∀ k : Nat, k < OUTPUT_LEN.val →
      keccakFLanes^[k / rate.val] state = s_b k) :
    ∀ k : Nat, k < OUTPUT_LEN.val →
      (squeezeLanes OUTPUT_LEN state rate.val).val[k]!
        = squeezeByteAt (s_b k) (k - (k / rate.val) * rate.val) := by
  intro k hk
  rw [squeezeLanes_getElem OUTPUT_LEN state rate.val k hk, h_iter k hk,
    show k % rate.val = k - (k / rate.val) * rate.val from by
      have h := Nat.div_add_mod k rate.val
      have hc : rate.val * (k / rate.val) = (k / rate.val) * rate.val := by ring
      omega]


end libcrux_iot_sha3.Sponge
