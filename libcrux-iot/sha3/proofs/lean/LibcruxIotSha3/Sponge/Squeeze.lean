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
    `squeeze_fold s (blocks - 1) = .ok (lift r)`.

  * `squeeze_byte_at` — the per-byte projection of a spec state used
    by both `keccak.squeeze_next_block_spec` and the per-byte
    equivalence theorem.

  * `sponge_squeeze_byte_eq` — pure block-wise characterization of
    `sponge.squeeze`. Equates byte `k` of `sponge.squeeze` (under
    `iterate_keccak_f (k/rate) state = .ok s_b`) with
    `squeeze_byte_at s_b (k % rate.val)`. The conditional totality
    of `iterate_keccak_f` is supplied at the use site via Bridge 1's
    `keccakf1600_equiv_hacspec`.

  ## See also

  - `Sponge/SqueezeBlock.lean:keccak.squeeze_next_block_spec` —
    per-block Triple used in the loop body.
-/
import LibcruxIotSha3.Sponge.SqueezeBlock

open Aeneas Aeneas.Std Result Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

set_option mvcgen.warning false

attribute [local spec] Aeneas.Std.uncurry

open libcrux_iot_sha3.Foundation libcrux_iot_sha3.Composition

-- Defensive seal re-issue: no proof in this file may unfold either side
-- of Bridge 1.
set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ## Squeeze loop. -/

/-! ### Local helpers (mirror of `Absorb.lean`). -/

private theorem triple_of_ok_sq {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PredTrans.apply, hp]

private theorem triple_exists_ok_sq {α : Type} {x : Result α}
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

/-! ### Theorem 1: `iterate_keccak_f_eq_fold`.

The spec's `sponge.iterate_keccak_f n state` equals the `Nat.fold` of
`keccak_f.keccak_f` over `n.val`. Proved by Nat-induction. -/

/-- Pure `Nat.fold` form of `sponge.iterate_keccak_f`. At index `n`, this
    is the right-associated chain of `keccak_f.keccak_f` calls. -/
def iterate_keccak_f_fold (state : Std.Array Std.U64 25#usize) (n : Nat) :
    Result (Std.Array Std.U64 25#usize) :=
  Nat.fold n (init := (.ok state : Result _))
    (fun _ _ acc => acc >>= fun st => keccak_f.keccak_f st)

theorem iterate_keccak_f_eq_fold
    (n : Std.Usize) (state : Std.Array Std.U64 25#usize) :
    sponge.iterate_keccak_f n state = iterate_keccak_f_fold state n.val := by
  -- Induction on `m := n.val`, generalized over state and n.
  suffices h : ∀ (m : Nat) (n : Std.Usize) (state : Std.Array Std.U64 25#usize),
      n.val = m → sponge.iterate_keccak_f n state = iterate_keccak_f_fold state m
    by exact h n.val n state rfl
  intro m
  induction m with
  | zero =>
    intro n state h_n_val
    rw [sponge.iterate_keccak_f.eq_def]
    have h_n_eq : n = 0#usize := by
      apply Std.UScalar.eq_of_val_eq
      rw [h_n_val]; rfl
    rw [h_n_eq]; simp only [↓reduceIte]
    unfold iterate_keccak_f_fold
    simp only [Nat.fold_zero]
  | succ k ih =>
    intro n state h_n_val
    rw [sponge.iterate_keccak_f.eq_def]
    have h_n_nz : ¬ n = 0#usize := by
      intro h
      have : n.val = 0 := by rw [h]; rfl
      omega
    simp only [h_n_nz, ↓reduceIte]
    -- Now reduce `n - 1#usize`. Use `sub_equiv`-style direct reduction.
    set i : Std.Usize := ⟨BitVec.ofNat _ (n.val - 1)⟩ with hi_def
    have h_n_ge : ¬ n.val < (1#usize : Std.Usize).val := by
      show ¬ n.val < 1; rw [h_n_val]; omega
    have h_sub_eq : n - 1#usize = (.ok i : Result Std.Usize) := by
      show Std.UScalar.sub n 1#usize = .ok i
      unfold Std.UScalar.sub
      rw [if_neg h_n_ge]
      rfl
    have h_i_val : i.val = k := by
      show (BitVec.ofNat _ (n.val - 1)).toNat = k
      rw [BitVec.toNat_ofNat]
      have h_bound : n.val - 1 < 2 ^ Std.UScalarTy.Usize.numBits := by
        have := n.hBounds
        simp [Std.UScalarTy.numBits] at *
        omega
      rw [Nat.mod_eq_of_lt h_bound, h_n_val]; omega
    rw [h_sub_eq]; simp only [bind_tc_ok]
    -- IH on i.
    rw [ih i state h_i_val]
    -- Goal: `iterate_keccak_f_fold state k >>= keccak_f.keccak_f
    --      = iterate_keccak_f_fold state (k+1)`.
    unfold iterate_keccak_f_fold
    rw [Nat.fold_succ]

/-! ### Theorem 2: `sponge_squeeze_byte_eq`.

Per-byte characterization of `sponge.squeeze`. For each byte index
`k < OUTPUT_LEN.val`, byte `k` of `sponge.squeeze OUTPUT_LEN state rate`
equals the byte-projection of `iterate_keccak_f (k/rate) state` at
position `k % rate`. -/

/-- Per-byte projection of a spec state: byte `j` of the lane-major
    serialization of `s`. Matches the per-byte formula used in
    `keccak.squeeze_next_block_spec` and is the form that
    `sponge.squeeze` produces for byte `k = b*rate + j` of the OUTPUT
    (with `b = k/rate`, `j = k % rate < rate`). -/
def squeeze_byte_at (s : Std.Array Std.U64 25#usize) (j : Nat) : Std.U8 :=
  ⟨(BitVec.toLEBytes (s.val[j / 8]!).bv)[j % 8]!⟩

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
                ∀ s', (p.2 s').val = s.val.setSlice! r.start.val s'.val ⌝ ⦄ := by
  unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
         CoreModels.core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
         core.slice.index.Slice.index_mut
         core.slice.index.SliceIndexRangeUsizeSlice.index_mut
  have h0' : (⟨r.start, s.len⟩ : core.ops.range.Range Std.Usize).start
              ≤ (⟨r.start, s.len⟩ : core.ops.range.Range Std.Usize).end := by
    simpa [UScalar.le_equiv, Std.Slice.len, Std.Slice.length] using h
  simp only [Triple, WP.wp]
  simp [h0', Std.Slice.length, Std.Slice.len]
  refine ⟨?_, ?_⟩
  · unfold List.slice
    exact List.take_of_length_le (by simp)
  · unfold List.slice
    rw [List.length_take, List.length_drop]
    exact ⟨by omega, fun s' => rfl⟩

/-! ### Theorem 3: `keccak.keccak_loop1_invariant`.

The impl-side squeeze loop equals a `Nat.fold` of `keccak_f.keccak_f` on
the spec state.

The loop iterates from `1..blocks`, applying ONE `keccakf1600` per
iteration. After all iterations, the state has had `blocks - 1`
applications, and the offset has advanced by `(blocks - 1) * RATE`. -/

/-- The fold-form invariant accumulator on the spec side. After `k`
    iterations of the loop body, the impl state corresponds to
    `iterate_keccak_f_fold (lift s_init) k`. -/
def squeeze_fold (s_init : state.KeccakState) (k : Nat) :
    Result (Std.Array Std.U64 25#usize) :=
  iterate_keccak_f_fold (Foundation.lift s_init) k

@[spec]
theorem keccak.keccak_loop1_invariant
    (RATE : Std.Usize) (blocks : Std.Usize) (s : state.KeccakState)
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
        ∧ squeeze_fold s (blocks.val - 1) = .ok (Foundation.lift s_final)
        ∧ (∀ j : Nat, j < (blocks.val - 1) * RATE.val →
            ∃ s_bj : Std.Array Std.U64 25#usize,
              squeeze_fold s ((j / RATE.val) + 1) = .ok s_bj
              ∧ out_final.val[offset.val + j]! = squeeze_byte_at s_bj (j % RATE.val))
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
          ∧ squeeze_fold s (k.val - 1) = .ok (Foundation.lift acc.2.1)
          ∧ (∀ j : Nat, j < (k.val - 1) * RATE.val →
              ∃ s_bj : Std.Array Std.U64 25#usize,
                squeeze_fold s ((j / RATE.val) + 1) = .ok s_bj
                ∧ acc.1.val[offset.val + j]! = squeeze_byte_at s_bj (j % RATE.val))
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
    -- Body: keccak.keccak_loop1.body RATE { start := k, end := blocks } out_acc s_acc offset_acc.
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
      have h_new_fold : squeeze_fold s ((k.val + 1) - 1) = .ok (Foundation.lift r_1.1) := by
        show squeeze_fold s (k.val + 1 - 1) = _
        have hk_ge_1 : 1 ≤ k.val := h_ge
        have h_idx : k.val + 1 - 1 = (k.val - 1) + 1 := by omega
        rw [h_idx]
        unfold squeeze_fold iterate_keccak_f_fold
        rw [Nat.fold_succ]
        have h_inner :
            (Nat.fold (k.val - 1) (init := (.ok (Foundation.lift s) : Result _))
              (fun _ _ acc => acc >>= fun st => keccak_f.keccak_f st))
            = .ok (Foundation.lift s_acc) := by
          have := h_fold_acc
          unfold squeeze_fold iterate_keccak_f_fold at this
          exact this
        rw [h_inner]; simp only [bind_tc_ok]
        rw [h_snb_spec]
        rw [h_snb_lift]
      refine ⟨?_, h_snb_i, ?_, ?_, ?_, ?_⟩
      · -- Length: `(back snb_out).val.length = out.val.length`.
        rw [h_back]
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
      · -- squeeze_fold s (iter1.start.val - 1) = .ok (lift r_1.1).
        rw [hiter1_start]; exact h_new_fold
      · -- Per-byte clause for the new iteration: j < ((k.val + 1) - 1) * RATE.val = k.val * RATE.val.
        rw [hiter1_start]
        intro j hj
        have hk_ge_1 : 1 ≤ k.val := h_ge
        have h_kp1m1 : (k.val + 1) - 1 = k.val := by omega
        rw [h_kp1m1] at hj
        -- hj : j < k.val * RATE.val. Split on j < (k.val - 1) * RATE.val.
        rw [h_back]
        by_cases h_j_old : j < (k.val - 1) * RATE.val
        · -- Preserved from previous invariant: j is in the prefix.
          obtain ⟨s_bj, h_fold_bj, h_byte_bj⟩ := h_acc_bytes j h_j_old
          refine ⟨s_bj, h_fold_bj, ?_⟩
          -- Show: (out_acc.val.setSlice! offset_acc.val r_1.2.val)[offset.val + j]!
          --     = out_acc.val[offset.val + j]! = squeeze_byte_at s_bj (j % RATE.val).
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
          · -- squeeze_fold s ((j / RATE.val) + 1) = .ok (lift r_1.1).
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
            --   = squeeze_byte_at (lift r_1.1) (j % RATE.val).
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
              --     = squeeze_byte_at (lift r_1.1) (j % RATE.val).
              rw [h_off_rel]
              -- Use h_snb_bytes (j % RATE.val).
              have h_byte := h_snb_bytes (j % RATE.val) h_mod_lt
              rw [h_byte]
              -- h_snb_lift : s_spec = lift r_1.1. The byte uses s_spec; rewrite.
              unfold squeeze_byte_at
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
        rw [h_back]
        have hk_ge_1 : 1 ≤ k.val := h_ge
        have h_off_ge_offset : offset.val ≤ offset_acc.val := by
          rw [h_acc_offset]; omega
        rw [List.getElem!_setSlice!_same _ _ _ _ (Or.inl (by omega))]
        exact h_acc_prefix j hj

/-! ### Theorem: `sponge_squeeze_byte_eq` — block-wise characterization of
`sponge.squeeze`.

Two-step formulation:

* `squeeze_closure_call_eq` — Result-level equation for the squeeze closure's
  `call` (the body that drives each byte). Conditional on
  `iterate_keccak_f b state` succeeding. The conclusion identifies the
  returned byte with `squeeze_byte_at s_b (k - b*rate)`.

* `sponge_squeeze_byte_eq` — lifts the per-call equation to
  `sponge.squeeze` via `createi_pure_eq`, *conditional* on the per-byte
  `iterate_keccak_f` succeeding for every block needed in
  `0..OUTPUT_LEN.val`. -/

set_option maxHeartbeats 1600000 in
/-- For every byte index `k` (as a Nat), the squeeze closure's `call`,
    when applied with the captured state `(rate, state)` and the
    argument `⟨BitVec.ofNat _ k⟩`, equals `.ok ⟨...⟩` where the byte
    is exactly `squeeze_byte_at s_b (k - b*rate)`, with
    `b = k / rate.val` and the precondition that
    `iterate_keccak_f ⟨BitVec.ofNat _ b⟩ state = .ok s_b`.

    This is the pure (Result-level) characterization driven directly
    by the chain of `Usize` ops in the closure body. The `iterate`
    success is supplied as a hypothesis. -/
private theorem squeeze_closure_call_eq
    {OUTPUT_LEN : Std.Usize}
    (rate : Std.Usize) (state : Std.Array Std.U64 25#usize)
    (k : Nat) (h_k_le : k ≤ Std.Usize.max)
    (h_rate_pos : 0 < rate.val)
    (h_rate_bnd : rate.val ≤ 200)
    (s_b : Std.Array Std.U64 25#usize)
    (h_iter :
      sponge.iterate_keccak_f ⟨BitVec.ofNat _ (k / rate.val)⟩ state = .ok s_b) :
    (sponge.squeeze.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
        (OUTPUT_LEN := OUTPUT_LEN) (rate, state) ⟨BitVec.ofNat _ k⟩)
      = .ok (squeeze_byte_at s_b (k - (k / rate.val) * rate.val),
             ((rate, state) : sponge.squeeze.closure OUTPUT_LEN)) := by
  -- args.val = k (since k ≤ Usize.max).
  set args : Std.Usize := ⟨BitVec.ofNat _ k⟩ with hargs_def
  have h_args_val : args.val = k := usize_ofNat_toNat k h_k_le
  -- rate.val ≠ 0 used by div/rem.
  have h_rate_nz : rate.val ≠ 0 := Nat.pos_iff_ne_zero.mp h_rate_pos
  -- Step 1: b = args / rate.
  obtain ⟨b, h_b_eq, h_b_val_raw, _⟩ :=
    Std.UScalar.div_bv_spec args (y := rate) h_rate_nz
  have h_b_val : b.val = k / rate.val := by
    rw [h_b_val_raw, h_args_val]
  -- Step 2: i1 = b * rate. Bound: b*rate ≤ args = k ≤ Usize.max.
  have h_brate_le : b.val * rate.val ≤ k := by
    rw [h_b_val]; exact Nat.div_mul_le_self k rate.val
  have h_i1_bnd : b.val * rate.val ≤ Std.UScalar.max .Usize := by
    rw [Std.UScalar.max_USize_eq]; omega
  obtain ⟨i1, h_i1_eq, h_i1_val_raw, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.mul_bv_spec (x := b) (y := rate) h_i1_bnd)
  have h_i1_val : i1.val = b.val * rate.val := by
    rw [h_i1_val_raw]
  -- Step 3: j = args - i1. Bound: i1 ≤ args.
  have h_i1_le_args : i1.val ≤ args.val := by
    rw [h_args_val, h_i1_val]; exact h_brate_le
  obtain ⟨j, h_j_eq, h_j_val_raw, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.sub_bv_spec (x := args) (y := i1) h_i1_le_args)
  have h_j_val : j.val = args.val - i1.val := by
    rw [h_j_val_raw]
  have h_j_eq_residue : j.val = k - (k / rate.val) * rate.val := by
    rw [h_j_val, h_args_val, h_i1_val, h_b_val]
  -- j.val < rate.val: since k = b*rate + j and j = k - b*rate, j < rate.
  have h_j_lt_rate : j.val < rate.val := by
    rw [h_j_eq_residue]
    have h_d : k = (k / rate.val) * rate.val + k % rate.val := by
      rw [Nat.div_add_mod' k rate.val]
    have h_eq_mod : k - (k / rate.val) * rate.val = k % rate.val := by omega
    rw [h_eq_mod]
    exact Nat.mod_lt _ h_rate_pos
  -- Step 4: iterate_keccak_f b state. Given by h_iter (after rewriting b).
  have h_b_eq_iter : b = (⟨BitVec.ofNat _ (k / rate.val)⟩ : Std.Usize) := by
    apply Std.UScalar.eq_of_val_eq
    rw [h_b_val]
    show k / rate.val = (BitVec.ofNat _ (k / rate.val)).toNat
    have h_div_le : k / rate.val ≤ k := Nat.div_le_self _ _
    have h_div_le_max : k / rate.val ≤ Std.Usize.max := le_trans h_div_le h_k_le
    symm; exact usize_ofNat_toNat _ h_div_le_max
  have h_iter' : sponge.iterate_keccak_f b state = .ok s_b := by
    rw [h_b_eq_iter]; exact h_iter
  -- Step 5: i2 = j / 8. Under the new spec layout, byte block j/8 lives at
  -- spec position j/8 directly (no transpose); no byte_lane_idx step is
  -- needed in the extracted closure.
  obtain ⟨i2, h_i2_eq, h_i2_val_raw, _⟩ :=
    Std.UScalar.div_bv_spec j (y := (8#usize : Std.Usize)) (by decide)
  have h_i2_val : i2.val = j.val / 8 := by rw [h_i2_val_raw]; rfl
  -- i2.val < 25 since j.val < rate.val ≤ 200 and i2 = j/8.
  have h_i2_lt : i2.val < 25 := by
    rw [h_i2_val]
    have : j.val < 200 := lt_of_lt_of_le h_j_lt_rate h_rate_bnd
    omega
  -- Step 7: i4 = Array.index_usize s_b i2 = s_b.val[i2.val]!.
  have h_i2_lt_sb : i2.val < s_b.val.length := by
    have : s_b.val.length = 25 := s_b.property
    rw [this]; exact h_i2_lt
  have h_i2_lt_sb' : i2.val < s_b.length := by
    show i2.val < s_b.val.length; exact h_i2_lt_sb
  obtain ⟨i4, h_i4_eq, h_i4_val_eq⟩ :=
    Std.WP.spec_imp_exists (Std.Array.index_usize_spec s_b i2 h_i2_lt_sb')
  -- Step 8: a1 = U64.to_le_bytes i4
  have h_a1_eq :
      CoreModels.core.num.U64.to_le_bytes i4
        = .ok (Std.core.num.U64.to_le_bytes i4) := by
    unfold CoreModels.core.num.U64.to_le_bytes
           CoreModels.rust_primitives.arithmetic.to_le_bytes_u64
    rfl
  set a1 : Std.Array Std.U8 8#usize := Std.core.num.U64.to_le_bytes i4 with ha1_def
  -- Step 9: i5 = j % 8.
  obtain ⟨i5, h_i5_eq, h_i5_val_raw, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.rem_bv_spec j (y := (8#usize : Std.Usize)) (by decide))
  have h_i5_val : i5.val = j.val % 8 := by rw [h_i5_val_raw]; rfl
  have h_i5_lt : i5.val < 8 := by rw [h_i5_val]; exact Nat.mod_lt _ (by decide)
  -- Step 10: final = Array.index_usize a1 i5.
  have h_i5_lt_a1 : i5.val < a1.length := by
    show i5.val < a1.val.length
    have h_len : a1.val.length = 8 := a1.property
    rw [h_len]; exact h_i5_lt
  obtain ⟨v_final, h_v_final_eq, h_v_final_val⟩ :=
    Std.WP.spec_imp_exists (Std.Array.index_usize_spec a1 i5 h_i5_lt_a1)
  -- Compute v_final's actual byte value.
  set u : Std.U64 := s_b.val[i2.val]! with hu_def
  have h_i4_eq_u : i4 = u := by
    rw [hu_def, h_i4_val_eq]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h_i2_lt_sb]
  have h_a1_unfold : a1.val
      = (BitVec.toLEBytes u.bv).map (@Std.UScalar.mk .U8) := by
    show (Std.core.num.U64.to_le_bytes i4).val = _
    rw [h_i4_eq_u]
    unfold Std.core.num.U64.to_le_bytes
    rfl
  have h_len_bytes : (BitVec.toLEBytes u.bv).length = 8 := by
    have h := @BitVec.toLEBytes_length 64 u.bv
    -- h : toLEBytes.length = 64 / 8
    exact h
  have h_jmod_lt : j.val % 8 < 8 := Nat.mod_lt _ (by decide)
  have h_v_final_byte :
      v_final = ⟨(BitVec.toLEBytes u.bv)[j.val % 8]!⟩ := by
    have h_i5_lt_a1' : i5.val < a1.val.length := by
      have : a1.val.length = 8 := a1.property
      rw [this]; exact h_i5_lt
    rw [show v_final = a1.val[i5.val]! from by
          rw [h_v_final_val]; exact (getElem!_pos a1.val i5.val h_i5_lt_a1').symm]
    rw [h_a1_unfold, h_i5_val]
    -- (xs.map UScalar.mk)[j.val % 8]! = ⟨xs[j.val % 8]!⟩
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map]
    rw [List.getElem?_eq_getElem (h := by rw [h_len_bytes]; exact h_jmod_lt)]
    rw [Option.map_some, Option.getD_some]
    rw [List.getElem!_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (h := by rw [h_len_bytes]; exact h_jmod_lt)]
    rw [Option.getD_some]
  -- Assemble: walk the closure body. New closure body (no byte_lane_idx).
  unfold sponge.squeeze.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
  show (do
    let b' ← args / rate
    let i1' ← b' * rate
    let j' ← args - i1'
    let state_b' ← sponge.iterate_keccak_f b' state
    let i2' ← j' / 8#usize
    let i3' ← Std.Array.index_usize state_b' i2'
    let a1' ← CoreModels.core.num.U64.to_le_bytes i3'
    let i4' ← j' % 8#usize
    let i5' ← Std.Array.index_usize a1' i4'
    Result.ok (i5', ((rate, state) : sponge.squeeze.closure OUTPUT_LEN))) = _
  rw [show args / rate = (.ok b : Result Std.Usize) from h_b_eq]; simp only [bind_tc_ok]
  rw [show b * rate = (.ok i1 : Result Std.Usize) from h_i1_eq]; simp only [bind_tc_ok]
  rw [show args - i1 = (.ok j : Result Std.Usize) from h_j_eq]; simp only [bind_tc_ok]
  rw [h_iter']; simp only [bind_tc_ok]
  rw [show j / 8#usize = (.ok i2 : Result Std.Usize) from h_i2_eq]; simp only [bind_tc_ok]
  rw [h_i4_eq]; simp only [bind_tc_ok]
  rw [h_a1_eq]; simp only [bind_tc_ok]
  rw [show j % 8#usize = (.ok i5 : Result Std.Usize) from h_i5_eq]; simp only [bind_tc_ok]
  rw [h_v_final_eq]; simp only [bind_tc_ok]
  -- Now goal: .ok (v_final, c) = .ok (squeeze_byte_at s_b (k - (k/rate.val)*rate.val), c)
  -- Under new layout, squeeze_byte_at indexes s_b at (j/8) directly.
  have h_u_eq :
      u = s_b.val[(k - k / rate.val * rate.val) / 8]! := by
    show s_b.val[i2.val]! = _
    rw [h_i2_val, h_j_eq_residue]
  have h_byte_eq :
      ⟨(BitVec.toLEBytes u.bv)[j.val % 8]!⟩
        = squeeze_byte_at s_b (k - k / rate.val * rate.val) := by
    unfold squeeze_byte_at
    rw [h_u_eq, h_j_eq_residue]
  rw [h_v_final_byte, h_byte_eq]
  rfl

/-- **Pure block-wise characterization of `sponge.squeeze`.**

If, for every byte index `k < OUTPUT_LEN.val`, `iterate_keccak_f (k/rate)
state` succeeds (yielding some `s_b k`), then `sponge.squeeze` succeeds
and byte `k` of the result equals
`squeeze_byte_at (s_b k) (k - (k/rate.val) * rate.val)`.

The hypothesis is conditional because `iterate_keccak_f` is a
`partial_fixpoint` and Lean does not know it terminates a priori; the
totality is established at use sites via Bridge 1's
`keccakf1600_equiv_hacspec` (which guarantees `keccak_f.keccak_f`
succeeds on every lifted impl state).

Used by the top-level `keccak` per-byte equivalence theorem to factor
`sponge.squeeze` through `iterate_keccak_f`. -/
theorem sponge_squeeze_byte_eq
    (OUTPUT_LEN : Std.Usize) (state : Std.Array Std.U64 25#usize)
    (rate : Std.Usize)
    (h_rate_pos : 0 < rate.val)
    (_h_rate_mod : rate.val % 8 = 0)
    (h_rate_bnd : rate.val ≤ 200)
    (s_b : Nat → Std.Array Std.U64 25#usize)
    (h_iter : ∀ k : Nat, k < OUTPUT_LEN.val →
      sponge.iterate_keccak_f
          ⟨BitVec.ofNat _ (k / rate.val)⟩ state = .ok (s_b k)) :
    ∃ a : Std.Array Std.U8 OUTPUT_LEN,
      sponge.squeeze OUTPUT_LEN state rate = .ok a
      ∧ ∀ k : Nat, k < OUTPUT_LEN.val →
          a.val[k]! = squeeze_byte_at (s_b k) (k - (k / rate.val) * rate.val) := by
  unfold sponge.squeeze
  -- We use createi_pure_eq with f := fun k => squeeze_byte_at (s_b k) (k - ...).
  set f : Nat → Std.U8 := fun k =>
    squeeze_byte_at (s_b k) (k - (k / rate.val) * rate.val) with hf_def
  have h_k_le_max : ∀ k : Nat, k < OUTPUT_LEN.val → k ≤ Std.Usize.max := by
    intro k hk
    have h_bound : OUTPUT_LEN.val ≤ Std.Usize.max := by scalar_tac
    omega
  -- Build the per-k call_mut equation.
  have h_call_mut_eq : ∀ k : Nat, k < OUTPUT_LEN.val →
      (sponge.squeeze.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
          OUTPUT_LEN).call_mut (rate, state) ⟨BitVec.ofNat _ k⟩
        = .ok (f k, (rate, state)) := by
    intro k hk
    show sponge.squeeze.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
            (rate, state) ⟨BitVec.ofNat _ k⟩
          = .ok (f k, (rate, state))
    rw [squeeze_closure_call_eq (OUTPUT_LEN := OUTPUT_LEN) rate state k
          (h_k_le_max k hk) h_rate_pos h_rate_bnd (s_b k) (h_iter k hk)]
  -- Apply createi_pure_eq.
  have h_createi :=
    _root_.libcrux_iot_sha3.Foundation.createi_pure_eq OUTPUT_LEN
      (sponge.squeeze.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 OUTPUT_LEN)
      (rate, state) f h_call_mut_eq
  refine ⟨_, h_createi, ?_⟩
  intro k hk
  show ((List.range OUTPUT_LEN.val).map f)[k]! = f k
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hk]
  rfl

end libcrux_iot_sha3.Sponge
