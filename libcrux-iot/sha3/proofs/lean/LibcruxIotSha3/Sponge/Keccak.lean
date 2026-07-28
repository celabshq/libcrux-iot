/-
  # Top-level `keccak.keccak` ↔ `sponge.keccak`.

  Largest composition in the sponge proofs: the impl function
  `keccak.keccak` (full pipeline: absorb-full-loop + absorb-final +
  first-output-block + squeeze-loop + optional trailing block) matches
  the spec `sponge.keccak` byte-by-byte.

  ## Post

  ```
  @[spec]
  theorem keccak.keccak_keccak_spec
      (RATE DELIM data out)
      (+ side conditions) :
      ⦃⌜True⌝⦄ keccak.keccak RATE DELIM data out
      ⦃⇓ r => ⌜ ∃ spec_out,
                  sponge.keccak ⟨Slice.len out⟩ RATE DELIM data = .ok spec_out
                  ∧ r.val.length = out.val.length
                  ∧ ∀ k < out.val.length, r.val[k]! = spec_out.val[k]! ⌝⦄
  ```

  Impl and spec sides are composed as independent `.ok`-equation chains,
  then bridged byte-by-byte.

  ### Impl side
  - `keccak.keccak_loop0_spec` ⇒ `absorb_fold s data RATE n.val = .ok (lift s1)`.
  - `keccak.absorb_final_spec` ⇒ `sponge.absorb_final (lift s1) data ... = .ok (lift s2)`.
  - Case-split on `blocks = 0`:
    - **blocks = 0** branch: `squeeze_first_and_last_spec` ⇒ output's bytes
      come from `lift s2` (no permutation).
    - **blocks ≥ 1** branch: `squeeze_first_block_spec` + `keccak_loop1_invariant`
      + (`squeeze_last_spec` if `last < outlen`) ⇒ output's bytes come from
      `iterate_keccak_f j (lift s2)` for various `j`.

  ### Spec side
  - `sponge.absorb` = `absorb_rec a₀ rate delim data` with `a₀ = Array.repeat 25 0`.
    Via `sponge_absorb_rec_eq_fold` and `absorb_fold_eq_spec`
    (from `Sponge/Absorb.lean`), tie to `absorb_fold s_init data RATE n.val`
    for the new-state `s_init`.
  - `sponge.squeeze` is characterized byte-wise by `sponge_squeeze_byte_eq`
    (from `Sponge/Squeeze.lean`).
-/
import LibcruxIotSha3.Sponge.AbsorbFinal
import LibcruxIotSha3.Sponge.Squeeze
import LibcruxIotSha3.Sponge.Absorb
import LibcruxIotSha3.Sponge.SqueezeBlock

open Aeneas Aeneas.Std Result Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

open libcrux_iot_sha3.Foundation

-- Defensive seal re-issue: no proof in this file may unfold either side
-- of Bridge 1.
set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ## Top-level keccak ↔ sponge.keccak. -/

/-! ### Local helpers. -/

private theorem triple_of_ok_kk {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PredTrans.apply, hp]

private theorem triple_exists_ok_kk {α : Type} {x : Result α}
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

/-! ### Lemma: `KeccakState.new` returns a fresh zero-initialised state. -/

/-- `state.KeccakState.new` always returns `.ok s_new` for the canonical
    initial state `s_new` with `s_new.i.val = 0` and
    `lift s_new = Array.repeat 25 0`. -/
theorem state_KeccakState_new_eq :
    ∃ s_new : state.KeccakState,
      state.KeccakState.new = .ok s_new
      ∧ s_new.i.val = 0
      ∧ Foundation.lift s_new = Std.Array.repeat 25#usize 0#u64 := by
  unfold state.KeccakState.new lane.Lane2U32.zero lane.Lane2U32.from_ints
  refine ⟨_, rfl, rfl, ?_⟩
  rfl

/-! ### Helper: `CoreModels.core.slice.Slice.len` Result-level equation. -/

private theorem slice_len_eq (s : Slice Std.U8) :
    CoreModels.core.slice.Slice.len s = .ok (Std.Slice.len s) := by
  unfold CoreModels.core.slice.Slice.len; rfl

/-! ### Helper: bridge `keccak_loop0` for the trivial n = 0 case.

When `n = 0`, the impl's absorb-full-blocks loop is a no-op. We derive
this via `keccak_loop0_spec` instantiated with `n = 0`. -/

theorem keccak_loop0_zero_terminates
    (RATE : Std.Usize) (data : Slice Std.U8) (s : state.KeccakState)
    (h_i : s.i.val = 0)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_bnd : RATE.val ≤ 200) :
    ∃ r : state.KeccakState,
      keccak.keccak_loop0 RATE { start := 0#usize, «end» := 0#usize } data s 0#usize = .ok r
      ∧ r.i.val = 0
      ∧ Foundation.lift r = Foundation.lift s := by
  have h_n_RATE : (0#usize : Std.Usize).val * RATE.val ≤ data.val.length := by
    show 0 * RATE.val ≤ data.val.length; omega
  have h_off : (0#usize : Std.Usize).val * RATE.val ≤ Std.Usize.max := by
    show 0 * RATE.val ≤ Std.Usize.max; omega
  obtain ⟨r, h_r_eq, h_r_i, h_fold⟩ :=
    triple_exists_ok_kk
      (keccak.keccak_loop0_spec RATE s data 0#usize h_i h_RATE_mod h_RATE_bnd h_n_RATE h_off)
  refine ⟨r, h_r_eq, h_r_i, ?_⟩
  -- `absorb_fold s data RATE 0 = .ok (lift s)` then equals `.ok (lift r)`.
  have h_zero_val : ((0#usize : Std.Usize).val : Nat) = 0 := rfl
  rw [h_zero_val] at h_fold
  have h_fold0 : absorb_fold s data RATE 0 = .ok (Foundation.lift s) := by
    unfold absorb_fold; simp [Nat.fold_zero]
  rw [h_fold0] at h_fold
  -- h_fold : .ok (lift s) = .ok (lift r). Extract.
  injection h_fold with h_eq
  exact h_eq.symm

/-! ### Helper: `iterate_keccak_f 0 = identity`.

When the iteration count is 0, `sponge.iterate_keccak_f 0 s` reduces to
`.ok s`. Derived via `iterate_keccak_f_eq_fold` + `Nat.fold_zero`. -/

theorem iterate_keccak_f_zero
    (state : Std.Array Std.U64 25#usize) :
    sponge.iterate_keccak_f (0#usize : Std.Usize) state = .ok state := by
  rw [iterate_keccak_f_eq_fold]
  unfold iterate_keccak_f_fold
  show Nat.fold ((0#usize : Std.Usize).val) _ _ = _
  show Nat.fold 0 _ _ = _
  rw [Nat.fold_zero]

/-! ### Main theorem: `keccak.keccak_keccak_spec` (blocks = 0 branch).

This lemma lands the `blocks = 0` case end-to-end; the post is the textbook
equality-form. The `blocks ≥ 1` case is handled separately by
`keccak.keccak_keccak_spec_blocks_nonzero`, and the two branches are combined
in the top-level `keccak.keccak_keccak_spec`. -/

-- Set higher heartbeats for this composition Triple.
set_option maxHeartbeats 16000000 in
@[spec]
theorem keccak.keccak_keccak_spec_blocks_zero
    (RATE : Std.Usize) (DELIM : Std.U8) (data : Slice Std.U8)
    (out : Slice Std.U8)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_ge_1 : 1 ≤ RATE.val)
    (h_RATE_le_200 : RATE.val ≤ 200)
    (h_blocks_zero : out.val.length < RATE.val) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccak RATE DELIM data out
    ⦃ ⇓ r => ⌜ ∃ spec_out : Std.Array Std.U8 (Std.Slice.len out),
                sponge.keccak (Std.Slice.len out) RATE DELIM data
                  = .ok spec_out
                ∧ r.val.length = out.val.length
                ∧ ∀ k : Nat, k < out.val.length →
                    r.val[k]! = spec_out.val[k]! ⌝ ⦄ := by
  -- Step 1: `KeccakState.new` produces canonical zero state.
  obtain ⟨s0, h_s0_eq, h_s0_i, h_s0_lift⟩ := state_KeccakState_new_eq
  -- Step 2: precompute the side-condition facts.
  have h_RATE_max : RATE.val ≤ Std.Usize.max := by
    have h200 : (200 : Nat) ≤ Std.Usize.max := by scalar_tac
    omega
  have h_data_len_max : data.val.length ≤ Std.Usize.max := by
    have := data.property; omega
  have h_out_len_max : out.val.length ≤ Std.Usize.max := by
    have := out.property; omega
  -- Step 3: data length decomposition.
  -- The impl computes: i := data.length; n := i/RATE; rem := i%RATE.
  -- So data.length = n*RATE + rem with rem < RATE.
  set n_nat : Nat := data.val.length / RATE.val with hn_nat_def
  set rem_nat : Nat := data.val.length % RATE.val with hrem_nat_def
  have h_n_rem : n_nat * RATE.val + rem_nat = data.val.length := by
    rw [hn_nat_def, hrem_nat_def]
    exact Nat.div_add_mod' data.val.length RATE.val
  have h_n_rate_le : n_nat * RATE.val ≤ data.val.length := by omega
  have h_n_rate_max : n_nat * RATE.val ≤ Std.Usize.max := by
    have := data.property; omega
  have h_rem_lt_RATE : rem_nat < RATE.val := Nat.mod_lt _ (by omega)
  -- Step 4: i (= data length).
  set i_us : Std.Usize := Std.Slice.len data with hi_us_def
  have h_i_us_val : i_us.val = data.val.length := Std.Slice.len_val data
  have h_i_us_eq : CoreModels.core.slice.Slice.len data = .ok i_us := slice_len_eq data
  -- Step 5: n (= i_us / RATE) = ⟨BitVec n_nat⟩.
  have h_RATE_nz : RATE.val ≠ 0 := by omega
  obtain ⟨n_us, h_n_us_eq, h_n_us_val_eq, _⟩ :=
    Std.UScalar.div_bv_spec i_us (y := RATE) h_RATE_nz
  have h_n_us_val : n_us.val = n_nat := by
    rw [h_n_us_val_eq, h_i_us_val]
  -- Step 6: rem = i_us % RATE.
  obtain ⟨rem_us, h_rem_us_eq, h_rem_us_val_eq, _⟩ :=
    Std.WP.spec_imp_exists
      (Std.UScalar.rem_bv_spec i_us (y := RATE) h_RATE_nz)
  have h_rem_us_val : rem_us.val = rem_nat := by
    rw [h_rem_us_val_eq, h_i_us_val]
  -- Step 7: outlen (= Slice.len out).
  set outlen_us : Std.Usize := Std.Slice.len out with houtlen_us_def
  have h_outlen_us_val : outlen_us.val = out.val.length := Std.Slice.len_val out
  have h_outlen_us_eq : CoreModels.core.slice.Slice.len out = .ok outlen_us := slice_len_eq out
  -- Step 8: blocks (= outlen / RATE) = 0 (since outlen < RATE).
  obtain ⟨blocks_us, h_blocks_us_eq, h_blocks_us_val_eq, _⟩ :=
    Std.UScalar.div_bv_spec outlen_us (y := RATE) h_RATE_nz
  have h_blocks_us_val : blocks_us.val = 0 := by
    rw [h_blocks_us_val_eq, h_outlen_us_val]
    exact Nat.div_eq_of_lt h_blocks_zero
  have h_blocks_us_eq_zero : blocks_us = 0#usize :=
    Std.UScalar.eq_of_val_eq h_blocks_us_val
  -- Step 9: i1 (= outlen % RATE) = outlen.
  obtain ⟨i1_us, h_i1_us_eq, h_i1_us_val_eq, _⟩ :=
    Std.WP.spec_imp_exists
      (Std.UScalar.rem_bv_spec outlen_us (y := RATE) h_RATE_nz)
  have h_i1_us_val : i1_us.val = out.val.length := by
    rw [h_i1_us_val_eq, h_outlen_us_val]
    exact Nat.mod_eq_of_lt h_blocks_zero
  -- Step 10: last (= outlen - i1) = 0.
  have h_i1_le_outlen : i1_us.val ≤ outlen_us.val := by
    rw [h_i1_us_val, h_outlen_us_val]
  obtain ⟨last_us, h_last_us_eq, h_last_us_val_eq, _⟩ :=
    Std.WP.spec_imp_exists
      (Std.UScalar.sub_bv_spec (x := outlen_us) (y := i1_us) h_i1_le_outlen)
  have h_last_us_val : last_us.val = 0 := by
    rw [h_last_us_val_eq, h_outlen_us_val, h_i1_us_val]; omega
  -- Step 11: keccak_loop0 RATE {0..n_us} data s0.
  have h_keccak_loop0_pre_n_RATE : n_us.val * RATE.val ≤ data.val.length := by
    rw [h_n_us_val]; exact h_n_rate_le
  have h_keccak_loop0_pre_off : n_us.val * RATE.val ≤ Std.Usize.max := by
    rw [h_n_us_val]; exact h_n_rate_max
  obtain ⟨s1, h_s1_eq, h_s1_i, h_s1_fold⟩ :=
    triple_exists_ok_kk
      (keccak.keccak_loop0_spec RATE s0 data n_us h_s0_i h_RATE_mod h_RATE_le_200
        h_keccak_loop0_pre_n_RATE h_keccak_loop0_pre_off)
  -- Step 12: absorb_final RATE DELIM s1 data (i_us - rem_us) rem_us.
  -- i_us - rem_us = data.length - rem_nat = n_nat * RATE.
  have h_rem_le_i : rem_us.val ≤ i_us.val := by
    rw [h_rem_us_val, h_i_us_val]; omega
  obtain ⟨i3_us, h_i3_us_eq, h_i3_us_val_eq, _⟩ :=
    Std.WP.spec_imp_exists
      (Std.UScalar.sub_bv_spec (x := i_us) (y := rem_us) h_rem_le_i)
  have h_i3_us_val : i3_us.val = n_nat * RATE.val := by
    rw [h_i3_us_val_eq, h_i_us_val, h_rem_us_val]; omega
  -- Absorb_final's preconditions.
  have h_absorb_final_h_len_lt : rem_us.val < RATE.val := by rw [h_rem_us_val]; exact h_rem_lt_RATE
  have h_absorb_final_h_last_len : i3_us.val + rem_us.val ≤ data.val.length := by
    rw [h_i3_us_val, h_rem_us_val]; omega
  have h_absorb_final_h_off : i3_us.val + rem_us.val ≤ Std.Usize.max := by
    rw [h_i3_us_val, h_rem_us_val]; omega
  obtain ⟨s2, h_s2_eq, h_s2_i, h_s2_spec⟩ :=
    triple_exists_ok_kk
      (keccak.absorb_final_spec RATE DELIM s1 data i3_us rem_us h_s1_i h_absorb_final_h_len_lt
        h_RATE_mod h_RATE_ge_1 h_RATE_le_200 h_absorb_final_h_last_len h_absorb_final_h_off)
  -- Step 13: squeeze_first_and_last RATE s2 out.
  have h_out_le_RATE : out.val.length ≤ RATE.val := by omega
  obtain ⟨r_out, h_r_out_eq, h_r_out_len, h_r_out_bytes⟩ :=
    triple_exists_ok_kk
      (keccak.squeeze_first_and_last_spec RATE s2 out h_RATE_mod h_RATE_le_200 h_out_le_RATE)
  -- Step 14: impl-side equation chain → keccak.keccak ... = .ok r_out.
  have h_impl_eq : keccak.keccak RATE DELIM data out = .ok r_out := by
    unfold keccak.keccak
    rw [h_i_us_eq]; simp only [bind_tc_ok]
    rw [h_n_us_eq]; simp only [bind_tc_ok]
    rw [h_rem_us_eq]; simp only [bind_tc_ok]
    rw [h_outlen_us_eq]; simp only [bind_tc_ok]
    rw [h_blocks_us_eq]; simp only [bind_tc_ok]
    rw [h_i1_us_eq]; simp only [bind_tc_ok]
    rw [h_last_us_eq]; simp only [bind_tc_ok]
    rw [h_s0_eq]; simp only [bind_tc_ok]
    rw [h_s1_eq]; simp only [bind_tc_ok]
    -- The second `Slice.len data` call: was already collapsed by the first rw above.
    rw [h_i3_us_eq]; simp only [bind_tc_ok]
    rw [h_s2_eq]; simp only [bind_tc_ok]
    -- Now the if: blocks_us = 0#usize.
    rw [if_pos h_blocks_us_eq_zero]
    exact h_r_out_eq
  -- Step 15: spec-side. We want `sponge.keccak outlen_us RATE DELIM data = .ok spec_out`
  -- with byte-by-byte equality `spec_out.val[k]! = r_out.val[k]!`.
  -- sponge.keccak = sponge.absorb >>= sponge.squeeze.
  -- sponge.absorb data = sponge.absorb_rec (repeat 25 0) RATE DELIM data.
  -- By `sponge_absorb_rec_eq_fold` n_nat: this peels n_nat full absorb_blocks then
  -- recurses on a tail of length rem_nat < RATE, which by `unfold_short` becomes
  -- `absorb_final`. Composing with `absorb_fold_eq_spec` and the impl chain s1, s2:
  --   sponge.absorb data = .ok (lift s2).
  -- We derive this from h_s1_fold and h_s2_spec.
  -- h_s1_fold : absorb_fold s0 data RATE n_us.val = .ok (lift s1).
  -- We use absorb_fold_eq_spec to translate to absorb_fold_spec (lift s0) data RATE n_us.val.
  have h_fold_spec : absorb_fold_spec (Foundation.lift s0) data RATE n_us.val
                      = .ok (Foundation.lift s1) := by
    rw [← absorb_fold_eq_spec]; exact h_s1_fold
  -- h_s2_spec : sponge.absorb_final (lift s1) data i3_us rem_us RATE DELIM = .ok (lift s2).
  -- Now compose via sponge_absorb_rec_eq_fold + unfold_short.
  have h_absorb_eq : sponge.absorb RATE DELIM data = .ok (Foundation.lift s2) := by
    unfold sponge.absorb
    -- Goal: `let a := Array.repeat 25 0; sponge.absorb_rec a RATE DELIM data = .ok (lift s2)`.
    show sponge.absorb_rec (Std.Array.repeat 25#usize 0#u64) RATE DELIM data
         = .ok (Foundation.lift s2)
    rw [← h_s0_lift]
    -- Now: sponge.absorb_rec (lift s0) RATE DELIM data = .ok (lift s2).
    rw [sponge_absorb_rec_eq_fold (Foundation.lift s0) RATE DELIM data n_nat (by rw [hn_nat_def]; exact h_n_rate_le)]
    -- Now: absorb_fold_spec (lift s0) data RATE n_nat >>= fun s_n =>
    --        absorb_rec s_n RATE DELIM ⟨data.drop (n_nat*RATE), _⟩
    --      = .ok (lift s2).
    -- Step A: absorb_fold_spec (lift s0) data RATE n_nat = .ok (lift s1).
    have h_fold_spec_n : absorb_fold_spec (Foundation.lift s0) data RATE n_nat
                        = .ok (Foundation.lift s1) := by
      rw [← h_n_us_val]; exact h_fold_spec
    rw [h_fold_spec_n]; simp only [bind_tc_ok]
    -- Step B: absorb_rec (lift s1) RATE DELIM ⟨data.drop (n_nat * RATE), _⟩ = .ok (lift s2).
    -- We apply `sponge_absorb_rec_unfold_short` since the tail length is rem_nat < RATE.
    set tail : Slice Std.U8 :=
      ⟨data.val.drop (n_nat * RATE.val), by
        rw [List.length_drop]; have := data.property; omega⟩ with htail_def
    have h_tail_len : tail.val.length = rem_nat := by
      show (data.val.drop (n_nat * RATE.val)).length = _
      rw [List.length_drop]; omega
    have h_tail_lt_rate : tail.val.length < RATE.val := by
      rw [h_tail_len]; exact h_rem_lt_RATE
    rw [sponge_absorb_rec_unfold_short (Foundation.lift s1) RATE DELIM tail h_tail_lt_rate]
    -- Now goal: sponge.absorb_final (lift s1) tail 0#usize (Slice.len tail) RATE DELIM
    --        = .ok (lift s2).
    -- We have h_s2_spec : sponge.absorb_final (lift s1) data i3_us rem_us RATE DELIM = .ok (lift s2).
    -- The two absorb_final calls have:
    --   LHS: message = tail (msg.drop (n*rate)), msg_offset = 0, remaining = Slice.len tail (= rem_nat).
    --   RHS: message = data, msg_offset = i3_us (= n*rate), remaining = rem_us (= rem_nat).
    -- Both extract the same bytes (data[n*rate..data.length]) via `pad_last_block`.
    -- Show LHS = RHS by `pad_last_block_eq`.
    -- We compute (Slice.len tail).val = tail.length = rem_nat = rem_us.val.
    have h_slt_eq_rem : Std.Slice.len tail = rem_us := by
      apply Std.UScalar.eq_of_val_eq
      simp [Std.Slice.len, h_tail_len, h_rem_us_val]
    rw [h_slt_eq_rem]
    -- Now LHS: sponge.absorb_final (lift s1) tail 0#usize rem_us RATE DELIM.
    -- RHS: sponge.absorb_final (lift s1) data i3_us rem_us RATE DELIM.
    -- Show these are equal by reducing to the same `pad_last_block`.
    rw [show sponge.absorb_final (Foundation.lift s1) tail 0#usize rem_us RATE DELIM
          = sponge.absorb_final (Foundation.lift s1) data i3_us rem_us RATE DELIM from ?_]
    · exact h_s2_spec
    · -- pad_last_block tail 0 rem RATE DELIM = pad_last_block data i3_us rem RATE DELIM.
      unfold sponge.absorb_final
      -- Both have form: do let block ← pad_last_block ...; ...
      have h_pad_eq :
          sponge.pad_last_block tail 0#usize rem_us RATE DELIM
            = sponge.pad_last_block data i3_us rem_us RATE DELIM := by
        unfold sponge.pad_last_block
        -- Both produce a buffer; they differ only in the `s1` slice extracted.
        -- Reduce both `let i ← off + remaining`.
        -- LHS: 0#usize + rem_us = .ok rem_us.
        have h_lhs_add : (0#usize : Std.Usize) + rem_us = (.ok rem_us : Result Std.Usize) := by
          have h_bnd : (0#usize : Std.Usize).val + rem_us.val ≤ Std.UScalar.max .Usize := by
            rw [Std.UScalar.max_USize_eq]; show 0 + rem_us.val ≤ Std.Usize.max
            rw [h_rem_us_val]; omega
          obtain ⟨v, h_eq_v, h_v_val_eq, _⟩ :=
            Std.WP.spec_imp_exists
              (Std.UScalar.add_bv_spec (x := (0#usize : Std.Usize)) (y := rem_us) h_bnd)
          have h_v_val : v.val = rem_us.val := by
            rw [h_v_val_eq]; show 0 + rem_us.val = rem_us.val; omega
          have h_v_eq : v = rem_us := Std.UScalar.eq_of_val_eq h_v_val
          rw [h_eq_v, h_v_eq]
        rw [h_lhs_add]; simp only [bind_tc_ok]
        -- RHS: i3_us + rem_us = .ok i_us (since i3_us.val + rem_us.val = n*RATE + rem = data.length = i_us.val).
        have h_rhs_add : i3_us + rem_us = (.ok i_us : Result Std.Usize) := by
          have h_bnd : i3_us.val + rem_us.val ≤ Std.UScalar.max .Usize := by
            rw [Std.UScalar.max_USize_eq, h_i3_us_val, h_rem_us_val]; omega
          obtain ⟨v, h_eq_v, h_v_val_eq, _⟩ :=
            Std.WP.spec_imp_exists
              (Std.UScalar.add_bv_spec (x := i3_us) (y := rem_us) h_bnd)
          have h_v_val : v.val = i_us.val := by
            rw [h_v_val_eq, h_i3_us_val, h_rem_us_val, h_i_us_val]; omega
          have h_v_eq : v = i_us := Std.UScalar.eq_of_val_eq h_v_val
          rw [h_eq_v, h_v_eq]
        rw [h_rhs_add]; simp only [bind_tc_ok]
        -- Now both sides have slice indices that produce the same byte sequence.
        -- LHS: index tail [0, rem_us]. Bytes = tail.val.slice 0 rem.val = tail.val (= data.drop n*rate, length rem).
        -- RHS: index data [i3_us, i_us]. Bytes = data.val.slice (n*rate) (data.length).
        -- = data.val.drop (n*rate) since (data.length - n*rate) covers the whole drop.
        -- Show both indices yield the same `Slice`.
        have h_lhs_idx :
            CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
              (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
              tail { start := 0#usize, «end» := rem_us }
            = .ok tail := by
          unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
                 CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                 core.slice.index.Slice.index
                 core.slice.index.SliceIndexRangeUsizeSlice.index
          have h0 : (0#usize : Std.Usize) ≤ rem_us := by
            show (0 : Nat) ≤ rem_us.val; omega
          have h1' : (⟨0#usize, rem_us⟩ : core.ops.range.Range Std.Usize).end.val ≤ tail.length := by
            show rem_us.val ≤ tail.val.length
            rw [h_tail_len, h_rem_us_val]
          simp [h0, h1']
          apply Subtype.ext
          show tail.val.slice ((0#usize : Std.Usize).val) rem_us.val = tail.val
          rw [show ((0#usize : Std.Usize).val : Nat) = 0 from rfl, h_rem_us_val]
          unfold List.slice
          rw [List.drop_zero]
          rw [List.take_of_length_le (by rw [h_tail_len]; omega)]
        have h_rhs_idx :
            CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
              (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
              data { start := i3_us, «end» := i_us }
            = .ok tail := by
          unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
                 CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                 core.slice.index.Slice.index
                 core.slice.index.SliceIndexRangeUsizeSlice.index
          have h0 : i3_us ≤ i_us := by
            show i3_us.val ≤ i_us.val; rw [h_i3_us_val, h_i_us_val]; omega
          have h1' : (⟨i3_us, i_us⟩ : core.ops.range.Range Std.Usize).end.val ≤ data.length := by
            show i_us.val ≤ data.length
            rw [h_i_us_val]
          simp [h0, h1']
          apply Subtype.ext
          show data.val.slice i3_us.val i_us.val = tail.val
          rw [h_i3_us_val, h_i_us_val]
          show data.val.slice (n_nat * RATE.val) data.val.length = data.val.drop (n_nat * RATE.val)
          unfold List.slice
          rw [List.take_of_length_le (by rw [List.length_drop])]
        rw [h_lhs_idx, h_rhs_idx]
      rw [h_pad_eq]
  -- Step 16: spec-side squeeze. Need:
  --   sponge.squeeze outlen_us (lift s2) RATE = .ok spec_out.
  -- Use sponge_squeeze_byte_eq with the constant `s_b` function (since outlen < RATE,
  -- every k < outlen has k/RATE = 0, and iterate_keccak_f 0 (lift s2) = .ok (lift s2)).
  have h_RATE_pos : 0 < RATE.val := h_RATE_ge_1
  set s_b : Nat → Std.Array Std.U64 25#usize := fun _ => Foundation.lift s2 with hsb_def
  have h_iter_const : ∀ k : Nat, k < outlen_us.val →
      sponge.iterate_keccak_f
          ⟨BitVec.ofNat _ (k / RATE.val)⟩ (Foundation.lift s2) = .ok (s_b k) := by
    intro k hk
    -- k < outlen_us.val = out.length < RATE.val, so k / RATE.val = 0.
    have h_k_div : k / RATE.val = 0 := by
      apply Nat.div_eq_of_lt
      rw [h_outlen_us_val] at hk; omega
    rw [h_k_div]
    -- iterate_keccak_f ⟨BitVec.ofNat _ 0⟩ (lift s2) = .ok (lift s2).
    have h_zero_usize : (⟨BitVec.ofNat _ 0⟩ : Std.Usize) = (0#usize : Std.Usize) := by
      apply Std.UScalar.eq_of_val_eq
      show (BitVec.ofNat _ 0).toNat = (0#usize : Std.Usize).val
      rfl
    rw [h_zero_usize]
    rw [iterate_keccak_f_zero]
  obtain ⟨spec_out, h_spec_squeeze, h_spec_bytes⟩ :=
    sponge_squeeze_byte_eq outlen_us (Foundation.lift s2) RATE h_RATE_pos h_RATE_mod h_RATE_le_200
      s_b h_iter_const
  -- Step 17: compose: sponge.keccak outlen_us RATE DELIM data = .ok spec_out.
  have h_spec_full_eq :
      sponge.keccak outlen_us RATE DELIM data = .ok spec_out := by
    unfold sponge.keccak
    rw [h_absorb_eq]; simp only [bind_tc_ok]
    exact h_spec_squeeze
  -- Step 18: assemble post.
  apply triple_of_ok_kk (v := r_out) h_impl_eq
  refine ⟨spec_out, h_spec_full_eq, h_r_out_len, ?_⟩
  intro k hk
  -- spec_out.val[k]! = squeeze_byte_at (s_b k) (k - (k/RATE.val) * RATE.val)
  --   = squeeze_byte_at (lift s2) (k - 0) = squeeze_byte_at (lift s2) k.
  have h_k_div : k / RATE.val = 0 := by
    apply Nat.div_eq_of_lt; omega
  have h_spec_byte := h_spec_bytes k (by rw [h_outlen_us_val]; exact hk)
  rw [h_spec_byte]
  -- Goal: r_out.val[k]! = squeeze_byte_at (s_b k) (k - (k/RATE.val) * RATE.val).
  unfold squeeze_byte_at
  rw [hsb_def]
  rw [h_k_div]
  show r_out.val[k]! = ⟨(BitVec.toLEBytes
      ((Foundation.lift s2).val[(k - 0 * RATE.val) / 8]!).bv)[(k - 0 * RATE.val) % 8]!⟩
  rw [show k - 0 * RATE.val = k from by omega]
  exact h_r_out_bytes k hk

/-! ### Main theorem: `keccak.keccak_keccak_spec` (blocks ≥ 1 branch).

The `blocks ≥ 1` case requires walking through the full impl pipeline:
`KeccakState.new → keccak_loop0 → absorb_final → squeeze_first_block →
keccak_loop1 → (optional `squeeze_last` for partial trailing block)`.

Bytes are bridged in three regions:
- `[0, RATE)`: from `squeeze_first_block_spec` (no permutation).
- `[RATE, last)`: from the strengthened `keccak_loop1_invariant`
  per-byte clause (one `keccakf1600` per block).
- `[last, outlen)` (if `last < outlen`): from `squeeze_last_spec`. -/

set_option maxHeartbeats 16000000 in
@[spec]
theorem keccak.keccak_keccak_spec_blocks_nonzero
    (RATE : Std.Usize) (DELIM : Std.U8) (data : Slice Std.U8)
    (out : Slice Std.U8)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_ge_1 : 1 ≤ RATE.val)
    (h_RATE_le_200 : RATE.val ≤ 200)
    (h_blocks_nonzero : RATE.val ≤ out.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccak RATE DELIM data out
    ⦃ ⇓ r => ⌜ ∃ spec_out : Std.Array Std.U8 (Std.Slice.len out),
                sponge.keccak (Std.Slice.len out) RATE DELIM data
                  = .ok spec_out
                ∧ r.val.length = out.val.length
                ∧ ∀ k : Nat, k < out.val.length →
                    r.val[k]! = spec_out.val[k]! ⌝ ⦄ := by
  -- Step 1: KeccakState.new.
  obtain ⟨s0, h_s0_eq, h_s0_i, h_s0_lift⟩ := state_KeccakState_new_eq
  -- Step 2: side-condition facts.
  have h_RATE_max : RATE.val ≤ Std.Usize.max := by
    have h200 : (200 : Nat) ≤ Std.Usize.max := by scalar_tac
    omega
  have h_data_len_max : data.val.length ≤ Std.Usize.max := by
    have := data.property; omega
  have h_out_len_max : out.val.length ≤ Std.Usize.max := by
    have := out.property; omega
  -- Step 3: data length decomposition.
  set n_nat : Nat := data.val.length / RATE.val with hn_nat_def
  set rem_nat : Nat := data.val.length % RATE.val with hrem_nat_def
  have h_n_rem : n_nat * RATE.val + rem_nat = data.val.length := by
    rw [hn_nat_def, hrem_nat_def]
    exact Nat.div_add_mod' data.val.length RATE.val
  have h_n_rate_le : n_nat * RATE.val ≤ data.val.length := by omega
  have h_n_rate_max : n_nat * RATE.val ≤ Std.Usize.max := by
    have := data.property; omega
  have h_rem_lt_RATE : rem_nat < RATE.val := Nat.mod_lt _ (by omega)
  -- Step 4: i_us = Slice.len data.
  set i_us : Std.Usize := Std.Slice.len data with hi_us_def
  have h_i_us_val : i_us.val = data.val.length := Std.Slice.len_val data
  have h_i_us_eq : CoreModels.core.slice.Slice.len data = .ok i_us := slice_len_eq data
  -- Step 5: n_us = i_us / RATE.
  have h_RATE_nz : RATE.val ≠ 0 := by omega
  obtain ⟨n_us, h_n_us_eq, h_n_us_val_eq, _⟩ :=
    Std.UScalar.div_bv_spec i_us (y := RATE) h_RATE_nz
  have h_n_us_val : n_us.val = n_nat := by
    rw [h_n_us_val_eq, h_i_us_val]
  -- Step 6: rem_us = i_us % RATE.
  obtain ⟨rem_us, h_rem_us_eq, h_rem_us_val_eq, _⟩ :=
    Std.WP.spec_imp_exists
      (Std.UScalar.rem_bv_spec i_us (y := RATE) h_RATE_nz)
  have h_rem_us_val : rem_us.val = rem_nat := by
    rw [h_rem_us_val_eq, h_i_us_val]
  -- Step 7: outlen_us = Slice.len out.
  set outlen_us : Std.Usize := Std.Slice.len out with houtlen_us_def
  have h_outlen_us_val : outlen_us.val = out.val.length := Std.Slice.len_val out
  have h_outlen_us_eq : CoreModels.core.slice.Slice.len out = .ok outlen_us := slice_len_eq out
  -- Step 8: blocks_us = outlen / RATE.
  set blocks_nat : Nat := out.val.length / RATE.val with hblocks_nat_def
  set i1_nat : Nat := out.val.length % RATE.val with hi1_nat_def
  have h_blocks_pos : 1 ≤ blocks_nat := by
    rw [hblocks_nat_def]; exact Nat.one_le_div_iff (by omega) |>.mpr h_blocks_nonzero
  have h_blocks_outlen : blocks_nat * RATE.val + i1_nat = out.val.length := by
    rw [hblocks_nat_def, hi1_nat_def]
    exact Nat.div_add_mod' out.val.length RATE.val
  have h_i1_lt : i1_nat < RATE.val := Nat.mod_lt _ (by omega)
  obtain ⟨blocks_us, h_blocks_us_eq, h_blocks_us_val_eq, _⟩ :=
    Std.UScalar.div_bv_spec outlen_us (y := RATE) h_RATE_nz
  have h_blocks_us_val : blocks_us.val = blocks_nat := by
    rw [h_blocks_us_val_eq, h_outlen_us_val]
  have h_blocks_us_nz : ¬ blocks_us = 0#usize := by
    intro h
    have : blocks_us.val = 0 := by rw [h]; rfl
    omega
  -- Step 9: i1_us = outlen % RATE.
  obtain ⟨i1_us, h_i1_us_eq, h_i1_us_val_eq, _⟩ :=
    Std.WP.spec_imp_exists
      (Std.UScalar.rem_bv_spec outlen_us (y := RATE) h_RATE_nz)
  have h_i1_us_val : i1_us.val = i1_nat := by
    rw [h_i1_us_val_eq, h_outlen_us_val]
  -- Step 10: last_us = outlen - i1.
  have h_i1_le_outlen : i1_us.val ≤ outlen_us.val := by
    rw [h_i1_us_val, h_outlen_us_val]; omega
  obtain ⟨last_us, h_last_us_eq, h_last_us_val_eq, _⟩ :=
    Std.WP.spec_imp_exists
      (Std.UScalar.sub_bv_spec (x := outlen_us) (y := i1_us) h_i1_le_outlen)
  have h_last_us_val : last_us.val = blocks_nat * RATE.val := by
    rw [h_last_us_val_eq, h_outlen_us_val, h_i1_us_val]; omega
  -- Step 11: keccak_loop0.
  have h_keccak_loop0_pre_n_RATE : n_us.val * RATE.val ≤ data.val.length := by
    rw [h_n_us_val]; exact h_n_rate_le
  have h_keccak_loop0_pre_off : n_us.val * RATE.val ≤ Std.Usize.max := by
    rw [h_n_us_val]; exact h_n_rate_max
  obtain ⟨s1, h_s1_eq, h_s1_i, h_s1_fold⟩ :=
    triple_exists_ok_kk
      (keccak.keccak_loop0_spec RATE s0 data n_us h_s0_i h_RATE_mod h_RATE_le_200
        h_keccak_loop0_pre_n_RATE h_keccak_loop0_pre_off)
  -- Step 12: i3_us = i_us - rem_us.
  have h_rem_le_i : rem_us.val ≤ i_us.val := by
    rw [h_rem_us_val, h_i_us_val]; omega
  obtain ⟨i3_us, h_i3_us_eq, h_i3_us_val_eq, _⟩ :=
    Std.WP.spec_imp_exists
      (Std.UScalar.sub_bv_spec (x := i_us) (y := rem_us) h_rem_le_i)
  have h_i3_us_val : i3_us.val = n_nat * RATE.val := by
    rw [h_i3_us_val_eq, h_i_us_val, h_rem_us_val]; omega
  -- Step 13: absorb_final.
  have h_absorb_final_h_len_lt : rem_us.val < RATE.val := by
    rw [h_rem_us_val]; exact h_rem_lt_RATE
  have h_absorb_final_h_last_len : i3_us.val + rem_us.val ≤ data.val.length := by
    rw [h_i3_us_val, h_rem_us_val]; omega
  have h_absorb_final_h_off : i3_us.val + rem_us.val ≤ Std.Usize.max := by
    rw [h_i3_us_val, h_rem_us_val]; omega
  obtain ⟨s2, h_s2_eq, h_s2_i, h_s2_spec⟩ :=
    triple_exists_ok_kk
      (keccak.absorb_final_spec RATE DELIM s1 data i3_us rem_us h_s1_i
        h_absorb_final_h_len_lt h_RATE_mod h_RATE_ge_1 h_RATE_le_200
        h_absorb_final_h_last_len h_absorb_final_h_off)
  -- Step 14: squeeze_first_block: bytes [0, RATE).
  have h_RATE_le_out : RATE.val ≤ out.val.length := h_blocks_nonzero
  obtain ⟨out1, h_out1_eq, h_out1_len, h_out1_bytes⟩ :=
    triple_exists_ok_kk
      (keccak.squeeze_first_block_spec RATE s2 out h_RATE_mod h_RATE_le_200
        h_RATE_le_out h_RATE_max)
  -- Step 15: keccak_loop1 with strengthened invariant.
  have h_loop1_offset : RATE.val + (blocks_us.val - 1) * RATE.val ≤ out1.val.length := by
    rw [h_out1_len, h_blocks_us_val]
    have h_arith : RATE.val + (blocks_nat - 1) * RATE.val = blocks_nat * RATE.val := by
      have h2 : blocks_nat = (blocks_nat - 1) + 1 := by omega
      conv_rhs => rw [h2]; rw [Nat.add_mul]
      ring
    rw [h_arith]; omega
  have h_loop1_offset_max : RATE.val + (blocks_us.val - 1) * RATE.val ≤ Std.Usize.max := by
    rw [h_blocks_us_val]
    have h_arith : RATE.val + (blocks_nat - 1) * RATE.val = blocks_nat * RATE.val := by
      have h2 : blocks_nat = (blocks_nat - 1) + 1 := by omega
      conv_rhs => rw [h2]; rw [Nat.add_mul]
      ring
    rw [h_arith]
    have : blocks_nat * RATE.val ≤ out.val.length := by omega
    omega
  have h_blocks_us_ge_1 : 1 ≤ blocks_us.val := by rw [h_blocks_us_val]; exact h_blocks_pos
  have h_loop1_call := keccak.keccak_loop1_invariant RATE blocks_us s2 out1 RATE h_s2_i h_RATE_mod
    h_RATE_le_200 (by show 1 ≤ RATE.val; exact h_RATE_ge_1) h_blocks_us_ge_1
    h_loop1_offset h_loop1_offset_max
  obtain ⟨r_loop1, h_loop1_eq, h_loop1_post⟩ := triple_exists_ok_kk h_loop1_call
  obtain ⟨out2, s3, offset⟩ := r_loop1
  obtain ⟨h_out2_len, h_s3_i, h_offset_val, h_fold_blocks, h_loop_bytes, h_loop_prefix⟩ :=
    h_loop1_post
  -- The loop1 post: offset.val = RATE.val + (blocks_us.val - 1) * RATE.val = blocks_nat * RATE.val.
  have h_offset_eq_last : offset.val = blocks_nat * RATE.val := by
    rw [h_offset_val, h_blocks_us_val]
    have h2 : blocks_nat = (blocks_nat - 1) + 1 := by omega
    conv_rhs => rw [h2]; rw [Nat.add_mul]
    ring
  -- And out2.val.length = out1.val.length = out.val.length.
  have h_out2_len_out : out2.val.length = out.val.length := by
    rw [h_out2_len, h_out1_len]
  -- massert side: ¬(last < outlen) ∨ (last = offset).
  -- We have last_us.val = blocks_nat * RATE.val = offset.val.
  have h_last_eq_offset : last_us = offset := by
    apply Std.UScalar.eq_of_val_eq
    rw [h_last_us_val, h_offset_eq_last]
  have h_massert :
      (massert ((¬ (last_us < outlen_us)) || (last_us = offset)) : Result Unit)
        = .ok () := by
    unfold Aeneas.Std.massert
    have h_or : ((¬ (last_us < outlen_us)) || (last_us = offset)) = true := by
      rw [h_last_eq_offset]; simp
    simp [h_last_eq_offset]
  -- Step 16: case-split on `last < outlen`, i.e. i1 ≠ 0.
  by_cases h_partial : last_us.val < outlen_us.val
  · -- Partial trailing block: i1_nat > 0.
    have h_last_lt_us : last_us < outlen_us := by
      show last_us.val < outlen_us.val; exact h_partial
    have h_i1_pos : 0 < i1_nat := by
      rw [h_outlen_us_val, h_last_us_val] at h_partial; omega
    -- Step 17: index_mut RangeFrom out2 { start := offset } ⇒ (s4, index_mut_back).
    have h_offset_le_out2 : offset.val ≤ out2.val.length := by
      rw [h_out2_len_out, h_offset_eq_last]; omega
    obtain ⟨r_idx, h_idx_eq, h_s4_val, h_s4_len, h_s4_back⟩ :=
      triple_exists_ok_kk
        (core_models_Slice_Insts_index_mut_RangeFromUsize_spec out2
          { start := offset } h_offset_le_out2)
    obtain ⟨s4, index_mut_back⟩ := r_idx
    dsimp only at h_s4_val h_s4_len h_s4_back
    -- s4.val.length = out2.val.length - offset.val = i1_nat.
    have h_s4_len' : s4.val.length = i1_nat := by
      rw [h_s4_len, h_out2_len_out, h_offset_eq_last]; omega
    -- Step 18: squeeze_last RATE s3 s4 ⇒ s5 with per-byte equality.
    have h_s4_le_RATE : s4.val.length ≤ RATE.val := by rw [h_s4_len']; omega
    obtain ⟨s5, h_s5_eq, h_s5_len, s_spec_last, h_s5_kf, h_s5_bytes⟩ :=
      triple_exists_ok_kk
        (keccak.squeeze_last_spec RATE s3 s4 h_s3_i h_RATE_mod h_RATE_le_200 h_s4_le_RATE)
    -- Step 19: assemble impl chain → keccak.keccak ... = .ok (index_mut_back s5).
    have h_impl_eq : keccak.keccak RATE DELIM data out = .ok (index_mut_back s5) := by
      unfold keccak.keccak
      rw [h_i_us_eq]; simp only [bind_tc_ok]
      rw [h_n_us_eq]; simp only [bind_tc_ok]
      rw [h_rem_us_eq]; simp only [bind_tc_ok]
      rw [h_outlen_us_eq]; simp only [bind_tc_ok]
      rw [h_blocks_us_eq]; simp only [bind_tc_ok]
      rw [h_i1_us_eq]; simp only [bind_tc_ok]
      rw [h_last_us_eq]; simp only [bind_tc_ok]
      rw [h_s0_eq]; simp only [bind_tc_ok]
      rw [h_s1_eq]; simp only [bind_tc_ok]
      rw [h_i3_us_eq]; simp only [bind_tc_ok]
      rw [h_s2_eq]; simp only [bind_tc_ok]
      -- blocks_us ≠ 0: take else-branch.
      rw [if_neg h_blocks_us_nz]
      rw [h_out1_eq]; simp only [bind_tc_ok]
      rw [h_loop1_eq]; simp only [bind_tc_ok]
      -- The let (out2', s3', offset') := (out2, s3, offset) destructures via match.
      -- Use a manual reduction by change:
      change (do
              massert ((¬ (last_us < outlen_us)) || (last_us = offset))
              if last_us < outlen_us
              then do
                let (s4, index_mut_back) ←
                  CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
                    (CoreModels.core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                      Std.U8) out2 { start := offset }
                let s5 ← keccak.squeeze_last RATE s3 s4
                ok (index_mut_back s5)
              else ok out2) = .ok (index_mut_back s5)
      rw [h_massert]; simp only [bind_tc_ok]
      rw [if_pos h_last_lt_us]
      rw [h_idx_eq]; simp only [bind_tc_ok]
      rw [h_s5_eq]; simp only [bind_tc_ok]
    -- Step 20: spec-side absorb (same as blocks_zero case).
    have h_fold_spec : absorb_fold_spec (Foundation.lift s0) data RATE n_us.val
                        = .ok (Foundation.lift s1) := by
      rw [← absorb_fold_eq_spec]; exact h_s1_fold
    have h_absorb_eq : sponge.absorb RATE DELIM data = .ok (Foundation.lift s2) := by
      unfold sponge.absorb
      show sponge.absorb_rec (Std.Array.repeat 25#usize 0#u64) RATE DELIM data
           = .ok (Foundation.lift s2)
      rw [← h_s0_lift]
      rw [sponge_absorb_rec_eq_fold (Foundation.lift s0) RATE DELIM data n_nat
        (by rw [hn_nat_def]; exact h_n_rate_le)]
      have h_fold_spec_n : absorb_fold_spec (Foundation.lift s0) data RATE n_nat
                          = .ok (Foundation.lift s1) := by
        rw [← h_n_us_val]; exact h_fold_spec
      rw [h_fold_spec_n]; simp only [bind_tc_ok]
      set tail : Slice Std.U8 :=
        ⟨data.val.drop (n_nat * RATE.val), by
          rw [List.length_drop]; have := data.property; omega⟩ with htail_def
      have h_tail_len : tail.val.length = rem_nat := by
        show (data.val.drop (n_nat * RATE.val)).length = _
        rw [List.length_drop]; omega
      have h_tail_lt_rate : tail.val.length < RATE.val := by
        rw [h_tail_len]; exact h_rem_lt_RATE
      rw [sponge_absorb_rec_unfold_short (Foundation.lift s1) RATE DELIM tail h_tail_lt_rate]
      have h_slt_eq_rem : Std.Slice.len tail = rem_us := by
        apply Std.UScalar.eq_of_val_eq
        simp [Std.Slice.len, h_tail_len, h_rem_us_val]
      rw [h_slt_eq_rem]
      rw [show sponge.absorb_final (Foundation.lift s1) tail 0#usize rem_us RATE DELIM
            = sponge.absorb_final (Foundation.lift s1) data i3_us rem_us RATE DELIM from ?_]
      · exact h_s2_spec
      · -- Same pad_last_block equality as in blocks_zero case.
        unfold sponge.absorb_final
        have h_pad_eq :
            sponge.pad_last_block tail 0#usize rem_us RATE DELIM
              = sponge.pad_last_block data i3_us rem_us RATE DELIM := by
          unfold sponge.pad_last_block
          have h_lhs_add : (0#usize : Std.Usize) + rem_us = (.ok rem_us : Result Std.Usize) := by
            have h_bnd : (0#usize : Std.Usize).val + rem_us.val ≤ Std.UScalar.max .Usize := by
              rw [Std.UScalar.max_USize_eq]; show 0 + rem_us.val ≤ Std.Usize.max
              rw [h_rem_us_val]; omega
            obtain ⟨v, h_eq_v, h_v_val_eq, _⟩ :=
              Std.WP.spec_imp_exists
                (Std.UScalar.add_bv_spec (x := (0#usize : Std.Usize)) (y := rem_us) h_bnd)
            have h_v_val : v.val = rem_us.val := by
              rw [h_v_val_eq]; show 0 + rem_us.val = rem_us.val; omega
            have h_v_eq : v = rem_us := Std.UScalar.eq_of_val_eq h_v_val
            rw [h_eq_v, h_v_eq]
          rw [h_lhs_add]; simp only [bind_tc_ok]
          have h_rhs_add : i3_us + rem_us = (.ok i_us : Result Std.Usize) := by
            have h_bnd : i3_us.val + rem_us.val ≤ Std.UScalar.max .Usize := by
              rw [Std.UScalar.max_USize_eq, h_i3_us_val, h_rem_us_val]; omega
            obtain ⟨v, h_eq_v, h_v_val_eq, _⟩ :=
              Std.WP.spec_imp_exists
                (Std.UScalar.add_bv_spec (x := i3_us) (y := rem_us) h_bnd)
            have h_v_val : v.val = i_us.val := by
              rw [h_v_val_eq, h_i3_us_val, h_rem_us_val, h_i_us_val]; omega
            have h_v_eq : v = i_us := Std.UScalar.eq_of_val_eq h_v_val
            rw [h_eq_v, h_v_eq]
          rw [h_rhs_add]; simp only [bind_tc_ok]
          have h_lhs_idx :
              CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
                (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                  Std.U8)
                tail { start := 0#usize, «end» := rem_us }
              = .ok tail := by
            unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
                   CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                   core.slice.index.Slice.index
                   core.slice.index.SliceIndexRangeUsizeSlice.index
            have h0 : (0#usize : Std.Usize) ≤ rem_us := by
              show (0 : Nat) ≤ rem_us.val; omega
            have h1' : (⟨0#usize, rem_us⟩ : core.ops.range.Range Std.Usize).end.val
                        ≤ tail.length := by
              show rem_us.val ≤ tail.val.length
              rw [h_tail_len, h_rem_us_val]
            simp [h0, h1']
            apply Subtype.ext
            show tail.val.slice ((0#usize : Std.Usize).val) rem_us.val = tail.val
            rw [show ((0#usize : Std.Usize).val : Nat) = 0 from rfl, h_rem_us_val]
            unfold List.slice
            rw [List.drop_zero]
            rw [List.take_of_length_le (by rw [h_tail_len]; omega)]
          have h_rhs_idx :
              CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
                (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                  Std.U8)
                data { start := i3_us, «end» := i_us }
              = .ok tail := by
            unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
                   CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                   core.slice.index.Slice.index
                   core.slice.index.SliceIndexRangeUsizeSlice.index
            have h0 : i3_us ≤ i_us := by
              show i3_us.val ≤ i_us.val; rw [h_i3_us_val, h_i_us_val]; omega
            have h1' : (⟨i3_us, i_us⟩ : core.ops.range.Range Std.Usize).end.val ≤ data.length := by
              show i_us.val ≤ data.length
              rw [h_i_us_val]
            simp [h0, h1']
            apply Subtype.ext
            show data.val.slice i3_us.val i_us.val = tail.val
            rw [h_i3_us_val, h_i_us_val]
            show data.val.slice (n_nat * RATE.val) data.val.length = data.val.drop (n_nat * RATE.val)
            unfold List.slice
            rw [List.take_of_length_le (by rw [List.length_drop])]
          rw [h_lhs_idx, h_rhs_idx]
        rw [h_pad_eq]
    -- Step 21: spec-side squeeze using sponge_squeeze_byte_eq.
    have h_RATE_pos : 0 < RATE.val := h_RATE_ge_1
    -- The s_b function: for each k < outlen, return state of iterate (k/RATE) (lift s2).
    -- We know:
    --   * h_fold_blocks : squeeze_fold s2 (blocks_us.val - 1) = .ok (lift s3)
    --   * For each j < (blocks_us.val - 1) * RATE.val (= last - RATE),
    --       squeeze_fold s2 (j/RATE + 1) = .ok s_bj.
    -- We need, for k < outlen, iterate (k/RATE) (lift s2) = .ok s_k where
    --   - k < RATE: k/RATE = 0, iterate 0 (lift s2) = .ok (lift s2). s_k = lift s2.
    --   - RATE ≤ k < last (= blocks*RATE): k/RATE ∈ [1, blocks), via squeeze_fold.
    --   - last ≤ k < outlen: k/RATE = blocks, via iterate^blocks (lift s2) = lift s3 (then keccak_f s3 = s_spec_last).
    -- Use the s_b function valued at the resolved per-block states.
    -- For the per-byte clause, we'll build s_b on case-by-case.
    -- We use sponge_squeeze_byte_eq with the s_b function set to:
    --   k → if k < RATE then lift s2 else if k < blocks*RATE then s_bj else s_spec_last.
    -- Define s_b directly:
    -- Helper: iterate_keccak_f via squeeze_fold-conversion.
    have h_iter_eq_fold : ∀ (n : Nat) (st : Std.Array Std.U64 25#usize),
        n ≤ Std.Usize.max →
        sponge.iterate_keccak_f (⟨BitVec.ofNat _ n⟩ : Std.Usize) st
          = iterate_keccak_f_fold st n := by
      intro n st h_n_le
      rw [iterate_keccak_f_eq_fold]
      -- (⟨BitVec.ofNat _ n⟩ : Usize).val = n.
      have h_val : (⟨BitVec.ofNat _ n⟩ : Std.Usize).val = n := by
        show (BitVec.ofNat _ n).toNat = n
        rw [BitVec.toNat_ofNat]
        apply Nat.mod_eq_of_lt
        have h1 : Std.UScalarTy.Usize.numBits = Std.Usize.numBits := by
          rw [Std.Usize.numBits]
        rw [h1]
        have hpos : 0 < 2 ^ Std.Usize.numBits := Nat.two_pow_pos _
        have h2 : 2 ^ Std.Usize.numBits = Std.Usize.max + 1 := by
          rw [Std.Usize.max]; omega
        omega
      rw [h_val]
    -- Bound: blocks_nat ≤ outlen / RATE so blocks_nat ≤ Std.Usize.max.
    have h_blocks_le_max : blocks_nat ≤ Std.Usize.max := by
      have : blocks_nat ≤ out.val.length := by
        rw [hblocks_nat_def]; exact Nat.div_le_self _ _
      omega
    -- Build the per-byte iterate witness for sponge_squeeze_byte_eq.
    -- We use a "choice" s_b: for k < outlen_us.val, it returns the appropriate state.
    -- Helper: condition for being a "middle" k.
    have h_middle_bound : ∀ k : Nat, RATE.val ≤ k → k < blocks_nat * RATE.val →
        k - RATE.val < (blocks_us.val - 1) * RATE.val := by
      intro k hk_lo hk_hi
      rw [h_blocks_us_val]
      have h_eq : blocks_nat * RATE.val = (blocks_nat - 1) * RATE.val + RATE.val := by
        have h2 : blocks_nat = (blocks_nat - 1) + 1 := by omega
        conv_lhs => rw [h2]
        rw [Nat.add_mul, Nat.one_mul]
      omega
    -- Existential witness function via Classical.choice on the relevant condition.
    let s_b : Nat → Std.Array Std.U64 25#usize := fun k =>
      if hk_lo : RATE.val ≤ k then
        if hk_hi : k < blocks_nat * RATE.val then
          Classical.choose (h_loop_bytes (k - RATE.val) (h_middle_bound k hk_lo hk_hi))
        else s_spec_last
      else Foundation.lift s2
    -- The condition "iterate_keccak_f (k/RATE) (lift s2) = .ok (s_b k)" for each region.
    have h_iter_const : ∀ k : Nat, k < outlen_us.val →
        sponge.iterate_keccak_f
            ⟨BitVec.ofNat _ (k / RATE.val)⟩ (Foundation.lift s2) = .ok (s_b k) := by
      intro k hk
      rw [h_outlen_us_val] at hk
      -- k < outlen ≤ Std.Usize.max so k ≤ Std.Usize.max so k/RATE.val ≤ Std.Usize.max.
      have h_k_le : k ≤ Std.Usize.max := by omega
      have h_kRATE_le : k / RATE.val ≤ Std.Usize.max := by
        have := Nat.div_le_self k RATE.val; omega
      rw [h_iter_eq_fold _ _ h_kRATE_le]
      -- Split on which region k is in.
      by_cases hk_RATE : k < RATE.val
      · -- Region 1: k < RATE. k/RATE = 0, iterate 0 = .ok state.
        have hsb : s_b k = Foundation.lift s2 := by
          show (if hk_lo : RATE.val ≤ k then _ else Foundation.lift s2) = _
          rw [dif_neg (by omega)]
        rw [hsb]
        have h_div : k / RATE.val = 0 := Nat.div_eq_of_lt hk_RATE
        rw [h_div]
        unfold iterate_keccak_f_fold
        rw [Nat.fold_zero]
      · push Not at hk_RATE
        by_cases hk_last : k < blocks_nat * RATE.val
        · -- Region 2: RATE ≤ k < last. k/RATE ∈ [1, blocks).
          have h_mb := h_middle_bound k hk_RATE hk_last
          have hsb : s_b k = Classical.choose (h_loop_bytes (k - RATE.val) h_mb) := by
            show (if hk_lo : RATE.val ≤ k then
                    if hk_hi : k < blocks_nat * RATE.val then
                      Classical.choose (h_loop_bytes (k - RATE.val)
                        (h_middle_bound k hk_lo hk_hi))
                    else s_spec_last
                  else _) = _
            rw [dif_pos hk_RATE, dif_pos hk_last]
          rw [hsb]
          have h_choose_spec := Classical.choose_spec (h_loop_bytes (k - RATE.val) h_mb)
          have h_fold_eq := h_choose_spec.1
          have hd_ge_1 : 1 ≤ k / RATE.val :=
            (Nat.one_le_div_iff (by omega)).mpr hk_RATE
          have h_mod_lt : k % RATE.val < RATE.val := Nat.mod_lt _ (by omega)
          have h_kdivmod : k = k / RATE.val * RATE.val + k % RATE.val :=
            (Nat.div_add_mod' k RATE.val).symm
          have h_split : k / RATE.val * RATE.val
                        = (k / RATE.val - 1) * RATE.val + RATE.val := by
            conv_lhs => rw [show k / RATE.val = (k / RATE.val - 1) + 1 from by omega]
            rw [Nat.add_mul, Nat.one_mul]
          have h_eq : k - RATE.val = k % RATE.val + (k / RATE.val - 1) * RATE.val := by omega
          have h_div_eq : (k - RATE.val) / RATE.val + 1 = k / RATE.val := by
            have h_div_compute : (k - RATE.val) / RATE.val = k / RATE.val - 1 := by
              rw [h_eq]
              rw [Nat.add_mul_div_right _ _ (by omega : 0 < RATE.val)]
              rw [Nat.div_eq_of_lt h_mod_lt]
              omega
            omega
          unfold squeeze_fold at h_fold_eq
          -- h_fold_eq : Nat.fold ((k-RATE)/RATE + 1) ... = .ok (Classical.choose ...).
          -- Goal: Nat.fold (k/RATE) ... = .ok (Classical.choose ...).
          -- Use h_div_eq directly.
          have h_eq_arg : (k - RATE.val) / RATE.val + 1 = k / RATE.val := h_div_eq
          calc iterate_keccak_f_fold (Foundation.lift s2) (k / RATE.val)
              = iterate_keccak_f_fold (Foundation.lift s2) ((k - RATE.val) / RATE.val + 1) := by
                rw [h_eq_arg]
            _ = .ok (Classical.choose (h_loop_bytes (k - RATE.val) h_mb)) := h_fold_eq
        · -- Region 3: k ≥ last = blocks_nat * RATE.val. s_b k = s_spec_last.
          push Not at hk_last
          have hsb : s_b k = s_spec_last := by
            show (if hk_lo : RATE.val ≤ k then
                    if hk_hi : k < blocks_nat * RATE.val then _
                    else s_spec_last
                  else _) = _
            rw [dif_pos hk_RATE, dif_neg (by omega)]
          rw [hsb]
          have h_div : k / RATE.val = blocks_nat := by
            apply Nat.div_eq_of_lt_le hk_last
            have h_kRATE : (blocks_nat + 1) * RATE.val = blocks_nat * RATE.val + RATE.val := by
              rw [Nat.add_mul, Nat.one_mul]
            rw [h_kRATE]
            omega
          rw [h_div]
          -- Goal: iterate_keccak_f_fold (lift s2) blocks_nat = .ok s_spec_last.
          -- iterate^blocks (lift s2) = keccak_f (iterate^(blocks-1) (lift s2)) = keccak_f (lift s3) = s_spec_last.
          unfold iterate_keccak_f_fold
          have h_blocks_eq : blocks_nat = (blocks_nat - 1) + 1 := by omega
          rw [h_blocks_eq, Nat.fold_succ]
          -- Goal: (fold (blocks_nat - 1) ... ) >>= keccak_f.keccak_f = .ok s_spec_last.
          have h_inner : Nat.fold (blocks_nat - 1)
              (init := (.ok (Foundation.lift s2) : Result _))
              (fun _ _ acc => acc >>= fun st => keccak_f.keccak_f st)
              = .ok (Foundation.lift s3) := by
            have h_blocks_us_minus : blocks_us.val - 1 = blocks_nat - 1 := by
              rw [h_blocks_us_val]
            unfold squeeze_fold iterate_keccak_f_fold at h_fold_blocks
            rw [← h_blocks_us_minus]
            exact h_fold_blocks
          rw [h_inner]; simp only [bind_tc_ok]
          exact h_s5_kf
    obtain ⟨spec_out, h_spec_squeeze, h_spec_bytes⟩ :=
      sponge_squeeze_byte_eq outlen_us (Foundation.lift s2) RATE h_RATE_pos h_RATE_mod
        h_RATE_le_200 s_b h_iter_const
    -- Step 22: compose spec-side.
    have h_spec_full_eq :
        sponge.keccak outlen_us RATE DELIM data = .ok spec_out := by
      unfold sponge.keccak
      rw [h_absorb_eq]; simp only [bind_tc_ok]
      exact h_spec_squeeze
    -- Step 23: assemble post.
    apply triple_of_ok_kk (v := index_mut_back s5) h_impl_eq
    have h_final_len : (index_mut_back s5).val.length = out.val.length := by
      rw [h_s4_back s5, List.length_setSlice!, h_out2_len_out]
    refine ⟨spec_out, h_spec_full_eq, h_final_len, ?_⟩
    intro k hk
    have h_spec_byte := h_spec_bytes k (by rw [h_outlen_us_val]; exact hk)
    rw [h_spec_byte]
    -- LHS: (index_mut_back s5).val[k]! = (out2.val.setSlice! offset.val s5.val)[k]!
    rw [h_s4_back s5]
    -- Split into 3 regions for the byte equation.
    by_cases hk_RATE : k < RATE.val
    · -- Region 1: k < RATE ≤ last = offset, so squeeze_last's setSlice at offset preserves k.
      have hsb : s_b k = Foundation.lift s2 := by
        show (if hk_lo : RATE.val ≤ k then _ else Foundation.lift s2) = _
        rw [dif_neg (by omega)]
      rw [hsb]
      have h_div : k / RATE.val = 0 := Nat.div_eq_of_lt hk_RATE
      rw [List.getElem!_setSlice!_same _ _ _ _ (Or.inl (by rw [h_offset_eq_last]; omega))]
      have h_prefix := h_loop_prefix k hk_RATE
      rw [h_prefix]
      rw [h_out1_bytes k hk_RATE]
      unfold squeeze_byte_at
      rw [h_div, Nat.zero_mul, Nat.sub_zero]
    · push Not at hk_RATE
      by_cases hk_last : k < blocks_nat * RATE.val
      · -- Region 2: RATE ≤ k < last.
        rw [List.getElem!_setSlice!_same _ _ _ _ (Or.inl (by rw [h_offset_eq_last]; omega))]
        have h_j_lt := h_middle_bound k hk_RATE hk_last
        obtain ⟨s_bj_loop, h_fold_loop, h_byte_loop⟩ := h_loop_bytes (k - RATE.val) h_j_lt
        have h_RATE_plus : RATE.val + (k - RATE.val) = k := by omega
        rw [h_RATE_plus] at h_byte_loop
        rw [h_byte_loop]
        have hsb : s_b k = Classical.choose (h_loop_bytes (k - RATE.val) h_j_lt) := by
          show (if hk_lo : RATE.val ≤ k then
                  if hk_hi : k < blocks_nat * RATE.val then
                    Classical.choose (h_loop_bytes (k - RATE.val)
                      (h_middle_bound k hk_lo hk_hi))
                  else s_spec_last
                else _) = _
          rw [dif_pos hk_RATE, dif_pos hk_last]
        rw [hsb]
        have h_choose_spec := Classical.choose_spec (h_loop_bytes (k - RATE.val) h_j_lt)
        have h_s_b_eq : Classical.choose (h_loop_bytes (k - RATE.val) h_j_lt) = s_bj_loop := by
          have h1 := h_choose_spec.1
          have h2 := h_fold_loop
          -- h1 : squeeze_fold s2 ((k - RATE.val)/RATE.val + 1) = .ok (Classical.choose ...).
          -- h2 : squeeze_fold s2 ((k - RATE.val)/RATE.val + 1) = .ok s_bj_loop.
          have : (.ok (Classical.choose (h_loop_bytes (k - RATE.val) h_j_lt)) : Result _)
                  = .ok s_bj_loop := by rw [← h1, h2]
          exact (Result.ok.injEq _ _).mp this
        rw [h_s_b_eq]
        have h_div_ge_1 : 1 ≤ k / RATE.val := (Nat.one_le_div_iff (by omega)).mpr hk_RATE
        have h_kmRATE_mod : (k - RATE.val) % RATE.val = k % RATE.val := by
          have h_rewrite : k - RATE.val = k % RATE.val + (k / RATE.val - 1) * RATE.val := by
            have hd := Nat.div_add_mod' k RATE.val
            have h_split : k / RATE.val * RATE.val = (k / RATE.val - 1) * RATE.val + RATE.val := by
              conv_lhs => rw [show k / RATE.val = (k / RATE.val - 1) + 1 from by omega]
              rw [Nat.add_mul, Nat.one_mul]
            omega
          rw [h_rewrite]
          rw [Nat.add_mul_mod_self_right]
          exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))
        have h_sub_mod : k - k / RATE.val * RATE.val = k % RATE.val := by
          have hd := Nat.div_add_mod' k RATE.val; omega
        rw [h_kmRATE_mod, h_sub_mod]
      · push Not at hk_last
        -- Region 3: last ≤ k < outlen.
        have h_off_le_k : offset.val ≤ k := by rw [h_offset_eq_last]; exact hk_last
        have h_k_lt_outlen : k < out.val.length := hk
        have h_k_minus_off_lt : k - offset.val < s5.val.length := by
          rw [h_s5_len, h_s4_len', h_offset_eq_last]; omega
        rw [List.getElem!_setSlice!_middle _ _ _ _
          ⟨h_off_le_k, h_k_minus_off_lt, by rw [h_out2_len_out]; exact h_k_lt_outlen⟩]
        have h_k_minus_off_lt_out : k - offset.val < s4.val.length := by
          rw [h_s4_len', h_offset_eq_last]; omega
        have h_s5_byte := h_s5_bytes (k - offset.val) h_k_minus_off_lt_out
        rw [h_s5_byte]
        have hsb : s_b k = s_spec_last := by
          show (if hk_lo : RATE.val ≤ k then
                  if hk_hi : k < blocks_nat * RATE.val then _
                  else s_spec_last
                else _) = _
          rw [dif_pos hk_RATE, dif_neg (by omega)]
        rw [hsb]
        have h_k_div : k / RATE.val = blocks_nat := by
          apply Nat.div_eq_of_lt_le hk_last
          have h_kRATE : (blocks_nat + 1) * RATE.val = blocks_nat * RATE.val + RATE.val := by
            rw [Nat.add_mul, Nat.one_mul]
          rw [h_kRATE]; omega
        have h_k_off_eq : k - offset.val = k - k / RATE.val * RATE.val := by
          rw [h_k_div, h_offset_eq_last]
        unfold squeeze_byte_at
        rw [h_k_off_eq]
  · -- Else-branch: ¬(last < outlen) ⇒ i1 = 0, no partial trailing block.
    push Not at h_partial
    have h_last_eq_outlen : last_us.val = outlen_us.val := by
      rw [h_last_us_val, h_outlen_us_val]; omega
    have h_i1_zero : i1_nat = 0 := by
      rw [h_outlen_us_val, h_last_us_val] at h_partial
      omega
    have h_outlen_eq_last : out.val.length = blocks_nat * RATE.val := by omega
    have h_not_partial : ¬ (last_us < outlen_us) := by
      intro h; exact absurd h (by show ¬ last_us.val < outlen_us.val; omega)
    have h_impl_eq : keccak.keccak RATE DELIM data out = .ok out2 := by
      unfold keccak.keccak
      rw [h_i_us_eq]; simp only [bind_tc_ok]
      rw [h_n_us_eq]; simp only [bind_tc_ok]
      rw [h_rem_us_eq]; simp only [bind_tc_ok]
      rw [h_outlen_us_eq]; simp only [bind_tc_ok]
      rw [h_blocks_us_eq]; simp only [bind_tc_ok]
      rw [h_i1_us_eq]; simp only [bind_tc_ok]
      rw [h_last_us_eq]; simp only [bind_tc_ok]
      rw [h_s0_eq]; simp only [bind_tc_ok]
      rw [h_s1_eq]; simp only [bind_tc_ok]
      rw [h_i3_us_eq]; simp only [bind_tc_ok]
      rw [h_s2_eq]; simp only [bind_tc_ok]
      rw [if_neg h_blocks_us_nz]
      rw [h_out1_eq]; simp only [bind_tc_ok]
      rw [h_loop1_eq]; simp only [bind_tc_ok]
      change (do
              massert ((¬ (last_us < outlen_us)) || (last_us = offset))
              if last_us < outlen_us
              then do
                let (s4, index_mut_back) ←
                  CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
                    (CoreModels.core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                      Std.U8) out2 { start := offset }
                let s5 ← keccak.squeeze_last RATE s3 s4
                ok (index_mut_back s5)
              else ok out2) = .ok out2
      rw [h_massert]; simp only [bind_tc_ok]
      rw [if_neg h_not_partial]
    -- Spec-side absorb (same as partial branch).
    have h_fold_spec : absorb_fold_spec (Foundation.lift s0) data RATE n_us.val
                        = .ok (Foundation.lift s1) := by
      rw [← absorb_fold_eq_spec]; exact h_s1_fold
    have h_absorb_eq : sponge.absorb RATE DELIM data = .ok (Foundation.lift s2) := by
      unfold sponge.absorb
      show sponge.absorb_rec (Std.Array.repeat 25#usize 0#u64) RATE DELIM data
           = .ok (Foundation.lift s2)
      rw [← h_s0_lift]
      rw [sponge_absorb_rec_eq_fold (Foundation.lift s0) RATE DELIM data n_nat
        (by rw [hn_nat_def]; exact h_n_rate_le)]
      have h_fold_spec_n : absorb_fold_spec (Foundation.lift s0) data RATE n_nat
                          = .ok (Foundation.lift s1) := by
        rw [← h_n_us_val]; exact h_fold_spec
      rw [h_fold_spec_n]; simp only [bind_tc_ok]
      set tail : Slice Std.U8 :=
        ⟨data.val.drop (n_nat * RATE.val), by
          rw [List.length_drop]; have := data.property; omega⟩ with htail_def
      have h_tail_len : tail.val.length = rem_nat := by
        show (data.val.drop (n_nat * RATE.val)).length = _
        rw [List.length_drop]; omega
      have h_tail_lt_rate : tail.val.length < RATE.val := by
        rw [h_tail_len]; exact h_rem_lt_RATE
      rw [sponge_absorb_rec_unfold_short (Foundation.lift s1) RATE DELIM tail h_tail_lt_rate]
      have h_slt_eq_rem : Std.Slice.len tail = rem_us := by
        apply Std.UScalar.eq_of_val_eq
        simp [Std.Slice.len, h_tail_len, h_rem_us_val]
      rw [h_slt_eq_rem]
      rw [show sponge.absorb_final (Foundation.lift s1) tail 0#usize rem_us RATE DELIM
            = sponge.absorb_final (Foundation.lift s1) data i3_us rem_us RATE DELIM from ?_]
      · exact h_s2_spec
      · unfold sponge.absorb_final
        have h_pad_eq :
            sponge.pad_last_block tail 0#usize rem_us RATE DELIM
              = sponge.pad_last_block data i3_us rem_us RATE DELIM := by
          unfold sponge.pad_last_block
          have h_lhs_add : (0#usize : Std.Usize) + rem_us = (.ok rem_us : Result Std.Usize) := by
            have h_bnd : (0#usize : Std.Usize).val + rem_us.val ≤ Std.UScalar.max .Usize := by
              rw [Std.UScalar.max_USize_eq]; show 0 + rem_us.val ≤ Std.Usize.max
              rw [h_rem_us_val]; omega
            obtain ⟨v, h_eq_v, h_v_val_eq, _⟩ :=
              Std.WP.spec_imp_exists
                (Std.UScalar.add_bv_spec (x := (0#usize : Std.Usize)) (y := rem_us) h_bnd)
            have h_v_val : v.val = rem_us.val := by
              rw [h_v_val_eq]; show 0 + rem_us.val = rem_us.val; omega
            have h_v_eq : v = rem_us := Std.UScalar.eq_of_val_eq h_v_val
            rw [h_eq_v, h_v_eq]
          rw [h_lhs_add]; simp only [bind_tc_ok]
          have h_rhs_add : i3_us + rem_us = (.ok i_us : Result Std.Usize) := by
            have h_bnd : i3_us.val + rem_us.val ≤ Std.UScalar.max .Usize := by
              rw [Std.UScalar.max_USize_eq, h_i3_us_val, h_rem_us_val]; omega
            obtain ⟨v, h_eq_v, h_v_val_eq, _⟩ :=
              Std.WP.spec_imp_exists
                (Std.UScalar.add_bv_spec (x := i3_us) (y := rem_us) h_bnd)
            have h_v_val : v.val = i_us.val := by
              rw [h_v_val_eq, h_i3_us_val, h_rem_us_val, h_i_us_val]; omega
            have h_v_eq : v = i_us := Std.UScalar.eq_of_val_eq h_v_val
            rw [h_eq_v, h_v_eq]
          rw [h_rhs_add]; simp only [bind_tc_ok]
          have h_lhs_idx :
              CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
                (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                  Std.U8)
                tail { start := 0#usize, «end» := rem_us }
              = .ok tail := by
            unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
                   CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                   core.slice.index.Slice.index
                   core.slice.index.SliceIndexRangeUsizeSlice.index
            have h0 : (0#usize : Std.Usize) ≤ rem_us := by
              show (0 : Nat) ≤ rem_us.val; omega
            have h1' : (⟨0#usize, rem_us⟩ : core.ops.range.Range Std.Usize).end.val
                        ≤ tail.length := by
              show rem_us.val ≤ tail.val.length
              rw [h_tail_len, h_rem_us_val]
            simp [h0, h1']
            apply Subtype.ext
            show tail.val.slice ((0#usize : Std.Usize).val) rem_us.val = tail.val
            rw [show ((0#usize : Std.Usize).val : Nat) = 0 from rfl, h_rem_us_val]
            unfold List.slice
            rw [List.drop_zero]
            rw [List.take_of_length_le (by rw [h_tail_len]; omega)]
          have h_rhs_idx :
              CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
                (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                  Std.U8)
                data { start := i3_us, «end» := i_us }
              = .ok tail := by
            unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
                   CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                   core.slice.index.Slice.index
                   core.slice.index.SliceIndexRangeUsizeSlice.index
            have h0 : i3_us ≤ i_us := by
              show i3_us.val ≤ i_us.val; rw [h_i3_us_val, h_i_us_val]; omega
            have h1' : (⟨i3_us, i_us⟩ : core.ops.range.Range Std.Usize).end.val ≤ data.length := by
              show i_us.val ≤ data.length
              rw [h_i_us_val]
            simp [h0, h1']
            apply Subtype.ext
            show data.val.slice i3_us.val i_us.val = tail.val
            rw [h_i3_us_val, h_i_us_val]
            show data.val.slice (n_nat * RATE.val) data.val.length
                = data.val.drop (n_nat * RATE.val)
            unfold List.slice
            rw [List.take_of_length_le (by rw [List.length_drop])]
          rw [h_lhs_idx, h_rhs_idx]
        rw [h_pad_eq]
    -- Spec-side squeeze (no region 3; outlen = blocks * RATE).
    have h_RATE_pos : 0 < RATE.val := h_RATE_ge_1
    have h_blocks_le_max : blocks_nat ≤ Std.Usize.max := by
      have : blocks_nat ≤ out.val.length := by
        rw [hblocks_nat_def]; exact Nat.div_le_self _ _
      omega
    have h_middle_bound : ∀ k : Nat, RATE.val ≤ k → k < blocks_nat * RATE.val →
        k - RATE.val < (blocks_us.val - 1) * RATE.val := by
      intro k hk_lo hk_hi
      rw [h_blocks_us_val]
      have h_eq : blocks_nat * RATE.val = (blocks_nat - 1) * RATE.val + RATE.val := by
        have h2 : blocks_nat = (blocks_nat - 1) + 1 := by omega
        conv_lhs => rw [h2]
        rw [Nat.add_mul, Nat.one_mul]
      omega
    let s_b : Nat → Std.Array Std.U64 25#usize := fun k =>
      if hk_lo : RATE.val ≤ k then
        if hk_hi : k < blocks_nat * RATE.val then
          Classical.choose (h_loop_bytes (k - RATE.val) (h_middle_bound k hk_lo hk_hi))
        else Foundation.lift s3
      else Foundation.lift s2
    have h_iter_eq_fold : ∀ (n : Nat) (st : Std.Array Std.U64 25#usize),
        n ≤ Std.Usize.max →
        sponge.iterate_keccak_f (⟨BitVec.ofNat _ n⟩ : Std.Usize) st
          = iterate_keccak_f_fold st n := by
      intro n st h_n_le
      rw [iterate_keccak_f_eq_fold]
      have h_val : (⟨BitVec.ofNat _ n⟩ : Std.Usize).val = n := by
        show (BitVec.ofNat _ n).toNat = n
        rw [BitVec.toNat_ofNat]
        apply Nat.mod_eq_of_lt
        have h1 : Std.UScalarTy.Usize.numBits = Std.Usize.numBits := by
          rw [Std.Usize.numBits]
        rw [h1]
        have hpos : 0 < 2 ^ Std.Usize.numBits := Nat.two_pow_pos _
        have h2 : 2 ^ Std.Usize.numBits = Std.Usize.max + 1 := by
          rw [Std.Usize.max]; omega
        omega
      rw [h_val]
    have h_iter_const : ∀ k : Nat, k < outlen_us.val →
        sponge.iterate_keccak_f
            ⟨BitVec.ofNat _ (k / RATE.val)⟩ (Foundation.lift s2) = .ok (s_b k) := by
      intro k hk
      rw [h_outlen_us_val] at hk
      have h_k_le : k ≤ Std.Usize.max := by omega
      have h_kRATE_le : k / RATE.val ≤ Std.Usize.max := by
        have := Nat.div_le_self k RATE.val; omega
      rw [h_iter_eq_fold _ _ h_kRATE_le]
      by_cases hk_RATE : k < RATE.val
      · have hsb : s_b k = Foundation.lift s2 := by
          show (if hk_lo : RATE.val ≤ k then _ else Foundation.lift s2) = _
          rw [dif_neg (by omega)]
        rw [hsb]
        have h_div : k / RATE.val = 0 := Nat.div_eq_of_lt hk_RATE
        rw [h_div]; unfold iterate_keccak_f_fold; rw [Nat.fold_zero]
      · push Not at hk_RATE
        have hk_last : k < blocks_nat * RATE.val := by rw [h_outlen_eq_last] at hk; exact hk
        have h_mb := h_middle_bound k hk_RATE hk_last
        have hsb : s_b k = Classical.choose (h_loop_bytes (k - RATE.val) h_mb) := by
          show (if hk_lo : RATE.val ≤ k then
                  if hk_hi : k < blocks_nat * RATE.val then
                    Classical.choose (h_loop_bytes (k - RATE.val)
                      (h_middle_bound k hk_lo hk_hi))
                  else _
                else _) = _
          rw [dif_pos hk_RATE, dif_pos hk_last]
        rw [hsb]
        have h_choose_spec := Classical.choose_spec (h_loop_bytes (k - RATE.val) h_mb)
        have h_fold_eq := h_choose_spec.1
        have hd_ge_1 : 1 ≤ k / RATE.val := (Nat.one_le_div_iff (by omega)).mpr hk_RATE
        have h_mod_lt : k % RATE.val < RATE.val := Nat.mod_lt _ (by omega)
        have h_kdivmod : k = k / RATE.val * RATE.val + k % RATE.val :=
          (Nat.div_add_mod' k RATE.val).symm
        have h_split : k / RATE.val * RATE.val
                      = (k / RATE.val - 1) * RATE.val + RATE.val := by
          conv_lhs => rw [show k / RATE.val = (k / RATE.val - 1) + 1 from by omega]
          rw [Nat.add_mul, Nat.one_mul]
        have h_eq : k - RATE.val = k % RATE.val + (k / RATE.val - 1) * RATE.val := by omega
        have h_div_eq : (k - RATE.val) / RATE.val + 1 = k / RATE.val := by
          have h_div_compute : (k - RATE.val) / RATE.val = k / RATE.val - 1 := by
            rw [h_eq]
            rw [Nat.add_mul_div_right _ _ (by omega : 0 < RATE.val)]
            rw [Nat.div_eq_of_lt h_mod_lt]
            omega
          omega
        unfold squeeze_fold at h_fold_eq
        calc iterate_keccak_f_fold (Foundation.lift s2) (k / RATE.val)
            = iterate_keccak_f_fold (Foundation.lift s2) ((k - RATE.val) / RATE.val + 1) := by
              rw [h_div_eq]
          _ = .ok (Classical.choose (h_loop_bytes (k - RATE.val) h_mb)) := h_fold_eq
    obtain ⟨spec_out, h_spec_squeeze, h_spec_bytes⟩ :=
      sponge_squeeze_byte_eq outlen_us (Foundation.lift s2) RATE h_RATE_pos h_RATE_mod
        h_RATE_le_200 s_b h_iter_const
    have h_spec_full_eq :
        sponge.keccak outlen_us RATE DELIM data = .ok spec_out := by
      unfold sponge.keccak
      rw [h_absorb_eq]; simp only [bind_tc_ok]
      exact h_spec_squeeze
    apply triple_of_ok_kk (v := out2) h_impl_eq
    refine ⟨spec_out, h_spec_full_eq, h_out2_len_out, ?_⟩
    intro k hk
    have h_spec_byte := h_spec_bytes k (by rw [h_outlen_us_val]; exact hk)
    rw [h_spec_byte]
    by_cases hk_RATE : k < RATE.val
    · -- Region 1.
      have hsb : s_b k = Foundation.lift s2 := by
        show (if hk_lo : RATE.val ≤ k then _ else Foundation.lift s2) = _
        rw [dif_neg (by omega)]
      rw [hsb]
      have h_div : k / RATE.val = 0 := Nat.div_eq_of_lt hk_RATE
      have h_prefix := h_loop_prefix k hk_RATE
      rw [h_prefix]
      rw [h_out1_bytes k hk_RATE]
      unfold squeeze_byte_at
      rw [h_div, Nat.zero_mul, Nat.sub_zero]
    · push Not at hk_RATE
      have hk_last : k < blocks_nat * RATE.val := by rw [h_outlen_eq_last] at hk; exact hk
      have h_j_lt := h_middle_bound k hk_RATE hk_last
      obtain ⟨s_bj_loop, h_fold_loop, h_byte_loop⟩ := h_loop_bytes (k - RATE.val) h_j_lt
      have h_RATE_plus : RATE.val + (k - RATE.val) = k := by omega
      rw [h_RATE_plus] at h_byte_loop
      rw [h_byte_loop]
      have hsb : s_b k = Classical.choose (h_loop_bytes (k - RATE.val) h_j_lt) := by
        show (if hk_lo : RATE.val ≤ k then
                if hk_hi : k < blocks_nat * RATE.val then
                  Classical.choose (h_loop_bytes (k - RATE.val)
                    (h_middle_bound k hk_lo hk_hi))
                else _
              else _) = _
        rw [dif_pos hk_RATE, dif_pos hk_last]
      rw [hsb]
      have h_choose_spec := Classical.choose_spec (h_loop_bytes (k - RATE.val) h_j_lt)
      have h_s_b_eq : Classical.choose (h_loop_bytes (k - RATE.val) h_j_lt) = s_bj_loop := by
        have h1 := h_choose_spec.1
        have h2 := h_fold_loop
        have : (.ok (Classical.choose (h_loop_bytes (k - RATE.val) h_j_lt)) : Result _)
                = .ok s_bj_loop := by rw [← h1, h2]
        exact (Result.ok.injEq _ _).mp this
      rw [h_s_b_eq]
      have h_div_ge_1 : 1 ≤ k / RATE.val := (Nat.one_le_div_iff (by omega)).mpr hk_RATE
      have h_kmRATE_mod : (k - RATE.val) % RATE.val = k % RATE.val := by
        have h_rewrite : k - RATE.val = k % RATE.val + (k / RATE.val - 1) * RATE.val := by
          have hd := Nat.div_add_mod' k RATE.val
          have h_split : k / RATE.val * RATE.val = (k / RATE.val - 1) * RATE.val + RATE.val := by
            conv_lhs => rw [show k / RATE.val = (k / RATE.val - 1) + 1 from by omega]
            rw [Nat.add_mul, Nat.one_mul]
          omega
        rw [h_rewrite]
        rw [Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))
      have h_sub_mod : k - k / RATE.val * RATE.val = k % RATE.val := by
        have hd := Nat.div_add_mod' k RATE.val; omega
      rw [h_kmRATE_mod, h_sub_mod]

/-! ### Combined dispatcher: `keccak.keccak_keccak_spec`.

Case-splits on `out.val.length < RATE.val` to dispatch to either
`keccak_keccak_spec_blocks_zero` or `keccak_keccak_spec_blocks_nonzero`. -/

@[spec]
theorem keccak.keccak_keccak_spec
    (RATE : Std.Usize) (DELIM : Std.U8) (data : Slice Std.U8)
    (out : Slice Std.U8)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_ge_1 : 1 ≤ RATE.val)
    (h_RATE_le_200 : RATE.val ≤ 200) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccak RATE DELIM data out
    ⦃ ⇓ r => ⌜ ∃ spec_out : Std.Array Std.U8 (Std.Slice.len out),
                sponge.keccak (Std.Slice.len out) RATE DELIM data
                  = .ok spec_out
                ∧ r.val.length = out.val.length
                ∧ ∀ k : Nat, k < out.val.length →
                    r.val[k]! = spec_out.val[k]! ⌝ ⦄ := by
  by_cases h : out.val.length < RATE.val
  · exact keccak.keccak_keccak_spec_blocks_zero RATE DELIM data out
      h_RATE_mod h_RATE_ge_1 h_RATE_le_200 h
  · push Not at h
    exact keccak.keccak_keccak_spec_blocks_nonzero RATE DELIM data out
      h_RATE_mod h_RATE_ge_1 h_RATE_le_200 h

end libcrux_iot_sha3.Sponge
