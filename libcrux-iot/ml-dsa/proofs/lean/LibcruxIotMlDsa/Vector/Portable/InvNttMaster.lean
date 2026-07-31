/-
  # `Vector/Portable/InvNttMaster.lean` — inverse NTT master (ML-DSA)

  Composes the 8 proven inverse layer-driver FCs (`invert_ntt_at_layer_0 …
  invert_ntt_at_layer_7`, all in `InvNttDriver`) and the finalize `×41978`
  Montgomery scale into the straight-line `simd.portable.invntt.invert_ntt_montgomery`
  body, giving the full inverse NTT impl↔spec equivalence on the lifted flat
  256-array:

    `lift_units r = (Pure.intt (lift_units re)).map (· * (R : Zq))`.

  The driver bound is threaded with CONCRETE numerals (each driver maps an input
  bound `K` to `≤ max (2*K) 12578816`, precond `2*K ≤ 2^31-1`); after layer 0 the
  running bound is a flat numeral, dodging the symbolic-nested-`max` kernel blowup.

  The finalize loop (`invert_ntt_montgomery_loop`) runs one
  `montgomery_multiply_by_constant(·, 41978)` per unit (32 units), each lifting to
  `(re8[u][l] : Zq) · (41978 : Zq) · R⁻¹` and staying `≤ 2^24`. The
  R-reconciliation `liftZ 41978 = (R : Zq) · inv256` turns this into the spec's
  `reduce_polynomial` scale times an extra `R` (mont-domain output convention).
-/
import LibcruxIotMlDsa.Vector.Portable.InvNttDriver

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_dsa.Vector.Portable.InvNttDriver
open CoreModels Aeneas Aeneas.Std Std.Do Result
open libcrux_iot_ml_dsa.Spec
open libcrux_iot_ml_dsa.Spec.Lift libcrux_iot_ml_dsa.Spec.Montgomery
  libcrux_iot_ml_dsa.Spec.Parameters
open libcrux_iot_ml_dsa.Util.LoopHelper
open libcrux_iot_ml_dsa.Util.LoopSpecs

/-- `classify` on an `i32` is the identity (file-scoped copy). -/
private theorem classify_ok (z : Std.I32) :
    libcrux_secrets.traits.Classify.Blanket.classify z = .ok z := rfl

/-- Reflect a `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` Triple into an `.ok` witness plus the post
    (file-scoped copy of the §13.5 helper). -/
private theorem triple_exists_ok
    {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl,
      (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

/-- `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` closer for `x = .ok v` (file-scoped §13.5 copy). -/
private theorem triple_of_ok
    {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

/-! ## R-reconciliation helper.

`liftZ 41978 = (R : Zq) · inv256`. Numerically `41978 = R²·256⁻¹ (mod q)`
(`Montgomery.lean:44 #guard`), so `(41978:Zq)·RINV = (R)²·INV256·RINV
= (R)·(R·RINV)·INV256 = R·INV256 = R·inv256`. The whole `ZMod Q` equation
closes by kernel `decide`. -/
theorem liftZ_INTT_FINAL :
    liftZ ((41978 : Int)) = ((Montgomery.R : Nat) : Zq) * Pure.inv256 := by
  unfold liftZ Pure.inv256
  decide

/-- `Array.map` of a `Pure.build` is the `Pure.build` of the composed index fn. -/
private theorem map_build (φ : Zq → Zq) (h : Nat → Zq) :
    Array.map φ (Pure.build h) = Pure.build (fun i => φ (h i)) := by
  unfold Pure.build
  rw [List.map_toArray, List.map_map]
  rfl

/-! ## Finalize loop infrastructure.

The finalize `invert_ntt_montgomery_loop {start:=0,end:=32} re8` applies
`montgomery_multiply_by_constant(·, classify 41978)` to each unit `[0, 32)`. The
accumulator is the full 32-unit array; the loop invariant says swept units carry
the `×41978` mont image (lift + bound), unswept units are still `re8`. -/

/-- The finalize accumulator: the whole 32-unit array. -/
abbrev FinAcc := Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize

/-- Finalize loop invariant. Units `[0, k)` carry the `×41978` lift + `≤2^24`
    bound; units `[k, 32)` are unchanged (`= re8`). -/
def finInv (re8 : FinAcc) : Std.Usize → FinAcc → Result Prop :=
  fun k acc => pure (
    (∀ u : Nat, u < k.val →
        ∀ l : Nat, l < 8 →
          liftZ_std (acc.val[u]!).values.val[l]!.val
            = ((re8.val[u]!).values.val[l]!.val : Zq) * ((41978 : Int) : Zq) * (RINV : Zq)
          ∧ (acc.val[u]!).values.val[l]!.val.natAbs ≤ 2 ^ 24)
    ∧ (∀ u : Nat, k.val ≤ u → acc.val[u]! = re8.val[u]!))

/-- Finalize step-post for `loop_range_spec_usize`. -/
def finStepPost (re8 : FinAcc) (e : Std.Usize) (k : Std.Usize)
    (r : ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) × FinAcc) FinAcc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < e.val ∧ iter'.«end» = e ∧ iter'.start.val = k.val + 1
        ∧ (finInv re8 iter'.start acc').holds
  | .done y => (finInv re8 e y).holds

set_option maxHeartbeats 16000000 in
/-- Per-iteration finalize step lemma. At cursor `k < 32` applies
    `montgomery_multiply_by_constant(·, 41978)` to unit `k`, extends the swept
    range, and keeps the unswept window unchanged. -/
theorem finalize_step_lemma
    (re8 : FinAcc) (e : Std.Usize) (he : e.val = 32)
    (acc : FinAcc) (k : Std.Usize)
    (h_ge : (0 : Nat) ≤ k.val) (h_le : k.val ≤ e.val)
    (h_inv : (finInv re8 k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_montgomery_loop.body
      { start := k, «end» := e } acc
    ⦃ ⇓ r => ⌜ finStepPost re8 e k r ⌝ ⦄ := by
  have h_acc_len : acc.length = 32 := Std.Array.length_eq _
  obtain ⟨h_swept, h_unswept⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_montgomery_loop.body
  by_cases h_lt : k.val < e.val
  · -- `Some k` branch.
    have hk_lt_32 : k.val < 32 := by omega
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k e h_lt
    -- acc[k] = re8[k] (unswept).
    have h_acc_k : acc.val[k.val]! = re8.val[k.val]! := h_unswept k.val (Nat.le_refl _)
    set ak : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients := acc.val[k.val]! with hak_def
    -- (1) (c, mb) = index_mut_usize acc k; c = acc[k] = ak.
    have h_idx_k : Aeneas.Std.Array.index_usize acc k = .ok ak :=
      array_index_usize_ok_eq acc k (by rw [h_acc_len]; exact hk_lt_32)
    have h_imt_k :
        Aeneas.Std.Array.index_mut_usize acc k = .ok (ak, acc.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_k]; rfl
    -- (2) i1 = classify 41978.
    -- (3) c1 = montgomery_multiply_by_constant ak (41978).
    have hc41978 : ((41978#i32 : Std.I32).val).natAbs ≤ 8380416 := by decide
    obtain ⟨c1, h_c1_eq, h_c1_P⟩ :=
      triple_exists_ok
        (libcrux_iot_ml_dsa.Vector.Portable.Element.montgomery_multiply_by_constant_spec
          ak (41978#i32) hc41978)
    -- a = mb c1 = acc.set k c1.
    set a : FinAcc := acc.set k c1 with ha_def
    have ha_len : a.length = 32 := by rw [ha_def, Std.Array.set_length]; exact h_acc_len
    -- Compose the body to .ok (cont ((s,e), a)).
    have h_body :
        libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_montgomery_loop.body
          { start := k, «end» := e } acc
        = .ok (ControlFlow.cont (({ start := s, «end» := e }
                  : CoreModels.core.ops.range.Range Std.Usize), a)) := by
      unfold libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_montgomery_loop.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := e } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := e }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp [Aeneas.Std.bind_tc_ok, h_imt_k, classify_ok, h_c1_eq]
      exact ha_def.symm
    apply triple_of_ok h_body
    -- step_post: cont branch.
    show finStepPost re8 e k
      (.cont (({ start := s, «end» := e } : CoreModels.core.ops.range.Range Std.Usize), a))
    unfold finStepPost
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (finInv re8 s a).holds
    -- a[k] = c1, a[u≠k] = acc[u].
    have ha_k : a.val[k.val]! = c1 := by
      rw [ha_def]
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq acc k k.val c1
          ⟨rfl, by rw [h_acc_len]; exact hk_lt_32⟩
    have h_inv_pure :
        (∀ u : Nat, u < s.val →
            ∀ l : Nat, l < 8 →
              liftZ_std (a.val[u]!).values.val[l]!.val
                = ((re8.val[u]!).values.val[l]!.val : Zq) * ((41978 : Int) : Zq) * (RINV : Zq)
              ∧ (a.val[u]!).values.val[l]!.val.natAbs ≤ 2 ^ 24)
        ∧ (∀ u : Nat, s.val ≤ u → a.val[u]! = re8.val[u]!) := by
      refine ⟨?_, ?_⟩
      · -- Swept range [0, s) = [0, k+1).
        intro u hu_lt l hl
        rw [hs_val] at hu_lt
        by_cases h_u_k : u = k.val
        · subst h_u_k
          rw [ha_k]
          have hP := h_c1_P l hl
          refine ⟨?_, hP.2⟩
          -- hP.1 : liftZ_std c1[l] = ak[l] · 41978 · RINV; ak = acc[k] = re8[k].
          rw [hP.1]
          have hak2 : acc.val[k.val]! = re8.val[k.val]! := h_unswept k.val (Nat.le_refl _)
          rw [show ak = acc.val[k.val]! from hak_def, hak2]
          norm_cast
        · -- u < k, untouched by the set at k.
          have h_u_lt_k : u < k.val := by omega
          have h_a_u : a.val[u]! = acc.val[u]! := by
            rw [ha_def]
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc k u c1 (Ne.symm h_u_k)
          rw [h_a_u]
          exact h_swept u h_u_lt_k l hl
      · -- Unswept range [s, 32) = [k+1, 32).
        intro u hu_ge
        rw [hs_val] at hu_ge
        have h_u_ne_k : u ≠ k.val := by omega
        have h_a_u : a.val[u]! = acc.val[u]! := by
          rw [ha_def]
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne acc k u c1 (Ne.symm h_u_ne_k)
        rw [h_a_u]
        exact h_unswept u (by omega)
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ e, done.
    have hk_ge : k.val ≥ e.val := Nat.not_lt.mp h_lt
    have h_iter_none := iter_next_none_eq k e hk_ge
    have h_body :
        libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_montgomery_loop.body
          { start := k, «end» := e } acc
        = .ok (ControlFlow.done acc) := by
      unfold libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_montgomery_loop.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := e } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := e }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    apply triple_of_ok h_body
    show finStepPost re8 e k (.done acc)
    unfold finStepPost
    have hk_eq : k.val = e.val := by omega
    show (finInv re8 e acc).holds
    have h_inv_pure :
        (∀ u : Nat, u < e.val →
            ∀ l : Nat, l < 8 →
              liftZ_std (acc.val[u]!).values.val[l]!.val
                = ((re8.val[u]!).values.val[l]!.val : Zq) * ((41978 : Int) : Zq) * (RINV : Zq)
              ∧ (acc.val[u]!).values.val[l]!.val.natAbs ≤ 2 ^ 24)
        ∧ (∀ u : Nat, e.val ≤ u → acc.val[u]! = re8.val[u]!) := by
      refine ⟨?_, ?_⟩
      · intro u hu l hl; rw [← hk_eq] at hu; exact h_swept u hu l hl
      · intro u hu; rw [← hk_eq] at hu; exact h_unswept u hu
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

/-- `Slice.len (Array.to_slice re8) = 32#usize` for the finalize length plumbing. -/
private theorem fin_slice_len_eq (re8 : FinAcc) :
    Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice re8) = (32#usize : Std.Usize) := by
  apply Std.UScalar.eq_of_val_eq
  rw [Aeneas.Std.Slice.len_val]
  show (Aeneas.Std.Array.to_slice re8).length = (32#usize : Std.Usize).val
  rw [Aeneas.Std.Array.length_to_slice re8]

/-- The finalize loop spec: `invert_ntt_montgomery_loop {0, 32} re8` yields an array
    `r` whose every unit is the `×41978` Montgomery image of `re8` (lift + `≤2^24`). -/
theorem finalize_loop_fc (re8 : FinAcc) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_montgomery_loop
      { start := 0#usize, «end» := 32#usize } re8
    ⦃ ⇓ r => ⌜ ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                liftZ_std (r.val[u]!).values.val[l]!.val
                  = ((re8.val[u]!).values.val[l]!.val : Zq) * ((41978 : Int) : Zq) * (RINV : Zq)
                ∧ (r.val[u]!).values.val[l]!.val.natAbs ≤ 2 ^ 24 ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_montgomery_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_montgomery_loop.body iter1 acc1)
      (β := FinAcc)
      re8
      (0#usize) (32#usize)
      (finInv re8)
      (by decide)
      (by
        -- h_init at k = 0: swept range empty, unswept trivial.
        show (pure _ : Result Prop).holds
        have h_init_pure :
            (∀ u : Nat, u < (0#usize : Std.Usize).val →
                ∀ l : Nat, l < 8 →
                  liftZ_std (re8.val[u]!).values.val[l]!.val
                    = ((re8.val[u]!).values.val[l]!.val : Zq) * ((41978 : Int) : Zq) * (RINV : Zq)
                  ∧ (re8.val[u]!).values.val[l]!.val.natAbs ≤ 2 ^ 24)
            ∧ (∀ u : Nat, (0#usize : Std.Usize).val ≤ u → re8.val[u]! = re8.val[u]!) := by
          refine ⟨?_, ?_⟩
          · intro u hu
            have : (0#usize : Std.Usize).val = 0 := by decide
            rw [this] at hu; exact absurd hu (Nat.not_lt_zero u)
          · intro u _; rfl
        simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_init_pure)
      ?_)
  · -- Post-entailment: inv at k = 32 yields the per-unit post.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (finInv re8 (32#usize) r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    obtain ⟨h_swept, _h_unswept⟩ := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_holds
    intro u hu l hl
    exact h_swept u (by simpa using hu) l hl
  · -- Step lemma dispatch.
    intro acc k h_ge_k h_le_k hinv
    have h_step :=
      finalize_step_lemma re8 (32#usize) (by decide) acc k (Nat.zero_le _) h_le_k hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : finStepPost re8 (32#usize) k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [finStepPost] using hP
    · have hP : finStepPost re8 (32#usize) k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [finStepPost] using hP

/-! ## Inverse NTT master `invert_ntt_inner_fc`.

`simd.portable.invntt.invert_ntt_montgomery` is the straight-line
`do let re1 ← invert_ntt_at_layer_0 re; …; re8 ← invert_ntt_at_layer_7 re7;
   finalize ×41978 over [0,32)`. Composing the 8 proven inverse layer drivers
gives `lift_units re8 = foldl intt_layer (lift_units re) [0..7]`; the finalize
`×41978` then equals the spec `reduce_polynomial` scale (`·inv256`) times an
extra `R` (mont-domain output), so
`lift_units r = (Pure.intt (lift_units re)).map (· * R)`. -/

set_option maxHeartbeats 16000000 in
@[spec]
theorem invert_ntt_inner_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hB : (B : Int) ≤ 2 ^ 23 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_montgomery re
    ⦃ ⇓ r => ⌜ Lift.lift_units r
                 = (Pure.intt (Lift.lift_units re)).map (· * ((Montgomery.R : Nat) : Zq))
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.val[u]!).values.val[l]!.val.natAbs ≤ 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.invntt.invert_ntt_montgomery
  -- Layer 0 (input bound B): precond 2*B ≤ 2^31-1.
  have hB0 : (2 : Int) * B ≤ 2 ^ 31 - 1 := by omega
  obtain ⟨r1, hr1_eq, hr1_lift, hr1_bd⟩ := triple_exists_ok (invert_ntt_at_layer_0_fc re B hB0 hin)
  -- Weaken r1 bound: max (2*B) 12578816 ≤ 16777214.
  have hbd1 : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
      (r1.val[u]!).values.val[l]!.val.natAbs ≤ 16777214 := by
    intro u hu l hl; have := hr1_bd u hu l hl; omega
  -- Layer 1 (input bound 16777214).
  have hB1 : (2 : Int) * (16777214 : Nat) ≤ 2 ^ 31 - 1 := by decide
  obtain ⟨r2, hr2_eq, hr2_lift, hr2_bd⟩ :=
    triple_exists_ok (invert_ntt_at_layer_1_fc r1 16777214 hB1 hbd1)
  have hbd2 : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
      (r2.val[u]!).values.val[l]!.val.natAbs ≤ 33554428 := by
    intro u hu l hl; have := hr2_bd u hu l hl; omega
  -- Layer 2 (input bound 33554428).
  have hB2 : (2 : Int) * (33554428 : Nat) ≤ 2 ^ 31 - 1 := by decide
  obtain ⟨r3, hr3_eq, hr3_lift, hr3_bd⟩ :=
    triple_exists_ok (invert_ntt_at_layer_2_fc r2 33554428 hB2 hbd2)
  have hbd3 : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
      (r3.val[u]!).values.val[l]!.val.natAbs ≤ 67108856 := by
    intro u hu l hl; have := hr3_bd u hu l hl; omega
  -- Layer 3 (input bound 67108856).
  have hB3 : (2 : Int) * (67108856 : Nat) ≤ 2 ^ 31 - 1 := by decide
  obtain ⟨r4, hr4_eq, hr4_lift, hr4_bd⟩ :=
    triple_exists_ok (invert_ntt_at_layer_3_fc r3 67108856 hB3 hbd3)
  have hbd4 : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
      (r4.val[u]!).values.val[l]!.val.natAbs ≤ 134217712 := by
    intro u hu l hl; have := hr4_bd u hu l hl; omega
  -- Layer 4 (input bound 134217712).
  have hB4 : (2 : Int) * (134217712 : Nat) ≤ 2 ^ 31 - 1 := by decide
  obtain ⟨r5, hr5_eq, hr5_lift, hr5_bd⟩ :=
    triple_exists_ok (invert_ntt_at_layer_4_fc r4 134217712 hB4 hbd4)
  have hbd5 : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
      (r5.val[u]!).values.val[l]!.val.natAbs ≤ 268435424 := by
    intro u hu l hl; have := hr5_bd u hu l hl; omega
  -- Layer 5 (input bound 268435424).
  have hB5 : (2 : Int) * (268435424 : Nat) ≤ 2 ^ 31 - 1 := by decide
  obtain ⟨r6, hr6_eq, hr6_lift, hr6_bd⟩ :=
    triple_exists_ok (invert_ntt_at_layer_5_fc r5 268435424 hB5 hbd5)
  have hbd6 : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
      (r6.val[u]!).values.val[l]!.val.natAbs ≤ 536870848 := by
    intro u hu l hl; have := hr6_bd u hu l hl; omega
  -- Layer 6 (input bound 536870848).
  have hB6 : (2 : Int) * (536870848 : Nat) ≤ 2 ^ 31 - 1 := by decide
  obtain ⟨r7, hr7_eq, hr7_lift, hr7_bd⟩ :=
    triple_exists_ok (invert_ntt_at_layer_6_fc r6 536870848 hB6 hbd6)
  have hbd7 : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
      (r7.val[u]!).values.val[l]!.val.natAbs ≤ 1073741696 := by
    intro u hu l hl; have := hr7_bd u hu l hl; omega
  -- Layer 7 (input bound 1073741696).
  have hB7 : (2 : Int) * (1073741696 : Nat) ≤ 2 ^ 31 - 1 := by decide
  obtain ⟨r8, hr8_eq, hr8_lift, hr8_bd⟩ :=
    triple_exists_ok (invert_ntt_at_layer_7_fc r7 1073741696 hB7 hbd7)
  -- Collapse the 8 `.ok` binds.
  rw [hr1_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr2_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr3_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr4_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr5_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr6_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr7_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  -- `lift (Array.to_slice r8) = .ok (Array.to_slice r8)`; `Slice.len … = 32#usize`.
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice r8)
        = .ok (Aeneas.Std.Array.to_slice r8) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show CoreModels.core.slice.Slice.len (Aeneas.Std.Array.to_slice r8)
        = .ok (Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice r8)) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [fin_slice_len_eq r8]
  -- Dispatch the finalize loop spec.
  obtain ⟨rf, hrf_eq, hrf_P⟩ := triple_exists_ok (finalize_loop_fc r8)
  apply triple_of_ok hrf_eq
  refine ⟨?_, ?_⟩
  · -- Equality conjunct.
    -- Per-flat-index: lift_units rf [i] = lift_units r8 [i] · R · inv256.
    -- Both sides reduce to (lift_units r8).map (· * (R · inv256)).
    show Lift.lift_units rf
      = (Pure.intt (Lift.lift_units re)).map (· * ((Montgomery.R : Nat) : Zq))
    -- Drive both sides to a per-index `build_congr` form.
    have h_re8_chain : Lift.lift_units r8
        = ([0, 1, 2, 3, 4, 5, 6, 7].foldl
            (fun acc layer => Pure.intt_layer acc layer) (Lift.lift_units re)) := by
      simp only [List.foldl]
      rw [hr8_lift, hr7_lift, hr6_lift, hr5_lift, hr4_lift, hr3_lift, hr2_lift, hr1_lift]
    -- RHS = (lift_units r8).map (· * inv256) .map (· * R).
    rw [Pure.intt, Pure.reduce_polynomial, ← h_re8_chain]
    -- Now goal: lift_units rf = ((lift_units r8).map (·*inv256)).map (·*R).
    unfold Lift.lift_units
    -- Collapse both `map`s on the RHS `build` into a single `build`.
    rw [map_build (· * Pure.inv256), map_build (· * ((Montgomery.R : Nat) : Zq))]
    apply Pure.build_congr
    intro i hi
    have huu : i / 8 < 32 := by omega
    have hll : i % 8 < 8 := by omega
    have hP := hrf_P (i / 8) huu (i % 8) hll
    -- LHS: liftZ (rf[i/8][i%8]) ; from hP.1 (liftZ_std form) + liftZ_INTT_FINAL.
    -- liftZ rf[..] = liftZ r8[..] · liftZ 41978 = (r8[..]:Zq)·RINV · (R·inv256).
    have h_lift_rf : liftZ (rf.val[i / 8]!).values.val[i % 8]!.val
        = liftZ (r8.val[i / 8]!).values.val[i % 8]!.val * (((Montgomery.R : Nat) : Zq) * Pure.inv256) := by
      have hseam := liftZ_of_mont (rf.val[i / 8]!).values.val[i % 8]!.val
        (r8.val[i / 8]!).values.val[i % 8]!.val (41978 : Int) (by
          have h1 := hP.1
          unfold liftZ_std at h1
          rw [h1])
      rw [hseam, liftZ_INTT_FINAL]
    -- Goal: liftZ rf[..] = (liftZ r8[..] * inv256) * R ; via h_lift_rf + ring.
    rw [h_lift_rf]
    ring
  · -- Bound conjunct: every unit ≤ 2^24 (from finalize post).
    intro u hu l hl
    exact (hrf_P u hu l hl).2

end libcrux_iot_ml_dsa.Vector.Portable.InvNttDriver
