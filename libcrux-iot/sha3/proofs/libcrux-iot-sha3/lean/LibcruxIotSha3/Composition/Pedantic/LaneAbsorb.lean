import LibcruxIotSha3.Composition.Pedantic.LaneSponge
/-!
# `hacspec_sha3`'s absorb loop is the pedantic one

`absorb_rec` peels `rate` bytes off the message at a time and pads the last,
short block; the pedantic `absorbFrom` walks the blocks of the already-padded
bit string.  This module lines the two up.
-/

open CoreModels Aeneas
open LibcruxIotSha3.LaneModel
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-! ### Reading `pad10*1` -/

theorem padBits_get (x m k : Nat) (hk : k < (padBits x m).length) :
    (padBits x m)[k]! = decide (k = 0 ∨ k = (padBits x m).length - 1) := by
  have hlen : (padBits x m).length = ((-(m : Int) - 2) % (x : Int)).toNat + 2 := by
    simp [padBits]
  set j := ((-(m : Int) - 2) % (x : Int)).toNat with hj
  rw [hlen] at hk ⊢
  simp only [padBits, ← hj]
  match k with
  | 0 => simp
  | k + 1 =>
    rw [List.getElem!_cons_succ]
    by_cases hkj : k < j
    · rw [List.getElem!_append_left _ _ _ (by simpa using hkj),
        getElem!_pos _ k (by simpa using hkj), List.getElem_replicate]
      simp
      omega
    · have hkj' : k = j := by omega
      subst hkj'
      rw [List.getElem!_append_right _ _ _ (by simp), List.length_replicate, Nat.sub_self]
      simp


/-! ### The padded bit string -/

/-- What the pedantic sponge absorbs: the message's bits, the
    domain-separation suffix, then `pad10*1`. -/
def paddedBits (M : List Std.U8) (sfx : List Bool) (r : Nat) : List Bool :=
  (h2bList M ++ sfx) ++ padBits r (8 * M.length + sfx.length)

theorem paddedBits_pre_len (M : List Std.U8) (sfx : List Bool) :
    (h2bList M ++ sfx).length = 8 * M.length + sfx.length := by
  rw [List.length_append, h2bList_len]

/-- Two multiples of `r` inside a window of `r` consecutive values coincide. -/
theorem eq_of_multiples (r a b : Nat) (_hr : 0 < r) (ha : a % r = 0) (hb : b % r = 0)
    (hab : a ≤ b) (hlt : b < a + r) : a = b := by
  have ha' : r ∣ a := Nat.dvd_of_mod_eq_zero ha
  have hb' : r ∣ b := Nat.dvd_of_mod_eq_zero hb
  have hd : r ∣ (b - a) := Nat.dvd_sub hb' ha'
  have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  omega

theorem eq_of_multiples' (r a b lo : Nat) (hr : 0 < r) (ha : a % r = 0) (hb : b % r = 0)
    (hal : lo ≤ a) (hah : a < lo + r) (hbl : lo ≤ b) (hbh : b < lo + r) : a = b := by
  rcases Nat.le_total a b with h | h
  · exact eq_of_multiples r a b hr ha hb h (by omega)
  · exact (eq_of_multiples r b a hr hb ha h (by omega)).symm

theorem paddedBits_len (M : List Std.U8) (sfx : List Bool) (rate : Nat)
    (hrate : 1 ≤ rate) (hsfx : sfx.length + 2 ≤ 8) :
    (paddedBits M sfx (8 * rate)).length = 8 * rate * (M.length / rate + 1) := by
  have hr0 : 0 < 8 * rate := by omega
  have hpl : (padBits (8 * rate) (8 * M.length + sfx.length)).length
      = ((-((8 * M.length + sfx.length : Nat) : Int) - 2)
          % ((8 * rate : Nat) : Int)).toNat + 2 := padBits_len _ _ hr0
  have hj0 : (0 : Int)
      ≤ (-((8 * M.length + sfx.length : Nat) : Int) - 2) % ((8 * rate : Nat) : Int) :=
    Int.emod_nonneg _ (by omega)
  have hjr : (-((8 * M.length + sfx.length : Nat) : Int) - 2) % ((8 * rate : Nat) : Int)
      < ((8 * rate : Nat) : Int) := Int.emod_lt_of_pos _ (by omega)
  have hjb : ((-((8 * M.length + sfx.length : Nat) : Int) - 2)
      % ((8 * rate : Nat) : Int)).toNat < 8 * rate := by omega
  have hlen : (paddedBits M sfx (8 * rate)).length
      = 8 * M.length + sfx.length
        + (padBits (8 * rate) (8 * M.length + sfx.length)).length := by
    simp only [paddedBits, List.length_append, h2bList_len]
  have hmul : (paddedBits M sfx (8 * rate)).length % (8 * rate) = 0 := by
    rw [hlen]; exact padBits_length _ _ hr0
  have hdiv : rate * (M.length / rate) + M.length % rate = M.length := Nat.div_add_mod _ _
  have hmod : M.length % rate < rate := Nat.mod_lt _ (by omega)
  have hprod : 8 * rate * (M.length / rate + 1) = 8 * (rate * (M.length / rate)) + 8 * rate := by
    ring
  have hBmul : (8 * rate * (M.length / rate + 1)) % (8 * rate) = 0 := Nat.mul_mod_right _ _
  refine eq_of_multiples' (8 * rate) _ _ (8 * M.length + sfx.length + 2) hr0 hmul hBmul
    ?_ ?_ ?_ ?_
  · rw [hlen, hpl]; omega
  · rw [hlen, hpl]; omega
  · rw [hprod]; omega
  · rw [hprod]; omega


/-! ### Reading the padded bit string -/

theorem drop_take_append_left {α : Type} (A B : List α) (k r : Nat) (h : k + r ≤ A.length) :
    ((A ++ B).drop k).take r = (A.drop k).take r := by
  rw [List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp only [List.length_drop]; omega)]

theorem drop_take_get {α : Type} [Inhabited α] (L : List α) (a b q : Nat) (hq : q < b)
    (hlt : a + q < L.length) : ((L.drop a).take b)[q]! = L[a + q]! := by
  rw [getElem!_pos _ q (by simp only [List.length_take, List.length_drop]; omega),
    List.getElem_take, List.getElem_drop, ← getElem!_pos L (a + q) hlt]

theorem h2bList_get' (M : List Std.U8) (idx : Nat) (h : idx < 8 * M.length) :
    (h2bList M)[idx]! = (M[idx / 8]!).bv.getLsbD (idx % 8) := by
  conv_lhs => rw [show idx = 8 * (idx / 8) + idx % 8 from by omega]
  exact h2bList_get M (idx / 8) (idx % 8) (by omega) (by omega)

/-- Every bit of the padded string, in closed form. -/
theorem paddedBits_get (M : List Std.U8) (sfx : List Bool) (r idx : Nat) (hr : 0 < r)
    (h : idx < (paddedBits M sfx r).length) :
    (paddedBits M sfx r)[idx]!
      = if idx < 8 * M.length then (M[idx / 8]!).bv.getLsbD (idx % 8)
        else if idx < 8 * M.length + sfx.length then sfx[idx - 8 * M.length]!
        else decide (idx = 8 * M.length + sfx.length
                     ∨ idx = (paddedBits M sfx r).length - 1) := by
  have hpre : (h2bList M ++ sfx).length = 8 * M.length + sfx.length := paddedBits_pre_len M sfx
  have hlen : (paddedBits M sfx r).length
      = 8 * M.length + sfx.length + (padBits r (8 * M.length + sfx.length)).length := by
    simp only [paddedBits, List.length_append, h2bList_len]
  by_cases h1 : idx < 8 * M.length
  · rw [if_pos h1]
    simp only [paddedBits]
    rw [List.getElem!_append_left _ _ _ (by rw [hpre]; omega),
      List.getElem!_append_left _ _ _ (by rw [h2bList_len]; omega),
      h2bList_get' M idx h1]
  · rw [if_neg h1]
    by_cases h2 : idx < 8 * M.length + sfx.length
    · rw [if_pos h2]
      simp only [paddedBits]
      rw [List.getElem!_append_left _ _ _ (by rw [hpre]; omega),
        List.getElem!_append_right _ _ _ (by rw [h2bList_len]; omega), h2bList_len]
    · rw [if_neg h2]
      simp only [paddedBits]
      rw [List.getElem!_append_right _ _ _ (by rw [hpre]; omega), hpre,
        padBits_get r (8 * M.length + sfx.length) (idx - (8 * M.length + sfx.length))
          (by rw [hlen] at h; omega)]
      have hpl2 : 2 ≤ (padBits r (8 * M.length + sfx.length)).length := by
        rw [padBits_len _ _ hr]; omega
      congr 1
      simp only [eq_iff_iff, List.length_append, h2bList_len]
      omega


/-! ### Blocks of the padded string -/

theorem paddedBits_block_full (M : List Std.U8) (sfx : List Bool) (rate i : Nat)
    (hi : (i + 1) * rate ≤ M.length) :
    ((paddedBits M sfx (8 * rate)).drop (i * (8 * rate))).take (8 * rate)
      = h2bList ((M.drop (i * rate)).take rate) := by
  have h8 : 8 * ((i + 1) * rate) ≤ 8 * M.length := Nat.mul_le_mul_left 8 hi
  have hexp : i * (8 * rate) + 8 * rate = 8 * ((i + 1) * rate) := by ring
  have hb2 : i * (8 * rate) + 8 * rate ≤ (h2bList M).length := by
    rw [h2bList_len]; omega
  have hb : i * (8 * rate) + 8 * rate ≤ (h2bList M ++ sfx).length := by
    rw [paddedBits_pre_len]; omega
  rw [paddedBits, drop_take_append_left _ _ _ _ hb, drop_take_append_left _ _ _ _ hb2,
    h2bList_take, h2bList_drop, show 8 * (i * rate) = i * (8 * rate) from by ring]

/-- The eight bits of the domain-separation byte: the suffix, the `1` that
    opens `pad10*1`, then zeros. -/
theorem delimBits_get (delim : Std.U8) (sfx : List Bool) (_hsfx : sfx.length + 2 ≤ 8)
    (hdelim : byteBits delim = sfx ++ true :: List.replicate (7 - sfx.length) false) (j : Nat) :
    (byteBits delim)[j]! = if j < sfx.length then sfx[j]! else decide (j = sfx.length) := by
  rw [hdelim]
  by_cases h1 : j < sfx.length
  · rw [List.getElem!_append_left _ _ _ h1, if_pos h1]
  · rw [List.getElem!_append_right _ _ _ (by omega), if_neg h1]
    by_cases h2 : j = sfx.length
    · rw [show j - sfx.length = 0 from by omega]
      simp [h2]
    · rw [show j - sfx.length = (j - sfx.length - 1) + 1 from by omega,
        List.getElem!_cons_succ]
      by_cases h3 : j - sfx.length - 1 < 7 - sfx.length
      · rw [getElem!_pos _ _ (by simpa using h3), List.getElem_replicate]
        simp [h2]
      · rw [List.getElem!_eq_getElem?_getD,
          List.getElem?_eq_none (by simp only [List.length_replicate]; omega)]
        simp [h2]

theorem paddedBits_last_get (M : List Std.U8) (sfx : List Bool) (rate q : Nat)
    (hrate : 1 ≤ rate) (hsfx : sfx.length + 2 ≤ 8) (hq : q < 8 * rate) :
    (((paddedBits M sfx (8 * rate)).drop (M.length / rate * (8 * rate))).take (8 * rate))[q]!
      = (if q < 8 * (M.length % rate)
         then (M[M.length / rate * rate + q / 8]!).bv.getLsbD (q % 8)
         else if q < 8 * (M.length % rate) + sfx.length
         then sfx[q - 8 * (M.length % rate)]!
         else decide (q = 8 * (M.length % rate) + sfx.length ∨ q = 8 * rate - 1)) := by
  have hplen : (paddedBits M sfx (8 * rate)).length = 8 * rate * (M.length / rate + 1) :=
    paddedBits_len M sfx rate hrate hsfx
  have hdiv : rate * (M.length / rate) + M.length % rate = M.length := Nat.div_add_mod _ _
  have hprod : 8 * rate * (M.length / rate + 1)
      = 8 * (rate * (M.length / rate)) + 8 * rate := by ring
  have hbase : M.length / rate * (8 * rate) = 8 * (rate * (M.length / rate)) := by ring
  have hlt : M.length / rate * (8 * rate) + q < (paddedBits M sfx (8 * rate)).length := by
    rw [hplen, hprod, hbase]; omega
  rw [drop_take_get _ _ _ _ hq hlt,
    paddedBits_get M sfx (8 * rate) _ (by omega) hlt]
  have hidx : M.length / rate * (8 * rate) + q = 8 * (rate * (M.length / rate)) + q := by
    rw [hbase]
  rw [hidx]
  have hm8 : 8 * M.length = 8 * (rate * (M.length / rate)) + 8 * (M.length % rate) := by omega
  by_cases h1 : q < 8 * (M.length % rate)
  · rw [if_pos (by omega), if_pos h1]
    have hA : (8 * (rate * (M.length / rate)) + q) / 8 = M.length / rate * rate + q / 8 := by
      rw [show M.length / rate * rate = rate * (M.length / rate) from by ring]
      omega
    have hB : (8 * (rate * (M.length / rate)) + q) % 8 = q % 8 := by omega
    rw [hA, hB]
  · rw [if_neg (by omega), if_neg h1]
    by_cases h2 : q < 8 * (M.length % rate) + sfx.length
    · rw [if_pos (by omega), if_pos h2]
      congr 1
      omega
    · rw [if_neg (by omega), if_neg h2]
      congr 1
      simp only [eq_iff_iff]
      omega


/-- The hacspec side's padded last block is the pedantic side's last block. -/
theorem last_block_eq (M : List Std.U8) (sfx : List Bool) (rate : Nat) (delim : Std.U8)
    (hrate : 1 ≤ rate) (hrate200 : rate ≤ 200) (hsfx : sfx.length + 2 ≤ 8)
    (hdelim : byteBits delim = sfx ++ true :: List.replicate (7 - sfx.length) false) :
    h2bList ((padBlockList M (M.length / rate * rate) (M.length % rate) rate delim).take rate)
      = ((paddedBits M sfx (8 * rate)).drop (M.length / rate * (8 * rate))).take (8 * rate) := by
  have hrem : M.length % rate < rate := Nat.mod_lt _ (by omega)
  have hdiv : rate * (M.length / rate) + M.length % rate = M.length := Nat.div_add_mod _ _
  have hcomm : M.length / rate * rate = rate * (M.length / rate) := by ring
  have hoff : M.length / rate * rate + M.length % rate ≤ M.length := by rw [hcomm]; omega
  have hplen : (paddedBits M sfx (8 * rate)).length = 8 * rate * (M.length / rate + 1) :=
    paddedBits_len M sfx rate hrate hsfx
  have hprod : 8 * rate * (M.length / rate + 1)
      = 8 * (rate * (M.length / rate)) + 8 * rate := by ring
  have hbase : M.length / rate * (8 * rate) = 8 * (rate * (M.length / rate)) := by ring
  apply list_ext_getElem!
  · rw [h2bList_len, List.length_take, padBlockList_len, List.length_take, List.length_drop,
      hplen, hprod, hbase]
    omega
  · intro q hqlt
    have hq : q < 8 * rate := by
      rw [h2bList_len, List.length_take, padBlockList_len] at hqlt
      omega
    rw [padBlockBits_get M (M.length / rate * rate) (M.length % rate) rate delim hrem hrate200
        hoff q hq,
      paddedBits_last_get M sfx rate q hrate hsfx hq]
    by_cases h1 : q < 8 * (M.length % rate)
    · rw [if_pos h1, if_pos h1,
        show decide (q = 8 * rate - 1) = false from by simp only [decide_eq_false_iff_not]; omega,
        Bool.or_false]
    · rw [if_neg h1, if_neg h1, delimBits_get delim sfx hsfx hdelim]
      by_cases h2 : q < 8 * (M.length % rate) + sfx.length
      · rw [if_pos h2, if_pos (by omega),
          show decide (q = 8 * rate - 1) = false from by
            simp only [decide_eq_false_iff_not]; omega,
          Bool.or_false]
      · rw [if_neg h2, if_neg (by omega)]
        by_cases h3 : q = 8 * (M.length % rate) + sfx.length
        · simp [h3]
        · by_cases h4 : q = 8 * rate - 1
          · simp [h4]
          · simp [h3, h4]
            omega


/-! ### `absorb_final` -/

theorem array_index_range_eq {N : Std.Usize} (a : Std.Array Std.U8 N) (b e : Std.Usize)
    (hbe : b.val ≤ e.val) (he : e.val ≤ a.val.length) :
    core.Array.Insts.CoreOpsIndexIndex.index
      (core.Slice.Insts.CoreOpsIndexIndex
        (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)) a
      { start := b, «end» := e }
    = ok ⟨a.val.slice b.val e.val, by
        have := a.val.slice_length_le b.val e.val
        have := a.property
        scalar_tac⟩ := by
  unfold core.Array.Insts.CoreOpsIndexIndex.index core.array.Array.as_slice
    rust_primitives.slice.array_as_slice
  rw [bind_tc_ok]
  exact slice_index_range_eq (Std.Array.to_slice a) b e hbe he

theorem blockMask_exact (blk : Slice Std.U8) (rate : Nat) (h8 : rate % 8 = 0)
    (hlen : blk.val.length = rate) (_hr : 8 * rate ≤ 1600) :
    blockMask blk (rate / 8) = h2bList blk.val ++ List.replicate (1600 - 8 * rate) false := by
  have h64 : 64 * (rate / 8) = 8 * rate := by omega
  have hbl : (h2bList blk.val).length = 8 * rate := by rw [h2bList_len, hlen]
  simp only [blockMask, h64]
  rw [List.take_of_length_le (by omega)]

theorem padBlockList_drop (M : List Std.U8) (a rem rate : Nat) (delim : Std.U8) :
    padBlockList (M.drop a) 0 rem rate delim = padBlockList M a rem rate delim := by
  simp only [padBlockList, padBlockPre, List.slice, Nat.sub_zero, List.drop_zero,
    Nat.add_sub_cancel_left, Nat.zero_add]

theorem absorb_final_eq (s : Lanes) (message : Slice Std.U8) (off rem rate : Std.Usize)
    (delim : Std.U8) (hrem : rem.val < rate.val) (hrate200 : rate.val ≤ 200)
    (hrate1 : 1 ≤ rate.val) (hrate8 : rate.val % 8 = 0)
    (hmsg : off.val + rem.val ≤ message.val.length) :
    ∃ s' : Lanes, hacspec_sha3.sponge.absorb_final s message off rem rate delim = ok s' ∧
      lanesToBits s' = keccakF (List.zipWith (· ^^ ·) (lanesToBits s)
        (h2bList ((padBlockList message.val off.val rem.val rate.val delim).take rate.val)
          ++ List.replicate (1600 - 8 * rate.val) false)) := by
  have hblen : (padBlockList message.val off.val rem.val rate.val delim).length = 200 :=
    padBlockList_len _ _ _ _ _
  have hslice : (padBlockList message.val off.val rem.val rate.val delim).slice 0 rate.val
      = (padBlockList message.val off.val rem.val rate.val delim).take rate.val := by
    simp only [List.slice, List.drop_zero, Nat.sub_zero]
  have hslen : ((padBlockList message.val off.val rem.val rate.val delim).slice 0 rate.val).length
      = rate.val := by rw [hslice, List.length_take, hblen]; omega
  obtain ⟨s', hs', hbits⟩ := absorb_block_eq s
    ⟨(padBlockList message.val off.val rem.val rate.val delim).slice 0 rate.val, by
      rw [hslen]; scalar_tac⟩ rate (by omega)
    (show 8 * (rate.val / 8)
        ≤ ((padBlockList message.val off.val rem.val rate.val delim).slice 0 rate.val).length from by
      rw [hslen]; omega)
  refine ⟨s', ?_, ?_⟩
  · unfold hacspec_sha3.sponge.absorb_final
    rw [pad_last_block_eq message off rem rate delim hrem hrate200 hrate1 hmsg, bind_tc_ok,
      array_index_range_eq _ 0#usize rate (by simp) (by rw [hblen]; omega), bind_tc_ok]
    exact hs'
  · rw [hbits,
      blockMask_exact _ rate.val hrate8
        (show ((padBlockList message.val off.val rem.val rate.val delim).slice 0
          rate.val).length = rate.val from hslen) (by omega)]
    rw [show ((⟨(padBlockList message.val off.val rem.val rate.val delim).slice 0 rate.val, by
        rw [hslen]; scalar_tac⟩ : Slice Std.U8)).val
      = (padBlockList message.val off.val rem.val rate.val delim).take rate.val from hslice]


/-! ### The absorb recursion -/

theorem slice_index_from_eq {α : Type} (v : Slice α) (a : Std.Usize) (ha : a.val ≤ v.val.length) :
    core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α) v
      { start := a }
    = ok ⟨v.val.drop a.val, by
        have := v.property
        have : (v.val.drop a.val).length ≤ v.val.length := by simp
        scalar_tac⟩ := by
  simp [core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_slice, rust_primitives.slice.slice_length,
    Std.Slice.subslice, Std.Slice.length, ha, List.slice]
  apply Subtype.ext
  simp only []
  rw [List.take_of_length_le (by simp)]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
theorem absorb_rec_bits (rate : Std.Usize) (delim : Std.U8) (sfx : List Bool)
    (hrate1 : 1 ≤ rate.val) (hrate200 : rate.val ≤ 200) (hrate8 : rate.val % 8 = 0)
    (hsfx : sfx.length + 2 ≤ 8)
    (hdelim : byteBits delim = sfx ++ true :: List.replicate (7 - sfx.length) false)
    (M : List Std.U8) :
    ∀ (k i : Nat) (s : Lanes) (Msuf : Slice Std.U8),
      i * rate.val ≤ M.length →
      Msuf.val = M.drop (i * rate.val) →
      Msuf.val.length / rate.val = k →
      ∃ s' : Lanes, hacspec_sha3.sponge.absorb_rec s rate delim Msuf = ok s' ∧
        lanesToBits s' = absorbFrom keccakF (8 * rate.val) (1600 - 8 * rate.val)
          (paddedBits M sfx (8 * rate.val)) (lanesToBits s) i (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro i s Msuf hile hMs hk
    have hMlen : Msuf.val.length = M.length - i * rate.val := by rw [hMs]; simp
    have hlt : Msuf.val.length < rate.val := by
      rcases Nat.lt_or_ge Msuf.val.length rate.val with h | h
      · exact h
      · exact absurd hk (by have := Nat.div_pos h (show 0 < rate.val by omega); omega)
    have hb2 : M.length < (i + 1) * rate.val := by
      have h2 : (i + 1) * rate.val = i * rate.val + rate.val := by ring
      omega
    have hMdiv : M.length / rate.val = i := Nat.div_eq_of_lt_le hile hb2
    have hMmod : M.length % rate.val = Msuf.val.length := by
      have hdm := Nat.div_add_mod M.length rate.val
      rw [hMdiv] at hdm
      have hc : i * rate.val = rate.val * i := by ring
      omega
    obtain ⟨s', hs', hbits⟩ := absorb_final_eq s Msuf 0#usize
      (Std.Usize.ofNatCore Msuf.val.length (by scalar_tac)) rate delim
      (by simpa using hlt) hrate200 hrate1 hrate8 (by simp)
    refine ⟨s', ?_, ?_⟩
    · rw [hacspec_sha3.sponge.absorb_rec, slice_len_eq, bind_tc_ok,
        if_pos (show (Std.Usize.ofNatCore Msuf.val.length (by scalar_tac) : Std.Usize) < rate from
          (Std.UScalar.lt_equiv _ _).mpr (by simpa using hlt))]
      exact hs'
    · rw [hbits]
      simp only [absorbFrom, absorbStep]
      congr 2
      rw [show (Std.Usize.ofNatCore Msuf.val.length (by scalar_tac) : Std.Usize).val
          = Msuf.val.length from by simp,
        show (0#usize : Std.Usize).val = 0 from by simp, hMs, padBlockList_drop,
        show (M.drop (i * rate.val)).length = M.length % rate.val from by rw [← hMs, hMmod],
        show i * rate.val = M.length / rate.val * rate.val from by rw [hMdiv]]
      rw [last_block_eq M sfx rate.val delim hrate1 hrate200 hsfx hdelim,
        show M.length / rate.val * (8 * rate.val) = i * (8 * rate.val) from by rw [hMdiv]]
  | succ k ih =>
    intro i s Msuf hile hMs hk
    have hMlen : Msuf.val.length = M.length - i * rate.val := by rw [hMs]; simp
    have hge : rate.val ≤ Msuf.val.length := by
      rcases Nat.lt_or_ge Msuf.val.length rate.val with h | h
      · exact absurd hk (by rw [Nat.div_eq_of_lt h]; omega)
      · exact h
    have hz : (0#usize : Std.Usize).val = 0 := by simp
    have hsl : Msuf.val.slice (0#usize : Std.Usize).val rate.val = Msuf.val.take rate.val := by
      rw [hz]; simp only [List.slice, List.drop_zero, Nat.sub_zero]
    have hsllen : (Msuf.val.slice (0#usize : Std.Usize).val rate.val).length = rate.val := by
      rw [hsl, List.length_take]; omega
    obtain ⟨s1, hs1, hb1⟩ := absorb_block_eq s
      ⟨Msuf.val.slice (0#usize : Std.Usize).val rate.val, by rw [hsllen]; scalar_tac⟩ rate
      (by omega)
      (show 8 * (rate.val / 8)
          ≤ (Msuf.val.slice (0#usize : Std.Usize).val rate.val).length from by
        rw [hsllen]; omega)
    obtain ⟨s', hs', hb'⟩ := ih (i + 1) s1
      ⟨Msuf.val.drop rate.val, by
        have := Msuf.property
        have h2 : (Msuf.val.drop rate.val).length ≤ Msuf.val.length := by simp
        scalar_tac⟩
      (by rw [Nat.add_mul, Nat.one_mul]; omega)
      (show Msuf.val.drop rate.val = M.drop ((i + 1) * rate.val) from by
        rw [hMs, List.drop_drop, Nat.add_mul, Nat.one_mul, Nat.add_comm])
      (show (Msuf.val.drop rate.val).length / rate.val = k from by
        have hmod : Msuf.val.length % rate.val < rate.val := Nat.mod_lt _ (by omega)
        have hdm := Nat.div_add_mod Msuf.val.length rate.val
        rw [hk] at hdm
        have hcm2 : rate.val * (k + 1) = k * rate.val + rate.val := by ring
        rw [List.length_drop,
          show Msuf.val.length - rate.val = Msuf.val.length % rate.val + k * rate.val from by
            omega,
          Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hmod]
        omega)
    refine ⟨s', ?_, ?_⟩
    · rw [hacspec_sha3.sponge.absorb_rec, slice_len_eq, bind_tc_ok,
        if_neg (show ¬ ((Std.Usize.ofNatCore Msuf.val.length (by scalar_tac) : Std.Usize) < rate)
          from fun hc => by
            have h := (Std.UScalar.lt_equiv _ _).mp hc
            simp at h
            omega),
        slice_index_range_eq Msuf 0#usize rate (by scalar_tac) (by scalar_tac), bind_tc_ok, hs1,
        bind_tc_ok, slice_index_from_eq Msuf rate (by omega), bind_tc_ok]
      exact hs'
    · rw [hb', hb1]
      have hfull : (i + 1) * rate.val ≤ M.length := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      have hblk : blockMask ⟨Msuf.val.slice (0#usize : Std.Usize).val rate.val, by
            rw [hsllen]; scalar_tac⟩ (rate.val / 8)
          = ((paddedBits M sfx (8 * rate.val)).drop (i * (8 * rate.val))).take (8 * rate.val)
            ++ List.replicate (1600 - 8 * rate.val) false := by
        rw [blockMask_exact _ rate.val hrate8
          (show (Msuf.val.slice (0#usize : Std.Usize).val rate.val).length = rate.val
            from hsllen) (by omega)]
        rw [paddedBits_block_full M sfx rate.val i hfull]
        congr 2
        show Msuf.val.slice (0#usize : Std.Usize).val rate.val
          = (M.drop (i * rate.val)).take rate.val
        rw [hsl, hMs]
      rw [hblk]
      simp only [absorbFrom, absorbStep]

end LibcruxIotSha3.Composition.Pedantic
