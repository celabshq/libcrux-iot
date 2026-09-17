import LibcruxIotSha3.Composition.Pedantic.LaneSponge
/-!
# `hacspec_sha3`'s absorb loop is the pedantic one

`absorb_rec` peels `rate` bytes off the message at a time and pads the last,
short block; the pedantic `absorbFrom` walks the blocks of the already-padded
bit string.  This module lines the two up.
-/

open CoreModels Aeneas
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

end LibcruxIotSha3.Composition.Pedantic
