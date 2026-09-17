import LibcruxIotSha3.Composition.Pedantic.LaneAbsorb
/-!
# `hacspec_sha3`'s squeeze, and the byte/bit round trip

`squeeze` reads output bytes straight out of the lanes, permuting the state
every `rate` bytes; the pedantic `squeezeFrom` emits `r` bits at a time.  This
module relates them, and proves `b2h ∘ h2b = id`, which is what lets the two
specs' byte-level results be compared.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-! ### `b2h` inverts `h2b` -/

theorem byteOf_get (f : Nat → Bool) (k : Nat) (hk : k < 8) :
    (byteOf f).bv.getLsbD k = f k := by
  have key : ∀ (n : Nat), n ≤ 8 → ∀ k < 8,
      (((List.range n).foldl
          (fun acc j => if f j then acc ||| BitVec.twoPow 8 j else acc) 0#8)).getLsbD k
        = (decide (k < n) && f k) := by
    intro n
    induction n with
    | zero => intro _ k _; simp
    | succ n ih =>
      intro hn k hk
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hf : f n
      · rw [if_pos hf, BitVec.getLsbD_or, ih (by omega) k hk, BitVec.getLsbD_twoPow]
        by_cases hkn : k = n
        · subst hkn
          rw [show decide (k < k) = false from by simp,
            show decide (k = k) = true from by simp,
            show decide (k < 8) = true from by simp [hk],
            show decide (k < k + 1) = true from by simp, hf]
          simp
        · rw [show decide (n = k) = false from by simp; omega, Bool.and_false, Bool.or_false]
          congr 1
          simp only [decide_eq_decide]
          omega
      · have hf' : f n = false := by simpa using hf
        rw [if_neg hf, ih (by omega) k hk]
        by_cases hkn : k = n
        · subst hkn
          rw [hf']
          simp
        · congr 1
          simp only [decide_eq_decide]
          omega
  have hkey := key 8 (le_refl _) k hk
  rw [show (byteOf f).bv = (List.range 8).foldl
      (fun acc j => if f j then acc ||| BitVec.twoPow 8 j else acc) 0#8 from rfl, hkey]
  simp [hk]

theorem byteOf_bits (x : Std.U8) : byteOf (fun j => x.bv.getLsbD j) = x := by
  apply Std.U8.bv_eq_imp_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact byteOf_get _ i hi

theorem b2hList_h2bList (l : List Std.U8) : b2hList (h2bList l) = l := by
  have hlen : (h2bList l).length = 8 * l.length := h2bList_len l
  have hpad : (8 - (h2bList l).length % 8) % 8 = 0 := by rw [hlen]; omega
  have ht : h2bList l ++ List.replicate ((8 - (h2bList l).length % 8) % 8) false = h2bList l := by
    rw [hpad]; simp
  simp only [b2hList]
  rw [ht, hlen]
  rw [show 8 * l.length / 8 = l.length from by omega]
  have hb : ∀ i, i ∈ List.range l.length →
      byteOf (fun j => (h2bList l)[8 * i + j]!) = l[i]! := by
    intro i hi
    have hi' : i < l.length := by simpa using hi
    refine Std.U8.bv_eq_imp_eq _ _ ?_
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [byteOf_get _ k hk, h2bList_get l i k hi' hk]
  rw [List.map_congr_left hb, range_map_getElem' l]


/-! ### The initial state, and `absorb` -/

theorem lanesToBits_zero :
    lanesToBits (Std.Array.repeat 25#usize 0#u64) = List.replicate 1600 false := by
  have h : ∀ i, i < 25 → ((Std.Array.repeat 25#usize (0#u64)).val)[i]! = 0#u64 := by
    intro i hi
    show (List.replicate 25 (0#u64))[i]! = 0#u64
    rw [getElem!_pos _ i (by simp only [List.length_replicate]; omega), List.getElem_replicate]
  rw [show List.replicate 1600 false = (List.range 1600).map (fun _ => false) from by simp]
  simp only [lanesToBits]
  apply List.map_congr_left
  intro p hp
  have hp' : p < 1600 := by simpa using hp
  rw [laneBit, show 5 * (p / 320) + p / 64 % 5 = p / 64 from by omega, h (p / 64) (by omega)]
  simp

theorem absorb_bits (rate : Std.Usize) (delim : Std.U8) (sfx : List Bool)
    (hrate1 : 1 ≤ rate.val) (hrate200 : rate.val ≤ 200) (hrate8 : rate.val % 8 = 0)
    (hsfx : sfx.length + 2 ≤ 8)
    (hdelim : byteBits delim = sfx ++ true :: List.replicate (7 - sfx.length) false)
    (M : Slice Std.U8) :
    ∃ s' : Lanes, hacspec_sha3.sponge.absorb rate delim M = ok s' ∧
      lanesToBits s' = absorbFrom keccakF (8 * rate.val) (1600 - 8 * rate.val)
        (paddedBits M.val sfx (8 * rate.val)) (List.replicate 1600 false) 0
        (M.val.length / rate.val + 1) := by
  obtain ⟨s', hs', hb⟩ := absorb_rec_bits rate delim sfx hrate1 hrate200 hrate8 hsfx hdelim M.val
    (M.val.length / rate.val) 0 (Std.Array.repeat 25#usize 0#u64) M (by simp) (by simp) rfl
  exact ⟨s', hs', by rw [hb, lanesToBits_zero]⟩

/-! ### `iterate_keccak_f` -/

theorem iterate_keccak_f_eq (s : Lanes) : ∀ (n : Nat) (nU : Std.Usize), nU.val = n →
    ∃ s' : Lanes, hacspec_sha3.sponge.iterate_keccak_f nU s = ok s' ∧
      lanesToBits s' = keccakF^[n] (lanesToBits s) := by
  intro n
  induction n with
  | zero =>
    intro nU hn
    refine ⟨s, ?_, by simp⟩
    rw [hacspec_sha3.sponge.iterate_keccak_f,
      if_pos (show nU = 0#usize from (Std.UScalar.eq_equiv _ _).mpr (by simp [hn]))]
  | succ n ih =>
    intro nU hn
    obtain ⟨m, hm, hmv⟩ := usize_sub_eq nU 1#usize (by simp; omega)
    obtain ⟨s1, hs1, hb1⟩ := ih m (by rw [hmv]; simp; omega)
    obtain ⟨s2, hs2, hb2⟩ := keccakF_lanes_eq s1
    refine ⟨s2, ?_, ?_⟩
    · rw [hacspec_sha3.sponge.iterate_keccak_f,
        if_neg (show ¬ (nU = 0#usize) from fun hc => by
          have h0 : nU.val = (0#usize : Std.Usize).val := by rw [hc]
          simp at h0
          omega),
        hm, bind_tc_ok, hs1, bind_tc_ok]
      exact hs2
    · rw [← hb2, hb1, Function.iterate_succ_apply']


/-! ### Squeezing, bit by bit -/

theorem iterate_len (F : List Bool → List Bool)
    (hF : ∀ x : List Bool, x.length = 1600 → (F x).length = 1600) :
    ∀ (j : Nat) (s : List Bool), s.length = 1600 → (F^[j] s).length = 1600 := by
  intro j
  induction j with
  | zero => intro s hs; simpa using hs
  | succ j ih => intro s hs; rw [Function.iterate_succ_apply]; exact ih _ (hF s hs)

theorem squeezeFrom_get (F : List Bool → List Bool) (r d : Nat) (hr : 0 < r)
    (hF : ∀ x : List Bool, x.length = 1600 → (F x).length = 1600) (hrb : r ≤ 1600)
    (s0 : List Bool) (hs0 : s0.length = 1600) :
    ∀ (k j : Nat) (z : List Bool),
      z.length = j * r →
      (∀ q, q < j * r → z[q]! = (F^[q / r] s0)[q % r]!) →
      d ≤ (j + k + 1) * r →
      ∀ q, q < d → (squeezeFrom F r d k (F^[j] s0) z)[q]! = (F^[q / r] s0)[q % r]! := by
  have step : ∀ (j : Nat) (z : List Bool), z.length = j * r →
      (∀ q, q < j * r → z[q]! = (F^[q / r] s0)[q % r]!) →
      ∀ q, q < (j + 1) * r →
        (z ++ (F^[j] s0).take r)[q]! = (F^[q / r] s0)[q % r]! := by
    intro j z hzlen hz q hq
    have hFj : (F^[j] s0).length = 1600 := iterate_len F hF j s0 hs0
    have hexp : (j + 1) * r = j * r + r := by ring
    have hcm0 : r * j = j * r := by ring
    by_cases hqj : q < j * r
    · rw [List.getElem!_append_left _ _ _ (by omega), hz q hqj]
    · have hbound : j * r ≤ q := by omega
      have hqr : q / r = j := Nat.div_eq_of_lt_le hbound (by omega)
      have hdm := Nat.div_add_mod q r
      rw [hqr] at hdm
      have hcm : r * j = j * r := by ring
      have hqm : q % r = q - j * r := by omega
      rw [List.getElem!_append_right _ _ _ (by omega), hzlen, hqr, hqm,
        getElem!_pos _ _ (by rw [List.length_take]; omega), List.getElem_take,
        ← getElem!_pos (F^[j] s0) _ (by omega)]
  intro k
  induction k with
  | zero =>
    intro j z hzlen hz hfuel q hq
    have hz0 : (j + 0 + 1) * r = (j + 1) * r := by ring
    simp only [squeezeFrom]
    exact step j z hzlen hz q (by omega)
  | succ k ih =>
    intro j z hzlen hz hfuel q hq
    have hzs : (j + (k + 1) + 1) * r = (j + 1 + k + 1) * r := by ring
    have hFj : (F^[j] s0).length = 1600 := iterate_len F hF j s0 hs0
    have hz'len : (z ++ (F^[j] s0).take r).length = (j + 1) * r := by
      rw [List.length_append, hzlen, List.length_take, hFj]
      have : min r 1600 = r := by omega
      rw [this]; ring
    simp only [squeezeFrom]
    by_cases hstop : d ≤ (z ++ (F^[j] s0).take r).length
    · rw [if_pos hstop]
      exact step j z hzlen hz q (by omega)
    · rw [if_neg hstop, ← Function.iterate_succ_apply' F j s0]
      exact ih (j + 1) (z ++ (F^[j] s0).take r) hz'len
        (fun q hq => step j z hzlen hz q (by omega)) (by omega) q hq

theorem squeezeAll_get (F : List Bool → List Bool) (r d : Nat) (hr : 0 < r)
    (hF : ∀ x : List Bool, x.length = 1600 → (F x).length = 1600) (hrb : r ≤ 1600)
    (s0 : List Bool) (hs0 : s0.length = 1600) :
    ∀ q, q < d → (squeezeAll F r d s0)[q]! = (F^[q / r] s0)[q % r]! := by
  intro q hq
  have hfuel : d ≤ (0 + d / r + 1) * r := by
    have h1 := Nat.div_add_mod d r
    have h2 := Nat.mod_lt d hr
    have h3 : (0 + d / r + 1) * r = r * (d / r) + r := by ring
    omega
  have hthis := squeezeFrom_get F r d hr hF hrb s0 hs0 (d / r) 0 [] (by simp)
    (by intro q hq; simp at hq) hfuel q hq
  rw [Function.iterate_zero_apply] at hthis
  rw [squeezeAll]
  exact hthis

end LibcruxIotSha3.Composition.Pedantic
