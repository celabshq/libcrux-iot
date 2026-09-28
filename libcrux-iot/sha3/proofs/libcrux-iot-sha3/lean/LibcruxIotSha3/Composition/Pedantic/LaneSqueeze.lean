import LibcruxIotSha3.Composition.Pedantic.LaneAbsorb
/-!
# `hacspec_sha3`'s squeeze, and the byte/bit round trip

`squeeze` reads output bytes straight out of the lanes, permuting the state
every `rate` bytes; the pedantic `squeezeFrom` emits `r` bits at a time.  This
module relates them, and proves `b2h ∘ h2b = id`, which is what lets the two
specs' byte-level results be compared.
-/

open CoreModels Aeneas
open LibcruxIotSha3.LaneModel
open LibcruxIotSha3.SpongeModel
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

theorem byteOf_congr {f g : Nat → Bool} (h : ∀ t, t < 8 → f t = g t) : byteOf f = byteOf g := by
  apply Std.U8.bv_eq_imp_eq
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [byteOf_get f k hk, byteOf_get g k hk, h k hk]

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
  rw [laneBitAt, laneBit, show 5 * (p / 320) + p / 64 % 5 = p / 64 from by omega, h (p / 64) (by omega)]
  simp

theorem lanesToBits_absorbLanes (rate : Std.Usize) (delim : Std.U8) (sfx : List Bool)
    (hrate1 : 1 ≤ rate.val) (hrate200 : rate.val ≤ 200) (hrate8 : rate.val % 8 = 0)
    (hsfx : sfx.length + 2 ≤ 8)
    (hdelim : byteBits delim = sfx ++ true :: List.replicate (7 - sfx.length) false)
    (M : Slice Std.U8) :
    lanesToBits (absorbLanes rate.val delim M.val)
      = absorbFrom keccakF (8 * rate.val) (1600 - 8 * rate.val)
        (paddedBits M.val sfx (8 * rate.val)) (List.replicate 1600 false) 0
        (M.val.length / rate.val + 1) := by
  have hb := lanesToBits_absorbRecLanes rate delim sfx hrate1 hrate200 hrate8 hsfx hdelim M.val
    (M.val.length / rate.val) 0 (Std.Array.repeat 25#usize 0#u64) M (by simp) (by simp) rfl
  rw [absorbLanes, hb, lanesToBits_zero]

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


/-! ### `squeeze` -/

theorem to_le_bytes_bit (x : Std.U64) (j t : Nat) (ht : t < 8) :
    ((Std.core.num.U64.to_le_bytes x).val[j]!).bv.getLsbD t = x.bv.getLsbD (8 * j + t) := by
  have hv : (Std.core.num.U64.to_le_bytes x).val
      = x.bv.toLEBytes.map (@Std.UScalar.mk Std.UScalarTy.U8) := rfl
  rw [hv]
  by_cases hj : j < x.bv.toLEBytes.length
  · rw [getElem!_pos _ j (by simpa using hj), List.getElem_map,
      ← getElem!_pos x.bv.toLEBytes j hj]
    show (x.bv.toLEBytes[j]!).getLsbD t = _
    rw [← bv_getElem!_eq_getLsbD, ← bv_getElem!_eq_getLsbD]
    exact BitVec.getElem!_toLEBytes _ j t ht
  · rw [List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_none (by simp only [List.length_map]; omega)]
    have hlen : x.bv.toLEBytes.length = 8 := by
      rw [BitVec.toLEBytes_length]
    show (0#u8 : Std.U8).bv.getLsbD t = _
    rw [show x.bv.getLsbD (8 * j + t) = false from by
      apply BitVec.getLsbD_of_ge
      omega]
    simp

/-! ### The whole byte-rate sponge -/

/-! ### (b) The sponge's squeeze phase, and `KECCAK[c]`, on the lane model -/

/-- Permuting `n` times commutes with reading the state as bits. -/
theorem keccakF_iterate_lanesToBits (s : Lanes) (n : Nat) :
    keccakF^[n] (lanesToBits s) = lanesToBits (keccakFLanes^[n] s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih, keccakF_lanesToBits]

theorem lanesToBits_getElem (s : Lanes) (p : Nat) (hp : p < 1600) :
    (lanesToBits s)[p]! = laneBitAt s p := by
  simp only [lanesToBits]
  rw [getElem!_pos _ _ (by simp only [List.length_map, List.length_range]; exact hp)]
  simp

/-- (c) Squeezing on the model, read as bits. -/
theorem squeezeLanes_bits (OUTPUT_LEN : Std.Usize) (state : Lanes) (rate : Std.Usize)
    (hrate1 : 1 ≤ rate.val) (hrate200 : rate.val ≤ 200) :
    squeezeLanes OUTPUT_LEN state rate.val
      = mkArr OUTPUT_LEN (fun i => byteOf (fun t =>
          (keccakF^[i / rate.val] (lanesToBits state))[8 * (i % rate.val) + t]!)) := by
  refine mkArr_congr OUTPUT_LEN ?_
  intro i _
  refine byteOf_congr ?_
  intro t ht
  have hmod : i % rate.val < rate.val := Nat.mod_lt _ (by omega)
  rw [keccakF_iterate_lanesToBits, lanesToBits_getElem _ _ (by omega)]

theorem b2hList_of_len (bits : List Bool) (n : Nat) (h : bits.length = 8 * n) :
    b2hList bits = (List.range n).map (fun i => byteOf (fun j => bits[8 * i + j]!)) := by
  simp only [b2hList]
  rw [show (8 - bits.length % 8) % 8 = 0 from by rw [h]; omega]
  simp only [List.replicate_zero, List.append_nil, h]
  rw [show 8 * n / 8 = n from by omega]

set_option maxRecDepth 20000 in
theorem keccakLanes_bytes (OUTPUT_LEN rate : Std.Usize) (delim : Std.U8) (sfx : List Bool)
    (M : Slice Std.U8)
    (hrate1 : 1 ≤ rate.val) (hrate200 : rate.val ≤ 200) (hrate8 : rate.val % 8 = 0)
    (hsfx : sfx.length + 2 ≤ 8)
    (hdelim : byteBits delim = sfx ++ true :: List.replicate (7 - sfx.length) false) :
    (keccakLanes OUTPUT_LEN rate.val delim M.val).val
      = b2hList (keccakCList (1600 - 8 * rate.val) (h2bList M.val ++ sfx)
        (8 * OUTPUT_LEN.val)) := by
  have hr : 1600 - (1600 - 8 * rate.val) = 8 * rate.val := by omega
  have hc : 1600 - 8 * rate.val < 1600 := by omega
  set s0 : Lanes := absorbLanes rate.val delim M.val with hs0_def
  have hs0b := lanesToBits_absorbLanes rate delim sfx hrate1 hrate200 hrate8 hsfx hdelim M
  have hpre : (h2bList M.val ++ sfx).length = 8 * M.val.length + sfx.length :=
    paddedBits_pre_len M.val sfx
  have hpad : (h2bList M.val ++ sfx) ++ padBits (8 * rate.val) (h2bList M.val ++ sfx).length
      = paddedBits M.val sfx (8 * rate.val) := by rw [hpre]; rfl
  have hplen : (paddedBits M.val sfx (8 * rate.val)).length
      = 8 * rate.val * (M.val.length / rate.val + 1) :=
    paddedBits_len M.val sfx rate.val hrate1 hsfx
  have hblocks : (paddedBits M.val sfx (8 * rate.val)).length / (8 * rate.val)
      = M.val.length / rate.val + 1 := by
    rw [hplen, Nat.mul_div_cancel_left _ (by omega)]
  have hkc : keccakCList (1600 - 8 * rate.val) (h2bList M.val ++ sfx) (8 * OUTPUT_LEN.val)
      = (squeezeAll keccakF (8 * rate.val) (8 * OUTPUT_LEN.val) (lanesToBits s0)).take
        (8 * OUTPUT_LEN.val) := by
    simp only [keccakCList, hr]
    rw [hpad, hblocks, ← hs0b]
  have hs0len : (lanesToBits s0).length = 1600 := lanesToBits_len s0
  have hkclen : (keccakCList (1600 - 8 * rate.val) (h2bList M.val ++ sfx)
      (8 * OUTPUT_LEN.val)).length = 8 * OUTPUT_LEN.val :=
    keccakCList_len _ _ _ hc
  rw [keccakLanes, ← hs0_def, squeezeLanes_bits OUTPUT_LEN s0 rate hrate1 hrate200]
  · rw [b2hList_of_len _ OUTPUT_LEN.val hkclen]
    show (List.range OUTPUT_LEN.val).map _ = _
    apply List.map_congr_left
    intro i hi
    have hi' : i < OUTPUT_LEN.val := by simpa using hi
    apply byteOf_congr
    intro t ht
    have hq : 8 * i + t < 8 * OUTPUT_LEN.val := by omega
    rw [hkc, getElem!_pos _ (8 * i + t) (by
        rw [List.length_take]
        have := squeezeFrom_len keccakF (fun x _ => keccakF_len x) (8 * rate.val)
          (8 * OUTPUT_LEN.val) (by omega) (by omega) (8 * OUTPUT_LEN.val / (8 * rate.val))
          (lanesToBits s0) [] hs0len (by
            have h1 := Nat.div_add_mod (8 * OUTPUT_LEN.val) (8 * rate.val)
            have h2 := Nat.mod_lt (8 * OUTPUT_LEN.val) (show 0 < 8 * rate.val by omega)
            have h3 : (8 * OUTPUT_LEN.val / (8 * rate.val) + 1) * (8 * rate.val)
                = 8 * rate.val * (8 * OUTPUT_LEN.val / (8 * rate.val)) + 8 * rate.val := by ring
            simp only [List.length_nil, Nat.zero_add]
            omega)
        simp only [squeezeAll] at this ⊢
        omega),
      List.getElem_take, ← getElem!_pos _ (8 * i + t) (by
        have := squeezeFrom_len keccakF (fun x _ => keccakF_len x) (8 * rate.val)
          (8 * OUTPUT_LEN.val) (by omega) (by omega) (8 * OUTPUT_LEN.val / (8 * rate.val))
          (lanesToBits s0) [] hs0len (by
            have h1 := Nat.div_add_mod (8 * OUTPUT_LEN.val) (8 * rate.val)
            have h2 := Nat.mod_lt (8 * OUTPUT_LEN.val) (show 0 < 8 * rate.val by omega)
            have h3 : (8 * OUTPUT_LEN.val / (8 * rate.val) + 1) * (8 * rate.val)
                = 8 * rate.val * (8 * OUTPUT_LEN.val / (8 * rate.val)) + 8 * rate.val := by ring
            simp only [List.length_nil, Nat.zero_add]
            omega)
        simp only [squeezeAll] at this ⊢
        omega),
      squeezeAll_get keccakF (8 * rate.val) (8 * OUTPUT_LEN.val) (by omega)
        (fun x _ => keccakF_len x) (by omega) (lanesToBits s0) hs0len (8 * i + t) hq]
    have hb : i % rate.val < rate.val := Nat.mod_lt _ (by omega)
    have hid : rate.val * (i / rate.val) + i % rate.val = i := Nat.div_add_mod i rate.val
    have hrw : 8 * i + t = (8 * (i % rate.val) + t) + (8 * rate.val) * (i / rate.val) := by
      have h1 : 8 * i = 8 * (rate.val * (i / rate.val)) + 8 * (i % rate.val) := by omega
      have h2 : 8 * (rate.val * (i / rate.val)) = (8 * rate.val) * (i / rate.val) := by ring
      omega
    have hdiv : (8 * i + t) / (8 * rate.val) = i / rate.val := by
      rw [hrw, Nat.add_mul_div_left _ _ (show 0 < 8 * rate.val by omega),
        Nat.div_eq_of_lt (by omega)]
      omega
    have hmod : (8 * i + t) % (8 * rate.val) = 8 * (i % rate.val) + t := by
      rw [hrw, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hdiv, hmod]

/-! ### The six entry points

Each says the transcript's entry point computes the lane model's `keccakLanes`
at that rate and delimiter: `keccakLanes_bytes` gives the model's bytes, the
`*_bytes_eq` theorems in `Sha3.lean` give the transcript's, and they are the
same bit string.  These are what `Sponge/` is stated against. -/

/-- `SHA3-224`: the transcript computes the lane model. -/
theorem sha3_224_lanes_agree (M : Slice Std.U8) :
    hacspec_sha3_pedantic.bytes.sha3_224 M
      = ok (keccakLanes 28#usize (144#usize : Std.Usize).val 6#u8 M.val) := by
  obtain ⟨o2, h2, h2v⟩ := sha3_224_bytes_eq M
  have hkl := keccakLanes_bytes 28#usize 144#usize 6#u8 [false, true] M
    (by simp) (by simp) (by simp) (by simp) (by decide)
  rw [h2]
  congr 1
  apply Subtype.ext
  rw [h2v, hkl]
  norm_num

/-- `SHA3-256`: the transcript computes the lane model. -/
theorem sha3_256_lanes_agree (M : Slice Std.U8) :
    hacspec_sha3_pedantic.bytes.sha3_256 M
      = ok (keccakLanes 32#usize (136#usize : Std.Usize).val 6#u8 M.val) := by
  obtain ⟨o2, h2, h2v⟩ := sha3_256_bytes_eq M
  have hkl := keccakLanes_bytes 32#usize 136#usize 6#u8 [false, true] M
    (by simp) (by simp) (by simp) (by simp) (by decide)
  rw [h2]
  congr 1
  apply Subtype.ext
  rw [h2v, hkl]
  norm_num

/-- `SHA3-384`: the transcript computes the lane model. -/
theorem sha3_384_lanes_agree (M : Slice Std.U8) :
    hacspec_sha3_pedantic.bytes.sha3_384 M
      = ok (keccakLanes 48#usize (104#usize : Std.Usize).val 6#u8 M.val) := by
  obtain ⟨o2, h2, h2v⟩ := sha3_384_bytes_eq M
  have hkl := keccakLanes_bytes 48#usize 104#usize 6#u8 [false, true] M
    (by simp) (by simp) (by simp) (by simp) (by decide)
  rw [h2]
  congr 1
  apply Subtype.ext
  rw [h2v, hkl]
  norm_num

/-- `SHA3-512`: the transcript computes the lane model. -/
theorem sha3_512_lanes_agree (M : Slice Std.U8) :
    hacspec_sha3_pedantic.bytes.sha3_512 M
      = ok (keccakLanes 64#usize (72#usize : Std.Usize).val 6#u8 M.val) := by
  obtain ⟨o2, h2, h2v⟩ := sha3_512_bytes_eq M
  have hkl := keccakLanes_bytes 64#usize 72#usize 6#u8 [false, true] M
    (by simp) (by simp) (by simp) (by simp) (by decide)
  rw [h2]
  congr 1
  apply Subtype.ext
  rw [h2v, hkl]
  norm_num

/-- `SHAKE128`: the transcript computes the lane model. -/
theorem shake128_lanes_agree (NU : Std.Usize) (M : Slice Std.U8) :
    ∃ o2 : alloc.vec.Vec Std.U8,
      hacspec_sha3_pedantic.bytes.shake128 M NU = ok o2 ∧
      o2.val = (keccakLanes NU (168#usize : Std.Usize).val 31#u8 M.val).val := by
  obtain ⟨o2, h2, h2v⟩ := shake128_bytes_eq M NU
  have hkl := keccakLanes_bytes NU 168#usize 31#u8 [true, true, true, true] M
    (by simp) (by simp) (by simp) (by simp) (by decide)
  refine ⟨o2, h2, ?_⟩
  rw [h2v, hkl]
  norm_num

/-- `SHAKE256`: the transcript computes the lane model. -/
theorem shake256_lanes_agree (NU : Std.Usize) (M : Slice Std.U8) :
    ∃ o2 : alloc.vec.Vec Std.U8,
      hacspec_sha3_pedantic.bytes.shake256 M NU = ok o2 ∧
      o2.val = (keccakLanes NU (136#usize : Std.Usize).val 31#u8 M.val).val := by
  obtain ⟨o2, h2, h2v⟩ := shake256_bytes_eq M NU
  have hkl := keccakLanes_bytes NU 136#usize 31#u8 [true, true, true, true] M
    (by simp) (by simp) (by simp) (by simp) (by decide)
  refine ⟨o2, h2, ?_⟩
  rw [h2v, hkl]
  norm_num

-- Pin the six agreements to Lean's standard three axioms.

/--
info: 'LibcruxIotSha3.Composition.Pedantic.sha3_224_lanes_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sha3_224_lanes_agree

/--
info: 'LibcruxIotSha3.Composition.Pedantic.sha3_256_lanes_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sha3_256_lanes_agree

/--
info: 'LibcruxIotSha3.Composition.Pedantic.sha3_384_lanes_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sha3_384_lanes_agree

/--
info: 'LibcruxIotSha3.Composition.Pedantic.sha3_512_lanes_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sha3_512_lanes_agree

/--
info: 'LibcruxIotSha3.Composition.Pedantic.shake128_lanes_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms shake128_lanes_agree

/--
info: 'LibcruxIotSha3.Composition.Pedantic.shake256_lanes_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms shake256_lanes_agree

end LibcruxIotSha3.Composition.Pedantic
