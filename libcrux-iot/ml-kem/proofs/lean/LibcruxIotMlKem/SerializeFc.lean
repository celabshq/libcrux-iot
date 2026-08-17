/-
  # `SerializeFc.lean` — INC-1 obligation stubs for the (de)serialize layer.

  SCAFFOLD ONLY. Every theorem below is `sorry`ed: these are the OBLIGATIONS the
  driver will dispatch a PROVER to close, not results. They are authored by the
  HELPER as a *low-distance binding* to the EXISTING `HacspecMlKem` model (skill
  §0.2) — nothing here invents a spec. The statements are NOT frozen until the
  PRINCIPAL approves them; the driver locks each signature at that point.

  Shape follows the tree's established convention (see `Matrix/ComputeAsPlusE.lean`,
  `Serialize.lean`): an mvcgen Triple whose post equates the hacspec model applied
  to `lift`ed inputs with `.ok` of the `lift`ed impl result.

      ⦃ ⌜pre⌝ ⦄  <impl call>  ⦃ ⇓ p => ⌜ <hacspec> (lift args…) = .ok (lift p…) ⌝ ⦄

  ## Scope of THIS file

  Only the bindings where the impl function and a hacspec function correspond
  1:1, so the statement is mechanical. Deliberately NOT scaffolded here, because
  each needs a PRINCIPAL decision rather than a transcription — see the campaign
  STATE.md (P7):

  * `compress_then_serialize_ring_element_u` / `deserialize_then_decompress_ring_element_u`
    — the impl works on ONE ring element; the hacspec `compress_then_serialize_u` /
    `deserialize_then_decompress_u` work on the WHOLE rank-K vector. Binding the
    per-element impl needs either a spec-side per-element projection or a
    whole-vector statement assembled from K impl calls. That is a modelling
    choice, not a transcription.
  * `compress_then_serialize_{4,5,10,11}` / `deserialize_then_decompress_{4,5,10,11}`
    — impl-internal specializations of a `d`-parametric operation. No named
    hacspec counterpart; the natural binding is
    `byte_encode_into (compress_d · d) ` / `byte_decode` at that `d`, i.e. step
    lemmas feeding the `_u`/`_v` apexes above. Their statement shape should be
    fixed together with the `_u` decision so the two compose.
  * `to_unsigned_field_modulus` — an impl-internal helper with no spec image.
-/

import LibcruxIotMlKem.Spec.Lift
import LibcruxIotMlKem.Serialize
import LibcruxIotMlKem.Util.CreateI
import LibcruxIotMlKem.Util.LoopSpecs
import LibcruxIotMlKem.Matrix.ComputeRingElementV.Impl

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace libcrux_iot_ml_kem.SerializeFc

open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec.Lift
open libcrux_iot_ml_kem.Spec

/-! ## PROVER bank for L5.7 — pure decode model + impl-side closed forms.

    Everything in this section is `private`; the shared vocabulary is the pure
    12-bit decode model `dec12_lo` / `dec12_hi` / `dec12`, which is the common
    normal form of the impl's byte arithmetic and the spec's bit vector. -/

section L57Bank

open Aeneas.Std

/-- Low lane of a 3-byte group: bits 0..11 = `b0 ++ (b1 & 0xf)`. -/
private def dec12_lo (b0 b1 : Nat) : Nat := b0 + b1 % 16 * 256

/-- High lane of a 3-byte group: bits 12..23 = `(b1 >> 4) ++ b2`. -/
private def dec12_hi (b1 b2 : Nat) : Nat := b1 / 16 + b2 * 16

private theorem dec12_lo_lt (b0 b1 : Nat) (h0 : b0 < 256) : dec12_lo b0 b1 < 4096 := by
  unfold dec12_lo; have : b1 % 16 < 16 := Nat.mod_lt _ (by omega); omega

private theorem dec12_hi_lt (b1 b2 : Nat) (h1 : b1 < 256) (h2 : b2 < 256) :
    dec12_hi b1 b2 < 4096 := by
  unfold dec12_hi; have : b1 / 16 < 16 := by omega
  omega

/-! ### Pure ℕ bit algebra

    `bitSum f k = Σ_{t<k} (if f t then 2^t else 0)`. The two facts we need are
    (a) the bit-decomposition round trip `bitSum (bit x) k = x % 2^k` and
    (b) bit extraction from a bounded sum, `bitSum f k / 2^s % 2 = f s`. -/

/-- `Σ_{t<k} (if f t then 2^t else 0)`. -/
private def bitSum (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => bitSum f k + (if f k then 2 ^ k else 0)

/-- Bit `s` of a natural number, as a `Bool`. -/
private def natBit (x s : Nat) : Bool := decide (x / 2 ^ s % 2 = 1)

private theorem bitSum_lt (f : Nat → Bool) : ∀ k, bitSum f k < 2 ^ k
  | 0 => by simp [bitSum]
  | k + 1 => by
      have ih := bitSum_lt f k
      have : (if f k then 2 ^ k else 0) ≤ 2 ^ k := by split <;> omega
      have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
      simp only [bitSum]; omega

/-- Splitting a modulus by one bit: `x % (b*2) = x % b + b * (x / b % 2)`. -/
private theorem mod_two_mul_split (x b : Nat) (hb : 0 < b) :
    x % (b * 2) = x % b + b * (x / b % 2) := by
  have h1 : x = b * (x / b) + x % b := (Nat.div_add_mod x b).symm
  have h2 : x / b = 2 * (x / b / 2) + x / b % 2 := (Nat.div_add_mod (x / b) 2).symm
  have hr1 : x % b < b := Nat.mod_lt _ hb
  have hr2 : x / b % 2 < 2 := Nat.mod_lt _ (by omega)
  have hx : x = (b * 2) * (x / b / 2) + (b * (x / b % 2) + x % b) := by
    calc x = b * (x / b) + x % b := h1
    _ = b * (2 * (x / b / 2) + x / b % 2) + x % b := by rw [← h2]
    _ = (b * 2) * (x / b / 2) + (b * (x / b % 2) + x % b) := by ring
  have hlt : b * (x / b % 2) + x % b < b * 2 := by
    have : b * (x / b % 2) ≤ b * 1 := Nat.mul_le_mul_left b (by omega)
    omega
  calc x % (b * 2) = ((b * 2) * (x / b / 2) + (b * (x / b % 2) + x % b)) % (b * 2) := by rw [← hx]
  _ = (b * (x / b % 2) + x % b) % (b * 2) := by
        rw [Nat.mul_add_mod]
  _ = b * (x / b % 2) + x % b := Nat.mod_eq_of_lt hlt
  _ = x % b + b * (x / b % 2) := by omega

/-- (a) Bit decomposition round trip. -/
private theorem bitSum_natBit (x : Nat) : ∀ k, bitSum (natBit x) k = x % 2 ^ k
  | 0 => by simp [bitSum, Nat.mod_one]
  | k + 1 => by
      have ih := bitSum_natBit x k
      have hb : (0:Nat) < 2 ^ k := Nat.two_pow_pos _
      have hsplit : x % 2 ^ (k + 1) = x % 2 ^ k + 2 ^ k * (x / 2 ^ k % 2) := by
        rw [pow_succ]; exact mod_two_mul_split x (2 ^ k) hb
      have hb2 : x / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by omega)
      simp only [bitSum, ih, natBit, hsplit]
      by_cases h : x / 2 ^ k % 2 = 1 <;> simp [h] <;> omega

/-- (b) Bit extraction from a bit sum. -/
private theorem natBit_bitSum (f : Nat → Bool) (k s : Nat) (hs : s < k) :
    natBit (bitSum f k) s = f s := by
  induction k with
  | zero => omega
  | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h | h
      · -- s < k: the top term `2^k` does not affect bit s
        have hlow : bitSum f k < 2 ^ k := bitSum_lt f k
        have hps : (0:Nat) < 2 ^ s := Nat.two_pow_pos _
        have hdvd : 2 ^ s ∣ 2 ^ k := pow_dvd_pow 2 (le_of_lt h)
        obtain ⟨c, hc⟩ := hdvd
        have hc2 : 2 ∣ c := by
          have : 2 ^ (s + 1) ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
          obtain ⟨e, he⟩ := this
          refine ⟨e, ?_⟩
          have h2s : (0:Nat) < 2 ^ s := hps
          have : 2 ^ s * c = 2 ^ s * (2 * e) := by
            rw [← hc, he, pow_succ]; ring
          exact Nat.eq_of_mul_eq_mul_left h2s this
        obtain ⟨e, he⟩ := hc2
        simp only [bitSum, natBit]
        rw [← ih h]
        simp only [natBit]
        congr 1
        by_cases hf : f k
        · simp only [hf, if_true]
          have hkey : (bitSum f k + 2 ^ k) / 2 ^ s = bitSum f k / 2 ^ s + 2 * e := by
            rw [hc, he, show 2 ^ s * (2 * e) = (2 * e) * 2 ^ s by ring,
              Nat.add_mul_div_right _ _ hps]
          rw [hkey, Nat.add_mul_mod_self_left]
        · simp [hf]
      · -- s = k: the top term is exactly bit s
        subst h
        have hlow : bitSum f s < 2 ^ s := bitSum_lt f s
        have hps : (0:Nat) < 2 ^ s := Nat.two_pow_pos _
        simp only [bitSum, natBit]
        by_cases hf : f s
        · simp only [hf, if_true]
          rw [show bitSum f s + 2 ^ s = bitSum f s + 1 * 2 ^ s by ring,
              Nat.add_mul_div_right _ _ hps, Nat.div_eq_of_lt hlow]
          simp [hf]
        · simp only [hf, Bool.false_eq_true, if_false, add_zero]
          rw [Nat.div_eq_of_lt hlow]
          simp [hf]

private theorem bitSum_congr (f g : Nat → Bool) (k : Nat)
    (h : ∀ t, t < k → f t = g t) : bitSum f k = bitSum g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [bitSum, bitSum, ih (fun t ht => h t (by omega)), h k (by omega)]

private theorem bitSum_add (f : Nat → Bool) (a : Nat) :
    ∀ b, bitSum f (a + b) = bitSum f a + 2 ^ a * bitSum (fun t => f (a + t)) b
  | 0 => by simp [bitSum]
  | b + 1 => by
      have ih := bitSum_add f a b
      have hab : a + (b + 1) = (a + b) + 1 := by omega
      rw [hab, bitSum, ih, bitSum]
      by_cases hf : f (a + b) <;> simp [hf, pow_add] <;> ring

private theorem bitSum_shift (x c : Nat) :
    ∀ k, bitSum (fun t => natBit x (c + t)) k = x / 2 ^ c % 2 ^ k := by
  intro k
  have hpt : ∀ t, natBit x (c + t) = natBit (x / 2 ^ c) t := by
    intro t
    simp only [natBit, pow_add, Nat.div_div_eq_div_mul]
  rw [bitSum_congr _ (natBit (x / 2 ^ c)) k (fun t _ => hpt t), bitSum_natBit]

/-! ### The 12-bit lane model over a byte list -/

/-- Bit `m` of a byte list, little-endian within each byte — the pure form of
    the hacspec `bytes_to_bits` closure. -/
private def sliceBit (l : List Std.U8) (m : Nat) : Bool := natBit (l[m / 8]!.val) (m % 8)

/-- Byte-level 12-bit decode of lane `j`: the pure form of the impl's
    `deserialize_12_int`. -/
private def dec12 (l : List Std.U8) (j : Nat) : Nat :=
  if j % 2 = 0 then dec12_lo (l[3 * (j / 2)]!.val) (l[3 * (j / 2) + 1]!.val)
  else dec12_hi (l[3 * (j / 2) + 1]!.val) (l[3 * (j / 2) + 2]!.val)

private theorem dec12_lt (l : List Std.U8) (j : Nat) : dec12 l j < 4096 := by
  unfold dec12
  have h0 : ∀ i : Nat, (l[i]! : Std.U8).val < 256 := by
    intro i; have := (l[i]! : Std.U8).hBounds; simpa using this
  split
  · exact dec12_lo_lt _ _ (h0 _)
  · exact dec12_hi_lt _ _ (h0 _) (h0 _)

private theorem u8_val_lt (l : List Std.U8) (i : Nat) : (l[i]! : Std.U8).val < 256 := by
  have := (l[i]! : Std.U8).hBounds; simpa using this

/-- Even lane of a 3-byte group: the low 12 bits. -/
private theorem bitSum_sliceBit_even (l : List Std.U8) (g : Nat) :
    bitSum (fun t => sliceBit l (12 * (2 * g) + t)) 12
      = dec12_lo (l[3 * g]!.val) (l[3 * g + 1]!.val) := by
  have e1 : bitSum (fun t => sliceBit l (12 * (2 * g) + t)) 8
      = bitSum (natBit (l[3 * g]!.val)) 8 := by
    refine bitSum_congr _ _ 8 (fun t ht => ?_)
    have hi : (12 * (2 * g) + t) / 8 = 3 * g := by omega
    have hm : (12 * (2 * g) + t) % 8 = t := by omega
    simp only [sliceBit, hi, hm]
  have e2 : bitSum (fun t => sliceBit l (12 * (2 * g) + (8 + t))) 4
      = bitSum (natBit (l[3 * g + 1]!.val)) 4 := by
    refine bitSum_congr _ _ 4 (fun t ht => ?_)
    have hi : (12 * (2 * g) + (8 + t)) / 8 = 3 * g + 1 := by omega
    have hm : (12 * (2 * g) + (8 + t)) % 8 = t := by omega
    simp only [sliceBit, hi, hm]
  rw [show (12 : Nat) = 8 + 4 from rfl, bitSum_add, e1, e2, bitSum_natBit, bitSum_natBit]
  have hlt : (l[3 * g]! : Std.U8).val < 2 ^ 8 := u8_val_lt l (3 * g)
  rw [Nat.mod_eq_of_lt hlt]
  unfold dec12_lo
  simp only [show (2:Nat) ^ 8 = 256 from rfl, show (2:Nat) ^ 4 = 16 from rfl]
  ring

/-- Odd lane of a 3-byte group: the high 12 bits. -/
private theorem bitSum_sliceBit_odd (l : List Std.U8) (g : Nat) :
    bitSum (fun t => sliceBit l (12 * (2 * g + 1) + t)) 12
      = dec12_hi (l[3 * g + 1]!.val) (l[3 * g + 2]!.val) := by
  have e1 : bitSum (fun t => sliceBit l (12 * (2 * g + 1) + t)) 4
      = bitSum (fun t => natBit (l[3 * g + 1]!.val) (4 + t)) 4 := by
    refine bitSum_congr _ _ 4 (fun t ht => ?_)
    have hi : (12 * (2 * g + 1) + t) / 8 = 3 * g + 1 := by omega
    have hm : (12 * (2 * g + 1) + t) % 8 = 4 + t := by omega
    simp only [sliceBit, hi, hm]
  have e2 : bitSum (fun t => sliceBit l (12 * (2 * g + 1) + (4 + t))) 8
      = bitSum (natBit (l[3 * g + 2]!.val)) 8 := by
    refine bitSum_congr _ _ 8 (fun t ht => ?_)
    have hi : (12 * (2 * g + 1) + (4 + t)) / 8 = 3 * g + 2 := by omega
    have hm : (12 * (2 * g + 1) + (4 + t)) % 8 = t := by omega
    simp only [sliceBit, hi, hm]
  rw [show (12 : Nat) = 4 + 8 from rfl, bitSum_add, e1, e2, bitSum_shift, bitSum_natBit]
  have h1 : (l[3 * g + 1]! : Std.U8).val < 256 := u8_val_lt l (3 * g + 1)
  have h2 : (l[3 * g + 2]! : Std.U8).val < 2 ^ 8 := u8_val_lt l (3 * g + 2)
  rw [Nat.mod_eq_of_lt h2]
  unfold dec12_hi
  simp only [show (2:Nat) ^ 8 = 256 from rfl, show (2:Nat) ^ 4 = 16 from rfl]
  rw [Nat.mod_eq_of_lt (show (l[3 * g + 1]! : Std.U8).val / 16 < 16 by omega)]
  ring

/-- **The decode keystone**: the 12 spec-side bits of lane `j` sum to the
    impl-side byte expression `dec12`. -/
private theorem bitSum_sliceBit_eq_dec12 (l : List Std.U8) (j : Nat) :
    bitSum (fun t => sliceBit l (12 * j + t)) 12 = dec12 l j := by
  unfold dec12
  rcases (show j % 2 = 0 ∨ j % 2 = 1 by omega) with he | he
  · rw [if_pos he, show 12 * j = 12 * (2 * (j / 2)) by omega]
    exact bitSum_sliceBit_even l (j / 2)
  · rw [if_neg (by omega), show 12 * j = 12 * (2 * (j / 2) + 1) by omega]
    exact bitSum_sliceBit_odd l (j / 2)

/-! ### Impl side — `deserialize_12_int` closed form

    All lanes are `I16`s holding values `< 4096`, so the signed `.val` agrees
    with the `BitVec.toNat`, and the byte algebra is pure ℕ. -/

/-- The `U8 → I16` widening the impl performs (classify/declassify are the
    identity in this tree's model). -/
private def c16 (x : Std.U8) : Std.I16 := Std.UScalar.hcast .I16 x

private theorem as_i16_eq (x : Std.U8) :
    libcrux_secrets.U8.Insts.Libcrux_secretsIntCastOps.as_i16 x = .ok (c16 x) := by
  unfold libcrux_secrets.U8.Insts.Libcrux_secretsIntCastOps.as_i16
    libcrux_secrets.traits.Declassify.Blanket.declassify
    libcrux_secrets.traits.Classify.Blanket.classify
  simp [c16, Aeneas.Std.lift]

private theorem c16_bv_toNat (x : Std.U8) : (c16 x).bv.toNat = x.val := by
  have hx : x.val < 256 := by scalar_tac
  show (Std.IScalar.bv (Std.UScalar.hcast .I16 x)).toNat = x.val
  rw [Std.UScalar.hcast_bv_eq, BitVec.toNat_setWidth, Std.IScalarTy.I16_numBits_eq]
  show x.val % 2 ^ 16 = x.val
  exact Nat.mod_eq_of_lt (by omega)

/-- Nonnegative small `I16`s: `.val` is the `BitVec.toNat`. -/
private theorem i16_val_of_toNat (x : Std.I16) (h : x.bv.toNat < 4096) :
    x.val = (x.bv.toNat : Int) := by
  show x.bv.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt (by simpa using (by omega : 2 * x.bv.toNat < 65536))]

private theorem slice_index_usize_eq {α : Type} [Inhabited α] (v : Slice α) (i : Std.Usize)
    (h : i.val < v.val.length) :
    Aeneas.Std.Slice.index_usize v i = .ok (v.val[i.val]!) := by
  simp only [Aeneas.Std.Slice.index_usize, Aeneas.Std.Slice.getElem?_Usize_eq,
    List.getElem?_eq_getElem h]
  rw [getElem!_pos v.val i.val h]

/-- The two `I16` lanes the impl computes from a 3-byte group. -/
private def r0of (x0 x1 : Std.U8) : Std.I16 :=
  { bv := (((c16 x1).bv &&& 15#16) <<< 8) ||| ((c16 x0).bv &&& 255#16) }

private def r1of (x1 x2 : Std.U8) : Std.I16 :=
  { bv := ((c16 x2).bv <<< 4) ||| (((c16 x1).bv.sshiftRight 4) &&& 15#16) }

private theorem deserialize_12_int_eq (s : Slice Std.U8) (h : 3 ≤ s.val.length) :
    libcrux_iot_ml_kem.vector.portable.serialize.deserialize_12_int s
      = .ok (r0of s.val[0]! s.val[1]!, r1of s.val[1]! s.val[2]!) := by
  have h0 : Aeneas.Std.Slice.index_usize s 0#usize = .ok s.val[0]! :=
    slice_index_usize_eq s 0#usize (by simpa using (by omega : 0 < s.val.length))
  have h1 : Aeneas.Std.Slice.index_usize s 1#usize = .ok s.val[1]! :=
    slice_index_usize_eq s 1#usize (by simpa using (by omega : 1 < s.val.length))
  have h2 : Aeneas.Std.Slice.index_usize s 2#usize = .ok s.val[2]! :=
    slice_index_usize_eq s 2#usize (by simpa using (by omega : 2 < s.val.length))
  unfold libcrux_iot_ml_kem.vector.portable.serialize.deserialize_12_int
  rw [h0]; simp only [Aeneas.Std.bind_tc_ok]
  rw [as_i16_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [h1]; simp only [Aeneas.Std.bind_tc_ok]
  rw [as_i16_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [h2]; simp only [Aeneas.Std.bind_tc_ok]
  rw [as_i16_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rfl

private theorem nat_or_shift (a b k : Nat) (hb : b < 2 ^ k) :
    (a <<< k) ||| b = a * 2 ^ k + b := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hb a, Nat.shiftLeft_eq]

private theorem nat_and_15 (x : Nat) : x &&& 15 = x % 16 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 4
  norm_num at this
  exact this

private theorem nat_and_255 (x : Nat) : x &&& 255 = x % 256 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 8
  norm_num at this
  exact this

private theorem r0of_bv_toNat (x0 x1 : Std.U8) :
    (r0of x0 x1).bv.toNat = dec12_lo x0.val x1.val := by
  have hb0 : x0.val < 256 := by scalar_tac
  have hb1 : x1.val < 256 := by scalar_tac
  show (((((c16 x1).bv &&& 15#16) <<< 8) ||| ((c16 x0).bv &&& 255#16)) : BitVec 16).toNat = _
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_and,
    c16_bv_toNat, c16_bv_toNat]
  have h15 : (15#16 : BitVec 16).toNat = 15 := rfl
  have h255 : (255#16 : BitVec 16).toNat = 255 := rfl
  rw [h15, h255, nat_and_15, nat_and_255, Nat.mod_eq_of_lt hb0]
  have hlt : (x1.val % 16) <<< 8 < 2 ^ 16 := by
    rw [Nat.shiftLeft_eq]
    have : x1.val % 16 < 16 := Nat.mod_lt _ (by omega)
    simp only [show (2:Nat) ^ 8 = 256 from rfl, show (2:Nat) ^ 16 = 65536 from rfl]
    omega
  rw [Nat.mod_eq_of_lt hlt, nat_or_shift _ _ _ (show x0.val < 2 ^ 8 by omega)]
  unfold dec12_lo
  simp only [show (2:Nat) ^ 8 = 256 from rfl]
  omega

private theorem r1of_bv_toNat (x1 x2 : Std.U8) :
    (r1of x1 x2).bv.toNat = dec12_hi x1.val x2.val := by
  have hb1 : x1.val < 256 := by scalar_tac
  have hb2 : x2.val < 256 := by scalar_tac
  have hmsb : ((c16 x1).bv).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, c16_bv_toNat]
    simp only [show (2:Nat) ^ 16 = 65536 from rfl]; omega
  show ((((c16 x2).bv <<< 4) ||| (((c16 x1).bv.sshiftRight 4) &&& 15#16)) : BitVec 16).toNat = _
  rw [BitVec.sshiftRight_eq_of_msb_false hmsb]
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    c16_bv_toNat, c16_bv_toNat]
  have h15 : (15#16 : BitVec 16).toNat = 15 := rfl
  rw [h15, nat_and_15]
  have hsr : x1.val >>> 4 = x1.val / 16 := by
    rw [Nat.shiftRight_eq_div_pow]
  rw [hsr, Nat.mod_eq_of_lt (show x1.val / 16 < 16 by omega)]
  have hlt : x2.val <<< 4 < 2 ^ 16 := by
    rw [Nat.shiftLeft_eq]
    simp only [show (2:Nat) ^ 4 = 16 from rfl, show (2:Nat) ^ 16 = 65536 from rfl]
    omega
  rw [Nat.mod_eq_of_lt hlt, nat_or_shift _ _ _ (show x1.val / 16 < 2 ^ 4 by
    simp only [show (2:Nat) ^ 4 = 16 from rfl]; omega)]
  unfold dec12_hi
  simp only [show (2:Nat) ^ 4 = 16 from rfl]
  omega

private theorem r0of_val (x0 x1 : Std.U8) :
    (r0of x0 x1).val = (dec12_lo x0.val x1.val : Int) := by
  have hb0 : x0.val < 256 := by scalar_tac
  rw [i16_val_of_toNat _ (by rw [r0of_bv_toNat]; exact dec12_lo_lt _ _ hb0), r0of_bv_toNat]

private theorem r1of_val (x1 x2 : Std.U8) :
    (r1of x1 x2).val = (dec12_hi x1.val x2.val : Int) := by
  have hb1 : x1.val < 256 := by scalar_tac
  have hb2 : x2.val < 256 := by scalar_tac
  rw [i16_val_of_toNat _ (by rw [r1of_bv_toNat]; exact dec12_hi_lt _ _ hb1 hb2), r1of_bv_toNat]

/-! ### Impl side — the 16-lane `deserialize_12`

    The sub-slicing here is over STRICT ranges (`3g < 3g+3`), so it goes through
    aeneas's real `Slice.subslice_spec`, NOT the `Slice.subslice_le_eq`
    empty-range axiom. -/

private theorem slice_index_range_strict {T : Type} [Inhabited T]
    (s : Slice T) (a b : Std.Usize)
    (h0 : a.val < b.val) (h1 : b.val ≤ s.val.length) :
    ∃ ns : Slice T,
      CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
        (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) s
        ⟨a, b⟩ = .ok ns
      ∧ ns.val.length = b.val - a.val
      ∧ ∀ i : Nat, i < b.val - a.val → ns.val[i]! = s.val[a.val + i]! := by
  obtain ⟨ns, hns_eq, hns_val, hns_get⟩ :=
    Std.WP.spec_imp_exists (Aeneas.Std.Slice.subslice_spec s ⟨a, b⟩ h0 h1)
  have hlen : ns.val.length = b.val - a.val := by
    rw [hns_val]
    show (List.slice a.val b.val s.val).length = b.val - a.val
    rw [List.slice_length]; omega
  refine ⟨ns, ?_, hlen, ?_⟩
  · unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
      CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
      CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get
      CoreModels.rust_primitives.slice.slice_slice
      CoreModels.rust_primitives.slice.slice_length
    simp only [hns_eq, bind_tc_ok]
    split_ifs with hc1 hc2
    · rfl
    · exfalso; scalar_tac
    · exfalso; scalar_tac
  · intro i hi
    rw [hns_val]
    show (List.slice a.val b.val s.val)[i]! = _
    rw [List.getElem!_slice a.val b.val i s.val ⟨by omega, by omega⟩]

/-- The `I16` the impl writes into lane `k` of a 16-lane vector. -/
private def lane12 (l : List Std.U8) (k : Nat) : Std.I16 :=
  if k % 2 = 0 then r0of l[3 * (k / 2)]! l[3 * (k / 2) + 1]!
  else r1of l[3 * (k / 2) + 1]! l[3 * (k / 2) + 2]!

private theorem lane12_val (l : List Std.U8) (k : Nat) :
    (lane12 l k).val = (dec12 l k : Int) := by
  unfold lane12 dec12
  split
  · exact r0of_val _ _
  · exact r1of_val _ _

/-- One 3-byte group of `deserialize_12`: sub-slice + `deserialize_12_int`. -/
private theorem d12_group (bytes : Slice Std.U8) (h : bytes.val.length = 24)
    (a bnd : Std.Usize) (n0 n1 n2 : Nat) (hn : a.val = n0)
    (hn1 : n1 = n0 + 1) (hn2 : n2 = n0 + 2) (ha : n0 + 3 = bnd.val) (hb : bnd.val ≤ 24) :
    ∃ ns : Slice Std.U8,
      CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
        (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
        bytes ⟨a, bnd⟩ = .ok ns
      ∧ libcrux_iot_ml_kem.vector.portable.serialize.deserialize_12_int ns
          = .ok (r0of bytes.val[n0]! bytes.val[n1]!,
                 r1of bytes.val[n1]! bytes.val[n2]!) := by
  subst hn; subst hn1; subst hn2
  obtain ⟨ns, hns_eq, hns_len, hns_get⟩ :=
    slice_index_range_strict bytes a bnd (by omega) (by omega)
  refine ⟨ns, hns_eq, ?_⟩
  rw [deserialize_12_int_eq ns (by omega)]
  rw [hns_get 0 (by omega), hns_get 1 (by omega), hns_get 2 (by omega), Nat.add_zero]

private theorem set16_get (E : Std.Array Std.I16 16#usize)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Std.I16) (k : Nat) (hk : k < 16) :
    (((((((((((((((((E.set 0#usize v0).set 1#usize v1).set 2#usize v2).set 3#usize v3).set 4#usize v4).set 5#usize v5).set 6#usize v6).set 7#usize v7).set 8#usize v8).set 9#usize v9).set 10#usize v10).set 11#usize v11).set 12#usize v12).set 13#usize v13).set 14#usize v14).set 15#usize v15).val)[k]! = ([v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] : List Std.I16)[k]! := by
  have hE : E.val.length = 16 := by have := E.property; simpa using this
  simp only [Std.Array.set_val_eq]
  interval_cases k <;> simp_lists

private theorem bind_ok_pair {α β γ : Type} {x : Result (α × β)} {a : α} {b : β}
    (h : x = .ok (a, b)) (g : α → β → Result γ) :
    (do let (u, v) ← x; g u v) = g a b := by rw [h]; rfl

private theorem array_update16 (A : Std.Array Std.I16 16#usize) (i : Std.Usize) (x : Std.I16)
    (hi : i.val < 16) : Aeneas.Std.Array.update A i x = .ok (A.set i x) := by
  have hlen : i.val < A.val.length := by
    have hA : A.val.length = 16 := by have := A.property; simpa using this
    omega
  simp only [Aeneas.Std.Array.update, Aeneas.Std.Array.getElem?_Usize_eq,
    List.getElem?_eq_getElem hlen]
  rfl

/-- **Impl-side lane closed form**: one 24-byte chunk decodes to the 16 lanes
    `lane12`, i.e. (through `lane12_val`) to `dec12` of the chunk bytes. -/
private theorem deserialize_12_eq (bytes : Slice Std.U8)
    (out : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h : bytes.val.length = 24) :
    ∃ v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector,
      libcrux_iot_ml_kem.vector.portable.serialize.deserialize_12 bytes out = .ok v
      ∧ ∀ k : Nat, k < 16 → v.elements.val[k]! = lane12 bytes.val k := by
  obtain ⟨ns0, he0, hd0⟩ := d12_group bytes h 0#usize 3#usize 0 1 2
    (by scalar_tac) (by norm_num) (by norm_num) (by norm_num) (by scalar_tac)
  obtain ⟨ns1, he1, hd1⟩ := d12_group bytes h 3#usize 6#usize 3 4 5
    (by scalar_tac) (by norm_num) (by norm_num) (by norm_num) (by scalar_tac)
  obtain ⟨ns2, he2, hd2⟩ := d12_group bytes h 6#usize 9#usize 6 7 8
    (by scalar_tac) (by norm_num) (by norm_num) (by norm_num) (by scalar_tac)
  obtain ⟨ns3, he3, hd3⟩ := d12_group bytes h 9#usize 12#usize 9 10 11
    (by scalar_tac) (by norm_num) (by norm_num) (by norm_num) (by scalar_tac)
  obtain ⟨ns4, he4, hd4⟩ := d12_group bytes h 12#usize 15#usize 12 13 14
    (by scalar_tac) (by norm_num) (by norm_num) (by norm_num) (by scalar_tac)
  obtain ⟨ns5, he5, hd5⟩ := d12_group bytes h 15#usize 18#usize 15 16 17
    (by scalar_tac) (by norm_num) (by norm_num) (by norm_num) (by scalar_tac)
  obtain ⟨ns6, he6, hd6⟩ := d12_group bytes h 18#usize 21#usize 18 19 20
    (by scalar_tac) (by norm_num) (by norm_num) (by norm_num) (by scalar_tac)
  obtain ⟨ns7, he7, hd7⟩ := d12_group bytes h 21#usize 24#usize 21 22 23
    (by scalar_tac) (by norm_num) (by norm_num) (by norm_num) (by scalar_tac)
  refine ⟨{ elements := ((((((((((((((((out.elements.set 0#usize (r0of bytes.val[0]! bytes.val[1]!)).set 1#usize (r1of bytes.val[1]! bytes.val[2]!)).set 2#usize (r0of bytes.val[3]! bytes.val[4]!)).set 3#usize (r1of bytes.val[4]! bytes.val[5]!)).set 4#usize (r0of bytes.val[6]! bytes.val[7]!)).set 5#usize (r1of bytes.val[7]! bytes.val[8]!)).set 6#usize (r0of bytes.val[9]! bytes.val[10]!)).set 7#usize (r1of bytes.val[10]! bytes.val[11]!)).set 8#usize (r0of bytes.val[12]! bytes.val[13]!)).set 9#usize (r1of bytes.val[13]! bytes.val[14]!)).set 10#usize (r0of bytes.val[15]! bytes.val[16]!)).set 11#usize (r1of bytes.val[16]! bytes.val[17]!)).set 12#usize (r0of bytes.val[18]! bytes.val[19]!)).set 13#usize (r1of bytes.val[19]! bytes.val[20]!)).set 14#usize (r0of bytes.val[21]! bytes.val[22]!)).set 15#usize (r1of bytes.val[22]! bytes.val[23]!)) }, ?_, ?_⟩
  · unfold libcrux_iot_ml_kem.vector.portable.serialize.deserialize_12
    rw [he0]; simp only [Aeneas.Std.bind_tc_ok]
    rw [bind_ok_pair hd0]
    rw [array_update16 _ _ _ (by scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
    rw [array_update16 _ _ _ (by scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
    rw [he1]; simp only [Aeneas.Std.bind_tc_ok]
    rw [bind_ok_pair hd1]
    rw [array_update16 _ _ _ (by scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
    rw [array_update16 _ _ _ (by scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
    rw [he2]; simp only [Aeneas.Std.bind_tc_ok]
    rw [bind_ok_pair hd2]
    rw [array_update16 _ _ _ (by scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
    rw [array_update16 _ _ _ (by scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
    rw [he3]; simp only [Aeneas.Std.bind_tc_ok]
    rw [bind_ok_pair hd3]
    rw [array_update16 _ _ _ (by scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
    rw [array_update16 _ _ _ (by scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
    rw [he4]; simp only [Aeneas.Std.bind_tc_ok]
    rw [bind_ok_pair hd4]
    rw [array_update16 _ _ _ (by scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
    rw [array_update16 _ _ _ (by scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
    rw [he5]; simp only [Aeneas.Std.bind_tc_ok]
    rw [bind_ok_pair hd5]
    rw [array_update16 _ _ _ (by scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
    rw [array_update16 _ _ _ (by scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
    rw [he6]; simp only [Aeneas.Std.bind_tc_ok]
    rw [bind_ok_pair hd6]
    rw [array_update16 _ _ _ (by scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
    rw [array_update16 _ _ _ (by scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
    rw [he7]; simp only [Aeneas.Std.bind_tc_ok]
    rw [bind_ok_pair hd7]
    rw [array_update16 _ _ _ (by scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
    rw [array_update16 _ _ _ (by scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  · intro k hk
    show (((((((((((((((((out.elements.set 0#usize (r0of bytes.val[0]! bytes.val[1]!)).set 1#usize (r1of bytes.val[1]! bytes.val[2]!)).set 2#usize (r0of bytes.val[3]! bytes.val[4]!)).set 3#usize (r1of bytes.val[4]! bytes.val[5]!)).set 4#usize (r0of bytes.val[6]! bytes.val[7]!)).set 5#usize (r1of bytes.val[7]! bytes.val[8]!)).set 6#usize (r0of bytes.val[9]! bytes.val[10]!)).set 7#usize (r1of bytes.val[10]! bytes.val[11]!)).set 8#usize (r0of bytes.val[12]! bytes.val[13]!)).set 9#usize (r1of bytes.val[13]! bytes.val[14]!)).set 10#usize (r0of bytes.val[15]! bytes.val[16]!)).set 11#usize (r1of bytes.val[16]! bytes.val[17]!)).set 12#usize (r0of bytes.val[18]! bytes.val[19]!)).set 13#usize (r1of bytes.val[19]! bytes.val[20]!)).set 14#usize (r0of bytes.val[21]! bytes.val[22]!)).set 15#usize (r1of bytes.val[22]! bytes.val[23]!)).val)[k]! = _
    rw [set16_get]
    · interval_cases k <;> rfl
    · exact hk

/-! ### Impl side — the 16-chunk `chunks_exact` loop -/

open libcrux_iot_ml_kem.Matrix.ComputeRingElementV.Impl in
private theorem triple_of_ok_fc {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    (⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) := by
  subst hx; simp [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PostCond.noThrow,
    Std.Do.PredTrans.apply, hp]

/-- Re-indexing: `dec12` of a 24-byte chunk at offset `24*i` of `l`. -/
private theorem dec12_chunk (l c : List Std.U8) (i ℓ : Nat) (hℓ : ℓ < 16)
    (hc : ∀ m : Nat, m < 24 → c[m]! = l[24 * i + m]!) :
    dec12 c ℓ = dec12 l (16 * i + ℓ) := by
  unfold dec12
  have hpar : (16 * i + ℓ) % 2 = ℓ % 2 := by omega
  have hdiv : (16 * i + ℓ) / 2 = 8 * i + ℓ / 2 := by omega
  have hq : ℓ / 2 < 8 := by omega
  rw [hpar, hdiv]
  have e0 : 3 * (8 * i + ℓ / 2) = 24 * i + 3 * (ℓ / 2) := by ring
  have e1 : 3 * (8 * i + ℓ / 2) + 1 = 24 * i + (3 * (ℓ / 2) + 1) := by omega
  have e2 : 3 * (8 * i + ℓ / 2) + 2 = 24 * i + (3 * (ℓ / 2) + 2) := by omega
  split
  · rw [hc (3 * (ℓ / 2)) (by omega), hc (3 * (ℓ / 2) + 1) (by omega)]
    congr 3 <;> omega
  · rw [hc (3 * (ℓ / 2) + 1) (by omega), hc (3 * (ℓ / 2) + 2) (by omega)]
    congr 3 <;> omega

/-- Loop invariant: the first `k` chunks of `re` carry the decoded lanes. -/
private def declane (l : List Std.U8)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (k : Nat) : Prop :=
  ∀ i : Nat, i < k → ∀ ℓ : Nat, ℓ < 16 →
    ((re.coefficients.val[i]!).elements.val[ℓ]!).val = (dec12 l (16 * i + ℓ) : Int)

private theorem array_index_mut16 {α : Type} (A : Std.Array α 16#usize) (i : Std.Usize)
    (h : i.val < A.val.length) :
    Aeneas.Std.Array.index_mut_usize A i = .ok (A.val[i.val]'h, Std.Array.set A i) := by
  simp only [Aeneas.Std.Array.index_mut_usize, Aeneas.Std.Array.index_usize,
    Aeneas.Std.Array.getElem?_Usize_eq, List.getElem?_eq_getElem h, bind_tc_ok]

private theorem array_set_get16 {α : Type} [Inhabited α]
    (A : Std.Array α 16#usize) (i : Std.Usize) (x : α) (k : Nat) (hk : k < 16) (hi : i.val < 16) :
    ((Std.Array.set A i x).val)[k]! = if k = i.val then x else A.val[k]! := by
  have hlen : A.val.length = 16 := by have := A.property; simpa using this
  simp only [Std.Array.set_val_eq]
  by_cases h : k = i.val
  · subst h; rw [if_pos rfl, getElem!_pos _ _ (by simp [hlen]; omega)]
    simp [List.getElem_set_self]
  · rw [if_neg h, getElem!_pos _ _ (by simp [hlen]; omega),
      getElem!_pos _ _ (by omega), List.getElem_set_ne (by omega)]

private theorem triple_exists_ok_fc {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) : ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl, (by subst hx; simpa [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PostCond.noThrow, Std.Do.PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PostCond.noThrow, Std.Do.PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PostCond.noThrow, Std.Do.PredTrans.apply])

private theorem holds_ok (P : Prop) : (Aeneas.Std.Result.ok P).holds ↔ P := by
  constructor
  · intro h
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp, Std.Do.PostCond.noThrow,
      Std.Do.PredTrans.apply] using h
  · intro h
    simp [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp, Std.Do.PostCond.noThrow,
      Std.Do.PredTrans.apply, h]

open libcrux_iot_ml_kem.Matrix.ComputeRingElementV.Impl in
/-- The 16-iteration `chunks_exact 24` loop decodes every lane. -/
private theorem deserialize_uncompressed_loop_fc
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 384)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_to_uncompressed_ring_element_loop
      (vectortraitsOperationsInst := portable_ops_inst)
      { iter := { cs := 24#usize, elements := serialized }, count := 0#usize } re
    ⦃ ⇓ p => ⌜ (Aeneas.Std.Result.ok (declane serialized.val p 16)).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.deserialize_to_uncompressed_ring_element_loop
  refine loop_chunks_exact_pk_spec _ re serialized 24#usize 16
    (fun k acc => .ok (declane serialized.val acc k)) (by scalar_tac)
    (by simpa [Aeneas.Std.Slice.length] using h_len)
    ((holds_ok _).mpr (by intro i hi; omega)) ?_
  intro acc k rest cnt hk hcnt hrest hsuf hinv
  have hinv' : declane serialized.val acc k := (holds_ok _).mp hinv
  have h24 : ((24#usize : Std.Usize).val) = 24 := by scalar_tac
  rw [h24] at hrest
  simp only [h24] at hsuf
  by_cases hlt : k < 16
  · -- a full chunk remains
    have hrest24 : 24 ≤ rest.length := by
      rw [hrest]
      have h1 : 1 ≤ 16 - k := by omega
      calc (24:Nat) = 1 * 24 := by ring
      _ ≤ (16 - k) * 24 := Nat.mul_le_mul_right 24 h1
    obtain ⟨chunk, drop, cnt', hnext, hcnt', hclen, hdlen, hcget, hdget⟩ :=
      enumerate_chunks_next_cont_drop rest 24#usize cnt
        (by rw [h24]; simpa [Aeneas.Std.Slice.length] using hrest24) (by scalar_tac)
    have hcnt16 : cnt.val < 16 := by omega
    have hcoeff_len : cnt.val < acc.coefficients.val.length := by
      have hc : acc.coefficients.val.length = 16 := by
        have := acc.coefficients.property; simpa using this
      omega
    have hchunk_len : chunk.val.length = 24 := by
      simpa [Aeneas.Std.Slice.length] using hclen
    obtain ⟨v, hv_eq, hv⟩ :=
      deserialize_12_eq chunk (acc.coefficients.val[cnt.val]'hcoeff_len) hchunk_len
    -- the chunk sits at byte offset `24*k` of `serialized`
    have hcser : ∀ m : Nat, m < 24 → chunk.val[m]! = serialized.val[24 * k + m]! := by
      intro m hm
      rw [hcget m (by rw [h24]; omega), hsuf m]
      congr 1; omega
    refine triple_of_ok_fc
      (v := .cont ({ iter := { cs := 24#usize, elements := drop }, count := cnt' },
                   { coefficients := Std.Array.set acc.coefficients cnt v })) ?_ ?_
    · show libcrux_iot_ml_kem.serialize.deserialize_to_uncompressed_ring_element_loop.body
        portable_ops_inst { iter := { cs := 24#usize, elements := rest }, count := cnt } acc = _
      unfold libcrux_iot_ml_kem.serialize.deserialize_to_uncompressed_ring_element_loop.body
      rw [show (CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
            (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice Std.U8)
            { iter := { cs := 24#usize, elements := rest }, count := cnt })
          = .ok (CoreModels.core.option.Option.Some (cnt, chunk),
                 { iter := { cs := 24#usize, elements := drop }, count := cnt' }) from hnext]
      simp only [Aeneas.Std.bind_tc_ok]
      show (do
          let (t, index_mut_back) ← Aeneas.Std.Array.index_mut_usize acc.coefficients cnt
          let t1 ← portable_ops_inst.deserialize_12 chunk t
          Result.ok (ControlFlow.cont
            (({ iter := { cs := 24#usize, elements := drop }, count := cnt' } : EnumCE),
             ({ coefficients := index_mut_back t1 } :
               libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                 libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)))) = _
      rw [array_index_mut16 acc.coefficients cnt hcoeff_len]
      simp only [Aeneas.Std.bind_tc_ok]
      show (do
          let t1 ← libcrux_iot_ml_kem.vector.portable.serialize.deserialize_12 chunk
              (acc.coefficients.val[cnt.val]'hcoeff_len)
          Result.ok (ControlFlow.cont
            (({ iter := { cs := 24#usize, elements := drop }, count := cnt' } : EnumCE),
             ({ coefficients := Std.Array.set acc.coefficients cnt t1 } :
               libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                 libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)))) = _
      rw [hv_eq]
      rfl
    · refine ⟨hlt, rfl, (by show cnt'.val = k + 1; rw [hcnt', hcnt]), ?_, ?_, ?_⟩
      · show drop.length = (16 - (k + 1)) * (24#usize : Std.Usize).val
        rw [h24, hdlen, hrest]
        have : (16 - k) = (16 - (k + 1)) + 1 := by omega
        rw [this]; ring_nf; omega
      · intro ℓ
        simp only [h24]
        rw [hdget ℓ]
        simp only [h24]
        rw [hsuf (24 + ℓ)]
        congr 1 <;> omega
      · refine (holds_ok _).mpr ?_
        show declane serialized.val { coefficients := Std.Array.set acc.coefficients cnt v } (k + 1)
        intro i hi ℓ hℓ
        show ((Std.Array.set acc.coefficients cnt v).val[i]!).elements.val[ℓ]!.val = _
        by_cases hik : i = k
        · subst hik
          rw [array_set_get16 _ _ _ _ (by omega) (by omega), if_pos (by omega)]
          rw [hv ℓ hℓ, lane12_val, dec12_chunk serialized.val chunk.val i ℓ hℓ hcser]
        · rw [array_set_get16 _ _ _ _ (by omega) (by omega), if_neg (by omega)]
          exact hinv' i (by omega) ℓ hℓ
  · -- no full chunk remains: k = 16, the loop is done
    have hk16 : k = 16 := by omega
    subst hk16
    have hrest0 : rest.length = 0 := by simp [hrest]
    refine triple_of_ok_fc (v := .done acc) ?_ ?_
    · show libcrux_iot_ml_kem.serialize.deserialize_to_uncompressed_ring_element_loop.body
        portable_ops_inst { iter := { cs := 24#usize, elements := rest }, count := cnt } acc = _
      unfold libcrux_iot_ml_kem.serialize.deserialize_to_uncompressed_ring_element_loop.body
      rw [show (CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
            (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice Std.U8)
            { iter := { cs := 24#usize, elements := rest }, count := cnt })
          = .ok (CoreModels.core.option.Option.None,
                 { iter := { cs := 24#usize, elements := rest }, count := cnt }) from
          enumerate_chunks_next_done rest 24#usize cnt (by rw [h24, hrest0]; omega)]
      rfl
    · exact (holds_ok _).mpr hinv'

open libcrux_iot_ml_kem.Matrix.ComputeRingElementV.Impl in
/-- **Impl-side apex**: `deserialize_to_uncompressed_ring_element` decodes every
    one of the 256 lanes to `dec12` of the input bytes. -/
private theorem deserialize_uncompressed_impl_fc
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 384)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_to_uncompressed_ring_element
      (vectortraitsOperationsInst := portable_ops_inst) serialized re
    ⦃ ⇓ p => ⌜ (Aeneas.Std.Result.ok (declane serialized.val p 16)).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.deserialize_to_uncompressed_ring_element
  rw [show (CoreModels.core.slice.Slice.chunks_exact serialized (24#usize : Std.Usize))
        = .ok { cs := 24#usize, elements := serialized } from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show (CoreModels.core.iter.traits.iterator.Iterator.enumerate.default
        (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice
          Std.U8)
        { cs := (24#usize : Std.Usize), elements := serialized })
      = .ok ({ iter := { cs := 24#usize, elements := serialized }, count := 0#usize } : EnumCE)
      from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  exact deserialize_uncompressed_loop_fc serialized h_len re

/-! ### Spec side — `bytes_to_bits` closed form

    The hacspec model expands the 384 bytes into 3072 booleans through a
    `createi`; the pure normal form of the closure is exactly `sliceBit`. -/

private theorem u8_val_eq_one_iff (w : Std.U8) : (w = 1#u8) ↔ (w.val = 1) := by
  constructor
  · intro h; rw [h]; rfl
  · intro h; apply Std.UScalar.eq_of_val_eq; rw [h]; rfl

private theorem shr_and1_eq (x : Std.U8) (sh : Std.Usize) (hsh : sh.val < 8) :
    ∃ y : Std.U8, (x >>> sh) = .ok y
      ∧ decide ((y &&& 1#u8) = 1#u8) = natBit x.val sh.val := by
  obtain ⟨y, hy_eq, hy_val, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.ShiftRight_spec (ty0 := .U8) x sh (by simpa using hsh))
  refine ⟨y, hy_eq, ?_⟩
  have hand : (y &&& 1#u8).val = y.val % 2 := by
    rw [Std.UScalar.val_and]
    have h1 : ((1#u8 : Std.U8).val) = 1 := rfl
    rw [h1]
    have h2 := Nat.and_two_pow_sub_one_eq_mod y.val 1
    rw [show (2:Nat) ^ 1 - 1 = 1 from rfl, show (2:Nat) ^ 1 = 2 from rfl] at h2
    exact h2
  have hyv : y.val = x.val / 2 ^ sh.val := by
    rw [hy_val, Nat.shiftRight_eq_div_pow]
  simp only [natBit, u8_val_eq_one_iff, hand, hyv]

/-- Pure normal form of the `bytes_to_bits` closure. -/
private theorem bytes_to_bits_closure_eq (a : Std.Array Std.U8 384#usize) (k : Nat)
    (hk : k < 3072) :
    (hacspec_ml_kem.serialize.bytes_to_bits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBool
        384#usize 3072#usize).call_mut a ⟨BitVec.ofNat _ k⟩
      = .ok (sliceBit a.val k, a) := by
  have hkv : ((⟨BitVec.ofNat _ k⟩ : Std.Usize)).val = k := by
    show (BitVec.ofNat _ k).toNat = k
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by scalar_tac)
  obtain ⟨q, hq_eq, hq_val⟩ :=
    Std.UScalar.div_spec (⟨BitVec.ofNat _ k⟩ : Std.Usize)
      (y := (8#usize : Std.Usize)) (by decide)
  obtain ⟨r, hr_eq, hr_val⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.rem_spec (⟨BitVec.ofNat _ k⟩ : Std.Usize)
      (y := (8#usize : Std.Usize)) (by decide))
  have h8 : ((8#usize : Std.Usize).val) = 8 := by scalar_tac
  have hq16 : q.val = k / 8 := by rw [hq_val, hkv, h8]
  have hr8 : r.val = k % 8 := by rw [hr_val, hkv, h8]
  have hqlt : q.val < a.val.length := by
    have ha : a.val.length = 384 := by have := a.property; simpa using this
    rw [ha, hq16]; omega
  have hidx : Aeneas.Std.Array.index_usize a q = .ok (a.val[q.val]!) := by
    simp only [Aeneas.Std.Array.index_usize, Aeneas.Std.Array.getElem?_Usize_eq,
      List.getElem?_eq_getElem hqlt]
    rw [getElem!_pos a.val q.val hqlt]
  obtain ⟨y, hy_eq, hy⟩ := shr_and1_eq (a.val[q.val]!) r (by omega)
  show (do
      let i ← (⟨BitVec.ofNat _ k⟩ : Std.Usize) / 8#usize
      let i1 ← Aeneas.Std.Array.index_usize a i
      let i2 ← (⟨BitVec.ofNat _ k⟩ : Std.Usize) % 8#usize
      let i3 ← i1 >>> i2
      let i4 ← Aeneas.Std.lift (i3 &&& 1#u8)
      Result.ok (decide (i4 = 1#u8), a)) = _
  rw [hq_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hidx]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hy_eq]; simp only [Aeneas.Std.bind_tc_ok]
  show Result.ok (decide (y &&& 1#u8 = 1#u8), a) = _
  rw [hy]
  unfold sliceBit
  rw [hq16, hr8]

private theorem usize_mul_lit (x y z : Std.Usize) (h : x.val * y.val = z.val)
    (hb : x.val * y.val ≤ Std.Usize.max) :
    (x * y : Aeneas.Std.Result Std.Usize) = .ok z := by
  obtain ⟨m, hm_eq, hm_v⟩ := Std.WP.spec_imp_exists
    (Std.WP.spec_of_partialSpec (@Std.Usize.mul_spec x y)
      (fun e => by cases e <;> scalar_tac) (by simp))
  have hm : m = z := by
    apply Aeneas.Std.UScalar.eq_of_val_eq
    rw [hm_v, h]
  rw [hm_eq, hm]

/-- **Spec-side bit expansion**: the 3072 booleans are exactly `sliceBit`. -/
private theorem bytes_to_bits_get (a : Std.Array Std.U8 384#usize) :
    ∃ bv : Std.Array Bool 3072#usize,
      hacspec_ml_kem.serialize.bytes_to_bits (N := 384#usize) 3072#usize a = .ok bv
      ∧ ∀ m : Nat, m < 3072 → bv.val[m]! = sliceBit a.val m := by
  have hmul : ((384#usize : Std.Usize) * (8#usize : Std.Usize) : Aeneas.Std.Result Std.Usize)
      = .ok (3072#usize : Std.Usize) :=
    usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have h3072 : ((3072#usize : Std.Usize)).val = 3072 := by scalar_tac
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq (T := Bool)
      (3072#usize : Std.Usize)
      (hacspec_ml_kem.serialize.bytes_to_bits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBool
        384#usize 3072#usize) a (fun m => sliceBit a.val m)
      (fun k hk => bytes_to_bits_closure_eq a k (by rw [h3072] at hk; exact hk))
  have key : hacspec_ml_kem.serialize.bytes_to_bits (N := 384#usize) 3072#usize a
      = CoreModels.core.array.from_fn (3072#usize : Std.Usize)
          (hacspec_ml_kem.serialize.bytes_to_bits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBool
            384#usize 3072#usize) a := by
    unfold hacspec_ml_kem.serialize.bytes_to_bits
    rw [hmul]
    simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.massert,
      hacspec_ml_kem.parameters.createi, if_true, Aeneas.Std.bind_tc_ok]
  rw [key, hfn]
  refine ⟨_, rfl, ?_⟩
  intro m hm
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by rw [h3072]; exact hm)]
  rfl


end L57Bank

/-! ## Message (de)serialization — `d = 1`, exact 1:1 with the hacspec model. -/

/-- L5.1 — `serialize.deserialize_then_decompress_message`.

    FIPS-203 message decode: 32 bytes → 256 coefficients, each bit `b` mapped to
    `Decompress_1(b)`. The hacspec counterpart takes the same fixed-size 32-byte
    array and returns the ring element directly, so the binding is exact: no
    length side conditions, no chunk indexing. -/
@[spec]
theorem deserialize_then_decompress_message_fc
    (serialized : Std.Array Std.U8 32#usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_message
      (vectortraitsOperationsInst := portable_ops_inst)
      serialized re
    ⦃ ⇓ p => ⌜ hacspec_ml_kem.serialize.deserialize_then_decompress_message serialized
                = .ok (lift_poly p) ⌝ ⦄ := by
  sorry

/-- L5.2 — `serialize.compress_then_serialize_message`.

    The encode direction of L5.1: `Compress_1` each coefficient, pack 256 bits
    into 32 bytes. The impl writes into a caller-provided `serialized` slice and
    threads a `scratch` vector, returning both; the hacspec returns a fresh
    32-byte array. The post therefore constrains the RETURNED slice `p.1`, and
    requires it to have message length. `scratch` is workspace and is
    deliberately unconstrained. -/
@[spec]
theorem compress_then_serialize_message_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (serialized : Slice Std.U8)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_len : serialized.length = 32) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.compress_then_serialize_message
      (vectortraitsOperationsInst := portable_ops_inst)
      re serialized scratch
    ⦃ ⇓ p => ⌜ ∃ out : Std.Array Std.U8 32#usize,
                  hacspec_ml_kem.serialize.compress_then_serialize_message (lift_poly re)
                    = .ok out
                  ∧ p.1.length = 32
                  ∧ ∀ ℓ : Nat, ℓ < 32 → p.1.val[ℓ]! = out.val[ℓ]! ⌝ ⦄ := by
  sorry

/-! ## Ciphertext component `v` — `d = dv`, exact 1:1 with the hacspec model. -/

/-- L5.3 — `serialize.deserialize_then_decompress_ring_element_v`.

    `ByteDecode_dv` then `Decompress_dv` over one ring element. The hacspec
    counterpart takes the same `(serialized, dv)` pair and returns the ring
    element, so the binding is exact. The impl's `K` is a rank parameter that does
    not appear in the spec side. -/
@[spec]
theorem deserialize_then_decompress_ring_element_v_fc
    (K V_COMPRESSION_FACTOR : Std.Usize)
    (serialized : Slice Std.U8)
    (output : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_v
      (vectortraitsOperationsInst := portable_ops_inst)
      K V_COMPRESSION_FACTOR serialized output
    ⦃ ⇓ p => ⌜ hacspec_ml_kem.serialize.deserialize_then_decompress_v
                  serialized V_COMPRESSION_FACTOR
                = .ok (lift_poly p) ⌝ ⦄ := by
  sorry

/-- L5.4 — `serialize.compress_then_serialize_ring_element_v`.

    The encode direction of L5.3: `Compress_dv` then `ByteEncode_dv`. The impl
    writes into the caller's `out` slice and threads `scratch`; the hacspec
    returns a fresh `Array U8 C2_LEN`. The post therefore compares the returned
    slice bytewise against the spec array, exactly as L5.2 does for the message.
    `V_SIZE` on the spec side is the impl's `C2_LEN`. -/
@[spec]
theorem compress_then_serialize_ring_element_v_fc
    (K V_COMPRESSION_FACTOR C2_LEN : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_len : out.length = C2_LEN.val) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_v
      (vectortraitsOperationsInst := portable_ops_inst)
      K V_COMPRESSION_FACTOR C2_LEN re out scratch
    ⦃ ⇓ p => ⌜ ∃ enc : Std.Array Std.U8 C2_LEN,
                  hacspec_ml_kem.serialize.compress_then_serialize_v
                      C2_LEN (lift_poly re) V_COMPRESSION_FACTOR
                    = .ok enc
                  ∧ p.1.length = C2_LEN.val
                  ∧ ∀ ℓ : Nat, ℓ < C2_LEN.val → p.1.val[ℓ]! = enc.val[ℓ]! ⌝ ⦄ := by
  sorry

/-! ## Public-key deserialization — exact 1:1 with the hacspec model. -/

/-- L5.5 — `serialize.deserialize_ring_elements_reduced`.

    Rank-K public-key decode: K consecutive 384-byte chunks, each `ByteDecode_12`
    then reduced to canonical residues. This is the vector-level apex that
    assembles `Serialize.deserialize_to_reduced_ring_element_fc` (currently the A2
    axiom) K times. The impl threads a caller-provided `deserialized_pk` slice and
    returns it; the spec returns a fresh rank-K array, so the impl result is
    compared through `lift_vec_slice`. -/
@[spec]
theorem deserialize_ring_elements_reduced_fc
    (K : Std.Usize)
    (public_key : Slice Std.U8)
    (deserialized_pk : Slice
        (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (h_pk_len : public_key.length = K.val * 384)
    (h_out_len : deserialized_pk.length = K.val) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_ring_elements_reduced
      (vectortraitsOperationsInst := portable_ops_inst)
      K public_key deserialized_pk
    ⦃ ⇓ p => ⌜ p.length = K.val
                ∧ hacspec_ml_kem.serialize.deserialize_ring_elements_reduced K public_key
                  = .ok (lift_vec_slice p K) ⌝ ⦄ := by
  sorry

/-! ## Uncompressed ring elements — `d = 12`, no compression step.

    `BITS_PER_COEFFICIENT = 12`, so these are plain `ByteEncode_12` / `ByteDecode_12`
    with no `Compress`/`Decompress` in the chain. The slice-shaped hacspec variants
    (`byte_encode_into`, `byte_decode_dyn`) match the impl's slice plumbing directly,
    so no container conversion is needed. -/

/-- L5.6 — `serialize.serialize_uncompressed_ring_element` (= `ByteEncode_12`).

    The impl returns `(scratch', serialized')`; the byte content of interest is
    `p.2`, which `byte_encode_into` produces from the same `out` slice. -/
@[spec]
theorem serialize_uncompressed_ring_element_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (serialized : Slice Std.U8)
    (h_len : serialized.length = 384) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.serialize_uncompressed_ring_element
      (vectortraitsOperationsInst := portable_ops_inst)
      re scratch serialized
    ⦃ ⇓ p => ⌜ hacspec_ml_kem.serialize.byte_encode_into (lift_poly re) 12#usize serialized
                = .ok p.2 ⌝ ⦄ := by
  sorry

/-! ## PROVER bank for L5.7, part 2 — the SPEC-side decode chain.

    Ported from `Hacspec_ml_kem.Commute.Serialize_bits.fst`: the ladder
    `lemma_bytes_to_bits_index` → `lemma_coeff_bit` → `lemma_coeff_value` →
    `lemma_recon_step`/`lemma_recon_combine` → `lemma_bitvec_to_bounded_index_12`
    → `lemma_byte_decode_index_12` → `lemma_deserialize_coeff_eq_byte_decode_12`.

    Architectural note (copied from F*): `Serialize_bits.fst` keeps its per-chunk
    bit equality behind the `[@@ "opaque_to_smt"]` atom `chunk_decoded_12` so the
    bit-vector equality never enters the composer's loop-body VC. The Lean
    analogue here is the named `dec12` atom of part 1 together with the
    `bitSum_sliceBit_eq_dec12` keystone: below, the accumulator loop is stated
    purely in terms of `bitSum`, and `dec12` is only introduced once, at the
    apex. No raw `|||`/`testBit` reasoning appears in any loop residue. -/

section L57Bank2

open Aeneas.Std
open libcrux_iot_ml_kem.Util.LoopSpecs

/-! ### Generic scalar / array / iterator plumbing.

    `Vector/Portable/Arithmetic/LoopHelper.lean` has the same iterator lemmas but
    pinned to the bound `16`; the spec-side bit loop runs to `d = 12`, so the
    generic-bound versions are re-derived here from
    `LoopSpecs.IteratorRange_next_spec_usize`. -/

private theorem usize_mul_ok (x y : Std.Usize) (hb : x.val * y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x * y : Result Std.Usize) = .ok z ∧ z.val = x.val * y.val := by
  obtain ⟨z, hz, hv, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.mul_bv_spec (x := x) (y := y) (by scalar_tac))
  exact ⟨z, hz, hv⟩

private theorem usize_add_ok (x y : Std.Usize) (hb : x.val + y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x + y : Result Std.Usize) = .ok z ∧ z.val = x.val + y.val := by
  obtain ⟨z, hz, hv, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.add_bv_spec (x := x) (y := y) (by scalar_tac))
  exact ⟨z, hz, hv⟩

private theorem u16_add_ok (x y : Std.U16) (hb : x.val + y.val ≤ 65535) :
    ∃ z : Std.U16, (x + y : Result Std.U16) = .ok z ∧ z.val = x.val + y.val := by
  obtain ⟨z, hz, hv, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.add_bv_spec (x := x) (y := y) (by scalar_tac))
  exact ⟨z, hz, hv⟩

/-- `1u16 << n` for `n < 16`: the shift result stays SYMBOLIC as `2 ^ n.val`
    (the closed-large-scalar pitfall — never `decide` on `1 <<< k`). -/
private theorem u16_shl_one_ok (n : Std.Usize) (hn : n.val < 16) :
    ∃ z : Std.U16, ((1#u16 : Std.U16) <<< n : Result Std.U16) = .ok z
      ∧ z.val = 2 ^ n.val := by
  obtain ⟨z, hz, hv, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.ShiftLeft_spec (ty0 := .U16) (1#u16) n
      (Std.UScalar.size .U16) (by simpa using hn) rfl)
  refine ⟨z, hz, ?_⟩
  have h1 : ((1#u16 : Std.U16).val) = 1 := rfl
  have hsize : Std.UScalar.size .U16 = 65536 := by
    rw [Std.UScalar.size_def]; norm_num [Std.UScalarTy.numBits]
  have hlt : (2:Nat) ^ n.val < 65536 := by
    have : (2:Nat) ^ n.val ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
    have h15 : (2:Nat) ^ 15 = 32768 := by norm_num
    omega
  rw [hv, h1, hsize, Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt hlt]

private theorem u16_rem_ok (x y : Std.U16) (hy : 0 < y.val) :
    ∃ z : Std.U16, (x % y : Result Std.U16) = .ok z ∧ z.val = x.val % y.val := by
  obtain ⟨z, hz, hv⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.rem_spec (ty := .U16) x (y := y) (by omega))
  exact ⟨z, hz, hv⟩

private theorem array_index_ok {α : Type} [Inhabited α] {N : Std.Usize}
    (a : Std.Array α N) (i : Std.Usize) (h : i.val < a.val.length) :
    Aeneas.Std.Array.index_usize a i = .ok (a.val[i.val]!) := by
  simp only [Aeneas.Std.Array.index_usize, Aeneas.Std.Array.getElem?_Usize_eq,
    List.getElem?_eq_getElem h]
  rw [getElem!_pos a.val i.val h]

/-- Generic-bound analogue of `LoopHelper.iter_next_some_eq`. -/
private theorem iter_some_gen (i e : Std.Usize) (h_lt : i.val < e.val) :
    ∃ s : Std.Usize, s.val = i.val + 1 ∧
      CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
          CoreModels.core.Usize.Insts.CoreIterRangeStep
          ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)
        = .ok (some i,
            ({ start := s, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)) := by
  have hT := IteratorRange_next_spec_usize i e
    (Q := Std.Do.PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
      ∃ s : Std.Usize, s.val = i.val + 1
        ∧ oi = (some i,
            ({ start := s, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)) ⌝)
    (fun _ s hs => by
      dsimp only [Std.Do.PostCond.noThrow, Std.Do.SPred.down_pure]
      exact ⟨s, hs, rfl⟩)
    (fun hge => absurd h_lt (Nat.not_lt.mpr hge))
  obtain ⟨v, hveq, s, hs, hpair⟩ := triple_exists_ok_fc hT
  refine ⟨s, hs, ?_⟩
  show CoreModels.core.iter.range.IteratorRange.next
      CoreModels.core.Usize.Insts.CoreIterRangeStep
      ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize) = _
  rw [hveq, hpair]

/-- Generic-bound analogue of `LoopHelper.iter_next_none_eq`. -/
private theorem iter_none_gen (i e : Std.Usize) (h_ge : e.val ≤ i.val) :
    CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
        CoreModels.core.Usize.Insts.CoreIterRangeStep
        ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)
      = .ok ((none : Option Std.Usize),
          ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)) := by
  have hT := IteratorRange_next_spec_usize i e
    (Q := Std.Do.PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
      oi = ((none : Option Std.Usize),
        ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)) ⌝)
    (fun hlt => absurd hlt (Nat.not_lt.mpr h_ge))
    (fun _ => by dsimp only [Std.Do.PostCond.noThrow, Std.Do.SPred.down_pure])
  obtain ⟨v, hveq, hP⟩ := triple_exists_ok_fc hT
  show CoreModels.core.iter.range.IteratorRange.next
      CoreModels.core.Usize.Insts.CoreIterRangeStep
      ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize) = _
  rw [hveq, hP]

/-! ### The `d`-step bit-accumulation loop of `bitvector_to_bounded_ints`.

    Port of F* `dec_inv` / `dec_step` (`Commute.Serialize_bits.fst`): the loop
    invariant is exactly "the accumulator equals the partial bit sum", which is
    `bitSum` here. The residue never sees a bit-vector equality — `dec12` enters
    only at the apex, through `bitSum_sliceBit_eq_dec12`. -/

private theorem bvb_loop_fc {Nd : Std.Usize} (a : Std.Array Bool Nd) (d j : Std.Usize)
    (hd : d.val ≤ 16)
    (hmul : j.val * d.val + d.val ≤ Std.Usize.max)
    (hbd : j.val * d.val + d.val ≤ Nd.val) :
    ⦃ ⌜ True ⌝ ⦄
    hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16.call_mut_loop
      (Nd := Nd) { start := 0#usize, «end» := d } d a j 0#u16
    ⦃ ⇓ c => ⌜ c.val = bitSum (fun t => a.val[j.val * d.val + t]!) d.val ⌝ ⦄ := by
  have halen : a.val.length = Nd.val := a.property
  unfold
    hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16.call_mut_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, c1) =>
        hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16.call_mut_loop.body
          (Nd := Nd) d a j iter1 c1)
      (β := Std.U16) 0#u16 0#usize d
      (fun i c => .ok (c.val = bitSum (fun t => a.val[j.val * d.val + t]!) i.val))
      (by scalar_tac)
      ((holds_ok _).mpr (by
        show (0#u16 : Std.U16).val = bitSum (fun t => a.val[j.val * d.val + t]!) 0
        simp [bitSum]))
      ?_)
  · rw [Std.Do.PostCond.entails_noThrow]
    intro r h
    exact (holds_ok _).mp h
  · intro acc i hge hle hinv
    have hinv' : acc.val = bitSum (fun t => a.val[j.val * d.val + t]!) i.val :=
      (holds_ok _).mp hinv
    by_cases hlt : i.val < d.val
    · obtain ⟨s, hs, hnext⟩ := iter_some_gen i d hlt
      obtain ⟨m, hm, hmv⟩ := usize_mul_ok j d (by omega)
      obtain ⟨q, hq, hqv⟩ := usize_add_ok m i (by omega)
      have hqval : q.val = j.val * d.val + i.val := by rw [hqv, hmv]
      have hqlt : q.val < a.val.length := by rw [halen, hqval]; omega
      have hidx : Aeneas.Std.Array.index_usize a q = .ok (a.val[q.val]!) :=
        array_index_ok a q hqlt
      have hbitsum : bitSum (fun t => a.val[j.val * d.val + t]!) (i.val + 1)
          = bitSum (fun t => a.val[j.val * d.val + t]!) i.val
            + (if a.val[q.val]! then 2 ^ i.val else 0) := by
        rw [bitSum, hqval]
      by_cases hb : a.val[q.val]! = true
      · obtain ⟨w, hw, hwv⟩ := u16_shl_one_ok i (by omega)
        have hlow : bitSum (fun t => a.val[j.val * d.val + t]!) i.val < 2 ^ i.val :=
          bitSum_lt _ _
        have hpow : (2:Nat) ^ i.val ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
        have h15 : (2:Nat) ^ 15 = 32768 := by norm_num
        obtain ⟨c2, hc2, hc2v⟩ := u16_add_ok acc w (by omega)
        refine triple_of_ok_fc
          (v := .cont (({ start := s, «end» := d } :
                          CoreModels.core.ops.range.Range Std.Usize), c2)) ?_ ?_
        · show
            hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16.call_mut_loop.body
              (Nd := Nd) d a j ({ start := i, «end» := d } :
                CoreModels.core.ops.range.Range Std.Usize) acc = _
          unfold
            hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16.call_mut_loop.body
          rw [hnext]
          show (do
              let i2 ← j * d
              let i3 ← i2 + i
              let b ← Aeneas.Std.Array.index_usize a i3
              if b = true then do
                  let i4 ← (1#u16 : Std.U16) <<< i
                  let coefficient1 ← acc + i4
                  Result.ok (ControlFlow.cont
                    ((⟨s, d⟩ : CoreModels.core.ops.range.Range Std.Usize), coefficient1))
                else Result.ok (ControlFlow.cont
                    ((⟨s, d⟩ : CoreModels.core.ops.range.Range Std.Usize), acc))) = _
          rw [hm]; simp only [Aeneas.Std.bind_tc_ok]
          rw [hq]; simp only [Aeneas.Std.bind_tc_ok]
          rw [hidx]; simp only [Aeneas.Std.bind_tc_ok, hb, if_true]
          rw [hw]; simp only [Aeneas.Std.bind_tc_ok]
          rw [hc2]; rfl
        · refine ⟨hlt, rfl, hs, (holds_ok _).mpr ?_⟩
          show c2.val = bitSum (fun t => a.val[j.val * d.val + t]!) s.val
          rw [hs, hbitsum, hc2v, hinv', hwv, if_pos hb]
      · have hbf : a.val[q.val]! = false := by
          cases h : a.val[q.val]! with
          | false => rfl
          | true => exact absurd h hb
        refine triple_of_ok_fc
          (v := .cont (({ start := s, «end» := d } :
                          CoreModels.core.ops.range.Range Std.Usize), acc)) ?_ ?_
        · show
            hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16.call_mut_loop.body
              (Nd := Nd) d a j ({ start := i, «end» := d } :
                CoreModels.core.ops.range.Range Std.Usize) acc = _
          unfold
            hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16.call_mut_loop.body
          rw [hnext]
          show (do
              let i2 ← j * d
              let i3 ← i2 + i
              let b ← Aeneas.Std.Array.index_usize a i3
              if b = true then do
                  let i4 ← (1#u16 : Std.U16) <<< i
                  let coefficient1 ← acc + i4
                  Result.ok (ControlFlow.cont
                    ((⟨s, d⟩ : CoreModels.core.ops.range.Range Std.Usize), coefficient1))
                else Result.ok (ControlFlow.cont
                    ((⟨s, d⟩ : CoreModels.core.ops.range.Range Std.Usize), acc))) = _
          rw [hm]; simp only [Aeneas.Std.bind_tc_ok]
          rw [hq]; simp only [Aeneas.Std.bind_tc_ok]
          rw [hidx]; simp only [Aeneas.Std.bind_tc_ok, hbf, Bool.false_eq_true, if_false]
        · refine ⟨hlt, rfl, hs, (holds_ok _).mpr ?_⟩
          show acc.val = bitSum (fun t => a.val[j.val * d.val + t]!) s.val
          rw [hs, hbitsum, hinv', hbf]
          simp
    · have hieq : i.val = d.val := by omega
      refine triple_of_ok_fc (v := .done acc) ?_ ?_
      · show
          hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16.call_mut_loop.body
            (Nd := Nd) d a j ({ start := i, «end» := d } :
              CoreModels.core.ops.range.Range Std.Usize) acc = _
        unfold
          hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16.call_mut_loop.body
        rw [iter_none_gen i d (by omega)]
        rfl
      · refine (holds_ok _).mpr ?_
        show acc.val = bitSum (fun t => a.val[j.val * d.val + t]!) d.val
        rw [hieq] at hinv'; exact hinv'

/-! ### `bitvector_to_bounded_ints` closed form.

    F* analogue: `lemma_bitvec_to_bounded_index_12` (`Serialize_bits.fst`). -/

/-- The `U16` carrying a `Nat` payload. Kept as a named `def` so the array
    element function below is a closed term (no inline computation). -/
private def u16OfNat (x : Nat) : Std.U16 := ⟨BitVec.ofNat _ x⟩

private theorem u16OfNat_val (x : Nat) (h : x < 65536) : (u16OfNat x).val = x := by
  show (BitVec.ofNat _ x).toNat = x
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by simpa [Std.UScalarTy.numBits] using h)

/-- Pure normal form of the `bitvector_to_bounded_ints` closure at index `k`. -/
private theorem bvb_closure_eq {N Nd : Std.Usize} (a : Std.Array Bool Nd)
    (d : Std.Usize) (k : Nat)
    (hd : d.val ≤ 16) (hk : k < 2 ^ 32)
    (hmul : k * d.val + d.val ≤ Std.Usize.max)
    (hbd : k * d.val + d.val ≤ Nd.val) :
    (hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16
        N Nd).call_mut (d, a) ⟨BitVec.ofNat _ k⟩
      = .ok (u16OfNat (bitSum (fun t => a.val[k * d.val + t]!) d.val), (d, a)) := by
  -- `LoopSpecs.bv_ofNat_val_eq` is `private` there, so the same two lines here.
  have hkv : ((⟨BitVec.ofNat _ k⟩ : Std.Usize)).val = k := by
    show (BitVec.ofNat _ k).toNat = k
    simp only [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have h32 : (32 : Nat) ≤ System.Platform.numBits := by
      have := System.Platform.numBits_eq; omega
    calc k < 2 ^ 32 := hk
      _ ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) h32
  obtain ⟨z, hz, hzv⟩ :=
    triple_exists_ok_fc (bvb_loop_fc a d ⟨BitVec.ofNat _ k⟩ hd
      (by rw [hkv]; exact hmul) (by rw [hkv]; exact hbd))
  have hzeq : z = u16OfNat (bitSum (fun t => a.val[k * d.val + t]!) d.val) := by
    refine Aeneas.Std.UScalar.eq_of_val_eq ?_
    have hlt : bitSum (fun t => a.val[k * d.val + t]!) d.val < 65536 := by
      have h1 := bitSum_lt (fun t => a.val[k * d.val + t]!) d.val
      have h2 : (2:Nat) ^ d.val ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) hd
      have h16 : (2:Nat) ^ 16 = 65536 := by norm_num
      omega
    rw [u16OfNat_val _ hlt, hzv, hkv]
  show (do
      let coefficient ←
        hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16.call_mut_loop
          (Nd := Nd) { start := 0#usize, «end» := d } d a ⟨BitVec.ofNat _ k⟩ 0#u16
      Result.ok (coefficient, ((d, a) : Std.Usize × Std.Array Bool Nd))) = _
  rw [hz]; simp only [Aeneas.Std.bind_tc_ok, hzeq]; rfl

/-- `bitvector_to_bounded_ints` at `N = 256`, `d = 12`, `Nd = 3072`: cell `k` is
    the 12-bit sum of bits `12k .. 12k+11`. -/
private theorem bvb_256_12_get (bv : Std.Array Bool 3072#usize) :
    ∃ arr : Std.Array Std.U16 256#usize,
      hacspec_ml_kem.serialize.bitvector_to_bounded_ints 256#usize bv 12#usize = .ok arr
      ∧ ∀ k : Nat, k < 256 →
          (arr.val[k]!).val = bitSum (fun t => bv.val[12 * k + t]!) 12 := by
  have h256 : ((256#usize : Std.Usize)).val = 256 := by scalar_tac
  have h12 : ((12#usize : Std.Usize)).val = 12 := by scalar_tac
  have h3072 : ((3072#usize : Std.Usize)).val = 3072 := by scalar_tac
  have hmul : ((256#usize : Std.Usize) * (12#usize : Std.Usize) : Result Std.Usize)
      = .ok (3072#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq (T := Std.U16)
      (256#usize : Std.Usize)
      (hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16
        256#usize 3072#usize)
      ((12#usize : Std.Usize), bv)
      (fun k => u16OfNat (bitSum (fun t => bv.val[k * 12 + t]!) 12))
      (fun k hk => by
        rw [h256] at hk
        have h32 : (2:Nat) ^ 32 = 4294967296 := by norm_num
        have := bvb_closure_eq (N := 256#usize) bv (12#usize) k
          (by rw [h12]; omega) (by omega) (by rw [h12]; scalar_tac)
          (by rw [h12, h3072]; omega)
        rw [h12] at this
        exact this)
  have key : hacspec_ml_kem.serialize.bitvector_to_bounded_ints 256#usize bv 12#usize
      = CoreModels.core.array.from_fn (256#usize : Std.Usize)
          (hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16
            256#usize 3072#usize)
          ((12#usize : Std.Usize), bv) := by
    unfold hacspec_ml_kem.serialize.bitvector_to_bounded_ints
    rw [hmul]
    simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.massert,
      hacspec_ml_kem.parameters.createi, if_true, Aeneas.Std.bind_tc_ok]
  rw [key, hfn]
  refine ⟨_, rfl, ?_⟩
  intro k hk
  have hget : ((List.range ((256#usize : Std.Usize)).val).map
      (fun k => u16OfNat (bitSum (fun t => bv.val[k * 12 + t]!) 12)))[k]!
      = u16OfNat (bitSum (fun t => bv.val[k * 12 + t]!) 12) := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by rw [h256]; exact hk)]
    rfl
  have hcomm : (fun t => bv.val[k * 12 + t]!) = (fun t => bv.val[12 * k + t]!) := by
    funext t; rw [Nat.mul_comm]
  show (((List.range ((256#usize : Std.Usize)).val).map
      (fun k => u16OfNat (bitSum (fun t => bv.val[k * 12 + t]!) 12)))[k]!).val = _
  rw [hget, hcomm]
  refine u16OfNat_val _ ?_
  have h1 := bitSum_lt (fun t => bv.val[12 * k + t]!) 12
  have h12' : (2:Nat) ^ 12 = 4096 := by norm_num
  omega

/-! ### `byte_decode_generic` and `byte_decode` at `d = 12`.

    F* analogue: `lemma_byte_decode_index_12` and the headline
    `lemma_deserialize_coeff_eq_byte_decode_12` (`Serialize_bits.fst`). -/

private theorem byte_decode_generic_12_get (a : Std.Array Std.U8 384#usize) :
    ∃ arr : Std.Array Std.U16 256#usize,
      hacspec_ml_kem.serialize.byte_decode_generic 32#usize 256#usize
          (Nd := 384#usize) 3072#usize a 12#usize = .ok arr
      ∧ ∀ k : Nat, k < 256 → (arr.val[k]!).val = dec12 a.val k := by
  obtain ⟨bv, hbv, hbvget⟩ := bytes_to_bits_get a
  obtain ⟨arr, harr, harrget⟩ := bvb_256_12_get bv
  have e1 : ((32#usize : Std.Usize) * (8#usize : Std.Usize) : Result Std.Usize)
      = .ok (256#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have e2 : ((32#usize : Std.Usize) * (12#usize : Std.Usize) : Result Std.Usize)
      = .ok (384#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have e3 : ((384#usize : Std.Usize) * (8#usize : Std.Usize) : Result Std.Usize)
      = .ok (3072#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  refine ⟨arr, ?_, ?_⟩
  · unfold hacspec_ml_kem.serialize.byte_decode_generic
    simp only [hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT, Aeneas.Std.massert,
      le_refl, if_true, Aeneas.Std.bind_tc_ok, e1, e2, e3, hbv, harr]
  · intro k hk
    rw [harrget k hk,
      bitSum_congr _ (fun t => sliceBit a.val (12 * k + t)) 12
        (fun t ht => hbvget (12 * k + t) (by omega))]
    exact bitSum_sliceBit_eq_dec12 a.val k

/-! ### The FE bridge: spec-side `FieldElement.new (x % q)` ↔ impl-side `lift_fe`. -/

private theorem lift_fe_of_nat (lane : Std.I16) (n : Nat) (h : lane.val = (n : Int)) :
    lift_fe lane = { val := u16OfNat (n % 3329) } := by
  unfold lift_fe libcrux_iot_ml_kem.Spec.feOfZMod
    libcrux_iot_ml_kem.Spec.i16_to_spec_fe_plain
  have hz : (((n : Int) : ZMod 3329)).val = n % 3329 := by
    rw [show (((n : Int)) : ZMod 3329) = ((n : Nat) : ZMod 3329) by push_cast; ring]
    simp [ZMod.val_natCast]
  rw [h, hz]
  rfl

/-- The `byte_decode` reduce-and-wrap closure, at index `k`. -/
private theorem byte_decode_closure_eq {D32 D256 : Std.Usize}
    (decoded : Std.Array Std.U16 256#usize) (k : Nat) (hk : k < 256) (hk32 : k < 2 ^ 32) :
    (hacspec_ml_kem.serialize.byte_decode.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement
        D32 D256).call_mut decoded ⟨BitVec.ofNat _ k⟩
      = .ok (({ val := u16OfNat ((decoded.val[k]!).val % 3329) } :
                hacspec_ml_kem.parameters.FieldElement), decoded) := by
  have hkv : ((⟨BitVec.ofNat _ k⟩ : Std.Usize)).val = k := by
    show (BitVec.ofNat _ k).toNat = k
    simp only [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have h32 : (32 : Nat) ≤ System.Platform.numBits := by
      have := System.Platform.numBits_eq; omega
    calc k < 2 ^ 32 := hk32
      _ ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) h32
  have hlen : decoded.val.length = 256 := by have := decoded.property; simpa using this
  have hidx : Aeneas.Std.Array.index_usize decoded (⟨BitVec.ofNat _ k⟩ : Std.Usize)
      = .ok (decoded.val[k]!) := by
    have := array_index_ok decoded (⟨BitVec.ofNat _ k⟩ : Std.Usize) (by rw [hkv, hlen]; exact hk)
    rw [hkv] at this; exact this
  have hq : ((hacspec_ml_kem.parameters.FIELD_MODULUS : Std.U16)).val = 3329 := by
    simp [hacspec_ml_kem.parameters.FIELD_MODULUS]
  obtain ⟨r, hr, hrv⟩ :=
    u16_rem_ok (decoded.val[k]!) hacspec_ml_kem.parameters.FIELD_MODULUS (by rw [hq]; omega)
  have hreq : r = u16OfNat ((decoded.val[k]!).val % 3329) := by
    refine Aeneas.Std.UScalar.eq_of_val_eq ?_
    rw [hrv, hq, u16OfNat_val _ (by omega)]
  show (do
      let i ← Aeneas.Std.Array.index_usize decoded (⟨BitVec.ofNat _ k⟩ : Std.Usize)
      let i1 ← i % hacspec_ml_kem.parameters.FIELD_MODULUS
      let fe ← hacspec_ml_kem.parameters.FieldElement.new i1
      Result.ok (fe, decoded)) = _
  rw [hidx]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr]; simp only [Aeneas.Std.bind_tc_ok]
  unfold hacspec_ml_kem.parameters.FieldElement.new
  simp only [Aeneas.Std.bind_tc_ok, hreq]

/-- **The apex, spec side**: `byte_decode 3072 a 12` reproduces `lift_poly p`
    whenever `p`'s lanes hold `dec12` of `a`'s bytes. -/
private theorem byte_decode_12_eq (a : Std.Array Std.U8 384#usize)
    (p : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
           libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hp : declane a.val p 16) :
    hacspec_ml_kem.serialize.byte_decode (D32 := 384#usize) 3072#usize a 12#usize
      = .ok (lift_poly p) := by
  obtain ⟨decoded, hdec, hdecget⟩ := byte_decode_generic_12_get a
  have e2 : ((32#usize : Std.Usize) * (12#usize : Std.Usize) : Result Std.Usize)
      = .ok (384#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have e4 : ((256#usize : Std.Usize) * (12#usize : Std.Usize) : Result Std.Usize)
      = .ok (3072#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have halen : a.val.length = 384 := by have := a.property; simpa using this
  have hslice : (Aeneas.Std.lift (Aeneas.Std.Array.to_slice a) : Result (Slice Std.U8))
      = .ok ⟨a.val, by scalar_tac⟩ := by
    simp [Aeneas.Std.lift, Aeneas.Std.Array.to_slice]
  have hlenq : ∀ sl : Slice Std.U8, sl.val.length = 384 →
      CoreModels.core.slice.Slice.len sl = .ok (384#usize : Std.Usize) := by
    intro sl hsl
    have hl : Aeneas.Std.Slice.len sl = (384#usize : Std.Usize) := by
      refine Aeneas.Std.UScalar.eq_of_val_eq ?_
      rw [Aeneas.Std.Slice.len_val]
      show sl.val.length = ((384#usize : Std.Usize)).val
      rw [hsl]; scalar_tac
    simp [CoreModels.core.slice.Slice.len, hl]
    rfl
  -- the reduce-and-wrap `createi`
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
      (T := hacspec_ml_kem.parameters.FieldElement)
      (256#usize : Std.Usize)
      (hacspec_ml_kem.serialize.byte_decode.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement
        384#usize 3072#usize)
      decoded
      (fun k => lift_fe (p.coefficients.val[k / 16]!).elements.val[k % 16]!)
      (fun k hk => by
        have hk256 : k < 256 := by simpa using hk
        have hlane : ((p.coefficients.val[k / 16]!).elements.val[k % 16]!).val
            = ((dec12 a.val k : Nat) : Int) := by
          have := hp (k / 16) (by omega) (k % 16) (by omega)
          rw [show 16 * (k / 16) + k % 16 = k from by omega] at this
          exact this
        rw [byte_decode_closure_eq decoded k hk256 (by omega),
          lift_fe_of_nat _ (dec12 a.val k) hlane, hdecget k hk256])
  unfold hacspec_ml_kem.serialize.byte_decode
  simp only [hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT, Aeneas.Std.massert,
    le_refl, if_true, Aeneas.Std.bind_tc_ok, hslice, hlenq ⟨a.val, by scalar_tac⟩ halen, e2, e4, hdec,
    hacspec_ml_kem.parameters.createi, hfn]
  rfl

/-! ### `byte_decode_dyn` at `d = 12` — the slice-shaped entry point. -/

private theorem byte_decode_dyn_12_eq (b : Slice Std.U8) (hb : b.val.length = 384)
    (p : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
           libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hp : declane b.val p 16) :
    hacspec_ml_kem.serialize.byte_decode_dyn b 12#usize = .ok (lift_poly p) := by
  have hl : Aeneas.Std.Slice.len b = (384#usize : Std.Usize) := by
    refine Aeneas.Std.UScalar.eq_of_val_eq ?_
    rw [Aeneas.Std.Slice.len_val]
    show b.val.length = ((384#usize : Std.Usize)).val
    rw [hb]; scalar_tac
  have hlen : CoreModels.core.slice.Slice.len b = .ok (384#usize : Std.Usize) := by
    simp [CoreModels.core.slice.Slice.len, hl]
    rfl
  have e2 : ((32#usize : Std.Usize) * (12#usize : Std.Usize) : Result Std.Usize)
      = .ok (384#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  unfold hacspec_ml_kem.serialize.byte_decode_dyn
  simp only [hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT, Aeneas.Std.massert,
    le_refl, if_true, Aeneas.Std.bind_tc_ok, hlen, e2]
  -- select the `d = 12` branch of the `match d.val with` dispatch
  show (do
      let r ←
        CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
          (384#usize : Std.Usize) b
      let a ←
        CoreModels.core.result.Result.unwrap
          CoreModels.core.array.TryFromSliceError.Insts.CoreFmtDebug r
      hacspec_ml_kem.serialize.byte_decode (D32 := 384#usize) 3072#usize a 12#usize) = _
  have htry :
      CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
          (384#usize : Std.Usize) b
        = .ok (CoreModels.core.result.Result.Ok
            (⟨b.val, by rw [hb]; scalar_tac⟩ : Std.Array Std.U8 384#usize)) := by
    unfold
      CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
    rw [dif_pos hl]
  rw [htry]
  simp only [Aeneas.Std.bind_tc_ok, CoreModels.core.result.Result.unwrap]
  exact byte_decode_12_eq _ p hp

end L57Bank2

/-- L5.7 — `serialize.deserialize_to_uncompressed_ring_element` (= `ByteDecode_12`).

    Sibling of L5.6 and of the A2 axiom `deserialize_to_reduced_ring_element_fc`;
    the difference from A2 is that this one does NOT apply the trailing
    `cond_subtract_3329` reduction, so no canonicality bound is claimed. -/
@[spec]
theorem deserialize_to_uncompressed_ring_element_fc
    (serialized : Slice Std.U8)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_len : serialized.length = 384) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_to_uncompressed_ring_element
      (vectortraitsOperationsInst := portable_ops_inst)
      serialized re
    ⦃ ⇓ p => ⌜ hacspec_ml_kem.serialize.byte_decode_dyn serialized 12#usize
                = .ok (lift_poly p) ⌝ ⦄ := by
  -- Impl side: the 16-chunk `chunks_exact 24` loop puts `dec12` in every lane.
  have hlen' : serialized.val.length = 384 := by
    simpa [Aeneas.Std.Slice.length] using h_len
  obtain ⟨p, hp_eq, hp⟩ :=
    triple_exists_ok_fc (deserialize_uncompressed_impl_fc serialized hlen' re)
  -- Spec side: `byte_decode_dyn _ 12` reproduces exactly those lanes.
  exact triple_of_ok_fc hp_eq
    (byte_decode_dyn_12_eq serialized hlen' p ((holds_ok _).mp hp))

end libcrux_iot_ml_kem.SerializeFc
