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

/-! ## PROVER bank for L5.6 — the ENCODE direction (`byte_encode` at `d = 12`).

    Mirror of the L5.7 decode bank above, in the other direction. Provenance:
    the decomposition is the `_d`-generic encode ladder of
    `Hacspec_ml_kem.Commute.Serialize_compress.fst` specialised to `d = 12`
    (`lemma_bitvec_from_bounded_index_d` → `lemma_bits_to_bytes_bit_d` →
    `lemma_byte_encode_bit_d` → `lemma_serialize_byte_eq_d` →
    `lemma_serialize_chunk_eq_byte_encode_d`), plus the `to_unsigned_representative`
    contract of `Libcrux_ml_kem.Vector.Traits.Spec` (F*
    `to_unsigned_representative_pre`/`_post`, ported here as `to_unsigned_fm_eq`).
    Every Lean proof below stands on its own; the F* names are provenance only.

    The shared vocabulary is:
    * `uval` — the canonical residue of an impl lane, as a `Nat` in `[0, q)`;
    * `encByte re n` — byte `n` of the 12-bit packing of `re`, purely in `Nat`;
    * `vbyte v m` — byte `m` of one 24-byte chunk, as the impl's `I16→U8` terms.

    Representation rule (skill §4.1 / the bit-packing recipe): all bit algebra is
    done in `Nat`, never `BitVec`, and never inside a loop residue. -/

section L56Bank

open Aeneas.Std

/-! ### `I16` sign/`bv` plumbing. -/

private theorem i16_toNat_lt (x : Std.I16) : x.bv.toNat < 65536 := by
  have h := x.bv.isLt; simpa using h

/-- Sign case analysis for an `I16`: msb, `bv.toNat` range, and `.val`, together.
    Stated as a disjunction so callers get all three facts from one `rcases`. -/
private theorem i16_msb_cases (x : Std.I16) :
    (x.bv.msb = true ∧ 32768 ≤ x.bv.toNat ∧ x.val = (x.bv.toNat : Int) - 65536)
    ∨ (x.bv.msb = false ∧ x.bv.toNat < 32768 ∧ x.val = (x.bv.toNat : Int)) := by
  have hlt := i16_toNat_lt x
  have hval : x.val = if 2 * x.bv.toNat < 2 ^ 16 then (x.bv.toNat : Int)
      else (x.bv.toNat : Int) - ((2 ^ 16 : Nat) : Int) := BitVec.toInt_eq_toNat_cond x.bv
  have hmsb := BitVec.msb_eq_false_iff_two_mul_lt (x := x.bv)
  simp only [show (2:Nat) ^ 16 = 65536 from rfl] at hval hmsb
  by_cases hc : 2 * x.bv.toNat < 65536
  · exact Or.inr ⟨hmsb.mpr hc, by omega, by rw [hval, if_pos hc]⟩
  · refine Or.inl ⟨?_, by omega, by rw [hval, if_neg hc]; norm_num⟩
    rcases Bool.eq_false_or_eq_true x.bv.msb with h | h
    · exact h
    · exact absurd (hmsb.mp h) hc

private theorem msb_false_of_toNat_lt (x : Std.I16) (h : x.bv.toNat < 4096) :
    x.bv.msb = false := by
  rw [BitVec.msb_eq_false_iff_two_mul_lt]
  simp only [show (2:Nat) ^ 16 = 65536 from rfl]; omega

/-- Arithmetic shift right by 15 on an `I16` is the sign mask. -/
private theorem sshr15_toNat (x : Std.I16) :
    (x.bv.sshiftRight 15).toNat = if x.bv.msb then 65535 else 0 := by
  have hlt := i16_toNat_lt x
  rcases i16_msb_cases x with ⟨hm, hn, _⟩ | ⟨hm, hn, _⟩
  · rw [hm, if_pos rfl, BitVec.sshiftRight_eq_of_msb_true hm]
    have hnot : (~~~x.bv).toNat = 65535 - x.bv.toNat := by rw [BitVec.toNat_not]
    have hz : (~~~x.bv) >>> 15 = 0#16 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, hnot, Nat.shiftRight_eq_div_pow]
      simp only [show (2:Nat) ^ 15 = 32768 from rfl]
      show (65535 - x.bv.toNat) / 32768 = (0#16 : BitVec 16).toNat
      rw [Nat.div_eq_of_lt (by omega)]; rfl
    rw [hz]; rfl
  · rw [hm]
    simp only [Bool.false_eq_true, if_false]
    rw [BitVec.toNat_sshiftRight_of_msb_false hm, Nat.shiftRight_eq_div_pow]
    simp only [show (2:Nat) ^ 15 = 32768 from rfl]
    exact Nat.div_eq_of_lt hn

/-- The sign mask AND `q`: `q` when the lane is negative, `0` otherwise. -/
private theorem and3329_toNat (x : Std.I16) :
    ((x.bv.sshiftRight 15) &&& (3329#i16 : Std.I16).bv).toNat
      = if x.bv.msb then 3329 else 0 := by
  rw [BitVec.toNat_and, sshr15_toNat, show ((3329#i16 : Std.I16).bv).toNat = 3329 from rfl]
  rcases i16_msb_cases x with ⟨hm, _, _⟩ | ⟨hm, _, _⟩
  · rw [hm, if_pos rfl, if_pos rfl, Nat.land_comm]
    have := Nat.and_two_pow_sub_one_eq_mod 3329 16
    norm_num at this
    exact this
  · rw [hm]
    simp only [Bool.false_eq_true, if_false]
    exact Nat.zero_and 3329

/-! ### `to_unsigned_field_modulus` — the canonical-residue projection.

    Port of F* `lemma_to_unsigned_representative_chunk_commutes`
    (`Commute.Chunk.fst:973`) together with its trait contract
    `to_unsigned_representative_pre = is_i16b_array_opaque 3328 vec` /
    `_post = (0 ≤ v y ≤ 3328 ∧ mod_q_eq (v y) (v x))`. The hypothesis `hb`
    below IS that `pre`; see the SPECREQ in the dispatch report — the L5.6
    obligation as frozen does not supply it. -/

private theorem to_unsigned_fm_eq
    (a out : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hb : ∀ i : Nat, i < 16 → (a.elements.val[i]!).val.natAbs ≤ 3328) :
    ∃ r : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector,
      libcrux_iot_ml_kem.serialize.to_unsigned_field_modulus
        (vectortraitsOperationsInst := portable_ops_inst) a out = .ok r
      ∧ ∀ i : Nat, i < 16 →
          (r.elements.val[i]!).bv.toNat < 3329
          ∧ (r.elements.val[i]!).val = ((r.elements.val[i]!).bv.toNat : Int)
          ∧ ((r.elements.val[i]!).val : ZMod 3329)
              = ((a.elements.val[i]!).val : ZMod 3329) := by
  have hFM : libcrux_iot_ml_kem.vector.traits.FIELD_MODULUS = (3329#i16 : Std.I16) := by
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_MODULUS; rfl
  obtain ⟨a1, ha1_eq, ha1⟩ :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.triple_exists_ok_fc
      (libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.shift_right_spec
        (15#i32 : Std.I32) ⟨by scalar_tac, by scalar_tac⟩ a)
  obtain ⟨a2, ha2_eq, ha2⟩ :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.triple_exists_ok_fc
      (libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.bitwise_and_with_constant_spec
        a1 libcrux_iot_ml_kem.vector.traits.FIELD_MODULUS)
  have ha2n : ∀ i : Nat, i < 16 →
      (a2.elements.val[i]!).bv.toNat = if (a.elements.val[i]!).bv.msb then 3329 else 0 := by
    intro i hi
    rw [ha2 i hi, ha1 i hi, hFM,
      show ((15#i32 : Std.I32).val.toNat) = 15 from by scalar_tac]
    exact and3329_toNat _
  have ha2v : ∀ i : Nat, i < 16 →
      (a2.elements.val[i]!).val = if (a.elements.val[i]!).bv.msb then (3329 : Int) else 0 := by
    intro i hi
    rcases i16_msb_cases (a2.elements.val[i]!) with ⟨hm, hn, hv⟩ | ⟨hm, hn, hv⟩
    · exfalso; rw [ha2n i hi] at hn; split at hn <;> omega
    · rw [hv, ha2n i hi]; split <;> norm_num
  have hsum : ∀ i : Nat, i < 16 →
      0 ≤ (a2.elements.val[i]!).val + (a.elements.val[i]!).val
      ∧ (a2.elements.val[i]!).val + (a.elements.val[i]!).val ≤ 3328 := by
    intro i hi
    have h1 := ha2v i hi
    have h3 := hb i hi
    rcases i16_msb_cases (a.elements.val[i]!) with ⟨hm, hn, hv⟩ | ⟨hm, hn, hv⟩
    · rw [hm, if_pos rfl] at h1; rw [h1, hv]; omega
    · rw [hm] at h1; simp only [Bool.false_eq_true, if_false] at h1
      rw [h1, hv]; omega
  obtain ⟨r, hr_eq, hr⟩ :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.triple_exists_ok_fc
      (libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.add_spec a2 a
        (fun i hi => by have := hsum i hi; omega))
  refine ⟨r, ?_, ?_⟩
  · show (do
        let a1' ← libcrux_iot_ml_kem.vector.portable.arithmetic.shift_right (15#i32 : Std.I32) a
        let a2' ← libcrux_iot_ml_kem.vector.portable.arithmetic.bitwise_and_with_constant a1'
                    libcrux_iot_ml_kem.vector.traits.FIELD_MODULUS
        libcrux_iot_ml_kem.vector.portable.arithmetic.add a2' a) = _
    rw [ha1_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [ha2_eq]; simp only [Aeneas.Std.bind_tc_ok]
    exact hr_eq
  · intro i hi
    have hrv := (hr i hi).1
    have hs := hsum i hi
    rcases i16_msb_cases (r.elements.val[i]!) with ⟨hm, hn, hv⟩ | ⟨hm, hn, hv⟩
    · exfalso
      have := i16_toNat_lt (r.elements.val[i]!)
      rw [hrv] at hv; omega
    · refine ⟨by omega, hv, ?_⟩
      rw [hrv]
      rw [ha2v i hi]
      split
      · push_cast; norm_num [show ((3329 : Int) : ZMod 3329) = 0 from by decide]
      · push_cast; norm_num

/-! ### Impl side — `serialize_12_int` closed form.

    The `U8` truncation the impl performs (`as_u8` = declassify ∘ hcast ∘ classify). -/

private def c8 (x : Std.I16) : Std.U8 := Std.IScalar.hcast .U8 x

private theorem c8_val (x : Std.I16) : (c8 x).val = x.bv.toNat % 256 := by
  show (Std.UScalar.bv (Std.IScalar.hcast .U8 x)).toNat = _
  rw [Std.IScalar.hcast_bv_eq, BitVec.signExtend_eq_setWidth_of_le _ (by decide),
    BitVec.toNat_setWidth]
  rfl

/-- The three bytes the impl computes from a 2-lane group. -/
private def w0of (v0 : Std.I16) : Std.U8 := c8 ⟨v0.bv &&& 255#16⟩

private def w1of (v0 v1 : Std.I16) : Std.U8 :=
  c8 ⟨(v0.bv.sshiftRight 8) ||| ((v1.bv &&& 15#16) <<< 4)⟩

private def w2of (v1 : Std.I16) : Std.U8 := c8 ⟨(v1.bv.sshiftRight 4) &&& 255#16⟩

private theorem serialize_12_int_eq (s : Slice Std.I16) (h : 2 ≤ s.val.length) :
    libcrux_iot_ml_kem.vector.portable.serialize.serialize_12_int s
      = .ok (w0of s.val[0]!, w1of s.val[0]! s.val[1]!, w2of s.val[1]!) := by
  have h0 : Aeneas.Std.Slice.index_usize s 0#usize = .ok s.val[0]! :=
    slice_index_usize_eq s 0#usize (by simpa using (by omega : 0 < s.val.length))
  have h1 : Aeneas.Std.Slice.index_usize s 1#usize = .ok s.val[1]! :=
    slice_index_usize_eq s 1#usize (by simpa using (by omega : 1 < s.val.length))
  unfold libcrux_iot_ml_kem.vector.portable.serialize.serialize_12_int
  rw [h0, h1]
  rfl

/-! The three `Nat` closed forms. `w0of` needs no bound; `w1of`/`w2of` need the
    12-bit lane bound (which `to_unsigned_fm_eq` supplies). -/

private theorem w0of_val (v0 : Std.I16) : (w0of v0).val = v0.bv.toNat % 256 := by
  rw [w0of, c8_val]
  show ((v0.bv &&& 255#16).toNat) % 256 = _
  rw [BitVec.toNat_and, show (255#16 : BitVec 16).toNat = 255 from rfl, nat_and_255]
  omega

private theorem w2of_val (v1 : Std.I16) (h1 : v1.bv.toNat < 4096) :
    (w2of v1).val = v1.bv.toNat / 16 := by
  rw [w2of, c8_val]
  show (((v1.bv.sshiftRight 4) &&& 255#16).toNat) % 256 = _
  rw [BitVec.sshiftRight_eq_of_msb_false (msb_false_of_toNat_lt v1 h1)]
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight,
    show (255#16 : BitVec 16).toNat = 255 from rfl, nat_and_255,
    Nat.shiftRight_eq_div_pow]
  simp only [show (2:Nat) ^ 4 = 16 from rfl]
  omega

private theorem w1of_val (v0 v1 : Std.I16) (h0 : v0.bv.toNat < 4096) (h1 : v1.bv.toNat < 4096) :
    (w1of v0 v1).val = v0.bv.toNat / 256 + v1.bv.toNat % 16 * 16 := by
  rw [w1of, c8_val]
  show (((v0.bv.sshiftRight 8) ||| ((v1.bv &&& 15#16) <<< 4)).toNat) % 256 = _
  rw [BitVec.sshiftRight_eq_of_msb_false (msb_false_of_toNat_lt v0 h0)]
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_and,
    show (15#16 : BitVec 16).toNat = 15 from rfl, nat_and_15, Nat.shiftRight_eq_div_pow]
  simp only [show (2:Nat) ^ 8 = 256 from rfl]
  have hm : v1.bv.toNat % 16 < 16 := Nat.mod_lt _ (by omega)
  have hsl : (v1.bv.toNat % 16) <<< 4 = v1.bv.toNat % 16 * 16 := by
    rw [Nat.shiftLeft_eq]
  have hlt : (v1.bv.toNat % 16) <<< 4 < 2 ^ 16 := by
    rw [hsl]; simp only [show (2:Nat) ^ 16 = 65536 from rfl]; omega
  rw [Nat.mod_eq_of_lt hlt, Nat.lor_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt (i := 4) (a := v1.bv.toNat % 16)
      (show v0.bv.toNat / 256 < 2 ^ 4 by
        simp only [show (2:Nat) ^ 4 = 16 from rfl]; omega),
    hsl]
  omega

/-! ### Impl side — the 24-byte `serialize_12`.

    Sub-slicing is over STRICT ranges (`2g < 2g+2`), so it goes through aeneas's
    real `Slice.subslice_spec`, NOT the A3/A4 empty-range axioms. -/

/-- Array-shaped strict subslice: `&arr[a..b]` via `as_slice` + the slice index. -/
private theorem array_index_range_strict {T : Type} [Inhabited T] {N : Std.Usize}
    (arr : Std.Array T N) (a b : Std.Usize)
    (h0 : a.val < b.val) (h1 : b.val ≤ arr.val.length) :
    ∃ ns : Slice T,
      CoreModels.core.Array.Insts.CoreOpsIndexIndex.index
        (CoreModels.core.Slice.Insts.CoreOpsIndexIndex
          (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T))
        arr ⟨a, b⟩ = .ok ns
      ∧ ns.val.length = b.val - a.val
      ∧ ∀ i : Nat, i < b.val - a.val → ns.val[i]! = arr.val[a.val + i]! := by
  have has : CoreModels.core.array.Array.as_slice arr = .ok (Aeneas.Std.Array.to_slice arr) := rfl
  have hlen : b.val ≤ (Aeneas.Std.Array.to_slice arr).val.length := h1
  obtain ⟨ns, he, hl, hg⟩ := slice_index_range_strict (Aeneas.Std.Array.to_slice arr) a b h0 hlen
  refine ⟨ns, ?_, hl, hg⟩
  unfold CoreModels.core.Array.Insts.CoreOpsIndexIndex.index
  rw [has]
  simp only [Aeneas.Std.bind_tc_ok]
  exact he

private theorem slice_update_eq {α : Type} (s : Slice α) (i : Std.Usize) (x : α)
    (h : i.val < s.val.length) :
    Aeneas.Std.Slice.update s i x = .ok (s.set i x) := by
  simp only [Aeneas.Std.Slice.update, List.getElem?_eq_getElem h]
  rfl

private theorem bind_ok_triple {α β γ δ : Type} {x : Result (α × β × γ)} {a : α} {b : β} {c : γ}
    (h : x = .ok (a, b, c)) (g : α → β → γ → Result δ) :
    (do let (u, v, w) ← x; g u v w) = g a b c := by rw [h]; rfl

/-- Byte `m` of the 12-bit packing of one 16-lane vector, in impl terms. -/
private def vbyte (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (n : Nat) : Std.U8 :=
  if n % 3 = 0 then w0of (v.elements.val[2 * (n / 3)]!)
  else if n % 3 = 1 then w1of (v.elements.val[2 * (n / 3)]!) (v.elements.val[2 * (n / 3) + 1]!)
  else w2of (v.elements.val[2 * (n / 3) + 1]!)

/-- One group of `serialize_12`: 2-lane sub-slice + `serialize_12_int`. -/
private theorem s12_group (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (a bnd : Std.Usize) (m0 m1 : Nat) (ha : a.val = m0) (hb : bnd.val = m0 + 2)
    (hm1 : m1 = m0 + 1) (hm : m0 + 2 ≤ 16) :
    ∃ ns : Slice Std.I16,
      CoreModels.core.Array.Insts.CoreOpsIndexIndex.index
        (CoreModels.core.Slice.Insts.CoreOpsIndexIndex
          (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I16))
        v.elements ⟨a, bnd⟩ = .ok ns
      ∧ libcrux_iot_ml_kem.vector.portable.serialize.serialize_12_int ns
          = .ok (w0of v.elements.val[m0]!,
                 w1of v.elements.val[m0]! v.elements.val[m1]!,
                 w2of v.elements.val[m1]!) := by
  subst hm1
  have hE : v.elements.val.length = 16 := by have := v.elements.property; simpa using this
  obtain ⟨ns, he, hl, hget⟩ := array_index_range_strict v.elements a bnd (by omega) (by omega)
  refine ⟨ns, he, ?_⟩
  rw [serialize_12_int_eq ns (by omega)]
  rw [hget 0 (by omega), hget 1 (by omega), ha]
  norm_num

/-- The 24 bytes `serialize_12` writes into `out`, as an explicit `set` chain. -/
private def s12set (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8) : Slice Std.U8 :=
  out.set 0#usize (w0of v.elements.val[0]!)
  |>.set 1#usize (w1of v.elements.val[0]! v.elements.val[1]!)
  |>.set 2#usize (w2of v.elements.val[1]!)
  |>.set 3#usize (w0of v.elements.val[2]!)
  |>.set 4#usize (w1of v.elements.val[2]! v.elements.val[3]!)
  |>.set 5#usize (w2of v.elements.val[3]!)
  |>.set 6#usize (w0of v.elements.val[4]!)
  |>.set 7#usize (w1of v.elements.val[4]! v.elements.val[5]!)
  |>.set 8#usize (w2of v.elements.val[5]!)
  |>.set 9#usize (w0of v.elements.val[6]!)
  |>.set 10#usize (w1of v.elements.val[6]! v.elements.val[7]!)
  |>.set 11#usize (w2of v.elements.val[7]!)
  |>.set 12#usize (w0of v.elements.val[8]!)
  |>.set 13#usize (w1of v.elements.val[8]! v.elements.val[9]!)
  |>.set 14#usize (w2of v.elements.val[9]!)
  |>.set 15#usize (w0of v.elements.val[10]!)
  |>.set 16#usize (w1of v.elements.val[10]! v.elements.val[11]!)
  |>.set 17#usize (w2of v.elements.val[11]!)
  |>.set 18#usize (w0of v.elements.val[12]!)
  |>.set 19#usize (w1of v.elements.val[12]! v.elements.val[13]!)
  |>.set 20#usize (w2of v.elements.val[13]!)
  |>.set 21#usize (w0of v.elements.val[14]!)
  |>.set 22#usize (w1of v.elements.val[14]! v.elements.val[15]!)
  |>.set 23#usize (w2of v.elements.val[15]!)

private theorem s12set_length
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8) (h : out.val.length = 24) : (s12set v out).val.length = 24 := by
  unfold s12set
  simp only [Aeneas.Std.Slice.set_val_eq, List.length_set]; exact h

set_option maxHeartbeats 4000000 in
private theorem s12set_get
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8) (h : out.val.length = 24) (n : Nat) (hn : n < 24) :
    (s12set v out).val[n]! = vbyte v n := by
  unfold s12set
  simp only [Aeneas.Std.Slice.set_val_eq]
  interval_cases n <;> (simp_lists; norm_num [vbyte])

set_option maxHeartbeats 4000000 in
/-- **Impl-side chunk closed form**: `serialize_12` writes exactly `vbyte`. -/
private theorem serialize_12_eq
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8) (h : out.val.length = 24) :
    libcrux_iot_ml_kem.vector.portable.serialize.serialize_12 v out = .ok (s12set v out) := by
  obtain ⟨ns0, he0, hs0⟩ := s12_group v 0#usize 2#usize 0 1
    (by scalar_tac) (by scalar_tac) rfl (by omega)
  obtain ⟨ns1, he1, hs1⟩ := s12_group v 2#usize 4#usize 2 3
    (by scalar_tac) (by scalar_tac) rfl (by omega)
  obtain ⟨ns2, he2, hs2⟩ := s12_group v 4#usize 6#usize 4 5
    (by scalar_tac) (by scalar_tac) rfl (by omega)
  obtain ⟨ns3, he3, hs3⟩ := s12_group v 6#usize 8#usize 6 7
    (by scalar_tac) (by scalar_tac) rfl (by omega)
  obtain ⟨ns4, he4, hs4⟩ := s12_group v 8#usize 10#usize 8 9
    (by scalar_tac) (by scalar_tac) rfl (by omega)
  obtain ⟨ns5, he5, hs5⟩ := s12_group v 10#usize 12#usize 10 11
    (by scalar_tac) (by scalar_tac) rfl (by omega)
  obtain ⟨ns6, he6, hs6⟩ := s12_group v 12#usize 14#usize 12 13
    (by scalar_tac) (by scalar_tac) rfl (by omega)
  obtain ⟨ns7, he7, hs7⟩ := s12_group v 14#usize 16#usize 14 15
    (by scalar_tac) (by scalar_tac) rfl (by omega)
  have hlen : CoreModels.core.slice.Slice.len out = .ok (24#usize : Std.Usize) := by
    show Result.ok (Aeneas.Std.Slice.len out) = _
    congr 1
    apply Std.UScalar.eq_of_val_eq
    simp [Aeneas.Std.Slice.len_val, h]
  unfold libcrux_iot_ml_kem.vector.portable.serialize.serialize_12 s12set
  rw [hlen]
  simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.massert, if_true]
  rw [he0]; simp only [Aeneas.Std.bind_tc_ok]
  rw [bind_ok_triple hs0]
  rw [slice_update_eq _ _ _ (by simp only [h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [he1]; simp only [Aeneas.Std.bind_tc_ok]
  rw [bind_ok_triple hs1]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [he2]; simp only [Aeneas.Std.bind_tc_ok]
  rw [bind_ok_triple hs2]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [he3]; simp only [Aeneas.Std.bind_tc_ok]
  rw [bind_ok_triple hs3]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [he4]; simp only [Aeneas.Std.bind_tc_ok]
  rw [bind_ok_triple hs4]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [he5]; simp only [Aeneas.Std.bind_tc_ok]
  rw [bind_ok_triple hs5]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [he6]; simp only [Aeneas.Std.bind_tc_ok]
  rw [bind_ok_triple hs6]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [he7]; simp only [Aeneas.Std.bind_tc_ok]
  rw [bind_ok_triple hs7]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]

/-! ### The pure `Nat` encode model.

    `encByte re n` is byte `n` of the `d = 12` packing of `re`'s canonical lane
    residues. This is the atom the loop invariant is stated in: no `|||`, `<<<`
    or `BitVec` ever enters the loop residue (the F* discipline of keeping the
    per-chunk bit equality `opaque_to_smt`). -/

/-- Canonical residue of an impl lane, as a `Nat` in `[0, q)`. -/
private def uval (x : Std.I16) : Nat := (x.val % 3329).toNat

private theorem uval_lt (x : Std.I16) : uval x < 3329 := by unfold uval; omega

/-- Lane `j` of `re`, as a canonical residue. -/
private def encLane (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (j : Nat) : Nat :=
  uval ((re.coefficients.val[j / 16]!).elements.val[j % 16]!)

private theorem encLane_lt (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (j : Nat) :
    encLane re j < 3329 := uval_lt _

/-- Byte `n` of the `d = 12` packing of `re` (`n < 384`). -/
private def encByte (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (n : Nat) : Nat :=
  if n % 3 = 0 then encLane re (2 * (n / 3)) % 256
  else if n % 3 = 1 then
    encLane re (2 * (n / 3)) / 256 + encLane re (2 * (n / 3) + 1) % 16 * 16
  else encLane re (2 * (n / 3) + 1) / 16

/-- The `to_unsigned_field_modulus` post, read as "this lane IS the canonical
    residue of the corresponding lane of `re`". -/
private theorem uval_encLane
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c l : Nat) (hc : c < 16) (hl : l < 16)
    (x : Std.I16) (hx0 : x.bv.toNat < 3329) (hx1 : x.val = (x.bv.toNat : Int))
    (hx2 : (x.val : ZMod 3329)
          = (((re.coefficients.val[c]!).elements.val[l]!).val : ZMod 3329)) :
    x.bv.toNat = encLane re (16 * c + l) := by
  have hdiv : (16 * c + l) / 16 = c := by omega
  have hmod : (16 * c + l) % 16 = l := by omega
  unfold encLane uval
  rw [hdiv, hmod]
  have hmod' : x.val % (3329 : Int)
      = ((re.coefficients.val[c]!).elements.val[l]!).val % (3329 : Int) := by
    have := (ZMod.intCast_eq_intCast_iff' x.val
      ((re.coefficients.val[c]!).elements.val[l]!).val 3329).mp hx2
    simpa using this
  rw [← hmod', hx1]
  omega

/-- Bridge: one 24-byte chunk of `vbyte` is the corresponding window of `encByte`. -/
private theorem vbyte_val_encByte
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Nat) (hc : c < 16)
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hv : ∀ l : Nat, l < 16 → (v.elements.val[l]!).bv.toNat = encLane re (16 * c + l))
    (m : Nat) (hm : m < 24) :
    (vbyte v m).val = encByte re (24 * c + m) := by
  have hp : m / 3 < 8 := by omega
  have h1 : (24 * c + m) % 3 = m % 3 := by omega
  have h2 : (24 * c + m) / 3 = 8 * c + m / 3 := by omega
  have e0 : 2 * (8 * c + m / 3) = 16 * c + 2 * (m / 3) := by ring
  have hg0 : (v.elements.val[2 * (m / 3)]!).bv.toNat = encLane re (16 * c + 2 * (m / 3)) :=
    hv _ (by omega)
  have hg1 : (v.elements.val[2 * (m / 3) + 1]!).bv.toNat
      = encLane re (16 * c + 2 * (m / 3) + 1) := by
    have hh := hv (2 * (m / 3) + 1) (by omega)
    rw [hh]; congr 1
  have hb0 : (v.elements.val[2 * (m / 3)]!).bv.toNat < 4096 := by
    rw [hg0]; have := encLane_lt re (16 * c + 2 * (m / 3)); omega
  have hb1 : (v.elements.val[2 * (m / 3) + 1]!).bv.toNat < 4096 := by
    rw [hg1]; have := encLane_lt re (16 * c + 2 * (m / 3) + 1); omega
  unfold vbyte encByte
  rw [h1, h2, e0]
  rcases (show m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 by omega) with hr | hr | hr
  · rw [hr]
    show (w0of (v.elements.val[2 * (m / 3)]!)).val
        = encLane re (16 * c + 2 * (m / 3)) % 256
    rw [w0of_val, hg0]
  · rw [hr]
    show (w1of (v.elements.val[2 * (m / 3)]!) (v.elements.val[2 * (m / 3) + 1]!)).val
        = encLane re (16 * c + 2 * (m / 3)) / 256
          + encLane re (16 * c + 2 * (m / 3) + 1) % 16 * 16
    rw [w1of_val _ _ hb0 hb1, hg0, hg1]
  · rw [hr]
    show (w2of (v.elements.val[2 * (m / 3) + 1]!)).val
        = encLane re (16 * c + 2 * (m / 3) + 1) / 16
    rw [w2of_val _ hb1, hg1]

/-! ### Impl side — the 16-iteration `0..16` range loop.

    Written-prefix invariant, with the undone-cells conjunct discharged by the
    `setSlice!` prefix lemma (the sub-slice writes are pairwise disjoint). -/

private theorem slice_index_mut_range_strict {T : Type} [Inhabited T]
    (s : Slice T) (a b : Std.Usize) (h0 : a.val < b.val) (h1 : b.val ≤ s.val.length) :
    ∃ (ns : Slice T) (wb : Slice T → Slice T),
      CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
        (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) s
        ⟨a, b⟩ = .ok (ns, wb)
      ∧ ns.val.length = b.val - a.val
      ∧ (∀ s' : Slice T, s'.val.length = b.val - a.val →
            (wb s').val = s.val.setSlice! a.val s'.val) := by
  obtain ⟨ns, hns_eq, hns_val, hns_get⟩ :=
    Std.WP.spec_imp_exists (Aeneas.Std.Slice.subslice_spec s ⟨a, b⟩ h0 h1)
  have hlen : ns.val.length = b.val - a.val := by
    rw [hns_val]
    show (List.slice a.val b.val s.val).length = b.val - a.val
    rw [List.slice_length]; omega
  have hTR : HaxToRange.toRange ({ start := a, «end» := b }
        : CoreModels.core.ops.range.Range Std.Usize) (Aeneas.Std.Slice.len s)
      = ({ start := a, «end» := b } : Aeneas.Std.core.ops.range.Range Std.Usize) := rfl
  refine ⟨ns, (fun sub' =>
      match Aeneas.Std.Slice.update_subslice s
          (HaxToRange.toRange
            ({ start := a, «end» := b } : CoreModels.core.ops.range.Range Std.Usize)
            (Aeneas.Std.Slice.len s)) sub' with
      | .ok s'' => s''
      | _ => s), ?_, hlen, ?_⟩
  · unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
    simp only [CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice,
      CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
      CoreModels.rust_primitives.slice.slice_slice, hns_eq, Aeneas.Std.bind_tc_ok]
    rfl
  · intro s' hs'
    have hupd : Aeneas.Std.Slice.update_subslice s
        (HaxToRange.toRange ({ start := a, «end» := b }
            : CoreModels.core.ops.range.Range Std.Usize) (Aeneas.Std.Slice.len s)) s'
        = .ok ⟨s.val.setSlice! a.val s'.val, by scalar_tac⟩ := by
      rw [hTR]
      unfold Aeneas.Std.Slice.update_subslice
      rw [dif_pos ⟨h0, by simpa [Aeneas.Std.Slice.length] using h1, by
        simpa [Aeneas.Std.Slice.length] using hs'⟩]
    simp only [hupd]

private theorem usize_mul_ok_e (x y : Std.Usize) (hb : x.val * y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x * y : Result Std.Usize) = .ok z ∧ z.val = x.val * y.val := by
  obtain ⟨z, hz, hv, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.mul_bv_spec (x := x) (y := y) (by scalar_tac))
  exact ⟨z, hz, hv⟩

private theorem usize_add_ok_e (x y : Std.Usize) (hb : x.val + y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x + y : Result Std.Usize) = .ok z ∧ z.val = x.val + y.val := by
  obtain ⟨z, hz, hv, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.add_bv_spec (x := x) (y := y) (by scalar_tac))
  exact ⟨z, hz, hv⟩

/-- Written-prefix loop invariant: after `k` iterations the first `24k` bytes
    carry `encByte`, and the length is preserved. -/
private def encInv (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (acc : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector × Slice Std.U8) :
    Result Prop :=
  pure (acc.2.val.length = 384 ∧
        ∀ n : Nat, n < 24 * k.val → (acc.2.val[n]!).val = encByte re n)

set_option maxHeartbeats 4000000 in
private theorem serialize_uncompressed_loop_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hbnd : ∀ c : Nat, c < 16 → ∀ l : Nat, l < 16 →
      ((re.coefficients.val[c]!).elements.val[l]!).val.natAbs ≤ 3328)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 384) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.serialize_uncompressed_ring_element_loop
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := 0#usize, «end» := 16#usize } re scratch serialized
    ⦃ ⇓ p => ⌜ (encInv re 16#usize p).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.serialize_uncompressed_ring_element_loop
  refine libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
    (fun (iter1, scratch1, serialized1) =>
      libcrux_iot_ml_kem.serialize.serialize_uncompressed_ring_element_loop.body
        (vectortraitsOperationsInst := portable_ops_inst) re iter1 scratch1 serialized1)
    (scratch, serialized) 0#usize 16#usize (encInv re) (by scalar_tac) ?_ ?_
  · show (pure _ : Result Prop).holds
    simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
    intro _
    exact ⟨h_len, by intro n hn; exact absurd hn (by scalar_tac)⟩
  · intro acc k hk0 hk16 hinv
    have h16 : (16#usize : Std.Usize).val = 16 := rfl
    obtain ⟨hacc_len, hacc_done⟩ : acc.2.val.length = 384 ∧
        ∀ n : Nat, n < 24 * k.val → (acc.2.val[n]!).val = encByte re n := by
      have hh := hinv
      simp only [encInv, Aeneas.Std.Result.holds, pure, Pure.pure, Std.Do.Triple,
        Std.Do.WP.wp, Std.Do.PredTrans.apply, Std.Do.PostCond.noThrow,
        Std.Do.SPred.pure, Std.Do.SPred.entails] at hh
      exact hh trivial
    by_cases hlt : k.val < 16
    · obtain ⟨s, hs_val, h_iter⟩ :=
        libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_some_eq k
          (by rw [h16]; exact hlt)
      have hcl : re.coefficients.val.length = 16 := by
        have := re.coefficients.property; simpa using this
      have h_idx : Aeneas.Std.Array.index_usize re.coefficients k
          = .ok (re.coefficients.val[k.val]!) :=
        libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq
          re.coefficients k (by rw [show re.coefficients.length = 16 from hcl]; exact hlt)
      obtain ⟨sc1, hsc1_eq, hsc1⟩ :=
        to_unsigned_fm_eq (re.coefficients.val[k.val]!) acc.1
          (fun l hl => hbnd k.val hlt l hl)
      obtain ⟨i1, hi1_eq, hi1⟩ := usize_mul_ok_e (24#usize : Std.Usize) k (by scalar_tac)
      obtain ⟨i2, hi2_eq, hi2⟩ := usize_add_ok_e i1 (24#usize : Std.Usize) (by scalar_tac)
      have hi1v : i1.val = 24 * k.val := by rw [hi1]; scalar_tac
      have hi2v : i2.val = 24 * k.val + 24 := by rw [hi2, hi1v]; scalar_tac
      obtain ⟨sub, wb, hmut_eq, hsub_len, hwb⟩ :=
        slice_index_mut_range_strict acc.2 i1 i2 (by omega) (by rw [hacc_len]; omega)
      have hsub24 : sub.val.length = 24 := by rw [hsub_len]; omega
      have hser12 := serialize_12_eq sc1 sub hsub24
      refine libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.triple_of_ok_fc
        (v := .cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize), (sc1, wb (s12set sc1 sub)))) ?_ ?_
      · show libcrux_iot_ml_kem.serialize.serialize_uncompressed_ring_element_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) re
          { start := k, «end» := 16#usize } acc.1 acc.2 = _
        unfold libcrux_iot_ml_kem.serialize.serialize_uncompressed_ring_element_loop.body
        rw [show (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : CoreModels.core.ops.range.Range Std.Usize)) from rfl]
        rw [h_iter]
        simp only [Aeneas.Std.bind_tc_ok]
        show (do
            let t ← Aeneas.Std.Array.index_usize re.coefficients k
            let scratch1 ← libcrux_iot_ml_kem.serialize.to_unsigned_field_modulus
                             portable_ops_inst t acc.1
            let i1' ← (24#usize : Std.Usize) * k
            let i2' ← i1' + (24#usize : Std.Usize)
            let (sb, index_mut_back) ←
              CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
                (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                  Std.U8) acc.2 { start := i1', «end» := i2' }
            let s1 ← libcrux_iot_ml_kem.vector.portable.serialize.serialize_12 scratch1 sb
            Result.ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
              (scratch1, index_mut_back s1)))) = _
        rw [h_idx]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hsc1_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hi1_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hi2_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hmut_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hser12]
        rfl
      · refine ⟨by rw [h16]; exact hlt, rfl, hs_val, ?_⟩
        show (encInv re s (sc1, wb (s12set sc1 sub))).holds
        simp only [encInv, Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        have hwbv := hwb (s12set sc1 sub) (by rw [s12set_length sc1 sub hsub24]; omega)
        refine ⟨?_, ?_⟩
        · rw [hwbv, List.length_setSlice!]; exact hacc_len
        · intro n hn
          rw [hs_val] at hn
          rw [hwbv]
          by_cases hnk : n < 24 * k.val
          · rw [List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]
            exact hacc_done n hnk
          · rw [List.getElem!_setSlice!_middle _ _ _ _
              ⟨by omega, by rw [s12set_length sc1 sub hsub24]; omega,
               by rw [hacc_len]; omega⟩]
            rw [hi1v, s12set_get sc1 sub hsub24 (n - 24 * k.val) (by omega)]
            have hlanes : ∀ l : Nat, l < 16 →
                (sc1.elements.val[l]!).bv.toNat = encLane re (16 * k.val + l) := by
              intro l hl
              obtain ⟨hb0, hb1, hb2⟩ := hsc1 l hl
              exact uval_encLane re k.val l hlt hl _ hb0 hb1 hb2
            rw [vbyte_val_encByte re k.val hlt sc1 hlanes (n - 24 * k.val) (by omega)]
            congr 1
            omega
    · have hk : k.val = 16 := by omega
      refine libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.triple_of_ok_fc
        (v := .done acc) ?_ ?_
      · show libcrux_iot_ml_kem.serialize.serialize_uncompressed_ring_element_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) re
          { start := k, «end» := 16#usize } acc.1 acc.2 = _
        unfold libcrux_iot_ml_kem.serialize.serialize_uncompressed_ring_element_loop.body
        rw [show (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : CoreModels.core.ops.range.Range Std.Usize)) from rfl]
        rw [libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_none_eq k
          (by rw [h16]; omega)]
        rfl
      · show (encInv re 16#usize acc).holds
        simp only [encInv, Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        exact ⟨hacc_len, by intro n hn; exact hacc_done n (by rw [hk]; rw [h16] at hn; omega)⟩

/-- **Impl-side apex**: under the lane bound (the F* `to_unsigned_representative_pre`),
    `serialize_uncompressed_ring_element` writes exactly `encByte re` into all
    384 bytes. This is the positive half of the L5.6 obligation; the missing
    half is the spec-side `byte_encode` closed form, and the missing HYPOTHESIS
    is `hbnd` — see the SPECREQ. -/
private theorem serialize_uncompressed_impl_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hbnd : ∀ c : Nat, c < 16 → ∀ l : Nat, l < 16 →
      ((re.coefficients.val[c]!).elements.val[l]!).val.natAbs ≤ 3328)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 384) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.serialize_uncompressed_ring_element
      (vectortraitsOperationsInst := portable_ops_inst) re scratch serialized
    ⦃ ⇓ p => ⌜ (encInv re 16#usize p).holds ⌝ ⦄ := by
  have hslen : CoreModels.core.slice.Slice.len serialized = .ok (384#usize : Std.Usize) := by
    show Result.ok (Aeneas.Std.Slice.len serialized) = _
    congr 1
    apply Std.UScalar.eq_of_val_eq
    simp [Aeneas.Std.Slice.len_val, h_len]
  have hdivlit : ∀ x y z : Std.Usize, y.val ≠ 0 → x.val / y.val = z.val →
      (x / y : Result Std.Usize) = .ok z := by
    intro x y z hy hz
    obtain ⟨q, hq_eq, hq_val⟩ := Std.UScalar.div_spec x (y := y) hy
    rw [hq_eq]
    congr 1
    exact Std.UScalar.eq_of_val_eq (by rw [hq_val, hz])
  have hbpr : libcrux_iot_ml_kem.constants.BYTES_PER_RING_ELEMENT
      = .ok (384#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.constants.BYTES_PER_RING_ELEMENT
      libcrux_iot_ml_kem.constants.BITS_PER_RING_ELEMENT
      libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
    rw [usize_mul_lit (256#usize : Std.Usize) (12#usize : Std.Usize)
      (3072#usize : Std.Usize) (by scalar_tac) (by scalar_tac)]
    simp only [Aeneas.Std.bind_tc_ok]
    exact hdivlit _ _ _ (by scalar_tac) (by scalar_tac)
  have hvre : libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
      = .ok (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
      libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
      libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
    exact hdivlit _ _ _ (by scalar_tac) (by scalar_tac)
  unfold libcrux_iot_ml_kem.serialize.serialize_uncompressed_ring_element
  rw [hslen]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hbpr]; simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.massert, if_true]
  rw [hvre]; simp only [Aeneas.Std.bind_tc_ok]
  exact serialize_uncompressed_loop_fc re hbnd scratch serialized h_len

/-! ### Spec side — the pure bit-stream bridge.

    Provenance: the `_d`-generic encode ladder of
    `Hacspec_ml_kem.Commute.Serialize_compress.fst` at `d = 12`
    (`lemma_bitvec_from_bounded_index_d` → `lemma_bits_to_bytes_bit_d` →
    `lemma_byte_encode_bit_d` → `lemma_serialize_byte_eq_d`). `encBit` is the
    Lean spelling of `bitvector_from_bounded_ints`'s closure normal form, and
    `bitSum_encBit_eq_encByte` is `lemma_serialize_byte_eq_12`: the LSB-first
    8-bit window of the 12-bit stream is exactly the impl's byte.

    The `bitSum` toolkit is the one already banked for the decode direction
    (`bitSum`, `natBit`, `bitSum_natBit`, `bitSum_congr`, `bitSum_add`,
    `bitSum_shift` above) — reused, not re-derived.

    STILL MISSING for the L5.6 apex (see the dispatch report): the `createi`
    plumbing that identifies `bits_to_bytes ∘ bitvector_from_bounded_ints ∘
    byte_encode.closure` with `fun n => bitSum (encBit re ∘ (8*n + ·)) 8`,
    and the `byte_encode_into` slice wrapper (`Array.to_slice` +
    `copy_from_slice`). Those are pure plumbing over
    `Util.CreateI.createi_pure_eq`, of the same shape as `bytes_to_bits_get`
    in the decode bank. -/

/-- Bit `m` of the `d = 12` bit stream of `re` — the pure normal form of the
    `bitvector_from_bounded_ints` closure at `d = 12`. -/
private def encBit (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (m : Nat) : Bool :=
  natBit (encLane re (m / 12)) (m % 12)

/-- **The encode keystone**: the LSB-first 8-bit window of the 12-bit stream at
    byte `n` is exactly `encByte re n` — i.e. the spec's `bits_to_bytes` output
    and the impl's `serialize_12` output are the same `Nat`. -/
private theorem bitSum_encBit_eq_encByte
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (n : Nat) :
    bitSum (fun t => encBit re (8 * n + t)) 8 = encByte re n := by
  set g := n / 3 with hg
  have hL0 : encLane re (2 * g) < 4096 := by have := encLane_lt re (2 * g); omega
  have hL1 : encLane re (2 * g + 1) < 4096 := by have := encLane_lt re (2 * g + 1); omega
  unfold encByte
  rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with hr | hr | hr
  · rw [hr]
    show bitSum (fun t => encBit re (8 * n + t)) 8 = encLane re (2 * g) % 256
    rw [bitSum_congr _ (natBit (encLane re (2 * g))) 8 (fun t ht => by
      unfold encBit
      have h1 : (8 * n + t) / 12 = 2 * g := by omega
      have h2 : (8 * n + t) % 12 = t := by omega
      rw [h1, h2])]
    rw [bitSum_natBit]
    norm_num
  · rw [hr]
    show bitSum (fun t => encBit re (8 * n + t)) 8
        = encLane re (2 * g) / 256 + encLane re (2 * g + 1) % 16 * 16
    rw [show (8 : Nat) = 4 + 4 from rfl, bitSum_add]
    rw [bitSum_congr _ (fun t => natBit (encLane re (2 * g)) (8 + t)) 4 (fun t ht => by
      unfold encBit
      have h1 : (8 * n + t) / 12 = 2 * g := by omega
      have h2 : (8 * n + t) % 12 = 8 + t := by omega
      rw [h1, h2])]
    rw [bitSum_congr (fun t => encBit re (8 * n + (4 + t)))
      (fun t => natBit (encLane re (2 * g + 1)) t) 4 (fun t ht => by
      unfold encBit
      have h1 : (8 * n + (4 + t)) / 12 = 2 * g + 1 := by omega
      have h2 : (8 * n + (4 + t)) % 12 = t := by omega
      rw [h1, h2])]
    rw [bitSum_shift, bitSum_natBit]
    have e1 : encLane re (2 * g) / 2 ^ 8 % 2 ^ 4 = encLane re (2 * g) / 256 := by
      simp only [show (2:Nat) ^ 8 = 256 from rfl, show (2:Nat) ^ 4 = 16 from rfl]
      omega
    simp only [show (2:Nat) ^ 4 = 16 from rfl] at *
    rw [e1]
    omega
  · rw [hr]
    show bitSum (fun t => encBit re (8 * n + t)) 8 = encLane re (2 * g + 1) / 16
    rw [bitSum_congr _ (fun t => natBit (encLane re (2 * g + 1)) (4 + t)) 8 (fun t ht => by
      unfold encBit
      have h1 : (8 * n + t) / 12 = 2 * g + 1 := by omega
      have h2 : (8 * n + t) % 12 = 4 + t := by omega
      rw [h1, h2])]
    rw [bitSum_shift]
    simp only [show (2:Nat) ^ 4 = 16 from rfl, show (2:Nat) ^ 8 = 256 from rfl]
    omega

/-! ### The `lift` seam: the spec's `p_raw` IS `encLane`.

    `byte_encode`'s first `createi` reads `(p[j]).val : U16` off the
    `FieldElement` array. When `p = lift_poly re` that raw `U16` is exactly the
    canonical residue `encLane re j`. This is the encode-side counterpart of the
    decode bank's `lift_fe_of_nat`. -/

private theorem lift_fe_raw (x : Std.I16) : ((lift_fe x).val).val = uval x := by
  unfold lift_fe feOfZMod uval i16_to_spec_fe_plain
  have hz : ((ZMod.val (((x.val : Int)) : ZMod 3329) : Int)) = x.val % (3329 : Int) :=
    ZMod.val_intCast _
  have hlt : ZMod.val (((x.val : Int)) : ZMod 3329) < 3329 := ZMod.val_lt _
  show (BitVec.ofNat 16 (ZMod.val (((x.val : Int)) : ZMod 3329))).toNat = _
  rw [BitVec.toNat_ofNat]
  simp only [show (2:Nat) ^ 16 = 65536 from rfl]
  omega

private theorem lift_poly_raw
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (j : Nat) (hj : j < 256) :
    (((lift_poly re).val[j]!).val).val = encLane re j := by
  have hget : (lift_poly re).val[j]!
      = lift_fe ((re.coefficients.val[j / 16]!).elements.val[j % 16]!) := by
    show ((List.range 256).map (fun j =>
        lift_fe (re.coefficients.val[j / 16]!).elements.val[j % 16]!))[j]! = _
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    rfl
  rw [hget, lift_fe_raw]
  rfl

end L56Bank

/-! ## Message (de)serialization — `d = 1`, exact 1:1 with the hacspec model.

    L5.1 (`deserialize_then_decompress_message_fc`) is stated at the END of this
    file, after its `L51Bank` section: it assembles `message_impl_fc` and
    `message_spec_eq`, which must therefore precede it. -/

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

/-! ### SPECREQ evidence for L5.3 (`deserialize_then_decompress_ring_element_v_fc`).

    The L5.3 statement below is **under-constrained**: its precondition is
    `⌜True⌝`, but the Rust source of `deserialize_then_decompress_ring_element_v`
    carries

        #[hax_lib::requires(
            (V_COMPRESSION_FACTOR == 4 || V_COMPRESSION_FACTOR == 5) &&
            serialized.len() == 32 * V_COMPRESSION_FACTOR)]

    (`ml-kem/src/serialize.rs`, immediately above the fn) and the scaffold did not
    transcribe it. Both conjuncts are independently necessary; the two lemmas
    below refute the L5.3 Triple at a concrete instance of each, so this is a
    machine-checked counterexample rather than a report.

    * `specreq_L53_refuted_at_dv_zero` — at `V_COMPRESSION_FACTOR = 0` the impl's
      `match V_COMPRESSION_FACTOR as u32` falls through to `unreachable!()`, i.e.
      `fail panic`, and `⇓` is `PostCond.noThrow` (total), so the Triple is false
      for EVERY `K`, `serialized`, `output`.
    * `specreq_L53_refuted_at_dv_four_empty` — at `V_COMPRESSION_FACTOR = 4` with a
      zero-length `serialized` the impl SUCCEEDS (`specreq_L53_d4_empty_ok`:
      `chunks_exact 8` yields no chunk, so the loop returns `output` unchanged)
      while the spec's `byte_decode_dyn` asserts `len = 32 * d = 128` and returns
      `fail assertionFailure`. So the post is violated by a successful run — the
      length conjunct is not merely a totality side-condition.

    Nothing here edits, weakens, or hypothesises the locked statement; the `sorry`
    stands. See the SPECREQ in the dispatch report for the proposed pre. -/

section SpecreqL53

open libcrux_iot_ml_kem.Matrix.ComputeRingElementV.Impl

/-- `V_COMPRESSION_FACTOR = 0` takes the `unreachable!()` arm. -/
private theorem specreq_L53_dispatch_fail_of_dv_zero (K : Std.Usize)
    (serialized : Slice Std.U8)
    (output : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_v
      (vectortraitsOperationsInst := portable_ops_inst) K 0#usize serialized output
    = .fail .panic := by
  simp only [libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_v,
    Aeneas.Std.lift, Aeneas.Std.bind_tc_ok, Std.UScalar.cast, Std.UScalarTy.U32_numBits_eq]
  simp

/-- **Counterexample 1** — the L5.3 post-condition shape at `V_COMPRESSION_FACTOR = 0`
    is refutable for every `K`, `serialized`, `output`. -/
private theorem specreq_L53_refuted_at_dv_zero (K : Std.Usize) (serialized : Slice Std.U8)
    (output : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ¬ (⦃ ⌜ True ⌝ ⦄
       libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_v
         (vectortraitsOperationsInst := portable_ops_inst) K 0#usize serialized output
       ⦃ ⇓ p => ⌜ hacspec_ml_kem.serialize.deserialize_then_decompress_v serialized 0#usize
                   = .ok (lift_poly p) ⌝ ⦄) := by
  rw [specreq_L53_dispatch_fail_of_dv_zero]
  simp [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PostCond.noThrow, Std.Do.PredTrans.apply]

/-- `V_COMPRESSION_FACTOR = 4` dispatches to `deserialize_then_decompress_4`. -/
private theorem specreq_L53_dispatch_eq_d4 (K : Std.Usize) (serialized : Slice Std.U8)
    (output : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_v
      (vectortraitsOperationsInst := portable_ops_inst) K 4#usize serialized output
    = libcrux_iot_ml_kem.serialize.deserialize_then_decompress_4
        (vectortraitsOperationsInst := portable_ops_inst) serialized output := by
  simp only [libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_v,
    Aeneas.Std.lift, Aeneas.Std.bind_tc_ok, Std.UScalar.cast, Std.UScalarTy.U32_numBits_eq]
  simp

private theorem specreq_L53_slice_len_zero (sl : Slice Std.U8) (h : sl.val.length = 0) :
    CoreModels.core.slice.Slice.len sl = .ok (0#usize : Std.Usize) := by
  have hlen : Aeneas.Std.Slice.len sl = (0#usize : Std.Usize) := by
    refine Aeneas.Std.UScalar.eq_of_val_eq ?_
    rw [Aeneas.Std.Slice.len_val]
    show sl.val.length = ((0#usize : Std.Usize)).val
    rw [h]; scalar_tac
  simp only [CoreModels.core.slice.Slice.len, hlen]; rfl

/-- Spec side: `byte_decode_dyn` at `d = 4` asserts `len = 32 * 4 = 128`, so a
    zero-length input makes the whole spec chain fail. -/
private theorem specreq_L53_spec_fail_of_empty (serialized : Slice Std.U8)
    (h : serialized.val.length = 0) :
    hacspec_ml_kem.serialize.deserialize_then_decompress_v serialized 4#usize
      = .fail .assertionFailure := by
  obtain ⟨z, hz, hzv⟩ : ∃ z : Std.Usize,
      ((32#usize : Std.Usize) * (4#usize : Std.Usize) : Result Std.Usize) = .ok z
        ∧ z.val = 128 := by
    obtain ⟨z, hz, hv, _⟩ := Std.WP.spec_imp_exists (Std.UScalar.mul_bv_spec
      (x := (32#usize : Std.Usize)) (y := (4#usize : Std.Usize)) (by scalar_tac))
    exact ⟨z, hz, by rw [hv]; scalar_tac⟩
  have hne : (0#usize : Std.Usize) ≠ z := by
    intro hc; rw [← hc] at hzv; scalar_tac
  simp only [hacspec_ml_kem.serialize.deserialize_then_decompress_v,
    hacspec_ml_kem.serialize.byte_decode_dyn]
  simp [Aeneas.Std.massert, hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT,
    specreq_L53_slice_len_zero serialized h, hz, hne]

/-- Impl side at `d = 4` on a zero-length input: `chunks_exact 8` produces no
    chunk, so the loop returns `output` unchanged — the impl SUCCEEDS. -/
private theorem specreq_L53_d4_empty_ok (serialized : Slice Std.U8)
    (h : serialized.val.length = 0)
    (output : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_4
      (vectortraitsOperationsInst := portable_ops_inst) serialized output
    ⦃ ⇓ p => ⌜ (Aeneas.Std.Result.ok (p = output)).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_4
  rw [show (CoreModels.core.slice.Slice.chunks_exact serialized (8#usize : Std.Usize))
        = .ok { cs := 8#usize, elements := serialized } from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show (CoreModels.core.iter.traits.iterator.Iterator.enumerate.default
        (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice
          Std.U8)
        { cs := (8#usize : Std.Usize), elements := serialized })
      = .ok ({ iter := { cs := 8#usize, elements := serialized }, count := 0#usize } : EnumCE)
      from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_4_loop
  refine loop_chunks_exact_pk_spec _ output serialized 8#usize 0
    (fun _ acc => .ok (acc = output)) (by scalar_tac)
    (by simpa [Aeneas.Std.Slice.length] using h)
    ((holds_ok _).mpr rfl) ?_
  intro acc k rest cnt hk hcnt hrest hsuf hinv
  have hk0 : k = 0 := by omega
  subst hk0
  have hrest0 : rest.length = 0 := by rw [hrest]; simp
  refine triple_of_ok_fc (v := .done acc) ?_ ?_
  · show libcrux_iot_ml_kem.serialize.deserialize_then_decompress_4_loop.body
      portable_ops_inst { iter := { cs := 8#usize, elements := rest }, count := cnt } acc = _
    unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_4_loop.body
    rw [show (CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
          (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice
            Std.U8)
          { iter := { cs := 8#usize, elements := rest }, count := cnt })
        = .ok (CoreModels.core.option.Option.None,
               { iter := { cs := 8#usize, elements := rest }, count := cnt }) from
        enumerate_chunks_next_done rest 8#usize cnt (by rw [hrest0]; scalar_tac)]
    rfl
  · exact hinv

/-- **Counterexample 2** — at `V_COMPRESSION_FACTOR = 4` with `serialized.len() = 0`
    the impl returns `.ok output` while the spec returns `fail assertionFailure`,
    so the L5.3 post-condition shape is refutable. The length conjunct of the
    source's `requires` is therefore independently necessary. -/
private theorem specreq_L53_refuted_at_dv_four_empty (K : Std.Usize)
    (serialized : Slice Std.U8) (h : serialized.val.length = 0)
    (output : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ¬ (⦃ ⌜ True ⌝ ⦄
       libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_v
         (vectortraitsOperationsInst := portable_ops_inst) K 4#usize serialized output
       ⦃ ⇓ p => ⌜ hacspec_ml_kem.serialize.deserialize_then_decompress_v serialized 4#usize
                   = .ok (lift_poly p) ⌝ ⦄) := by
  intro hT
  obtain ⟨v, _, hpost⟩ := triple_exists_ok_fc hT
  rw [specreq_L53_spec_fail_of_empty serialized h] at hpost
  exact absurd hpost (by simp)

end SpecreqL53

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

/-! ### PROVER bank toward the POSITIVE L5.3 proof.

    The section above shows the locked L5.3 Triple is FALSE as written, so it is not
    closable. Everything here is stated UNDER the source's `#[hax_lib::requires]`
    (`ml-kem/src/serialize.rs` 337-340), i.e. it is what the RE-LOCKED obligation will
    need; nothing here is used by, weakens, or hypothesises the locked statement,
    which keeps its `sorry`.

    `specreq_L53_dispatch_eq_d4` (above) is the `d = 4` half of the first rung;
    `L53_dispatch_eq_d5` completes it, and `L53_dispatch_of_pre` is the rung itself:
    under the dv-conjunct the dispatcher reduces to exactly one of the two real arms,
    with the `unreachable!()` arm eliminated. `specreq_L53_d4_empty_ok` (above) is the
    reusable `cs = 8` instantiation of the `chunks_exact` loop combinator. What remains
    for the positive proof is the per-chunk commute work at `d = 4` (8 bytes → 16 lanes)
    and `d = 5` (10 bytes → 16 lanes), plus `Decompress_d`. -/

section L53Bank

/-- `V_COMPRESSION_FACTOR = 5` dispatches to `deserialize_then_decompress_5` — the
    `d = 5` companion of `specreq_L53_dispatch_eq_d4`. -/
private theorem L53_dispatch_eq_d5 (K : Std.Usize) (serialized : Slice Std.U8)
    (output : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_v
      (vectortraitsOperationsInst := portable_ops_inst) K 5#usize serialized output
    = libcrux_iot_ml_kem.serialize.deserialize_then_decompress_5
        (vectortraitsOperationsInst := portable_ops_inst) serialized output := by
  simp only [libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_v,
    Aeneas.Std.lift, Aeneas.Std.bind_tc_ok, Std.UScalar.cast, Std.UScalarTy.U32_numBits_eq]
  simp

/-- **First rung of the positive L5.3 proof**: under the dv-conjunct of the source's
    `requires`, the dispatcher reduces to exactly one of the two real arms — the
    `unreachable!()` arm that `specreq_L53_refuted_at_dv_zero` exploits is gone. -/
private theorem L53_dispatch_of_pre (K V_COMPRESSION_FACTOR : Std.Usize)
    (serialized : Slice Std.U8)
    (output : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_dv : V_COMPRESSION_FACTOR.val = 4 ∨ V_COMPRESSION_FACTOR.val = 5) :
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_v
      (vectortraitsOperationsInst := portable_ops_inst)
      K V_COMPRESSION_FACTOR serialized output
    = if V_COMPRESSION_FACTOR.val = 4 then
        libcrux_iot_ml_kem.serialize.deserialize_then_decompress_4
          (vectortraitsOperationsInst := portable_ops_inst) serialized output
      else
        libcrux_iot_ml_kem.serialize.deserialize_then_decompress_5
          (vectortraitsOperationsInst := portable_ops_inst) serialized output := by
  rcases h_dv with h | h
  · rw [show V_COMPRESSION_FACTOR = 4#usize from Aeneas.Std.UScalar.eq_of_val_eq (by scalar_tac),
      specreq_L53_dispatch_eq_d4]
    simp
  · rw [show V_COMPRESSION_FACTOR = 5#usize from Aeneas.Std.UScalar.eq_of_val_eq (by scalar_tac),
      L53_dispatch_eq_d5]
    simp

/-- Spec-side normal form: `deserialize_then_decompress_v` is `ByteDecode_dv` followed
    by `Decompress_dv`. Stated once so the positive proof never unfolds it inline. -/
private theorem L53_spec_unfold (s : Slice Std.U8) (dv : Std.Usize) :
    hacspec_ml_kem.serialize.deserialize_then_decompress_v s dv
    = (do let a ← hacspec_ml_kem.serialize.byte_decode_dyn s dv
          hacspec_ml_kem.compress.decompress a dv) := rfl

end L53Bank

/-! ### SPECREQ evidence for L5.4 (`compress_then_serialize_ring_element_v_fc`).

    L5.4 carries the SAME defect as L5.3, and it is the next obligation in the queue.
    Its source (`ml-kem/src/serialize.rs` 231-234) carries

        #[hax_lib::requires(
            out.len() == C2_LEN &&
            (V_COMPRESSION_FACTOR == 4 && C2_LEN == 128 ||
                V_COMPRESSION_FACTOR == 5 && C2_LEN == 160))]

    but the scaffold transcribed only the `out.len() == C2_LEN` conjunct (as the binder
    `h_len`). `compress_then_serialize_ring_element_v` dispatches on the same
    `match V_COMPRESSION_FACTOR as u32 { 4, 5, _ => unreachable!() }`, so
    `V_COMPRESSION_FACTOR = 0` refutes the L5.4 Triple by the identical argument.

    The refutation below carries L5.4's `h_len` binder, so it refutes the obligation in
    its own exact shape rather than a convenient variant: the dropped conjunct is not
    recoverable from the one the scaffold kept. The L5.3 dispatch above was proved with
    the same three-lemma `simp only` normal form, so this cost one rung, not a dispatch.

    This is evidence, not a statement edit: L5.4's `sorry` stands untouched. -/

section SpecreqL54

/-- `V_COMPRESSION_FACTOR = 0` takes the `unreachable!()` arm of the L5.4 dispatcher. -/
private theorem specreq_L54_dispatch_fail_of_dv_zero (K C2_LEN : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_v
      (vectortraitsOperationsInst := portable_ops_inst) K 0#usize C2_LEN re out scratch
    = .fail .panic := by
  simp only [libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_v,
    Aeneas.Std.lift, Aeneas.Std.bind_tc_ok, Std.UScalar.cast, Std.UScalarTy.U32_numBits_eq]
  simp

/-- **Counterexample (L5.4)** — the L5.4 post-condition shape at `V_COMPRESSION_FACTOR = 0`
    is refutable for every `K`, `C2_LEN`, `re`, `out`, `scratch`, INCLUDING under L5.4's
    own `h_len : out.length = C2_LEN.val` binder. -/
private theorem specreq_L54_refuted_at_dv_zero (K C2_LEN : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_len : out.length = C2_LEN.val) :
    ¬ (⦃ ⌜ True ⌝ ⦄
       libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_v
         (vectortraitsOperationsInst := portable_ops_inst) K 0#usize C2_LEN re out scratch
       ⦃ ⇓ p => ⌜ ∃ enc : Std.Array Std.U8 C2_LEN,
                    hacspec_ml_kem.serialize.compress_then_serialize_v
                        C2_LEN (lift_poly re) 0#usize
                      = .ok enc
                    ∧ p.1.length = C2_LEN.val
                    ∧ ∀ ℓ : Nat, ℓ < C2_LEN.val → p.1.val[ℓ]! = enc.val[ℓ]! ⌝ ⦄) := by
  rw [specreq_L54_dispatch_fail_of_dv_zero]
  simp [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PostCond.noThrow, Std.Do.PredTrans.apply]

end SpecreqL54

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

private theorem u16_add_ok (x y : Std.U16) (hb : x.val + y.val ≤ Std.U16.max) :
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

/-- Value of the `Usize` literal that `createi`/`from_fn_pure_eq` puts in the
    closure's index argument. Every closure normal form in this file needs this
    bridge (`LoopSpecs.bv_ofNat_val_eq` is `private` there), so it is stated once. -/
private theorem usize_ofNat_val (k : Nat) (h : k < 2 ^ 32) :
    ((⟨BitVec.ofNat _ k⟩ : Std.Usize)).val = k := by
  show (BitVec.ofNat _ k).toNat = k
  simp only [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have h32 : (32 : Nat) ≤ System.Platform.numBits := by
    have := System.Platform.numBits_eq; omega
  calc k < 2 ^ 32 := h
    _ ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) h32

/-- The `Slice.len` bridge at this layer's one length, `384`. Stated once in both
    the raw and the `Result` shape: `byte_decode_dyn`'s `try_from` needs the raw
    form for its `dif_pos`, and both entry points need the `Result` form. -/
private theorem slice_len_eq_384 (sl : Slice Std.U8) (h : sl.val.length = 384) :
    Aeneas.Std.Slice.len sl = (384#usize : Std.Usize) := by
  refine Aeneas.Std.UScalar.eq_of_val_eq ?_
  rw [Aeneas.Std.Slice.len_val]
  show sl.val.length = ((384#usize : Std.Usize)).val
  rw [h]; scalar_tac

private theorem slice_len_384 (sl : Slice Std.U8) (h : sl.val.length = 384) :
    CoreModels.core.slice.Slice.len sl = .ok (384#usize : Std.Usize) := by
  simp only [CoreModels.core.slice.Slice.len, slice_len_eq_384 sl h]
  rfl

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
      -- The extraction-coupled body walk, done ONCE for both bit branches: the
      -- `show (do …)` below is the only place in this proof that spells out the
      -- machine-generated `call_mut_loop.body` (skill §4.1 pitfall).
      have hbody :
          hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16.call_mut_loop.body
              (Nd := Nd) d a j ({ start := i, «end» := d } :
                CoreModels.core.ops.range.Range Std.Usize) acc
            = (if a.val[q.val]! = true then do
                  let i4 ← (1#u16 : Std.U16) <<< i
                  let coefficient1 ← acc + i4
                  Result.ok (ControlFlow.cont
                    ((⟨s, d⟩ : CoreModels.core.ops.range.Range Std.Usize), coefficient1))
                else Result.ok (ControlFlow.cont
                    ((⟨s, d⟩ : CoreModels.core.ops.range.Range Std.Usize), acc))) := by
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
        rw [hidx]; simp only [Aeneas.Std.bind_tc_ok]
      by_cases hb : a.val[q.val]! = true
      · obtain ⟨w, hw, hwv⟩ := u16_shl_one_ok i (by omega)
        have hlow : bitSum (fun t => a.val[j.val * d.val + t]!) i.val < 2 ^ i.val :=
          bitSum_lt _ _
        have hpow : (2:Nat) ^ i.val ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
        have h15 : (2:Nat) ^ 15 = 32768 := by norm_num
        obtain ⟨c2, hc2, hc2v⟩ := u16_add_ok acc w (by scalar_tac)
        refine triple_of_ok_fc
          (v := .cont (({ start := s, «end» := d } :
                          CoreModels.core.ops.range.Range Std.Usize), c2)) ?_ ?_
        · show
            hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16.call_mut_loop.body
              (Nd := Nd) d a j ({ start := i, «end» := d } :
                CoreModels.core.ops.range.Range Std.Usize) acc = _
          rw [hbody]; simp only [hb, if_true]
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
          rw [hbody]; simp only [hbf, Bool.false_eq_true, if_false]
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

private theorem u16OfNat_val (x : Nat) (h : x ≤ Std.U16.max) : (u16OfNat x).val = x := by
  have h' : x < 65536 := by scalar_tac
  show (BitVec.ofNat _ x).toNat = x
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by simpa [Std.UScalarTy.numBits] using h')

/-- Pure normal form of the `bitvector_to_bounded_ints` closure at index `k`. -/
private theorem bvb_closure_eq {N Nd : Std.Usize} (a : Std.Array Bool Nd)
    (d : Std.Usize) (k : Nat)
    (hd : d.val ≤ 16) (hk : k < 2 ^ 32)
    (hmul : k * d.val + d.val ≤ Std.Usize.max)
    (hbd : k * d.val + d.val ≤ Nd.val) :
    (hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16
        N Nd).call_mut (d, a) ⟨BitVec.ofNat _ k⟩
      = .ok (u16OfNat (bitSum (fun t => a.val[k * d.val + t]!) d.val), (d, a)) := by
  have hkv := usize_ofNat_val k hk
  obtain ⟨z, hz, hzv⟩ :=
    triple_exists_ok_fc (bvb_loop_fc a d ⟨BitVec.ofNat _ k⟩ hd
      (by rw [hkv]; exact hmul) (by rw [hkv]; exact hbd))
  have hzeq : z = u16OfNat (bitSum (fun t => a.val[k * d.val + t]!) d.val) := by
    refine Aeneas.Std.UScalar.eq_of_val_eq ?_
    have hlt : bitSum (fun t => a.val[k * d.val + t]!) d.val ≤ Std.U16.max := by
      have h1 := bitSum_lt (fun t => a.val[k * d.val + t]!) d.val
      have h2 : (2:Nat) ^ d.val ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) hd
      have h16 : (2:Nat) ^ 16 = 65536 := by norm_num
      scalar_tac
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
  scalar_tac

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
    (decoded : Std.Array Std.U16 256#usize) (k : Nat) (hk : k < 256) :
    (hacspec_ml_kem.serialize.byte_decode.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement
        D32 D256).call_mut decoded ⟨BitVec.ofNat _ k⟩
      = .ok (({ val := u16OfNat ((decoded.val[k]!).val % 3329) } :
                hacspec_ml_kem.parameters.FieldElement), decoded) := by
  have hkv := usize_ofNat_val k (by omega)
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
    rw [hrv, hq, u16OfNat_val _ (by scalar_tac)]
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
        rw [byte_decode_closure_eq decoded k hk256,
          lift_fe_of_nat _ (dec12 a.val k) hlane, hdecget k hk256])
  unfold hacspec_ml_kem.serialize.byte_decode
  simp only [hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT, Aeneas.Std.massert,
    le_refl, if_true, Aeneas.Std.bind_tc_ok, hslice,
    slice_len_384 ⟨a.val, by scalar_tac⟩ halen, e2, e4, hdec,
    hacspec_ml_kem.parameters.createi, hfn]
  rfl

/-! ### `byte_decode_dyn` at `d = 12` — the slice-shaped entry point. -/

private theorem byte_decode_dyn_12_eq (b : Slice Std.U8) (hb : b.val.length = 384)
    (p : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
           libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hp : declane b.val p 16) :
    hacspec_ml_kem.serialize.byte_decode_dyn b 12#usize = .ok (lift_poly p) := by
  have hl := slice_len_eq_384 b hb
  have hlen := slice_len_384 b hb
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


/-! ## PROVER bank for L5.1 — the message layer (`d = 1`).

    Port of `Hacspec_ml_kem.Commute.Chunk.fst`
    (`lemma_decompress_1_fe_commute`, `lemma_decompress_1_chunk_commutes`,
    `lemma_decompress_1_bound`) and of the `chunk_decompressed_d` /
    `lemma_chunk_decompressed_intro_1_post` atoms of
    `…Commute.Serialize_compress.fst`.

    At `d = 1` the bit algebra degenerates: a lane is ONE bit, so the pure
    normal form of both sides is `sliceBit` — already in the bank from L5.7.
    Following `Serialize_bits.fst`'s `chunk_decoded_12` discipline, the
    per-chunk bit equality lives behind the named `msglane` predicate and never
    enters the loop's residue. -/

section L51Bank

open Aeneas.Std
open libcrux_iot_ml_kem.Util.LoopSpecs

/-! ### Impl side — one bit lane, `as_i16 ((byte >> s) & 1)`. -/

private theorem uscalar_eq_of_bv {ty : Std.UScalarTy} {x y : Std.UScalar ty}
    (h : x.bv = y.bv) : x = y :=
  Std.UScalar.eq_of_val_eq (by show x.bv.toNat = y.bv.toNat; rw [h])

/-- The `I16` lane the impl writes for the low bit of `y`. -/
private def mraw (y : Std.U8) : Std.I16 := c16 (y &&& 1#u8)

private theorem u8_and1_val (y : Std.U8) : (y &&& 1#u8).val = y.val % 2 := by
  rw [Std.UScalar.val_and]
  have h1 : ((1#u8 : Std.U8).val) = 1 := rfl
  rw [h1]
  have h2 := Nat.and_two_pow_sub_one_eq_mod y.val 1
  rw [show (2:Nat) ^ 1 - 1 = 1 from rfl, show (2:Nat) ^ 1 = 2 from rfl] at h2
  exact h2

private theorem mraw_toNat (y : Std.U8) :
    (mraw y).bv.toNat = (if natBit y.val 0 then 1 else 0) := by
  unfold mraw
  rw [c16_bv_toNat, u8_and1_val]
  unfold natBit
  simp only [pow_zero, Nat.div_one]
  have : y.val % 2 < 2 := Nat.mod_lt _ (by omega)
  by_cases h : y.val % 2 = 1 <;> simp [h] <;> omega

private def shr8 (y : Std.U8) (s : Nat) : Std.U8 := ⟨BitVec.ushiftRight y.bv s⟩

private theorem shifted_val (y : Std.U8) (s : Nat) :
    (shr8 y s).val = y.val / 2 ^ s := by
  show (BitVec.ushiftRight y.bv s).toNat = _
  rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rfl

private theorem mraw_shift_toNat (y : Std.U8) (s : Nat) :
    (mraw (shr8 y s)).bv.toNat = (if natBit y.val s then 1 else 0) := by
  rw [mraw_toNat, shifted_val]
  unfold natBit
  simp only [pow_zero, Nat.div_one]

private theorem u8_shr_ok (x : Std.U8) (s : Std.I32) (k : Nat)
    (hsv : s.val = (k : Int)) (h8 : k < 8) :
    (x >>> s : Result Std.U8) = .ok (shr8 x k) := by
  have h0 : (0:Int) ≤ s.val := by rw [hsv]; exact Int.natCast_nonneg k
  have hk : Std.IScalar.toNat s = k := by
    show s.val.toNat = k
    rw [hsv]; exact Int.toNat_natCast k
  obtain ⟨z, hz, _hzv, hzbv⟩ :=
    Std.WP.spec_imp_exists
      (Std.UScalar.ShiftRight_IScalar_spec (ty0 := .U8) x s h0 (by rw [hsv]; simpa using h8))
  rw [hz]
  congr 1
  refine uscalar_eq_of_bv ?_
  show z.bv = BitVec.ushiftRight x.bv k
  rw [hzbv, hk]
  rfl

/-! ### Impl side — `deserialize_1` writes the 16 bits of a 2-byte chunk. -/

/-- The 16-lane array `deserialize_1` produces from bytes `x0`, `x1`. -/
private def dser1 (x0 x1 : Std.U8) (E : Std.Array Std.I16 16#usize) :
    Std.Array Std.I16 16#usize :=
  (((((((((((((((E.set 0#usize (mraw x0)).set 1#usize (mraw (shr8 x0 1))).set 2#usize (mraw (shr8 x0 2))).set 3#usize (mraw (shr8 x0 3))).set 4#usize (mraw (shr8 x0 4))).set 5#usize (mraw (shr8 x0 5))).set 6#usize (mraw (shr8 x0 6))).set 7#usize (mraw (shr8 x0 7))).set 8#usize (mraw x1)).set 9#usize (mraw (shr8 x1 1))).set 10#usize (mraw (shr8 x1 2))).set 11#usize (mraw (shr8 x1 3))).set 12#usize (mraw (shr8 x1 4))).set 13#usize (mraw (shr8 x1 5))).set 14#usize (mraw (shr8 x1 6))).set 15#usize (mraw (shr8 x1 7))

private theorem deserialize_1_eq (v : Slice Std.U8) (h : 2 ≤ v.val.length)
    (out : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    libcrux_iot_ml_kem.vector.portable.serialize.deserialize_1 v out
      = .ok { elements := dser1 v.val[0]! v.val[1]! out.elements } := by
  have hidx0 : Aeneas.Std.Slice.index_usize v 0#usize = .ok v.val[0]! :=
    slice_index_usize_eq v 0#usize (by simpa using (by omega : 0 < v.val.length))
  have hidx1 : Aeneas.Std.Slice.index_usize v 1#usize = .ok v.val[1]! :=
    slice_index_usize_eq v 1#usize (by simpa using (by omega : 1 < v.val.length))
  have hu0 := fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) =>
    array_update16 A 0#usize x (by scalar_tac)
  have hu1 := fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) =>
    array_update16 A 1#usize x (by scalar_tac)
  have hu2 := fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) =>
    array_update16 A 2#usize x (by scalar_tac)
  have hu3 := fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) =>
    array_update16 A 3#usize x (by scalar_tac)
  have hu4 := fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) =>
    array_update16 A 4#usize x (by scalar_tac)
  have hu5 := fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) =>
    array_update16 A 5#usize x (by scalar_tac)
  have hu6 := fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) =>
    array_update16 A 6#usize x (by scalar_tac)
  have hu7 := fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) =>
    array_update16 A 7#usize x (by scalar_tac)
  have hu8 := fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) =>
    array_update16 A 8#usize x (by scalar_tac)
  have hu9 := fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) =>
    array_update16 A 9#usize x (by scalar_tac)
  have hu10 := fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) =>
    array_update16 A 10#usize x (by scalar_tac)
  have hu11 := fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) =>
    array_update16 A 11#usize x (by scalar_tac)
  have hu12 := fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) =>
    array_update16 A 12#usize x (by scalar_tac)
  have hu13 := fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) =>
    array_update16 A 13#usize x (by scalar_tac)
  have hu14 := fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) =>
    array_update16 A 14#usize x (by scalar_tac)
  have hu15 := fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) =>
    array_update16 A 15#usize x (by scalar_tac)
  have hs1 := fun (y : Std.U8) => u8_shr_ok y 1#i32 1 (by scalar_tac) (by omega)
  have hs2 := fun (y : Std.U8) => u8_shr_ok y 2#i32 2 (by scalar_tac) (by omega)
  have hs3 := fun (y : Std.U8) => u8_shr_ok y 3#i32 3 (by scalar_tac) (by omega)
  have hs4 := fun (y : Std.U8) => u8_shr_ok y 4#i32 4 (by scalar_tac) (by omega)
  have hs5 := fun (y : Std.U8) => u8_shr_ok y 5#i32 5 (by scalar_tac) (by omega)
  have hs6 := fun (y : Std.U8) => u8_shr_ok y 6#i32 6 (by scalar_tac) (by omega)
  have hs7 := fun (y : Std.U8) => u8_shr_ok y 7#i32 7 (by scalar_tac) (by omega)
  unfold libcrux_iot_ml_kem.vector.portable.serialize.deserialize_1 dser1
  simp only [hidx0, hidx1, Aeneas.Std.lift, Aeneas.Std.bind_tc_ok, as_i16_eq,
    hs1, hs2, hs3, hs4, hs5, hs6, hs7,
    hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7, hu8, hu9, hu10, hu11, hu12, hu13, hu14, hu15, mraw]

/-- Lane `m` of a decoded 2-byte chunk is bit `m` of that chunk. -/
private theorem dser1_get (v : Slice Std.U8) (E : Std.Array Std.I16 16#usize)
    (m : Nat) (hm : m < 16) :
    ((dser1 v.val[0]! v.val[1]! E).val[m]!).bv.toNat
      = (if sliceBit v.val m then 1 else 0) := by
  have e0 : ∀ n : Nat, n < 8 → sliceBit v.val n = natBit (v.val[0]!).val n := by
    intro n hn
    unfold sliceBit
    rw [show n / 8 = 0 by omega, show n % 8 = n by omega]
  have e1 : ∀ n : Nat, 8 ≤ n → n < 16 → sliceBit v.val n = natBit (v.val[1]!).val (n - 8) := by
    intro n h1 h2
    unfold sliceBit
    rw [show n / 8 = 1 by omega, show n % 8 = n - 8 by omega]
  unfold dser1
  rw [set16_get (E := E) (k := m) (hk := hm)]
  interval_cases m
  · rw [e0 0 (by omega)]
    exact mraw_toNat _
  · rw [e0 1 (by omega)]
    exact mraw_shift_toNat _ 1
  · rw [e0 2 (by omega)]
    exact mraw_shift_toNat _ 2
  · rw [e0 3 (by omega)]
    exact mraw_shift_toNat _ 3
  · rw [e0 4 (by omega)]
    exact mraw_shift_toNat _ 4
  · rw [e0 5 (by omega)]
    exact mraw_shift_toNat _ 5
  · rw [e0 6 (by omega)]
    exact mraw_shift_toNat _ 6
  · rw [e0 7 (by omega)]
    exact mraw_shift_toNat _ 7
  · rw [e1 8 (by omega) (by omega)]
    exact mraw_toNat _
  · rw [e1 9 (by omega) (by omega)]
    exact mraw_shift_toNat _ 1
  · rw [e1 10 (by omega) (by omega)]
    exact mraw_shift_toNat _ 2
  · rw [e1 11 (by omega) (by omega)]
    exact mraw_shift_toNat _ 3
  · rw [e1 12 (by omega) (by omega)]
    exact mraw_shift_toNat _ 4
  · rw [e1 13 (by omega) (by omega)]
    exact mraw_shift_toNat _ 5
  · rw [e1 14 (by omega) (by omega)]
    exact mraw_shift_toNat _ 6
  · rw [e1 15 (by omega) (by omega)]
    exact mraw_shift_toNat _ 7

/-! ### Impl side — `decompress_1` = `negate` then `& 1665`.

    Port of `lemma_decompress_1_fe_commute` (`Commute.Chunk.fst`): the impl's
    branch-free `(-b) & 1665` realises `Decompress_1(b) = b * 1665`, and the
    bound `lemma_decompress_1_bound` is the `< 4096` fact used below to read the
    signed `.val` off the `BitVec`. -/

private theorem bv_eq_of_toNat {w : Nat} (x : BitVec w) (n : Nat) (hn : n < 2 ^ w)
    (h : x.toNat = n) : x = BitVec.ofNat w n := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa using hn)]

private theorem decompress_1_eq
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (b : Nat → Bool)
    (hb : ∀ m : Nat, m < 16 → (vec.elements.val[m]!).bv.toNat = (if b m then 1 else 0)) :
    ∃ w : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector,
      libcrux_iot_ml_kem.vector.traits.decompress_1 portable_ops_inst vec = .ok w
      ∧ ∀ m : Nat, m < 16 →
          (w.elements.val[m]!).bv.toNat = (if b m then 1665 else 0) := by
  obtain ⟨w1, hw1, hp1⟩ := triple_exists_ok_fc
    (libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.negate_spec vec)
  obtain ⟨w2, hw2, hp2⟩ := triple_exists_ok_fc
    (libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.bitwise_and_with_constant_spec
      w1 1665#i16)
  refine ⟨w2, ?_, ?_⟩
  · unfold libcrux_iot_ml_kem.vector.traits.decompress_1
    show (do
        let vec1 ← libcrux_iot_ml_kem.vector.portable.arithmetic.negate vec
        libcrux_iot_ml_kem.vector.portable.arithmetic.bitwise_and_with_constant vec1 1665#i16)
      = _
    rw [hw1]
    simpa only [Aeneas.Std.bind_tc_ok] using hw2
  · intro m hm
    rw [hp2 m hm, hp1 m hm]
    have h := hb m hm
    by_cases hbm : b m
    · rw [if_pos hbm] at h ⊢
      rw [bv_eq_of_toNat _ 1 (by decide) h]
      decide
    · rw [if_neg hbm] at h ⊢
      rw [bv_eq_of_toNat _ 0 (by decide) h]
      decide

/-- Re-indexing: bit `m` of the 2-byte chunk at offset `2i` is bit `16i+m` of `l`. -/
private theorem sliceBit_chunk (l c : List Std.U8) (i m : Nat) (hm : m < 16)
    (hc : ∀ t : Nat, t < 2 → c[t]! = l[2 * i + t]!) :
    sliceBit c m = sliceBit l (16 * i + m) := by
  unfold sliceBit
  rw [show (16 * i + m) / 8 = 2 * i + m / 8 by omega,
      show (16 * i + m) % 8 = m % 8 by omega,
      hc (m / 8) (by omega)]

/-! ### Impl side — the 16-iteration `0..16` range loop.

    Written-prefix invariant `msglane`: after `k` iterations the first `k`
    chunks carry `Decompress_1` of their bits. Cells `≥ k` are untouched by the
    invariant, and each iteration writes only cell `i`, so no
    "undone-cells-unchanged" conjunct is needed. -/

/-- Loop invariant / per-chunk atom (the `chunk_decompressed_1` of
    `Serialize_compress.fst`, kept behind a name so the bit equality never
    enters the loop residue). -/
private def msglane (l : List Std.U8)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (k : Nat) : Prop :=
  ∀ i : Nat, i < k → ∀ m : Nat, m < 16 →
    ((re.coefficients.val[i]!).elements.val[m]!).bv.toNat
      = (if sliceBit l (16 * i + m) then 1665 else 0)

private theorem message_loop_fc
    (serialized : Std.Array Std.U8 32#usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_message_loop
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := 0#usize, «end» := 16#usize } serialized re
    ⦃ ⇓ p => ⌜ (Aeneas.Std.Result.ok (msglane serialized.val p 16)).holds ⌝ ⦄ := by
  have hlen : serialized.val.length = 32 := by have := serialized.property; simpa using this
  have h16 : ((16#usize : Std.Usize)).val = 16 := by scalar_tac
  have h0 : ((0#usize : Std.Usize)).val = 0 := by scalar_tac
  have hproj :
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations.deserialize_1
        = libcrux_iot_ml_kem.vector.portable.serialize.deserialize_1 := rfl
  unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_message_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, re1) =>
        libcrux_iot_ml_kem.serialize.deserialize_then_decompress_message_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) serialized iter1 re1)
      re 0#usize 16#usize
      (fun k acc => .ok (msglane serialized.val acc k.val))
      (by scalar_tac)
      ((holds_ok _).mpr (by
        intro j hj
        rw [h0] at hj
        exact absurd hj (Nat.not_lt_zero j)))
      ?_)
  · rw [Std.Do.PostCond.entails_noThrow]
    intro r h
    rw [h16] at h
    exact h
  · intro acc i hge hle hinv
    have hinv' : msglane serialized.val acc i.val := (holds_ok _).mp hinv
    by_cases hlt : i.val < 16
    · obtain ⟨s, hs, hnext⟩ := iter_some_gen i 16#usize (by rw [h16]; exact hlt)
      obtain ⟨i1, hi1, hi1v⟩ := usize_mul_ok_e 2#usize i (by scalar_tac)
      obtain ⟨i2, hi2, hi2v⟩ := usize_add_ok_e i1 2#usize (by scalar_tac)
      have hi1v' : i1.val = 2 * i.val := by rw [hi1v]; scalar_tac
      have hi2v' : i2.val = 2 * i.val + 2 := by rw [hi2v, hi1v']; scalar_tac
      obtain ⟨ns, hns, hnslen, hnsget⟩ :=
        array_index_range_strict serialized i1 i2 (by omega) (by rw [hlen]; omega)
      have hnslen2 : ns.val.length = 2 := by rw [hnslen]; omega
      have hmut : ∀ (A : Std.Array
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize),
          Aeneas.Std.Array.index_mut_usize A i = .ok (A.val[i.val]!, Std.Array.set A i) := by
        intro A
        have hAl : A.val.length = 16 := by have := A.property; simpa using this
        have hA : i.val < A.val.length := by omega
        rw [array_index_mut16 A i hA, getElem!_pos A.val i.val hA]
      have hset_self : ∀ (A : Std.Array
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize)
          (x : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector),
          ((Std.Array.set A i x).val)[i.val]! = x := by
        intro A x
        rw [array_set_get16 A i x i.val hlt hlt, if_pos rfl]
      have hc : ∀ t : Nat, t < 2 → ns.val[t]! = serialized.val[2 * i.val + t]! := by
        intro t ht
        rw [hnsget t (by omega), hi1v']
      have hd1 : libcrux_iot_ml_kem.vector.portable.serialize.deserialize_1 ns
          (acc.coefficients.val[i.val]!)
          = .ok { elements := dser1 ns.val[0]! ns.val[1]!
                    (acc.coefficients.val[i.val]!).elements } :=
        deserialize_1_eq ns (by omega) _
      have hbit : ∀ m : Nat, m < 16 →
          ((({ elements := dser1 ns.val[0]! ns.val[1]!
                  (acc.coefficients.val[i.val]!).elements } :
              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector).elements.val[m]!)).bv.toNat
            = (if (fun m => sliceBit serialized.val (16 * i.val + m)) m then 1 else 0) := by
        intro m hm
        show ((dser1 ns.val[0]! ns.val[1]!
                (acc.coefficients.val[i.val]!).elements).val[m]!).bv.toNat = _
        rw [dser1_get ns (acc.coefficients.val[i.val]!).elements m hm,
          sliceBit_chunk serialized.val ns.val i.val m hm hc]
      obtain ⟨t3, hdec, hdecget⟩ :=
        decompress_1_eq _ (fun m => sliceBit serialized.val (16 * i.val + m)) hbit
      refine triple_of_ok_fc
        (v := .cont (({ start := s, «end» := 16#usize } :
                        CoreModels.core.ops.range.Range Std.Usize),
                     ({ coefficients := Std.Array.set (Std.Array.set acc.coefficients i
                          { elements := dser1 ns.val[0]! ns.val[1]!
                              (acc.coefficients.val[i.val]!).elements }) i t3 } :
                        libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))) ?_ ?_
      · show libcrux_iot_ml_kem.serialize.deserialize_then_decompress_message_loop.body
            (vectortraitsOperationsInst := portable_ops_inst) serialized
            ({ start := i, «end» := 16#usize } :
               CoreModels.core.ops.range.Range Std.Usize) acc = _
        unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_message_loop.body
        rw [hnext]
        show (do
            let i1 ← (2#usize : Std.Usize) * i
            let i2 ← i1 + (2#usize : Std.Usize)
            let sl ← CoreModels.core.Array.Insts.CoreOpsIndexIndex.index
                (CoreModels.core.Slice.Insts.CoreOpsIndexIndex
                  (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                    Std.U8)) serialized { start := i1, «end» := i2 }
            let (t, index_mut_back) ← Aeneas.Std.Array.index_mut_usize acc.coefficients i
            let t1 ← libcrux_iot_ml_kem.vector.portable.serialize.deserialize_1 sl t
            let (t2, index_mut_back1) ← Aeneas.Std.Array.index_mut_usize (index_mut_back t1) i
            let t3 ← libcrux_iot_ml_kem.vector.traits.decompress_1 portable_ops_inst t2
            Result.ok (ControlFlow.cont
              (({ start := s, «end» := 16#usize } :
                  CoreModels.core.ops.range.Range Std.Usize),
               ({ coefficients := index_mut_back1 t3 } :
                  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)))) = _
        simp only [Aeneas.Std.bind_tc_ok, hi1, hi2, hns, hmut, hd1, hset_self, hdec]
      · refine ⟨by rw [h16]; exact hlt, rfl, hs, (holds_ok _).mpr ?_⟩
        show msglane serialized.val _ s.val
        intro j hj m hm
        rw [hs] at hj
        by_cases hje : j = i.val
        · subst hje
          show ((((Std.Array.set (Std.Array.set acc.coefficients i _) i t3)).val[i.val]!).elements.val[m]!).bv.toNat = _
          rw [hset_self]
          exact hdecget m hm
        · show ((((Std.Array.set (Std.Array.set acc.coefficients i _) i t3)).val[j]!).elements.val[m]!).bv.toNat = _
          rw [array_set_get16 _ i t3 j (by omega) hlt, if_neg hje,
            array_set_get16 _ i _ j (by omega) hlt, if_neg hje]
          exact hinv' j (by omega) m hm
    · have hieq : i.val = 16 := by rw [h16] at hle; omega
      refine triple_of_ok_fc (v := .done acc) ?_ ?_
      · show libcrux_iot_ml_kem.serialize.deserialize_then_decompress_message_loop.body
            (vectortraitsOperationsInst := portable_ops_inst) serialized
            ({ start := i, «end» := 16#usize } :
               CoreModels.core.ops.range.Range Std.Usize) acc = _
        unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_message_loop.body
        rw [iter_none_gen i 16#usize (by rw [h16]; omega)]
        rfl
      · refine (holds_ok _).mpr ?_
        show msglane serialized.val acc ((16#usize : Std.Usize)).val
        rw [h16, ← hieq]
        exact hinv'

/-! ### Impl side — the apex. -/

private theorem message_impl_fc
    (serialized : Std.Array Std.U8 32#usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_message
      (vectortraitsOperationsInst := portable_ops_inst) serialized re
    ⦃ ⇓ p => ⌜ (Aeneas.Std.Result.ok (msglane serialized.val p 16)).holds ⌝ ⦄ :=
  message_loop_fc serialized re

/-! ### Spec side — `bytes_to_bits` at the message length (32 bytes → 256 bits).

    Same ladder as the `d = 12` bank above, re-derived at this layer's lengths;
    the pure normal form of the closure is again `sliceBit`. -/

private theorem bytes_to_bits_closure_eq_32 (a : Std.Array Std.U8 32#usize) (k : Nat)
    (hk : k < 256) :
    (hacspec_ml_kem.serialize.bytes_to_bits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBool
        32#usize 256#usize).call_mut a ⟨BitVec.ofNat _ k⟩
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
    have ha : a.val.length = 32 := by have := a.property; simpa using this
    rw [ha, hq16]; omega
  have hidx : Aeneas.Std.Array.index_usize a q = .ok (a.val[q.val]!) :=
    array_index_ok a q hqlt
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

private theorem bytes_to_bits_get_32 (a : Std.Array Std.U8 32#usize) :
    ∃ bv : Std.Array Bool 256#usize,
      hacspec_ml_kem.serialize.bytes_to_bits (N := 32#usize) 256#usize a = .ok bv
      ∧ ∀ m : Nat, m < 256 → bv.val[m]! = sliceBit a.val m := by
  have hmul : ((32#usize : Std.Usize) * (8#usize : Std.Usize) : Aeneas.Std.Result Std.Usize)
      = .ok (256#usize : Std.Usize) :=
    usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have h256 : ((256#usize : Std.Usize)).val = 256 := by scalar_tac
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq (T := Bool)
      (256#usize : Std.Usize)
      (hacspec_ml_kem.serialize.bytes_to_bits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBool
        32#usize 256#usize) a (fun m => sliceBit a.val m)
      (fun k hk => bytes_to_bits_closure_eq_32 a k (by rw [h256] at hk; exact hk))
  have key : hacspec_ml_kem.serialize.bytes_to_bits (N := 32#usize) 256#usize a
      = CoreModels.core.array.from_fn (256#usize : Std.Usize)
          (hacspec_ml_kem.serialize.bytes_to_bits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBool
            32#usize 256#usize) a := by
    unfold hacspec_ml_kem.serialize.bytes_to_bits
    rw [hmul]
    simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.massert,
      hacspec_ml_kem.parameters.createi, if_true, Aeneas.Std.bind_tc_ok]
  rw [key, hfn]
  refine ⟨_, rfl, ?_⟩
  intro m hm
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by rw [h256]; exact hm)]
  rfl

/-! ### Spec side — `bitvector_to_bounded_ints` at `d = 1`.

    The `d`-step accumulator loop `bvb_loop_fc` is `d`-generic, so this is just
    its `d = 1` instance: the lane IS the bit. -/

private theorem bvb_256_1_get (bv : Std.Array Bool 256#usize) :
    ∃ arr : Std.Array Std.U16 256#usize,
      hacspec_ml_kem.serialize.bitvector_to_bounded_ints 256#usize bv 1#usize = .ok arr
      ∧ ∀ k : Nat, k < 256 → (arr.val[k]!).val = (if bv.val[k]! then 1 else 0) := by
  have h256 : ((256#usize : Std.Usize)).val = 256 := by scalar_tac
  have h1 : ((1#usize : Std.Usize)).val = 1 := by scalar_tac
  have hmul : ((256#usize : Std.Usize) * (1#usize : Std.Usize) : Result Std.Usize)
      = .ok (256#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq (T := Std.U16)
      (256#usize : Std.Usize)
      (hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16
        256#usize 256#usize)
      ((1#usize : Std.Usize), bv)
      (fun k => u16OfNat (bitSum (fun t => bv.val[k * 1 + t]!) 1))
      (fun k hk => by
        rw [h256] at hk
        have := bvb_closure_eq (N := 256#usize) bv (1#usize) k
          (by rw [h1]; omega) (by omega) (by rw [h1]; scalar_tac)
          (by rw [h1, h256]; omega)
        rw [h1] at this
        exact this)
  have key : hacspec_ml_kem.serialize.bitvector_to_bounded_ints 256#usize bv 1#usize
      = CoreModels.core.array.from_fn (256#usize : Std.Usize)
          (hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16
            256#usize 256#usize)
          ((1#usize : Std.Usize), bv) := by
    unfold hacspec_ml_kem.serialize.bitvector_to_bounded_ints
    rw [hmul]
    simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.massert,
      hacspec_ml_kem.parameters.createi, if_true, Aeneas.Std.bind_tc_ok]
  rw [key, hfn]
  refine ⟨_, rfl, ?_⟩
  intro k hk
  have hget : ((List.range ((256#usize : Std.Usize)).val).map
      (fun k => u16OfNat (bitSum (fun t => bv.val[k * 1 + t]!) 1)))[k]!
      = u16OfNat (bitSum (fun t => bv.val[k * 1 + t]!) 1) := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by rw [h256]; exact hk)]
    rfl
  have hb : bitSum (fun t => bv.val[k * 1 + t]!) 1 = (if bv.val[k]! then 1 else 0) := by
    simp [bitSum]
  show (((List.range ((256#usize : Std.Usize)).val).map
      (fun k => u16OfNat (bitSum (fun t => bv.val[k * 1 + t]!) 1)))[k]!).val = _
  rw [hget, hb]
  refine u16OfNat_val _ ?_
  split <;> scalar_tac

/-! ### Spec side — `byte_decode_generic` and `byte_decode` at `d = 1`. -/

private theorem byte_decode_generic_1_get (a : Std.Array Std.U8 32#usize) :
    ∃ arr : Std.Array Std.U16 256#usize,
      hacspec_ml_kem.serialize.byte_decode_generic 32#usize 256#usize
          (Nd := 32#usize) 256#usize a 1#usize = .ok arr
      ∧ ∀ k : Nat, k < 256 → (arr.val[k]!).val = (if sliceBit a.val k then 1 else 0) := by
  obtain ⟨bv, hbv, hbvget⟩ := bytes_to_bits_get_32 a
  obtain ⟨arr, harr, harrget⟩ := bvb_256_1_get bv
  have hle : ((1#usize : Std.Usize) ≤ (12#usize : Std.Usize)) := by scalar_tac
  have e1 : ((32#usize : Std.Usize) * (8#usize : Std.Usize) : Result Std.Usize)
      = .ok (256#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have e2 : ((32#usize : Std.Usize) * (1#usize : Std.Usize) : Result Std.Usize)
      = .ok (32#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  refine ⟨arr, ?_, ?_⟩
  · unfold hacspec_ml_kem.serialize.byte_decode_generic
    simp only [hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT, Aeneas.Std.massert,
      if_pos hle, Aeneas.Std.bind_tc_ok, e1, e2, if_true, hbv, harr]
  · intro k hk
    rw [harrget k hk, hbvget k hk]

private theorem byte_decode_1_get (a : Std.Array Std.U8 32#usize) :
    ∃ arr : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize,
      hacspec_ml_kem.serialize.byte_decode (D32 := 32#usize) 256#usize a 1#usize = .ok arr
      ∧ ∀ k : Nat, k < 256 →
          arr.val[k]! = { val := u16OfNat (if sliceBit a.val k then 1 else 0) } := by
  obtain ⟨decoded, hdec, hdecget⟩ := byte_decode_generic_1_get a
  have hle : ((1#usize : Std.Usize) ≤ (12#usize : Std.Usize)) := by scalar_tac
  have h256 : ((256#usize : Std.Usize)).val = 256 := by scalar_tac
  have e2 : ((32#usize : Std.Usize) * (1#usize : Std.Usize) : Result Std.Usize)
      = .ok (32#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have e4 : ((256#usize : Std.Usize) * (1#usize : Std.Usize) : Result Std.Usize)
      = .ok (256#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have halen : a.val.length = 32 := by have := a.property; simpa using this
  have hslice : (Aeneas.Std.lift (Aeneas.Std.Array.to_slice a) : Result (Slice Std.U8))
      = .ok ⟨a.val, by scalar_tac⟩ := by
    simp [Aeneas.Std.lift, Aeneas.Std.Array.to_slice]
  have hlen32 : CoreModels.core.slice.Slice.len (⟨a.val, by scalar_tac⟩ : Slice Std.U8)
      = .ok (32#usize : Std.Usize) := by
    have : Aeneas.Std.Slice.len (⟨a.val, by scalar_tac⟩ : Slice Std.U8)
        = (32#usize : Std.Usize) := by
      refine Aeneas.Std.UScalar.eq_of_val_eq ?_
      rw [Aeneas.Std.Slice.len_val]
      show a.val.length = ((32#usize : Std.Usize)).val
      rw [halen]; scalar_tac
    simp only [CoreModels.core.slice.Slice.len, this]
    rfl
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
      (T := hacspec_ml_kem.parameters.FieldElement)
      (256#usize : Std.Usize)
      (hacspec_ml_kem.serialize.byte_decode.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement
        32#usize 256#usize)
      decoded
      (fun k => ({ val := u16OfNat (if sliceBit a.val k then 1 else 0) } :
                  hacspec_ml_kem.parameters.FieldElement))
      (fun k hk => by
        have hk256 : k < 256 := by rw [h256] at hk; exact hk
        rw [byte_decode_closure_eq decoded k hk256, hdecget k hk256]
        congr 2
        split <;> norm_num)
  refine ⟨⟨(List.range ((256#usize : Std.Usize)).val).map
      (fun k => ({ val := u16OfNat (if sliceBit a.val k then 1 else 0) } :
        hacspec_ml_kem.parameters.FieldElement)),
      by simp [List.length_map, List.length_range]⟩, ?_, ?_⟩
  · unfold hacspec_ml_kem.serialize.byte_decode
    simp only [hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT, Aeneas.Std.massert,
      if_pos hle, Aeneas.Std.bind_tc_ok, hslice, hlen32, e2, e4, if_true, hdec,
      hacspec_ml_kem.parameters.createi, hfn]
  · intro k hk
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by rw [h256]; exact hk)]
    rfl

/-! ### Spec side — `Decompress_1` as `b ↦ b * 1665`.

    Port of `lemma_decompress_1_fe_commute` (`Commute.Chunk.fst`). The spec's
    `decompress_d` is the FIPS-203 rounding formula
    `⌊(2·fe·q + 2^d) / 2^(d+1)⌉`; at `d = 1` and `fe ∈ {0,1}` it collapses to
    `(6658·fe + 2) / 4 = 1665·fe`, which is exactly the impl's `(-b) & 1665`
    (`decompress_1_eq` above). Every intermediate is kept SYMBOLIC in `Nat`:
    `2 ^ d` never becomes a closed large scalar. -/

private theorem u32_mul_ok (x y : Std.U32) (hb : x.val * y.val ≤ Std.U32.max) :
    ∃ z : Std.U32, (x * y : Result Std.U32) = .ok z ∧ z.val = x.val * y.val := by
  obtain ⟨z, hz, hv, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.mul_bv_spec (x := x) (y := y) (by scalar_tac))
  exact ⟨z, hz, hv⟩

private theorem u32_add_ok (x y : Std.U32) (hb : x.val + y.val ≤ Std.U32.max) :
    ∃ z : Std.U32, (x + y : Result Std.U32) = .ok z ∧ z.val = x.val + y.val := by
  obtain ⟨z, hz, hv, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.add_bv_spec (x := x) (y := y) (by scalar_tac))
  exact ⟨z, hz, hv⟩

private theorem u32_div_ok (x y : Std.U32) (hy : 0 < y.val) :
    ∃ z : Std.U32, (x / y : Result Std.U32) = .ok z ∧ z.val = x.val / y.val := by
  obtain ⟨z, hz, hv⟩ := Std.UScalar.div_spec (ty := .U32) x (y := y) (by omega)
  exact ⟨z, hz, hv⟩

/-- `Decompress_1(b) = 1665 · b` for `b ∈ {0,1}` — the spec-side half of
    `lemma_decompress_1_fe_commute`. -/
private theorem decompress_d_1_eq (fe : hacspec_ml_kem.parameters.FieldElement)
    (hfe : fe.val.val < 2) :
    hacspec_ml_kem.compress.decompress_d fe 1#usize
      = .ok { val := u16OfNat (fe.val.val * 1665) } := by
  obtain ⟨t2, hshl, hshlv⟩ := u16_shl_one_ok (1#usize) (by scalar_tac)
  have h1u : ((1#usize : Std.Usize)).val = 1 := by scalar_tac
  have ht2 : t2.val = 2 := by rw [hshlv, h1u]; norm_num
  have hass1 : ((1#usize : Std.Usize) < (12#usize : Std.Usize)) := by scalar_tac
  have hass2 : fe.val < t2 := by
    have : fe.val.val < t2.val := by omega
    scalar_tac
  have hc1 : Std.UScalar.cast .U32 (1#usize : Std.Usize) = (1#u32 : Std.U32) := by
    refine Std.UScalar.eq_of_val_eq ?_
    rw [Std.UScalar.cast_val_eq, h1u]; scalar_tac
  have hc3329 : Std.UScalar.cast .U32 (3329#u16 : Std.U16) = (3329#u32 : Std.U32) := by
    refine Std.UScalar.eq_of_val_eq ?_
    rw [Std.UScalar.cast_val_eq]; scalar_tac
  have hcfe : (Std.UScalar.cast .U32 fe.val).val = fe.val.val := by
    rw [Std.UScalar.cast_val_eq]; scalar_tac
  have hpow : CoreModels.core.num.U32.pow 2#u32 (1#u32 : Std.U32) = .ok (2#u32 : Std.U32) := rfl
  have h2 : ((2#u32 : Std.U32)).val = 2 := by scalar_tac
  have h3329 : ((3329#u32 : Std.U32)).val = 3329 := by scalar_tac
  obtain ⟨i3, hi3, hi3v⟩ := u32_mul_ok 2#u32 (Std.UScalar.cast .U32 fe.val) (by
    rw [hcfe, h2]; scalar_tac)
  obtain ⟨i5, hi5, hi5v⟩ := u32_mul_ok i3 3329#u32 (by
    rw [hi3v, hcfe, h2, h3329]; scalar_tac)
  obtain ⟨num, hnum, hnumv⟩ := u32_add_ok i5 2#u32 (by
    rw [hi5v, hi3v, hcfe, h2, h3329]; scalar_tac)
  obtain ⟨i6, hi6, hi6v⟩ := u32_mul_ok 2#u32 2#u32 (by rw [h2]; scalar_tac)
  obtain ⟨dec, hdec, hdecv⟩ := u32_div_ok num i6 (by rw [hi6v, h2]; omega)
  have hdecv' : dec.val = fe.val.val * 1665 := by
    rw [hdecv, hnumv, hi5v, hi3v, hcfe, hi6v, h2, h3329]
    omega
  have hfinal : Std.UScalar.cast .U16 dec = u16OfNat (fe.val.val * 1665) := by
    refine Std.UScalar.eq_of_val_eq ?_
    rw [Std.UScalar.cast_val_eq, u16OfNat_val _ (by rw [← hdecv']; scalar_tac), hdecv']
    have h16 : (Std.UScalarTy.U16).numBits = 16 := rfl
    rw [h16]
    exact Nat.mod_eq_of_lt (by omega)
  unfold hacspec_ml_kem.compress.decompress_d
  simp only [Aeneas.Std.massert, hacspec_ml_kem.parameters.FIELD_MODULUS,
    hacspec_ml_kem.parameters.FieldElement.new, Aeneas.Std.lift,
    Aeneas.Std.bind_tc_ok, hshl, if_pos hass1, if_pos hass2, hc1, hc3329, hpow,
    hi3, hi5, hnum, hi6, hdec, hfinal]

/-- The `decompress` `createi` closure at `d = 1`, index `k`. -/
private theorem decompress_closure_1_eq
    (arr : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (k : Nat) (hk : k < 256) (b : Nat) (hb : b < 2)
    (hval : (arr.val[k]!).val.val = b) :
    (hacspec_ml_kem.compress.decompress.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement).call_mut
        ((arr, 1#usize) : hacspec_ml_kem.compress.decompress.closure)
        (⟨BitVec.ofNat _ k⟩ : Std.Usize)
      = .ok (({ val := u16OfNat (b * 1665) } : hacspec_ml_kem.parameters.FieldElement),
             ((arr, 1#usize) : hacspec_ml_kem.compress.decompress.closure)) := by
  have hkv := usize_ofNat_val k (by omega)
  have hlen : arr.val.length = 256 := by have := arr.property; simpa using this
  have hidx : Aeneas.Std.Array.index_usize arr (⟨BitVec.ofNat _ k⟩ : Std.Usize)
      = .ok (arr.val[k]!) := by
    have := array_index_ok arr (⟨BitVec.ofNat _ k⟩ : Std.Usize) (by rw [hkv, hlen]; exact hk)
    rw [hkv] at this; exact this
  have hdd := decompress_d_1_eq (arr.val[k]!) (by rw [hval]; exact hb)
  rw [hval] at hdd
  show (do
      let fe ← Aeneas.Std.Array.index_usize arr (⟨BitVec.ofNat _ k⟩ : Std.Usize)
      let fe1 ← hacspec_ml_kem.compress.decompress_d fe (1#usize : Std.Usize)
      Result.ok (fe1, ((arr, 1#usize) : hacspec_ml_kem.compress.decompress.closure))) = _
  rw [hidx]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hdd]; simp only [Aeneas.Std.bind_tc_ok]; rfl

/-! ### The `lift` seam at `d = 1`: an impl lane of `1665·b` IS `Decompress_1(b)`.

    Impl-side normal form is `bv.toNat ∈ {0, 1665}` (`decompress_1_eq`); the
    spec-side normal form is `FieldElement.new (1665·b)`. Both are below `q`, so
    the canonical-residue projection of `lift_fe` is the identity here. -/

private theorem lift_fe_of_toNat (lane : Std.I16) (n : Nat) (hn : n < 3329)
    (h : lane.bv.toNat = n) :
    lift_fe lane = { val := u16OfNat n } := by
  have hlt : lane.bv.toNat < 4096 := by rw [h]; omega
  rw [lift_fe_of_nat lane n (by rw [i16_val_of_toNat lane hlt, h]),
    Nat.mod_eq_of_lt hn]

/-- **The apex, spec side**: `byte_decode 256 · 1` followed by `Decompress_1`
    reproduces `lift_poly p` whenever `p`'s lanes hold `1665 ·` the message bit. -/
private theorem message_spec_eq
    (serialized : Std.Array Std.U8 32#usize)
    (p : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
           libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hp : msglane serialized.val p 16) :
    hacspec_ml_kem.serialize.deserialize_then_decompress_message serialized
      = .ok (lift_poly p) := by
  obtain ⟨arr, harr, harrget⟩ := byte_decode_1_get serialized
  have h256 : ((256#usize : Std.Usize)).val = 256 := by scalar_tac
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
      (T := hacspec_ml_kem.parameters.FieldElement)
      (256#usize : Std.Usize)
      hacspec_ml_kem.compress.decompress.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement
      ((arr, 1#usize) : hacspec_ml_kem.compress.decompress.closure)
      (fun k => lift_fe (p.coefficients.val[k / 16]!).elements.val[k % 16]!)
      (fun k hk => by
        have hk256 : k < 256 := by rw [h256] at hk; exact hk
        -- the spec lane holds the raw bit …
        have hbitval : (arr.val[k]!).val.val
            = (if sliceBit serialized.val k then 1 else 0) := by
          rw [harrget k hk256]
          exact u16OfNat_val _ (by split <;> scalar_tac)
        -- … and the impl lane holds `1665 ·` it.
        have hlane : ((p.coefficients.val[k / 16]!).elements.val[k % 16]!).bv.toNat
            = (if sliceBit serialized.val k then 1665 else 0) := by
          have := hp (k / 16) (by omega) (k % 16) (by omega)
          rw [show 16 * (k / 16) + k % 16 = k from by omega] at this
          exact this
        rw [decompress_closure_1_eq arr k hk256 _ (by split <;> omega) hbitval,
          lift_fe_of_toNat _ _ (by split <;> omega) hlane]
        congr 2
        split <;> norm_num)
  unfold hacspec_ml_kem.serialize.deserialize_then_decompress_message
  rw [harr]
  simp only [Aeneas.Std.bind_tc_ok, hacspec_ml_kem.compress.decompress,
    hacspec_ml_kem.parameters.createi, hfn]
  rfl

end L51Bank

/-- L5.1 — `serialize.deserialize_then_decompress_message`.

    FIPS-203 message decode: 32 bytes → 256 coefficients, each bit `b` mapped to
    `Decompress_1(b)`. The hacspec counterpart takes the same fixed-size 32-byte
    array and returns the ring element directly, so the binding is exact: no
    length side conditions, no chunk indexing.

    Stated after the `L51Bank` section so the two halves it assembles —
    `message_impl_fc` (the 16-chunk `deserialize_1`/`decompress_1` loop) and
    `message_spec_eq` (`ByteDecode_1` ∘ `Decompress_1`) — are already in scope. -/
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
  -- Impl side: the 16-chunk loop puts `1665 · bit` in every lane.
  obtain ⟨p, hp_eq, hp⟩ := triple_exists_ok_fc (message_impl_fc serialized re)
  -- Spec side: `ByteDecode_1` then `Decompress_1` reproduces exactly those lanes.
  exact triple_of_ok_fc hp_eq (message_spec_eq serialized p ((holds_ok _).mp hp))

end libcrux_iot_ml_kem.SerializeFc
