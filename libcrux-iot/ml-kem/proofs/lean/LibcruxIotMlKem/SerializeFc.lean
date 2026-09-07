/-
  # `SerializeFc.lean` — INC-1 obligation stubs for the (de)serialize layer.

  **All seven INC-1 obligations in this file are PROVED as of 2026-08-19.** (It was a
  scaffold when written; the header said so, and said so for one commit too long — the last
  close is what made it false.) As of 2026-08-20 the file carries the two INC-2a `_u`
  per-element obligations at the bottom, and **BOTH are PROVED as of 2026-08-20**, each
  axiom-clean `[propext, Classical.choice, Quot.sound]`:
  `deserialize_then_decompress_ring_element_u_fc` on the `LuBank` section that precedes it,
  and `compress_then_serialize_ring_element_u_fc` on `LuEncBank`. This file is now
  sorry-free throughout. Nothing above them was affected by either close.

  The obligations were authored by the HELPER as a *low-distance binding* to the EXISTING
  `HacspecMlKem` model (skill §0.2) — nothing here invents a spec — then frozen by the
  PRINCIPAL and locked signature-by-signature by the driver, which byte-compares each
  statement on every rung. Six are axiom-clean `[propext, Classical.choice, Quot.sound]`;
  `deserialize_ring_elements_reduced_fc` additionally rests on the A2 axiom
  `Serialize.deserialize_to_reduced_ring_element_fc` BY DESIGN (retiring it is item M-A),
  and that is its declared allowlist, not a gap. `AxiomCheck.lean` asserts the
  sorry-freedom of each, so a regression fails the build rather than being noticed later.

  Shape follows the tree's established convention (see `Matrix/ComputeAsPlusE.lean`,
  `Serialize.lean`): an mvcgen Triple whose post equates the hacspec model applied
  to `lift`ed inputs with `.ok` of the `lift`ed impl result.

      ⦃ ⌜pre⌝ ⦄  <impl call>  ⦃ ⇓ p => ⌜ <hacspec> (lift args…) = .ok (lift p…) ⌝ ⦄

  ## Scope of THIS file

  Only the bindings where the impl function and a hacspec function correspond
  1:1, so the statement is mechanical. Deliberately NOT scaffolded here, because
  each needs a PRINCIPAL decision rather than a transcription — see the campaign
  STATE.md (P7):

  * ~~`compress_then_serialize_ring_element_u` / `deserialize_then_decompress_ring_element_u`~~
    — **RETIRED 2026-08-20, and the reasoning below was WRONG.** It said the hacspec offers
    only whole-vector `_u` functions, so binding the per-element impl was a modelling choice.
    That compared ARITIES and never checked width-genericity: `deserialize_then_decompress_v`
    / `compress_then_serialize_v` take the width as a RUNTIME parameter and ARE the
    per-element `_u` operations — as upstream's own `#[hax_lib::ensures]` on the two
    per-element `_u` functions says in so many words. Both were scaffolded and CLOSED on
    2026-08-20, axiom-clean. See `plans/INC-2-scope.md` §9 and the section note there.
  * `compress_then_serialize_{4,5,10,11}` / `deserialize_then_decompress_{4,5,10,11}`
    — impl-internal specializations of a `d`-parametric operation. No named
    hacspec counterpart; they are step lemmas feeding the `_u`/`_v` apexes above and are
    proved as private banks inside those obligations, not as obligations of their own. The
    banks, by direction and width: `L53Bank2` (decode, d ∈ {4,5}), `L54Bank` (encode,
    d ∈ {4,5}), `LuBank` (decode, d ∈ {10,11}), `LuEncBank` (encode, d ∈ {10,11}). All four
    widths are covered in both directions; be precise about WHICH bank when you cite one —
    an earlier form of this bullet named `LuBank` for both directions, which was false while
    only the decode half existed.
  * `to_unsigned_field_modulus` — an impl-internal helper with no spec image.
-/

import LibcruxIotMlKem.Spec.Lift
import LibcruxIotMlKem.Serialize
import LibcruxIotMlKem.Util.CreateI
import LibcruxIotMlKem.Util.LoopSpecs
import LibcruxIotMlKem.Matrix.ComputeRingElementV.Impl
import LibcruxIotMlKem.Util.Shared

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace libcrux_iot_ml_kem.SerializeFc

open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Util.Shared
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
  -- aeneas nightly-2026.08.24: now a `partialSpec`; the bounds moved out of the
  -- arguments into the postcondition and the `panic` precondition.
  obtain ⟨ns, hns_eq, hns_val, -, -, -, hns_get⟩ :=
    Std.WP.spec_imp_exists (Std.WP.spec_of_partialSpec
      (Aeneas.Std.Slice.subslice_spec s ⟨a, b⟩)
      (by intro e; cases e <;> simp_all <;> omega) (by simp))
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

private theorem bind_ok_pair {α β γ : Type} {x : RustM (α × β)} {a : α} {b : β}
    (h : x = .ok (a, b)) (g : α → β → RustM γ) :
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
    ⦃ ⇓ p => ⌜ (Aeneas.Std.RustM.ok (declane serialized.val p 16)).holds ⌝ ⦄ := by
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
          RustM.ok (ControlFlow.cont
            (({ iter := { cs := 24#usize, elements := drop }, count := cnt' } : EnumCE),
             ({ coefficients := index_mut_back t1 } :
               libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                 libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)))) = _
      rw [array_index_mut16 acc.coefficients cnt hcoeff_len]
      simp only [Aeneas.Std.bind_tc_ok]
      show (do
          let t1 ← libcrux_iot_ml_kem.vector.portable.serialize.deserialize_12 chunk
              (acc.coefficients.val[cnt.val]'hcoeff_len)
          RustM.ok (ControlFlow.cont
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
    ⦃ ⇓ p => ⌜ (Aeneas.Std.RustM.ok (declane serialized.val p 16)).holds ⌝ ⦄ := by
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
  -- aeneas nightly-2026.08.24: now a `partialSpec`; the bounds moved out of the
  -- arguments into the postcondition and the `panic` precondition.
  obtain ⟨y, hy_eq, hy_val, _, _⟩ :=
    Std.WP.spec_imp_exists (Std.WP.spec_of_partialSpec
      (Std.UScalar.ShiftRight_spec (ty0 := .U8) x sh)
      (by intro e; cases e <;> simp_all) (by simp))
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
      RustM.ok (decide (i4 = 1#u8), a)) = _
  rw [hq_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hidx]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hy_eq]; simp only [Aeneas.Std.bind_tc_ok]
  show RustM.ok (decide (y &&& 1#u8 = 1#u8), a) = _
  rw [hy]
  unfold sliceBit
  rw [hq16, hr8]


/-- **Spec-side bit expansion**: the 3072 booleans are exactly `sliceBit`. -/
private theorem bytes_to_bits_get (a : Std.Array Std.U8 384#usize) :
    ∃ bv : Std.Array Bool 3072#usize,
      hacspec_ml_kem.serialize.bytes_to_bits (N := 384#usize) 3072#usize a = .ok bv
      ∧ ∀ m : Nat, m < 3072 → bv.val[m]! = sliceBit a.val m := by
  have hmul : ((384#usize : Std.Usize) * (8#usize : Std.Usize) : Aeneas.Std.RustM Std.Usize)
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
    -- hax v0.4.0-rc.1 no longer emits the `let i ← N * 8#usize; massert (N8 = i)` prelude
    -- (ALL 74 spec-side `massert`s are gone from the extraction), so the length check and
    -- its `hmul` witness are no longer part of this equation.
    simp only [hacspec_ml_kem.parameters.createi]
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

/-! ### `BitVec 16` primitives.

    These three are the PRIMITIVES of all 16-bit sign/mask reasoning in this file: they
    are stated on bare `BitVec 16`, so they serve both the `I16` plumbing directly below
    and the `U16` sign-mask bank of M-D (`section MDBank`), which reaches back for them
    rather than restating them. The `Std.I16` forms below are one-line corollaries. -/

private theorem toNat16_lt (x : BitVec 16) : x.toNat < 65536 := by
  have h := x.isLt
  simp only [show (2:Nat) ^ 16 = 65536 from rfl] at h
  exact h

private theorem msb16_iff (x : BitVec 16) : x.msb = false ↔ x.toNat < 32768 := by
  rw [BitVec.msb_eq_false_iff_two_mul_lt]
  simp only [show (2:Nat) ^ 16 = 65536 from rfl]
  omega

/-- The sign mask, as a `BitVec`: `>>> 15` on a 16-bit word is `allOnes` or `0`. -/
private theorem sshr15_bv (b : BitVec 16) :
    b.sshiftRight 15 = if b.msb then BitVec.allOnes 16 else 0#16 := by
  have hlt := toNat16_lt b
  rcases Bool.eq_false_or_eq_true b.msb with hm | hm
  · -- `msb = true`: the shift is `~~~((~~~b) >>> 15)` and the inner shift vanishes
    have hn : ¬ (b.toNat < 32768) := fun hc => by
      rw [(msb16_iff b).mpr hc] at hm; exact Bool.noConfusion hm
    rw [hm, if_pos rfl, BitVec.sshiftRight_eq_of_msb_true hm]
    have hnot : (~~~b).toNat = 65535 - b.toNat := by rw [BitVec.toNat_not]
    have hz : (~~~b) >>> 15 = 0#16 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, hnot, Nat.shiftRight_eq_div_pow]
      simp only [show (2:Nat) ^ 15 = 32768 from rfl]
      show (65535 - b.toNat) / 32768 = (0#16 : BitVec 16).toNat
      rw [Nat.div_eq_of_lt (by omega)]; rfl
    rw [hz]; rfl
  · -- `msb = false`: a logical shift, and `b.toNat < 2 ^ 15`
    have hn := (msb16_iff b).mp hm
    rw [hm]
    simp only [Bool.false_eq_true, if_false]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sshiftRight_of_msb_false hm, Nat.shiftRight_eq_div_pow]
    simp only [show (2:Nat) ^ 15 = 32768 from rfl]
    show b.toNat / 32768 = (0#16 : BitVec 16).toNat
    rw [Nat.div_eq_of_lt (by omega)]; rfl

/-! ### `I16` sign/`bv` plumbing. -/

private theorem i16_toNat_lt (x : Std.I16) : x.bv.toNat < 65536 := toNat16_lt x.bv

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
    x.bv.msb = false := (msb16_iff x.bv).mpr (by omega)

/-- Arithmetic shift right by 15 on an `I16` is the sign mask. The `toNat` shadow of the
    primitive `sshr15_bv`; the `BitVec` equation is the stronger form, so keep new work on
    that one. -/
private theorem sshr15_toNat (x : Std.I16) :
    (x.bv.sshiftRight 15).toNat = if x.bv.msb then 65535 else 0 := by
  rw [sshr15_bv]
  split <;> simp

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

private theorem bind_ok_triple {α β γ δ : Type} {x : RustM (α × β × γ)} {a : α} {b : β} {c : γ}
    (h : x = .ok (a, b, c)) (g : α → β → γ → RustM δ) :
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
    show RustM.ok (Aeneas.Std.Slice.len out) = _
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




/-- Written-prefix loop invariant: after `k` iterations the first `24k` bytes
    carry `encByte`, and the length is preserved. -/
private def encInv (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (acc : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector × Slice Std.U8) :
    RustM Prop :=
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
  · show (pure _ : RustM Prop).holds
    simp only [Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp]
    intro _
    exact ⟨h_len, by intro n hn; exact absurd hn (by scalar_tac)⟩
  · intro acc k hk0 hk16 hinv
    have h16 : (16#usize : Std.Usize).val = 16 := rfl
    obtain ⟨hacc_len, hacc_done⟩ : acc.2.val.length = 384 ∧
        ∀ n : Nat, n < 24 * k.val → (acc.2.val[n]!).val = encByte re n := by
      have hh := hinv
      simp only [encInv, Aeneas.Std.RustM.holds, pure, Pure.pure, Std.Do.Triple,
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
            RustM.ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
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
        simp only [encInv, Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp]
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
        simp only [encInv, Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp]
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
    show RustM.ok (Aeneas.Std.Slice.len serialized) = _
    congr 1
    apply Std.UScalar.eq_of_val_eq
    simp [Aeneas.Std.Slice.len_val, h_len]
  have hdivlit : ∀ x y z : Std.Usize, y.val ≠ 0 → x.val / y.val = z.val →
      (x / y : RustM Std.Usize) = .ok z := by
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

/-! ### M-B — the spec-side `createi` chain and the `byte_encode_into` wrapper.

    THE EXEMPLAR (readiness map §3 #1, re-ranked #1 in AMENDMENTS 3 §P1.8). These
    two are the UNIQUE remaining blocker for L5.6: everything else this file needs
    for the encode direction is already banked above — the impl-side 24-byte
    `serialize_12` closed form (`:1120`), the 16-iteration range loop (`:1388`),
    and the encode keystone `bitSum_encBit_eq_encByte` (`:1673`), which is the
    MATHEMATICS. What is missing is only PLUMBING: identifying `byte_encode`'s
    three-level `createi` chain with the pure byte function `encByte`, and then
    threading it through the `to_slice`/`copy_from_slice` wrapper.

    ## Shape

    Follow `bytes_to_bits_get` (`:854`) — the decode-side analogue, ~30 lines over
    `Util.CreateI.from_fn_pure_eq` / `createi_pure_eq`. The existential form is
    deliberate and is the CORRECTED shape: the readiness map's original sketch
    wrote the result as `.ok ⟨fun n => …⟩`, which does not elaborate —
    `createi_pure_eq` concludes at `RustM.ok ⟨List.map f (List.range ↑N), _⟩`, so
    the payload is a `List.map`, not a function, and the map's second sketch left
    its `s` unbound. Stating `∃ out, … = .ok out ∧ (pointwise)` sidesteps both and
    matches the idiom the decode side already uses.

    ## Why there is NO bound hypothesis (verified, not assumed)

    Both statements are UNCONDITIONAL. `encLane` is `(x.val % 3329).toNat` — the
    canonical residue by mathematical `%` — and `lift_poly_raw` (just above) proves
    `((lift_poly re).val[j]!).val).val = encLane re j` with no side condition. So on
    the SPEC side the canonicalisation has already happened and no `is_bounded_poly`
    is needed.

    The `h_bnd : natAbs ≤ 3328` that L5.6's own statement carries belongs to a
    DIFFERENT seam: the impl's `to_unsigned_field_modulus` adds q AT MOST ONCE, so
    it agrees with the canonical residue only for a reduced lane. That seam is
    `to_unsigned_fm_eq` (`:979`) and is already banked. Keeping the bound out of
    M-B is what isolates plumbing from mathematics.

    Machine-checked before locking (`references/mlkem-falsify-harness.lean`): both
    statements hold for all 6657 admissible lane values AND for 60 random polys with
    lanes drawn from the full I16 range, including the all-`32767` and all-`-32768`
    corners — i.e. they survive massive violations of `h_bnd`, which is what shows
    the hypothesis would be dead weight rather than load-bearing.

    ## Kinds covered

    K4 (sub-byte field packing, ENCODE) — closing the one PARTIAL entry in the §1
    taxonomy — and K11 for the ENCODE direction, whose terminal `bits_to_bytes` is
    MANY-TO-ONE (each byte folds 8 bools) where every decode generator is
    one-to-many and pointwise. That asymmetry is the "dimension of difference" from
    `bytes_to_bits_get`, and it is why the window lemma `bitSum_encBit_eq_encByte`
    had to exist at all.

    ## Provenance

    MINE, DO NOT PORT. The F* ladder `lemma_bitvec_from_bounded_index_d` →
    `lemma_bits_to_bytes_bit_d` → `lemma_byte_encode_bit_d` → `lemma_serialize_byte_eq_d`
    (`Hacspec_ml_kem.Commute.Serialize_compress.fst`) is a source of SPEC and of
    similarity signals only; its SMT-shaped lemma structure is not to be copied. -/

/-! #### Shared plumbing for the three `createi` levels.

    The decode bank's copies of these (`usize_ofNat_val`, `array_index_ok`,
    `u16OfNat`) live further down the file, after L5.6, so the encode side states
    its own; they are three-line `Std`-spec wrappers, not new mathematics. -/

/-- Value of the `Usize` literal `createi`/`from_fn_pure_eq` feeds the closure. -/
private theorem enc_usize_ofNat_val (k : Nat) (h : k < 2 ^ 32) :
    ((⟨BitVec.ofNat _ k⟩ : Std.Usize)).val = k := by
  show (BitVec.ofNat _ k).toNat = k
  simp only [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have h32 : (32 : Nat) ≤ System.Platform.numBits := by
    have := System.Platform.numBits_eq; omega
  calc k < 2 ^ 32 := h
    _ ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) h32

private theorem enc_array_index_ok {α : Type} [Inhabited α] {N : Std.Usize}
    (a : Std.Array α N) (i : Std.Usize) (h : i.val < a.val.length) :
    Aeneas.Std.Array.index_usize a i = .ok (a.val[i.val]!) := by
  simp only [Aeneas.Std.Array.index_usize, Aeneas.Std.Array.getElem?_Usize_eq,
    List.getElem?_eq_getElem h]
  rw [getElem!_pos a.val i.val h]

/-- Reading back a cell of the array `from_fn_pure_eq` produces. Stated ONCE and
    generically in `N`: doing it inline at `N = 3072` forces the kernel to unfold
    `List.range 3072` (the closed-large-scalar pitfall, skill §6). -/
private theorem enc_mk_getElem {α : Type} [Inhabited α] {N : Std.Usize}
    {f : Nat → α} {h : ((List.range N.val).map f).length = N.val} {k : Nat}
    (hk : k < N.val) :
    ((⟨(List.range N.val).map f, h⟩ : Std.Array α N).val)[k]! = f k := by
  show ((List.range N.val).map f)[k]! = f k
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

/-- The `U8` carrying a `Nat` payload, as a closed term. -/
private def u8OfNat (x : Nat) : Std.U8 := ⟨BitVec.ofNat _ x⟩

private theorem u8OfNat_val (x : Nat) (h : x < 256) : (u8OfNat x).val = x := by
  show (BitVec.ofNat _ x).toNat = x
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by simpa [Std.UScalarTy.numBits] using h)

/-- THE bit-packing bridge (`Nat.shiftLeft_add_eq_or_of_lt`, `Init/Data/Nat`):
    a bounded low field OR'd with a shifted high field is addition. Every `|||`
    in `bits_to_bytes` collapses through this, so no `BitVec` ever appears. -/
private theorem enc_or_shift_eq_add {lo hi i : Nat} (h : lo < 2 ^ i) :
    lo ||| (hi * 2 ^ i) = hi * 2 ^ i + lo := by
  rw [← Nat.shiftLeft_eq, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq]

/-- `x <<< t` for a `U8` and an `I32` shift amount, kept SYMBOLIC as `* 2 ^ e`. -/
private theorem u8_shl_iscalar (x : Std.U8) (t : Std.I32) (ht0 : 0 ≤ t.val) (ht : t.val < 8)
    (hx : x.val * 2 ^ t.toNat < 256) :
    ∃ z : Std.U8, (x <<< t : RustM Std.U8) = .ok z ∧ z.val = x.val * 2 ^ t.toNat := by
  -- aeneas nightly-2026.08.24: now a `partialSpec`; the bounds moved out of the
  -- arguments into the postcondition and the `panic` precondition.
  obtain ⟨z, hz, hv, _, _⟩ :=
    Std.WP.spec_imp_exists (Std.WP.spec_of_partialSpec
      (Std.UScalar.ShiftLeft_IScalar_spec (ty0 := .U8) x t (Std.UScalar.size .U8) rfl)
      (by intro e; cases e <;> simp_all <;> omega) (by simp))
  refine ⟨z, hz, ?_⟩
  have hsize : Std.UScalar.size .U8 = 256 := by
    rw [Std.UScalar.size_def]; norm_num [Std.UScalarTy.numBits]
  rw [hv, hsize, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hx]

private theorem cast_fromBool_u8_val (b : Bool) :
    (Std.UScalar.cast_fromBool .U8 b).val = if b then 1 else 0 := by cases b <;> rfl

/-- One `bits_to_bytes` bit slot: `bool_as_u8 b <<< e` is `if b then 2 ^ e else 0`. -/
private theorem u8_bit_shl (b : Bool) (t : Std.I32) (e : Nat)
    (ht0 : 0 ≤ t.val) (ht : t.val < 8) (he : t.toNat = e) (he8 : e < 8) :
    ∃ z : Std.U8, ((Std.UScalar.cast_fromBool .U8 b) <<< t : RustM Std.U8) = .ok z
      ∧ z.val = if b then 2 ^ e else 0 := by
  have hpow : (2:Nat) ^ e ≤ 128 := by
    calc (2:Nat) ^ e ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 128 := by norm_num
  obtain ⟨z, hz, hzv⟩ :=
    u8_shl_iscalar (Std.UScalar.cast_fromBool .U8 b) t ht0 ht
      (by rw [cast_fromBool_u8_val, he]; split <;> omega)
  exact ⟨z, hz, by rw [hzv, cast_fromBool_u8_val, he]; split <;> omega⟩

/-- One accumulation step of the `bits_to_bytes` OR chain, in pure `Nat`. -/
private theorem u8_or_bit_step (f : Nat → Bool) (acc z : Std.U8) (b : Bool) (t : Nat)
    (hacc : acc.val = bitSum f t) (hz : z.val = if b then 2 ^ t else 0) (hf : b = f t) :
    (acc ||| z).val = bitSum f (t + 1) := by
  have hlo : bitSum f t < 2 ^ t := bitSum_lt f t
  have hb : (if b then 2 ^ t else 0) = (if b then 1 else 0) * 2 ^ t := by split <;> omega
  rw [Std.UScalar.val_or, hacc, hz, hb, enc_or_shift_eq_add hlo, hf]
  simp only [bitSum]
  split <;> omega

/-! #### Level 1 — `byte_encode`'s own `createi`: `p_raw[k] = encLane re k`. -/

private theorem byte_encode_closure_eq
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) (k : Nat) (hk : k < 256) :
    (hacspec_ml_kem.serialize.byte_encode.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16
        384#usize 3072#usize).call_mut p ⟨BitVec.ofNat _ k⟩
      = .ok ((p.val[k]!).val, p) := by
  have hkv : ((⟨BitVec.ofNat _ k⟩ : Std.Usize)).val = k :=
    enc_usize_ofNat_val k (by omega)
  have hlen : p.val.length = 256 := by have := p.property; simpa using this
  show (do
      let fe ← Aeneas.Std.Array.index_usize p (⟨BitVec.ofNat _ k⟩ : Std.Usize)
      RustM.ok (fe.val, p)) = _
  rw [enc_array_index_ok p _ (by rw [hkv, hlen]; exact hk), hkv]
  simp only [Aeneas.Std.bind_tc_ok]

/-- **Level 1.** `byte_encode`'s first `createi` at `p = lift_poly re` is exactly
    `encLane`: the spec's `FieldElement.val` IS the canonical residue. -/
private theorem byte_encode_raw_get
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ∃ p_raw : Std.Array Std.U16 256#usize,
      hacspec_ml_kem.parameters.createi (256#usize : Std.Usize)
          (hacspec_ml_kem.serialize.byte_encode.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16
            384#usize 3072#usize) (lift_poly re)
        = .ok p_raw
      ∧ ∀ k : Nat, k < 256 → (p_raw.val[k]!).val = encLane re k := by
  have h256 : ((256#usize : Std.Usize)).val = 256 := by scalar_tac
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq (T := Std.U16)
      (256#usize : Std.Usize)
      (hacspec_ml_kem.serialize.byte_encode.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16
        384#usize 3072#usize) (lift_poly re)
      (fun k => ((lift_poly re).val[k]!).val)
      (fun k hk => byte_encode_closure_eq (lift_poly re) k (by rw [h256] at hk; exact hk))
  simp only [hacspec_ml_kem.parameters.createi]
  rw [hfn]
  refine ⟨_, rfl, ?_⟩
  intro k hk
  rw [enc_mk_getElem (by rw [h256]; exact hk)]
  exact lift_poly_raw re k hk

/-! #### Level 2 — `bitvector_from_bounded_ints`: `bv[m] = encBit re m`. -/

private theorem u16_val_eq_one_iff (w : Std.U16) : (w = 1#u16) ↔ (w.val = 1) := by
  constructor
  · intro h; rw [h]; rfl
  · intro h; apply Std.UScalar.eq_of_val_eq; rw [h]; rfl

private theorem u16_shr_and1_eq (x : Std.U16) (sh : Std.Usize) (hsh : sh.val < 16) :
    ∃ y : Std.U16, (x >>> sh) = .ok y
      ∧ decide ((y &&& 1#u16) = 1#u16) = natBit x.val sh.val := by
  -- aeneas nightly-2026.08.24: now a `partialSpec`; the bounds moved out of the
  -- arguments into the postcondition and the `panic` precondition.
  obtain ⟨y, hy_eq, hy_val, _, _⟩ :=
    Std.WP.spec_imp_exists (Std.WP.spec_of_partialSpec
      (Std.UScalar.ShiftRight_spec (ty0 := .U16) x sh)
      (by intro e; cases e <;> simp_all) (by simp))
  refine ⟨y, hy_eq, ?_⟩
  have hand : (y &&& 1#u16).val = y.val % 2 := by
    rw [Std.UScalar.val_and]
    have h1 : ((1#u16 : Std.U16).val) = 1 := rfl
    rw [h1]
    have h2 := Nat.and_two_pow_sub_one_eq_mod y.val 1
    rw [show (2:Nat) ^ 1 - 1 = 1 from rfl, show (2:Nat) ^ 1 = 2 from rfl] at h2
    exact h2
  have hyv : y.val = x.val / 2 ^ sh.val := by
    rw [hy_val, Nat.shiftRight_eq_div_pow]
  simp only [natBit, u16_val_eq_one_iff, hand, hyv]

private theorem bvfb_closure_eq (a : Std.Array Std.U16 256#usize) (m : Nat) (hm : m < 3072) :
    (hacspec_ml_kem.serialize.bitvector_from_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBool
        (256#usize : Std.Usize) (3072#usize : Std.Usize)).call_mut
        (a, (12#usize : Std.Usize)) ⟨BitVec.ofNat _ m⟩
      = .ok (natBit ((a.val[m / 12]!).val) (m % 12), (a, (12#usize : Std.Usize))) := by
  have hmv : ((⟨BitVec.ofNat _ m⟩ : Std.Usize)).val = m :=
    enc_usize_ofNat_val m (by omega)
  have h12 : ((12#usize : Std.Usize)).val = 12 := by scalar_tac
  have hlen : a.val.length = 256 := by have := a.property; simpa using this
  obtain ⟨q, hq_eq, hq_val⟩ :=
    Std.UScalar.div_spec (⟨BitVec.ofNat _ m⟩ : Std.Usize)
      (y := (12#usize : Std.Usize)) (by decide)
  obtain ⟨r, hr_eq, hr_val⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.rem_spec (⟨BitVec.ofNat _ m⟩ : Std.Usize)
      (y := (12#usize : Std.Usize)) (by decide))
  have hqv : q.val = m / 12 := by rw [hq_val, hmv, h12]
  have hrv : r.val = m % 12 := by rw [hr_val, hmv, h12]
  obtain ⟨y, hy_eq, hy⟩ := u16_shr_and1_eq (a.val[q.val]!) r (by rw [hrv]; omega)
  show (do
      let i1 ← (⟨BitVec.ofNat _ m⟩ : Std.Usize) / (12#usize : Std.Usize)
      let i2 ← Aeneas.Std.Array.index_usize a i1
      let i3 ← (⟨BitVec.ofNat _ m⟩ : Std.Usize) % (12#usize : Std.Usize)
      let i4 ← i2 >>> i3
      let i5 ← Aeneas.Std.lift (i4 &&& 1#u16)
      RustM.ok (decide (i5 = 1#u16),
        ((a, (12#usize : Std.Usize)) :
          hacspec_ml_kem.serialize.bitvector_from_bounded_ints.closure
            (256#usize : Std.Usize) (3072#usize : Std.Usize)))) = _
  rw [hq_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok a q (by rw [hqv, hlen]; omega)]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hr_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hy_eq]; simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hy, hqv, hrv]
  rfl

/-- **Level 2.** The 3072 booleans are exactly `encBit re`. -/
private theorem bvfb_3072_12_get
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (p_raw : Std.Array Std.U16 256#usize)
    (hp : ∀ k : Nat, k < 256 → (p_raw.val[k]!).val = encLane re k) :
    ∃ bv : Std.Array Bool 3072#usize,
      hacspec_ml_kem.serialize.bitvector_from_bounded_ints (N := 256#usize)
          (3072#usize : Std.Usize) p_raw (12#usize : Std.Usize) = .ok bv
      ∧ ∀ m : Nat, m < 3072 → bv.val[m]! = encBit re m := by
  have h3072 : ((3072#usize : Std.Usize)).val = 3072 := by scalar_tac
  have hmul : ((256#usize : Std.Usize) * (12#usize : Std.Usize) : RustM Std.Usize)
      = .ok (3072#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq (T := Bool)
      (3072#usize : Std.Usize)
      (hacspec_ml_kem.serialize.bitvector_from_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBool
        (256#usize : Std.Usize) (3072#usize : Std.Usize))
      (p_raw, (12#usize : Std.Usize))
      (fun m => natBit ((p_raw.val[m / 12]!).val) (m % 12))
      (fun m hm => bvfb_closure_eq p_raw m (by rw [h3072] at hm; exact hm))
  have key : hacspec_ml_kem.serialize.bitvector_from_bounded_ints (N := 256#usize)
        (3072#usize : Std.Usize) p_raw (12#usize : Std.Usize)
      = CoreModels.core.array.from_fn (3072#usize : Std.Usize)
          (hacspec_ml_kem.serialize.bitvector_from_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBool
            (256#usize : Std.Usize) (3072#usize : Std.Usize))
          (p_raw, (12#usize : Std.Usize)) := by
    unfold hacspec_ml_kem.serialize.bitvector_from_bounded_ints
    -- hax v0.4.0-rc.1 no longer emits the `let i ← N * 8#usize; massert (N8 = i)` prelude
    -- (ALL 74 spec-side `massert`s are gone from the extraction), so the length check and
    -- its `hmul` witness are no longer part of this equation.
    simp only [hacspec_ml_kem.parameters.createi]
  rw [key, hfn]
  refine ⟨_, rfl, ?_⟩
  intro m hm
  rw [enc_mk_getElem (by rw [h3072]; exact hm)]
  show natBit ((p_raw.val[m / 12]!).val) (m % 12) = encBit re m
  unfold encBit
  rw [hp (m / 12) (by omega)]

/-! #### Level 3 — `bits_to_bytes`: each byte is the LSB-first 8-bit window. -/

/-- **Level 3.** The `bits_to_bytes` closure at index `n` is `bitSum` of the eight
    bits `8n .. 8n+7`. Straight-line body walk: every `|||` is discharged by
    `u8_or_bit_step`, so the OR chain never leaves `Nat`. -/
private theorem bits_to_bytes_closure_eq (bv : Std.Array Bool 3072#usize) (n : Nat)
    (hn : n < 384) :
    (hacspec_ml_kem.serialize.bits_to_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
        (384#usize : Std.Usize) (3072#usize : Std.Usize)).call_mut bv ⟨BitVec.ofNat _ n⟩
      = .ok (u8OfNat (bitSum (fun t => bv.val[8 * n + t]!) 8), bv) := by
  set f : Nat → Bool := fun t => bv.val[8 * n + t]! with hf
  have hnv : ((⟨BitVec.ofNat _ n⟩ : Std.Usize)).val = n :=
    enc_usize_ofNat_val n (by omega)
  have hlen : bv.val.length = 3072 := by have := bv.property; simpa using this
  have h8 : ((8#usize : Std.Usize)).val = 8 := by scalar_tac
  obtain ⟨i, hi, hiv0⟩ :=
    usize_mul_ok_e (8#usize : Std.Usize) (⟨BitVec.ofNat _ n⟩ : Std.Usize)
      (by rw [h8, hnv]; scalar_tac)
  have hiv : i.val = 8 * n := by rw [hiv0, h8, hnv]
  -- the eight cell indices
  obtain ⟨j1, hj1, hj1v⟩ := usize_add_ok_e i (1#usize) (by rw [hiv]; scalar_tac)
  obtain ⟨j2, hj2, hj2v⟩ := usize_add_ok_e i (2#usize) (by rw [hiv]; scalar_tac)
  obtain ⟨j3, hj3, hj3v⟩ := usize_add_ok_e i (3#usize) (by rw [hiv]; scalar_tac)
  obtain ⟨j4, hj4, hj4v⟩ := usize_add_ok_e i (4#usize) (by rw [hiv]; scalar_tac)
  obtain ⟨j5, hj5, hj5v⟩ := usize_add_ok_e i (5#usize) (by rw [hiv]; scalar_tac)
  obtain ⟨j6, hj6, hj6v⟩ := usize_add_ok_e i (6#usize) (by rw [hiv]; scalar_tac)
  obtain ⟨j7, hj7, hj7v⟩ := usize_add_ok_e i (7#usize) (by rw [hiv]; scalar_tac)
  have e1 : j1.val = 8 * n + 1 := by rw [hj1v, hiv]; scalar_tac
  have e2 : j2.val = 8 * n + 2 := by rw [hj2v, hiv]; scalar_tac
  have e3 : j3.val = 8 * n + 3 := by rw [hj3v, hiv]; scalar_tac
  have e4 : j4.val = 8 * n + 4 := by rw [hj4v, hiv]; scalar_tac
  have e5 : j5.val = 8 * n + 5 := by rw [hj5v, hiv]; scalar_tac
  have e6 : j6.val = 8 * n + 6 := by rw [hj6v, hiv]; scalar_tac
  have e7 : j7.val = 8 * n + 7 := by rw [hj7v, hiv]; scalar_tac
  -- the eight shifted slots
  obtain ⟨z1, hz1, hz1v⟩ :=
    u8_bit_shl (bv.val[j1.val]!) (1#i32) 1 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z2, hz2, hz2v⟩ :=
    u8_bit_shl (bv.val[j2.val]!) (2#i32) 2 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z3, hz3, hz3v⟩ :=
    u8_bit_shl (bv.val[j3.val]!) (3#i32) 3 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z4, hz4, hz4v⟩ :=
    u8_bit_shl (bv.val[j4.val]!) (4#i32) 4 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z5, hz5, hz5v⟩ :=
    u8_bit_shl (bv.val[j5.val]!) (5#i32) 5 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z6, hz6, hz6v⟩ :=
    u8_bit_shl (bv.val[j6.val]!) (6#i32) 6 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z7, hz7, hz7v⟩ :=
    u8_bit_shl (bv.val[j7.val]!) (7#i32) 7 (by decide) (by decide) (by decide) (by decide)
  -- the accumulation, in pure `Nat`
  have a0 : (Std.UScalar.cast_fromBool .U8 (bv.val[i.val]!)).val = bitSum f 1 := by
    rw [cast_fromBool_u8_val]
    show _ = bitSum f 0 + (if f 0 then 2 ^ 0 else 0)
    simp only [bitSum, hf, hiv, Nat.add_zero, pow_zero]
    split <;> omega
  have a1 := u8_or_bit_step f _ z1 (bv.val[j1.val]!) 1 a0 hz1v (by rw [hf, e1])
  have a2 := u8_or_bit_step f _ z2 (bv.val[j2.val]!) 2 a1 hz2v (by rw [hf, e2])
  have a3 := u8_or_bit_step f _ z3 (bv.val[j3.val]!) 3 a2 hz3v (by rw [hf, e3])
  have a4 := u8_or_bit_step f _ z4 (bv.val[j4.val]!) 4 a3 hz4v (by rw [hf, e4])
  have a5 := u8_or_bit_step f _ z5 (bv.val[j5.val]!) 5 a4 hz5v (by rw [hf, e5])
  have a6 := u8_or_bit_step f _ z6 (bv.val[j6.val]!) 6 a5 hz6v (by rw [hf, e6])
  have a7 := u8_or_bit_step f _ z7 (bv.val[j7.val]!) 7 a6 hz7v (by rw [hf, e7])
  have hfinal : (Std.UScalar.cast_fromBool .U8 (bv.val[i.val]!) ||| z1 ||| z2 ||| z3 ||| z4
      ||| z5 ||| z6 ||| z7) = u8OfNat (bitSum f 8) := by
    refine Aeneas.Std.UScalar.eq_of_val_eq ?_
    rw [a7, u8OfNat_val _ (by have := bitSum_lt f 8; simpa using this)]
  show (do
      let i ← (8#usize : Std.Usize) * (⟨BitVec.ofNat _ n⟩ : Std.Usize)
      let b ← Aeneas.Std.Array.index_usize bv i
      let i1 ← Aeneas.Std.lift (Std.UScalar.cast_fromBool .U8 b)
      let i2 ← i + 1#usize
      let b1 ← Aeneas.Std.Array.index_usize bv i2
      let i3 ← Aeneas.Std.lift (Std.UScalar.cast_fromBool .U8 b1)
      let i4 ← i3 <<< (1#i32 : Std.I32)
      let i5 ← Aeneas.Std.lift (i1 ||| i4)
      let i6 ← i + 2#usize
      let b2 ← Aeneas.Std.Array.index_usize bv i6
      let i7 ← Aeneas.Std.lift (Std.UScalar.cast_fromBool .U8 b2)
      let i8 ← i7 <<< (2#i32 : Std.I32)
      let i9 ← Aeneas.Std.lift (i5 ||| i8)
      let i10 ← i + 3#usize
      let b3 ← Aeneas.Std.Array.index_usize bv i10
      let i11 ← Aeneas.Std.lift (Std.UScalar.cast_fromBool .U8 b3)
      let i12 ← i11 <<< (3#i32 : Std.I32)
      let i13 ← Aeneas.Std.lift (i9 ||| i12)
      let i14 ← i + 4#usize
      let b4 ← Aeneas.Std.Array.index_usize bv i14
      let i15 ← Aeneas.Std.lift (Std.UScalar.cast_fromBool .U8 b4)
      let i16 ← i15 <<< (4#i32 : Std.I32)
      let i17 ← Aeneas.Std.lift (i13 ||| i16)
      let i18 ← i + 5#usize
      let b5 ← Aeneas.Std.Array.index_usize bv i18
      let i19 ← Aeneas.Std.lift (Std.UScalar.cast_fromBool .U8 b5)
      let i20 ← i19 <<< (5#i32 : Std.I32)
      let i21 ← Aeneas.Std.lift (i17 ||| i20)
      let i22 ← i + 6#usize
      let b6 ← Aeneas.Std.Array.index_usize bv i22
      let i23 ← Aeneas.Std.lift (Std.UScalar.cast_fromBool .U8 b6)
      let i24 ← i23 <<< (6#i32 : Std.I32)
      let i25 ← Aeneas.Std.lift (i21 ||| i24)
      let i26 ← i + 7#usize
      let b7 ← Aeneas.Std.Array.index_usize bv i26
      let i27 ← Aeneas.Std.lift (Std.UScalar.cast_fromBool .U8 b7)
      let i28 ← i27 <<< (7#i32 : Std.I32)
      let i29 ← Aeneas.Std.lift (i25 ||| i28)
      RustM.ok (i29, bv)) = _
  rw [hi]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok bv i (by rw [hiv, hlen]; omega)]
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hj1]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok bv j1 (by rw [e1, hlen]; omega)]
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hz1]; simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hj2]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok bv j2 (by rw [e2, hlen]; omega)]
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hz2]; simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hj3]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok bv j3 (by rw [e3, hlen]; omega)]
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hz3]; simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hj4]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok bv j4 (by rw [e4, hlen]; omega)]
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hz4]; simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hj5]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok bv j5 (by rw [e5, hlen]; omega)]
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hz5]; simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hj6]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok bv j6 (by rw [e6, hlen]; omega)]
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hz6]; simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hj7]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok bv j7 (by rw [e7, hlen]; omega)]
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hz7]; simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hfinal]

/-- **Level 3, assembled.** -/
private theorem bits_to_bytes_384_get (bv : Std.Array Bool 3072#usize) :
    ∃ out : Std.Array Std.U8 384#usize,
      hacspec_ml_kem.serialize.bits_to_bytes (384#usize : Std.Usize)
          (N8 := 3072#usize) bv = .ok out
      ∧ ∀ n : Nat, n < 384 →
          (out.val[n]!).val = bitSum (fun t => bv.val[8 * n + t]!) 8 := by
  have h384 : ((384#usize : Std.Usize)).val = 384 := by scalar_tac
  have hmul : ((384#usize : Std.Usize) * (8#usize : Std.Usize) : RustM Std.Usize)
      = .ok (3072#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq (T := Std.U8)
      (384#usize : Std.Usize)
      (hacspec_ml_kem.serialize.bits_to_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
        (384#usize : Std.Usize) (3072#usize : Std.Usize)) bv
      (fun n => u8OfNat (bitSum (fun t => bv.val[8 * n + t]!) 8))
      (fun n hn => bits_to_bytes_closure_eq bv n (by rw [h384] at hn; exact hn))
  have key : hacspec_ml_kem.serialize.bits_to_bytes (384#usize : Std.Usize)
        (N8 := 3072#usize) bv
      = CoreModels.core.array.from_fn (384#usize : Std.Usize)
          (hacspec_ml_kem.serialize.bits_to_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
            (384#usize : Std.Usize) (3072#usize : Std.Usize)) bv := by
    unfold hacspec_ml_kem.serialize.bits_to_bytes
    -- hax v0.4.0-rc.1 no longer emits the `let i ← N * 8#usize; massert (N8 = i)` prelude
    -- (ALL 74 spec-side `massert`s are gone from the extraction), so the length check and
    -- its `hmul` witness are no longer part of this equation.
    simp only [hacspec_ml_kem.parameters.createi]
  rw [key, hfn]
  refine ⟨_, rfl, ?_⟩
  intro n hn
  rw [enc_mk_getElem (by rw [h384]; exact hn)]
  exact u8OfNat_val _ (by have := bitSum_lt (fun t => bv.val[8 * n + t]!) 8; simpa using this)

/-- **M-B(1)** — `byte_encode` at `d = 12` produces exactly the pure model
    `encByte`. This is the spec-side `createi` chain: `byte_encode.closure` reads
    `(p[j]).val`, `bitvector_from_bounded_ints` expands it to 3072 bits, and
    `bits_to_bytes` folds each 8-bit window back to a byte.

    The keystone `bitSum_encBit_eq_encByte` (`:1673`) already proves the WINDOW
    identity; what remains is to normalise the three `createi` levels onto it via
    `Util.CreateI.createi_pure_eq` / `from_fn_pure_eq`, exactly as
    `bytes_to_bits_get` does for the decode direction. -/
theorem byte_encode_12_eq
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ∃ out : Std.Array Std.U8 384#usize,
      hacspec_ml_kem.serialize.byte_encode 384#usize 3072#usize (lift_poly re) 12#usize
        = .ok out
      ∧ ∀ n : Nat, n < 384 → (out.val[n]!).val = encByte re n := by
  obtain ⟨p_raw, hp_raw, hp_get⟩ := byte_encode_raw_get re
  obtain ⟨bv, hbv, hbv_get⟩ := bvfb_3072_12_get re p_raw hp_get
  obtain ⟨out, hout, hout_get⟩ := bits_to_bytes_384_get bv
  have e1 : ((32#usize : Std.Usize) * (12#usize : Std.Usize) : RustM Std.Usize)
      = .ok (384#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have e2 : ((256#usize : Std.Usize) * (12#usize : Std.Usize) : RustM Std.Usize)
      = .ok (3072#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  refine ⟨out, ?_, ?_⟩
  · unfold hacspec_ml_kem.serialize.byte_encode
    simp only [hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT, Aeneas.Std.massert,
      le_refl, if_true, Aeneas.Std.bind_tc_ok, e1, e2, eq_self_iff_true, hp_raw, hbv, hout]
  · intro n hn
    rw [hout_get n hn,
      bitSum_congr _ (fun t => encBit re (8 * n + t)) 8
        (fun t ht => hbv_get (8 * n + t) (by omega))]
    exact bitSum_encBit_eq_encByte re n

/-- **M-B(2)** — the `byte_encode_into` slice wrapper. At `d = 12` the spec
    dispatches (`match d.val with | 12 => …`) to `byte_encode 384 3072 p 12`, then
    `Array.to_slice` and `copy_from_slice` into the caller's buffer. So this is
    M-B(1) plus the wrapper every encode obligation goes through; the `massert`s on
    `d ≤ BITS_PER_COEFFICIENT` and `out.len = 32 * d` discharge from `h_len`.

    This is the form L5.6's post is stated against, so it is the apex of the pair. -/
theorem byte_encode_into_12_eq
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (serialized : Slice Std.U8)
    (h_len : serialized.length = 384) :
    ∃ s : Slice Std.U8,
      hacspec_ml_kem.serialize.byte_encode_into (lift_poly re) 12#usize serialized
        = .ok s
      ∧ s.length = 384
      ∧ ∀ n : Nat, n < 384 → (s.val[n]!).val = encByte re n := by
  obtain ⟨a, ha, ha_get⟩ := byte_encode_12_eq re
  have hlen : serialized.val.length = 384 := h_len
  -- the two `Slice.len` bridges: the caller's buffer and the encoded array's view
  have hraw : Aeneas.Std.Slice.len serialized = (384#usize : Std.Usize) := by
    refine Aeneas.Std.UScalar.eq_of_val_eq ?_
    rw [Aeneas.Std.Slice.len_val]
    show serialized.val.length = ((384#usize : Std.Usize)).val
    rw [hlen]; scalar_tac
  have ha_val : (Aeneas.Std.Array.to_slice a).val = a.val := rfl
  have ha_len : (Aeneas.Std.Array.to_slice a).val.length = 384 := a.property
  have hraw_a : Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice a)
      = (384#usize : Std.Usize) := by
    refine Aeneas.Std.UScalar.eq_of_val_eq ?_
    rw [Aeneas.Std.Slice.len_val]
    show (Aeneas.Std.Array.to_slice a).val.length = ((384#usize : Std.Usize)).val
    rw [ha_len]; scalar_tac
  have hslen : CoreModels.core.slice.Slice.len serialized
      = .ok (384#usize : Std.Usize) := by
    -- `core.slice.Slice.len` now delegates to `rust_primitives.slice.slice_length`
    simp only [CoreModels.core.slice.Slice.len,
      CoreModels.rust_primitives.slice.slice_length, hraw]
  have hmul : ((32#usize : Std.Usize) * (12#usize : Std.Usize) : RustM Std.Usize)
      = .ok (384#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  -- dispatch: `d ≤ BITS_PER_COEFFICIENT` and `out.len = 32 * d` discharge, and
  -- `(12#usize).val = 12` selects the `d = 12` branch, which is M-B(1)
  -- hax v0.4.0-rc.1 dropped `byte_encode_into`'s `massert (d ≤ BITS_PER_COEFFICIENT)` and
  -- `massert (out.len = 32 * d)` prelude, so `hslen`/`hmul` no longer take part here; only
  -- the `d = 12` branch selection and `ha` remain.
  unfold hacspec_ml_kem.serialize.byte_encode_into
  simp only [Aeneas.Std.bind_tc_ok, ha,
    show ((12#usize : Std.Usize).val) = 12 from rfl,
    Aeneas.Std.lift]
  -- `copy_from_slice` returns the source slice outright when the lengths agree
  refine ⟨Aeneas.Std.Array.to_slice a, ?_, ?_, ?_⟩
  · -- `copy_from_slice` now goes through `rust_primitives.slice.slice_clone_from_slice`,
    -- i.e. a `mapM clone` over the source; `Util.SliceSpecs` already has the bridge that
    -- collapses it for a `Copy` instance whose `clone` is the identity.
    exact libcrux_iot_ml_kem.Util.SliceSpecs.core_models_slice_Slice_copy_from_slice_eq
      _ serialized (Aeneas.Std.Array.to_slice a) (by rw [hlen, ha_len]) (by intro x; rfl)
  · exact ha_len
  · intro n hn
    rw [ha_val]
    exact ha_get n hn

end L56Bank

/-! ## M-C — the sub-byte GROUP LAW at a modulus that does not divide 8.

    THE EXEMPLAR for kind K3's open sub-cases (readiness map §1; re-ranked #2 in
    AMENDMENTS 3 §P1.8). K3 is `FULL` at `d = 12` and `d = 1` and those are the EASY
    moduli: 12 = 8 + 4, so a 3-byte group holds exactly 2 lanes and realigns every 3
    bytes, and `d = 1` needs no group law at all. At `d ∈ {4,5,10,11}` a lane can
    straddle a byte boundary and the boundaries never realign inside a chunk. That is
    the "dimension of difference", and it is what these three close.

    ## Why this is stated GENERICALLY in `d`, against the map and against A1

    The map ranked this as `M-C(d=5)`; amendment A1 corrected the modulus to `d = 11`
    (the only width whose lanes span THREE bytes) and both assumed one exemplar per
    modulus. Measured before authoring: the group law does not need to be
    per-modulus. `n` bits read at ANY bit offset come from the 3-byte window at
    `m / 8`, for every `n ≤ 17` — so ONE lemma covers d = 4, 5, 10, 11 and 12 at once
    and the separate `M-C(d=11)` item (ranked #7, deferred) is subsumed rather than
    postponed. A1's ADEQUACY argument is what forced this: it is satisfied here by
    generality instead of by a second build.

    ## Side conditions — measured, and each one load-bearing

    `hn : n ≤ 17` on the decode law is EXACTLY TIGHT: a 3-byte window is 24 bits and
    the read starts at bit `m % 8 ≤ 7`, leaving 17. Swept `n = 0 … 20` over random
    byte lists at every offset — clean through 17, first counterexamples at n = 18.

    `hd : 4 ≤ d` and `hL : ∀ i, L i < 2 ^ d` on the encode law are both refuted when
    dropped: with `d ≤ 3` a 3-lane window cannot cover 8 bits (fails at d = 1, 2, 3),
    and with unbounded lanes it fails at EVERY d (the high bits of `L q` leak past the
    field). Neither is decoration.

    Out-of-range reads are fine and deliberate: `(default : Std.U8).val = 0`
    (evaluated), so `decw`'s window is zero-padded past the end of `l` and `sliceBit`
    reads `false` there — the two sides stay equal with no length hypothesis. That is
    what lets the decode law apply to the LAST lane of a group, where the 3-byte
    window genuinely runs off the end of a 5-byte slice.

    ## Falsified before locking (`references/mlkem-falsify-harness.lean`)

    Decode law: d ∈ {1,4,5,10,11,12}, every lane, random byte lists. Encode law:
    d ∈ {4,5,10,11,12}, every byte of a 40-lane run. Impl apex: 60 random 5-byte
    groups, the all-0x00/0xFF/alternating corners, and EXHAUSTIVELY over each of the
    five byte positions × all 256 values. Zero counterexamples.

    ## Provenance

    MINE, DO NOT PORT. `references/mlkem-bitpack-recipe.lean` (re-checked against this
    tree today: elaborates, no sorry) carries the two tools this needs —
    `or_shift_eq_add` ("OR == + when the fields are disjoint", skill §4.1's key device)
    and `field_eq : (x >>> s) &&& (2 ^ w - 1) = x / 2 ^ s % 2 ^ w`. Work in `Nat`, not
    `BitVec`. -/

section MCBank

/-- The shared normal form: the `n` bits at bit offset `m` of a byte list, read out
    of the 3-byte window based at byte `m / 8`. This is to a general `d` what `dec12`
    (`:209`) is to `d = 12` — the common normal form of the impl's byte arithmetic and
    the spec's bit vector. Zero-padded past the end of `l`, see the note above. -/
private def decw (l : List Std.U8) (m n : Nat) : Nat :=
  (l[m / 8]!.val + 256 * l[m / 8 + 1]!.val + 65536 * l[m / 8 + 2]!.val)
    / 2 ^ (m % 8) % 2 ^ n

/-! ### Bit-splitting toolkit for a positional sum `a + 2 ^ c * K`

    The two halves of "OR == + when the fields are disjoint" (the recipe's
    `or_shift_eq_add`), read in the DECODE direction: a bit below the split sees only
    the low field, a bit at or above the split sees only the high field. Everything
    below is generic in the split width `c`, so the 8/16 splits of a 3-byte window are
    two applications of the same pair rather than two hand-rolled arguments. -/

/-- Bits below the split are the low field's bits: the high field contributes a
    multiple of `2 ^ c`, hence an even multiple of `2 ^ t` for every `t < c`. -/
private theorem natBit_lo (a K c t : Nat) (ht : t < c) :
    natBit (a + 2 ^ c * K) t = natBit a t := by
  have hpos : (0:Nat) < 2 ^ t := Nat.two_pow_pos _
  obtain ⟨u, hu⟩ : ∃ u, c - t = u + 1 := ⟨c - t - 1, by omega⟩
  have h2 : (2:Nat) ^ c = 2 ^ t * (2 * 2 ^ u) := by
    rw [show (2:Nat) * 2 ^ u = 2 ^ (u + 1) by rw [Nat.pow_succ]; exact Nat.mul_comm _ _,
      ← Nat.pow_add]
    congr 1; omega
  have key : (a + 2 ^ c * K) / 2 ^ t = a / 2 ^ t + 2 * (2 ^ u * K) := by
    rw [h2, show 2 ^ t * (2 * 2 ^ u) * K = 2 ^ t * (2 * (2 ^ u * K)) by
      simp [Nat.mul_assoc]]
    exact Nat.add_mul_div_left _ _ hpos
  simp only [natBit, key, Nat.add_mul_mod_self_left]

/-- Bits at or above the split are the high field's bits: `a < 2 ^ c` is exactly what
    makes the low field vanish under `/ 2 ^ c`. This is where the field bound is
    load-bearing — drop it and the low field's overflow leaks upward. -/
private theorem natBit_hi (a K c t : Nat) (ha : a < 2 ^ c) :
    natBit (a + 2 ^ c * K) (c + t) = natBit K t := by
  have hpos : (0:Nat) < 2 ^ c := Nat.two_pow_pos _
  have key : (a + 2 ^ c * K) / 2 ^ (c + t) = K / 2 ^ t := by
    rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hpos,
        Nat.div_eq_of_lt ha, Nat.zero_add]
  simp only [natBit, key]

/-- The 3-byte window, bit by bit: bit `t` of `b0 + 256*b1 + 65536*b2` is bit `t % 8`
    of byte `t / 8`, for every `t < 24`. Two nested applications of the pair above at
    `c = 8`. Only the two LOW bytes need a bound: `b2` occupies the top field and
    nothing above it is ever read. -/
private theorem natBit_win (b0 b1 b2 t : Nat) (h0 : b0 < 256) (h1 : b1 < 256)
    (ht : t < 24) :
    natBit (b0 + 256 * b1 + 65536 * b2) t
      = natBit (if t < 8 then b0 else if t < 16 then b1 else b2) (t % 8) := by
  have hW : b0 + 256 * b1 + 65536 * b2 = b0 + 2 ^ 8 * (b1 + 2 ^ 8 * b2) := by
    simp [Nat.pow_succ]; omega
  rw [hW]
  rcases Nat.lt_or_ge t 8 with hc | hc
  · rw [if_pos hc, natBit_lo _ _ _ _ hc, Nat.mod_eq_of_lt hc]
  · rw [if_neg (by omega)]
    obtain ⟨t1, ht1⟩ : ∃ t1, t = 8 + t1 := ⟨t - 8, by omega⟩
    subst ht1
    rw [natBit_hi _ _ _ _ (show b0 < 2 ^ 8 by omega)]
    rcases Nat.lt_or_ge t1 8 with hc2 | hc2
    · rw [if_pos (by omega), natBit_lo _ _ _ _ hc2]
      congr 1
      omega
    · rw [if_neg (by omega)]
      obtain ⟨t2, ht2⟩ : ∃ t2, t1 = 8 + t2 := ⟨t1 - 8, by omega⟩
      subst ht2
      rw [natBit_hi _ _ _ _ (show b1 < 2 ^ 8 by omega)]
      congr 1
      omega

/-- **M-C(1) — the generic DECODE group law.** The spec-side bit stream, windowed at
    any offset, is a 3-byte read. Generalises `bitSum_sliceBit_eq_dec12` (`:274`) off
    `d = 12` and off byte alignment; `n ≤ 17` is tight. -/
theorem bitSum_sliceBit_window (l : List Std.U8) (m n : Nat) (hn : n ≤ 17) :
    bitSum (fun t => sliceBit l (m + t)) n = decw l m n := by
  -- every bit the window reads lands in the 3-byte group based at `m / 8`: the read
  -- starts at bit `m % 8 ≤ 7` and runs `n ≤ 17` bits, so `m % 8 + t ≤ 23 < 24`.
  -- This is where `hn` is exactly tight — at `n = 18` the last bit is bit 24, the
  -- FOURTH byte, which `decw`'s window does not contain.
  have hrlt : m % 8 < 8 := Nat.mod_lt _ (by omega)
  have hkey : ∀ t, t < n →
      sliceBit l (m + t)
        = natBit (l[m / 8]!.val + 256 * l[m / 8 + 1]!.val + 65536 * l[m / 8 + 2]!.val)
            (m % 8 + t) := by
    intro t ht
    simp only [sliceBit]
    rw [natBit_win _ _ _ _ (u8_val_lt l (m / 8)) (u8_val_lt l (m / 8 + 1))
      (show m % 8 + t < 24 by omega)]
    -- which byte of the window bit `m % 8 + t` falls in, and at which offset
    rcases Nat.lt_or_ge (m % 8 + t) 8 with hc | hc
    · rw [if_pos hc, show (m + t) / 8 = m / 8 by omega,
        show (m + t) % 8 = (m % 8 + t) % 8 by omega]
    · rcases Nat.lt_or_ge (m % 8 + t) 16 with hc2 | hc2
      · rw [if_neg (by omega), if_pos hc2, show (m + t) / 8 = m / 8 + 1 by omega,
          show (m + t) % 8 = (m % 8 + t) % 8 by omega]
      · rw [if_neg (by omega), if_neg (by omega),
          show (m + t) / 8 = m / 8 + 2 by omega,
          show (m + t) % 8 = (m % 8 + t) % 8 by omega]
  rw [bitSum_congr _
      (fun t => natBit (l[m / 8]!.val + 256 * l[m / 8 + 1]!.val + 65536 * l[m / 8 + 2]!.val)
        (m % 8 + t)) n hkey,
    bitSum_shift]
  rfl

/-! ### The ENCODE-direction window: three consecutive `d`-bit lanes

    `natBit_win` (`:2401`) with the byte width 8 replaced by the LANE width `d`: bit
    `u` of the packed 3-lane word `L q ++ L (q+1) ++ L (q+2)` is bit `u % d` of lane
    `q + u / d`, for every `u < 3 * d`. Same two applications of the
    `natBit_lo`/`natBit_hi` pair, so the encode direction costs no new bit algebra —
    only the split width changes from 8 to `d`. As in `natBit_win`, only the two LOW
    lanes need the field bound: nothing above lane `q + 2` is ever read. -/
private theorem natBit_lane_win (d : Nat) (hdpos : 0 < d) (L : Nat → Nat) (q : Nat)
    (h0 : L q < 2 ^ d) (h1 : L (q + 1) < 2 ^ d) (u : Nat) (hu : u < 3 * d) :
    natBit (L q + 2 ^ d * (L (q + 1) + 2 ^ d * L (q + 2))) u
      = natBit (L (q + u / d)) (u % d) := by
  -- `% d` by a VARIABLE modulus is out of `omega`'s reach, so the one shift fact the
  -- three branches share is proved once, by `Nat.add_mul_mod_self_left`.
  have hmod : ∀ x : Nat, (d + x) % d = x % d := fun x => by
    rw [show d + x = x + d * 1 by ring, Nat.add_mul_mod_self_left]
  rcases Nat.lt_or_ge u d with hc | hc
  · -- lane `q`: the bit is below the first split
    rw [natBit_lo _ _ _ _ hc, Nat.div_eq_of_lt hc, Nat.mod_eq_of_lt hc, Nat.add_zero]
  · obtain ⟨u1, hu1⟩ : ∃ u1, u = d + u1 := ⟨u - d, by omega⟩
    subst hu1
    rw [natBit_hi _ _ _ _ h0]
    rcases Nat.lt_or_ge u1 d with hc2 | hc2
    · -- lane `q + 1`
      rw [natBit_lo _ _ _ _ hc2,
        show (d + u1) / d = 1 from Nat.div_eq_of_lt_le (by omega) (by omega),
        hmod, Nat.mod_eq_of_lt hc2]
    · -- lane `q + 2`; `hu` is what bounds the read to THREE lanes
      obtain ⟨u2, hu2⟩ : ∃ u2, u1 = d + u2 := ⟨u1 - d, by omega⟩
      subst hu2
      rw [natBit_hi _ _ _ _ h1,
        show (d + (d + u2)) / d = 2 from Nat.div_eq_of_lt_le (by omega) (by omega),
        hmod, hmod, Nat.mod_eq_of_lt (show u2 < d by omega)]

/-- M-C(2) with the byte offset pre-split as `m = d * q + r`. Stated this way so the
    quotient and remainder are VARIABLES: `8 * n / d` and `8 * n % d` are division by
    a variable modulus, which `omega` cannot see through, whereas everything below is
    linear in `q` and `r`. -/
private theorem bitSum_laneBit_window_aux (d q r : Nat) (hd : 4 ≤ d) (hrlt : r < d)
    (L : Nat → Nat) (hL : ∀ i, L i < 2 ^ d) (m : Nat) (hm : m = d * q + r) :
    bitSum (fun t => natBit (L ((m + t) / d)) ((m + t) % d)) 8
      = (L q / 2 ^ r + L (q + 1) * 2 ^ (d - r) + L (q + 2) * 2 ^ (2 * d - r)) % 256 := by
  have hdpos : 0 < d := by omega
  -- (1) each of the 8 bits read at offset `m` is a bit of the 3-lane window at `q`.
  -- `r + t ≤ (d - 1) + 7 < 3 * d` is where `hd : 4 ≤ d` is load-bearing: at `d = 3`
  -- the eighth bit would fall in a FOURTH lane, which the window does not contain.
  have hkey : ∀ t, t < 8 →
      natBit (L ((m + t) / d)) ((m + t) % d)
        = natBit (L q + 2 ^ d * (L (q + 1) + 2 ^ d * L (q + 2))) (r + t) := by
    intro t ht
    rw [show m + t = d * q + (r + t) by rw [hm]; ring,
      Nat.mul_add_div hdpos, Nat.mul_add_mod,
      natBit_lane_win d hdpos L q (hL q) (hL (q + 1)) (r + t) (by omega)]
  rw [bitSum_congr _
      (fun t => natBit (L q + 2 ^ d * (L (q + 1) + 2 ^ d * L (q + 2))) (r + t)) 8 hkey,
    bitSum_shift]
  -- (2) the window divided by `2 ^ r` IS the impl's three-term sum: `2 ^ r` divides
  -- both high lane weights (`r < d`), so the division distributes exactly.
  have hsplit : L q + 2 ^ d * (L (q + 1) + 2 ^ d * L (q + 2))
      = L q + 2 ^ r * (2 ^ (d - r) * L (q + 1) + 2 ^ (2 * d - r) * L (q + 2)) := by
    have e1 : (2:Nat) ^ d = 2 ^ r * 2 ^ (d - r) := by
      rw [← Nat.pow_add]; congr 1; omega
    have e2 : (2:Nat) ^ d * 2 ^ d = 2 ^ r * 2 ^ (2 * d - r) := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    calc L q + 2 ^ d * (L (q + 1) + 2 ^ d * L (q + 2))
        = L q + (2 ^ d * L (q + 1) + 2 ^ d * 2 ^ d * L (q + 2)) := by ring
      _ = L q + (2 ^ r * 2 ^ (d - r) * L (q + 1)
            + 2 ^ r * 2 ^ (2 * d - r) * L (q + 2)) := by rw [e2, e1]
      _ = L q + 2 ^ r * (2 ^ (d - r) * L (q + 1) + 2 ^ (2 * d - r) * L (q + 2)) := by ring
  rw [hsplit, Nat.add_mul_div_left _ _ (Nat.two_pow_pos r),
    show (2:Nat) ^ 8 = 256 from rfl,
    show L q / 2 ^ r + (2 ^ (d - r) * L (q + 1) + 2 ^ (2 * d - r) * L (q + 2))
        = L q / 2 ^ r + L (q + 1) * 2 ^ (d - r) + L (q + 2) * 2 ^ (2 * d - r) by ring]

/-- **M-C(2) — the generic ENCODE group law.** Byte `n` of the `d`-bit lane stream is
    a 3-lane read. The encode counterpart of M-C(1), and the general-`d` form of
    `bitSum_encBit_eq_encByte` (`:1673`, which is `d = 12` only). Stated over an
    abstract lane function `L` rather than `encLane` so it serves every `d` and both
    the `_v` and (later) `_u` families. -/
theorem bitSum_laneBit_window (d : Nat) (hd : 4 ≤ d) (L : Nat → Nat)
    (hL : ∀ i, L i < 2 ^ d) (n : Nat) :
    bitSum (fun t => natBit (L ((8 * n + t) / d)) ((8 * n + t) % d)) 8
      = (L (8 * n / d) / 2 ^ (8 * n % d)
          + L (8 * n / d + 1) * 2 ^ (d - 8 * n % d)
          + L (8 * n / d + 2) * 2 ^ (2 * d - 8 * n % d)) % 256 := by
  -- the whole content is the aux above; here we only supply the division identity
  -- `8 * n = d * (8 * n / d) + 8 * n % d` that names the window's base lane.
  exact bitSum_laneBit_window_aux d (8 * n / d) (8 * n % d) hd
    (Nat.mod_lt _ (by omega)) L hL (8 * n) (Nat.div_add_mod (8 * n) d).symm

/-! ### Impl-side toolkit for `deserialize_5_int`

    What the `d = 12` bank (`:290`–`:413`) does not already provide, in EXISTENTIAL
    form: aeneas's `<<<` / `>>>` return a `RustM` whose payload is pinned only by its
    `.val`, and the apex's own conclusion is existential, so there is no reason to name
    the payload (which is what forced `shr8` (`:3879`) / `u8_shr_ok` (`:3893`) into a
    `BitVec` def). Everything here is `Nat`, per the bitpack recipe's representation rule. -/

/-- A byte widened to `I16` is value-preserving: no byte reaches the sign bit. -/
private theorem c16_val_nat (x : Std.U8) : (c16 x).val = (x.val : Int) := by
  have hx : x.val < 256 := by scalar_tac
  rw [i16_val_of_toNat _ (by rw [c16_bv_toNat]; omega), c16_bv_toNat]

/-- `&&& (2 ^ k - 1)` is `% 2 ^ k`, at the `U8` level. The `d = 12` bank has this only
    at the two hard-coded masks 15 and 255 (`:348`, `:353`); `deserialize_5_int` uses
    five different masks (31, 3, 15, 1, 7), so it is worth stating once in `k`. -/
private theorem u8_and_mask_val (x c : Std.U8) (k : Nat) (hc : c.val = 2 ^ k - 1) :
    (x &&& c).val = x.val % 2 ^ k := by
  rw [Std.UScalar.val_and, hc, Nat.and_two_pow_sub_one_eq_mod]

/-- The no-overflow side condition of every `<<<` in `deserialize_5_int`: a `k`-bit
    field shifted left by `e` stays in a byte as soon as `2 ^ k * 2 ^ e ≤ 256`. -/
private theorem u8_and_shl_bound (x c : Std.U8) (k e : Nat) (hc : c.val = 2 ^ k - 1)
    (h : 2 ^ k * 2 ^ e ≤ 256) : (x &&& c).val * 2 ^ e < 256 := by
  rw [u8_and_mask_val x c k hc]
  exact lt_of_lt_of_le
    ((Nat.mul_lt_mul_right (Nat.two_pow_pos e)).mpr (Nat.mod_lt _ (Nat.two_pow_pos k))) h

/-- `x <<< t` at a literal `I32` shift, kept symbolic as `* 2 ^ k`. -/
private theorem u8_shl_lit (x : Std.U8) (t : Std.I32) (k : Nat)
    (htv : t.val = (k : Int)) (hk : k < 8) (hx : x.val * 2 ^ k < 256) :
    ∃ z : Std.U8, (x <<< t : RustM Std.U8) = .ok z ∧ z.val = x.val * 2 ^ k := by
  have h0 : (0:Int) ≤ t.val := by rw [htv]; exact Int.natCast_nonneg k
  have hkn : t.toNat = k := by
    show t.val.toNat = k
    rw [htv]; exact Int.toNat_natCast k
  obtain ⟨z, hz, hzv⟩ :=
    u8_shl_iscalar x t h0 (by rw [htv]; exact_mod_cast hk) (by rw [hkn]; exact hx)
  exact ⟨z, hz, by rw [hzv, hkn]⟩

/-- `x >>> t` at a literal `I32` shift, kept symbolic as `/ 2 ^ k`. -/
private theorem u8_shr_lit (x : Std.U8) (t : Std.I32) (k : Nat)
    (htv : t.val = (k : Int)) (hk : k < 8) :
    ∃ z : Std.U8, (x >>> t : RustM Std.U8) = .ok z ∧ z.val = x.val / 2 ^ k := by
  have h0 : (0:Int) ≤ t.val := by rw [htv]; exact Int.natCast_nonneg k
  have hkn : Std.IScalar.toNat t = k := by
    show t.val.toNat = k
    rw [htv]; exact Int.toNat_natCast k
  -- aeneas nightly-2026.08.24: now a `partialSpec`; the bounds moved out of the
  -- arguments into the postcondition and the `panic` precondition.
  obtain ⟨z, hz, hzv, _, _⟩ :=
    Std.WP.spec_imp_exists (Std.WP.spec_of_partialSpec
      (Std.UScalar.ShiftRight_IScalar_spec (ty0 := .U8) x t)
      (by intro e; cases e <;> simp_all <;> omega) (by simp))
  exact ⟨z, hz, by rw [hzv, hkn, Nat.shiftRight_eq_div_pow]⟩

/-- The recipe's `or_shift_eq_add` in the orientation the impl writes it (high field
    first). "OR == + when the fields are disjoint". -/
private theorem or_shl_add (hi lo i : Nat) (h : lo < 2 ^ i) :
    (hi * 2 ^ i) ||| lo = hi * 2 ^ i + lo := by
  rw [Nat.or_comm, enc_or_shift_eq_add h]

/-- One straddling lane of `deserialize_5_int`: `(hi_field << e) ||| (lo >> s)`. -/
private theorem lane_or_val (zh zl : Std.U8) (hi lo e : Nat)
    (hzh : zh.val = hi * 2 ^ e) (hzl : zl.val = lo) (hlo : lo < 2 ^ e) :
    (zh ||| zl).val = hi * 2 ^ e + lo := by
  rw [Std.UScalar.val_or, hzh, hzl, or_shl_add _ _ _ hlo]

/-- Every `n`-bit window is an `n`-bit number — this is the bound conjunct's whole
    content, read off `decw`'s trailing `% 2 ^ n`. Stated GENERIC in `n`, not at the
    `n = 5` this apex happens to need, so the `d = 10` and `d = 11` apexes draw their
    `< 1024` / `< 2048` bound conjuncts from this same lemma rather than restating it. -/
private theorem decw_lt (l : List Std.U8) (m n : Nat) : decw l m n < 2 ^ n := by
  simp only [decw]
  exact Nat.mod_lt _ (Nat.two_pow_pos n)

/-- Out-of-range reads are zero — this is what lets the `k = 5, 6, 7` windows, whose
    3-byte frame runs past the end of an exactly-5-byte slice, still be `decw` reads. -/
private theorem u8_oob (l : List Std.U8) (i : Nat) (h : l.length ≤ i) :
    (l[i]! : Std.U8).val = 0 := by
  rw [getElem!_neg l i (by omega)]
  rfl

/-- **M-C(3) — the impl seam at `d = 5`, the APEX of this bank.** `deserialize_5_int`
    turns 5 bytes into 8 lanes through a chain of `&&&` / `|||` / `<<<` / `>>>`; this
    says each lane is exactly the corresponding 5-bit window of the spec bit stream.

    This is the half that is NOT mechanical, and it is why the exemplar includes an
    impl-side statement rather than only the two pure laws: at `d = 12` every lane is
    one `or_shift_eq_add` over a 3-byte group, whereas here the shift amounts advance
    by 5 modulo 8 and every lane has a different split. Expect M-C(1) to do the
    spec-side half and the bitpack recipe the impl-side half.

    No 3-byte-window caveat is needed: for `k < 8` every bit index is `≤ 39`, i.e.
    byte index `≤ 4`, which is in range for an exactly-5-byte slice. -/
theorem deserialize_5_int_lanes_eq (bytes : Slice Std.U8) (h_len : bytes.length = 5) :
    ∃ v0 v1 v2 v3 v4 v5 v6 v7 : Std.I16,
      libcrux_iot_ml_kem.vector.portable.serialize.deserialize_5_int bytes
          = .ok (v0, v1, v2, v3, v4, v5, v6, v7)
      ∧ ∀ k : Nat, k < 8 →
          (([v0, v1, v2, v3, v4, v5, v6, v7] : List Std.I16)[k]!).val
              = (bitSum (fun t => sliceBit bytes.val (5 * k + t)) 5 : Int)
            -- BOUND CONJUNCT, per the amended transcription rule's MANDATORY third
            -- check (references/mlkem-inc1-contracts.txt): the iot source carries only
            -- `#[hax_lib::requires(bytes.len() == 5)]` and NO `ensures`, so the post is
            -- ours to choose from what the CONSUMER binds. The consumer is
            -- `deserialize_5` -> `deserialize_then_decompress_ring_element_v` at dv = 5,
            -- whose Decompress_5 step needs `x < 2 ^ 5` (this is exactly the
            -- `pair it with a < 2^d` caveat AMENDMENTS 2 records for M-E: without it the
            -- downstream `.as_i16()` truncation invalidates the composed step).
            -- Implied by the equality via `bitSum_lt` (:91) — costs the prover a line
            -- here and saves the consumer from re-deriving it.
            ∧ (([v0, v1, v2, v3, v4, v5, v6, v7] : List Std.I16)[k]!).val < 32 := by
  have hlen : bytes.val.length = 5 := h_len
  have hb0 := u8_val_lt bytes.val 0
  have hb1 := u8_val_lt bytes.val 1
  have hb2 := u8_val_lt bytes.val 2
  have hb3 := u8_val_lt bytes.val 3
  have hb4 := u8_val_lt bytes.val 4
  -- the two zero-padded reads the `k = 5, 6, 7` windows make past the end
  have hoob5 : (bytes.val[5]! : Std.U8).val = 0 := u8_oob _ _ (by omega)
  have hoob6 : (bytes.val[6]! : Std.U8).val = 0 := u8_oob _ _ (by omega)
  have hi0 : Slice.index_usize bytes 0#usize = .ok bytes.val[0]! :=
    slice_index_usize_eq bytes 0#usize (by simp [hlen])
  have hi1 : Slice.index_usize bytes 1#usize = .ok bytes.val[1]! :=
    slice_index_usize_eq bytes 1#usize (by simp [hlen])
  have hi2 : Slice.index_usize bytes 2#usize = .ok bytes.val[2]! :=
    slice_index_usize_eq bytes 2#usize (by simp [hlen])
  have hi3 : Slice.index_usize bytes 3#usize = .ok bytes.val[3]! :=
    slice_index_usize_eq bytes 3#usize (by simp [hlen])
  have hi4 : Slice.index_usize bytes 4#usize = .ok bytes.val[4]! :=
    slice_index_usize_eq bytes 4#usize (by simp [hlen])
  -- the seven right shifts: `y<byte><amount>`
  obtain ⟨y05, hy05, hy05v⟩ := u8_shr_lit bytes.val[0]! 5#i32 5 (by simp) (by omega)
  obtain ⟨y12, hy12, hy12v⟩ := u8_shr_lit bytes.val[1]! 2#i32 2 (by simp) (by omega)
  obtain ⟨y17, hy17, hy17v⟩ := u8_shr_lit bytes.val[1]! 7#i32 7 (by simp) (by omega)
  obtain ⟨y24, hy24, hy24v⟩ := u8_shr_lit bytes.val[2]! 4#i32 4 (by simp) (by omega)
  obtain ⟨y31, hy31, hy31v⟩ := u8_shr_lit bytes.val[3]! 1#i32 1 (by simp) (by omega)
  obtain ⟨y36, hy36, hy36v⟩ := u8_shr_lit bytes.val[3]! 6#i32 6 (by simp) (by omega)
  obtain ⟨y43, hy43, hy43v⟩ := u8_shr_lit bytes.val[4]! 3#i32 3 (by simp) (by omega)
  -- the four left shifts, one per straddling lane; `s<lane>`
  obtain ⟨s1, hs1, hs1v⟩ := u8_shl_lit (bytes.val[1]! &&& 3#u8) 3#i32 3 (by simp) (by omega)
    (u8_and_shl_bound _ _ 2 3 rfl (by norm_num))
  obtain ⟨s3, hs3, hs3v⟩ := u8_shl_lit (bytes.val[2]! &&& 15#u8) 1#i32 1 (by simp) (by omega)
    (u8_and_shl_bound _ _ 4 1 rfl (by norm_num))
  obtain ⟨s4, hs4, hs4v⟩ := u8_shl_lit (bytes.val[3]! &&& 1#u8) 4#i32 4 (by simp) (by omega)
    (u8_and_shl_bound _ _ 1 4 rfl (by norm_num))
  obtain ⟨s6, hs6, hs6v⟩ := u8_shl_lit (bytes.val[4]! &&& 7#u8) 2#i32 2 (by simp) (by omega)
    (u8_and_shl_bound _ _ 3 2 rfl (by norm_num))
  refine ⟨c16 (bytes.val[0]! &&& 31#u8), c16 (s1 ||| y05), c16 (y12 &&& 31#u8),
    c16 (s3 ||| y17), c16 (s4 ||| y24), c16 (y31 &&& 31#u8), c16 (s6 ||| y36),
    c16 y43, ?_, ?_⟩
  · -- the straight-line body walk: every step is one of the four facts above
    simp only [libcrux_iot_ml_kem.vector.portable.serialize.deserialize_5_int,
      hi0, hi1, hi2, hi3, hi4, hy05, hy12, hy17, hy24, hy31, hy36, hy43,
      hs1, hs3, hs4, hs6, as_i16_eq, Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  · -- the spec side. Every lane is a pure ℕ expression in the five bytes; M-C(1)
    -- turns the bit stream into `decw`, and each of the eight identities is then
    -- linear-with-division, i.e. `omega`'s territory.
    intro k hk
    -- the eight lane values, in ℕ, powers kept symbolic
    have n0 : (bytes.val[0]! &&& 31#u8).val = bytes.val[0]!.val % 2 ^ 5 :=
      u8_and_mask_val _ _ 5 rfl
    have f1 : s1.val = bytes.val[1]!.val % 2 ^ 2 * 2 ^ 3 := by
      rw [hs1v, u8_and_mask_val _ _ 2 rfl]
    have f3 : s3.val = bytes.val[2]!.val % 2 ^ 4 * 2 ^ 1 := by
      rw [hs3v, u8_and_mask_val _ _ 4 rfl]
    have f4 : s4.val = bytes.val[3]!.val % 2 ^ 1 * 2 ^ 4 := by
      rw [hs4v, u8_and_mask_val _ _ 1 rfl]
    have f6 : s6.val = bytes.val[4]!.val % 2 ^ 3 * 2 ^ 2 := by
      rw [hs6v, u8_and_mask_val _ _ 3 rfl]
    have n1 : (s1 ||| y05).val
        = bytes.val[1]!.val % 2 ^ 2 * 2 ^ 3 + bytes.val[0]!.val / 2 ^ 5 :=
      lane_or_val _ _ _ _ 3 f1 hy05v (by omega)
    have n2 : (y12 &&& 31#u8).val = bytes.val[1]!.val / 2 ^ 2 % 2 ^ 5 := by
      rw [u8_and_mask_val _ _ 5 rfl, hy12v]
    have n3 : (s3 ||| y17).val
        = bytes.val[2]!.val % 2 ^ 4 * 2 ^ 1 + bytes.val[1]!.val / 2 ^ 7 :=
      lane_or_val _ _ _ _ 1 f3 hy17v (by omega)
    have n4 : (s4 ||| y24).val
        = bytes.val[3]!.val % 2 ^ 1 * 2 ^ 4 + bytes.val[2]!.val / 2 ^ 4 :=
      lane_or_val _ _ _ _ 4 f4 hy24v (by omega)
    have n5 : (y31 &&& 31#u8).val = bytes.val[3]!.val / 2 ^ 1 % 2 ^ 5 := by
      rw [u8_and_mask_val _ _ 5 rfl, hy31v]
    have n6 : (s6 ||| y36).val
        = bytes.val[4]!.val % 2 ^ 3 * 2 ^ 2 + bytes.val[3]!.val / 2 ^ 6 :=
      lane_or_val _ _ _ _ 2 f6 hy36v (by omega)
    -- the closer: the bound conjunct is the window's own `% 2 ^ 5`, so it comes free
    -- from the equality rather than from a second argument about the impl.
    have key : ∀ v : Std.I16, v.val = (decw bytes.val (5 * k) 5 : Int) →
        v.val = (bitSum (fun t => sliceBit bytes.val (5 * k + t)) 5 : Int) ∧ v.val < 32 := by
      intro v h
      have hbw : decw bytes.val (5 * k) 5 < 32 := decw_lt bytes.val (5 * k) 5
      rw [bitSum_sliceBit_window bytes.val (5 * k) 5 (by omega)]
      exact ⟨h, by omega⟩
    -- `decw` at the eight offsets, with the 3-byte frame's base index and shift
    -- computed. Kept SEPARATE from the `omega` steps below: `norm_num` rewrites
    -- `l[i]!` to `l[i]?.getD default`, and if that happened inside an `omega` goal
    -- the byte atoms would stop matching the `hb*`/`hoob*` hypotheses.
    have d0 : decw bytes.val (5 * 0) 5
        = (bytes.val[0]!.val + 256 * bytes.val[1]!.val + 65536 * bytes.val[2]!.val)
            % 32 := by norm_num [decw]
    have d1 : decw bytes.val (5 * 1) 5
        = (bytes.val[0]!.val + 256 * bytes.val[1]!.val + 65536 * bytes.val[2]!.val)
            / 32 % 32 := by norm_num [decw]
    have d2 : decw bytes.val (5 * 2) 5
        = (bytes.val[1]!.val + 256 * bytes.val[2]!.val + 65536 * bytes.val[3]!.val)
            / 4 % 32 := by norm_num [decw]
    have d3 : decw bytes.val (5 * 3) 5
        = (bytes.val[1]!.val + 256 * bytes.val[2]!.val + 65536 * bytes.val[3]!.val)
            / 128 % 32 := by norm_num [decw]
    have d4 : decw bytes.val (5 * 4) 5
        = (bytes.val[2]!.val + 256 * bytes.val[3]!.val + 65536 * bytes.val[4]!.val)
            / 16 % 32 := by norm_num [decw]
    have d5 : decw bytes.val (5 * 5) 5
        = (bytes.val[3]!.val + 256 * bytes.val[4]!.val + 65536 * bytes.val[5]!.val)
            / 2 % 32 := by norm_num [decw]
    have d6 : decw bytes.val (5 * 6) 5
        = (bytes.val[3]!.val + 256 * bytes.val[4]!.val + 65536 * bytes.val[5]!.val)
            / 64 % 32 := by norm_num [decw]
    have d7 : decw bytes.val (5 * 7) 5
        = (bytes.val[4]!.val + 256 * bytes.val[5]!.val + 65536 * bytes.val[6]!.val)
            / 8 % 32 := by norm_num [decw]
    refine key _ ?_
    interval_cases k
    · show (c16 (bytes.val[0]! &&& 31#u8)).val = _
      rw [c16_val_nat, n0, d0]; omega
    · show (c16 (s1 ||| y05)).val = _
      rw [c16_val_nat, n1, d1]; omega
    · show (c16 (y12 &&& 31#u8)).val = _
      rw [c16_val_nat, n2, d2]; omega
    · show (c16 (s3 ||| y17)).val = _
      rw [c16_val_nat, n3, d3]; omega
    · show (c16 (s4 ||| y24)).val = _
      rw [c16_val_nat, n4, d4]; omega
    · show (c16 (y31 &&& 31#u8)).val = _
      rw [c16_val_nat, n5, d5]; omega
    · show (c16 (s6 ||| y36)).val = _
      rw [c16_val_nat, n6, d6]; omega
    · show (c16 y43).val = _
      rw [c16_val_nat, hy43v, d7]; omega

end MCBank

/-! ## Message (de)serialization — `d = 1`, exact 1:1 with the hacspec model.

    L5.1 (`deserialize_then_decompress_message_fc`) is stated at the END of this
    file, after its `L51Bank` section: it assembles `message_impl_fc` and
    `message_spec_eq`, which must therefore precede it. -/

/-! L5.2 (`compress_then_serialize_message_fc`) is stated at the END of this file,
    after its `L52Bank` section — for the same reason L5.1 is. It assembles M-D
    (`compress_message_coefficient_eq`, `compress_1_threshold_eq`) and M-C′
    (`compress_d_gen_eq`), all of which are declared further down, so the statement cannot
    sit here. Its `@[spec]` registration and the full locked statement are unchanged; only
    the position moved. -/

/-! ## Ciphertext component `v` — `d = dv`, exact 1:1 with the hacspec model. -/

/-! ### SPECREQ evidence for L5.3 (`deserialize_then_decompress_ring_element_v_fc`).

    HISTORY — this section refutes a statement that NO LONGER EXISTS in this form, and it
    is kept because it is why the current hypotheses are there. The ORIGINAL L5.3 statement
    was under-constrained: its precondition was `⌜True⌝`, while the Rust source of
    `deserialize_then_decompress_ring_element_v` carries

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

    The statement was RESTATED on 2026-08-18 with `h_rank` / `h_cf` / `h_len` transcribed
    verbatim from that `requires`, and CLOSED on 2026-08-19; the theorem now lives BELOW its
    proof bank, not immediately after this section. Nothing here edits or weakens it — the
    refutations are of the superseded form, and remain true of it. **Do not read this section
    as a claim about the current theorem.** (This prose has now been wrong twice: once by the
    restatement, once by the close relocating the theorem. If it drifts again, delete it and
    keep only the refutation lemmas, which speak for themselves.) -/

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
  simp only [CoreModels.core.slice.Slice.len,
      CoreModels.rust_primitives.slice.slice_length,
    CoreModels.rust_primitives.slice.slice_length, hlen]

/-- Spec side at `d = 4` on a zero-length input: the whole spec chain FAILS, so the
    spec/impl divergence this SPECREQ records still stands — only the *seam* moved.

    Until hax v0.4.0-rc.1 the seam was `byte_decode_dyn`'s `massert (len = 32 * d)`, and the
    failure was `.assertionFailure`. That `massert` is gone from the extraction (all 74
    spec-side `massert`s are), and `Error` itself lost the `assertionFailure` constructor —
    it is now just `panic | undef`. The chain fails one step later instead: at `d = 4` the
    dispatch does `try_from 128#usize serialized`, which returns `Result.Err ()` because
    `serialized.len = 0 ≠ 128`, and `Result.unwrap` on an `Err` is
    `core.panicking.internal.panic`, i.e. `.fail .panic`.

    So the conclusion is now `.fail .panic`. Read together with
    `specreq_L53_d4_empty_ok` (the impl SUCCEEDS on the same input), this is the same
    completed divergence argument as before, and it is still what forces the length
    hypothesis into the FC statement. -/
private theorem specreq_L53_spec_fail_of_empty (serialized : Slice Std.U8)
    (h : serialized.val.length = 0) :
    hacspec_ml_kem.serialize.deserialize_then_decompress_v serialized 4#usize
      = .fail .panic := by
  have hne : ¬ (Aeneas.Std.Slice.len serialized = (128#usize : Std.Usize)) := by
    intro hc
    have hlen : serialized.val.length = 128 := by
      have := congrArg Aeneas.Std.UScalar.val hc
      rw [Aeneas.Std.Slice.len_val] at this; simpa using this
    omega
  simp only [hacspec_ml_kem.serialize.deserialize_then_decompress_v,
    hacspec_ml_kem.serialize.byte_decode_dyn,
    show ((4#usize : Std.Usize)).val = 4 from rfl,
    CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from,
    dif_neg hne, Aeneas.Std.bind_tc_ok, CoreModels.core.result.Result.unwrap]
  rfl

/-- Impl side at `d = 4` on a zero-length input: `chunks_exact 8` produces no
    chunk, so the loop returns `output` unchanged — the impl SUCCEEDS. -/
private theorem specreq_L53_d4_empty_ok (serialized : Slice Std.U8)
    (h : serialized.val.length = 0)
    (output : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_4
      (vectortraitsOperationsInst := portable_ops_inst) serialized output
    ⦃ ⇓ p => ⌜ (Aeneas.Std.RustM.ok (p = output)).holds ⌝ ⦄ := by
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

/-! L5.3 (`deserialize_then_decompress_ring_element_v_fc`) is stated at the END of this
    file, after its `L53Bank2` section — for the same reason L5.1/L5.2 are. It assembles
    material declared further down (the generic spec-side decode ladder built on
    `L57Bank2`, and `MEBank`'s `decompress_d_gen_eq` /
    `decompress_ciphertext_coefficient_gen_fc`), so the scaffold position above the
    `L53Bank` rungs could not hold it. Its text is byte-identical to the locked form;
    only its position moved. -/

/-! ### PROVER bank toward the POSITIVE L5.3 proof.

    HISTORY, so this section is not misread: the section above refuted the ORIGINAL
    L5.3 statement, which had a `⌜True⌝` pre and no hypotheses. That statement was
    RESTATED on 2026-08-18 with `h_rank` / `h_cf` / `h_len` transcribed verbatim from
    the source's `#[hax_lib::requires]` (`ml-kem/src/serialize.rs` 337-340), and the
    restated form is the live obligation. **The `specreq_L53_*` refutations remain true
    and remain the REASON those hypotheses exist — they do not refute the current
    target.** Everything here is stated under the same hypotheses, i.e. it is what the
    re-locked obligation needs; nothing here weakens or hypothesises the locked
    statement.

    **CLOSED 2026-08-18.** L5.3 is now PROVED, at the end of this file; the rest of what
    it needed is in `L53Bank2` there. `specreq_L53_dispatch_eq_d4` (above) is the `d = 4`
    half of the first rung; `L53_dispatch_eq_d5` completes it, and `L53_dispatch_of_pre`
    is the rung itself, cited by the closed proof: under the dv-conjunct the dispatcher
    reduces to exactly one of the two real arms, with the `unreachable!()` arm eliminated.
    `specreq_L53_d4_empty_ok` (above) is the reusable `cs = 8` instantiation of the
    `chunks_exact` loop combinator. What the positive proof added on top is the per-chunk
    commute work at `d = 4` (8 bytes → 16 lanes) and `d = 5` (10 bytes → 16 lanes), the
    `d`-generic spec-side decode ladder, and `Decompress_d`. -/

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

    HISTORY, as for L5.3: L5.4's ORIGINAL statement carried the SAME defect, and was
    RESTATED on 2026-08-18 (see the binders on the theorem itself). The refutation below
    is why those binders exist; it does NOT refute the current target.
    Its source (`ml-kem/src/serialize.rs` 231-234) carries

        #[hax_lib::requires(
            out.len() == C2_LEN &&
            (V_COMPRESSION_FACTOR == 4 && C2_LEN == 128 ||
                V_COMPRESSION_FACTOR == 5 && C2_LEN == 160))]

    but the ORIGINAL scaffold transcribed only the `out.len() == C2_LEN` conjunct (as the
    binder `h_len`). `compress_then_serialize_ring_element_v` dispatches on the same
    `match V_COMPRESSION_FACTOR as u32 { 4, 5, _ => unreachable!() }`, so
    `V_COMPRESSION_FACTOR = 0` refutes the L5.4 Triple by the identical argument.

    The refutation below carries L5.4's `h_len` binder, so it refutes the obligation in
    its own exact shape rather than a convenient variant: the dropped conjunct is not
    recoverable from the one the scaffold kept. The L5.3 dispatch above was proved with
    the same three-lemma `simp only` normal form, so this cost one rung, not a dispatch.

    This is evidence, not a statement edit: the restatement it motivated was made by the
    PRINCIPAL-sanctioned scaffold pass, not here.

    **CLOSED 2026-08-19.** L5.4 is now PROVED, at the END of this file, from the `L54Bank`
    section there; `L54_dispatch_of_pre` is the positive form of this section's
    refutation, cited by that proof. Nothing below refutes the live target. (This prose
    has now drifted once, exactly as L5.3's did; if it drifts again, delete it and keep
    only the two refutation lemmas, which speak for themselves.) -/

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

/-! L5.4 (`compress_then_serialize_ring_element_v_fc`) is stated at the END of this file,
    after its `L54Bank` section — for the same reason L5.1/L5.2/L5.3 are. It assembles
    material declared further down (`MCPBank`'s `compress_barrett_eq` /
    `compress_ciphertext_coefficient_eq` / `compress_d_gen_eq`, and `L52Bank`'s
    `as_u8_eq` / `cu16_val` / `byte_encode_closure_eq_gen` /
    `bits_to_bytes_closure_eq_gen`), so the scaffold position above could not hold it.
    Its text is byte-identical to the locked form; only its position moved. -/


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
    ∃ z : Std.Usize, (x * y : RustM Std.Usize) = .ok z ∧ z.val = x.val * y.val := by
  obtain ⟨z, hz, hv, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.mul_bv_spec (x := x) (y := y) (by scalar_tac))
  exact ⟨z, hz, hv⟩

private theorem usize_add_ok (x y : Std.Usize) (hb : x.val + y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x + y : RustM Std.Usize) = .ok z ∧ z.val = x.val + y.val := by
  obtain ⟨z, hz, hv, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.add_bv_spec (x := x) (y := y) (by scalar_tac))
  exact ⟨z, hz, hv⟩

private theorem u16_add_ok (x y : Std.U16) (hb : x.val + y.val ≤ Std.U16.max) :
    ∃ z : Std.U16, (x + y : RustM Std.U16) = .ok z ∧ z.val = x.val + y.val := by
  obtain ⟨z, hz, hv, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.add_bv_spec (x := x) (y := y) (by scalar_tac))
  exact ⟨z, hz, hv⟩

/-- `1u16 << n` for `n < 16`: the shift result stays SYMBOLIC as `2 ^ n.val`
    (the closed-large-scalar pitfall — never `decide` on `1 <<< k`). -/
private theorem u16_shl_one_ok (n : Std.Usize) (hn : n.val < 16) :
    ∃ z : Std.U16, ((1#u16 : Std.U16) <<< n : RustM Std.U16) = .ok z
      ∧ z.val = 2 ^ n.val := by
  -- aeneas nightly-2026.08.24: now a `partialSpec`; the bounds moved out of the
  -- arguments into the postcondition and the `panic` precondition.
  obtain ⟨z, hz, hv, _, _⟩ :=
    Std.WP.spec_imp_exists (Std.WP.spec_of_partialSpec
      (Std.UScalar.ShiftLeft_spec (ty0 := .U16) (1#u16) n (Std.UScalar.size .U16) rfl)
      (by intro e; cases e <;> simp_all) (by simp))
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
    ∃ z : Std.U16, (x % y : RustM Std.U16) = .ok z ∧ z.val = x.val % y.val := by
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
    the raw and the `RustM` shape: `byte_decode_dyn`'s `try_from` needs the raw
    form for its `dif_pos`, and both entry points need the `RustM` form. -/
theorem slice_len_eq_384 (sl : Slice Std.U8) (h : sl.val.length = 384) :
    Aeneas.Std.Slice.len sl = (384#usize : Std.Usize) := by
  refine Aeneas.Std.UScalar.eq_of_val_eq ?_
  rw [Aeneas.Std.Slice.len_val]
  show sl.val.length = ((384#usize : Std.Usize)).val
  rw [h]; scalar_tac

theorem slice_len_384 (sl : Slice Std.U8) (h : sl.val.length = 384) :
    CoreModels.core.slice.Slice.len sl = .ok (384#usize : Std.Usize) := by
  simp only [CoreModels.core.slice.Slice.len,
      CoreModels.rust_primitives.slice.slice_length, slice_len_eq_384 sl h]



/-! ### The `d`-step bit-accumulation loop of `bitvector_to_bounded_ints`.

    Port of F* `dec_inv` / `dec_step` (`Commute.Serialize_bits.fst`): the loop
    invariant is exactly "the accumulator equals the partial bit sum", which is
    `bitSum` here. The residue never sees a bit-vector equality — `dec12` enters
    only at the apex, through `bitSum_sliceBit_eq_dec12`. -/

private theorem bvb_loop_fc {N Nd : Std.Usize} (a : Std.Array Bool Nd) (d j : Std.Usize)
    (hd : d.val ≤ 16)
    (hmul : j.val * d.val + d.val ≤ Std.Usize.max)
    (hbd : j.val * d.val + d.val ≤ Nd.val) :
    ⦃ ⌜ True ⌝ ⦄
    hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16.call_mut_loop
      (Nd := Nd) N { start := 0#usize, «end» := d } d a j 0#u16
    ⦃ ⇓ c => ⌜ c.val = bitSum (fun t => a.val[j.val * d.val + t]!) d.val ⌝ ⦄ := by
  have halen : a.val.length = Nd.val := a.property
  unfold
    hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16.call_mut_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, c1) =>
        hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16.call_mut_loop.body
          (Nd := Nd) N d a j iter1 c1)
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
              (Nd := Nd) N d a j ({ start := i, «end» := d } :
                CoreModels.core.ops.range.Range Std.Usize) acc
            = (if a.val[q.val]! = true then do
                  let i4 ← (1#u16 : Std.U16) <<< i
                  let coefficient1 ← acc + i4
                  RustM.ok (ControlFlow.cont
                    ((⟨s, d⟩ : CoreModels.core.ops.range.Range Std.Usize), coefficient1))
                else RustM.ok (ControlFlow.cont
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
                RustM.ok (ControlFlow.cont
                  ((⟨s, d⟩ : CoreModels.core.ops.range.Range Std.Usize), coefficient1))
              else RustM.ok (ControlFlow.cont
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
              (Nd := Nd) N d a j ({ start := i, «end» := d } :
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
              (Nd := Nd) N d a j ({ start := i, «end» := d } :
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
            (Nd := Nd) N d a j ({ start := i, «end» := d } :
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
          (Nd := Nd) N { start := 0#usize, «end» := d } d a ⟨BitVec.ofNat _ k⟩ 0#u16
      RustM.ok (coefficient, ((d, a) : Std.Usize × Std.Array Bool Nd))) = _
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
  have hmul : ((256#usize : Std.Usize) * (12#usize : Std.Usize) : RustM Std.Usize)
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
    -- hax v0.4.0-rc.1 no longer emits the `let i ← N * 8#usize; massert (N8 = i)` prelude
    -- (ALL 74 spec-side `massert`s are gone from the extraction), so the length check and
    -- its `hmul` witness are no longer part of this equation.
    simp only [hacspec_ml_kem.parameters.createi]
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
  have e1 : ((32#usize : Std.Usize) * (8#usize : Std.Usize) : RustM Std.Usize)
      = .ok (256#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have e2 : ((32#usize : Std.Usize) * (12#usize : Std.Usize) : RustM Std.Usize)
      = .ok (384#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have e3 : ((384#usize : Std.Usize) * (8#usize : Std.Usize) : RustM Std.Usize)
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
      RustM.ok (fe, decoded)) = _
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
  have e2 : ((32#usize : Std.Usize) * (12#usize : Std.Usize) : RustM Std.Usize)
      = .ok (384#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have e4 : ((256#usize : Std.Usize) * (12#usize : Std.Usize) : RustM Std.Usize)
      = .ok (3072#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have halen : a.val.length = 384 := by have := a.property; simpa using this
  have hslice : (Aeneas.Std.lift (Aeneas.Std.Array.to_slice a) : RustM (Slice Std.U8))
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
  have e2 : ((32#usize : Std.Usize) * (12#usize : Std.Usize) : RustM Std.Usize)
      = .ok (384#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  unfold hacspec_ml_kem.serialize.byte_decode_dyn
  -- (the `massert` prelude this `simp only` discharged is gone from the
  -- hax v0.4.0-rc.1 spec extraction; `unfold` now lands directly on the
  -- `match d.val` dispatch that the `show` below selects from)
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

/-! ## PROVER bank for L5.5 — the rank-K public-key decode apex.

    Two halves, in the file's established shape.

    * SPEC side (`spec_deser_pk_eq`): the hacspec `deserialize_ring_elements_reduced`
      IS `vector_decode_12`, i.e. a `createi RANK` whose closure `byte_decode`s the
      384-byte window `[i*384, i*384+384)` of the public key. That window is exactly
      `Spec.pk_chunk public_key i`, so the whole `createi` collapses to
      `Spec.t_as_ntt_from_public_key_pure` — the very definition the A2 axiom's post
      is stated against. NO bit-level reasoning enters: the per-window decode stays
      the `byte_decode_dyn` atom and the only fact needed about it is that it
      SUCCEEDS on a 384-byte slice, which `byte_decode_dyn_12_ok` reads off the
      file's own L5.7 banks (`deserialize_uncompressed_impl_fc` + `byte_decode_dyn_12_eq`).
    * IMPL side (`deser_pk_loop_fc` / `deser_pk_impl_fc`): the
      `Enumerate (ChunksExact 384)` loop, through the K10/K1 keystone
      `Matrix.ComputeRingElementV.Impl.loop_chunks_exact_pk_spec` at `cs = 384`
      (the exemplar: the suffix relation it threads is precisely the A2 axiom's
      `h_chunk_eq` hypothesis), with the A2 leaf
      `Serialize.deserialize_to_reduced_ring_element_fc` discharging each chunk.
      The invariant is the written prefix `pkInv`; no undone-cells conjunct is
      needed because the post only speaks about indices `< K`. -/

section L55Bank

open libcrux_iot_ml_kem.Util.CreateI

/-! ### Spec side. -/


/-- `Spec.pk_chunk` delivers a FULL 384-byte window at every `i < K`. -/
theorem pk_chunk_len_384 (public_key : Slice Std.U8) (K : Std.Usize)
    (h_pk : public_key.val.length = K.val * 384) (i : Nat) (hi : i < K.val) :
    (Spec.pk_chunk public_key i).val.length = 384 := by
  show ((public_key.val.drop (i * 384)).take 384).length = 384
  rw [List.length_take, List.length_drop, h_pk]
  have h : (i + 1) * 384 ≤ K.val * 384 := by apply Nat.mul_le_mul_right; omega
  omega


/-- The hacspec `BYTES_PER_RING_ELEMENT` reduces to `384` (both constants are
    `irreducible`, so this needs the explicit unfolding). -/
theorem hacspec_bpre :
    (hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT : RustM Std.Usize)
      = .ok (384#usize : Std.Usize) := by
  unfold hacspec_ml_kem.parameters.BYTES_PER_RING_ELEMENT
    hacspec_ml_kem.parameters.BITS_PER_RING_ELEMENT
    hacspec_ml_kem.parameters.COEFFICIENTS_IN_RING_ELEMENT
  rw [usize_mul_lit (256#usize : Std.Usize) (12#usize : Std.Usize)
    (3072#usize : Std.Usize) (by scalar_tac) (by scalar_tac)]
  simp only [Aeneas.Std.bind_tc_ok]
  exact usize_div_lit _ _ _ (by scalar_tac) (by scalar_tac)

/-- The impl-side `BYTES_PER_RING_ELEMENT`, same shape. -/
theorem impl_bpre :
    (libcrux_iot_ml_kem.constants.BYTES_PER_RING_ELEMENT : RustM Std.Usize)
      = .ok (384#usize : Std.Usize) := by
  unfold libcrux_iot_ml_kem.constants.BYTES_PER_RING_ELEMENT
    libcrux_iot_ml_kem.constants.BITS_PER_RING_ELEMENT
    libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
  rw [usize_mul_lit (256#usize : Std.Usize) (12#usize : Std.Usize)
    (3072#usize : Std.Usize) (by scalar_tac) (by scalar_tac)]
  simp only [Aeneas.Std.bind_tc_ok]
  exact usize_div_lit _ _ _ (by scalar_tac) (by scalar_tac)

/-- **`byte_decode` at `d = 12` never fails.** For every 384-byte array `a` (and
    every slice `b` with the same bytes), `byte_decode 3072 a 12` succeeds and
    `byte_decode_dyn b 12` reduces to it.

    This is the ONLY fact needed about the decode atom here: it is what makes the
    `| _ => default` branch of `Spec.t_as_ntt_from_public_key_pure` unreachable,
    and it is what lets the spec-side `createi` closure and the pure model be
    identified WITHOUT any bit-level reasoning. Proved from the file's own L5.7
    spec bank (`byte_decode_generic_12_get` + `byte_decode_closure_eq`), which are
    both unconditional. -/
theorem byte_decode_dyn_12_ok (b : Slice Std.U8) (a : Std.Array Std.U8 384#usize)
    (hab : a.val = b.val) :
    ∃ q : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize,
      hacspec_ml_kem.serialize.byte_decode_dyn b 12#usize = .ok q
      ∧ hacspec_ml_kem.serialize.byte_decode (D32 := 384#usize) 3072#usize a 12#usize
          = .ok q := by
  have halen : a.val.length = 384 := by have := a.property; simpa using this
  have hb : b.val.length = 384 := by rw [← hab]; exact halen
  obtain ⟨decoded, hdec, _⟩ := byte_decode_generic_12_get a
  have e2 : ((32#usize : Std.Usize) * (12#usize : Std.Usize) : RustM Std.Usize)
      = .ok (384#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have e4 : ((256#usize : Std.Usize) * (12#usize : Std.Usize) : RustM Std.Usize)
      = .ok (3072#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have hslice : (Aeneas.Std.lift (Aeneas.Std.Array.to_slice a) : RustM (Slice Std.U8))
      = .ok ⟨a.val, by scalar_tac⟩ := by
    simp [Aeneas.Std.lift, Aeneas.Std.Array.to_slice]
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
      (T := hacspec_ml_kem.parameters.FieldElement)
      (256#usize : Std.Usize)
      (hacspec_ml_kem.serialize.byte_decode.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement
        384#usize 3072#usize)
      decoded
      (fun k => ({ val := u16OfNat ((decoded.val[k]!).val % 3329) } :
                  hacspec_ml_kem.parameters.FieldElement))
      (fun k hk => byte_decode_closure_eq decoded k (by simpa using hk))
  have hbd : hacspec_ml_kem.serialize.byte_decode (D32 := 384#usize) 3072#usize a 12#usize
      = .ok ⟨(List.range (256#usize : Std.Usize).val).map
               (fun k => ({ val := u16OfNat ((decoded.val[k]!).val % 3329) } :
                           hacspec_ml_kem.parameters.FieldElement)),
             by simp⟩ := by
    unfold hacspec_ml_kem.serialize.byte_decode
    simp only [hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT, Aeneas.Std.massert,
      le_refl, if_true, Aeneas.Std.bind_tc_ok, hslice,
      slice_len_384 ⟨a.val, by scalar_tac⟩ halen, e2, e4, hdec,
      hacspec_ml_kem.parameters.createi, hfn]
  refine ⟨_, ?_, hbd⟩
  have hl := slice_len_eq_384 b hb
  have hlen := slice_len_384 b hb
  have haeq : a = (⟨b.val, by rw [hb]; scalar_tac⟩ : Std.Array Std.U8 384#usize) :=
    Subtype.ext hab
  unfold hacspec_ml_kem.serialize.byte_decode_dyn
  -- (the `massert` prelude this `simp only` discharged is gone from the
  -- hax v0.4.0-rc.1 spec extraction; `unfold` now lands directly on the
  -- `match d.val` dispatch that the `show` below selects from)
  show (do
      let r ←
        CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
          (384#usize : Std.Usize) b
      let a' ←
        CoreModels.core.result.Result.unwrap
          CoreModels.core.array.TryFromSliceError.Insts.CoreFmtDebug r
      hacspec_ml_kem.serialize.byte_decode (D32 := 384#usize) 3072#usize a' 12#usize) = _
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
  rw [haeq] at hbd
  exact hbd

/-! ### Spec side — `deserialize_ring_elements_reduced` IS the pure model.

    `deserialize_ring_elements_reduced RANK = vector_decode_12 RANK`, a `createi RANK`
    whose closure at index `k` slices `[k*384, k*384+384)` — i.e. exactly
    `Spec.pk_chunk` — and `byte_decode`s it at `d = 12`. `byte_decode_dyn_12_ok`
    identifies that array-shaped decode with the slice-shaped `byte_decode_dyn` the
    pure model uses, so the whole `createi` collapses to
    `Spec.t_as_ntt_from_public_key_pure` with NO bit-level reasoning. -/



/-- The `vector_decode_12` closure at index `k` decodes exactly `Spec.pk_chunk pk k`,
    hence produces the `k`-th cell of the pure model. -/
theorem vector_decode_12_closure_eq (K : Std.Usize) (public_key : Slice Std.U8)
    (h_pk : public_key.val.length = K.val * 384) (k : Nat) (hk : k < K.val) :
    (hacspec_ml_kem.serialize.vector_decode_12.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256
        K).call_mut public_key (⟨BitVec.ofNat _ k⟩ : Std.Usize)
      = .ok ((Spec.t_as_ntt_from_public_key_pure public_key K).val[k]!, public_key) := by
  have hk384' : k * 384 + 384 ≤ K.val * 384 := by
    have h : (k + 1) * 384 ≤ K.val * 384 := by apply Nat.mul_le_mul_right; omega
    calc k * 384 + 384 = (k + 1) * 384 := by ring
      _ ≤ K.val * 384 := h
  have hKmax : K.val * 384 ≤ Std.Usize.max := by
    rw [← h_pk]; exact public_key.property
  have hk384 : k * 384 + 384 ≤ Std.Usize.max := le_trans hk384' hKmax
  have h384 : ((384#usize : Std.Usize)).val = 384 := rfl
  have hkval : ((⟨BitVec.ofNat _ k⟩ : Std.Usize)).val = k :=
    usize_ofNat_val_le k (le_trans (Nat.le_trans (Nat.le_mul_of_pos_right k (by omega))
      (Nat.le_add_right _ 384)) hk384)
  -- start = k * 384, end = k * 384 + 384
  obtain ⟨st, hst_eq, hst_val⟩ :=
    usize_mul_ok_e (⟨BitVec.ofNat _ k⟩ : Std.Usize) (384#usize : Std.Usize)
      (by rw [hkval, h384]; exact le_trans (Nat.le_add_right _ 384) hk384)
  rw [hkval, h384] at hst_val
  obtain ⟨en, hen_eq, hen_val⟩ :=
    usize_add_ok_e st (384#usize : Std.Usize) (by rw [hst_val, h384]; exact hk384)
  have hen_val' : en.val = k * 384 + 384 := by
    rw [hen_val, hst_val, h384]
  -- the sliced window IS `Spec.pk_chunk`
  have hchunk_len : (Spec.pk_chunk public_key k).val.length = 384 :=
    pk_chunk_len_384 public_key K h_pk k hk
  have hslice_eq : (⟨List.slice st.val en.val public_key.val, by
        have := public_key.val.slice_length_le st.val en.val; scalar_tac⟩ : Slice Std.U8)
      = Spec.pk_chunk public_key k := by
    apply Subtype.ext
    show List.slice st.val en.val public_key.val
        = (public_key.val.drop (k * 384)).take 384
    unfold List.slice
    rw [hst_val, hen_val']
    congr 1
    omega
  have hidx := slice_range_index_ok public_key st en
    (by rw [hst_val, hen_val']; omega) (by rw [hen_val', h_pk]; exact hk384')
  rw [hslice_eq] at hidx
  -- the array conversion
  have htry :
      CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
          (384#usize : Std.Usize) (Spec.pk_chunk public_key k)
        = .ok (CoreModels.core.result.Result.Ok
            (⟨(Spec.pk_chunk public_key k).val, by rw [hchunk_len]; scalar_tac⟩ :
              Std.Array Std.U8 384#usize)) := by
    unfold
      CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
    rw [dif_pos (slice_len_eq_384 _ hchunk_len)]
  obtain ⟨q, hq_dyn, hq_arr⟩ :=
    byte_decode_dyn_12_ok (Spec.pk_chunk public_key k)
      ⟨(Spec.pk_chunk public_key k).val, by rw [hchunk_len]; scalar_tac⟩ rfl
  have hcell : (Spec.t_as_ntt_from_public_key_pure public_key K).val[k]! = q := by
    show ((List.range K.val).map (fun i =>
        match hacspec_ml_kem.serialize.byte_decode_dyn (Spec.pk_chunk public_key i) 12#usize with
        | .ok p => p
        | _ => default))[k]! = q
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
    simp only [Option.map_some, Option.getD_some, hq_dyn]
  show (hacspec_ml_kem.serialize.vector_decode_12.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut
      (RANK := K) public_key (⟨BitVec.ofNat _ k⟩ : Std.Usize)) = _
  unfold
    hacspec_ml_kem.serialize.vector_decode_12.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut
  rw [hacspec_bpre]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hst_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hen_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hidx]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [htry]
  simp only [Aeneas.Std.bind_tc_ok, CoreModels.core.result.Result.unwrap]
  rw [hq_arr]
  simp only [Aeneas.Std.bind_tc_ok, hcell]

/-- **The spec bridge.** The hacspec rank-K decode is the pure model
    `Spec.t_as_ntt_from_public_key_pure`, i.e. `lift_t_as_ntt_from_public_key`. -/
private theorem spec_deser_pk_eq (K : Std.Usize) (public_key : Slice Std.U8)
    (h_pk : public_key.val.length = K.val * 384) :
    hacspec_ml_kem.serialize.deserialize_ring_elements_reduced K public_key
      = .ok (lift_t_as_ntt_from_public_key public_key K) := by
  have hKmax : K.val * 384 ≤ Std.Usize.max := by
    rw [← h_pk]; exact public_key.property
  obtain ⟨tot, htot_eq, htot_val⟩ :=
    usize_mul_ok_e K (384#usize : Std.Usize) (by scalar_tac)
  have htot_val' : tot.val = K.val * 384 := by rw [htot_val]; scalar_tac
  have hlen_eq : Aeneas.Std.Slice.len public_key = tot := by
    apply Aeneas.Std.UScalar.eq_of_val_eq
    rw [Aeneas.Std.Slice.len_val, htot_val']
    exact h_pk
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
      (T := Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
      K
      (hacspec_ml_kem.serialize.vector_decode_12.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256
        K)
      public_key
      (fun k => (Spec.t_as_ntt_from_public_key_pure public_key K).val[k]!)
      (fun k hk => vector_decode_12_closure_eq K public_key h_pk k hk)
  -- hax v0.4.0-rc.1 dropped the `len encoded` / `t_as_ntt_encoded_size` / `massert` prelude
  -- from both spec functions, so `hlen_eq`, `hacspec_bpre` and `htot_eq` no longer take part:
  -- what is left is the `createi` step alone.
  unfold hacspec_ml_kem.serialize.deserialize_ring_elements_reduced
    hacspec_ml_kem.serialize.vector_decode_12
  simp only [hacspec_ml_kem.parameters.createi, hfn]
  -- the two `List.range K` maps agree pointwise
  congr 1
  apply Subtype.ext
  show (List.range K.val).map (fun k => (Spec.t_as_ntt_from_public_key_pure public_key K).val[k]!)
      = (Spec.t_as_ntt_from_public_key_pure public_key K).val
  have hval : (Spec.t_as_ntt_from_public_key_pure public_key K).val.length = K.val := by
    exact (Spec.t_as_ntt_from_public_key_pure public_key K).property
  refine List.ext_getElem (by simp [hval]) ?_
  intro n h1 h2
  rw [List.getElem_map, List.getElem_range]
  rw [getElem!_pos _ _ (by rw [hval]; simpa using h1)]

/-! ### Impl side — the rank-K `Enumerate (ChunksExact 384)` loop.

    K10/K1 keystone `Matrix.ComputeRingElementV.Impl.loop_chunks_exact_pk_spec` at
    `cs = 384`: the suffix relation it threads to the step IS the A2 axiom's
    `h_chunk_eq` hypothesis. The invariant is the written prefix (no
    undone-cells conjunct: the post only speaks about indices `< K`). -/

/-- Written-prefix invariant for the rank-K decode loop. -/
private def pkInv (public_key : Slice Std.U8) (K : Std.Usize) (k : Nat)
    (p : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)) : Prop :=
  p.length = K.val
  ∧ (∀ i : Nat, i < k →
      lift_poly (p.val[i]!) = (lift_t_as_ntt_from_public_key public_key K).val[i]!)
  ∧ (∀ i : Nat, i < k → ∀ c : Nat, c < 16 → ∀ ℓ : Nat, ℓ < 16 →
      (((p.val[i]!).coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328)




open libcrux_iot_ml_kem.Matrix.ComputeRingElementV.Impl in
/-- The rank-K loop: after `K` chunks the written prefix covers every index `< K`. -/
private theorem deser_pk_loop_fc (K : Std.Usize) (public_key : Slice Std.U8)
    (h_pk_len : public_key.val.length = K.val * 384)
    (deserialized_pk : Slice
        (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (h_out_len : deserialized_pk.length = K.val) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_ring_elements_reduced_loop
      (vectortraitsOperationsInst := portable_ops_inst)
      { iter := { cs := 384#usize, elements := public_key }, count := 0#usize } deserialized_pk
    ⦃ ⇓ p => ⌜ (Aeneas.Std.RustM.ok (pkInv public_key K K.val p)).holds ⌝ ⦄ := by
  have h384 : ((384#usize : Std.Usize)).val = 384 := rfl
  have hKmax : K.val * 384 ≤ Std.Usize.max := by rw [← h_pk_len]; exact public_key.property
  have hK_le : K.val ≤ Std.Usize.max :=
    le_trans (Nat.le_mul_of_pos_right _ (by omega)) hKmax
  unfold libcrux_iot_ml_kem.serialize.deserialize_ring_elements_reduced_loop
  refine loop_chunks_exact_pk_spec _ deserialized_pk public_key 384#usize K.val
    (fun k acc => .ok (pkInv public_key K k acc)) (by rw [h384]; omega)
    (by rw [h384]; simpa [Aeneas.Std.Slice.length] using h_pk_len)
    ((holds_ok _).mpr ⟨h_out_len, by intro i hi; omega, by intro i hi; omega⟩) ?_
  intro acc k rest cnt hk hcnt hrest hsuf hinv
  obtain ⟨hacc_len, hacc_lift, hacc_bnd⟩ := (holds_ok _).mp hinv
  rw [h384] at hrest
  simp only [h384] at hsuf
  by_cases hlt : k < K.val
  · -- a full 384-byte chunk remains
    have hrest384 : 384 ≤ rest.length := by
      rw [hrest]
      calc (384 : Nat) = 1 * 384 := by ring
        _ ≤ (K.val - k) * 384 := Nat.mul_le_mul_right 384 (by omega)
    obtain ⟨chunk, drop, cnt', hnext, hcnt', hclen, hdlen, hcget, hdget⟩ :=
      enumerate_chunks_next_cont_drop rest 384#usize cnt
        (by rw [h384]; exact hrest384) (by rw [hcnt]; omega)
    have hcnt_lt : cnt.val < K.val := by rw [hcnt]; exact hlt
    have hacc_idx : cnt.val < acc.val.length := by
      have : acc.val.length = K.val := hacc_len
      omega
    -- the chunk sits at byte offset `cnt.val * 384` of the public key
    have hchunk_pk : ∀ ℓ : Nat, ℓ < 384 →
        chunk.val[ℓ]! = public_key.val[cnt.val * 384 + ℓ]! := by
      intro ℓ hℓ
      rw [hcget ℓ (by rw [h384]; omega), hsuf ℓ, hcnt]
    have hchunk_len : chunk.length = 384 := by rw [hclen, h384]
    -- A2: the per-element leaf
    obtain ⟨te1, hte_eq, hte_lift, hte_bnd⟩ :=
      triple_exists_ok_fc
        (libcrux_iot_ml_kem.Serialize.deserialize_to_reduced_ring_element_fc
          public_key K (acc.val[cnt.val]!) cnt h_pk_len hcnt_lt chunk hchunk_len hchunk_pk)
    refine triple_of_ok_fc
      (v := .cont ({ iter := { cs := 384#usize, elements := drop }, count := cnt' },
                   Aeneas.Std.Slice.set acc cnt te1)) ?_ ?_
    · show libcrux_iot_ml_kem.serialize.deserialize_ring_elements_reduced_loop.body
        portable_ops_inst { iter := { cs := 384#usize, elements := rest }, count := cnt } acc = _
      unfold libcrux_iot_ml_kem.serialize.deserialize_ring_elements_reduced_loop.body
      rw [show (CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
            (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice Std.U8)
            { iter := { cs := 384#usize, elements := rest }, count := cnt })
          = .ok (CoreModels.core.option.Option.Some (cnt, chunk),
                 { iter := { cs := 384#usize, elements := drop }, count := cnt' }) from hnext]
      simp only [Aeneas.Std.bind_tc_ok]
      show (do
          let (pre, index_mut_back) ← Aeneas.Std.Slice.index_mut_usize acc cnt
          let pre1 ← libcrux_iot_ml_kem.serialize.deserialize_to_reduced_ring_element
            portable_ops_inst chunk pre
          RustM.ok (ControlFlow.cont
            (({ iter := { cs := 384#usize, elements := drop }, count := cnt' } : EnumCE),
             index_mut_back pre1))) = _
      rw [slice_index_mut_ok acc cnt hacc_idx]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [hte_eq]
      rfl
    · refine ⟨hlt, rfl, (by show cnt'.val = k + 1; rw [hcnt', hcnt]), ?_, ?_, ?_⟩
      · show drop.length = (K.val - (k + 1)) * (384#usize : Std.Usize).val
        rw [h384, hdlen, hrest, h384]
        have hsplit : (K.val - k) = (K.val - (k + 1)) + 1 := by omega
        rw [hsplit]; ring_nf; omega
      · intro ℓ
        simp only [h384]
        rw [hdget ℓ]
        simp only [h384]
        rw [hsuf (384 + ℓ)]
        have hidx : k * 384 + (384 + ℓ) = (k + 1) * 384 + ℓ := by ring
        rw [hidx]
      · refine (holds_ok _).mpr ⟨?_, ?_, ?_⟩
        · rw [slice_set_length]; exact hacc_len
        · intro i hi
          have hilen : i < acc.val.length := by
            have : acc.val.length = K.val := hacc_len
            omega
          rw [slice_set_get acc cnt te1 i hilen]
          by_cases hik : i = cnt.val
          · rw [if_pos hik, hik]
            exact hte_lift
          · rw [if_neg hik]
            exact hacc_lift i (by rw [hcnt] at hik; omega)
        · intro i hi c hc ℓ hℓ
          have hilen : i < acc.val.length := by
            have : acc.val.length = K.val := hacc_len
            omega
          rw [slice_set_get acc cnt te1 i hilen]
          by_cases hik : i = cnt.val
          · rw [if_pos hik]; exact hte_bnd c hc ℓ hℓ
          · rw [if_neg hik]
            exact hacc_bnd i (by rw [hcnt] at hik; omega) c hc ℓ hℓ
  · -- no full chunk remains: k = K, the loop is done
    have hkK : k = K.val := by omega
    have hrest0 : rest.length = 0 := by rw [hrest, hkK]; simp
    refine triple_of_ok_fc (v := .done acc) ?_ ?_
    · show libcrux_iot_ml_kem.serialize.deserialize_ring_elements_reduced_loop.body
        portable_ops_inst { iter := { cs := 384#usize, elements := rest }, count := cnt } acc = _
      unfold libcrux_iot_ml_kem.serialize.deserialize_ring_elements_reduced_loop.body
      rw [show (CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
            (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice Std.U8)
            { iter := { cs := 384#usize, elements := rest }, count := cnt })
          = .ok (CoreModels.core.option.Option.None,
                 { iter := { cs := 384#usize, elements := rest }, count := cnt }) from
          enumerate_chunks_next_done rest 384#usize cnt (by rw [h384, hrest0]; omega)]
      rfl
    · refine (holds_ok _).mpr ⟨hacc_len, ?_, ?_⟩
      · intro i hi; exact hacc_lift i (by omega)
      · intro i hi; exact hacc_bnd i (by omega)

end L55Bank

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
    -- UNIFORMITY (KB, 2026-08-20): `is_rank` is transcribed wherever UPSTREAM carries it,
    -- even where a measurement says the statement is true without it. Rationale: every
    -- caller has it, so discharging it is free — unlike a bound such as `h_bnd`, which is
    -- real work for the consumer and therefore belongs in exactly one measured place. The
    -- rule it replaces ("drop what is measured unnecessary") was applied correctly here and
    -- then GENERALISED to `serialize_public_key_mut_fc`, where it was false and cost three
    -- rungs. Uniform transcription removes that judgement call per obligation.
    -- This statement remains TRUE without it (measured at K = 0, 1 and 5); adding a
    -- hypothesis only WEAKENS it, so the existing proof stands unchanged.
    (h_rank : hacspec_ml_kem.parameters.is_rank K = .ok true)
    (h_pk_len : public_key.length = K.val * 384)
    (h_out_len : deserialized_pk.length = K.val) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_ring_elements_reduced
      (vectortraitsOperationsInst := portable_ops_inst)
      K public_key deserialized_pk
    ⦃ ⇓ p => ⌜ p.length = K.val
                ∧ hacspec_ml_kem.serialize.deserialize_ring_elements_reduced K public_key
                  = .ok (lift_vec_slice p K)
                -- The K-fold apex must re-export the canonicality its own per-element
                -- leaf already asserts (Serialize.lean:53, the A2 axiom): the impl runs
                -- `cond_subtract_3329`, and downstream matrix consumers bind `≤ 3328`.
                -- Dropping it here made the apex true but undischargeable for them.
                ∧ (∀ i : Nat, i < K.val → ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
                    (((p.val[i]!).coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs
                      ≤ 3328) ⌝ ⦄ := by
  have h_pk : public_key.val.length = K.val * 384 := h_pk_len
  obtain ⟨p, hp_eq, hp_holds⟩ :=
    triple_exists_ok_fc (deser_pk_loop_fc K public_key h_pk deserialized_pk h_out_len)
  obtain ⟨hp_len, hp_lift, hp_bnd⟩ := (holds_ok _).mp hp_holds
  -- the impl reduces to the loop: classify_ref / ct_declassify are identities,
  -- `BYTES_PER_RING_ELEMENT = 384`, and chunks_exact+enumerate is the initial state.
  refine triple_of_ok_fc (v := p) ?_ ?_
  · unfold libcrux_iot_ml_kem.serialize.deserialize_ring_elements_reduced
    rw [show (libcrux_secrets.SharedASlice.Insts.Libcrux_secretsTraitsClassifyRefSharedASlice.classify_ref
          libcrux_secrets.U8.Insts.Libcrux_secretsTraitsScalar public_key)
        = .ok public_key from rfl]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [impl_bpre]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [show (CoreModels.core.slice.Slice.chunks_exact public_key (384#usize : Std.Usize))
          = .ok { cs := 384#usize, elements := public_key } from rfl]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [show (CoreModels.core.iter.traits.iterator.Iterator.enumerate.default
          (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice
            Std.U8)
          { cs := (384#usize : Std.Usize), elements := public_key })
        = .ok ({ iter := { cs := 384#usize, elements := public_key },
                 count := 0#usize } :
                libcrux_iot_ml_kem.Matrix.ComputeRingElementV.Impl.EnumCE) from rfl]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hp_eq]
    simp only [Aeneas.Std.bind_tc_ok, libcrux_secrets.mem_requests.ct_declassify]
  · -- the three post conjuncts
    refine ⟨hp_len, ?_, hp_bnd⟩
    have hvec : lift_vec_slice p K = lift_t_as_ntt_from_public_key public_key K := by
      apply Subtype.ext
      show (List.range K.val).map (fun i => lift_poly p.val[i]!)
          = (lift_t_as_ntt_from_public_key public_key K).val
      have hlen : (lift_t_as_ntt_from_public_key public_key K).val.length = K.val :=
        (lift_t_as_ntt_from_public_key public_key K).property
      refine List.ext_getElem (by simp [hlen]) ?_
      intro n h1 h2
      rw [List.getElem_map, List.getElem_range]
      have hn : n < K.val := by simpa using h1
      rw [hp_lift n hn, getElem!_pos _ _ (by rw [hlen]; exact hn)]
    rw [hvec]
    exact spec_deser_pk_eq K public_key h_pk

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
    (h_len : serialized.length = 384)
    -- ENCODE precondition, machine-falsified before adding: without it this statement is
    -- FALSE. `byte_encode` reads a canonicalised `FieldElement.val` while the impl's
    -- `to_unsigned_field_modulus` adds q AT MOST ONCE, so an unreduced lane diverges.
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
        ((re.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 3328) :
    -- Counterexample without h_bnd (evaluated on the extracted impl): lane 3400 ->
    -- impl bytes [72,13,0] (payload 0xD48); spec byte_encode of canon(3400)=71 -> [71,0,0].
    -- Tight: 3329 diverges, 3328 agrees. This is the `hbnd` the file's own prover bank
    -- already carries at L1601 -- the hypothesis was present in the PROOF and missing
    -- from the STATEMENT, which is why this obligation blocked twice ($71.82).
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.serialize_uncompressed_ring_element
      (vectortraitsOperationsInst := portable_ops_inst)
      re scratch serialized
    ⦃ ⇓ p => ⌜ hacspec_ml_kem.serialize.byte_encode_into (lift_poly re) 12#usize serialized
                = .ok p.2 ⌝ ⦄ := by
  -- Impl side: the 16-chunk `0..16` range loop writes `encByte re` into all 384 bytes.
  have hlen' : serialized.val.length = 384 := h_len
  obtain ⟨p, hp_eq, hp⟩ :=
    triple_exists_ok_fc (serialize_uncompressed_impl_fc re h_bnd scratch serialized hlen')
  obtain ⟨hp_len, hp_get⟩ := (holds_ok _).mp hp
  -- Spec side: M-B(2), stated at exactly this post's `byte_encode_into … = .ok _`.
  obtain ⟨s, hs_eq, hs_len, hs_get⟩ := byte_encode_into_12_eq re serialized h_len
  refine triple_of_ok_fc hp_eq ?_
  rw [hs_eq]
  -- Both slices are 384 bytes and byte `n` of each is `encByte re n`, so they are equal.
  have hs_len' : s.val.length = 384 := hs_len
  have hsp : s = p.2 := by
    apply Subtype.ext
    refine List.ext_getElem (by rw [hs_len', hp_len]) ?_
    intro n h1 h2
    have hn : n < 384 := by rw [hs_len'] at h1; exact h1
    refine Aeneas.Std.UScalar.eq_of_val_eq ?_
    rw [← getElem!_pos s.val n h1, ← getElem!_pos p.2.val n h2,
      hs_get n hn, hp_get n (by scalar_tac)]
  rw [hsp]

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
    ⦃ ⇓ p => ⌜ (hacspec_ml_kem.serialize.byte_decode_dyn serialized 12#usize
                  = .ok (lift_poly p))
                ∧ (∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
                    ((p.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs
                      ≤ 4095) ⌝ ⦄ := by
  -- Impl side: the 16-chunk `chunks_exact 24` loop puts `dec12` in every lane.
  have hlen' : serialized.val.length = 384 := by
    simpa [Aeneas.Std.Slice.length] using h_len
  obtain ⟨p, hp_eq, hp⟩ :=
    triple_exists_ok_fc (deserialize_uncompressed_impl_fc serialized hlen' re)
  have hdec : declane serialized.val p 16 := (holds_ok _).mp hp
  refine triple_of_ok_fc hp_eq ⟨byte_decode_dyn_12_eq serialized hlen' p hdec, ?_⟩
  -- BOUND CONJUNCT (added 2026-08-18 per KB: transcribe the `ensures`).
  -- Upstream `libcrux-ml-kem/src/serialize.rs` ensures `is_bounded_poly(4096, &result)`;
  -- stated here at the TIGHTER true bound 4095, which implies it. Both inputs are
  -- already banked in this file:
  --   `hdec`     : declane => lane .val = (dec12 serialized.val (16*chunk+ℓ) : Int)
  --   `dec12_lt` : (:213) dec12 l j < 4096, unconditionally
  -- so each lane is a non-negative Int below 4096 and its natAbs is ≤ 4095.
  intro chunk hchunk ℓ hℓ
  have hlane := hdec chunk hchunk ℓ hℓ
  have hb := dec12_lt serialized.val (16 * chunk + ℓ)
  omega


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
    (x >>> s : RustM Std.U8) = .ok (shr8 x k) := by
  have h0 : (0:Int) ≤ s.val := by rw [hsv]; exact Int.natCast_nonneg k
  have hk : Std.IScalar.toNat s = k := by
    show s.val.toNat = k
    rw [hsv]; exact Int.toNat_natCast k
  -- aeneas nightly-2026.08.24: now a `partialSpec`; the bounds moved out of the
  -- arguments into the postcondition and the `panic` precondition.
  obtain ⟨z, hz, _hzv, hzbv, _⟩ :=
    Std.WP.spec_imp_exists (Std.WP.spec_of_partialSpec
      (Std.UScalar.ShiftRight_IScalar_spec (ty0 := .U8) x s)
      (by intro e; cases e <;> simp_all <;> omega) (by simp))
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
    ⦃ ⇓ p => ⌜ (Aeneas.Std.RustM.ok (msglane serialized.val p 16)).holds ⌝ ⦄ := by
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
            RustM.ok (ControlFlow.cont
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
    ⦃ ⇓ p => ⌜ (Aeneas.Std.RustM.ok (msglane serialized.val p 16)).holds ⌝ ⦄ :=
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
      RustM.ok (decide (i4 = 1#u8), a)) = _
  rw [hq_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hidx]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hy_eq]; simp only [Aeneas.Std.bind_tc_ok]
  show RustM.ok (decide (y &&& 1#u8 = 1#u8), a) = _
  rw [hy]
  unfold sliceBit
  rw [hq16, hr8]

private theorem bytes_to_bits_get_32 (a : Std.Array Std.U8 32#usize) :
    ∃ bv : Std.Array Bool 256#usize,
      hacspec_ml_kem.serialize.bytes_to_bits (N := 32#usize) 256#usize a = .ok bv
      ∧ ∀ m : Nat, m < 256 → bv.val[m]! = sliceBit a.val m := by
  have hmul : ((32#usize : Std.Usize) * (8#usize : Std.Usize) : Aeneas.Std.RustM Std.Usize)
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
    -- hax v0.4.0-rc.1 no longer emits the `let i ← N * 8#usize; massert (N8 = i)` prelude
    -- (ALL 74 spec-side `massert`s are gone from the extraction), so the length check and
    -- its `hmul` witness are no longer part of this equation.
    simp only [hacspec_ml_kem.parameters.createi]
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
  have hmul : ((256#usize : Std.Usize) * (1#usize : Std.Usize) : RustM Std.Usize)
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
    -- hax v0.4.0-rc.1 no longer emits the `let i ← N * 8#usize; massert (N8 = i)` prelude
    -- (ALL 74 spec-side `massert`s are gone from the extraction), so the length check and
    -- its `hmul` witness are no longer part of this equation.
    simp only [hacspec_ml_kem.parameters.createi]
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
  have e1 : ((32#usize : Std.Usize) * (8#usize : Std.Usize) : RustM Std.Usize)
      = .ok (256#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have e2 : ((32#usize : Std.Usize) * (1#usize : Std.Usize) : RustM Std.Usize)
      = .ok (32#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  refine ⟨arr, ?_, ?_⟩
  · unfold hacspec_ml_kem.serialize.byte_decode_generic
    simp only [hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT, Aeneas.Std.massert,
      if_pos hle, Aeneas.Std.bind_tc_ok, e1, e2, if_true, hbv, harr]
  · intro k hk
    rw [harrget k hk, hbvget k hk]

-- The spec chain elaborates deeper terms under the hax v0.4.0-rc.1 slice/array models
-- (the `massert` prelude used to break the `do` block into shallower pieces).
set_option maxRecDepth 4000 in
private theorem byte_decode_1_get (a : Std.Array Std.U8 32#usize) :
    ∃ arr : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize,
      hacspec_ml_kem.serialize.byte_decode (D32 := 32#usize) 256#usize a 1#usize = .ok arr
      ∧ ∀ k : Nat, k < 256 →
          arr.val[k]! = { val := u16OfNat (if sliceBit a.val k then 1 else 0) } := by
  obtain ⟨decoded, hdec, hdecget⟩ := byte_decode_generic_1_get a
  have hle : ((1#usize : Std.Usize) ≤ (12#usize : Std.Usize)) := by scalar_tac
  have h256 : ((256#usize : Std.Usize)).val = 256 := by scalar_tac
  have e2 : ((32#usize : Std.Usize) * (1#usize : Std.Usize) : RustM Std.Usize)
      = .ok (32#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have e4 : ((256#usize : Std.Usize) * (1#usize : Std.Usize) : RustM Std.Usize)
      = .ok (256#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have halen : a.val.length = 32 := by have := a.property; simpa using this
  have hslice : (Aeneas.Std.lift (Aeneas.Std.Array.to_slice a) : RustM (Slice Std.U8))
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
    simp only [CoreModels.core.slice.Slice.len,
      CoreModels.rust_primitives.slice.slice_length, this]
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
    ∃ z : Std.U32, (x * y : RustM Std.U32) = .ok z ∧ z.val = x.val * y.val := by
  obtain ⟨z, hz, hv, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.mul_bv_spec (x := x) (y := y) (by scalar_tac))
  exact ⟨z, hz, hv⟩

private theorem u32_add_ok (x y : Std.U32) (hb : x.val + y.val ≤ Std.U32.max) :
    ∃ z : Std.U32, (x + y : RustM Std.U32) = .ok z ∧ z.val = x.val + y.val := by
  obtain ⟨z, hz, hv, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.add_bv_spec (x := x) (y := y) (by scalar_tac))
  exact ⟨z, hz, hv⟩

private theorem u32_div_ok (x y : Std.U32) (hy : 0 < y.val) :
    ∃ z : Std.U32, (x / y : RustM Std.U32) = .ok z ∧ z.val = x.val / y.val := by
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
      RustM.ok (fe1, ((arr, 1#usize) : hacspec_ml_kem.compress.decompress.closure))) = _
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

-- The spec chain elaborates deeper terms under the hax v0.4.0-rc.1 slice/array models
-- (the `massert` prelude used to break the `do` block into shallower pieces).
set_option maxRecDepth 4000 in
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

/-! ## M-E — DECOMPRESS at a general `d` (kind K6).

    THE EXEMPLAR for readiness-map kind K6, which is `PARTIAL — d = 1 only`. At `d = 1`
    the value set is `{0, 1665}`, so the whole thing is a two-case `decide`; there is no
    rounding argument at all. At a general `d` there is: an arithmetic shift right on a
    signed 32-bit value has to be identified with floor division, and the `.as_i16()`
    truncation at the end has to be shown faithful.

    BOTH SIDES ARE ABSENT at general `d`, which is why this bank has two statements
    rather than one. The tree's `decompress_d_1_eq` (`:4461`) is the SPEC side at
    `d = 1`; the IMPL side at `d = 1` is `decompress_1` (`:4272`, a `negate`-then-`& 1665`
    special case that shares no code with the general path). Neither transfers.

    ## Falsified before locking (`references/mlkem-falsify-harness.lean`)

    SPEC side: EXHAUSTIVE over every `x < 2 ^ d` at `d ∈ {1,4,5,10,11}`, and swept over
    EVERY `d < 12` (first 300 values each). Zero counterexamples — so the closed form is
    generic in `d < 12`, not merely valid at the four widths ML-KEM instantiates. Stated
    generically for that reason.
    IMPL side: `d ∈ {4,5,10,11}`, 25 random lane-vectors each plus the `0` and `2^d - 1`
    boundary vectors. Zero counterexamples.
    NEGATIVE CONTROL: with lanes NOT `< 2 ^ d` the impl statement is REFUTED immediately
    (lanes come back as arbitrary signed junk, e.g. `-16026`, because `.as_i16()`
    truncates a result that no longer fits). `hlane` is load-bearing, not decoration —
    this is the `pair it with a < 2^d` caveat AMENDMENTS 2 records for M-E, now measured.

    ## On the precondition — ours is deliberately STRONGER than the Rust's

    iot `ml-kem/src/vector/portable/compress.rs:89` says
    `#[hax_lib::requires(0 <= COEFFICIENT_BITS && COEFFICIENT_BITS < 31)]`. That is a
    PANIC-FREEDOM precondition (it keeps the shift well-defined), NOT a correctness one:
    verified by hand that no `I32` overflow is possible for ANY `I16` lane at any `d < 31`
    (`2 · 32767 · 3329 + 2 ^ 30 = 1,291,904,510 < 2 ^ 31`). Correctness of the RESULT needs
    more, and the extra hypotheses are not invented — `hd` is the spec's own
    `massert (to_bit_size < 12)` and `hlane` is its own `massert (fe.val < 1 <<< d)`.
    Transcribing only the Rust `requires` would give a TRUE panic-freedom statement that
    says nothing about decompression, which is the "true but useless for composition"
    failure mode `references/mlkem-inc1-contracts.txt` rule 2 exists to prevent.

    ## Provenance

    MINE, DO NOT PORT. ml-dsa `Vector/Portable/Rounding.lean:65` `sshiftRight_val_i32` is
    a full exemplar for the shift-is-division step and is `private` — a template to COPY,
    never to import (it is a different lake package). -/

section MEBank

/-! ### Scaffolding for the general-`d` spec side.

    The `d = 1` proof (`:4461`) got `two_pow_bit_size` by `rfl` because `2 ^ 1` is a
    closed scalar. At a general `d` the `U32.pow` call has to be discharged
    symbolically, which needs the `UScalar.tryMk` success lemma the tree does not
    yet carry. `2 ^ d.val` is kept an ATOM throughout — never a closed large
    scalar (the skill §6 pitfall). -/

/-- `UScalar.tryMk` at `U32` succeeds and is faithful strictly below `2 ^ 32`. -/
private theorem u32_tryMk_ok (x : Nat) (hx : x < 2 ^ 32) :
    ∃ z : Std.U32, Std.UScalar.tryMk .U32 x = .ok z ∧ z.val = x := by
  have hb : Std.UScalar.inBounds .U32 x := by
    simpa [Std.UScalarTy.numBits] using hx
  have hm := Std.UScalar.tryMk_eq .U32 x
  revert hm
  cases h : Std.UScalar.tryMk .U32 x with
  | ok z => intro hm; exact ⟨z, rfl, hm.1⟩
  | fail e => intro hm; exact absurd hb hm
  | div => intro hm; exact hm.elim

/-- `2u32.pow n = 2 ^ n`, symbolically, for any exponent below the word size. -/
private theorem u32_pow_two_ok (n : Std.U32) (hn : n.val < 32) :
    ∃ z : Std.U32, CoreModels.core.num.U32.pow 2#u32 n = .ok z ∧ z.val = 2 ^ n.val := by
  have h2 : ((2#u32 : Std.U32)).val = 2 := by scalar_tac
  have hlt : (2:Nat) ^ n.val < 2 ^ 32 := Nat.pow_lt_pow_right (by omega) hn
  obtain ⟨z, hz, hzv⟩ := u32_tryMk_ok (2 ^ n.val) hlt
  refine ⟨z, ?_, hzv⟩
  have hunf : CoreModels.core.num.U32.pow 2#u32 n
      = Std.UScalar.tryMk .U32 (((2#u32 : Std.U32)).val ^ n.val) := rfl
  rw [hunf, h2, hz]

/-- **M-E(1) — the SPEC side at a general `d`.** `Decompress_d(x) = (2x·q + 2^d) / 2^(d+1)`.
    Generalises `decompress_d_1_eq` (`:4461`) off `d = 1`, where the value set is `{0,1665}`
    and no rounding argument is needed. The two `massert`s discharge from `hd` and `hfe`;
    the result is `< 3329` so `FieldElement.new` is total here. -/
theorem decompress_d_gen_eq (fe : hacspec_ml_kem.parameters.FieldElement) (d : Std.Usize)
    (hd : d.val < 12) (hfe : fe.val.val < 2 ^ d.val) :
    hacspec_ml_kem.compress.decompress_d fe d
      = .ok { val := u16OfNat ((2 * fe.val.val * 3329 + 2 ^ d.val) / 2 ^ (d.val + 1)) } := by
  -- `2 ^ d.val` stays an atom; these are the only two facts we ever need about it.
  have hq_le : (2:Nat) ^ d.val ≤ 2048 := by
    calc (2:Nat) ^ d.val ≤ 2 ^ 11 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 2048 := by norm_num
  have hq_pos : 1 ≤ (2:Nat) ^ d.val := Nat.one_le_two_pow
  -- the two `massert`s
  obtain ⟨t2, hshl, hshlv⟩ := u16_shl_one_ok d (by omega)
  have hass1 : (d < (12#usize : Std.Usize)) := by scalar_tac
  have hass2 : fe.val < t2 := by
    have : fe.val.val < t2.val := by rw [hshlv]; exact hfe
    scalar_tac
  -- the casts
  have hcd : (Std.UScalar.cast .U32 d).val = d.val := by
    rw [Std.UScalar.cast_val_eq]; scalar_tac
  have hc3329 : Std.UScalar.cast .U32 (3329#u16 : Std.U16) = (3329#u32 : Std.U32) := by
    refine Std.UScalar.eq_of_val_eq ?_
    rw [Std.UScalar.cast_val_eq]; scalar_tac
  have hcfe : (Std.UScalar.cast .U32 fe.val).val = fe.val.val := by
    rw [Std.UScalar.cast_val_eq]; scalar_tac
  have h2 : ((2#u32 : Std.U32)).val = 2 := by scalar_tac
  have h3329 : ((3329#u32 : Std.U32)).val = 3329 := by scalar_tac
  have hfelt : fe.val.val < 65536 := by scalar_tac
  have hmax : Std.U32.max = 4294967295 := by scalar_tac
  -- the straight-line body, in order
  obtain ⟨tp, hpow, htpv⟩ := u32_pow_two_ok (Std.UScalar.cast .U32 d) (by rw [hcd]; omega)
  rw [hcd] at htpv
  obtain ⟨i3, hi3, hi3v⟩ := u32_mul_ok 2#u32 (Std.UScalar.cast .U32 fe.val) (by
    rw [hcfe, h2]; omega)
  obtain ⟨i5, hi5, hi5v⟩ := u32_mul_ok i3 3329#u32 (by
    rw [hi3v, hcfe, h2, h3329]; omega)
  obtain ⟨num, hnum, hnumv⟩ := u32_add_ok i5 tp (by
    rw [hi5v, hi3v, hcfe, h2, h3329, htpv]; omega)
  obtain ⟨i6, hi6, hi6v⟩ := u32_mul_ok tp 2#u32 (by rw [htpv, h2]; omega)
  obtain ⟨dec, hdec, hdecv⟩ := u32_div_ok num i6 (by rw [hi6v, htpv, h2]; omega)
  -- the rounding formula, and the `< 3329` that makes the `as U16` cast faithful
  have hdecv' : dec.val = (2 * fe.val.val * 3329 + 2 ^ d.val) / 2 ^ (d.val + 1) := by
    rw [hdecv, hnumv, hi5v, hi3v, hcfe, h3329, htpv, hi6v, htpv, h2, pow_succ]
  have hdlt : dec.val < 3329 := by
    rw [hdecv', pow_succ]
    refine Nat.div_lt_of_lt_mul ?_
    omega
  have hfinal : Std.UScalar.cast .U16 dec
      = u16OfNat ((2 * fe.val.val * 3329 + 2 ^ d.val) / 2 ^ (d.val + 1)) := by
    refine Std.UScalar.eq_of_val_eq ?_
    rw [Std.UScalar.cast_val_eq, u16OfNat_val _ (by rw [← hdecv']; scalar_tac), hdecv']
    have h16 : (Std.UScalarTy.U16).numBits = 16 := rfl
    rw [h16]
    exact Nat.mod_eq_of_lt (by omega)
  unfold hacspec_ml_kem.compress.decompress_d
  simp only [Aeneas.Std.massert, hacspec_ml_kem.parameters.FIELD_MODULUS,
    hacspec_ml_kem.parameters.FieldElement.new, Aeneas.Std.lift,
    Aeneas.Std.bind_tc_ok, hshl, if_pos hass1, if_pos hass2, hc3329, hpow,
    hi3, hi5, hnum, hi6, hdec, hfinal]

/-! ### Scaffolding for the general-`d` IMPL side.

    Aeneas ships `@[step]` shift specs for `UScalar` only, so the three `I32` bit
    operations the Rust performs (`x <<< 1`, `1 <<< d`, `x >>> (d+1)`) need `.val`
    lemmas here. All three are stated on the balanced-`Int` view (`.val`), never on
    `.bv.toNat`: that keeps `IScalarTy.I32.numBits` out of every rewrite motive (the
    dependent-`BitVec`-width trap) and lets `Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds'`
    discharge the no-wrap side conditions with the word size as an ordinary argument.
    `2 ^ d` is an ATOM throughout — never a closed large scalar (skill §6). -/

/-- `x <<< k` on `I32` is `x · 2 ^ k` balanced-mod the word size, for `k < 31`. -/
private theorem shiftLeft_val_i32 (x : Std.I32) (k : Nat) (hk : k < 31) :
    (⟨x.bv <<< k⟩ : Std.I32).val = (x.val * 2 ^ k).bmod (2 ^ 32) := by
  show (x.bv <<< k).toInt = _
  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.toInt_mul, BitVec.toInt_twoPow,
    if_neg (by omega), if_neg (by omega)]
  rfl

/-- `1 <<< k = 2 ^ k` on `I32`, for `k < 31` (no sign flip). -/
private theorem one_shiftLeft_val_i32 (k : Nat) (hk : k < 31) :
    (⟨(1#i32 : Std.I32).bv <<< k⟩ : Std.I32).val = (2 : Int) ^ k := by
  rw [shiftLeft_val_i32 _ k hk]
  have h1 : ((1#i32 : Std.I32)).val = 1 := by scalar_tac
  rw [h1, one_mul]
  apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
  · rw [show ((2 : Int) ^ (32 - 1)) = 2 ^ 31 from by norm_num]
    exact le_trans (by norm_num) (pow_nonneg (by norm_num) k)
  · rw [show ((2 : Int) ^ (32 - 1)) = 2 ^ 31 from by norm_num]
    exact pow_lt_pow_right₀ (by norm_num) hk

/-- `1#i32 <<< d` at the `RustM` level. Total for `0 ≤ d < 31`. -/
private theorem i32_one_shl_ok (d : Std.I32) (hd0 : 0 ≤ d.val) (hd : d.val < 31) :
    ∃ z : Std.I32, ((1#i32 : Std.I32) <<< d : RustM Std.I32) = RustM.ok z
      ∧ z.val = (2 : Int) ^ d.val.toNat := by
  refine ⟨⟨(1#i32 : Std.I32).bv <<< d.toNat⟩, ?_, ?_⟩
  · show Std.IScalar.shiftLeft_IScalar _ _ = _
    unfold Std.IScalar.shiftLeft_IScalar Std.IScalar.shiftLeft
    rw [if_pos hd0, if_pos (by scalar_tac : d.toNat < Std.IScalarTy.I32.numBits)]
    rfl
  · have h : d.toNat = d.val.toNat := rfl
    rw [h]; exact one_shiftLeft_val_i32 _ (by omega)

/-- `x <<< 1#i32` at the `RustM` level; faithful under the no-wrap bound. -/
private theorem i32_shl_one_ok (x : Std.I32)
    (hlb : -(2 ^ 31 : Int) ≤ 2 * x.val) (hub : 2 * x.val < 2 ^ 31) :
    ∃ z : Std.I32, (x <<< (1#i32 : Std.I32) : RustM Std.I32) = RustM.ok z
      ∧ z.val = 2 * x.val := by
  refine ⟨⟨x.bv <<< 1⟩, rfl, ?_⟩
  rw [shiftLeft_val_i32 _ 1 (by omega), show x.val * 2 ^ 1 = 2 * x.val from by ring]
  apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide) <;>
    (rw [show ((2 : Int) ^ (32 - 1)) = 2 ^ 31 from by norm_num]; omega)

/-- **Shift-is-division.** The arithmetic shift right on `I32` is floor division by
    `2 ^ k` on the balanced-`Int` view — for negative inputs too, which is why the
    statement needs no sign hypothesis. -/
private theorem i32_shr_ok (x k : Std.I32) (hk0 : 0 ≤ k.val) (hk : k.val < 32) :
    ∃ z : Std.I32, (x >>> k : RustM Std.I32) = RustM.ok z
      ∧ z.val = x.val / (2 : Int) ^ k.val.toNat := by
  refine ⟨⟨x.bv.sshiftRight k.toNat⟩, ?_, ?_⟩
  · show Std.IScalar.shiftRight_IScalar _ _ = _
    unfold Std.IScalar.shiftRight_IScalar Std.IScalar.shiftRight
    rw [if_pos hk0, if_pos (by scalar_tac : k.toNat < Std.IScalarTy.I32.numBits)]
  · show (⟨x.bv.sshiftRight k.toNat⟩ : Std.I32).val = _
    have h : k.toNat = k.val.toNat := rfl
    rw [h]
    show (x.bv.sshiftRight k.val.toNat).toInt = _
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]; norm_cast

private theorem i32_add_one_ok (d : Std.I32) (hd0 : 0 ≤ d.val) (hd : d.val < 12) :
    ∃ z : Std.I32, (d + (1#i32 : Std.I32) : RustM Std.I32) = RustM.ok z
      ∧ z.val = d.val + 1 := by
  obtain ⟨z, hz, hv, _⟩ :=
    Std.WP.spec_imp_exists
      (Std.IScalar.add_bv_spec (x := d) (y := (1#i32 : Std.I32)) (by scalar_tac) (by scalar_tac))
  exact ⟨z, hz, by rw [hv]; scalar_tac⟩

private theorem i32_wmul_ok (x y : Std.I32)
    (hlb : -(2 ^ 31 : Int) ≤ x.val * y.val) (hub : x.val * y.val < 2 ^ 31) :
    ∃ z : Std.I32, CoreModels.core.num.I32.wrapping_mul x y = RustM.ok z
      ∧ z.val = x.val * y.val := by
  refine ⟨Std.I32.wrapping_mul x y, rfl, ?_⟩
  rw [Aeneas.Std.I32.wrapping_mul_val_eq]
  apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide) <;>
    (rw [show ((2 : Int) ^ (32 - 1)) = 2 ^ 31 from by norm_num]; omega)

private theorem i32_wadd_ok (x y : Std.I32)
    (hlb : -(2 ^ 31 : Int) ≤ x.val + y.val) (hub : x.val + y.val < 2 ^ 31) :
    ∃ z : Std.I32, CoreModels.core.num.I32.wrapping_add x y = RustM.ok z
      ∧ z.val = x.val + y.val := by
  refine ⟨Std.I32.wrapping_add x y, rfl, ?_⟩
  rw [Aeneas.Std.I32.wrapping_add_val_eq]
  apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide) <;>
    (rw [show ((2 : Int) ^ (32 - 1)) = 2 ^ 31 from by norm_num]; omega)

/-- The `libcrux_secrets` `I16 → I32` cast is the identity on values (widening). -/
private theorem as_i32_ok (x : Std.I16) :
    ∃ z : Std.I32, libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 x = RustM.ok z
      ∧ z.val = x.val := by
  refine ⟨Std.IScalar.cast .I32 x, rfl, ?_⟩
  simp [Std.IScalar.val_mod_pow_greater_numBits]

/-- The `libcrux_secrets` `I32 → I16` cast never fails; faithfulness is separate. -/
private theorem dcc_as_i16_eq (x : Std.I32) :
    libcrux_secrets.I32.Insts.Libcrux_secretsIntCastOps.as_i16 x
      = RustM.ok (Std.IScalar.cast .I16 x) := rfl

/-- `.as_i16()` is FAITHFUL exactly when the `I32` value already fits in `I16`. This is
    the third of M-E(2)'s three obligations; without it the truncation is the source of
    the negative-control counterexamples (`-16026`) the falsify harness produced. -/
private theorem cast_i16_val_noov (x : Std.I32)
    (hlb : -(2 ^ 15 : Int) ≤ x.val) (hub : x.val < 2 ^ 15) :
    (Std.IScalar.cast .I16 x).val = x.val := by
  rw [Std.IScalar.cast_val_eq]
  show Int.bmod x.val (2 ^ 16) = x.val
  apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide) <;>
    (rw [show ((2 : Int) ^ (16 - 1)) = 2 ^ 15 from by norm_num]; omega)

private theorem classify_eq {T : Type} (x : T) :
    libcrux_secrets.traits.Classify.Blanket.classify x = RustM.ok x := rfl

private theorem field_modulus_val :
    (libcrux_iot_ml_kem.vector.traits.FIELD_MODULUS : Std.I16).val = 3329 := by
  unfold libcrux_iot_ml_kem.vector.traits.FIELD_MODULUS; rfl

/-- The per-lane body of `decompress_ciphertext_coefficient`, factored out of the loop
    so the 16-lane plumbing can be discharged by the tree's `elementwise_unary_spec`.
    Definitionally the extracted body modulo `RustM` bind-associativity — see
    `dcc_body_eq`. -/
private def dcc_per_elem (d : Std.I32) (x : Std.I16) : RustM Std.I16 := do
  let i2 ← libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 x
  let i3 ←
    libcrux_secrets.traits.Classify.Blanket.classify
      libcrux_iot_ml_kem.vector.traits.FIELD_MODULUS
  let i4 ← libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i32 i3
  let decompressed ← CoreModels.core.num.I32.wrapping_mul i2 i4
  let i5 ← decompressed <<< (1#i32 : Std.I32)
  let i6 ← (1#i32 : Std.I32) <<< d
  let decompressed1 ← CoreModels.core.num.I32.wrapping_add i5 i6
  let i7 ← d + (1#i32 : Std.I32)
  let decompressed2 ← decompressed1 >>> i7
  libcrux_secrets.I32.Insts.Libcrux_secretsIntCastOps.as_i16 decompressed2

/-- Per-lane post. The `0 ≤ x ∧ x < 2 ^ d` guard is carried INSIDE the predicate because
    `elementwise_unary_spec` demands an unconditional per-element Triple: the body is
    total for every `I16` lane (no `I32` wrap is possible at any `d < 31`), but its VALUE
    is only the rounding formula on in-range lanes. -/
private def dcc_P (d : Std.I32) (x r : Std.I16) : Prop :=
  0 ≤ x.val → x.val < 2 ^ d.val.toNat →
    r.val.toNat = (2 * x.val.toNat * 3329 + 2 ^ d.val.toNat) / 2 ^ (d.val.toNat + 1)
      ∧ 0 ≤ r.val ∧ r.val < 3329

/-- **The per-lane keystone.** Straight-line walk of the ten-operation body: every step
    is `.ok` for EVERY `I16` lane, in range or not (worst case `|lane| = 32768`,
    `d = 11`: `2 · 32768 · 3329 + 2 ^ 11 = 218,171,392 < 2 ^ 31`), and the value is the
    FIPS-203 rounding formula on lanes below `2 ^ d`. The split matters: totality is
    what `elementwise_unary_spec` needs unconditionally, correctness is what `hlane`
    buys — out of range the closing `.as_i16()` truncates and the formula is FALSE
    (the falsify harness's negative control). -/
private theorem dcc_per_elem_ok (d : Std.I32) (hd0 : 0 ≤ d.val) (hd : d.val < 12)
    (x : Std.I16) :
    ∃ r : Std.I16, dcc_per_elem d x = RustM.ok r ∧ dcc_P d x r := by
  have hDv : ((d.val.toNat : Nat) : Int) = d.val := Int.toNat_of_nonneg hd0
  have hPle : (2 : Int) ^ d.val.toNat ≤ 2048 := by
    calc (2 : Int) ^ d.val.toNat ≤ 2 ^ 11 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 2048 := by norm_num
  have hPpos : (0 : Int) < 2 ^ d.val.toNat := by positivity
  have hxlb : (-32768 : Int) ≤ x.val := by scalar_tac
  have hxub : x.val ≤ 32767 := by scalar_tac
  obtain ⟨v2, e2, h2v⟩ := as_i32_ok x
  obtain ⟨v4, e4, h4v⟩ := as_i32_ok libcrux_iot_ml_kem.vector.traits.FIELD_MODULUS
  rw [field_modulus_val] at h4v
  obtain ⟨vm, em, hmv⟩ := i32_wmul_ok v2 v4 (by rw [h2v, h4v]; omega) (by rw [h2v, h4v]; omega)
  rw [h2v, h4v] at hmv
  obtain ⟨v5, e5, h5v⟩ := i32_shl_one_ok vm (by rw [hmv]; omega) (by rw [hmv]; omega)
  rw [hmv] at h5v
  obtain ⟨v6, e6, h6v⟩ := i32_one_shl_ok d hd0 (by omega)
  obtain ⟨va, ea, hav⟩ := i32_wadd_ok v5 v6 (by rw [h5v, h6v]; omega) (by rw [h5v, h6v]; omega)
  rw [h5v, h6v] at hav
  obtain ⟨v7, e7, h7v⟩ := i32_add_one_ok d hd0 hd
  obtain ⟨v8, e8, h8v⟩ := i32_shr_ok va v7 (by omega) (by omega)
  have hexp : v7.val.toNat = d.val.toNat + 1 := by omega
  rw [hexp, hav] at h8v
  refine ⟨Std.IScalar.cast .I16 v8, ?_, ?_⟩
  · unfold dcc_per_elem
    simp only [e2, Aeneas.Std.bind_tc_ok, classify_eq, e4, em, e5, e6, ea, e7, e8, dcc_as_i16_eq]
  · unfold dcc_P
    intro hx0 hxlt
    have hxn : ((x.val.toNat : Nat) : Int) = x.val := Int.toNat_of_nonneg hx0
    have hNlt : x.val.toNat < 2 ^ d.val.toNat := by
      have h : ((x.val.toNat : Nat) : Int) < (((2 : Nat) ^ d.val.toNat : Nat) : Int) := by
        rw [hxn]; push_cast; exact hxlt
      exact_mod_cast h
    have hPnle : (2 : Nat) ^ d.val.toNat ≤ 2048 := by
      calc (2 : Nat) ^ d.val.toNat ≤ 2 ^ 11 := Nat.pow_le_pow_right (by omega) (by omega)
        _ = 2048 := by norm_num
    have hqlt :
        (2 * x.val.toNat * 3329 + 2 ^ d.val.toNat) / 2 ^ (d.val.toNat + 1) < 3329 := by
      refine Nat.div_lt_of_lt_mul ?_
      rw [show (2 : Nat) ^ (d.val.toNat + 1) = 2 * 2 ^ d.val.toNat from by rw [pow_succ]; ring]
      omega
    have hnum : (2 : Int) * (x.val * 3329) + 2 ^ d.val.toNat
        = ((2 * x.val.toNat * 3329 + 2 ^ d.val.toNat : Nat) : Int) := by
      push_cast [hxn]; ring
    have hden : (2 : Int) ^ (d.val.toNat + 1) = (((2 : Nat) ^ (d.val.toNat + 1) : Nat) : Int) := by
      push_cast; ring
    have hv8q : v8.val
        = (((2 * x.val.toNat * 3329 + 2 ^ d.val.toNat) / 2 ^ (d.val.toNat + 1) : Nat) : Int) := by
      rw [h8v, hnum, hden]
      exact_mod_cast rfl
    -- name the Nat quotient so `omega` sees a plain `Nat` atom, not a cast division
    set q : Nat := (2 * x.val.toNat * 3329 + 2 ^ d.val.toNat) / 2 ^ (d.val.toNat + 1) with hqdef
    clear_value q
    have hcast : (Std.IScalar.cast .I16 v8).val = v8.val :=
      cast_i16_val_noov v8 (by rw [hv8q]; omega) (by rw [hv8q]; omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [hcast, hv8q]; omega
    · rw [hcast, hv8q]; omega
    · rw [hcast, hv8q]; exact_mod_cast hqlt

/-- The extracted loop body IS `unary_loop_body dcc_per_elem`, modulo `RustM`
    bind-associativity (the extraction inlines the ten operations where the reusable
    combinator calls one `per_elem`). -/
private theorem dcc_body_eq (d : Std.I32) :
    (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
          × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
      libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient_loop.body
        d p.1 p.2)
    = (fun p =>
        libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.unary_loop_body
          (dcc_per_elem d) p.1 p.2) := by
  funext p
  rcases p with ⟨iter1, vec1⟩
  unfold libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient_loop.body
  unfold libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.unary_loop_body dcc_per_elem
  simp only [Aeneas.Std.bind_assoc_eq]
  rfl

/-- **M-E(2) — the IMPL side at a general `d`, the APEX of this bank.** The 16-lane loop
    of `decompress_ciphertext_coefficient` computes, per lane,
    `((lane · 3329) <<< 1 + (1 <<< d)) >>> (d+1)` in `I32` and truncates back to `I16`.

    Three things have to be shown and none of them arises at `d = 1`: the `I32` arithmetic
    does not wrap (worst case `d = 11`, lane `2047`: `13,630,974 < 2 ^ 31` — note this
    CORRECTS the readiness map body's `13,629,374`, per amendment A4); the arithmetic
    shift right on a NON-NEGATIVE `I32` is floor division by `2 ^ (d+1)`; and the closing
    `.as_i16()` is faithful because the result is `< 3329`.

    The `0 ≤ · ∧ · < 3329` conjunct is the CONSUMER's bound, per the amended transcription
    rule's mandatory third check: L5.3's post requires `natAbs ≤ 3328` on every lane
    (`deserialize_then_decompress_ring_element_v_fc`), and `compute_message_fc` binds the
    same downstream. Stating it here is what makes this bank composable rather than merely
    true. -/
theorem decompress_ciphertext_coefficient_gen_fc (d : Std.I32)
    (a : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hd0 : 0 ≤ d.val) (hd : d.val < 12)
    (hlane : ∀ i : Nat, i < 16 →
        0 ≤ (a.elements.val[i]!).val ∧ (a.elements.val[i]!).val < 2 ^ d.val.toNat) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient d a
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
                ((r.elements.val[i]!).val).toNat
                    = (2 * ((a.elements.val[i]!).val).toNat * 3329 + 2 ^ d.val.toNat)
                        / 2 ^ (d.val.toNat + 1)
                  ∧ 0 ≤ (r.elements.val[i]!).val
                  ∧ (r.elements.val[i]!).val < 3329 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
  unfold libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient_loop
  have h_field : libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
                  = (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR; rfl
  rw [h_field, dcc_body_eq d]
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.elementwise_unary_spec
      (dcc_per_elem d) (dcc_P d)
      (fun y => by
        obtain ⟨r, hr, hP⟩ := dcc_per_elem_ok d hd0 hd y
        exact triple_of_ok_fc hr hP)
      a)
  rw [PostCond.entails_noThrow]
  intro r hh j hj
  obtain ⟨rj, _hr, h_acc, h_P⟩ := hh j hj
  rw [h_acc]
  exact h_P (hlane j hj).1 (hlane j hj).2

end MEBank

/-! ## M-C′ — COMPRESS: the magic-multiply proved EXACTLY EQUAL to integer division (K7).

    THE EXEMPLAR for the one kind the readiness map records as having NO precedent
    anywhere in the three trees. The nearest thing is Barrett
    (`PerElement.lean:141 barrett_q`), and it is NOT close: **Barrett's post is a
    congruence plus a bound, never an exact quotient identity.** Compress needs the
    exact one.

    ## The shape of the problem

    The impl and the spec compute the compressed coefficient by genuinely different
    routes and both are exact:
      IMPL (`compress_ciphertext_coefficient`, `Funs.lean:3569`) — a u64 magic-reciprocal
        multiply: `((x·2^d + 1664) · 10321340) >>> 35`, then mask to `d` bits.
      SPEC (`compress.compress_d`, hacspec `Funs.lean:50`) — honest integer division:
        `(2x·2^d + 3329) / 6658`, then `% 2^d`.
    So this bank is three statements: the two seams that pin each side to its own `Nat`
    closed form, and the KEYSTONE identity that they are the same number.

    ## MINE, DO NOT PORT

    F* has the mathematics in ONE readable lemma —
    `Commute.Chunk.fst:4143–4173 lemma_compress_d_barrett_eq` — in two steps, and those
    two steps are the transferable content (the SMT proof around them is not):
      (1) write `n = x·2^d + 1664 = 3329q + r`; then `2x·2^d + 3329 = (2r+1) + 6658q`,
          and `2r+1` is ODD and `< 6658`, so the exact side `= q`;
      (2) `3329 · 10321340 = 34,359,740,860 > 2^35 = 34,359,738,368`, so
          `2^35·q ≤ n·10321340 < 2^35·(q+1)`, so the Barrett side `= q`.
    Reuse `barrett_q` / `barrett_reduce_core` for multiply-shift → `ediv` normalisation,
    but NOT Barrett's post.

    ## Two measured corrections to the readiness map's statement

    **(a) State it UN-MODDED.** The map writes the identity with `% 2^d` on both sides.
    Measured: the identity holds WITHOUT the mod — the two quotients are equal as
    naturals, exhaustively for every `x < 3329` at every `d`. That is also what F*'s
    two-step argument actually proves (both sides equal the same `q`), and the stronger
    form composes better: the `% 2^d` then belongs to the two seams, where the impl's
    `get_n_least_significant_bits` and the spec's `% two_pow_bit_size` each live.

    **(b) It is GENERIC in `d`.** The map states it at `d ∈ {4,5,10,11}`. Swept every
    `d = 0 … 11` over every `x < 3329`: zero counterexamples. Stated at `d < 12`
    accordingly — same outcome as M-C and M-E, where per-case statements turned out to be
    an unnecessary restriction.

    ## Where the `x < 3329` bound goes, and where it does NOT

    It is load-bearing in the KEYSTONE only. Without it the identity fails, first at
    `x = 14566` (d=10) and `x = 7283` (d=11) — and never anywhere in u16 at d = 4 or 5,
    which is exactly why a d=4/5-only check would have called the hypothesis decorative.
    It is DEAD WEIGHT on both seams: measured across the FULL u16 range at every `d < 12`,
    and exhaustively over all 65536 values at the four ML-KEM widths, both seams hold with
    no bound at all. So the bound appears exactly once in this bank, where it is real.

    ## Falsified before locking (`references/mlkem-falsify-harness.lean`)
    Keystone: exhaustive over `x < 3329` × `d = 0..11`. Impl seam and spec seam: exhaustive
    over all 65536 `u16` values at `d ∈ {4,5,10,11}` plus a stride-7 sweep of the full u16
    range at every `d < 12`. Zero counterexamples. -/

section MCPBank

/-- **M-C′(1) — THE KEYSTONE (kind K7).** The u64 magic-reciprocal multiply and the
    honest integer division are the SAME natural number. Stated un-modded and generic in
    `d`; see the two corrections in the bank docstring. -/
theorem compress_barrett_eq (x d : Nat) (hx : x < 3329) (hd : d < 12) :
    ((x * 2 ^ d + 1664) * 10321340) / 2 ^ 35 = (2 * x * 2 ^ d + 3329) / 6658 := by
  -- The whole content of the identity is a statement about `m = x * 2 ^ d` alone: the
  -- exponent never has to be unfolded, only bounded.  Split the two concerns.
  --
  -- (1) The magic constant is exact on the range that matters.  With `n = m + 1664` and
  -- `n = 3329 * q + r`, the honest side is `(2 * n + 1) / 6658 = q` because `2 * r + 1` is
  -- below 6658; the Barrett side is `q` because `3329 * 10321340 = 2 ^ 35 + 2492`, so the
  -- slack `2492 * q + 10321340 * r` stays under `2 ^ 35` as long as `q ≤ 4140`, and
  -- `m ≤ 6815744` gives `q ≤ 2047`.  Both divisors are literals, so this is linear integer
  -- arithmetic once `m` is abstract, and `omega` does it in one step.
  have key : ∀ m : Nat, m ≤ 6815744 →
      ((m + 1664) * 10321340) / 2 ^ 35 = (2 * m + 3329) / 6658 := by
    intro m hm; omega
  -- (2) `hx` and `hd` are exactly what pins `m` into that range: `3328 * 2048 = 6815744`.
  -- This is where `hx : x < 3329` is load-bearing — the identity genuinely fails above it,
  -- first at `x = 14566` (d = 10) and `x = 7283` (d = 11).
  have h2 : (2 : Nat) ^ d ≤ 2048 :=
    calc (2 : Nat) ^ d ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2048 := by norm_num
  have hm : x * 2 ^ d ≤ 6815744 :=
    calc x * 2 ^ d ≤ 3328 * 2048 := Nat.mul_le_mul (by omega) h2
      _ = 6815744 := by norm_num
  rw [show 2 * x * 2 ^ d = 2 * (x * 2 ^ d) from by ring]
  exact key _ hm

/-! ### Scaffolding for the u64 magic-multiply IMPL seam.

    The seam below is a straight-line `RustM` walk, not an mvcgen goal, so each of the
    `U64` operations gets an `∃ z, … = .ok z ∧ z.val = …` lemma in exactly the shape
    M-E's `I32` bank uses (`:4737` ff). All of them are stated on the `Nat` view
    (`.val`), never on `.bv`: that keeps `UScalarTy.U64.numBits` out of every rewrite
    motive (the dependent-`BitVec`-width trap) and lets the no-wrap side conditions be
    ordinary `Nat.mod_eq_of_lt`. `2 ^ d` is an ATOM throughout (skill §6). -/

/-- `UScalar.size` is `irreducible_def`, so the word modulus needs one named unfolding. -/
private theorem u64_size_eq : Std.UScalar.size .U64 = 2 ^ 64 := by
  rw [Std.UScalar.size]; rfl

/-- `x <<< s` on `U64` by a `U8` amount is `x · 2 ^ s` mod the word size, for `s < 64`. -/
private theorem u64_shl_ok (x : Std.U64) (s : Std.U8) (hs : s.val < 64) :
    ∃ z : Std.U64, (x <<< s : RustM Std.U64) = RustM.ok z
      ∧ z.val = (x.val * 2 ^ s.val) % 2 ^ 64 := by
  refine ⟨⟨x.bv <<< s.val⟩, ?_, ?_⟩
  · show Std.UScalar.shiftLeft_UScalar _ _ = _
    unfold Std.UScalar.shiftLeft_UScalar Std.UScalar.shiftLeft
    rw [if_pos (show s.val < Std.UScalarTy.U64.numBits by simpa using hs)]
    rfl
  · show (x.bv <<< s.val).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    rfl

/-- **Shift-is-division.** The logical shift right on `U64` by a non-negative `I32`
    amount is floor division by `2 ^ k` on the `Nat` view. -/
private theorem u64_shr_ok (x : Std.U64) (k : Std.I32) (hk0 : 0 ≤ k.val) (hk : k.val < 64) :
    ∃ z : Std.U64, (x >>> k : RustM Std.U64) = RustM.ok z
      ∧ z.val = x.val / 2 ^ k.val.toNat := by
  refine ⟨⟨x.bv >>> k.toNat⟩, ?_, ?_⟩
  · show Std.UScalar.shiftRight_IScalar _ _ = _
    unfold Std.UScalar.shiftRight_IScalar Std.UScalar.shiftRight
    rw [if_pos hk0, if_pos (show k.toNat < Std.UScalarTy.U64.numBits by scalar_tac)]
    rfl
  · show (x.bv >>> k.toNat).toNat = _
    have h : k.toNat = k.val.toNat := rfl
    rw [h, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rfl

private theorem u64_wadd_ok (x y : Std.U64) (hb : x.val + y.val < 2 ^ 64) :
    ∃ z : Std.U64, CoreModels.core.num.U64.wrapping_add x y = RustM.ok z
      ∧ z.val = x.val + y.val := by
  refine ⟨Std.U64.wrapping_add x y, rfl, ?_⟩
  rw [Aeneas.Std.U64.wrapping_add_val_eq, u64_size_eq]
  exact Nat.mod_eq_of_lt hb

private theorem u64_wmul_ok (x y : Std.U64) (hb : x.val * y.val < 2 ^ 64) :
    ∃ z : Std.U64, CoreModels.core.num.U64.wrapping_mul x y = RustM.ok z
      ∧ z.val = x.val * y.val := by
  refine ⟨Std.U64.wrapping_mul x y, rfl, ?_⟩
  rw [Aeneas.Std.U64.wrapping_mul_val_eq, u64_size_eq]
  exact Nat.mod_eq_of_lt hb

/-- The `libcrux_secrets` `U16 → U64` cast is the identity on values (widening). -/
private theorem cc_as_u64_ok (x : Std.U16) :
    ∃ z : Std.U64, libcrux_secrets.U16.Insts.Libcrux_secretsIntCastOps.as_u64 x = RustM.ok z
      ∧ z.val = x.val := by
  refine ⟨Std.UScalar.cast .U64 x, rfl, ?_⟩
  rw [Std.UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by scalar_tac)

/-- The `U64 → U32` cast is FAITHFUL exactly below `2 ^ 32`; this is the first of the
    seam's two truncation obligations. -/
private theorem cc_as_u32_ok (x : Std.U64) (h : x.val < 2 ^ 32) :
    ∃ z : Std.U32, libcrux_secrets.U64.Insts.Libcrux_secretsIntCastOps.as_u32 x = RustM.ok z
      ∧ z.val = x.val := by
  refine ⟨Std.UScalar.cast .U32 x, rfl, ?_⟩
  rw [Std.UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by simpa using h)

/-- The `U32 → I16` cast is FAITHFUL exactly below `2 ^ 15` — the second truncation
    obligation, and the one the `< 2 ^ d` mask bound is what buys. -/
private theorem cc_as_i16_ok (x : Std.U32) (h : x.val < 2 ^ 15) :
    ∃ z : Std.I16, libcrux_secrets.U32.Insts.Libcrux_secretsIntCastOps.as_i16 x = RustM.ok z
      ∧ z.val = (x.val : Int) := by
  refine ⟨Std.UScalar.hcast .I16 x, rfl, ?_⟩
  rw [Std.UScalar.hcast_val_eq]
  show Int.bmod (x.val : Int) (2 ^ (16 : Nat)) = _
  apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide) <;>
    (rw [show ((2 : Int) ^ (16 - 1)) = 2 ^ 15 from by norm_num]
     have : (x.val : Int) < 2 ^ 15 := by exact_mod_cast h
     have : (0 : Int) ≤ (x.val : Int) := Int.natCast_nonneg _
     omega)

/-- **M-C′(2) — the IMPL seam.** `compress_ciphertext_coefficient` in closed `Nat` form.
    Carries the u64 no-wrap obligation (`wrapping_add`/`wrapping_mul`: worst case
    `(65535·2^11 + 1664)·10321340 ≈ 1.39e15 < 2^64`), the `>>> 35` as division, and
    `get_n_least_significant_bits d` as `% 2^d`.

    UNCONDITIONAL in `fe` — no `< 3329` — which is measured, not assumed (see the bank
    docstring). The `0 ≤ · < 2^d` conjunct is the CONSUMER's bound per the amended
    transcription rule's third check: L5.4 feeds this straight into `byte_encode` at width
    `d`, and it is literally the `hL : ∀ i, L i < 2 ^ d` hypothesis of
    `bitSum_laneBit_window` (M-C(2)) — so the two exemplars compose without a gap. -/
theorem compress_ciphertext_coefficient_eq (d : Std.U8) (fe : Std.U16) (hd : d.val < 12) :
    ∃ r : Std.I16,
      libcrux_iot_ml_kem.vector.portable.compress.compress_ciphertext_coefficient d fe
          = .ok r
      ∧ (r.val).toNat = (((fe.val * 2 ^ d.val + 1664) * 10321340) / 2 ^ 35) % 2 ^ d.val
      ∧ 0 ≤ r.val ∧ r.val < 2 ^ d.val := by
  -- `2 ^ d.val` is an ATOM: these two facts are all that is ever needed about it.
  have hP2 : (2 : Nat) ^ d.val ≤ 2048 := by
    calc (2 : Nat) ^ d.val ≤ 2 ^ 11 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 2048 := by norm_num
  have hP1 : 1 ≤ (2 : Nat) ^ d.val := Nat.one_le_two_pow
  have hfv : fe.val ≤ 65535 := by scalar_tac
  -- Name the shifted input.  Once `n` is a bare local constant every remaining side
  -- condition is LINEAR, so `omega` discharges the whole no-wrap chain and no nonlinear
  -- arithmetic tactic is needed anywhere; the one nonlinear step is `Nat.mul_le_mul` below.
  obtain ⟨n, hn⟩ : ∃ n : Nat, fe.val * 2 ^ d.val = n := ⟨_, rfl⟩
  have hN : n ≤ 134215680 := by
    rw [← hn]
    calc fe.val * 2 ^ d.val ≤ 65535 * 2048 := Nat.mul_le_mul hfv hP2
      _ = 134215680 := by norm_num
  rw [hn]
  -- the literal moduli, so `omega` sees numerals rather than powers
  have e64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  have e35 : (2 : Nat) ^ 35 = 34359738368 := by norm_num
  have e32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have e15 : (2 : Nat) ^ 15 = 32768 := by norm_num
  have c1664 : ((1664#u64 : Std.U64)).val = 1664 := by scalar_tac
  have cmag : ((10321340#u64 : Std.U64)).val = 10321340 := by scalar_tac
  have c35 : ((35#i32 : Std.I32)).val = 35 := by scalar_tac
  -- the straight-line body, in order
  obtain ⟨v0, e0, h0v⟩ := cc_as_u64_ok fe
  obtain ⟨v1, e1, h1v⟩ := u64_shl_ok v0 d (by omega)
  rw [h0v, hn, e64] at h1v
  have h1 : v1.val = n := by omega
  obtain ⟨v2, e2, h2v⟩ := u64_wadd_ok v1 1664#u64 (by rw [h1, c1664, e64]; omega)
  rw [h1, c1664] at h2v
  obtain ⟨v3, e3, h3v⟩ := u64_wmul_ok v2 10321340#u64 (by rw [h2v, cmag, e64]; omega)
  rw [h2v, cmag] at h3v
  obtain ⟨v4, e4, h4v⟩ := u64_shr_ok v3 35#i32 (by rw [c35]; norm_num) (by rw [c35]; norm_num)
  rw [h3v, show ((35#i32 : Std.I32)).val.toNat = 35 from by rw [c35]; rfl] at h4v
  obtain ⟨v5, e5, h5v⟩ := cc_as_u32_ok v4 (by rw [h4v, e35, e32]; omega)
  rw [h4v] at h5v
  -- the mask, from the tree's existing L0.1 `@[spec]`
  obtain ⟨v6, e6, hlt6, h6v⟩ := triple_exists_ok_fc
    (libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.get_n_least_significant_bits_spec
      d v5 (by omega))
  rw [h5v] at h6v
  -- the closing `.as_i16()` is faithful because the mask already put us below `2 ^ 15`
  obtain ⟨r, er, hrv⟩ := cc_as_i16_ok v6 (by rw [e15]; omega)
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · unfold libcrux_iot_ml_kem.vector.portable.compress.compress_ciphertext_coefficient
    simp only [e0, Aeneas.Std.bind_tc_ok, e1, e2, e3, e4, e5, e6, er]
  · rw [hrv, Int.toNat_natCast]; exact h6v
  · rw [hrv]; exact Int.natCast_nonneg _
  · rw [hrv]; exact_mod_cast hlt6

/-- `%` on `U32` — the one scalar operation this seam needs that the M-E bank
    (`:4442` ff) does not already provide, in the same
    `∃ z, … = .ok z ∧ z.val = …` shape. Total here because the modulus is `2 ^ d`. -/
private theorem u32_rem_ok (x y : Std.U32) (hy : 0 < y.val) :
    ∃ z : Std.U32, (x % y : RustM Std.U32) = .ok z ∧ z.val = x.val % y.val := by
  obtain ⟨z, hz, hv⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.rem_spec (ty := .U32) x (y := y) (by omega))
  exact ⟨z, hz, hv⟩

/-- **M-C′(3) — the SPEC seam.** `compress.compress_d` in closed `Nat` form. The lone
    `massert (to_bit_size < 12)` discharges from `hd`; `FieldElement.new` is total.
    UNCONDITIONAL in `fe` for the same measured reason as M-C′(2). -/
theorem compress_d_gen_eq (fe : hacspec_ml_kem.parameters.FieldElement) (d : Std.Usize)
    (hd : d.val < 12) :
    hacspec_ml_kem.compress.compress_d fe d
      = .ok { val := u16OfNat (((2 * fe.val.val * 2 ^ d.val + 3329) / 6658) % 2 ^ d.val) } := by
  -- `2 ^ d.val` stays an ATOM: these are the only facts ever needed about it.
  have hq_le : (2:Nat) ^ d.val ≤ 2048 := by
    calc (2:Nat) ^ d.val ≤ 2 ^ 11 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 2048 := by norm_num
  have hq_pos : 1 ≤ (2:Nat) ^ d.val := Nat.one_le_two_pow
  have hfelt : fe.val.val ≤ 65535 := by scalar_tac
  have hmax : Std.U32.max = 4294967295 := by scalar_tac
  -- the lone `massert`
  have hass1 : (d < (12#usize : Std.Usize)) := by scalar_tac
  -- the casts
  have hcd : (Std.UScalar.cast .U32 d).val = d.val := by
    rw [Std.UScalar.cast_val_eq]; scalar_tac
  have hcfe : (Std.UScalar.cast .U32 fe.val).val = fe.val.val := by
    rw [Std.UScalar.cast_val_eq]; scalar_tac
  have hc3329 : Std.UScalar.cast .U32 (3329#u16 : Std.U16) = (3329#u32 : Std.U32) := by
    refine Std.UScalar.eq_of_val_eq ?_
    rw [Std.UScalar.cast_val_eq]; scalar_tac
  have h2 : ((2#u32 : Std.U32)).val = 2 := by scalar_tac
  have h3329 : ((3329#u32 : Std.U32)).val = 3329 := by scalar_tac
  -- The ONE nonlinear step: `fe · 2 ^ d` is bounded by the product of the bounds, so
  -- every no-wrap side condition below is linear in that single atom and `omega` does it.
  have hprod : fe.val.val * 2 ^ d.val ≤ 134215680 :=
    calc fe.val.val * 2 ^ d.val ≤ 65535 * 2048 := Nat.mul_le_mul hfelt hq_le
      _ = 134215680 := by norm_num
  -- the straight-line body, in order
  obtain ⟨tp, hpow, htpv⟩ := u32_pow_two_ok (Std.UScalar.cast .U32 d) (by rw [hcd]; omega)
  rw [hcd] at htpv
  obtain ⟨i2, hi2, hi2v⟩ := u32_mul_ok (Std.UScalar.cast .U32 fe.val) 2#u32 (by
    rw [hcfe, h2]; omega)
  rw [hcfe, h2] at hi2v
  obtain ⟨i3, hi3, hi3v⟩ := u32_mul_ok i2 tp (by
    rw [hi2v, htpv, show fe.val.val * 2 * 2 ^ d.val = 2 * (fe.val.val * 2 ^ d.val) from by
      ring]
    omega)
  rw [hi2v, htpv, show fe.val.val * 2 * 2 ^ d.val = 2 * fe.val.val * 2 ^ d.val from by ring]
    at hi3v
  obtain ⟨i5, hi5, hi5v⟩ := u32_add_ok i3 3329#u32 (by
    rw [hi3v, h3329, show 2 * fe.val.val * 2 ^ d.val = 2 * (fe.val.val * 2 ^ d.val) from by
      ring]
    omega)
  rw [hi3v, h3329] at hi5v
  obtain ⟨i7, hi7, hi7v⟩ := u32_mul_ok 2#u32 3329#u32 (by rw [h2, h3329]; omega)
  rw [h2, h3329] at hi7v
  obtain ⟨cmp, hcmp, hcmpv⟩ := u32_div_ok i5 i7 (by rw [hi7v]; omega)
  rw [hi5v, hi7v] at hcmpv
  obtain ⟨i8, hi8, hi8v⟩ := u32_rem_ok cmp tp (by rw [htpv]; omega)
  rw [hcmpv, htpv] at hi8v
  -- the closing `as U16` is faithful because the mask already put us below `2 ^ d ≤ 2048`
  have hi8lt : i8.val < 2 ^ d.val := by rw [hi8v]; exact Nat.mod_lt _ (by omega)
  have hfinal : Std.UScalar.cast .U16 i8
      = u16OfNat (((2 * fe.val.val * 2 ^ d.val + 3329) / 6658) % 2 ^ d.val) := by
    refine Std.UScalar.eq_of_val_eq ?_
    rw [Std.UScalar.cast_val_eq, u16OfNat_val _ (by rw [← hi8v]; scalar_tac), hi8v]
    have h16 : (Std.UScalarTy.U16).numBits = 16 := rfl
    rw [h16]
    exact Nat.mod_eq_of_lt (by omega)
  unfold hacspec_ml_kem.compress.compress_d
  simp only [Aeneas.Std.massert, hacspec_ml_kem.parameters.FIELD_MODULUS,
    hacspec_ml_kem.parameters.FieldElement.new, Aeneas.Std.lift,
    Aeneas.Std.bind_tc_ok, if_pos hass1, hc3329, hpow,
    hi2, hi3, hi5, hi7, hcmp, hi8, hfinal]

end MCPBank

/-! ## M-D — COMPRESS at `d = 1`: the branch-free THRESHOLD (kind K8).

    THE EXEMPLAR for the second kind the readiness map records as having no precedent.
    The nearest article is ml-dsa `Rounding.lean:121 xor_clamp_val`, and the delta is
    real: ml-dsa's clamp targets a BOUND, whereas this one has to land an interval
    TRICHOTOMY — and it is `I16`, not `I32`.

    ## Why this bank is only TWO statements

    Because M-C′(3) `compress_d_gen_eq` is generic in `d < 12`, it already covers the
    SPEC side at `d = 1` — no separate spec statement is needed. What remains is the
    impl seam and the arithmetic bridge between the spec's closed form at `d = 1` and the
    threshold predicate the impl actually computes.

    ## What the impl does

    `compress_message_coefficient` (`Funs.lean`, from `compress.rs:28–56`) is branch-free
    via a DOUBLE sign-mask:
        shifted   = 1664 - fe                      (I16 wrapping_sub)
        mask      = shifted >>> 15                 (-1 if negative, else 0)
        positive  = mask ^^^ shifted               (|shifted| - 1 if negative, else shifted)
        inRange   = positive - 832
        result    = (inRange >>> 15) &&& 1         (1 iff positive < 832)
    i.e. `1` exactly when `833 ≤ fe ≤ 2496`. The F* source gives that trichotomy verbatim
    (`compress.rs` ~28–56 — NOT 101–124, per amendment A4).

    ## Where the bound goes — measured, and it lands in exactly one place again

    IMPL SEAM: UNCONDITIONAL. Checked over ALL 65536 `u16` values, not merely `x < 3329`:
    the double-mask identity holds everywhere, so no hypothesis is carried.

    PURE BRIDGE: needs `x < 3329`, and it is load-bearing. First counterexample at
    **x = 4162** — which is EXACTLY the counterexample `AMENDMENTS 2` records for L5.2
    ("CE lane 4162: impl `[0,0,0,0]`, spec byte0 `1`"). That is not a coincidence and it
    is worth stating: L5.2's missing `h_bnd` and this bridge's `hx` are the SAME bound,
    witnessed by the SAME value, arrived at independently. Closing this bridge is
    therefore precisely what makes L5.2's restated bound dischargeable.

    ## Falsified before locking (`references/mlkem-falsify-harness.lean`)
    Impl seam: EXHAUSTIVE over `x < 3329`, then EXHAUSTIVE over all 65536 `u16` values.
    Pure bridge: EXHAUSTIVE over `x < 3329`, plus the four named boundary values
    832 / 833 / 2496 / 2497, plus the first-counterexample search that produced 4162.
    Zero counterexamples inside the stated domains. -/

section MDBank

/-- The whole branch-free body of `compress_message_coefficient`, as a total
    `BitVec 16 → BitVec 16` function. Every step of the impl is total (wrapping
    subtraction, an arithmetic shift by a closed in-range amount, xor, and), so the
    `RustM` monad never fails and the seam below is a `rfl`-level identity. -/
private def cmcBv (b : BitVec 16) : BitVec 16 :=
  (((((1664#16) - b).sshiftRight 15 ^^^ ((1664#16) - b)) - (832#16)).sshiftRight 15) &&& (1#16)

private theorem cmc_seam (fe : Std.U16) :
    libcrux_iot_ml_kem.vector.portable.compress.compress_message_coefficient fe
      = .ok (c8 ⟨cmcBv fe.bv⟩) := rfl

/-! ### The pure `BitVec 16` sign-mask algebra.

    Three facts do all the work, and none of them is bit-packing: an arithmetic shift by
    `15` is `allOnes`-or-`0` (`sshr15_bv`), `allOnes ^^^ ·` is complement, and `allOnes
    &&& 1 = 1`. Everything after that is `Nat` interval arithmetic under `omega`.

    `toNat16_lt` / `msb16_iff` / `sshr15_bv` are NOT restated here: they are the shared
    `BitVec 16` primitives declared once at the head of `section L56Bank`, from which the
    `Std.I16` forms `i16_toNat_lt` / `sshr15_toNat` are corollaries. -/

/-- `mask ^^^ shifted`: the "absolute value minus one" step, at the `toNat` level. -/
private theorem xor_mask_toNat (b : BitVec 16) :
    ((b.sshiftRight 15) ^^^ b).toNat = if b.msb then 65535 - b.toNat else b.toNat := by
  rw [sshr15_bv b]
  split
  · rw [BitVec.allOnes_xor, BitVec.toNat_not]
  · rw [BitVec.zero_xor]

/-- The SECOND mask: `(p - t) >>> 15 &&& 1` is the indicator of `p < t`, for any `p`
    already known to sit in the nonnegative half and any threshold `t` in it too. This is
    the step that turns a sign bit into a `0`/`1` value, and it is where the `&&& 1` earns
    its keep.

    GENERIC in the threshold `t`: nothing here is specific to the `d = 1` half-width
    `832`, so another `d`, or an `abs`-style clamp at a different bound, instantiates this
    instead of restating it. The `t = 832#16` instance is `mask_sub_step_832` below. -/
private theorem mask_sub_step (p t : BitVec 16) (hp : p.toNat < 32768)
    (ht : t.toNat ≤ 32768) :
    ((p - t).sshiftRight 15) &&& (1#16) = if p.toNat < t.toNat then 1#16 else 0#16 := by
  have hirn : (p - t).toNat = (65536 - t.toNat + p.toNat) % 65536 := by
    rw [BitVec.toNat_sub, show (2:Nat) ^ 16 = 65536 from rfl]
  have hiff := msb16_iff (p - t)
  rw [sshr15_bv]
  by_cases hc : p.toNat < t.toNat
  · have hm : (p - t).msb = true := by
      rcases Bool.eq_false_or_eq_true (p - t).msb with h | h
      · exact h
      · exfalso
        have h1 := hiff.mp h
        rw [hirn, Nat.mod_eq_of_lt (by omega)] at h1
        omega
    rw [hm, if_pos hc]
    simp only [if_true, BitVec.allOnes_and]
  · have hm : (p - t).msb = false := by
      rw [hiff, hirn, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hm, if_neg hc]
    simp only [Bool.false_eq_true, if_false, BitVec.zero_and]

/-- The `t = 832#16` instance of `mask_sub_step`, with the threshold literal reduced.
    The ONLY place `832` is hard-coded in this bank. -/
private theorem mask_sub_step_832 (p : BitVec 16) (hp : p.toNat < 32768) :
    ((p - (832#16)).sshiftRight 15) &&& (1#16) = if p.toNat < 832 then 1#16 else 0#16 := by
  have h832 : ((832#16 : BitVec 16)).toNat = 832 := rfl
  rw [mask_sub_step p (832#16) hp (by rw [h832]; omega), h832]

private theorem cmcBv_eq (b : BitVec 16) :
    cmcBv b = if 833 ≤ b.toNat ∧ b.toNat ≤ 2496 then 1#16 else 0#16 := by
  have hb := toNat16_lt b
  have hs65 := toNat16_lt ((1664#16) - b)
  -- the wrapped difference `1664 - b`, as a linear fact `omega` can use directly
  have hsn : ((1664#16) - b).toNat = (65536 - b.toNat + 1664) % 65536 := by
    rw [BitVec.toNat_sub, show ((1664#16 : BitVec 16)).toNat = 1664 from rfl,
      show (2:Nat) ^ 16 = 65536 from rfl]
  have hsv : ((1664#16) - b).toNat + b.toNat = 1664
      ∨ ((1664#16) - b).toNat + b.toNat = 67200 := by
    rcases Nat.lt_or_ge b.toNat 1665 with hc | hc
    · left
      rw [hsn, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · right
      rw [hsn, Nat.mod_eq_of_lt (by omega)]
      omega
  -- `positive`: the sign-folded magnitude. BOTH facts we need come out of ONE case split.
  have hmain : (((1664#16) - b).sshiftRight 15 ^^^ ((1664#16) - b)).toNat < 32768
      ∧ ((((1664#16) - b).sshiftRight 15 ^^^ ((1664#16) - b)).toNat < 832
          ↔ (833 ≤ b.toNat ∧ b.toNat ≤ 2496)) := by
    have hmsb := msb16_iff ((1664#16) - b)
    rw [xor_mask_toNat]
    rcases Bool.eq_false_or_eq_true ((1664#16) - b).msb with h | h
    · have hge : ¬ (((1664#16) - b).toNat < 32768) := by
        intro hc
        rw [hmsb.mpr hc] at h
        exact Bool.noConfusion h
      rw [h, if_pos rfl]
      omega
    · have hlt := hmsb.mp h
      rw [h]
      simp only [Bool.false_eq_true, if_false]
      omega
  unfold cmcBv
  rw [mask_sub_step_832 _ hmain.1]
  simp only [hmain.2]

/-- **M-D(1) — the IMPL seam.** The branch-free double-sign-mask computes the interval
    indicator `1 iff 833 ≤ fe ≤ 2496`.

    UNCONDITIONAL in `fe`, which is measured over the whole `u16` range and not assumed —
    the masks are total. This is the K8 content: `xor_clamp_val` (ml-dsa
    `Rounding.lean:121`) is the nearest template and targets a bound rather than an
    interval, so it is a shape to COPY, never to import. -/
theorem compress_message_coefficient_eq (fe : Std.U16) :
    libcrux_iot_ml_kem.vector.portable.compress.compress_message_coefficient fe
      = .ok (u8OfNat (if 833 ≤ fe.val ∧ fe.val ≤ 2496 then 1 else 0)) := by
  rw [cmc_seam, cmcBv_eq, show fe.bv.toNat = fe.val from rfl]
  by_cases hk : 833 ≤ fe.val ∧ fe.val ≤ 2496
  · rw [if_pos hk, if_pos hk]; rfl
  · rw [if_neg hk, if_neg hk]; rfl

/-- **M-D(2) — the PURE bridge.** The spec's `d = 1` closed form (from M-C′(3)
    `compress_d_gen_eq`, which is generic in `d < 12` and so already covers `d = 1`) IS
    the threshold predicate.

    `hx` is load-bearing: first counterexample `x = 4162`, the same witness `AMENDMENTS 2`
    records for L5.2's missing bound. -/
theorem compress_1_threshold_eq (x : Nat) (hx : x < 3329) :
    ((2 * x * 2 ^ 1 + 3329) / 6658) % 2 ^ 1
      = (if 833 ≤ x ∧ x ≤ 2496 then 1 else 0) := by
  -- `(4x + 3329) / 6658 ∈ {0, 1, 2}` under `hx`, and only the middle quotient is odd:
  -- `q = 0` for `x ≤ 832`, `q = 1` for `833 ≤ x ≤ 2496`, `q = 2` for `2497 ≤ x ≤ 3328`.
  -- Without `hx` the first `q = 3` lands at `x = 4162`, which is odd again — the
  -- counterexample `AMENDMENTS 2` records for L5.2.
  split <;> omega

end MDBank

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
    ⦃ ⇓ p => ⌜ (hacspec_ml_kem.serialize.deserialize_then_decompress_message serialized
                  = .ok (lift_poly p))
                ∧ (∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
                    ((p.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs
                      ≤ 3328) ⌝ ⦄ := by
  -- Impl side: the 16-chunk loop puts `1665 · bit` in every lane.
  obtain ⟨p, hp_eq, hp⟩ := triple_exists_ok_fc (message_impl_fc serialized re)
  have hmsg : msglane serialized.val p 16 := (holds_ok _).mp hp
  -- Spec side: `ByteDecode_1` then `Decompress_1` reproduces exactly those lanes.
  refine triple_of_ok_fc hp_eq ⟨message_spec_eq serialized p hmsg, ?_⟩
  -- BOUND CONJUNCT (added 2026-08-18 per KB: transcribe the `ensures`).
  -- Upstream ensures `is_bounded_poly (sz 3328) $result`. Stated at 3328 (not the
  -- tighter true 1665) because 3328 is the form every downstream consumer binds --
  -- notably `compute_message_fc`, whose precondition this is meant to satisfy.
  --   `hmsg` : msglane => lane .bv.toNat = if sliceBit .. then 1665 else 0
  -- so every lane is 0 or 1665; both are < 2^15, so .val = .bv.toNat and natAbs ≤ 1665.
  intro chunk hchunk ℓ hℓ
  have hlane := hmsg chunk hchunk ℓ hℓ
  have hlt : ((p.coefficients.val[chunk]!).elements.val[ℓ]!).bv.toNat < 4096 := by
    rw [hlane]; split <;> omega
  rw [i16_val_of_toNat _ hlt, hlane]
  split <;> simp

/-! ## L5.2 bank — ENCODE at `d = 1` (`compress_then_serialize_message`).

    Stated HERE, at the end of the file, for the same reason L5.1 is: the obligation
    assembles `compress_message_coefficient_eq` / `compress_1_threshold_eq` (M-D, above)
    and `compress_d_gen_eq` (M-C′), all of which live after L5.2's scaffold position.

    ### What is NEW here, and what is copied

    * COPIED, not cited: the three-level `createi` normalisation of `byte_encode`
      (`byte_encode_12_eq`'s shape, `L56Bank`). Those lemmas are hard-wired at
      `384 / 3072 / d = 12` and conclude against `encByte`, a `d = 12` byte model with no
      `d` parameter, so they cannot be instantiated here; the SHAPE transfers verbatim at
      `32 / 256 / d = 1`.
    * NOT applicable: `bitSum_laneBit_window` (M-C) carries `4 ≤ d`. At `d = 1` lane `j`
      occupies bit `j` exactly, so a byte is a one-to-one fold of eight lanes and there is
      no group law to instantiate. `msgByte` IS the `bits_to_bytes` window by definition.
    * NEW (no exemplar at any width): the `serialize_1` impl seam. `serialize_N` had no
      precedent in this tree at any `N`; `serialize_1_eq` below is that gap closed, and it
      needed nothing beyond the `u8_or_bit_step` accumulator the encode bank already had —
      a page of straight-line body walk, not a new technique.
    * REUSED from `L56Bank`: `encLane`/`uval` (the canonical-residue model),
      `to_unsigned_fm_eq` + `uval_encLane` (where `h_bnd` is consumed the FIRST time),
      `slice_index_mut_range_strict` + `slice_update_eq` (the K2 write-back),
      `u8_shl_iscalar` / `u8_or_bit_step` / `bitSum` (the packing accumulator). -/

section L52Bank

/-! ### Scalar seams the `d = 1` path needs and the `d = 12` path did not. -/

/-- `as_u16` on an `I16`: a SAME-WIDTH cast, so it is faithful with no side condition. -/
private def cu16 (x : Std.I16) : Std.U16 := Std.IScalar.hcast .U16 x

private theorem as_u16_eq (x : Std.I16) :
    libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_u16 x = .ok (cu16 x) := by
  unfold libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_u16
    libcrux_secrets.traits.Declassify.Blanket.declassify
    libcrux_secrets.traits.Classify.Blanket.classify
  simp [cu16, Aeneas.Std.lift]

private theorem cu16_val (x : Std.I16) : (cu16 x).val = x.bv.toNat := by
  show (Std.UScalar.bv (Std.IScalar.hcast .U16 x)).toNat = _
  rw [Std.IScalar.hcast_bv_eq, BitVec.signExtend_eq_setWidth_of_le _ (by decide),
    BitVec.toNat_setWidth]
  show x.bv.toNat % 2 ^ 16 = x.bv.toNat
  exact Nat.mod_eq_of_lt (by simpa using toNat16_lt x.bv)

private theorem as_u8_eq (x : Std.I16) :
    libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_u8 x = .ok (c8 x) := by
  unfold libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_u8
    libcrux_secrets.traits.Declassify.Blanket.declassify
    libcrux_secrets.traits.Classify.Blanket.classify
  simp [c8, Aeneas.Std.lift]

/-- One slot of the `serialize_1` OR chain: a `0`/`1` byte shifted by a closed amount.
    The `d = 12` bank's `u8_bit_shl` is stated for `cast_fromBool`; here the bit already
    arrived as a `U8` whose value is `0` or `1`, so the bound is the same but the source
    is not. -/
private theorem u8_bit_shl_of_val (x : Std.U8) (b : Bool) (t : Std.I32) (e : Nat)
    (hx : x.val = if b then 1 else 0)
    (ht0 : 0 ≤ t.val) (ht : t.val < 8) (he : t.toNat = e) (he8 : e < 8) :
    ∃ z : Std.U8, (x <<< t : RustM Std.U8) = .ok z ∧ z.val = if b then 2 ^ e else 0 := by
  have hpow : (2:Nat) ^ e ≤ 128 := by
    calc (2:Nat) ^ e ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 128 := by norm_num
  obtain ⟨z, hz, hzv⟩ := u8_shl_iscalar x t ht0 ht (by rw [hx, he]; split <;> omega)
  exact ⟨z, hz, by rw [hzv, hx, he]; split <;> omega⟩

/-! ### The pure `Nat` / `Bool` model at `d = 1`.

    `msgBit re j` is the compressed bit of lane `j` and `msgByte re n` is byte `n`.
    Because `d = 1` divides `8`, `msgByte` is LITERALLY the `bits_to_bytes` window, so
    the spec-side Level-3 step is a `bitSum_congr` and nothing more. -/

/-- The compressed bit of lane `j`: `Compress_1(canon(re[j]))`, as a `Bool`. The
    threshold form comes from M-D's `compress_1_threshold_eq` / `compress_message_coefficient_eq`,
    which is why BOTH sides can be stated against it. -/
private def msgBit (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (j : Nat) : Bool :=
  decide (833 ≤ encLane re j ∧ encLane re j ≤ 2496)

/-- Byte `n` of the `d = 1` packing of `re`: the LSB-first fold of lanes `8n … 8n+7`. -/
private def msgByte (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (n : Nat) : Nat :=
  bitSum (fun t => msgBit re (8 * n + t)) 8

private theorem msgByte_lt (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (n : Nat) :
    msgByte re n < 256 := by
  have := bitSum_lt (fun t => msgBit re (8 * n + t)) 8
  simpa [msgByte] using this

/-! ### Impl step 2 — `compress_1`.

    The per-lane body is `as_u16 ∘ compress_message_coefficient ∘ as_i16`, and M-D's
    `compress_message_coefficient_eq` is UNCONDITIONAL, so `cmc1` below is total and the
    whole 16-lane loop is `LoopHelper.elementwise_unary_spec` at `per_elem := cmc1`. No
    new loop reasoning: the body is literally `unary_loop_body cmc1`. -/

/-- The per-lane closed form of `compress_1`'s body. -/
private def cmc1 (x : Std.I16) : RustM Std.I16 :=
  .ok (c16 (u8OfNat (if 833 ≤ x.bv.toNat ∧ x.bv.toNat ≤ 2496 then 1 else 0)))

private theorem cmc1_toNat (x : Std.I16) :
    ∃ r : Std.I16, cmc1 x = .ok r
      ∧ r.bv.toNat = if 833 ≤ x.bv.toNat ∧ x.bv.toNat ≤ 2496 then 1 else 0 := by
  refine ⟨_, rfl, ?_⟩
  rw [c16_bv_toNat, u8OfNat_val _ (by split <;> omega)]

/-- The extracted `compress_1` body IS `unary_loop_body cmc1`: every intermediate step
    (`as_u16`, `compress_message_coefficient`, `as_i16`) is total, so the flat bind chain
    collapses onto the canonical unary shape. -/
private theorem compress_1_body_eq (iter : CoreModels.core.ops.range.Range Std.Usize)
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    libcrux_iot_ml_kem.vector.portable.compress.compress_1_loop.body iter v
      = libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.unary_loop_body cmc1 iter v := by
  unfold libcrux_iot_ml_kem.vector.portable.compress.compress_1_loop.body
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.unary_loop_body
  simp only [as_u16_eq, compress_message_coefficient_eq, cu16_val, as_i16_eq, cmc1,
    Aeneas.Std.bind_tc_ok]
  rfl

private theorem compress_1_eq
    (v0 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ∃ r : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector,
      libcrux_iot_ml_kem.vector.portable.compress.compress_1 v0 = .ok r
      ∧ ∀ l : Nat, l < 16 →
          (r.elements.val[l]!).bv.toNat
            = if 833 ≤ (v0.elements.val[l]!).bv.toNat
                ∧ (v0.elements.val[l]!).bv.toNat ≤ 2496 then 1 else 0 := by
  have hloop : libcrux_iot_ml_kem.vector.portable.compress.compress_1 v0
      = loop (fun p => libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.unary_loop_body
                cmc1 p.1 p.2)
          (({ start := 0#usize, «end» := 16#usize }
              : CoreModels.core.ops.range.Range Std.Usize), v0) := by
    unfold libcrux_iot_ml_kem.vector.portable.compress.compress_1
      libcrux_iot_ml_kem.vector.portable.compress.compress_1_loop
    congr 1
    · funext p
      exact compress_1_body_eq p.1 p.2
    · have hFEV : (libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR : Std.Usize)
          = (16#usize : Std.Usize) :=
        Std.UScalar.eq_of_val_eq (by
          rw [libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.field_elements_in_vector_val]
          scalar_tac)
      rw [hFEV]
  obtain ⟨r, hr_eq, hr⟩ := triple_exists_ok_fc
    (libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.elementwise_unary_spec cmc1
      (fun x y => y.bv.toNat
        = if 833 ≤ x.bv.toNat ∧ x.bv.toNat ≤ 2496 then 1 else 0)
      (fun x => by
        obtain ⟨y, hy_eq, hy⟩ := cmc1_toNat x
        exact triple_of_ok_fc hy_eq hy)
      v0)
  refine ⟨r, by rw [hloop]; exact hr_eq, ?_⟩
  intro l hl
  obtain ⟨ri, _, hri, hP⟩ := hr l hl
  rw [hri]; exact hP

/-! ### Impl step 3 — `serialize_1`. THE UNCOVERED SEAM.

    There is no `serialize_N` exemplar in this tree at ANY width (the decode side has
    `deserialize_1_eq` / `deserialize_5_int_lanes_eq`; the encode side had only
    `serialize_12`, which goes through `serialize_12_int` and a 3-byte group law). This is
    that gap closed, and the measured answer is: **no new technique was needed.** It is a
    straight-line body walk over the accumulator the `d = 12` encode bank already banked
    (`u8_shl_iscalar` → `u8_or_bit_step` → `bitSum`), with `u8_bit_shl_of_val` as the only
    new one-liner (the bit arrives as a `U8` of value `0`/`1` rather than as
    `cast_fromBool`).

    Stated against an ARBITRARY `f : Nat → Bool` rather than against `msgBit`: the two
    output bytes are then the two `bitSum` windows verbatim, so the caller supplies
    `f := msgBit re ∘ (16 * i + ·)` and no re-indexing algebra enters the loop residue. -/
set_option maxHeartbeats 4000000 in
private theorem serialize_1_eq
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8) (h : out.val.length = 2) (f : Nat → Bool)
    (hv : ∀ l : Nat, l < 16 → (v.elements.val[l]!).bv.toNat = if f l then 1 else 0) :
    ∃ s : Slice Std.U8,
      libcrux_iot_ml_kem.vector.portable.serialize.serialize_1 v out = .ok s
      ∧ s.val.length = 2
      ∧ (s.val[0]!).val = bitSum f 8
      ∧ (s.val[1]!).val = bitSum (fun t => f (8 + t)) 8 := by
  have hE : v.elements.val.length = 16 := by have := v.elements.property; simpa using this
  have hb : ∀ l : Nat, l < 16 → (c8 (v.elements.val[l]!)).val = if f l then 1 else 0 := by
    intro l hl
    rw [c8_val, hv l hl]
    split <;> norm_num
  have hidx : ∀ (u : Std.Usize) (l : Nat), u.val = l → l < 16 →
      Aeneas.Std.Array.index_usize v.elements u = .ok (v.elements.val[l]!) := by
    intro u l hu hl
    rw [enc_array_index_ok v.elements u (by rw [hE, hu]; omega), hu]
  have q0 := hidx 0#usize 0 (by scalar_tac) (by omega)
  have q1 := hidx 1#usize 1 (by scalar_tac) (by omega)
  have q2 := hidx 2#usize 2 (by scalar_tac) (by omega)
  have q3 := hidx 3#usize 3 (by scalar_tac) (by omega)
  have q4 := hidx 4#usize 4 (by scalar_tac) (by omega)
  have q5 := hidx 5#usize 5 (by scalar_tac) (by omega)
  have q6 := hidx 6#usize 6 (by scalar_tac) (by omega)
  have q7 := hidx 7#usize 7 (by scalar_tac) (by omega)
  have q8 := hidx 8#usize 8 (by scalar_tac) (by omega)
  have q9 := hidx 9#usize 9 (by scalar_tac) (by omega)
  have q10 := hidx 10#usize 10 (by scalar_tac) (by omega)
  have q11 := hidx 11#usize 11 (by scalar_tac) (by omega)
  have q12 := hidx 12#usize 12 (by scalar_tac) (by omega)
  have q13 := hidx 13#usize 13 (by scalar_tac) (by omega)
  have q14 := hidx 14#usize 14 (by scalar_tac) (by omega)
  have q15 := hidx 15#usize 15 (by scalar_tac) (by omega)
  -- the fourteen shifted slots, seven per output byte
  obtain ⟨z1, hz1, hz1v⟩ := u8_bit_shl_of_val (c8 (v.elements.val[1]!)) (f 1) 1#i32 1
    (hb 1 (by omega)) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z2, hz2, hz2v⟩ := u8_bit_shl_of_val (c8 (v.elements.val[2]!)) (f 2) 2#i32 2
    (hb 2 (by omega)) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z3, hz3, hz3v⟩ := u8_bit_shl_of_val (c8 (v.elements.val[3]!)) (f 3) 3#i32 3
    (hb 3 (by omega)) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z4, hz4, hz4v⟩ := u8_bit_shl_of_val (c8 (v.elements.val[4]!)) (f 4) 4#i32 4
    (hb 4 (by omega)) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z5, hz5, hz5v⟩ := u8_bit_shl_of_val (c8 (v.elements.val[5]!)) (f 5) 5#i32 5
    (hb 5 (by omega)) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z6, hz6, hz6v⟩ := u8_bit_shl_of_val (c8 (v.elements.val[6]!)) (f 6) 6#i32 6
    (hb 6 (by omega)) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z7, hz7, hz7v⟩ := u8_bit_shl_of_val (c8 (v.elements.val[7]!)) (f 7) 7#i32 7
    (hb 7 (by omega)) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z9, hz9, hz9v⟩ := u8_bit_shl_of_val (c8 (v.elements.val[9]!)) (f 9) 1#i32 1
    (hb 9 (by omega)) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z10, hz10, hz10v⟩ := u8_bit_shl_of_val (c8 (v.elements.val[10]!)) (f 10) 2#i32 2
    (hb 10 (by omega)) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z11, hz11, hz11v⟩ := u8_bit_shl_of_val (c8 (v.elements.val[11]!)) (f 11) 3#i32 3
    (hb 11 (by omega)) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z12, hz12, hz12v⟩ := u8_bit_shl_of_val (c8 (v.elements.val[12]!)) (f 12) 4#i32 4
    (hb 12 (by omega)) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z13, hz13, hz13v⟩ := u8_bit_shl_of_val (c8 (v.elements.val[13]!)) (f 13) 5#i32 5
    (hb 13 (by omega)) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z14, hz14, hz14v⟩ := u8_bit_shl_of_val (c8 (v.elements.val[14]!)) (f 14) 6#i32 6
    (hb 14 (by omega)) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z15, hz15, hz15v⟩ := u8_bit_shl_of_val (c8 (v.elements.val[15]!)) (f 15) 7#i32 7
    (hb 15 (by omega)) (by decide) (by decide) (by decide) (by decide)
  -- byte 0: the accumulation over lanes 0 … 7, in pure `Nat`
  have a0 : (c8 (v.elements.val[0]!)).val = bitSum f 1 := by
    rw [hb 0 (by omega)]
    show _ = bitSum f 0 + (if f 0 then 2 ^ 0 else 0)
    simp only [bitSum, pow_zero]
    split <;> omega
  have a1 := u8_or_bit_step f _ z1 (f 1) 1 a0 hz1v rfl
  have a2 := u8_or_bit_step f _ z2 (f 2) 2 a1 hz2v rfl
  have a3 := u8_or_bit_step f _ z3 (f 3) 3 a2 hz3v rfl
  have a4 := u8_or_bit_step f _ z4 (f 4) 4 a3 hz4v rfl
  have a5 := u8_or_bit_step f _ z5 (f 5) 5 a4 hz5v rfl
  have a6 := u8_or_bit_step f _ z6 (f 6) 6 a5 hz6v rfl
  have a7 := u8_or_bit_step f _ z7 (f 7) 7 a6 hz7v rfl
  -- byte 1: the same accumulation over lanes 8 … 15, against the shifted window
  have b0 : (c8 (v.elements.val[8]!)).val = bitSum (fun t => f (8 + t)) 1 := by
    rw [hb 8 (by omega)]
    show _ = bitSum (fun t => f (8 + t)) 0 + (if f (8 + 0) then 2 ^ 0 else 0)
    simp only [bitSum, pow_zero, Nat.add_zero]
    split <;> omega
  have b1 := u8_or_bit_step (fun t => f (8 + t)) _ z9 (f 9) 1 b0 hz9v (by norm_num)
  have b2 := u8_or_bit_step (fun t => f (8 + t)) _ z10 (f 10) 2 b1 hz10v (by norm_num)
  have b3 := u8_or_bit_step (fun t => f (8 + t)) _ z11 (f 11) 3 b2 hz11v (by norm_num)
  have b4 := u8_or_bit_step (fun t => f (8 + t)) _ z12 (f 12) 4 b3 hz12v (by norm_num)
  have b5 := u8_or_bit_step (fun t => f (8 + t)) _ z13 (f 13) 5 b4 hz13v (by norm_num)
  have b6 := u8_or_bit_step (fun t => f (8 + t)) _ z14 (f 14) 6 b5 hz14v (by norm_num)
  have b7 := u8_or_bit_step (fun t => f (8 + t)) _ z15 (f 15) 7 b6 hz15v (by norm_num)
  -- `bitSum _ (7 + 1)` is `bitSum _ 8` by reduction; name the closed forms once
  have a7' : (c8 (v.elements.val[0]!) ||| z1 ||| z2 ||| z3 ||| z4 ||| z5 ||| z6 ||| z7).val
      = bitSum f 8 := a7
  have b7' : (c8 (v.elements.val[8]!) ||| z9 ||| z10 ||| z11 ||| z12 ||| z13 ||| z14
        ||| z15).val
      = bitSum (fun t => f (8 + t)) 8 := b7
  have hu0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
  have hu1 : (1#usize : Std.Usize).val = 1 := by scalar_tac
  have hlen : CoreModels.core.slice.Slice.len out = .ok (2#usize : Std.Usize) := by
    show RustM.ok (Aeneas.Std.Slice.len out) = _
    congr 1
    apply Std.UScalar.eq_of_val_eq
    simp [Aeneas.Std.Slice.len_val, h]
  refine ⟨(out.set 0#usize
              (c8 (v.elements.val[0]!) ||| z1 ||| z2 ||| z3 ||| z4 ||| z5 ||| z6 ||| z7)).set
            1#usize
              (c8 (v.elements.val[8]!) ||| z9 ||| z10 ||| z11 ||| z12 ||| z13 ||| z14 ||| z15),
          ?_, ?_, ?_, ?_⟩
  · unfold libcrux_iot_ml_kem.vector.portable.serialize.serialize_1
    rw [hlen]
    simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.massert, if_true,
      q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15,
      as_u8_eq, hz1, hz2, hz3, hz4, hz5, hz6, hz7,
      hz9, hz10, hz11, hz12, hz13, hz14, hz15, Aeneas.Std.lift]
    rw [slice_update_eq _ _ _ (by simp only [h]; scalar_tac)]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [slice_update_eq _ _ _
      (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]
  · simp only [Aeneas.Std.Slice.set_val_eq, List.length_set]; exact h
  · simp only [Aeneas.Std.Slice.set_val_eq, hu0, hu1]
    rw [← a7']
    simp_lists
  · simp only [Aeneas.Std.Slice.set_val_eq, hu0, hu1]
    rw [← b7']
    simp_lists

/-! ### Impl apex — the `0..16` range loop with the 2-byte mutable subslice write-back.

    Structurally identical to `serialize_uncompressed_loop_fc` (K2): written-prefix
    invariant, `slice_index_mut_range_strict` for `&mut serialized[2i .. 2i+2]`,
    `List.getElem!_setSlice!_{prefix,middle}` for the two conjuncts. Only the chunk width
    changes, 24 → 2. -/

/-- Written-prefix loop invariant: after `k` iterations the first `2k` bytes carry
    `msgByte`, and the length is preserved. -/
private def msgInv (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (acc : Slice Std.U8 × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    RustM Prop :=
  pure (acc.1.val.length = 32 ∧
        ∀ n : Nat, n < 2 * k.val → (acc.1.val[n]!).val = msgByte re n)

/-- The two bytes one chunk writes, re-indexed onto the global byte stream. -/
private theorem s1chunk_get
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Nat) (s : Slice Std.U8)
    (h0 : (s.val[0]!).val = msgByte re (2 * k))
    (h1 : (s.val[1]!).val = msgByte re (2 * k + 1))
    (m : Nat) (hm : m < 2) : (s.val[m]!).val = msgByte re (2 * k + m) := by
  interval_cases m
  · simpa using h0
  · simpa using h1

set_option maxHeartbeats 4000000 in
private theorem msg_enc_loop_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hbnd : ∀ c : Nat, c < 16 → ∀ l : Nat, l < 16 →
      ((re.coefficients.val[c]!).elements.val[l]!).val.natAbs ≤ 3328)
    (serialized : Slice Std.U8)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_len : serialized.val.length = 32) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.compress_then_serialize_message_loop
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := 0#usize, «end» := 16#usize } re serialized scratch
    ⦃ ⇓ p => ⌜ (msgInv re 16#usize p).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_message_loop
  refine libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
    (fun (iter1, serialized1, scratch1) =>
      libcrux_iot_ml_kem.serialize.compress_then_serialize_message_loop.body
        (vectortraitsOperationsInst := portable_ops_inst) re iter1 serialized1 scratch1)
    (serialized, scratch) 0#usize 16#usize (msgInv re) (by scalar_tac) ?_ ?_
  · show (pure _ : RustM Prop).holds
    simp only [Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp]
    intro _
    exact ⟨h_len, by intro n hn; exact absurd hn (by scalar_tac)⟩
  · intro acc k hk0 hk16 hinv
    have h16 : (16#usize : Std.Usize).val = 16 := rfl
    obtain ⟨hacc_len, hacc_done⟩ : acc.1.val.length = 32 ∧
        ∀ n : Nat, n < 2 * k.val → (acc.1.val[n]!).val = msgByte re n := by
      have hh := hinv
      simp only [msgInv, Aeneas.Std.RustM.holds, pure, Pure.pure, Std.Do.Triple,
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
        to_unsigned_fm_eq (re.coefficients.val[k.val]!) acc.2
          (fun l hl => hbnd k.val hlt l hl)
      -- lane facts: `sc1` carries the canonical residues, `sc2` their compressed bits
      have hlanes : ∀ l : Nat, l < 16 →
          (sc1.elements.val[l]!).bv.toNat = encLane re (16 * k.val + l) := by
        intro l hl
        obtain ⟨hb0, hb1, hb2⟩ := hsc1 l hl
        exact uval_encLane re k.val l hlt hl _ hb0 hb1 hb2
      obtain ⟨sc2, hsc2_eq, hsc2⟩ := compress_1_eq sc1
      have hbits : ∀ l : Nat, l < 16 →
          (sc2.elements.val[l]!).bv.toNat
            = if msgBit re (16 * k.val + l) then 1 else 0 := by
        intro l hl
        rw [hsc2 l hl, hlanes l hl]
        unfold msgBit
        simp only [decide_eq_true_eq]
      obtain ⟨i1, hi1_eq, hi1⟩ := usize_mul_ok_e (2#usize : Std.Usize) k (by scalar_tac)
      obtain ⟨i2, hi2_eq, hi2⟩ := usize_add_ok_e i1 (2#usize : Std.Usize) (by scalar_tac)
      have hi1v : i1.val = 2 * k.val := by rw [hi1]; scalar_tac
      have hi2v : i2.val = 2 * k.val + 2 := by rw [hi2, hi1v]; scalar_tac
      obtain ⟨sub, wb, hmut_eq, hsub_len, hwb⟩ :=
        slice_index_mut_range_strict acc.1 i1 i2 (by omega) (by rw [hacc_len]; omega)
      have hsub2 : sub.val.length = 2 := by rw [hsub_len]; omega
      obtain ⟨s1, hs1_eq, hs1_len, hs1_b0, hs1_b1⟩ :=
        serialize_1_eq sc2 sub hsub2 (fun t => msgBit re (16 * k.val + t)) hbits
      -- re-index the two bytes onto the global stream
      have hb0 : (s1.val[0]!).val = msgByte re (2 * k.val) := by
        rw [hs1_b0]
        unfold msgByte
        exact bitSum_congr _ _ 8 (fun t _ => by congr 1; omega)
      have hb1 : (s1.val[1]!).val = msgByte re (2 * k.val + 1) := by
        rw [hs1_b1]
        unfold msgByte
        exact bitSum_congr _ _ 8 (fun t _ => by congr 1; omega)
      refine libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.triple_of_ok_fc
        (v := .cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize), (wb s1, sc2))) ?_ ?_
      · show libcrux_iot_ml_kem.serialize.compress_then_serialize_message_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) re
          { start := k, «end» := 16#usize } acc.1 acc.2 = _
        unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_message_loop.body
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
                             portable_ops_inst t acc.2
            let scratch2 ← libcrux_iot_ml_kem.vector.portable.compress.compress_1 scratch1
            let i1' ← (2#usize : Std.Usize) * k
            let i2' ← i1' + (2#usize : Std.Usize)
            let (sb, index_mut_back) ←
              CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
                (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                  Std.U8) acc.1 { start := i1', «end» := i2' }
            let sr ← libcrux_iot_ml_kem.vector.portable.serialize.serialize_1 scratch2 sb
            RustM.ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
              (index_mut_back sr, scratch2)))) = _
        rw [h_idx]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hsc1_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hsc2_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hi1_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hi2_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hmut_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hs1_eq]; rfl
      · refine ⟨by rw [h16]; exact hlt, rfl, hs_val, ?_⟩
        show (msgInv re s (wb s1, sc2)).holds
        simp only [msgInv, Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        have hwbv := hwb s1 (by rw [hs1_len]; omega)
        refine ⟨?_, ?_⟩
        · rw [hwbv, List.length_setSlice!]; exact hacc_len
        · intro n hn
          rw [hs_val] at hn
          rw [hwbv]
          by_cases hnk : n < 2 * k.val
          · rw [List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]
            exact hacc_done n hnk
          · rw [List.getElem!_setSlice!_middle _ _ _ _
              ⟨by omega, by rw [hs1_len]; omega, by rw [hacc_len]; omega⟩]
            rw [hi1v, s1chunk_get re k.val s1 hb0 hb1 (n - 2 * k.val) (by omega)]
            congr 1
            omega
    · have hk : k.val = 16 := by omega
      refine libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.triple_of_ok_fc
        (v := .done acc) ?_ ?_
      · show libcrux_iot_ml_kem.serialize.compress_then_serialize_message_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) re
          { start := k, «end» := 16#usize } acc.1 acc.2 = _
        unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_message_loop.body
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
      · show (msgInv re 16#usize acc).holds
        simp only [msgInv, Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        exact ⟨hacc_len, by intro n hn; exact hacc_done n (by rw [hk]; rw [h16] at hn; omega)⟩

/-- Impl-side apex: `compress_then_serialize_message` writes exactly `msgByte re` into all
    32 bytes and preserves the length. -/
private theorem msg_enc_impl_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hbnd : ∀ c : Nat, c < 16 → ∀ l : Nat, l < 16 →
      ((re.coefficients.val[c]!).elements.val[l]!).val.natAbs ≤ 3328)
    (serialized : Slice Std.U8)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_len : serialized.val.length = 32) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.compress_then_serialize_message
      (vectortraitsOperationsInst := portable_ops_inst) re serialized scratch
    ⦃ ⇓ p => ⌜ (msgInv re 16#usize p).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_message
  exact msg_enc_loop_fc re hbnd serialized scratch h_len

/-! ### Spec side — `byte_encode 32 256 (compress p 1) 1`.

    FOUR `createi` levels, one more than the `d = 12` encode bank, because the spec applies
    `Compress_1` to every coefficient first. Level 0 is where M-D and M-C′ are CITED:
    `compress_d_gen_eq` (generic in `d < 12`, hence covers `d = 1`) gives the closed form,
    and `compress_1_threshold_eq` turns it into the threshold predicate. Levels 1–3 are the
    `byte_encode_12_eq` shape at `32 / 256 / d = 1`.

    Note the ASYMMETRY in where the bound lives: on the spec side `compress_1_threshold_eq`'s
    `x < 3329` is discharged by `encLane_lt`, which is definitional (`encLane` is a residue
    mod q by construction). `h_bnd` is therefore consumed on the IMPL side only — through
    `to_unsigned_fm_eq`, which is what makes the impl lane equal that residue at all. -/

/-- The spec-side compressed coefficient at lane `k`. -/
private def msgFe (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (k : Nat) :
    hacspec_ml_kem.parameters.FieldElement :=
  { val := u16OfNat (if msgBit re k then 1 else 0) }

/-! #### Level 0 — `compress.compress p 1`: every coefficient becomes its compressed bit. -/

private theorem compress_msg_closure_eq
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Nat) (hk : k < 256) :
    (hacspec_ml_kem.compress.compress.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement).call_mut
        (lift_poly re, (1#usize : Std.Usize)) ⟨BitVec.ofNat _ k⟩
      = .ok (msgFe re k, (lift_poly re, (1#usize : Std.Usize))) := by
  have hkv : ((⟨BitVec.ofNat _ k⟩ : Std.Usize)).val = k :=
    enc_usize_ofNat_val k (by omega)
  have hlen : (lift_poly re).val.length = 256 := by
    have := (lift_poly re).property; simpa using this
  show (do
      let fe ← Aeneas.Std.Array.index_usize (lift_poly re) (⟨BitVec.ofNat _ k⟩ : Std.Usize)
      let fe1 ← hacspec_ml_kem.compress.compress_d fe (1#usize : Std.Usize)
      RustM.ok (fe1, ((lift_poly re, (1#usize : Std.Usize))
        : hacspec_ml_kem.compress.compress.closure))) = _
  rw [enc_array_index_ok (lift_poly re) _ (by rw [hkv, hlen]; exact hk), hkv]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [compress_d_gen_eq ((lift_poly re).val[k]!) (1#usize : Std.Usize) (by scalar_tac)]
  simp only [Aeneas.Std.bind_tc_ok]
  -- M-C′(3) gave the closed form; M-D(2) turns it into the threshold predicate
  rw [show ((1#usize : Std.Usize)).val = 1 from by scalar_tac, lift_poly_raw re k hk,
    compress_1_threshold_eq (encLane re k) (encLane_lt re k)]
  unfold msgFe msgBit
  simp only [decide_eq_true_eq]
  rfl

/-- **Level 0.** The 256 compressed coefficients are exactly `msgBit re`. -/
private theorem compress_msg_get
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ∃ a : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize,
      hacspec_ml_kem.compress.compress (lift_poly re) (1#usize : Std.Usize) = .ok a
      ∧ ∀ k : Nat, k < 256 → ((a.val[k]!).val).val = if msgBit re k then 1 else 0 := by
  have h256 : ((256#usize : Std.Usize)).val = 256 := by scalar_tac
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
      (T := hacspec_ml_kem.parameters.FieldElement) (256#usize : Std.Usize)
      (hacspec_ml_kem.compress.compress.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement)
      (lift_poly re, (1#usize : Std.Usize))
      (fun k => msgFe re k)
      (fun k hk => compress_msg_closure_eq re k (by rw [h256] at hk; exact hk))
  unfold hacspec_ml_kem.compress.compress
  simp only [hacspec_ml_kem.parameters.createi]
  rw [hfn]
  refine ⟨_, rfl, ?_⟩
  intro k hk
  rw [enc_mk_getElem (by rw [h256]; exact hk)]
  show ((msgFe re k).val).val = _
  unfold msgFe
  exact u16OfNat_val _ (by split <;> scalar_tac)

/-! #### Level 1 — `byte_encode`'s own `createi`, generic in the two width params.

    The `d = 12` bank states this at `384 / 3072`; the closure body never mentions either,
    so the generic form below is the same twelve lines and serves both. -/

private theorem byte_encode_closure_eq_gen {D32 D256 : Std.Usize}
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) (k : Nat) (hk : k < 256) :
    (hacspec_ml_kem.serialize.byte_encode.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16
        D32 D256).call_mut p ⟨BitVec.ofNat _ k⟩
      = .ok ((p.val[k]!).val, p) := by
  have hkv : ((⟨BitVec.ofNat _ k⟩ : Std.Usize)).val = k :=
    enc_usize_ofNat_val k (by omega)
  have hlen : p.val.length = 256 := by have := p.property; simpa using this
  show (do
      let fe ← Aeneas.Std.Array.index_usize p (⟨BitVec.ofNat _ k⟩ : Std.Usize)
      RustM.ok (fe.val, p)) = _
  rw [enc_array_index_ok p _ (by rw [hkv, hlen]; exact hk), hkv]
  simp only [Aeneas.Std.bind_tc_ok]

/-- **Level 1** at `d = 1`: the raw `U16` array is the `0`/`1` bit array. -/
private theorem byte_encode_msg_raw_get
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (ha : ∀ k : Nat, k < 256 → ((a.val[k]!).val).val = if msgBit re k then 1 else 0) :
    ∃ p_raw : Std.Array Std.U16 256#usize,
      hacspec_ml_kem.parameters.createi (256#usize : Std.Usize)
          (hacspec_ml_kem.serialize.byte_encode.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16
            32#usize 256#usize) a
        = .ok p_raw
      ∧ ∀ k : Nat, k < 256 → (p_raw.val[k]!).val = if msgBit re k then 1 else 0 := by
  have h256 : ((256#usize : Std.Usize)).val = 256 := by scalar_tac
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq (T := Std.U16)
      (256#usize : Std.Usize)
      (hacspec_ml_kem.serialize.byte_encode.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16
        32#usize 256#usize) a
      (fun k => (a.val[k]!).val)
      (fun k hk => byte_encode_closure_eq_gen a k (by rw [h256] at hk; exact hk))
  simp only [hacspec_ml_kem.parameters.createi]
  rw [hfn]
  refine ⟨_, rfl, ?_⟩
  intro k hk
  rw [enc_mk_getElem (by rw [h256]; exact hk)]
  exact ha k hk

/-! #### Level 2 — `bitvector_from_bounded_ints` at `d = 1`: bit `m` IS lane `m`.

    `m / 1 = m` and `m % 1 = 0`, so there is no windowing at all: the bit stream is the
    lane stream. This is precisely why `bitSum_laneBit_window` (which needs `4 ≤ d`) has
    nothing to do here. -/

private theorem bvfb_closure_1_eq (a : Std.Array Std.U16 256#usize) (m : Nat) (hm : m < 256) :
    (hacspec_ml_kem.serialize.bitvector_from_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBool
        (256#usize : Std.Usize) (256#usize : Std.Usize)).call_mut
        (a, (1#usize : Std.Usize)) ⟨BitVec.ofNat _ m⟩
      = .ok (natBit ((a.val[m]!).val) 0, (a, (1#usize : Std.Usize))) := by
  have hmv : ((⟨BitVec.ofNat _ m⟩ : Std.Usize)).val = m :=
    enc_usize_ofNat_val m (by omega)
  have h1 : ((1#usize : Std.Usize)).val = 1 := by scalar_tac
  have hlen : a.val.length = 256 := by have := a.property; simpa using this
  obtain ⟨q, hq_eq, hq_val⟩ :=
    Std.UScalar.div_spec (⟨BitVec.ofNat _ m⟩ : Std.Usize)
      (y := (1#usize : Std.Usize)) (by decide)
  obtain ⟨r, hr_eq, hr_val⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.rem_spec (⟨BitVec.ofNat _ m⟩ : Std.Usize)
      (y := (1#usize : Std.Usize)) (by decide))
  have hqv : q.val = m := by rw [hq_val, hmv, h1, Nat.div_one]
  have hrv : r.val = 0 := by rw [hr_val, hmv, h1, Nat.mod_one]
  obtain ⟨y, hy_eq, hy⟩ := u16_shr_and1_eq (a.val[q.val]!) r (by rw [hrv]; omega)
  show (do
      let i1 ← (⟨BitVec.ofNat _ m⟩ : Std.Usize) / (1#usize : Std.Usize)
      let i2 ← Aeneas.Std.Array.index_usize a i1
      let i3 ← (⟨BitVec.ofNat _ m⟩ : Std.Usize) % (1#usize : Std.Usize)
      let i4 ← i2 >>> i3
      let i5 ← Aeneas.Std.lift (i4 &&& 1#u16)
      RustM.ok (decide (i5 = 1#u16),
        ((a, (1#usize : Std.Usize)) :
          hacspec_ml_kem.serialize.bitvector_from_bounded_ints.closure
            (256#usize : Std.Usize) (256#usize : Std.Usize)))) = _
  rw [hq_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok a q (by rw [hqv, hlen]; omega)]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hr_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hy_eq]; simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hy, hqv, hrv]
  rfl

/-- **Level 2.** The 256 booleans are exactly `msgBit re`. -/
private theorem bvfb_256_1_msg_get
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (p_raw : Std.Array Std.U16 256#usize)
    (hp : ∀ k : Nat, k < 256 → (p_raw.val[k]!).val = if msgBit re k then 1 else 0) :
    ∃ bv : Std.Array Bool 256#usize,
      hacspec_ml_kem.serialize.bitvector_from_bounded_ints (N := 256#usize)
          (256#usize : Std.Usize) p_raw (1#usize : Std.Usize) = .ok bv
      ∧ ∀ m : Nat, m < 256 → bv.val[m]! = msgBit re m := by
  have h256 : ((256#usize : Std.Usize)).val = 256 := by scalar_tac
  have hmul : ((256#usize : Std.Usize) * (1#usize : Std.Usize) : RustM Std.Usize)
      = .ok (256#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq (T := Bool)
      (256#usize : Std.Usize)
      (hacspec_ml_kem.serialize.bitvector_from_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBool
        (256#usize : Std.Usize) (256#usize : Std.Usize))
      (p_raw, (1#usize : Std.Usize))
      (fun m => natBit ((p_raw.val[m]!).val) 0)
      (fun m hm => bvfb_closure_1_eq p_raw m (by rw [h256] at hm; exact hm))
  have key : hacspec_ml_kem.serialize.bitvector_from_bounded_ints (N := 256#usize)
        (256#usize : Std.Usize) p_raw (1#usize : Std.Usize)
      = CoreModels.core.array.from_fn (256#usize : Std.Usize)
          (hacspec_ml_kem.serialize.bitvector_from_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBool
            (256#usize : Std.Usize) (256#usize : Std.Usize))
          (p_raw, (1#usize : Std.Usize)) := by
    unfold hacspec_ml_kem.serialize.bitvector_from_bounded_ints
    -- hax v0.4.0-rc.1 no longer emits the `let i ← N * 8#usize; massert (N8 = i)` prelude
    -- (ALL 74 spec-side `massert`s are gone from the extraction), so the length check and
    -- its `hmul` witness are no longer part of this equation.
    simp only [hacspec_ml_kem.parameters.createi]
  rw [key, hfn]
  refine ⟨_, rfl, ?_⟩
  intro m hm
  rw [enc_mk_getElem (by rw [h256]; exact hm)]
  show natBit ((p_raw.val[m]!).val) 0 = msgBit re m
  rw [hp m hm]
  cases hb : msgBit re m <;> simp [natBit]

/-! #### Level 3 — `bits_to_bytes`, generic in the two width params.

    The `d = 12` bank states this at `384 / 3072`; nothing in the closure body mentions
    either width, so the generic form below is the same body walk and covers both. Stated
    generically rather than copied so the `d ∈ {4,5,10,11}` rungs inherit it. -/

private theorem bits_to_bytes_closure_eq_gen {N N8 : Std.Usize} (bv : Std.Array Bool N8)
    (n : Nat) (hn : 8 * n + 8 ≤ N8.val) (hn32 : n < 2 ^ 32)
    (hmax : 8 * n + 8 ≤ Std.Usize.max) :
    (hacspec_ml_kem.serialize.bits_to_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
        N N8).call_mut bv ⟨BitVec.ofNat _ n⟩
      = .ok (u8OfNat (bitSum (fun t => bv.val[8 * n + t]!) 8), bv) := by
  set f : Nat → Bool := fun t => bv.val[8 * n + t]! with hf
  have hnv : ((⟨BitVec.ofNat _ n⟩ : Std.Usize)).val = n := enc_usize_ofNat_val n hn32
  have hlen : bv.val.length = N8.val := by have := bv.property; simpa using this
  have h8 : ((8#usize : Std.Usize)).val = 8 := by scalar_tac
  obtain ⟨i, hi, hiv0⟩ :=
    usize_mul_ok_e (8#usize : Std.Usize) (⟨BitVec.ofNat _ n⟩ : Std.Usize)
      (by rw [h8, hnv]; omega)
  have hiv : i.val = 8 * n := by rw [hiv0, h8, hnv]
  -- the eight cell indices
  obtain ⟨j1, hj1, hj1v⟩ := usize_add_ok_e i (1#usize) (by rw [hiv]; scalar_tac)
  obtain ⟨j2, hj2, hj2v⟩ := usize_add_ok_e i (2#usize) (by rw [hiv]; scalar_tac)
  obtain ⟨j3, hj3, hj3v⟩ := usize_add_ok_e i (3#usize) (by rw [hiv]; scalar_tac)
  obtain ⟨j4, hj4, hj4v⟩ := usize_add_ok_e i (4#usize) (by rw [hiv]; scalar_tac)
  obtain ⟨j5, hj5, hj5v⟩ := usize_add_ok_e i (5#usize) (by rw [hiv]; scalar_tac)
  obtain ⟨j6, hj6, hj6v⟩ := usize_add_ok_e i (6#usize) (by rw [hiv]; scalar_tac)
  obtain ⟨j7, hj7, hj7v⟩ := usize_add_ok_e i (7#usize) (by rw [hiv]; scalar_tac)
  have e1 : j1.val = 8 * n + 1 := by rw [hj1v, hiv]; scalar_tac
  have e2 : j2.val = 8 * n + 2 := by rw [hj2v, hiv]; scalar_tac
  have e3 : j3.val = 8 * n + 3 := by rw [hj3v, hiv]; scalar_tac
  have e4 : j4.val = 8 * n + 4 := by rw [hj4v, hiv]; scalar_tac
  have e5 : j5.val = 8 * n + 5 := by rw [hj5v, hiv]; scalar_tac
  have e6 : j6.val = 8 * n + 6 := by rw [hj6v, hiv]; scalar_tac
  have e7 : j7.val = 8 * n + 7 := by rw [hj7v, hiv]; scalar_tac
  -- the eight shifted slots
  obtain ⟨z1, hz1, hz1v⟩ :=
    u8_bit_shl (bv.val[j1.val]!) (1#i32) 1 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z2, hz2, hz2v⟩ :=
    u8_bit_shl (bv.val[j2.val]!) (2#i32) 2 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z3, hz3, hz3v⟩ :=
    u8_bit_shl (bv.val[j3.val]!) (3#i32) 3 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z4, hz4, hz4v⟩ :=
    u8_bit_shl (bv.val[j4.val]!) (4#i32) 4 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z5, hz5, hz5v⟩ :=
    u8_bit_shl (bv.val[j5.val]!) (5#i32) 5 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z6, hz6, hz6v⟩ :=
    u8_bit_shl (bv.val[j6.val]!) (6#i32) 6 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨z7, hz7, hz7v⟩ :=
    u8_bit_shl (bv.val[j7.val]!) (7#i32) 7 (by decide) (by decide) (by decide) (by decide)
  -- the accumulation, in pure `Nat`
  have a0 : (Std.UScalar.cast_fromBool .U8 (bv.val[i.val]!)).val = bitSum f 1 := by
    rw [cast_fromBool_u8_val]
    show _ = bitSum f 0 + (if f 0 then 2 ^ 0 else 0)
    simp only [bitSum, hf, hiv, Nat.add_zero, pow_zero]
    split <;> omega
  have a1 := u8_or_bit_step f _ z1 (bv.val[j1.val]!) 1 a0 hz1v (by rw [hf, e1])
  have a2 := u8_or_bit_step f _ z2 (bv.val[j2.val]!) 2 a1 hz2v (by rw [hf, e2])
  have a3 := u8_or_bit_step f _ z3 (bv.val[j3.val]!) 3 a2 hz3v (by rw [hf, e3])
  have a4 := u8_or_bit_step f _ z4 (bv.val[j4.val]!) 4 a3 hz4v (by rw [hf, e4])
  have a5 := u8_or_bit_step f _ z5 (bv.val[j5.val]!) 5 a4 hz5v (by rw [hf, e5])
  have a6 := u8_or_bit_step f _ z6 (bv.val[j6.val]!) 6 a5 hz6v (by rw [hf, e6])
  have a7 := u8_or_bit_step f _ z7 (bv.val[j7.val]!) 7 a6 hz7v (by rw [hf, e7])
  have hfinal : (Std.UScalar.cast_fromBool .U8 (bv.val[i.val]!) ||| z1 ||| z2 ||| z3 ||| z4
      ||| z5 ||| z6 ||| z7) = u8OfNat (bitSum f 8) := by
    refine Aeneas.Std.UScalar.eq_of_val_eq ?_
    rw [a7, u8OfNat_val _ (by have := bitSum_lt f 8; simpa using this)]
  show (do
      let i ← (8#usize : Std.Usize) * (⟨BitVec.ofNat _ n⟩ : Std.Usize)
      let b ← Aeneas.Std.Array.index_usize bv i
      let i1 ← Aeneas.Std.lift (Std.UScalar.cast_fromBool .U8 b)
      let i2 ← i + 1#usize
      let b1 ← Aeneas.Std.Array.index_usize bv i2
      let i3 ← Aeneas.Std.lift (Std.UScalar.cast_fromBool .U8 b1)
      let i4 ← i3 <<< (1#i32 : Std.I32)
      let i5 ← Aeneas.Std.lift (i1 ||| i4)
      let i6 ← i + 2#usize
      let b2 ← Aeneas.Std.Array.index_usize bv i6
      let i7 ← Aeneas.Std.lift (Std.UScalar.cast_fromBool .U8 b2)
      let i8 ← i7 <<< (2#i32 : Std.I32)
      let i9 ← Aeneas.Std.lift (i5 ||| i8)
      let i10 ← i + 3#usize
      let b3 ← Aeneas.Std.Array.index_usize bv i10
      let i11 ← Aeneas.Std.lift (Std.UScalar.cast_fromBool .U8 b3)
      let i12 ← i11 <<< (3#i32 : Std.I32)
      let i13 ← Aeneas.Std.lift (i9 ||| i12)
      let i14 ← i + 4#usize
      let b4 ← Aeneas.Std.Array.index_usize bv i14
      let i15 ← Aeneas.Std.lift (Std.UScalar.cast_fromBool .U8 b4)
      let i16 ← i15 <<< (4#i32 : Std.I32)
      let i17 ← Aeneas.Std.lift (i13 ||| i16)
      let i18 ← i + 5#usize
      let b5 ← Aeneas.Std.Array.index_usize bv i18
      let i19 ← Aeneas.Std.lift (Std.UScalar.cast_fromBool .U8 b5)
      let i20 ← i19 <<< (5#i32 : Std.I32)
      let i21 ← Aeneas.Std.lift (i17 ||| i20)
      let i22 ← i + 6#usize
      let b6 ← Aeneas.Std.Array.index_usize bv i22
      let i23 ← Aeneas.Std.lift (Std.UScalar.cast_fromBool .U8 b6)
      let i24 ← i23 <<< (6#i32 : Std.I32)
      let i25 ← Aeneas.Std.lift (i21 ||| i24)
      let i26 ← i + 7#usize
      let b7 ← Aeneas.Std.Array.index_usize bv i26
      let i27 ← Aeneas.Std.lift (Std.UScalar.cast_fromBool .U8 b7)
      let i28 ← i27 <<< (7#i32 : Std.I32)
      let i29 ← Aeneas.Std.lift (i25 ||| i28)
      RustM.ok (i29, bv)) = _
  rw [hi]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok bv i (by rw [hiv, hlen]; omega)]
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hj1]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok bv j1 (by rw [e1, hlen]; omega)]
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hz1]; simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hj2]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok bv j2 (by rw [e2, hlen]; omega)]
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hz2]; simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hj3]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok bv j3 (by rw [e3, hlen]; omega)]
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hz3]; simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hj4]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok bv j4 (by rw [e4, hlen]; omega)]
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hz4]; simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hj5]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok bv j5 (by rw [e5, hlen]; omega)]
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hz5]; simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hj6]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok bv j6 (by rw [e6, hlen]; omega)]
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hz6]; simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hj7]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok bv j7 (by rw [e7, hlen]; omega)]
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hz7]; simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hfinal]

/-- **Level 3, assembled at `N = 32`.** -/
private theorem bits_to_bytes_32_get (bv : Std.Array Bool 256#usize) :
    ∃ out : Std.Array Std.U8 32#usize,
      hacspec_ml_kem.serialize.bits_to_bytes (32#usize : Std.Usize)
          (N8 := 256#usize) bv = .ok out
      ∧ ∀ n : Nat, n < 32 →
          (out.val[n]!).val = bitSum (fun t => bv.val[8 * n + t]!) 8 := by
  have h32 : ((32#usize : Std.Usize)).val = 32 := by scalar_tac
  have h256 : ((256#usize : Std.Usize)).val = 256 := by scalar_tac
  have hmul : ((32#usize : Std.Usize) * (8#usize : Std.Usize) : RustM Std.Usize)
      = .ok (256#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq (T := Std.U8)
      (32#usize : Std.Usize)
      (hacspec_ml_kem.serialize.bits_to_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
        (32#usize : Std.Usize) (256#usize : Std.Usize)) bv
      (fun n => u8OfNat (bitSum (fun t => bv.val[8 * n + t]!) 8))
      (fun n hn => bits_to_bytes_closure_eq_gen bv n
        (by rw [h32] at hn; rw [h256]; omega)
        (by rw [h32] at hn; omega)
        (by rw [h32] at hn; scalar_tac))
  have key : hacspec_ml_kem.serialize.bits_to_bytes (32#usize : Std.Usize)
        (N8 := 256#usize) bv
      = CoreModels.core.array.from_fn (32#usize : Std.Usize)
          (hacspec_ml_kem.serialize.bits_to_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
            (32#usize : Std.Usize) (256#usize : Std.Usize)) bv := by
    unfold hacspec_ml_kem.serialize.bits_to_bytes
    -- hax v0.4.0-rc.1 no longer emits the `let i ← N * 8#usize; massert (N8 = i)` prelude
    -- (ALL 74 spec-side `massert`s are gone from the extraction), so the length check and
    -- its `hmul` witness are no longer part of this equation.
    simp only [hacspec_ml_kem.parameters.createi]
  rw [key, hfn]
  refine ⟨_, rfl, ?_⟩
  intro n hn
  rw [enc_mk_getElem (by rw [h32]; exact hn)]
  exact u8OfNat_val _ (by have := bitSum_lt (fun t => bv.val[8 * n + t]!) 8; simpa using this)

/-! #### Spec apex — the four levels assembled. -/

private theorem msg_enc_spec_eq
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ∃ out : Std.Array Std.U8 32#usize,
      hacspec_ml_kem.serialize.compress_then_serialize_message (lift_poly re) = .ok out
      ∧ ∀ n : Nat, n < 32 → (out.val[n]!).val = msgByte re n := by
  obtain ⟨a, ha, ha_get⟩ := compress_msg_get re
  obtain ⟨p_raw, hp_raw, hp_get⟩ := byte_encode_msg_raw_get re a ha_get
  obtain ⟨bv, hbv, hbv_get⟩ := bvfb_256_1_msg_get re p_raw hp_get
  obtain ⟨out, hout, hout_get⟩ := bits_to_bytes_32_get bv
  have e1 : ((32#usize : Std.Usize) * (1#usize : Std.Usize) : RustM Std.Usize)
      = .ok (32#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have e2 : ((256#usize : Std.Usize) * (1#usize : Std.Usize) : RustM Std.Usize)
      = .ok (256#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have hass : ((1#usize : Std.Usize) ≤ (12#usize : Std.Usize)) := by scalar_tac
  refine ⟨out, ?_, ?_⟩
  · unfold hacspec_ml_kem.serialize.compress_then_serialize_message
      hacspec_ml_kem.serialize.byte_encode
    simp only [ha, Aeneas.Std.bind_tc_ok, hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT,
      Aeneas.Std.massert, if_pos hass, if_true, e1, e2, hp_raw, hbv, hout]
  · intro n hn
    rw [hout_get n hn]
    unfold msgByte
    exact bitSum_congr _ _ 8 (fun t ht => hbv_get (8 * n + t) (by omega))

end L52Bank

/-- L5.2 — `serialize.compress_then_serialize_message`.

    The encode direction of L5.1: `Compress_1` each coefficient, pack 256 bits
    into 32 bytes. The impl writes into a caller-provided `serialized` slice and
    threads a `scratch` vector, returning both; the hacspec returns a fresh
    32-byte array. The post therefore constrains the RETURNED slice `p.1`, and
    requires it to have message length. `scratch` is workspace and is
    deliberately unconstrained.

    Stated after `L52Bank` so the two halves it assembles — `msg_enc_impl_fc` (the
    16-chunk `to_unsigned_field_modulus` / `compress_1` / `serialize_1` loop) and
    `msg_enc_spec_eq` (`Compress_1` then `ByteEncode_1`) — are already in scope. Both
    halves are stated against the SAME pure byte model `msgByte re`, so the apex is a
    `.val`-level equality and nothing bit-level survives into it. -/
@[spec]
theorem compress_then_serialize_message_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (serialized : Slice Std.U8)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_len : serialized.length = 32)
    -- ENCODE precondition, machine-falsified before adding: without it this statement is
    -- FALSE. `byte_encode` reads a canonicalised `FieldElement.val` while the impl's
    -- `to_unsigned_field_modulus` adds q AT MOST ONCE, so an unreduced lane diverges.
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
        ((re.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 3328) :
    -- Counterexample without h_bnd (evaluated on the extracted impl): lane 4162 ->
    -- impl bytes [0,0,0,0]; canon(4162)=833, Compress_1(833)=1 so spec byte0=1.
    -- Tight: 3328 agrees, 3329 already diverges. Mirrored at -4162.
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.compress_then_serialize_message
      (vectortraitsOperationsInst := portable_ops_inst)
      re serialized scratch
    ⦃ ⇓ p => ⌜ ∃ out : Std.Array Std.U8 32#usize,
                  hacspec_ml_kem.serialize.compress_then_serialize_message (lift_poly re)
                    = .ok out
                  ∧ p.1.length = 32
                  ∧ ∀ ℓ : Nat, ℓ < 32 → p.1.val[ℓ]! = out.val[ℓ]! ⌝ ⦄ := by
  -- Impl side: the 16-chunk loop writes `msgByte re` into all 32 bytes. `h_bnd` is
  -- consumed HERE and only here, inside `to_unsigned_fm_eq`.
  obtain ⟨p, hp_eq, hp⟩ :=
    triple_exists_ok_fc (msg_enc_impl_fc re h_bnd serialized scratch h_len)
  have himpl : p.1.val.length = 32 ∧ ∀ n : Nat, n < 2 * (16#usize : Std.Usize).val →
      (p.1.val[n]!).val = msgByte re n := by
    simp only [msgInv, Aeneas.Std.RustM.holds, pure, Pure.pure, Std.Do.Triple,
      Std.Do.WP.wp, Std.Do.PredTrans.apply, Std.Do.PostCond.noThrow,
      Std.Do.SPred.pure, Std.Do.SPred.entails] at hp
    exact hp trivial
  -- Spec side: `Compress_1` then `ByteEncode_1` reproduces exactly those bytes.
  obtain ⟨out, hout_eq, hout⟩ := msg_enc_spec_eq re
  refine triple_of_ok_fc hp_eq ⟨out, hout_eq, himpl.1, ?_⟩
  intro ℓ hℓ
  refine Aeneas.Std.UScalar.eq_of_val_eq ?_
  rw [himpl.2 ℓ (by scalar_tac), hout ℓ hℓ]


/-! ## PROVER bank for L5.3 — `deserialize_then_decompress_ring_element_v` at `dv ∈ {4,5}`.

    L5.3's statement is at the END of this file, after this bank, for the same reason
    L5.1/L5.2 are: it assembles material declared in `L57Bank2` (the spec-side
    `bytes_to_bits` / `bitvector_to_bounded_ints` / `byte_decode` ladder) and in `MEBank`
    (`decompress_d_gen_eq`, `decompress_ciphertext_coefficient_gen_fc`), both of which
    are declared further down than L5.3's original scaffold position, so the statement
    could not stay where the scaffold put it. Its text is byte-identical to the locked
    form; only its position moved.

    Both halves of the dispatcher are proved, and everything that CAN be generic in `d`
    is: the spec-side ladder is stated once in `d` and instantiated twice, and so is the
    per-chunk decompress step. What is NOT generic is the two impl seams
    (`deserialize_4_int` / `deserialize_5_int` are different straight-line programs) and
    the two `chunks_exact` loop bodies (different machine-generated names). -/

section L53Bank2

open Aeneas.Std
open libcrux_iot_ml_kem.Matrix.ComputeRingElementV.Impl

/-! ### Shared vocabulary — the `d`-bit window.

    `win l d j` is the `j`-th `d`-bit field of the byte list `l`, read as the spec reads
    it (a bit stream). It is to a general `d` what `dec12` is to `d = 12`, and M-C(1)
    (`bitSum_sliceBit_window`) is what turns it into the 3-byte read `decw` that the
    impl's byte arithmetic produces. -/

private def win (l : List Std.U8) (d j : Nat) : Nat :=
  bitSum (fun t => sliceBit l (d * j + t)) d

private theorem win_lt (l : List Std.U8) (d j : Nat) : win l d j < 2 ^ d :=
  bitSum_lt _ _

/-- CITES M-C(1) `bitSum_sliceBit_window`: the spec-side window IS the 3-byte read, at
    every `d ≤ 17`. This is the one place the group law is used, and because the law is
    generic it covers `d = 4`, `5`, `10` and `11` — every decode width in the tree — at
    once. (UPDATED 2026-08-20: it said "`d = 4` and `d = 5`", written before `LuBank`
    consumed it unchanged at 10 and 11. Understating a generic lemma's reach is how a
    later rung ends up re-deriving it.) -/
private theorem win_eq_decw (l : List Std.U8) (d j : Nat) (hd : d ≤ 17) :
    win l d j = decw l (d * j) d :=
  bitSum_sliceBit_window l (d * j) d hd

/-- Re-indexing a bit of a sub-list at byte offset `bo`. Generalises `sliceBit_chunk`
    (which is fixed at 2-byte chunks) off the chunk size. -/
private theorem sliceBit_at_offset (l c : List Std.U8) (bo len m : Nat)
    (hc : ∀ t : Nat, t < len → c[t]! = l[bo + t]!) (hm : m / 8 < len) :
    sliceBit c m = sliceBit l (8 * bo + m) := by
  unfold sliceBit
  rw [show (8 * bo + m) / 8 = bo + m / 8 by omega,
    show (8 * bo + m) % 8 = m % 8 by omega, hc (m / 8) hm]

/-- Re-indexing a whole window. `hq` says the sub-list starts on a `d`-bit lane
    boundary (`8 * bo = d * q`), which is true for every split this file makes —
    at `d ∈ {4,5}` (L5.3): `8·4 = 4·8`, `8·5 = 5·8`, `8·(8i) = 4·(16i)`, `8·(10i) = 5·(16i)`;
    at `d ∈ {10,11}` (`LuBank`): `8·10 = 10·8`, `8·11 = 11·8`, `8·(20i) = 10·(16i)`,
    `8·(22i) = 11·(16i)`. (The second line added 2026-08-20; the lemma was already generic,
    only the enumeration was stale.) -/
private theorem win_at_offset (l c : List Std.U8) (bo len d j q : Nat)
    (hc : ∀ t : Nat, t < len → c[t]! = l[bo + t]!)
    (hq : 8 * bo = d * q)
    (hlt : ∀ t : Nat, t < d → (d * j + t) / 8 < len) :
    win c d j = win l d (q + j) := by
  unfold win
  refine bitSum_congr _ _ d ?_
  intro t ht
  rw [sliceBit_at_offset l c bo len (d * j + t) hc (hlt t ht)]
  congr 1
  rw [hq]; ring

/-- The decompressed window is below `q`, so the closing `FieldElement.new` / `.as_i16()`
    are both total and the post's `natAbs ≤ 3328` is available. -/
private theorem win_dec_lt (w d : Nat) (hw : w < 2 ^ d) (hd : d < 12) :
    (2 * w * 3329 + 2 ^ d) / 2 ^ (d + 1) < 3329 := by
  have hle : (2:Nat) ^ d ≤ 2048 := by
    calc (2:Nat) ^ d ≤ 2 ^ 11 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 2048 := by norm_num
  refine Nat.div_lt_of_lt_mul ?_
  rw [show (2:Nat) ^ (d + 1) = 2 * 2 ^ d from by rw [pow_succ]; ring]
  omega

/-! ### Impl seam at `d = 4` — the PATTERN-TRANSFER target.

    No analogue of this exists anywhere in the tree; `deserialize_5_int_lanes_eq`
    (M-C(3)) is fixed at `d = 5`. The SHAPE is copied from it verbatim: name every
    `RustM` payload existentially, push each lane to a pure `Nat` expression in the
    four bytes, convert the spec side to `decw` with M-C(1) once, and close the eight
    identities by `omega`. At `d = 4` there are no straddling lanes (4 divides 8), so
    the `|||` half of the `d = 5` shape is absent — every lane is one mask, on either
    the byte or the byte shifted right by 4. -/

private theorem deserialize_4_int_lanes_eq (bytes : Slice Std.U8) (h_len : bytes.length = 4) :
    ∃ v0 v1 v2 v3 v4 v5 v6 v7 : Std.I16,
      libcrux_iot_ml_kem.vector.portable.serialize.deserialize_4_int bytes
          = .ok (v0, v1, v2, v3, v4, v5, v6, v7)
      ∧ ∀ k : Nat, k < 8 →
          (([v0, v1, v2, v3, v4, v5, v6, v7] : List Std.I16)[k]!).val
            = (win bytes.val 4 k : Int) := by
  have hlen : bytes.val.length = 4 := h_len
  have hb0 := u8_val_lt bytes.val 0
  have hb1 := u8_val_lt bytes.val 1
  have hb2 := u8_val_lt bytes.val 2
  have hb3 := u8_val_lt bytes.val 3
  -- the two zero-padded reads the `k = 6, 7` windows make past the end
  have hoob4 : (bytes.val[4]! : Std.U8).val = 0 := u8_oob _ _ (by omega)
  have hoob5 : (bytes.val[5]! : Std.U8).val = 0 := u8_oob _ _ (by omega)
  have hi0 : Slice.index_usize bytes 0#usize = .ok bytes.val[0]! :=
    slice_index_usize_eq bytes 0#usize (by simp [hlen])
  have hi1 : Slice.index_usize bytes 1#usize = .ok bytes.val[1]! :=
    slice_index_usize_eq bytes 1#usize (by simp [hlen])
  have hi2 : Slice.index_usize bytes 2#usize = .ok bytes.val[2]! :=
    slice_index_usize_eq bytes 2#usize (by simp [hlen])
  have hi3 : Slice.index_usize bytes 3#usize = .ok bytes.val[3]! :=
    slice_index_usize_eq bytes 3#usize (by simp [hlen])
  -- the four right shifts, one per odd lane
  obtain ⟨y0, hy0, hy0v⟩ := u8_shr_lit bytes.val[0]! 4#i32 4 (by simp) (by omega)
  obtain ⟨y1, hy1, hy1v⟩ := u8_shr_lit bytes.val[1]! 4#i32 4 (by simp) (by omega)
  obtain ⟨y2, hy2, hy2v⟩ := u8_shr_lit bytes.val[2]! 4#i32 4 (by simp) (by omega)
  obtain ⟨y3, hy3, hy3v⟩ := u8_shr_lit bytes.val[3]! 4#i32 4 (by simp) (by omega)
  refine ⟨c16 (bytes.val[0]! &&& 15#u8), c16 (y0 &&& 15#u8),
    c16 (bytes.val[1]! &&& 15#u8), c16 (y1 &&& 15#u8),
    c16 (bytes.val[2]! &&& 15#u8), c16 (y2 &&& 15#u8),
    c16 (bytes.val[3]! &&& 15#u8), c16 (y3 &&& 15#u8), ?_, ?_⟩
  · simp only [libcrux_iot_ml_kem.vector.portable.serialize.deserialize_4_int,
      hi0, hi1, hi2, hi3, hy0, hy1, hy2, hy3, as_i16_eq,
      Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  · intro k hk
    have n0 : (bytes.val[0]! &&& 15#u8).val = bytes.val[0]!.val % 2 ^ 4 :=
      u8_and_mask_val _ _ 4 rfl
    have n2 : (bytes.val[1]! &&& 15#u8).val = bytes.val[1]!.val % 2 ^ 4 :=
      u8_and_mask_val _ _ 4 rfl
    have n4 : (bytes.val[2]! &&& 15#u8).val = bytes.val[2]!.val % 2 ^ 4 :=
      u8_and_mask_val _ _ 4 rfl
    have n6 : (bytes.val[3]! &&& 15#u8).val = bytes.val[3]!.val % 2 ^ 4 :=
      u8_and_mask_val _ _ 4 rfl
    have n1 : (y0 &&& 15#u8).val = bytes.val[0]!.val / 2 ^ 4 % 2 ^ 4 := by
      rw [u8_and_mask_val _ _ 4 rfl, hy0v]
    have n3 : (y1 &&& 15#u8).val = bytes.val[1]!.val / 2 ^ 4 % 2 ^ 4 := by
      rw [u8_and_mask_val _ _ 4 rfl, hy1v]
    have n5 : (y2 &&& 15#u8).val = bytes.val[2]!.val / 2 ^ 4 % 2 ^ 4 := by
      rw [u8_and_mask_val _ _ 4 rfl, hy2v]
    have n7 : (y3 &&& 15#u8).val = bytes.val[3]!.val / 2 ^ 4 % 2 ^ 4 := by
      rw [u8_and_mask_val _ _ 4 rfl, hy3v]
    have key : ∀ v : Std.I16, v.val = (decw bytes.val (4 * k) 4 : Int) →
        v.val = (win bytes.val 4 k : Int) := by
      intro v h
      rw [win_eq_decw bytes.val 4 k (by omega)]
      exact h
    -- `decw` at the eight offsets. Kept SEPARATE from the `omega` steps: `norm_num`
    -- rewrites `l[i]!` to `l[i]?.getD default`, and inside an `omega` goal the byte
    -- atoms would stop matching the `hb*` / `hoob*` hypotheses.
    have d0 : decw bytes.val (4 * 0) 4
        = (bytes.val[0]!.val + 256 * bytes.val[1]!.val + 65536 * bytes.val[2]!.val)
            % 16 := by norm_num [decw]
    have d1 : decw bytes.val (4 * 1) 4
        = (bytes.val[0]!.val + 256 * bytes.val[1]!.val + 65536 * bytes.val[2]!.val)
            / 16 % 16 := by norm_num [decw]
    have d2 : decw bytes.val (4 * 2) 4
        = (bytes.val[1]!.val + 256 * bytes.val[2]!.val + 65536 * bytes.val[3]!.val)
            % 16 := by norm_num [decw]
    have d3 : decw bytes.val (4 * 3) 4
        = (bytes.val[1]!.val + 256 * bytes.val[2]!.val + 65536 * bytes.val[3]!.val)
            / 16 % 16 := by norm_num [decw]
    have d4 : decw bytes.val (4 * 4) 4
        = (bytes.val[2]!.val + 256 * bytes.val[3]!.val + 65536 * bytes.val[4]!.val)
            % 16 := by norm_num [decw]
    have d5 : decw bytes.val (4 * 5) 4
        = (bytes.val[2]!.val + 256 * bytes.val[3]!.val + 65536 * bytes.val[4]!.val)
            / 16 % 16 := by norm_num [decw]
    have d6 : decw bytes.val (4 * 6) 4
        = (bytes.val[3]!.val + 256 * bytes.val[4]!.val + 65536 * bytes.val[5]!.val)
            % 16 := by norm_num [decw]
    have d7 : decw bytes.val (4 * 7) 4
        = (bytes.val[3]!.val + 256 * bytes.val[4]!.val + 65536 * bytes.val[5]!.val)
            / 16 % 16 := by norm_num [decw]
    refine key _ ?_
    interval_cases k
    · show (c16 (bytes.val[0]! &&& 15#u8)).val = _
      rw [c16_val_nat, n0, d0]; omega
    · show (c16 (y0 &&& 15#u8)).val = _
      rw [c16_val_nat, n1, d1]; omega
    · show (c16 (bytes.val[1]! &&& 15#u8)).val = _
      rw [c16_val_nat, n2, d2]; omega
    · show (c16 (y1 &&& 15#u8)).val = _
      rw [c16_val_nat, n3, d3]; omega
    · show (c16 (bytes.val[2]! &&& 15#u8)).val = _
      rw [c16_val_nat, n4, d4]; omega
    · show (c16 (y2 &&& 15#u8)).val = _
      rw [c16_val_nat, n5, d5]; omega
    · show (c16 (bytes.val[3]! &&& 15#u8)).val = _
      rw [c16_val_nat, n6, d6]; omega
    · show (c16 (y3 &&& 15#u8)).val = _
      rw [c16_val_nat, n7, d7]; omega

/-! ### Impl side — one 16-lane chunk, at both `d`.

    `deserialize_4` / `deserialize_5` are the same program modulo the `_int` seam and
    the half-chunk width: sub-slice the low half, eight `Array.update`s, sub-slice the
    high half, eight more. The 16 writes are factored into `put16` so the lane read-back
    is one lemma rather than two 16-case walks. -/

/-- The 16-lane write chain both `deserialize_d` functions perform. -/
private def put16 (E : Std.Array Std.I16 16#usize)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Std.I16) :
    Std.Array Std.I16 16#usize :=
  (((((((((((((((E.set 0#usize v0).set 1#usize v1).set 2#usize v2).set 3#usize v3).set 4#usize v4).set 5#usize v5).set 6#usize v6).set 7#usize v7).set 8#usize v8).set 9#usize v9).set 10#usize v10).set 11#usize v11).set 12#usize v12).set 13#usize v13).set 14#usize v14).set 15#usize v15

private theorem put16_get (E : Std.Array Std.I16 16#usize)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Std.I16)
    (k : Nat) (hk : k < 16) :
    ((put16 E v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).val)[k]!
      = ([v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
          : List Std.I16)[k]! := by
  unfold put16
  exact set16_get E v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 k hk

private theorem deserialize_4_eq (bytes : Slice Std.U8) (h_len : bytes.val.length = 8)
    (out : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ∃ v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector,
      libcrux_iot_ml_kem.vector.portable.serialize.deserialize_4 bytes out = .ok v
      ∧ ∀ k : Nat, k < 16 → (v.elements.val[k]!).val = (win bytes.val 4 k : Int) := by
  obtain ⟨s0, hs0, hs0len, hs0get⟩ :=
    slice_index_range_strict bytes 0#usize 4#usize (by scalar_tac) (by rw [h_len]; scalar_tac)
  obtain ⟨s1, hs1, hs1len, hs1get⟩ :=
    slice_index_range_strict bytes 4#usize 8#usize (by scalar_tac) (by rw [h_len]; scalar_tac)
  have hs0len' : s0.val.length = 4 := by rw [hs0len]; scalar_tac
  have hs1len' : s1.val.length = 4 := by rw [hs1len]; scalar_tac
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, hlo, hlow⟩ := deserialize_4_int_lanes_eq s0 hs0len'
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hhi, hhiw⟩ := deserialize_4_int_lanes_eq s1 hs1len'
  -- the two halves sit at byte offsets 0 and 4, i.e. lane offsets 0 and 8
  have hlow' : ∀ k : Nat, k < 8 →
      (([a0, a1, a2, a3, a4, a5, a6, a7] : List Std.I16)[k]!).val
        = (win bytes.val 4 k : Int) := by
    intro k hk
    rw [hlow k hk, win_at_offset bytes.val s0.val 0 4 4 k 0
      (fun t ht => by simpa using hs0get t (by scalar_tac))
      (by omega) (fun t ht => by omega), Nat.zero_add]
  have hhiw' : ∀ k : Nat, k < 8 →
      (([b0, b1, b2, b3, b4, b5, b6, b7] : List Std.I16)[k]!).val
        = (win bytes.val 4 (8 + k) : Int) := by
    intro k hk
    rw [hhiw k hk, win_at_offset bytes.val s1.val 4 4 4 k 8
      (fun t ht => by simpa using hs1get t (by scalar_tac))
      (by omega) (fun t ht => by omega)]
  have hu := fun (i : Std.Usize) (hi : i.val < 16) =>
    fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) => array_update16 A i x hi
  refine ⟨{ elements := put16 out.elements a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 },
    ?_, ?_⟩
  · unfold libcrux_iot_ml_kem.vector.portable.serialize.deserialize_4 put16
    simp only [hs0, hs1, hlo, hhi, Aeneas.Std.bind_tc_ok,
      hu 0#usize (by scalar_tac), hu 1#usize (by scalar_tac), hu 2#usize (by scalar_tac),
      hu 3#usize (by scalar_tac), hu 4#usize (by scalar_tac), hu 5#usize (by scalar_tac),
      hu 6#usize (by scalar_tac), hu 7#usize (by scalar_tac), hu 8#usize (by scalar_tac),
      hu 9#usize (by scalar_tac), hu 10#usize (by scalar_tac), hu 11#usize (by scalar_tac),
      hu 12#usize (by scalar_tac), hu 13#usize (by scalar_tac), hu 14#usize (by scalar_tac),
      hu 15#usize (by scalar_tac)]
    rfl
  · intro k hk
    show ((put16 out.elements a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7).val)[k]!.val = _
    rw [put16_get (k := k) (hk := hk)]
    interval_cases k
    · exact hlow' 0 (by omega)
    · exact hlow' 1 (by omega)
    · exact hlow' 2 (by omega)
    · exact hlow' 3 (by omega)
    · exact hlow' 4 (by omega)
    · exact hlow' 5 (by omega)
    · exact hlow' 6 (by omega)
    · exact hlow' 7 (by omega)
    · exact hhiw' 0 (by omega)
    · exact hhiw' 1 (by omega)
    · exact hhiw' 2 (by omega)
    · exact hhiw' 3 (by omega)
    · exact hhiw' 4 (by omega)
    · exact hhiw' 5 (by omega)
    · exact hhiw' 6 (by omega)
    · exact hhiw' 7 (by omega)

/-- The `d = 5` companion. CITES the exemplar `deserialize_5_int_lanes_eq` at exactly its
    instance for both halves; the only work here is the two sub-slices, the 16 writes and
    the lane re-indexing. -/
private theorem deserialize_5_eq (bytes : Slice Std.U8) (h_len : bytes.val.length = 10)
    (out : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ∃ v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector,
      libcrux_iot_ml_kem.vector.portable.serialize.deserialize_5 bytes out = .ok v
      ∧ ∀ k : Nat, k < 16 → (v.elements.val[k]!).val = (win bytes.val 5 k : Int) := by
  obtain ⟨s0, hs0, hs0len, hs0get⟩ :=
    slice_index_range_strict bytes 0#usize 5#usize (by scalar_tac) (by rw [h_len]; scalar_tac)
  obtain ⟨s1, hs1, hs1len, hs1get⟩ :=
    slice_index_range_strict bytes 5#usize 10#usize (by scalar_tac) (by rw [h_len]; scalar_tac)
  have hs0len' : s0.val.length = 5 := by rw [hs0len]; scalar_tac
  have hs1len' : s1.val.length = 5 := by rw [hs1len]; scalar_tac
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, hlo, hlow⟩ := deserialize_5_int_lanes_eq s0 hs0len'
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hhi, hhiw⟩ := deserialize_5_int_lanes_eq s1 hs1len'
  have hlow' : ∀ k : Nat, k < 8 →
      (([a0, a1, a2, a3, a4, a5, a6, a7] : List Std.I16)[k]!).val
        = (win bytes.val 5 k : Int) := by
    intro k hk
    rw [(hlow k hk).1]
    show ((win s0.val 5 k : Nat) : Int) = _
    rw [win_at_offset bytes.val s0.val 0 5 5 k 0
      (fun t ht => by simpa using hs0get t (by scalar_tac))
      (by omega) (fun t ht => by omega), Nat.zero_add]
  have hhiw' : ∀ k : Nat, k < 8 →
      (([b0, b1, b2, b3, b4, b5, b6, b7] : List Std.I16)[k]!).val
        = (win bytes.val 5 (8 + k) : Int) := by
    intro k hk
    rw [(hhiw k hk).1]
    show ((win s1.val 5 k : Nat) : Int) = _
    rw [win_at_offset bytes.val s1.val 5 5 5 k 8
      (fun t ht => by simpa using hs1get t (by scalar_tac))
      (by omega) (fun t ht => by omega)]
  have hu := fun (i : Std.Usize) (hi : i.val < 16) =>
    fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) => array_update16 A i x hi
  refine ⟨{ elements := put16 out.elements a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 },
    ?_, ?_⟩
  · unfold libcrux_iot_ml_kem.vector.portable.serialize.deserialize_5 put16
    simp only [hs0, hs1, hlo, hhi, Aeneas.Std.bind_tc_ok,
      hu 0#usize (by scalar_tac), hu 1#usize (by scalar_tac), hu 2#usize (by scalar_tac),
      hu 3#usize (by scalar_tac), hu 4#usize (by scalar_tac), hu 5#usize (by scalar_tac),
      hu 6#usize (by scalar_tac), hu 7#usize (by scalar_tac), hu 8#usize (by scalar_tac),
      hu 9#usize (by scalar_tac), hu 10#usize (by scalar_tac), hu 11#usize (by scalar_tac),
      hu 12#usize (by scalar_tac), hu 13#usize (by scalar_tac), hu 14#usize (by scalar_tac),
      hu 15#usize (by scalar_tac)]
    rfl
  · intro k hk
    show ((put16 out.elements a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7).val)[k]!.val = _
    rw [put16_get (k := k) (hk := hk)]
    interval_cases k
    · exact hlow' 0 (by omega)
    · exact hlow' 1 (by omega)
    · exact hlow' 2 (by omega)
    · exact hlow' 3 (by omega)
    · exact hlow' 4 (by omega)
    · exact hlow' 5 (by omega)
    · exact hlow' 6 (by omega)
    · exact hlow' 7 (by omega)
    · exact hhiw' 0 (by omega)
    · exact hhiw' 1 (by omega)
    · exact hhiw' 2 (by omega)
    · exact hhiw' 3 (by omega)
    · exact hhiw' 4 (by omega)
    · exact hhiw' 5 (by omega)
    · exact hhiw' 6 (by omega)
    · exact hhiw' 7 (by omega)

/-! ### Impl side — the per-chunk decompress step, generic in `d`.

    CITES M-E(2) `decompress_ciphertext_coefficient_gen_fc` at both instances; the only
    work here is moving between the `Int`/`Nat` views of a lane that the citation's
    `hlane` guard makes non-negative. `win_lt` is what discharges that guard, and it is
    the reason the impl seams above are stated as an equality to `win` rather than to a
    raw byte expression. -/

private theorem chunk_decompress_ok (l : List Std.U8) (dN : Nat) (hd : dN < 12)
    (dI : Std.I32) (hdI : dI.val = (dN : Int)) (i : Nat)
    (t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hlane : ∀ ℓ : Nat, ℓ < 16 → (t.elements.val[ℓ]!).val = (win l dN (16 * i + ℓ) : Int)) :
    ∃ w : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector,
      libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient dI t = .ok w
      ∧ ∀ ℓ : Nat, ℓ < 16 →
          (w.elements.val[ℓ]!).val
            = (((2 * win l dN (16 * i + ℓ) * 3329 + 2 ^ dN) / 2 ^ (dN + 1) : Nat) : Int) := by
  have hdt : dI.val.toNat = dN := by rw [hdI]; exact Int.toNat_natCast dN
  have hlane' : ∀ j : Nat, j < 16 →
      0 ≤ (t.elements.val[j]!).val ∧ (t.elements.val[j]!).val < 2 ^ dI.val.toNat := by
    intro j hj
    rw [hlane j hj, hdt]
    refine ⟨Int.natCast_nonneg _, ?_⟩
    have h := win_lt l dN (16 * i + j)
    exact_mod_cast h
  obtain ⟨w, hw, hpost⟩ := triple_exists_ok_fc
    (decompress_ciphertext_coefficient_gen_fc dI t
      (by rw [hdI]; exact Int.natCast_nonneg _) (by rw [hdI]; exact_mod_cast hd) hlane')
  refine ⟨w, hw, ?_⟩
  intro ℓ hℓ
  obtain ⟨heq, hnn, _hlt⟩ := hpost ℓ hℓ
  rw [hdt, hlane ℓ hℓ, Int.toNat_natCast] at heq
  rw [← Int.toNat_of_nonneg hnn, heq]

/-! ### Impl side — the two `chunks_exact` loops.

    CITES the K1 exemplar `loop_chunks_exact_pk_spec`: the suffix relation it threads is
    exactly what ties each chunk's bytes back to `serialized`, which is what the window
    re-indexing needs. Body walk, both `d`: read `re.coefficients[i]`, `deserialize_d`
    into it, read it back, `decompress_ciphertext_coefficient d` into it. Two writes to
    the SAME cell per iteration, so the read-back is two `array_set_get16`s.

    The two loops are separate proofs because the machine-generated body names differ;
    everything they say is shared, through `dcplane`, `deserialize_d_eq` and
    `chunk_decompress_ok`. -/

/-- Loop invariant: the first `k` chunks of `re` carry the DECOMPRESSED windows. -/
private def dcplane (l : List Std.U8) (d : Nat)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (k : Nat) : Prop :=
  ∀ i : Nat, i < k → ∀ ℓ : Nat, ℓ < 16 →
    ((re.coefficients.val[i]!).elements.val[ℓ]!).val
      = (((2 * win l d (16 * i + ℓ) * 3329 + 2 ^ d) / 2 ^ (d + 1) : Nat) : Int)

-- NB: the trait-instance projections (`portable_ops_inst.deserialize_d`,
-- `.decompress_ciphertext_coefficient`) are DEFEQ to the plain `vector.portable.*`
-- functions — `classify_ref` is the identity — so the body walks below name the plain
-- functions in their `show`s and no bridging lemma is needed.

private theorem L53_loop_4_fc
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 128)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_4_loop
      (vectortraitsOperationsInst := portable_ops_inst)
      { iter := { cs := 8#usize, elements := serialized }, count := 0#usize } re
    ⦃ ⇓ p => ⌜ (Aeneas.Std.RustM.ok (dcplane serialized.val 4 p 16)).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_4_loop
  refine loop_chunks_exact_pk_spec _ re serialized 8#usize 16
    (fun k acc => .ok (dcplane serialized.val 4 acc k)) (by scalar_tac)
    (by simpa [Aeneas.Std.Slice.length] using h_len)
    ((holds_ok _).mpr (by intro i hi; omega)) ?_
  intro acc k rest cnt hk hcnt hrest hsuf hinv
  have hinv' : dcplane serialized.val 4 acc k := (holds_ok _).mp hinv
  have h8 : ((8#usize : Std.Usize).val) = 8 := by scalar_tac
  rw [h8] at hrest
  simp only [h8] at hsuf
  by_cases hlt : k < 16
  · have hrest8 : 8 ≤ rest.length := by
      rw [hrest]
      have h1 : 1 ≤ 16 - k := by omega
      calc (8:Nat) = 1 * 8 := by ring
      _ ≤ (16 - k) * 8 := Nat.mul_le_mul_right 8 h1
    obtain ⟨chunk, drop, cnt', hnext, hcnt', hclen, hdlen, hcget, hdget⟩ :=
      enumerate_chunks_next_cont_drop rest 8#usize cnt
        (by rw [h8]; simpa [Aeneas.Std.Slice.length] using hrest8) (by scalar_tac)
    have hcnt16 : cnt.val < 16 := by omega
    have hlen1 : cnt.val < acc.coefficients.val.length := by
      have hc : acc.coefficients.val.length = 16 := by
        have := acc.coefficients.property; simpa using this
      omega
    have hchunk_len : chunk.val.length = 8 := by
      simpa [Aeneas.Std.Slice.length] using hclen
    -- the chunk sits at byte offset `8*k` of `serialized`
    have hcser : ∀ m : Nat, m < 8 → chunk.val[m]! = serialized.val[8 * k + m]! := by
      intro m hm
      rw [hcget m (by rw [h8]; omega), hsuf m]
      congr 1; omega
    have hwin : ∀ ℓ : Nat, ℓ < 16 →
        win chunk.val 4 ℓ = win serialized.val 4 (16 * k + ℓ) := by
      intro ℓ hℓ
      exact win_at_offset serialized.val chunk.val (8 * k) 8 4 ℓ (16 * k)
        (fun t ht => hcser t ht) (by ring) (fun t ht => by omega)
    obtain ⟨v, hv_eq, hv⟩ :=
      deserialize_4_eq chunk hchunk_len (acc.coefficients.val[cnt.val]'hlen1)
    have hvwin : ∀ ℓ : Nat, ℓ < 16 →
        (v.elements.val[ℓ]!).val = (win serialized.val 4 (16 * k + ℓ) : Int) := by
      intro ℓ hℓ
      rw [hv ℓ hℓ, hwin ℓ hℓ]
    obtain ⟨w, hw_eq, hw⟩ :=
      chunk_decompress_ok serialized.val 4 (by omega) 4#i32 (by scalar_tac) k v hvwin
    have hlen2 : cnt.val < (Std.Array.set acc.coefficients cnt v).val.length := by
      have hc : (Std.Array.set acc.coefficients cnt v).val.length = 16 := by
        have := (Std.Array.set acc.coefficients cnt v).property; simpa using this
      omega
    have hgi : (Std.Array.set acc.coefficients cnt v).val[cnt.val]!
        = (Std.Array.set acc.coefficients cnt v).val[cnt.val]'hlen2 :=
      getElem!_pos (Std.Array.set acc.coefficients cnt v).val cnt.val hlen2
    have hself : (Std.Array.set acc.coefficients cnt v).val[cnt.val]'hlen2 = v := by
      rw [← hgi, array_set_get16 acc.coefficients cnt v cnt.val hcnt16 hcnt16, if_pos rfl]
    refine triple_of_ok_fc
      (v := .cont ({ iter := { cs := 8#usize, elements := drop }, count := cnt' },
                   { coefficients :=
                       Std.Array.set (Std.Array.set acc.coefficients cnt v) cnt w })) ?_ ?_
    · show libcrux_iot_ml_kem.serialize.deserialize_then_decompress_4_loop.body
        portable_ops_inst { iter := { cs := 8#usize, elements := rest }, count := cnt } acc = _
      unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_4_loop.body
      rw [show (CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
            (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice Std.U8)
            { iter := { cs := 8#usize, elements := rest }, count := cnt })
          = .ok (CoreModels.core.option.Option.Some (cnt, chunk),
                 { iter := { cs := 8#usize, elements := drop }, count := cnt' }) from hnext]
      -- the ONE place this proof spells out the machine-generated body (skill §4.1): the
      -- `show` is what iota-reduces the `Option`/pair matches the extraction leaves behind.
      show (do
          let (t, back) ← Aeneas.Std.Array.index_mut_usize acc.coefficients cnt
          let t1 ← libcrux_iot_ml_kem.vector.portable.serialize.deserialize_4 chunk t
          let (t2, back1) ← Aeneas.Std.Array.index_mut_usize (back t1) cnt
          let t3 ← libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
            4#i32 t2
          RustM.ok (ControlFlow.cont
            (({ iter := { cs := 8#usize, elements := drop }, count := cnt' } : EnumCE),
             ({ coefficients := back1 t3 } :
               libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                 libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)))) = _
      rw [array_index_mut16 acc.coefficients cnt hlen1]
      simp only [Aeneas.Std.bind_tc_ok]
      show (do
          let t1 ← libcrux_iot_ml_kem.vector.portable.serialize.deserialize_4 chunk
            (acc.coefficients.val[cnt.val]'hlen1)
          let (t2, back1) ← Aeneas.Std.Array.index_mut_usize
            (Std.Array.set acc.coefficients cnt t1) cnt
          let t3 ← libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
            4#i32 t2
          RustM.ok (ControlFlow.cont
            (({ iter := { cs := 8#usize, elements := drop }, count := cnt' } : EnumCE),
             ({ coefficients := back1 t3 } :
               libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                 libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)))) = _
      rw [hv_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [array_index_mut16 (Std.Array.set acc.coefficients cnt v) cnt hlen2]
      simp only [Aeneas.Std.bind_tc_ok]
      show (do
          let t3 ← libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
            4#i32 ((Std.Array.set acc.coefficients cnt v).val[cnt.val]'hlen2)
          RustM.ok (ControlFlow.cont
            (({ iter := { cs := 8#usize, elements := drop }, count := cnt' } : EnumCE),
             ({ coefficients :=
                 Std.Array.set (Std.Array.set acc.coefficients cnt v) cnt t3 } :
               libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                 libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)))) = _
      rw [hself, hw_eq]
      rfl
    · refine ⟨hlt, rfl, (by show cnt'.val = k + 1; rw [hcnt', hcnt]), ?_, ?_, ?_⟩
      · show drop.length = (16 - (k + 1)) * (8#usize : Std.Usize).val
        rw [h8, hdlen, hrest]
        have h : (16 - k) = (16 - (k + 1)) + 1 := by omega
        rw [h]; ring_nf; omega
      · intro ℓ
        simp only [h8]
        rw [hdget ℓ]
        simp only [h8]
        rw [hsuf (8 + ℓ)]
        congr 1 <;> omega
      · refine (holds_ok _).mpr ?_
        intro i hi ℓ hℓ
        show ((Std.Array.set (Std.Array.set acc.coefficients cnt v) cnt w).val[i]!).elements.val[ℓ]!.val
          = _
        by_cases hik : i = k
        · subst hik
          rw [array_set_get16 _ _ _ _ (by omega) (by omega), if_pos (by omega)]
          exact hw ℓ hℓ
        · rw [array_set_get16 _ _ _ _ (by omega) (by omega), if_neg (by omega),
            array_set_get16 _ _ _ _ (by omega) (by omega), if_neg (by omega)]
          exact hinv' i (by omega) ℓ hℓ
  · have hk16 : k = 16 := by omega
    subst hk16
    have hrest0 : rest.length = 0 := by simp [hrest]
    refine triple_of_ok_fc (v := .done acc) ?_ ?_
    · show libcrux_iot_ml_kem.serialize.deserialize_then_decompress_4_loop.body
        portable_ops_inst { iter := { cs := 8#usize, elements := rest }, count := cnt } acc = _
      unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_4_loop.body
      rw [show (CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
            (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice Std.U8)
            { iter := { cs := 8#usize, elements := rest }, count := cnt })
          = .ok (CoreModels.core.option.Option.None,
                 { iter := { cs := 8#usize, elements := rest }, count := cnt }) from
          enumerate_chunks_next_done rest 8#usize cnt (by rw [h8, hrest0]; omega)]
      rfl
    · exact (holds_ok _).mpr hinv'

private theorem L53_loop_5_fc
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 160)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_5_loop
      (vectortraitsOperationsInst := portable_ops_inst)
      { iter := { cs := 10#usize, elements := serialized }, count := 0#usize } re
    ⦃ ⇓ p => ⌜ (Aeneas.Std.RustM.ok (dcplane serialized.val 5 p 16)).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_5_loop
  refine loop_chunks_exact_pk_spec _ re serialized 10#usize 16
    (fun k acc => .ok (dcplane serialized.val 5 acc k)) (by scalar_tac)
    (by simpa [Aeneas.Std.Slice.length] using h_len)
    ((holds_ok _).mpr (by intro i hi; omega)) ?_
  intro acc k rest cnt hk hcnt hrest hsuf hinv
  have hinv' : dcplane serialized.val 5 acc k := (holds_ok _).mp hinv
  have h10 : ((10#usize : Std.Usize).val) = 10 := by scalar_tac
  rw [h10] at hrest
  simp only [h10] at hsuf
  by_cases hlt : k < 16
  · have hrest10 : 10 ≤ rest.length := by
      rw [hrest]
      have h1 : 1 ≤ 16 - k := by omega
      calc (10:Nat) = 1 * 10 := by ring
      _ ≤ (16 - k) * 10 := Nat.mul_le_mul_right 10 h1
    obtain ⟨chunk, drop, cnt', hnext, hcnt', hclen, hdlen, hcget, hdget⟩ :=
      enumerate_chunks_next_cont_drop rest 10#usize cnt
        (by rw [h10]; simpa [Aeneas.Std.Slice.length] using hrest10) (by scalar_tac)
    have hcnt16 : cnt.val < 16 := by omega
    have hlen1 : cnt.val < acc.coefficients.val.length := by
      have hc : acc.coefficients.val.length = 16 := by
        have := acc.coefficients.property; simpa using this
      omega
    have hchunk_len : chunk.val.length = 10 := by
      simpa [Aeneas.Std.Slice.length] using hclen
    have hcser : ∀ m : Nat, m < 10 → chunk.val[m]! = serialized.val[10 * k + m]! := by
      intro m hm
      rw [hcget m (by rw [h10]; omega), hsuf m]
      congr 1; omega
    have hwin : ∀ ℓ : Nat, ℓ < 16 →
        win chunk.val 5 ℓ = win serialized.val 5 (16 * k + ℓ) := by
      intro ℓ hℓ
      exact win_at_offset serialized.val chunk.val (10 * k) 10 5 ℓ (16 * k)
        (fun t ht => hcser t ht) (by ring) (fun t ht => by omega)
    obtain ⟨v, hv_eq, hv⟩ :=
      deserialize_5_eq chunk hchunk_len (acc.coefficients.val[cnt.val]'hlen1)
    have hvwin : ∀ ℓ : Nat, ℓ < 16 →
        (v.elements.val[ℓ]!).val = (win serialized.val 5 (16 * k + ℓ) : Int) := by
      intro ℓ hℓ
      rw [hv ℓ hℓ, hwin ℓ hℓ]
    obtain ⟨w, hw_eq, hw⟩ :=
      chunk_decompress_ok serialized.val 5 (by omega) 5#i32 (by scalar_tac) k v hvwin
    have hlen2 : cnt.val < (Std.Array.set acc.coefficients cnt v).val.length := by
      have hc : (Std.Array.set acc.coefficients cnt v).val.length = 16 := by
        have := (Std.Array.set acc.coefficients cnt v).property; simpa using this
      omega
    have hgi : (Std.Array.set acc.coefficients cnt v).val[cnt.val]!
        = (Std.Array.set acc.coefficients cnt v).val[cnt.val]'hlen2 :=
      getElem!_pos (Std.Array.set acc.coefficients cnt v).val cnt.val hlen2
    have hself : (Std.Array.set acc.coefficients cnt v).val[cnt.val]'hlen2 = v := by
      rw [← hgi, array_set_get16 acc.coefficients cnt v cnt.val hcnt16 hcnt16, if_pos rfl]
    refine triple_of_ok_fc
      (v := .cont ({ iter := { cs := 10#usize, elements := drop }, count := cnt' },
                   { coefficients :=
                       Std.Array.set (Std.Array.set acc.coefficients cnt v) cnt w })) ?_ ?_
    · show libcrux_iot_ml_kem.serialize.deserialize_then_decompress_5_loop.body
        portable_ops_inst { iter := { cs := 10#usize, elements := rest }, count := cnt } acc = _
      unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_5_loop.body
      rw [show (CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
            (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice Std.U8)
            { iter := { cs := 10#usize, elements := rest }, count := cnt })
          = .ok (CoreModels.core.option.Option.Some (cnt, chunk),
                 { iter := { cs := 10#usize, elements := drop }, count := cnt' }) from hnext]
      show (do
          let (t, back) ← Aeneas.Std.Array.index_mut_usize acc.coefficients cnt
          let t1 ← libcrux_iot_ml_kem.vector.portable.serialize.deserialize_5 chunk t
          let (t2, back1) ← Aeneas.Std.Array.index_mut_usize (back t1) cnt
          let t3 ← libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
            5#i32 t2
          RustM.ok (ControlFlow.cont
            (({ iter := { cs := 10#usize, elements := drop }, count := cnt' } : EnumCE),
             ({ coefficients := back1 t3 } :
               libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                 libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)))) = _
      rw [array_index_mut16 acc.coefficients cnt hlen1]
      simp only [Aeneas.Std.bind_tc_ok]
      show (do
          let t1 ← libcrux_iot_ml_kem.vector.portable.serialize.deserialize_5 chunk
            (acc.coefficients.val[cnt.val]'hlen1)
          let (t2, back1) ← Aeneas.Std.Array.index_mut_usize
            (Std.Array.set acc.coefficients cnt t1) cnt
          let t3 ← libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
            5#i32 t2
          RustM.ok (ControlFlow.cont
            (({ iter := { cs := 10#usize, elements := drop }, count := cnt' } : EnumCE),
             ({ coefficients := back1 t3 } :
               libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                 libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)))) = _
      rw [hv_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [array_index_mut16 (Std.Array.set acc.coefficients cnt v) cnt hlen2]
      simp only [Aeneas.Std.bind_tc_ok]
      show (do
          let t3 ← libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
            5#i32 ((Std.Array.set acc.coefficients cnt v).val[cnt.val]'hlen2)
          RustM.ok (ControlFlow.cont
            (({ iter := { cs := 10#usize, elements := drop }, count := cnt' } : EnumCE),
             ({ coefficients :=
                 Std.Array.set (Std.Array.set acc.coefficients cnt v) cnt t3 } :
               libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                 libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)))) = _
      rw [hself, hw_eq]
      rfl
    · refine ⟨hlt, rfl, (by show cnt'.val = k + 1; rw [hcnt', hcnt]), ?_, ?_, ?_⟩
      · show drop.length = (16 - (k + 1)) * (10#usize : Std.Usize).val
        rw [h10, hdlen, hrest]
        have h : (16 - k) = (16 - (k + 1)) + 1 := by omega
        rw [h]; ring_nf; omega
      · intro ℓ
        simp only [h10]
        rw [hdget ℓ]
        simp only [h10]
        rw [hsuf (10 + ℓ)]
        congr 1 <;> omega
      · refine (holds_ok _).mpr ?_
        intro i hi ℓ hℓ
        show ((Std.Array.set (Std.Array.set acc.coefficients cnt v) cnt w).val[i]!).elements.val[ℓ]!.val
          = _
        by_cases hik : i = k
        · subst hik
          rw [array_set_get16 _ _ _ _ (by omega) (by omega), if_pos (by omega)]
          exact hw ℓ hℓ
        · rw [array_set_get16 _ _ _ _ (by omega) (by omega), if_neg (by omega),
            array_set_get16 _ _ _ _ (by omega) (by omega), if_neg (by omega)]
          exact hinv' i (by omega) ℓ hℓ
  · have hk16 : k = 16 := by omega
    subst hk16
    have hrest0 : rest.length = 0 := by simp [hrest]
    refine triple_of_ok_fc (v := .done acc) ?_ ?_
    · show libcrux_iot_ml_kem.serialize.deserialize_then_decompress_5_loop.body
        portable_ops_inst { iter := { cs := 10#usize, elements := rest }, count := cnt } acc = _
      unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_5_loop.body
      rw [show (CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
            (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice Std.U8)
            { iter := { cs := 10#usize, elements := rest }, count := cnt })
          = .ok (CoreModels.core.option.Option.None,
                 { iter := { cs := 10#usize, elements := rest }, count := cnt }) from
          enumerate_chunks_next_done rest 10#usize cnt (by rw [h10, hrest0]; omega)]
      rfl
    · exact (holds_ok _).mpr hinv'

/-- Impl apex at `d = 4`: `chunks_exact 8` + `enumerate` is the initial loop state. -/
private theorem L53_impl_4_fc
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 128)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_4
      (vectortraitsOperationsInst := portable_ops_inst) serialized re
    ⦃ ⇓ p => ⌜ (Aeneas.Std.RustM.ok (dcplane serialized.val 4 p 16)).holds ⌝ ⦄ := by
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
  exact L53_loop_4_fc serialized h_len re

/-- Impl apex at `d = 5`. -/
private theorem L53_impl_5_fc
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 160)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_5
      (vectortraitsOperationsInst := portable_ops_inst) serialized re
    ⦃ ⇓ p => ⌜ (Aeneas.Std.RustM.ok (dcplane serialized.val 5 p 16)).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_5
  rw [show (CoreModels.core.slice.Slice.chunks_exact serialized (10#usize : Std.Usize))
        = .ok { cs := 10#usize, elements := serialized } from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show (CoreModels.core.iter.traits.iterator.Iterator.enumerate.default
        (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice
          Std.U8)
        { cs := (10#usize : Std.Usize), elements := serialized })
      = .ok ({ iter := { cs := 10#usize, elements := serialized }, count := 0#usize } : EnumCE)
      from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  exact L53_loop_5_fc serialized h_len re

/-! ### Spec side, stated ONCE in `d`.

    The tree's decode ladder is fixed at `d = 12` (`bytes_to_bits_get`, `bvb_256_12_get`,
    `byte_decode_generic_12_get`, `byte_decode_12_eq`) and at `d = 1` (the 32-byte
    message variants). L5.3 needs it at TWO more widths, so it is generalised here off
    the array sizes rather than instantiated twice: the four lemmas below are the `d = 12`
    proofs with `384`/`3072`/`12` replaced by `N`/`Nb`/`d` and the size arithmetic supplied
    as hypotheses. Only `byte_decode_dyn`'s `match d.val` dispatch stays per-`d`. -/

private theorem bytes_to_bits_closure_gen {N Nb : Std.Usize} (a : Std.Array Std.U8 N)
    (hNb : Nb.val = 8 * N.val) (k : Nat) (hk : k < Nb.val) :
    (hacspec_ml_kem.serialize.bytes_to_bits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBool
        N Nb).call_mut a ⟨BitVec.ofNat _ k⟩
      = .ok (sliceBit a.val k, a) := by
  have hNbmax : Nb.val ≤ Std.Usize.max := by scalar_tac
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
    have ha : a.val.length = N.val := a.property
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
      RustM.ok (decide (i4 = 1#u8), a)) = _
  rw [hq_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hidx]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hy_eq]; simp only [Aeneas.Std.bind_tc_ok]
  show RustM.ok (decide (y &&& 1#u8 = 1#u8), a) = _
  rw [hy]
  unfold sliceBit
  rw [hq16, hr8]

private theorem bytes_to_bits_gen {N Nb : Std.Usize} (a : Std.Array Std.U8 N)
    (hNb : Nb.val = 8 * N.val) :
    ∃ bv : Std.Array Bool Nb,
      hacspec_ml_kem.serialize.bytes_to_bits (N := N) Nb a = .ok bv
      ∧ ∀ m : Nat, m < Nb.val → bv.val[m]! = sliceBit a.val m := by
  have hmul : ((N : Std.Usize) * (8#usize : Std.Usize) : RustM Std.Usize) = .ok Nb :=
    usize_mul_lit _ _ _ (by rw [hNb]; scalar_tac) (by scalar_tac)
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq (T := Bool) Nb
      (hacspec_ml_kem.serialize.bytes_to_bits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBool
        N Nb) a (fun m => sliceBit a.val m)
      (fun k hk => bytes_to_bits_closure_gen a hNb k hk)
  have key : hacspec_ml_kem.serialize.bytes_to_bits (N := N) Nb a
      = CoreModels.core.array.from_fn Nb
          (hacspec_ml_kem.serialize.bytes_to_bits.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBool
            N Nb) a := by
    unfold hacspec_ml_kem.serialize.bytes_to_bits
    -- hax v0.4.0-rc.1 no longer emits the `let i ← N * 8#usize; massert (N8 = i)` prelude
    -- (ALL 74 spec-side `massert`s are gone from the extraction), so the length check and
    -- its `hmul` witness are no longer part of this equation.
    simp only [hacspec_ml_kem.parameters.createi]
  rw [key, hfn]
  refine ⟨_, rfl, ?_⟩
  intro m hm
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]
  rfl

private theorem bvb_256_gen (d : Std.Usize) {Nd : Std.Usize} (bv : Std.Array Bool Nd)
    (hd : d.val ≤ 16) (hNd : Nd.val = 256 * d.val) :
    ∃ arr : Std.Array Std.U16 256#usize,
      hacspec_ml_kem.serialize.bitvector_to_bounded_ints 256#usize bv d = .ok arr
      ∧ ∀ k : Nat, k < 256 →
          (arr.val[k]!).val = bitSum (fun t => bv.val[d.val * k + t]!) d.val := by
  have h256 : ((256#usize : Std.Usize)).val = 256 := by scalar_tac
  have h32 : (2:Nat) ^ 32 = 4294967296 := by norm_num
  have hNdmax : Nd.val ≤ Std.Usize.max := by scalar_tac
  -- `k * d + d ≤ 256 * d = Nd`, the one nonlinear step, done once
  have hbd : ∀ k : Nat, k < 256 → k * d.val + d.val ≤ Nd.val := by
    intro k hk
    rw [hNd]
    calc k * d.val + d.val = (k + 1) * d.val := by ring
      _ ≤ 256 * d.val := Nat.mul_le_mul_right _ (by omega)
  have hmul : ((256#usize : Std.Usize) * d : RustM Std.Usize) = .ok Nd :=
    usize_mul_lit _ _ _ (by rw [h256, hNd]) (by rw [h256, ← hNd]; scalar_tac)
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq (T := Std.U16)
      (256#usize : Std.Usize)
      (hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16
        256#usize Nd)
      (d, bv)
      (fun k => u16OfNat (bitSum (fun t => bv.val[k * d.val + t]!) d.val))
      (fun k hk => by
        rw [h256] at hk
        exact bvb_closure_eq (N := 256#usize) bv d k hd (by omega)
          (by have := hbd k hk; scalar_tac) (hbd k hk))
  have key : hacspec_ml_kem.serialize.bitvector_to_bounded_ints 256#usize bv d
      = CoreModels.core.array.from_fn (256#usize : Std.Usize)
          (hacspec_ml_kem.serialize.bitvector_to_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16
            256#usize Nd)
          (d, bv) := by
    unfold hacspec_ml_kem.serialize.bitvector_to_bounded_ints
    -- hax v0.4.0-rc.1 no longer emits the `let i ← N * 8#usize; massert (N8 = i)` prelude
    -- (ALL 74 spec-side `massert`s are gone from the extraction), so the length check and
    -- its `hmul` witness are no longer part of this equation.
    simp only [hacspec_ml_kem.parameters.createi]
  rw [key, hfn]
  refine ⟨_, rfl, ?_⟩
  intro k hk
  have hget : ((List.range ((256#usize : Std.Usize)).val).map
      (fun k => u16OfNat (bitSum (fun t => bv.val[k * d.val + t]!) d.val)))[k]!
      = u16OfNat (bitSum (fun t => bv.val[k * d.val + t]!) d.val) := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by rw [h256]; exact hk)]
    rfl
  have hcomm : (fun t => bv.val[k * d.val + t]!) = (fun t => bv.val[d.val * k + t]!) := by
    funext t; rw [Nat.mul_comm]
  show (((List.range ((256#usize : Std.Usize)).val).map
      (fun k => u16OfNat (bitSum (fun t => bv.val[k * d.val + t]!) d.val)))[k]!).val = _
  rw [hget, hcomm]
  refine u16OfNat_val _ ?_
  have h1 := bitSum_lt (fun t => bv.val[d.val * k + t]!) d.val
  have h2 : (2:Nat) ^ d.val ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) hd
  have h16 : (2:Nat) ^ 16 = 65536 := by norm_num
  scalar_tac

private theorem byte_decode_generic_gen (d : Std.Usize) {Nd : Std.Usize}
    (a : Std.Array Std.U8 Nd) (Nd8 : Std.Usize)
    (hd : d.val ≤ 12) (hNd : Nd.val = 32 * d.val) (hNd8 : Nd8.val = 8 * Nd.val) :
    ∃ arr : Std.Array Std.U16 256#usize,
      hacspec_ml_kem.serialize.byte_decode_generic 32#usize 256#usize (Nd := Nd) Nd8 a d
          = .ok arr
      ∧ ∀ k : Nat, k < 256 → (arr.val[k]!).val = win a.val d.val k := by
  obtain ⟨bv, hbv, hbvget⟩ := bytes_to_bits_gen a hNd8
  obtain ⟨arr, harr, harrget⟩ := bvb_256_gen d bv (by omega) (by omega)
  have hle : (d ≤ (12#usize : Std.Usize)) := by scalar_tac
  have e1 : ((32#usize : Std.Usize) * (8#usize : Std.Usize) : RustM Std.Usize)
      = .ok (256#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
  have e2 : ((32#usize : Std.Usize) * d : RustM Std.Usize) = .ok Nd :=
    usize_mul_lit _ _ _ (by rw [hNd]; scalar_tac) (by scalar_tac)
  have e3 : ((Nd : Std.Usize) * (8#usize : Std.Usize) : RustM Std.Usize) = .ok Nd8 :=
    usize_mul_lit _ _ _ (by rw [hNd8]; scalar_tac) (by scalar_tac)
  refine ⟨arr, ?_, ?_⟩
  · unfold hacspec_ml_kem.serialize.byte_decode_generic
    simp only [hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT, Aeneas.Std.massert,
      if_pos hle, if_true, Aeneas.Std.bind_tc_ok, e1, e2, e3, hbv, harr]
  · intro k hk
    rw [harrget k hk]
    have hb : ∀ t : Nat, t < d.val → d.val * k + t < Nd8.val := by
      intro t ht
      have h2 : d.val * k + d.val ≤ 256 * d.val := by
        calc d.val * k + d.val = d.val * (k + 1) := by ring
          _ ≤ d.val * 256 := Nat.mul_le_mul_left _ (by omega)
          _ = 256 * d.val := by ring
      rw [hNd8, hNd]
      omega
    exact (bitSum_congr _ (fun t => sliceBit a.val (d.val * k + t)) d.val
      (fun t ht => hbvget (d.val * k + t) (hb t ht))).symm ▸ rfl

private theorem byte_decode_gen_eq (d : Std.Usize) {Nd : Std.Usize} (a : Std.Array Std.U8 Nd)
    (D256 : Std.Usize) (hd : d.val ≤ 12) (hdlt : 2 ^ d.val ≤ 3329)
    (hNd : Nd.val = 32 * d.val) (hD : D256.val = 8 * Nd.val) :
    ∃ arr : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize,
      hacspec_ml_kem.serialize.byte_decode (D32 := Nd) D256 a d = .ok arr
      ∧ ∀ k : Nat, k < 256 →
          arr.val[k]! = ({ val := u16OfNat (win a.val d.val k) }
                          : hacspec_ml_kem.parameters.FieldElement) := by
  obtain ⟨decoded, hdec, hdecget⟩ := byte_decode_generic_gen d a D256 hd hNd hD
  have hle : (d ≤ (12#usize : Std.Usize)) := by scalar_tac
  have h256 : ((256#usize : Std.Usize)).val = 256 := by scalar_tac
  have halen : a.val.length = Nd.val := a.property
  have hsub : a.val.length ≤ Std.Usize.max := by rw [halen]; scalar_tac
  have hslice : (Aeneas.Std.lift (Aeneas.Std.Array.to_slice a) : RustM (Slice Std.U8))
      = .ok ⟨a.val, hsub⟩ := by
    simp [Aeneas.Std.lift, Aeneas.Std.Array.to_slice]
  have hlen : CoreModels.core.slice.Slice.len (⟨a.val, hsub⟩ : Slice Std.U8) = .ok Nd := by
    rw [slice_len_gen]
    congr 1
    refine Aeneas.Std.UScalar.eq_of_val_eq ?_
    rw [Aeneas.Std.Slice.len_val]
    exact halen
  have e2 : ((32#usize : Std.Usize) * d : RustM Std.Usize) = .ok Nd :=
    usize_mul_lit _ _ _ (by rw [hNd]; scalar_tac) (by scalar_tac)
  have e4 : ((256#usize : Std.Usize) * d : RustM Std.Usize) = .ok D256 :=
    usize_mul_lit _ _ _ (by rw [hD, hNd]; scalar_tac) (by scalar_tac)
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
      (T := hacspec_ml_kem.parameters.FieldElement) (256#usize : Std.Usize)
      (hacspec_ml_kem.serialize.byte_decode.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement
        Nd D256)
      decoded
      (fun k => ({ val := u16OfNat (win a.val d.val k) }
                  : hacspec_ml_kem.parameters.FieldElement))
      (fun k hk => by
        have hk256 : k < 256 := by rw [h256] at hk; exact hk
        rw [byte_decode_closure_eq decoded k hk256, hdecget k hk256,
          Nat.mod_eq_of_lt (lt_of_lt_of_le (win_lt a.val d.val k) hdlt)])
  refine ⟨⟨(List.range ((256#usize : Std.Usize)).val).map
      (fun k => ({ val := u16OfNat (win a.val d.val k) }
                  : hacspec_ml_kem.parameters.FieldElement)),
      by simp [List.length_map, List.length_range]⟩, ?_, ?_⟩
  · unfold hacspec_ml_kem.serialize.byte_decode
    simp only [hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT, Aeneas.Std.massert,
      if_pos hle, Aeneas.Std.bind_tc_ok, hslice, hlen, e2, e4, if_true, hdec,
      hacspec_ml_kem.parameters.createi, hfn]
  · intro k hk
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by rw [h256]; exact hk)]
    rfl

/-! ### `byte_decode_dyn` at `dv ∈ {4,5}` — the slice-shaped entry point.

    The `match d.val` dispatch is the one part of the spec ladder that cannot be generic,
    so this is two copies of a four-line argument: the two `massert`s, `try_from` at the
    fixed array size, then the generic `byte_decode`. -/

private theorem slice_len_eq_of (sl : Slice Std.U8) (n : Std.Usize)
    (h : sl.val.length = n.val) : Aeneas.Std.Slice.len sl = n := by
  refine Aeneas.Std.UScalar.eq_of_val_eq ?_
  rw [Aeneas.Std.Slice.len_val]; exact h

private theorem slice_len_of (sl : Slice Std.U8) (n : Std.Usize)
    (h : sl.val.length = n.val) : CoreModels.core.slice.Slice.len sl = .ok n := by
  rw [slice_len_gen, slice_len_eq_of sl n h]

private theorem byte_decode_dyn_45_eq (b : Slice Std.U8) (dv : Std.Usize)
    (hdv : dv.val = 4 ∨ dv.val = 5) (hb : b.val.length = 32 * dv.val) :
    ∃ arr : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize,
      hacspec_ml_kem.serialize.byte_decode_dyn b dv = .ok arr
      ∧ ∀ k : Nat, k < 256 →
          arr.val[k]! = ({ val := u16OfNat (win b.val dv.val k) }
                          : hacspec_ml_kem.parameters.FieldElement) := by
  rcases hdv with h | h
  · have hdv4 : dv = 4#usize := Aeneas.Std.UScalar.eq_of_val_eq (by rw [h]; scalar_tac)
    subst hdv4
    have hb128 : b.val.length = ((128#usize : Std.Usize)).val := by rw [hb]; scalar_tac
    have hle : ((4#usize : Std.Usize) ≤ (12#usize : Std.Usize)) := by scalar_tac
    have h4 : ((4#usize : Std.Usize)).val = 4 := by scalar_tac
    have e2 : ((32#usize : Std.Usize) * (4#usize : Std.Usize) : RustM Std.Usize)
        = .ok (128#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
    obtain ⟨arr, harr, harrget⟩ :=
      byte_decode_gen_eq 4#usize (⟨b.val, hb128⟩ : Std.Array Std.U8 128#usize) 1024#usize
        (by scalar_tac) (by rw [h4]; norm_num) (by scalar_tac) (by scalar_tac)
    refine ⟨arr, ?_, harrget⟩
    unfold hacspec_ml_kem.serialize.byte_decode_dyn
    -- (the `massert` prelude this `simp only` discharged is gone from the
    -- hax v0.4.0-rc.1 spec extraction; `unfold` now lands directly on the
    -- `match d.val` dispatch that the `show` below selects from)
    show (do
        let r ←
          CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
            (128#usize : Std.Usize) b
        let a ←
          CoreModels.core.result.Result.unwrap
            CoreModels.core.array.TryFromSliceError.Insts.CoreFmtDebug r
        hacspec_ml_kem.serialize.byte_decode (D32 := 128#usize) 1024#usize a 4#usize) = _
    rw [show
        CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
            (128#usize : Std.Usize) b
          = .ok (CoreModels.core.result.Result.Ok
              (⟨b.val, hb128⟩ : Std.Array Std.U8 128#usize)) from by
      unfold
        CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
      rw [dif_pos (slice_len_eq_of b 128#usize hb128)]]
    simp only [Aeneas.Std.bind_tc_ok, CoreModels.core.result.Result.unwrap]
    exact harr
  · have hdv5 : dv = 5#usize := Aeneas.Std.UScalar.eq_of_val_eq (by rw [h]; scalar_tac)
    subst hdv5
    have hb160 : b.val.length = ((160#usize : Std.Usize)).val := by rw [hb]; scalar_tac
    have hle : ((5#usize : Std.Usize) ≤ (12#usize : Std.Usize)) := by scalar_tac
    have h5 : ((5#usize : Std.Usize)).val = 5 := by scalar_tac
    have e2 : ((32#usize : Std.Usize) * (5#usize : Std.Usize) : RustM Std.Usize)
        = .ok (160#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
    obtain ⟨arr, harr, harrget⟩ :=
      byte_decode_gen_eq 5#usize (⟨b.val, hb160⟩ : Std.Array Std.U8 160#usize) 1280#usize
        (by scalar_tac) (by rw [h5]; norm_num) (by scalar_tac) (by scalar_tac)
    refine ⟨arr, ?_, harrget⟩
    unfold hacspec_ml_kem.serialize.byte_decode_dyn
    -- (the `massert` prelude this `simp only` discharged is gone from the
    -- hax v0.4.0-rc.1 spec extraction; `unfold` now lands directly on the
    -- `match d.val` dispatch that the `show` below selects from)
    show (do
        let r ←
          CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
            (160#usize : Std.Usize) b
        let a ←
          CoreModels.core.result.Result.unwrap
            CoreModels.core.array.TryFromSliceError.Insts.CoreFmtDebug r
        hacspec_ml_kem.serialize.byte_decode (D32 := 160#usize) 1280#usize a 5#usize) = _
    rw [show
        CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
            (160#usize : Std.Usize) b
          = .ok (CoreModels.core.result.Result.Ok
              (⟨b.val, hb160⟩ : Std.Array Std.U8 160#usize)) from by
      unfold
        CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
      rw [dif_pos (slice_len_eq_of b 160#usize hb160)]]
    simp only [Aeneas.Std.bind_tc_ok, CoreModels.core.result.Result.unwrap]
    exact harr

/-! ### Spec side — `Decompress_d` over the 256 coefficients.

    CITES M-E(1) `decompress_d_gen_eq` for the per-coefficient rounding formula; the
    `createi` plumbing is the same `from_fn_pure_eq` shape as every other closure in this
    file. `win_dec_lt` is what makes the trailing `% 3329` of `lift_fe` disappear. -/

private theorem decompress_closure_gen (d : Std.Usize)
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) (k : Nat) (hk : k < 256)
    (hd : d.val < 12) (hfe : (a.val[k]!).val.val < 2 ^ d.val) :
    (hacspec_ml_kem.compress.decompress.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement).call_mut
        ((a, d) : hacspec_ml_kem.compress.decompress.closure) ⟨BitVec.ofNat _ k⟩
      = .ok (({ val := u16OfNat ((2 * (a.val[k]!).val.val * 3329 + 2 ^ d.val)
                                  / 2 ^ (d.val + 1)) } : hacspec_ml_kem.parameters.FieldElement),
             ((a, d) : hacspec_ml_kem.compress.decompress.closure)) := by
  have hkv := usize_ofNat_val k (by omega)
  have hlen : a.val.length = 256 := by have := a.property; simpa using this
  have hidx : Aeneas.Std.Array.index_usize a (⟨BitVec.ofNat _ k⟩ : Std.Usize)
      = .ok (a.val[k]!) := by
    have h := array_index_ok a (⟨BitVec.ofNat _ k⟩ : Std.Usize) (by rw [hkv, hlen]; exact hk)
    rw [hkv] at h; exact h
  show (do
      let fe ← Aeneas.Std.Array.index_usize a (⟨BitVec.ofNat _ k⟩ : Std.Usize)
      let fe1 ← hacspec_ml_kem.compress.decompress_d fe d
      RustM.ok (fe1, ((a, d) : hacspec_ml_kem.compress.decompress.closure))) = _
  rw [hidx]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [decompress_d_gen_eq (a.val[k]!) d hd hfe]
  rfl

private theorem decompress_gen_eq (d : Std.Usize)
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) (hd : d.val < 12)
    (p : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
           libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hfe : ∀ k : Nat, k < 256 → (a.val[k]!).val.val < 2 ^ d.val)
    (hp : ∀ k : Nat, k < 256 →
        ((p.coefficients.val[k / 16]!).elements.val[k % 16]!).val
          = (((2 * (a.val[k]!).val.val * 3329 + 2 ^ d.val) / 2 ^ (d.val + 1) : Nat) : Int)) :
    hacspec_ml_kem.compress.decompress a d = .ok (lift_poly p) := by
  have h256 : ((256#usize : Std.Usize)).val = 256 := by scalar_tac
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
      (T := hacspec_ml_kem.parameters.FieldElement) (256#usize : Std.Usize)
      hacspec_ml_kem.compress.decompress.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement
      ((a, d) : hacspec_ml_kem.compress.decompress.closure)
      (fun k => lift_fe (p.coefficients.val[k / 16]!).elements.val[k % 16]!)
      (fun k hk => by
        have hk256 : k < 256 := by rw [h256] at hk; exact hk
        rw [decompress_closure_gen d a k hk256 hd (hfe k hk256),
          lift_fe_of_nat _ ((2 * (a.val[k]!).val.val * 3329 + 2 ^ d.val) / 2 ^ (d.val + 1))
            (hp k hk256),
          Nat.mod_eq_of_lt (win_dec_lt _ _ (hfe k hk256) hd)])
  unfold hacspec_ml_kem.compress.decompress
  simp only [hacspec_ml_kem.parameters.createi, hfn]
  rfl

/-- **Spec-side apex.** Given the impl's decompressed lanes, the whole spec chain
    `byte_decode_dyn` then `Decompress_dv` reproduces `lift_poly p`. -/
private theorem L53_spec_eq (serialized : Slice Std.U8) (dv : Std.Usize)
    (hdv : dv.val = 4 ∨ dv.val = 5) (hlen : serialized.val.length = 32 * dv.val)
    (p : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
           libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hdc : dcplane serialized.val dv.val p 16) :
    hacspec_ml_kem.serialize.deserialize_then_decompress_v serialized dv
      = .ok (lift_poly p) := by
  have hd : dv.val < 12 := by rcases hdv with h | h <;> omega
  have hp2 : (2:Nat) ^ dv.val ≤ 32 := by rcases hdv with h | h <;> rw [h] <;> norm_num
  obtain ⟨arr, harr, harrget⟩ := byte_decode_dyn_45_eq serialized dv hdv hlen
  have hval : ∀ k : Nat, k < 256 → (arr.val[k]!).val.val = win serialized.val dv.val k := by
    intro k hk
    rw [harrget k hk]
    exact u16OfNat_val _ (by have h1 := win_lt serialized.val dv.val k; scalar_tac)
  rw [L53_spec_unfold, harr]
  simp only [Aeneas.Std.bind_tc_ok]
  refine decompress_gen_eq dv arr hd p ?_ ?_
  · intro k hk
    rw [hval k hk]
    exact win_lt _ _ _
  · intro k hk
    rw [hval k hk]
    have h := hdc (k / 16) (by omega) (k % 16) (by omega)
    rw [show 16 * (k / 16) + k % 16 = k from by omega] at h
    exact h

end L53Bank2

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
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    -- RESTATED 2026-08-18. The previous form had NO hypotheses and a `⌜True⌝` pre; it
    -- was FALSE, and this file proves it so (`specreq_L53_refuted_at_dv_zero`, and again
    -- at dv = 4 with an empty slice). Hypotheses transcribed VERBATIM from the upstream
    -- contract (libcrux-ml-kem/src/serialize.rs):
    --   is_rank $K /\ $COMPRESSION_FACTOR == vector_v_compression_factor $K
    --   /\ Seq.length $serialized == 32 * v $COMPRESSION_FACTOR
    (h_rank : hacspec_ml_kem.parameters.is_rank K = .ok true)
    (h_cf : hacspec_ml_kem.parameters.vector_v_compression_factor K
              = .ok V_COMPRESSION_FACTOR)
    (h_len : serialized.length = 32 * V_COMPRESSION_FACTOR.val) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_v
      (vectortraitsOperationsInst := portable_ops_inst)
      K V_COMPRESSION_FACTOR serialized output
    ⦃ ⇓ p => ⌜ hacspec_ml_kem.serialize.deserialize_then_decompress_v
                  serialized V_COMPRESSION_FACTOR
                = .ok (lift_poly p)
                -- 3328, NOT upstream's 4095. 4095 is a DELIBERATELY WEAKENED dispatcher
                -- bound (`is_bounded_poly_higher(result, 3328, 4095)`) introduced to fit
                -- UPSTREAM's `compute_message`, which requires 4095. iot's
                -- `compute_message_fc` requires `natAbs ≤ 3328` (Matrix/ComputeMessage/
                -- FC.lean:119), so 4095 would be TRUE BUT USELESS FOR COMPOSITION.
                -- Tight bound measured end-to-end on the extracted impl: max lane is
                -- 3121 (dv=4) / 3225 (dv=5), so 3328 is sound and dischargeable.
                ∧ (∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
                    ((p.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 3328) ⌝ ⦄ := by
  -- The dv-conjunct of the source's `requires`: `vector_v_compression_factor` is 5 at
  -- rank 4 and 4 otherwise, so `h_cf` ALONE pins dv to {4,5} — `h_rank` is not needed for
  -- this step (it is the source's own panic-freedom conjunct, kept in the transcription).
  have hdv : V_COMPRESSION_FACTOR.val = 4 ∨ V_COMPRESSION_FACTOR.val = 5 := by
    unfold hacspec_ml_kem.parameters.vector_v_compression_factor at h_cf
    by_cases hK : K = 4#usize
    · rw [if_pos hK] at h_cf
      exact Or.inr (by injection h_cf with h; rw [← h]; scalar_tac)
    · rw [if_neg hK] at h_cf
      exact Or.inl (by injection h_cf with h; rw [← h]; scalar_tac)
  have hlen' : serialized.val.length = 32 * V_COMPRESSION_FACTOR.val := h_len
  -- FIRST RUNG (`L53_dispatch_of_pre`): the `unreachable!()` arm is gone.
  rw [L53_dispatch_of_pre K V_COMPRESSION_FACTOR serialized output hdv]
  rcases hdv with h4 | h5
  · rw [if_pos h4]
    have hlen4 : serialized.val.length = 128 := by rw [hlen', h4]
    obtain ⟨p, hp_eq, hp⟩ := triple_exists_ok_fc (L53_impl_4_fc serialized hlen4 output)
    have hdc : dcplane serialized.val 4 p 16 := (holds_ok _).mp hp
    have hdc' : dcplane serialized.val V_COMPRESSION_FACTOR.val p 16 := by rw [h4]; exact hdc
    refine triple_of_ok_fc hp_eq
      ⟨L53_spec_eq serialized V_COMPRESSION_FACTOR (Or.inl h4) hlen' p hdc', ?_⟩
    -- BOUND CONJUNCT: every lane is `(2·w·q + 2^d) / 2^(d+1)` with `w < 2^d`, hence < 3329.
    intro chunk hchunk ℓ hℓ
    have h := hdc chunk hchunk ℓ hℓ
    have hb := win_dec_lt (win serialized.val 4 (16 * chunk + ℓ)) 4 (win_lt _ _ _) (by omega)
    omega
  · rw [if_neg (by omega)]
    have hlen5 : serialized.val.length = 160 := by rw [hlen', h5]
    obtain ⟨p, hp_eq, hp⟩ := triple_exists_ok_fc (L53_impl_5_fc serialized hlen5 output)
    have hdc : dcplane serialized.val 5 p 16 := (holds_ok _).mp hp
    have hdc' : dcplane serialized.val V_COMPRESSION_FACTOR.val p 16 := by rw [h5]; exact hdc
    refine triple_of_ok_fc hp_eq
      ⟨L53_spec_eq serialized V_COMPRESSION_FACTOR (Or.inr h5) hlen' p hdc', ?_⟩
    intro chunk hchunk ℓ hℓ
    have h := hdc chunk hchunk ℓ hℓ
    have hb := win_dec_lt (win serialized.val 5 (16 * chunk + ℓ)) 5 (win_lt _ _ _) (by omega)
    omega

/-! ## PROVER bank for L5.4 — `compress_then_serialize_ring_element_v` at `dv ∈ {4,5}`.

    L5.4's statement is at the END of this file, after this bank, for the same reason
    L5.1/L5.2/L5.3 are: it assembles material declared FURTHER DOWN than the scaffold
    position could hold — `MCPBank`'s `compress_barrett_eq` /
    `compress_ciphertext_coefficient_eq` / `compress_d_gen_eq`, and `L52Bank`'s
    `as_u8_eq` / `cu16_val` / `byte_encode_closure_eq_gen` /
    `bits_to_bytes_closure_eq_gen`.  Its text is byte-identical to the locked form;
    only its position moved.

    Everything that CAN be generic in `d` is: the pure byte model (`cLane` / `cByte` /
    `cBit`), the per-lane compress seam, and the whole spec-side `createi` ladder are
    each stated ONCE in `d` and instantiated twice.  What is NOT generic is the two
    impl seams — `serialize_4_int` and `serialize_5_int` are different straight-line
    programs, and at `d = 4` no lane straddles a byte while at `d = 5` four bytes out of
    five do — and the two range-loop bodies (different machine-generated names,
    different stride literals).  That is the honest measurement for CORRECTION 2: the
    ENCODE impl seam does not generalise even within one obligation, while everything
    around it does. -/

section L54Bank

open Aeneas.Std
open libcrux_iot_ml_kem.Util.LoopSpecs

/-! ### The dispatcher rung — the same three-lemma `simp only` normal form as L5.3's
    `L53_dispatch_of_pre`, copied verbatim off it (that is what made it one rung and not
    a dispatch). -/

/-- `V_COMPRESSION_FACTOR = 4` dispatches to `compress_then_serialize_4`. -/
private theorem L54_dispatch_eq_d4 (K C2_LEN : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_v
      (vectortraitsOperationsInst := portable_ops_inst) K 4#usize C2_LEN re out scratch
    = libcrux_iot_ml_kem.serialize.compress_then_serialize_4
        (vectortraitsOperationsInst := portable_ops_inst) re out scratch := by
  simp only [libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_v,
    Aeneas.Std.lift, Aeneas.Std.bind_tc_ok, Std.UScalar.cast, Std.UScalarTy.U32_numBits_eq]
  simp

/-- `V_COMPRESSION_FACTOR = 5` dispatches to `compress_then_serialize_5`. -/
private theorem L54_dispatch_eq_d5 (K C2_LEN : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_v
      (vectortraitsOperationsInst := portable_ops_inst) K 5#usize C2_LEN re out scratch
    = libcrux_iot_ml_kem.serialize.compress_then_serialize_5
        (vectortraitsOperationsInst := portable_ops_inst) re out scratch := by
  simp only [libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_v,
    Aeneas.Std.lift, Aeneas.Std.bind_tc_ok, Std.UScalar.cast, Std.UScalarTy.U32_numBits_eq]
  simp

/-- **First rung of the positive L5.4 proof**: under the dv-conjunct of the source's
    `requires`, the dispatcher reduces to exactly one of the two real arms — the
    `unreachable!()` arm that `specreq_L54_refuted_at_dv_zero` exploits is gone. -/
private theorem L54_dispatch_of_pre (K V_COMPRESSION_FACTOR C2_LEN : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_dv : V_COMPRESSION_FACTOR.val = 4 ∨ V_COMPRESSION_FACTOR.val = 5) :
    libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_v
      (vectortraitsOperationsInst := portable_ops_inst)
      K V_COMPRESSION_FACTOR C2_LEN re out scratch
    = if V_COMPRESSION_FACTOR.val = 4 then
        libcrux_iot_ml_kem.serialize.compress_then_serialize_4
          (vectortraitsOperationsInst := portable_ops_inst) re out scratch
      else
        libcrux_iot_ml_kem.serialize.compress_then_serialize_5
          (vectortraitsOperationsInst := portable_ops_inst) re out scratch := by
  rcases h_dv with h | h
  · rw [show V_COMPRESSION_FACTOR = 4#usize from Aeneas.Std.UScalar.eq_of_val_eq (by scalar_tac),
      L54_dispatch_eq_d4]
    simp
  · rw [show V_COMPRESSION_FACTOR = 5#usize from Aeneas.Std.UScalar.eq_of_val_eq (by scalar_tac),
      L54_dispatch_eq_d5]
    simp

/-! ### The pure `Nat` byte model, generic in `d`.

    `cLane re d j` is the `d`-bit COMPRESSED value of lane `j`, in the spec's own closed
    form (`compress_d_gen_eq`'s RHS).  `cByte re d n` is byte `n` of the packed stream,
    read as the 3-lane window that M-C(2) `bitSum_laneBit_window` produces — so the
    spec-side bit algebra is discharged by CITING that law and the impl side only has to
    hit the same three-term expression. -/

/-- Byte `n` of a `d`-bit lane stream: the RHS of M-C(2), as a named atom. -/
private def lanewin (d : Nat) (L : Nat → Nat) (n : Nat) : Nat :=
  (L (8 * n / d) / 2 ^ (8 * n % d)
    + L (8 * n / d + 1) * 2 ^ (d - 8 * n % d)
    + L (8 * n / d + 2) * 2 ^ (2 * d - 8 * n % d)) % 256

/-- The `d`-bit compressed value of lane `j`. -/
private def cLane (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (d j : Nat) : Nat :=
  ((2 * encLane re j * 2 ^ d + 3329) / 6658) % 2 ^ d

private theorem cLane_lt (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (d j : Nat) :
    cLane re d j < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)

/-- Byte `n` of the `d`-bit packing of `re`'s compressed lanes. -/
private def cByte (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (d n : Nat) : Nat :=
  lanewin d (cLane re d) n

/-- Bit `m` of the `d`-bit stream — the normal form of `bitvector_from_bounded_ints`'s
    closure at width `d`. -/
private def cBit (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (d m : Nat) : Bool :=
  natBit (cLane re d (m / d)) (m % d)

/-- **CITES M-C(2) `bitSum_laneBit_window`** — and nothing else.  The LSB-first 8-bit
    window of the `d`-bit compressed stream IS the 3-lane read the impl computes.  The
    `hL` hypothesis of the window law is `cLane_lt`, which is exactly the
    `0 ≤ r < 2 ^ d` post of `compress_ciphertext_coefficient_eq`; that is why compress
    and encode compose here with no bridging lemma. -/
private theorem bitSum_cBit_eq_cByte
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (d : Nat) (hd : 4 ≤ d) (n : Nat) :
    bitSum (fun t => cBit re d (8 * n + t)) 8 = cByte re d n :=
  bitSum_laneBit_window d hd (cLane re d) (cLane_lt re d) n

/-- Re-indexing: chunk `k`'s local byte `n` is global byte `2 * d * k + n`.  `8 * (2dk+n)`
    is `d * (16k) + 8n`, so the window's base lane shifts by exactly `16k` and the bit
    offset does not move — which is why the per-chunk seam can be stated locally. -/
private theorem lanewin_shift
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (d k n : Nat) (hd : 0 < d) :
    lanewin d (fun j => cLane re d (16 * k + j)) n = cByte re d (2 * d * k + n) := by
  have e1 : 8 * (2 * d * k + n) = d * (16 * k) + 8 * n := by ring
  unfold cByte lanewin
  rw [e1, Nat.mul_add_div hd, Nat.mul_add_mod]
  simp only [← Nat.add_assoc]

/-! ### `RustM`-payload plumbing the `d = 12` bank does not have: 4- and 5-tuples. -/

private theorem bind_ok_quad {α β γ δ ε : Type} {x : RustM (α × β × γ × δ)}
    {a : α} {b : β} {c : γ} {e : δ}
    (h : x = .ok (a, b, c, e)) (g : α → β → γ → δ → RustM ε) :
    (do let (u, v, w, z) ← x; g u v w z) = g a b c e := by rw [h]; rfl

private theorem bind_ok_quint {α β γ δ ε ζ : Type} {x : RustM (α × β × γ × δ × ε)}
    {a : α} {b : β} {c : γ} {e : δ} {f : ε}
    (h : x = .ok (a, b, c, e, f)) (g : α → β → γ → δ → ε → RustM ζ) :
    (do let (u, v, w, z, y) ← x; g u v w z y) = g a b c e f := by rw [h]; rfl

/-! ### Shift payloads PINNED at the `BitVec` level.

    The `d = 12` bank's `u8_shl_iscalar` / `u8_shl_lit` pin only the `.val`, which is
    enough for a straight-line walk but not to name the output byte as a `def`.  The
    encode seams need the latter (their outputs go into a `set`-chain), so each shift
    gets a payload-pinned form.  Aeneas's `<<<` on both `UScalar` and `IScalar`
    TRUNCATES rather than failing (`shiftLeft` is total for `s < numBits`), so these
    carry no value side-condition at all — the bounds appear later, in the `.val`
    lemmas, where they are real. -/

private theorem u8_shl_bvp (x : Std.U8) (t : Std.I32) (k : Nat)
    (htv : t.val = (k : Int)) (hk : k < 8) :
    (x <<< t : RustM Std.U8) = .ok ⟨x.bv <<< k⟩ := by
  have h0 : (0:Int) ≤ t.val := by rw [htv]; exact Int.natCast_nonneg k
  have hkn : Std.IScalar.toNat t = k := by
    show t.val.toNat = k; rw [htv]; exact Int.toNat_natCast k
  show Std.UScalar.shiftLeft_IScalar x t = _
  unfold Std.UScalar.shiftLeft_IScalar Std.UScalar.shiftLeft
  rw [if_pos h0, hkn, if_pos (show k < Std.UScalarTy.U8.numBits by simpa using hk)]
  rfl

private theorem i16_shl_bvp (x : Std.I16) (t : Std.I32) (k : Nat)
    (htv : t.val = (k : Int)) (hk : k < 16) :
    (x <<< t : RustM Std.I16) = .ok ⟨x.bv <<< k⟩ := by
  have h0 : (0:Int) ≤ t.val := by rw [htv]; exact Int.natCast_nonneg k
  have hkn : Std.IScalar.toNat t = k := by
    show t.val.toNat = k; rw [htv]; exact Int.toNat_natCast k
  show Std.IScalar.shiftLeft_IScalar x t = _
  unfold Std.IScalar.shiftLeft_IScalar Std.IScalar.shiftLeft
  rw [if_pos h0, hkn, if_pos (show k < Std.IScalarTy.I16.numBits by simpa using hk)]
  rfl

private theorem i16_shr_bvp (x : Std.I16) (t : Std.I32) (k : Nat)
    (htv : t.val = (k : Int)) (hk : k < 16) :
    (x >>> t : RustM Std.I16) = .ok ⟨x.bv.sshiftRight k⟩ := by
  have h0 : (0:Int) ≤ t.val := by rw [htv]; exact Int.natCast_nonneg k
  have hkn : Std.IScalar.toNat t = k := by
    show t.val.toNat = k; rw [htv]; exact Int.toNat_natCast k
  show Std.IScalar.shiftRight_IScalar x t = _
  unfold Std.IScalar.shiftRight_IScalar Std.IScalar.shiftRight
  rw [if_pos h0, hkn, if_pos (show k < Std.IScalarTy.I16.numBits by simpa using hk)]

/-- A left shift that does not truncate, on the `Nat` view. -/
private theorem bv16_shl_p (a : BitVec 16) (k : Nat) (h : a.toNat * 2 ^ k < 65536) :
    (a <<< k).toNat = a.toNat * 2 ^ k := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt (by simpa using h)

/-- The arithmetic right shift of a NONNEGATIVE `I16` is floor division. -/
private theorem bv16_sshr_p (a : BitVec 16) (k : Nat) (h : a.toNat < 32768) :
    (a.sshiftRight k).toNat = a.toNat / 2 ^ k := by
  rw [BitVec.sshiftRight_eq_of_msb_false
      (BitVec.msb_eq_false_iff_two_mul_lt.mpr (by simp; omega)),
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-! ### IMPL SEAM at `d = 4`. THE UNCOVERED PART, half one.

    `serialize_4_int` packs 8 four-bit lanes into 4 bytes.  Four divides eight, so NO
    lane straddles a byte and every output byte is one `(hi <<< 4) ||| lo` — the whole
    seam is `or_shl_add` eight times over.  Contrast the `d = 5` half below, where four
    of the five bytes straddle and the shift amounts advance by 5 mod 8. -/

/-- The one byte `serialize_4_int` builds from a lane pair. -/
private def s4b (x0 x1 : Std.I16) : Std.U8 := ⟨((c8 x1).bv <<< 4) ||| (c8 x0).bv⟩

private theorem s4b_val (x0 x1 : Std.I16) (h0 : x0.bv.toNat < 16) (h1 : x1.bv.toNat < 16) :
    (s4b x0 x1).val = x0.bv.toNat + 16 * x1.bv.toNat := by
  have e1 : (c8 x1).bv.toNat = x1.bv.toNat := by
    show (c8 x1).val = _; rw [c8_val]; omega
  have e0 : (c8 x0).bv.toNat = x0.bv.toNat := by
    show (c8 x0).val = _; rw [c8_val]; omega
  show (((c8 x1).bv <<< 4) ||| (c8 x0).bv).toNat = _
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, e1, e0, Nat.shiftLeft_eq,
    show (2:Nat) ^ 4 = 16 from rfl]
  rw [Nat.mod_eq_of_lt (show x1.bv.toNat * 16 < 2 ^ 8 by norm_num; omega)]
  rw [show x1.bv.toNat * 16 = x1.bv.toNat * 2 ^ 4 from rfl,
    or_shl_add _ _ 4 (show x0.bv.toNat < 2 ^ 4 by norm_num; omega)]
  norm_num
  omega

private theorem serialize_4_int_eq (v : Slice Std.I16) (h : 8 ≤ v.val.length) :
    libcrux_iot_ml_kem.vector.portable.serialize.serialize_4_int v
      = .ok (s4b v.val[0]! v.val[1]!, s4b v.val[2]! v.val[3]!,
             s4b v.val[4]! v.val[5]!, s4b v.val[6]! v.val[7]!) := by
  have q : ∀ (u : Std.Usize) (j : Nat), u.val = j → j < 8 →
      Aeneas.Std.Slice.index_usize v u = .ok (v.val[j]!) := by
    intro u j hu hj
    rw [slice_index_usize_eq v u (by omega), hu]
  unfold libcrux_iot_ml_kem.vector.portable.serialize.serialize_4_int
  simp only [Aeneas.Std.lift]
  rw [q 1#usize 1 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [as_u8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [u8_shl_bvp _ _ 4 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [q 0#usize 0 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [as_u8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [q 3#usize 3 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [as_u8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [u8_shl_bvp _ _ 4 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [q 2#usize 2 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [as_u8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [q 5#usize 5 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [as_u8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [u8_shl_bvp _ _ 4 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [q 4#usize 4 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [as_u8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [q 7#usize 7 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [as_u8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [u8_shl_bvp _ _ 4 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [q 6#usize 6 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [as_u8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rfl

/-! ### IMPL SEAM at `d = 5`. THE UNCOVERED PART, half two. -/

private def s5b0 (x0 x1 : Std.I16) : Std.U8 := c8 ⟨x0.bv ||| (x1.bv <<< 5)⟩

private def s5b1 (x1 x2 x3 : Std.I16) : Std.U8 :=
  c8 ⟨((x1.bv.sshiftRight 3) ||| (x2.bv <<< 2)) ||| (x3.bv <<< 7)⟩

private def s5b2 (x3 x4 : Std.I16) : Std.U8 :=
  c8 ⟨(x3.bv.sshiftRight 1) ||| (x4.bv <<< 4)⟩

private def s5b3 (x4 x5 x6 : Std.I16) : Std.U8 :=
  c8 ⟨((x4.bv.sshiftRight 4) ||| (x5.bv <<< 1)) ||| (x6.bv <<< 6)⟩

private def s5b4 (x6 x7 : Std.I16) : Std.U8 :=
  c8 ⟨(x6.bv.sshiftRight 2) ||| (x7.bv <<< 3)⟩

private theorem s5b0_val (x0 x1 : Std.I16) (h0 : x0.bv.toNat < 32) (h1 : x1.bv.toNat < 32) :
    (s5b0 x0 x1).val = (x0.bv.toNat / 2 ^ 0 + x1.bv.toNat * 2 ^ 5) % 256 := by
  show (c8 ⟨x0.bv ||| (x1.bv <<< 5)⟩).val = _
  rw [c8_val]
  show (x0.bv ||| (x1.bv <<< 5)).toNat % 256 = _
  rw [BitVec.toNat_or, bv16_shl_p _ 5 (by norm_num; omega), Nat.or_comm,
    or_shl_add _ _ 5 (show x0.bv.toNat < 2 ^ 5 by norm_num; omega)]
  norm_num
  omega

private theorem s5b1_val (x1 x2 x3 : Std.I16)
    (h1 : x1.bv.toNat < 32) (h2 : x2.bv.toNat < 32) (h3 : x3.bv.toNat < 32) :
    (s5b1 x1 x2 x3).val
      = (x1.bv.toNat / 2 ^ 3 + x2.bv.toNat * 2 ^ 2 + x3.bv.toNat * 2 ^ 7) % 256 := by
  show (c8 ⟨((x1.bv.sshiftRight 3) ||| (x2.bv <<< 2)) ||| (x3.bv <<< 7)⟩).val = _
  rw [c8_val]
  show (((x1.bv.sshiftRight 3) ||| (x2.bv <<< 2)) ||| (x3.bv <<< 7)).toNat % 256 = _
  rw [BitVec.toNat_or, BitVec.toNat_or, bv16_sshr_p _ 3 (by omega),
    bv16_shl_p _ 2 (by norm_num; omega), bv16_shl_p _ 7 (by norm_num; omega)]
  rw [Nat.or_comm (x1.bv.toNat / 2 ^ 3),
    or_shl_add _ _ 2 (show x1.bv.toNat / 2 ^ 3 < 2 ^ 2 by norm_num; omega)]
  rw [Nat.or_comm, or_shl_add _ _ 7
    (show x2.bv.toNat * 2 ^ 2 + x1.bv.toNat / 2 ^ 3 < 2 ^ 7 by norm_num; omega)]
  norm_num
  omega

private theorem s5b2_val (x3 x4 : Std.I16) (h3 : x3.bv.toNat < 32) (h4 : x4.bv.toNat < 32) :
    (s5b2 x3 x4).val = (x3.bv.toNat / 2 ^ 1 + x4.bv.toNat * 2 ^ 4) % 256 := by
  show (c8 ⟨(x3.bv.sshiftRight 1) ||| (x4.bv <<< 4)⟩).val = _
  rw [c8_val]
  show ((x3.bv.sshiftRight 1) ||| (x4.bv <<< 4)).toNat % 256 = _
  rw [BitVec.toNat_or, bv16_sshr_p _ 1 (by omega), bv16_shl_p _ 4 (by norm_num; omega),
    Nat.or_comm, or_shl_add _ _ 4 (show x3.bv.toNat / 2 ^ 1 < 2 ^ 4 by norm_num; omega)]
  norm_num
  omega

private theorem s5b3_val (x4 x5 x6 : Std.I16)
    (h4 : x4.bv.toNat < 32) (h5 : x5.bv.toNat < 32) (h6 : x6.bv.toNat < 32) :
    (s5b3 x4 x5 x6).val
      = (x4.bv.toNat / 2 ^ 4 + x5.bv.toNat * 2 ^ 1 + x6.bv.toNat * 2 ^ 6) % 256 := by
  show (c8 ⟨((x4.bv.sshiftRight 4) ||| (x5.bv <<< 1)) ||| (x6.bv <<< 6)⟩).val = _
  rw [c8_val]
  show (((x4.bv.sshiftRight 4) ||| (x5.bv <<< 1)) ||| (x6.bv <<< 6)).toNat % 256 = _
  rw [BitVec.toNat_or, BitVec.toNat_or, bv16_sshr_p _ 4 (by omega),
    bv16_shl_p _ 1 (by norm_num; omega), bv16_shl_p _ 6 (by norm_num; omega)]
  rw [Nat.or_comm (x4.bv.toNat / 2 ^ 4),
    or_shl_add _ _ 1 (show x4.bv.toNat / 2 ^ 4 < 2 ^ 1 by norm_num; omega)]
  rw [Nat.or_comm, or_shl_add _ _ 6
    (show x5.bv.toNat * 2 ^ 1 + x4.bv.toNat / 2 ^ 4 < 2 ^ 6 by norm_num; omega)]
  norm_num
  omega

private theorem s5b4_val (x6 x7 : Std.I16) (h6 : x6.bv.toNat < 32) (h7 : x7.bv.toNat < 32) :
    (s5b4 x6 x7).val = (x6.bv.toNat / 2 ^ 2 + x7.bv.toNat * 2 ^ 3) % 256 := by
  show (c8 ⟨(x6.bv.sshiftRight 2) ||| (x7.bv <<< 3)⟩).val = _
  rw [c8_val]
  show ((x6.bv.sshiftRight 2) ||| (x7.bv <<< 3)).toNat % 256 = _
  rw [BitVec.toNat_or, bv16_sshr_p _ 2 (by omega), bv16_shl_p _ 3 (by norm_num; omega),
    Nat.or_comm, or_shl_add _ _ 3 (show x6.bv.toNat / 2 ^ 2 < 2 ^ 3 by norm_num; omega)]
  norm_num
  omega

private theorem serialize_5_int_eq (v : Slice Std.I16) (h : 8 ≤ v.val.length) :
    libcrux_iot_ml_kem.vector.portable.serialize.serialize_5_int v
      = .ok (s5b0 v.val[0]! v.val[1]!,
             s5b1 v.val[1]! v.val[2]! v.val[3]!,
             s5b2 v.val[3]! v.val[4]!,
             s5b3 v.val[4]! v.val[5]! v.val[6]!,
             s5b4 v.val[6]! v.val[7]!) := by
  have q : ∀ (u : Std.Usize) (j : Nat), u.val = j → j < 8 →
      Aeneas.Std.Slice.index_usize v u = .ok (v.val[j]!) := by
    intro u j hu hj
    rw [slice_index_usize_eq v u (by omega), hu]
  unfold libcrux_iot_ml_kem.vector.portable.serialize.serialize_5_int
  simp only [Aeneas.Std.lift]
  rw [q 0#usize 0 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [q 1#usize 1 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [i16_shl_bvp _ _ 5 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [as_u8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [i16_shr_bvp _ _ 3 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [q 2#usize 2 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [i16_shl_bvp _ _ 2 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [q 3#usize 3 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [i16_shl_bvp _ _ 7 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [as_u8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [i16_shr_bvp _ _ 1 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [q 4#usize 4 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [i16_shl_bvp _ _ 4 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [as_u8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [i16_shr_bvp _ _ 4 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [q 5#usize 5 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [i16_shl_bvp _ _ 1 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [q 6#usize 6 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [i16_shl_bvp _ _ 6 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [as_u8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [i16_shr_bvp _ _ 2 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [q 7#usize 7 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [i16_shl_bvp _ _ 3 (by scalar_tac) (by omega)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [as_u8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rfl

/-! ### `serialize_4` — the 8-byte wrapper: two 8-lane sub-slices, eight `Slice.update`s. -/

private theorem s4_group (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (a bnd : Std.Usize) (m0 : Nat) (ha : a.val = m0) (hb : bnd.val = m0 + 8)
    (hm : m0 + 8 ≤ 16) :
    ∃ ns : Slice Std.I16,
      CoreModels.core.Array.Insts.CoreOpsIndexIndex.index
        (CoreModels.core.Slice.Insts.CoreOpsIndexIndex
          (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I16))
        v.elements ⟨a, bnd⟩ = .ok ns
      ∧ libcrux_iot_ml_kem.vector.portable.serialize.serialize_4_int ns
          = .ok (s4b v.elements.val[m0]! v.elements.val[m0 + 1]!,
                 s4b v.elements.val[m0 + 2]! v.elements.val[m0 + 3]!,
                 s4b v.elements.val[m0 + 4]! v.elements.val[m0 + 5]!,
                 s4b v.elements.val[m0 + 6]! v.elements.val[m0 + 7]!) := by
  have hE : v.elements.val.length = 16 := by have := v.elements.property; simpa using this
  obtain ⟨ns, he, hl, hget⟩ := array_index_range_strict v.elements a bnd (by omega) (by omega)
  refine ⟨ns, he, ?_⟩
  rw [serialize_4_int_eq ns (by omega)]
  rw [hget 0 (by omega), hget 1 (by omega), hget 2 (by omega), hget 3 (by omega),
    hget 4 (by omega), hget 5 (by omega), hget 6 (by omega), hget 7 (by omega), ha]
  norm_num

/-- The 8 bytes `serialize_4` writes into `out`, as an explicit `set` chain. -/
private def s4set (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8) : Slice Std.U8 :=
  out.set 0#usize (s4b v.elements.val[0]! v.elements.val[1]!)
  |>.set 1#usize (s4b v.elements.val[2]! v.elements.val[3]!)
  |>.set 2#usize (s4b v.elements.val[4]! v.elements.val[5]!)
  |>.set 3#usize (s4b v.elements.val[6]! v.elements.val[7]!)
  |>.set 4#usize (s4b v.elements.val[8]! v.elements.val[9]!)
  |>.set 5#usize (s4b v.elements.val[10]! v.elements.val[11]!)
  |>.set 6#usize (s4b v.elements.val[12]! v.elements.val[13]!)
  |>.set 7#usize (s4b v.elements.val[14]! v.elements.val[15]!)

private theorem s4set_length
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8) (h : out.val.length = 8) : (s4set v out).val.length = 8 := by
  unfold s4set
  simp only [Aeneas.Std.Slice.set_val_eq, List.length_set]; exact h

/-- Byte `n` of the `d = 4` packing of one 16-lane vector, in impl terms. -/
private def v4byte (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (n : Nat) : Std.U8 :=
  s4b (v.elements.val[2 * n]!) (v.elements.val[2 * n + 1]!)

set_option maxHeartbeats 4000000 in
private theorem s4set_get
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8) (h : out.val.length = 8) (n : Nat) (hn : n < 8) :
    (s4set v out).val[n]! = v4byte v n := by
  unfold s4set
  simp only [Aeneas.Std.Slice.set_val_eq]
  interval_cases n <;> (simp_lists; norm_num [v4byte])

set_option maxHeartbeats 4000000 in
/-- **Impl-side chunk closed form at `d = 4`**: `serialize_4` writes exactly `v4byte`. -/
private theorem serialize_4_eq
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8) (h : out.val.length = 8) :
    libcrux_iot_ml_kem.vector.portable.serialize.serialize_4 v out = .ok (s4set v out) := by
  obtain ⟨ns0, he0, hs0⟩ := s4_group v 0#usize 8#usize 0
    (by scalar_tac) (by scalar_tac) (by omega)
  obtain ⟨ns1, he1, hs1⟩ := s4_group v 8#usize 16#usize 8
    (by scalar_tac) (by scalar_tac) (by omega)
  simp only [Nat.reduceAdd] at hs0 hs1
  have hlen : CoreModels.core.slice.Slice.len out = .ok (8#usize : Std.Usize) := by
    show RustM.ok (Aeneas.Std.Slice.len out) = _
    congr 1
    apply Std.UScalar.eq_of_val_eq
    simp [Aeneas.Std.Slice.len_val, h]
  unfold libcrux_iot_ml_kem.vector.portable.serialize.serialize_4 s4set
  rw [hlen]
  simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.massert, if_true]
  rw [he0]; simp only [Aeneas.Std.bind_tc_ok]
  rw [bind_ok_quad hs0]
  rw [slice_update_eq _ _ _ (by simp only [h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [he1]; simp only [Aeneas.Std.bind_tc_ok]
  rw [bind_ok_quad hs1]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]

/-- The `d = 4` byte value against an abstract lane function. Reads lane `2n + 2` out of
    `L` — one PAST the vector at `n = 7` — which is sound because that term is a multiple
    of `256` and dies under the truncation; that is also exactly what makes the per-chunk
    seam agree with the GLOBAL byte model at the chunk boundary. -/
private theorem v4byte_val
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (L : Nat → Nat)
    (hv : ∀ l : Nat, l < 16 → (v.elements.val[l]!).bv.toNat = L l)
    (hL : ∀ i : Nat, L i < 16) (n : Nat) (hn : n < 8) :
    (v4byte v n).val = lanewin 4 L n := by
  have b0 := hv (2 * n) (by omega)
  have b1 := hv (2 * n + 1) (by omega)
  have l0 := hL (2 * n)
  have l1 := hL (2 * n + 1)
  have l2 := hL (2 * n + 2)
  unfold v4byte
  rw [s4b_val _ _ (by rw [b0]; omega) (by rw [b1]; omega), b0, b1]
  unfold lanewin
  rw [show 8 * n / 4 = 2 * n from by omega, show 8 * n % 4 = 0 from by omega,
    show (2:Nat) ^ 0 = 1 from rfl, show (2:Nat) ^ (4 - 0) = 16 from rfl,
    show (2:Nat) ^ (2 * 4 - 0) = 256 from rfl, Nat.div_one]
  omega

/-! ### `serialize_5` — the 10-byte wrapper. -/

private theorem s5_group (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (a bnd : Std.Usize) (m0 : Nat) (ha : a.val = m0) (hb : bnd.val = m0 + 8)
    (hm : m0 + 8 ≤ 16) :
    ∃ ns : Slice Std.I16,
      CoreModels.core.Array.Insts.CoreOpsIndexIndex.index
        (CoreModels.core.Slice.Insts.CoreOpsIndexIndex
          (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I16))
        v.elements ⟨a, bnd⟩ = .ok ns
      ∧ libcrux_iot_ml_kem.vector.portable.serialize.serialize_5_int ns
          = .ok (s5b0 v.elements.val[m0]! v.elements.val[m0 + 1]!,
                 s5b1 v.elements.val[m0 + 1]! v.elements.val[m0 + 2]! v.elements.val[m0 + 3]!,
                 s5b2 v.elements.val[m0 + 3]! v.elements.val[m0 + 4]!,
                 s5b3 v.elements.val[m0 + 4]! v.elements.val[m0 + 5]! v.elements.val[m0 + 6]!,
                 s5b4 v.elements.val[m0 + 6]! v.elements.val[m0 + 7]!) := by
  have hE : v.elements.val.length = 16 := by have := v.elements.property; simpa using this
  obtain ⟨ns, he, hl, hget⟩ := array_index_range_strict v.elements a bnd (by omega) (by omega)
  refine ⟨ns, he, ?_⟩
  rw [serialize_5_int_eq ns (by omega)]
  rw [hget 0 (by omega), hget 1 (by omega), hget 2 (by omega), hget 3 (by omega),
    hget 4 (by omega), hget 5 (by omega), hget 6 (by omega), hget 7 (by omega), ha]
  norm_num

private def s5set (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8) : Slice Std.U8 :=
  out.set 0#usize (s5b0 v.elements.val[0]! v.elements.val[1]!)
  |>.set 1#usize (s5b1 v.elements.val[1]! v.elements.val[2]! v.elements.val[3]!)
  |>.set 2#usize (s5b2 v.elements.val[3]! v.elements.val[4]!)
  |>.set 3#usize (s5b3 v.elements.val[4]! v.elements.val[5]! v.elements.val[6]!)
  |>.set 4#usize (s5b4 v.elements.val[6]! v.elements.val[7]!)
  |>.set 5#usize (s5b0 v.elements.val[8]! v.elements.val[9]!)
  |>.set 6#usize (s5b1 v.elements.val[9]! v.elements.val[10]! v.elements.val[11]!)
  |>.set 7#usize (s5b2 v.elements.val[11]! v.elements.val[12]!)
  |>.set 8#usize (s5b3 v.elements.val[12]! v.elements.val[13]! v.elements.val[14]!)
  |>.set 9#usize (s5b4 v.elements.val[14]! v.elements.val[15]!)

private theorem s5set_length
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8) (h : out.val.length = 10) : (s5set v out).val.length = 10 := by
  unfold s5set
  simp only [Aeneas.Std.Slice.set_val_eq, List.length_set]; exact h

/-- Byte `n` of the `d = 5` packing of one 16-lane vector, in impl terms. Unlike `v4byte`
    this is a FIVE-way split: the lane/byte boundaries realign only every 5 bytes. -/
private def v5byte (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (n : Nat) : Std.U8 :=
  if n % 5 = 0 then
    s5b0 (v.elements.val[8 * (n / 5)]!) (v.elements.val[8 * (n / 5) + 1]!)
  else if n % 5 = 1 then
    s5b1 (v.elements.val[8 * (n / 5) + 1]!) (v.elements.val[8 * (n / 5) + 2]!)
      (v.elements.val[8 * (n / 5) + 3]!)
  else if n % 5 = 2 then
    s5b2 (v.elements.val[8 * (n / 5) + 3]!) (v.elements.val[8 * (n / 5) + 4]!)
  else if n % 5 = 3 then
    s5b3 (v.elements.val[8 * (n / 5) + 4]!) (v.elements.val[8 * (n / 5) + 5]!)
      (v.elements.val[8 * (n / 5) + 6]!)
  else
    s5b4 (v.elements.val[8 * (n / 5) + 6]!) (v.elements.val[8 * (n / 5) + 7]!)

set_option maxHeartbeats 4000000 in
private theorem s5set_get
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8) (h : out.val.length = 10) (n : Nat) (hn : n < 10) :
    (s5set v out).val[n]! = v5byte v n := by
  unfold s5set
  simp only [Aeneas.Std.Slice.set_val_eq]
  interval_cases n <;> (simp_lists; norm_num [v5byte])

set_option maxHeartbeats 4000000 in
/-- **Impl-side chunk closed form at `d = 5`**: `serialize_5` writes exactly `v5byte`. -/
private theorem serialize_5_eq
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8) (h : out.val.length = 10) :
    libcrux_iot_ml_kem.vector.portable.serialize.serialize_5 v out = .ok (s5set v out) := by
  obtain ⟨ns0, he0, hs0⟩ := s5_group v 0#usize 8#usize 0
    (by scalar_tac) (by scalar_tac) (by omega)
  obtain ⟨ns1, he1, hs1⟩ := s5_group v 8#usize 16#usize 8
    (by scalar_tac) (by scalar_tac) (by omega)
  simp only [Nat.reduceAdd] at hs0 hs1
  have hlen : CoreModels.core.slice.Slice.len out = .ok (10#usize : Std.Usize) := by
    show RustM.ok (Aeneas.Std.Slice.len out) = _
    congr 1
    apply Std.UScalar.eq_of_val_eq
    simp [Aeneas.Std.Slice.len_val, h]
  unfold libcrux_iot_ml_kem.vector.portable.serialize.serialize_5 s5set
  rw [hlen]
  simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.massert, if_true]
  rw [he0]; simp only [Aeneas.Std.bind_tc_ok]
  rw [bind_ok_quint hs0]
  rw [slice_update_eq _ _ _ (by simp only [h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [he1]; simp only [Aeneas.Std.bind_tc_ok]
  rw [bind_ok_quint hs1]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]; simp only [Aeneas.Std.bind_tc_ok]
  rw [slice_update_eq _ _ _ (by simp only [Aeneas.Std.Slice.set_val_eq, List.length_set, h]; scalar_tac)]

private theorem v5byte_val
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (L : Nat → Nat)
    (hv : ∀ l : Nat, l < 16 → (v.elements.val[l]!).bv.toNat = L l)
    (hL : ∀ i : Nat, L i < 32) (n : Nat) (hn : n < 10) :
    (v5byte v n).val = lanewin 5 L n := by
  obtain ⟨m, hm5⟩ : ∃ m : Nat, n / 5 = m := ⟨_, rfl⟩
  have hmlt : m < 2 := by omega
  have b0 : (v.elements.val[8 * m]!).bv.toNat = L (8 * m) := hv _ (by omega)
  have b1 : (v.elements.val[8 * m + 1]!).bv.toNat = L (8 * m + 1) := hv _ (by omega)
  have b2 : (v.elements.val[8 * m + 2]!).bv.toNat = L (8 * m + 2) := hv _ (by omega)
  have b3 : (v.elements.val[8 * m + 3]!).bv.toNat = L (8 * m + 3) := hv _ (by omega)
  have b4 : (v.elements.val[8 * m + 4]!).bv.toNat = L (8 * m + 4) := hv _ (by omega)
  have b5 : (v.elements.val[8 * m + 5]!).bv.toNat = L (8 * m + 5) := hv _ (by omega)
  have b6 : (v.elements.val[8 * m + 6]!).bv.toNat = L (8 * m + 6) := hv _ (by omega)
  have b7 : (v.elements.val[8 * m + 7]!).bv.toNat = L (8 * m + 7) := hv _ (by omega)
  have c0 := hL (8 * m); have c1 := hL (8 * m + 1); have c2 := hL (8 * m + 2)
  have c3 := hL (8 * m + 3); have c4 := hL (8 * m + 4); have c5 := hL (8 * m + 5)
  have c6 := hL (8 * m + 6); have c7 := hL (8 * m + 7); have c8 := hL (8 * m + 8)
  unfold v5byte
  rw [hm5]
  unfold lanewin
  rcases (show n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 by omega)
    with hr | hr | hr | hr | hr
  · rw [if_pos hr, s5b0_val _ _ (by rw [b0]; omega) (by rw [b1]; omega), b0, b1,
      show 8 * n / 5 = 8 * m from by omega, show 8 * n % 5 = 0 from by omega]
    all_goals simp only [Nat.add_assoc, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow]
    all_goals omega
  · rw [if_neg (by omega), if_pos hr,
      s5b1_val _ _ _ (by rw [b1]; omega) (by rw [b2]; omega) (by rw [b3]; omega), b1, b2, b3,
      show 8 * n / 5 = 8 * m + 1 from by omega, show 8 * n % 5 = 3 from by omega]
    all_goals simp only [Nat.add_assoc, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow]
    all_goals omega
  · rw [if_neg (by omega), if_neg (by omega), if_pos hr,
      s5b2_val _ _ (by rw [b3]; omega) (by rw [b4]; omega), b3, b4,
      show 8 * n / 5 = 8 * m + 3 from by omega, show 8 * n % 5 = 1 from by omega]
    all_goals simp only [Nat.add_assoc, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow]
    all_goals omega
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hr,
      s5b3_val _ _ _ (by rw [b4]; omega) (by rw [b5]; omega) (by rw [b6]; omega), b4, b5, b6,
      show 8 * n / 5 = 8 * m + 4 from by omega, show 8 * n % 5 = 4 from by omega]
    all_goals simp only [Nat.add_assoc, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow]
    all_goals omega
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      s5b4_val _ _ (by rw [b6]; omega) (by rw [b7]; omega), b6, b7,
      show 8 * n / 5 = 8 * m + 6 from by omega, show 8 * n % 5 = 2 from by omega]
    all_goals simp only [Nat.add_assoc, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow]
    all_goals omega

/-! ### The vector-level COMPRESS seam, generic in `d`.

    CITES `compress_ciphertext_coefficient_eq` (M-C′(2)) per lane and lifts it over the
    16-lane loop with `LoopHelper.elementwise_unary_spec`; no new loop reasoning, the
    extracted body IS `unary_loop_body` once the two total casts are rewritten. -/

private theorem as_i16_id (x : Std.I16) :
    libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_i16 x = .ok x := rfl

/-- `to_unsigned_field_modulus` IS `to_unsigned_representative` (a one-statement `do`), so
    `to_unsigned_fm_eq` serves both arms — the `d = 4` body calls the former and the
    `d = 5` body the latter. -/
private theorem tufm_eq_tur
    (a out : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    libcrux_iot_ml_kem.serialize.to_unsigned_field_modulus
      (vectortraitsOperationsInst := portable_ops_inst) a out
    = libcrux_iot_ml_kem.vector.traits.to_unsigned_representative portable_ops_inst a out := rfl

private def cccb (d : Std.U8) (x : Std.I16) : RustM Std.I16 := do
  let u ← libcrux_secrets.I16.Insts.Libcrux_secretsIntCastOps.as_u16 x
  libcrux_iot_ml_kem.vector.portable.compress.compress_ciphertext_coefficient d u

private theorem cccb_spec (d : Std.U8) (hd : d.val < 12) (x : Std.I16) :
    ∃ r : Std.I16, cccb d x = .ok r
      ∧ r.bv.toNat = (((x.bv.toNat * 2 ^ d.val + 1664) * 10321340) / 2 ^ 35) % 2 ^ d.val
      ∧ r.bv.toNat < 2 ^ d.val := by
  obtain ⟨r, hr_eq, hrv, hr0, hrlt⟩ := compress_ciphertext_coefficient_eq d (cu16 x) hd
  rw [cu16_val x] at hrv
  have hlt16 := i16_toNat_lt r
  have hbn : r.bv.toNat = r.val.toNat := by
    rcases i16_msb_cases r with ⟨_, hn, hv⟩ | ⟨_, hn, hv⟩ <;> omega
  have hcast : ((2:Int) ^ d.val) = ((2 ^ d.val : Nat) : Int) := by push_cast; ring
  rw [hcast] at hrlt
  refine ⟨r, ?_, ?_, ?_⟩
  · unfold cccb
    rw [as_u16_eq]; simp only [Aeneas.Std.bind_tc_ok]
    exact hr_eq
  · rw [hbn, hrv]
  · rw [hbn]; omega

private theorem compress_body_eq (CB : Std.I32)
    (iter : CoreModels.core.ops.range.Range Std.Usize)
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    libcrux_iot_ml_kem.vector.portable.compress.compress_loop.body CB iter v
      = libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.unary_loop_body
          (cccb (Std.IScalar.hcast .U8 CB)) iter v := by
  unfold libcrux_iot_ml_kem.vector.portable.compress.compress_loop.body
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.unary_loop_body cccb
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok, as_u16_eq, as_i16_id]
  rfl

private theorem compress_vec_eq (CB : Std.I32) (dn : Nat)
    (hCB : (Std.IScalar.hcast .U8 CB : Std.U8).val = dn) (hd : dn < 12)
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ∃ r : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector,
      libcrux_iot_ml_kem.vector.portable.compress.compress CB v = .ok r
      ∧ ∀ l : Nat, l < 16 →
          (r.elements.val[l]!).bv.toNat
            = ((((v.elements.val[l]!).bv.toNat * 2 ^ dn + 1664) * 10321340) / 2 ^ 35)
              % 2 ^ dn := by
  have hloop : libcrux_iot_ml_kem.vector.portable.compress.compress CB v
      = loop (fun p => libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.unary_loop_body
                (cccb (Std.IScalar.hcast .U8 CB)) p.1 p.2)
          (({ start := 0#usize, «end» := 16#usize }
              : CoreModels.core.ops.range.Range Std.Usize), v) := by
    have hFEV : (libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR : Std.Usize)
        = (16#usize : Std.Usize) :=
      Std.UScalar.eq_of_val_eq (by
        rw [libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.field_elements_in_vector_val]
        scalar_tac)
    have h1 : ∀ (iter1 : CoreModels.core.ops.range.Range Std.Usize)
        (a1 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector),
        libcrux_iot_ml_kem.vector.portable.compress.compress_loop.body CB iter1 a1
          = libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.unary_loop_body
              (cccb (Std.IScalar.hcast .U8 CB)) iter1 a1 :=
      fun i a => compress_body_eq CB i a
    unfold libcrux_iot_ml_kem.vector.portable.compress.compress
    rw [hFEV]
    unfold libcrux_iot_ml_kem.vector.portable.compress.compress_loop
    simp only [h1]
  obtain ⟨r, hr_eq, hr⟩ := triple_exists_ok_fc
    (libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.elementwise_unary_spec
      (cccb (Std.IScalar.hcast .U8 CB))
      (fun x y => y.bv.toNat = (((x.bv.toNat * 2 ^ dn + 1664) * 10321340) / 2 ^ 35) % 2 ^ dn)
      (fun x => by
        obtain ⟨y, hy_eq, hy1, hy2⟩ := cccb_spec _ (by rw [hCB]; exact hd) x
        rw [hCB] at hy1
        exact triple_of_ok_fc hy_eq hy1)
      v)
  refine ⟨r, by rw [hloop]; exact hr_eq, ?_⟩
  intro l hl
  obtain ⟨ri, _, hri, hP⟩ := hr l hl
  rw [hri]; exact hP

/-! ### The two 16-iteration range loops. Written-prefix invariant; the
    undone-cells-unchanged conjunct is discharged by the `setSlice!` prefix lemma, exactly
    as in `serialize_uncompressed_loop_fc`. -/

private def cInv (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (d C2 : Nat) (k : Std.Usize)
    (acc : Slice Std.U8 × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    RustM Prop :=
  pure (acc.1.val.length = C2 ∧
        ∀ n : Nat, n < 2 * d * k.val → (acc.1.val[n]!).val = cByte re d n)

private theorem vectors_in_ring_element_eq :
    libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT = .ok (16#usize : Std.Usize) := by
  have hdivlit : ∀ x y z : Std.Usize, y.val ≠ 0 → x.val / y.val = z.val →
      (x / y : RustM Std.Usize) = .ok z := by
    intro x y z hy hz
    obtain ⟨q, hq_eq, hq_val⟩ := Std.UScalar.div_spec x (y := y) hy
    rw [hq_eq]
    congr 1
    exact Std.UScalar.eq_of_val_eq (by rw [hq_val, hz])
  unfold libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
    libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
    libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
  exact hdivlit _ _ _ (by scalar_tac) (by scalar_tac)

set_option maxHeartbeats 4000000 in
private theorem L54_loop_4_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hbnd : ∀ c : Nat, c < 16 → ∀ l : Nat, l < 16 →
      ((re.coefficients.val[c]!).elements.val[l]!).val.natAbs ≤ 3328)
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 128)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.compress_then_serialize_4_loop
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := 0#usize, «end» := 16#usize } re serialized scratch
    ⦃ ⇓ p => ⌜ (cInv re 4 128 16#usize p).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_4_loop
  refine libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
    (fun (iter1, serialized1, scratch1) =>
      libcrux_iot_ml_kem.serialize.compress_then_serialize_4_loop.body
        (vectortraitsOperationsInst := portable_ops_inst) re iter1 serialized1 scratch1)
    (serialized, scratch) 0#usize 16#usize (cInv re 4 128) (by scalar_tac) ?_ ?_
  · show (pure _ : RustM Prop).holds
    simp only [Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp]
    intro _
    exact ⟨h_len, by intro n hn; exact absurd hn (by scalar_tac)⟩
  · intro acc k hk0 hk16 hinv
    have h16 : (16#usize : Std.Usize).val = 16 := rfl
    obtain ⟨hacc_len, hacc_done⟩ : acc.1.val.length = 128 ∧
        ∀ n : Nat, n < 2 * 4 * k.val → (acc.1.val[n]!).val = cByte re 4 n := by
      have hh := hinv
      simp only [cInv, Aeneas.Std.RustM.holds, pure, Pure.pure, Std.Do.Triple,
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
        to_unsigned_fm_eq (re.coefficients.val[k.val]!) acc.2
          (fun l hl => hbnd k.val hlt l hl)
      have hlanes : ∀ l : Nat, l < 16 →
          (sc1.elements.val[l]!).bv.toNat = encLane re (16 * k.val + l) := by
        intro l hl
        obtain ⟨hb0, hb1, hb2⟩ := hsc1 l hl
        exact uval_encLane re k.val l hlt hl _ hb0 hb1 hb2
      obtain ⟨sc2, hsc2_eq, hsc2⟩ :=
        compress_vec_eq (4#i32) 4 (by decide) (by omega) sc1
      have hclanes : ∀ l : Nat, l < 16 →
          (sc2.elements.val[l]!).bv.toNat = cLane re 4 (16 * k.val + l) := by
        intro l hl
        rw [hsc2 l hl, hlanes l hl]
        unfold cLane
        rw [compress_barrett_eq (encLane re (16 * k.val + l)) 4
          (encLane_lt re (16 * k.val + l)) (by omega)]
      obtain ⟨i1, hi1_eq, hi1⟩ := usize_mul_ok_e (8#usize : Std.Usize) k (by scalar_tac)
      obtain ⟨i2, hi2_eq, hi2⟩ := usize_add_ok_e i1 (8#usize : Std.Usize) (by scalar_tac)
      have hi1v : i1.val = 8 * k.val := by rw [hi1]; scalar_tac
      have hi2v : i2.val = 8 * k.val + 8 := by rw [hi2, hi1v]; scalar_tac
      obtain ⟨sub, wb, hmut_eq, hsub_len, hwb⟩ :=
        slice_index_mut_range_strict acc.1 i1 i2 (by omega) (by rw [hacc_len]; omega)
      have hsub8 : sub.val.length = 8 := by rw [hsub_len]; omega
      have hser4 := serialize_4_eq sc2 sub hsub8
      refine libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.triple_of_ok_fc
        (v := .cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize), (wb (s4set sc2 sub), sc2))) ?_ ?_
      · show libcrux_iot_ml_kem.serialize.compress_then_serialize_4_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) re
          { start := k, «end» := 16#usize } acc.1 acc.2 = _
        unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_4_loop.body
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
                             portable_ops_inst t acc.2
            let scratch2 ← libcrux_iot_ml_kem.vector.portable.compress.compress
                             (4#i32 : Std.I32) scratch1
            let i1' ← (8#usize : Std.Usize) * k
            let i2' ← i1' + (8#usize : Std.Usize)
            let (sb, index_mut_back) ←
              CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
                (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                  Std.U8) acc.1 { start := i1', «end» := i2' }
            let s1 ← libcrux_iot_ml_kem.vector.portable.serialize.serialize_4 scratch2 sb
            RustM.ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
              (index_mut_back s1, scratch2)))) = _
        rw [h_idx]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hsc1_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hsc2_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hi1_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hi2_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hmut_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hser4]
        rfl
      · refine ⟨by rw [h16]; exact hlt, rfl, hs_val, ?_⟩
        show (cInv re 4 128 s (wb (s4set sc2 sub), sc2)).holds
        simp only [cInv, Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        have hwbv := hwb (s4set sc2 sub) (by rw [s4set_length sc2 sub hsub8]; omega)
        refine ⟨?_, ?_⟩
        · rw [hwbv, List.length_setSlice!]; exact hacc_len
        · intro n hn
          rw [hs_val] at hn
          rw [hwbv]
          by_cases hnk : n < 2 * 4 * k.val
          · rw [List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]
            exact hacc_done n hnk
          · rw [List.getElem!_setSlice!_middle _ _ _ _
              ⟨by omega, by rw [s4set_length sc2 sub hsub8]; omega,
               by rw [hacc_len]; omega⟩]
            rw [hi1v, s4set_get sc2 sub hsub8 (n - 8 * k.val) (by omega),
              v4byte_val sc2 (fun j => cLane re 4 (16 * k.val + j)) hclanes
                (fun i => by
                  have := cLane_lt re 4 (16 * k.val + i)
                  simpa using this)
                (n - 8 * k.val) (by omega),
              lanewin_shift re 4 k.val (n - 8 * k.val) (by omega)]
            congr 1
            omega
    · have hk : k.val = 16 := by omega
      refine libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.triple_of_ok_fc
        (v := .done acc) ?_ ?_
      · show libcrux_iot_ml_kem.serialize.compress_then_serialize_4_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) re
          { start := k, «end» := 16#usize } acc.1 acc.2 = _
        unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_4_loop.body
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
      · show (cInv re 4 128 16#usize acc).holds
        simp only [cInv, Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        exact ⟨hacc_len, by intro n hn; exact hacc_done n (by rw [hk]; rw [h16] at hn; omega)⟩

private theorem L54_impl_4_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hbnd : ∀ c : Nat, c < 16 → ∀ l : Nat, l < 16 →
      ((re.coefficients.val[c]!).elements.val[l]!).val.natAbs ≤ 3328)
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 128)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.compress_then_serialize_4
      (vectortraitsOperationsInst := portable_ops_inst) re serialized scratch
    ⦃ ⇓ p => ⌜ (cInv re 4 128 16#usize p).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_4
  rw [vectors_in_ring_element_eq]; simp only [Aeneas.Std.bind_tc_ok]
  exact L54_loop_4_fc re hbnd serialized h_len scratch

set_option maxHeartbeats 4000000 in
private theorem L54_loop_5_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hbnd : ∀ c : Nat, c < 16 → ∀ l : Nat, l < 16 →
      ((re.coefficients.val[c]!).elements.val[l]!).val.natAbs ≤ 3328)
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 160)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.compress_then_serialize_5_loop
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := 0#usize, «end» := 16#usize } re serialized scratch
    ⦃ ⇓ p => ⌜ (cInv re 5 160 16#usize p).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_5_loop
  refine libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
    (fun (iter1, serialized1, scratch1) =>
      libcrux_iot_ml_kem.serialize.compress_then_serialize_5_loop.body
        (vectortraitsOperationsInst := portable_ops_inst) re iter1 serialized1 scratch1)
    (serialized, scratch) 0#usize 16#usize (cInv re 5 160) (by scalar_tac) ?_ ?_
  · show (pure _ : RustM Prop).holds
    simp only [Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp]
    intro _
    exact ⟨h_len, by intro n hn; exact absurd hn (by scalar_tac)⟩
  · intro acc k hk0 hk16 hinv
    have h16 : (16#usize : Std.Usize).val = 16 := rfl
    obtain ⟨hacc_len, hacc_done⟩ : acc.1.val.length = 160 ∧
        ∀ n : Nat, n < 2 * 5 * k.val → (acc.1.val[n]!).val = cByte re 5 n := by
      have hh := hinv
      simp only [cInv, Aeneas.Std.RustM.holds, pure, Pure.pure, Std.Do.Triple,
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
        to_unsigned_fm_eq (re.coefficients.val[k.val]!) acc.2
          (fun l hl => hbnd k.val hlt l hl)
      have hlanes : ∀ l : Nat, l < 16 →
          (sc1.elements.val[l]!).bv.toNat = encLane re (16 * k.val + l) := by
        intro l hl
        obtain ⟨hb0, hb1, hb2⟩ := hsc1 l hl
        exact uval_encLane re k.val l hlt hl _ hb0 hb1 hb2
      obtain ⟨sc2, hsc2_eq, hsc2⟩ :=
        compress_vec_eq (5#i32) 5 (by decide) (by omega) sc1
      have hclanes : ∀ l : Nat, l < 16 →
          (sc2.elements.val[l]!).bv.toNat = cLane re 5 (16 * k.val + l) := by
        intro l hl
        rw [hsc2 l hl, hlanes l hl]
        unfold cLane
        rw [compress_barrett_eq (encLane re (16 * k.val + l)) 5
          (encLane_lt re (16 * k.val + l)) (by omega)]
      obtain ⟨i1, hi1_eq, hi1⟩ := usize_mul_ok_e (10#usize : Std.Usize) k (by scalar_tac)
      obtain ⟨i2, hi2_eq, hi2⟩ := usize_add_ok_e i1 (10#usize : Std.Usize) (by scalar_tac)
      have hi1v : i1.val = 10 * k.val := by rw [hi1]; scalar_tac
      have hi2v : i2.val = 10 * k.val + 10 := by rw [hi2, hi1v]; scalar_tac
      obtain ⟨sub, wb, hmut_eq, hsub_len, hwb⟩ :=
        slice_index_mut_range_strict acc.1 i1 i2 (by omega) (by rw [hacc_len]; omega)
      have hsub10 : sub.val.length = 10 := by rw [hsub_len]; omega
      have hser5 := serialize_5_eq sc2 sub hsub10
      refine libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.triple_of_ok_fc
        (v := .cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize), (wb (s5set sc2 sub), sc2))) ?_ ?_
      · show libcrux_iot_ml_kem.serialize.compress_then_serialize_5_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) re
          { start := k, «end» := 16#usize } acc.1 acc.2 = _
        unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_5_loop.body
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
            let scratch1 ← libcrux_iot_ml_kem.vector.traits.to_unsigned_representative
                             portable_ops_inst t acc.2
            let scratch2 ← libcrux_iot_ml_kem.vector.portable.compress.compress
                             (5#i32 : Std.I32) scratch1
            let i1' ← (10#usize : Std.Usize) * k
            let i2' ← i1' + (10#usize : Std.Usize)
            let (sb, index_mut_back) ←
              CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
                (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                  Std.U8) acc.1 { start := i1', «end» := i2' }
            let s1 ← libcrux_iot_ml_kem.vector.portable.serialize.serialize_5 scratch2 sb
            RustM.ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
              (index_mut_back s1, scratch2)))) = _
        rw [h_idx]; simp only [Aeneas.Std.bind_tc_ok]
        rw [← tufm_eq_tur (re.coefficients.val[k.val]!) acc.2, hsc1_eq]
        simp only [Aeneas.Std.bind_tc_ok]
        rw [hsc2_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hi1_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hi2_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hmut_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hser5]
        rfl
      · refine ⟨by rw [h16]; exact hlt, rfl, hs_val, ?_⟩
        show (cInv re 5 160 s (wb (s5set sc2 sub), sc2)).holds
        simp only [cInv, Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        have hwbv := hwb (s5set sc2 sub) (by rw [s5set_length sc2 sub hsub10]; omega)
        refine ⟨?_, ?_⟩
        · rw [hwbv, List.length_setSlice!]; exact hacc_len
        · intro n hn
          rw [hs_val] at hn
          rw [hwbv]
          by_cases hnk : n < 2 * 5 * k.val
          · rw [List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]
            exact hacc_done n hnk
          · rw [List.getElem!_setSlice!_middle _ _ _ _
              ⟨by omega, by rw [s5set_length sc2 sub hsub10]; omega,
               by rw [hacc_len]; omega⟩]
            rw [hi1v, s5set_get sc2 sub hsub10 (n - 10 * k.val) (by omega),
              v5byte_val sc2 (fun j => cLane re 5 (16 * k.val + j)) hclanes
                (fun i => by
                  have := cLane_lt re 5 (16 * k.val + i)
                  simpa using this)
                (n - 10 * k.val) (by omega),
              lanewin_shift re 5 k.val (n - 10 * k.val) (by omega)]
            congr 1
            omega
    · have hk : k.val = 16 := by omega
      refine libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.triple_of_ok_fc
        (v := .done acc) ?_ ?_
      · show libcrux_iot_ml_kem.serialize.compress_then_serialize_5_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) re
          { start := k, «end» := 16#usize } acc.1 acc.2 = _
        unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_5_loop.body
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
      · show (cInv re 5 160 16#usize acc).holds
        simp only [cInv, Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        exact ⟨hacc_len, by intro n hn; exact hacc_done n (by rw [hk]; rw [h16] at hn; omega)⟩

private theorem L54_impl_5_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hbnd : ∀ c : Nat, c < 16 → ∀ l : Nat, l < 16 →
      ((re.coefficients.val[c]!).elements.val[l]!).val.natAbs ≤ 3328)
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 160)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.compress_then_serialize_5
      (vectortraitsOperationsInst := portable_ops_inst) re serialized scratch
    ⦃ ⇓ p => ⌜ (cInv re 5 160 16#usize p).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_5
  rw [vectors_in_ring_element_eq]; simp only [Aeneas.Std.bind_tc_ok]
  exact L54_loop_5_fc re hbnd serialized h_len scratch

/-! ### SPEC side, generic in `d`.

    Four levels, as in the `d = 12` and `d = 1` banks: `compress.compress`'s `createi`,
    `byte_encode`'s `createi`, `bitvector_from_bounded_ints`, `bits_to_bytes`.  Levels 1
    and 4 are already generic in the tree (`byte_encode_closure_eq_gen`,
    `bits_to_bytes_closure_eq_gen`); levels 0 and 2 are generalised here off `d = 1` /
    `d = 12` and then instantiated twice. -/

/-- The spec-side compressed coefficient at lane `k`. -/
private def cFe (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) (d k : Nat) :
    hacspec_ml_kem.parameters.FieldElement :=
  { val := u16OfNat (cLane re d k) }

private theorem cLane_le_u16 (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (d : Nat) (hd : d < 12) (k : Nat) : cLane re d k ≤ Std.U16.max := by
  have h1 := cLane_lt re d k
  have h2 : (2:Nat) ^ d ≤ 2048 := by
    calc (2:Nat) ^ d ≤ 2 ^ 11 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 2048 := by norm_num
  have h3 : Std.U16.max = 65535 := by scalar_tac
  omega

/-- **Level 0**, generic in `d`: `compress.compress`'s closure at `p = lift_poly re` is
    exactly `cLane`.  CITES M-C′(3) `compress_d_gen_eq` for the per-coefficient step. -/
private theorem compress_v_closure_eq
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (d : Std.Usize) (hd : d.val < 12) (k : Nat) (hk : k < 256) :
    (hacspec_ml_kem.compress.compress.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement).call_mut
        (lift_poly re, d) ⟨BitVec.ofNat _ k⟩
      = .ok (cFe re d.val k, (lift_poly re, d)) := by
  have hkv : ((⟨BitVec.ofNat _ k⟩ : Std.Usize)).val = k :=
    enc_usize_ofNat_val k (by omega)
  have hlen : (lift_poly re).val.length = 256 := by
    have := (lift_poly re).property; simpa using this
  show (do
      let fe ← Aeneas.Std.Array.index_usize (lift_poly re) (⟨BitVec.ofNat _ k⟩ : Std.Usize)
      let fe1 ← hacspec_ml_kem.compress.compress_d fe d
      RustM.ok (fe1, ((lift_poly re, d) : hacspec_ml_kem.compress.compress.closure))) = _
  rw [enc_array_index_ok (lift_poly re) _ (by rw [hkv, hlen]; exact hk), hkv]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [compress_d_gen_eq ((lift_poly re).val[k]!) d hd]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [lift_poly_raw re k hk]
  unfold cFe cLane
  rfl

/-- **Level 0, assembled.** -/
private theorem compress_v_get
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (d : Std.Usize) (hd : d.val < 12) :
    ∃ a : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize,
      hacspec_ml_kem.compress.compress (lift_poly re) d = .ok a
      ∧ ∀ k : Nat, k < 256 → ((a.val[k]!).val).val = cLane re d.val k := by
  have h256 : ((256#usize : Std.Usize)).val = 256 := by scalar_tac
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
      (T := hacspec_ml_kem.parameters.FieldElement) (256#usize : Std.Usize)
      (hacspec_ml_kem.compress.compress.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement)
      (lift_poly re, d)
      (fun k => cFe re d.val k)
      (fun k hk => compress_v_closure_eq re d hd k (by rw [h256] at hk; exact hk))
  unfold hacspec_ml_kem.compress.compress
  simp only [hacspec_ml_kem.parameters.createi]
  rw [hfn]
  refine ⟨_, rfl, ?_⟩
  intro k hk
  rw [enc_mk_getElem (by rw [h256]; exact hk)]
  show ((cFe re d.val k).val).val = _
  unfold cFe
  exact u16OfNat_val _ (cLane_le_u16 re d.val hd k)

/-- **Level 2**, generic in `d`: `bitvector_from_bounded_ints`'s closure.  The `d = 12`
    bank states this at `d = 12` and the `d = 1` bank at `d = 1`; the body never mentions
    the width, so one statement in `d` serves every rung. -/
private theorem bvfb_closure_eq_gen {Nd : Std.Usize} (a : Std.Array Std.U16 256#usize)
    (d : Std.Usize) (m : Nat) (hm32 : m < 2 ^ 32) (hd0 : 0 < d.val) (hd16 : d.val < 16)
    (hidx : m / d.val < 256) :
    (hacspec_ml_kem.serialize.bitvector_from_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBool
        (256#usize : Std.Usize) Nd).call_mut (a, d) ⟨BitVec.ofNat _ m⟩
      = .ok (natBit ((a.val[m / d.val]!).val) (m % d.val), (a, d)) := by
  have hmv : ((⟨BitVec.ofNat _ m⟩ : Std.Usize)).val = m := enc_usize_ofNat_val m hm32
  have hlen : a.val.length = 256 := by have := a.property; simpa using this
  obtain ⟨q, hq_eq, hq_val⟩ :=
    Std.UScalar.div_spec (⟨BitVec.ofNat _ m⟩ : Std.Usize) (y := d) (by omega)
  obtain ⟨r, hr_eq, hr_val⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.rem_spec (⟨BitVec.ofNat _ m⟩ : Std.Usize)
      (y := d) (by omega))
  have hqv : q.val = m / d.val := by rw [hq_val, hmv]
  have hrv : r.val = m % d.val := by rw [hr_val, hmv]
  -- `% d.val` by a VARIABLE modulus is out of `omega`'s reach; supply it once.
  have hmod : m % d.val < d.val := Nat.mod_lt _ (by omega)
  obtain ⟨y, hy_eq, hy⟩ := u16_shr_and1_eq (a.val[q.val]!) r (by rw [hrv]; omega)
  show (do
      let i1 ← (⟨BitVec.ofNat _ m⟩ : Std.Usize) / d
      let i2 ← Aeneas.Std.Array.index_usize a i1
      let i3 ← (⟨BitVec.ofNat _ m⟩ : Std.Usize) % d
      let i4 ← i2 >>> i3
      let i5 ← Aeneas.Std.lift (i4 &&& 1#u16)
      RustM.ok (decide (i5 = 1#u16),
        ((a, d) :
          hacspec_ml_kem.serialize.bitvector_from_bounded_ints.closure
            (256#usize : Std.Usize) Nd))) = _
  rw [hq_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [enc_array_index_ok a q (by rw [hqv, hlen]; omega)]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hr_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hy_eq]; simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hy, hqv, hrv]
  rfl

/-- **Level 2, assembled**: the `256 * d` booleans are exactly `cBit re d`. -/
private theorem bvfb_get_gen
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (d Nd : Std.Usize) (hd0 : 0 < d.val) (hd16 : d.val < 16) (hNd : Nd.val = 256 * d.val)
    (p_raw : Std.Array Std.U16 256#usize)
    (hp : ∀ k : Nat, k < 256 → (p_raw.val[k]!).val = cLane re d.val k) :
    ∃ bv : Std.Array Bool Nd,
      hacspec_ml_kem.serialize.bitvector_from_bounded_ints (N := 256#usize) Nd p_raw d
        = .ok bv
      ∧ ∀ m : Nat, m < Nd.val → bv.val[m]! = cBit re d.val m := by
  have hmul : ((256#usize : Std.Usize) * d : RustM Std.Usize) = .ok Nd :=
    usize_mul_lit _ _ _ (by rw [hNd]; scalar_tac) (by scalar_tac)
  -- division by a VARIABLE modulus, again out of `omega`'s reach: stated once.
  have hdiv : ∀ m : Nat, m < Nd.val → m / d.val < 256 := by
    intro m hm
    rw [hNd] at hm
    exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq (T := Bool) Nd
      (hacspec_ml_kem.serialize.bitvector_from_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBool
        (256#usize : Std.Usize) Nd) (p_raw, d)
      (fun m => natBit ((p_raw.val[m / d.val]!).val) (m % d.val))
      (fun m hm => bvfb_closure_eq_gen p_raw d m (by omega) hd0 hd16 (hdiv m hm))
  have key : hacspec_ml_kem.serialize.bitvector_from_bounded_ints (N := 256#usize) Nd p_raw d
      = CoreModels.core.array.from_fn Nd
          (hacspec_ml_kem.serialize.bitvector_from_bounded_ints.closure.Insts.CoreOpsFunctionFnMutTupleUsizeBool
            (256#usize : Std.Usize) Nd) (p_raw, d) := by
    unfold hacspec_ml_kem.serialize.bitvector_from_bounded_ints
    -- hax v0.4.0-rc.1 no longer emits the `let i ← N * 8#usize; massert (N8 = i)` prelude
    -- (ALL 74 spec-side `massert`s are gone from the extraction), so the length check and
    -- its `hmul` witness are no longer part of this equation.
    simp only [hacspec_ml_kem.parameters.createi]
  rw [key, hfn]
  refine ⟨_, rfl, ?_⟩
  intro m hm
  rw [enc_mk_getElem hm]
  show natBit ((p_raw.val[m / d.val]!).val) (m % d.val) = cBit re d.val m
  unfold cBit
  rw [hp (m / d.val) (hdiv m hm)]

/-- **Level 3**, generic in the two width params. -/
private theorem bits_to_bytes_get_gen (N N8 : Std.Usize) (hN8 : N8.val = N.val * 8)
    (hmax : N.val * 8 ≤ Std.Usize.max) (hN32 : N.val < 2 ^ 32) (bv : Std.Array Bool N8) :
    ∃ out : Std.Array Std.U8 N,
      hacspec_ml_kem.serialize.bits_to_bytes N (N8 := N8) bv = .ok out
      ∧ ∀ n : Nat, n < N.val →
          (out.val[n]!).val = bitSum (fun t => bv.val[8 * n + t]!) 8 := by
  have hmul : (N * (8#usize : Std.Usize) : RustM Std.Usize) = .ok N8 :=
    usize_mul_lit _ _ _ (by rw [hN8]; scalar_tac) (by scalar_tac)
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq (T := Std.U8) N
      (hacspec_ml_kem.serialize.bits_to_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
        N N8) bv
      (fun n => u8OfNat (bitSum (fun t => bv.val[8 * n + t]!) 8))
      (fun n hn => bits_to_bytes_closure_eq_gen bv n
        (by rw [hN8]; omega) (by omega) (by omega))
  have key : hacspec_ml_kem.serialize.bits_to_bytes N (N8 := N8) bv
      = CoreModels.core.array.from_fn N
          (hacspec_ml_kem.serialize.bits_to_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
            N N8) bv := by
    unfold hacspec_ml_kem.serialize.bits_to_bytes
    -- hax v0.4.0-rc.1 no longer emits the `let i ← N * 8#usize; massert (N8 = i)` prelude
    -- (ALL 74 spec-side `massert`s are gone from the extraction), so the length check and
    -- its `hmul` witness are no longer part of this equation.
    simp only [hacspec_ml_kem.parameters.createi]
  rw [key, hfn]
  refine ⟨_, rfl, ?_⟩
  intro n hn
  rw [enc_mk_getElem hn]
  exact u8OfNat_val _ (by have := bitSum_lt (fun t => bv.val[8 * n + t]!) 8; simpa using this)

/-- **The spec-side `byte_encode` apex, generic in `d ∈ [4, 12]`.** The three `createi`
    levels normalised onto `bitSum_cBit_eq_cByte`, i.e. onto M-C(2). -/
theorem byte_encode_gen_eq
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (D32 D256 d : Std.Usize) (hd4 : 4 ≤ d.val) (hd12 : d.val ≤ 12)
    (hD32 : D32.val = 32 * d.val) (hD256 : D256.val = 256 * d.val)
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (ha : ∀ k : Nat, k < 256 → ((a.val[k]!).val).val = cLane re d.val k) :
    ∃ out : Std.Array Std.U8 D32,
      hacspec_ml_kem.serialize.byte_encode D32 D256 a d = .ok out
      ∧ ∀ n : Nat, n < D32.val → (out.val[n]!).val = cByte re d.val n := by
  have h256 : ((256#usize : Std.Usize)).val = 256 := by scalar_tac
  have hfn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq (T := Std.U16)
      (256#usize : Std.Usize)
      (hacspec_ml_kem.serialize.byte_encode.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16
        D32 D256) a
      (fun k => (a.val[k]!).val)
      (fun k hk => byte_encode_closure_eq_gen a k (by rw [h256] at hk; exact hk))
  obtain ⟨p_raw, hp_raw', hp_get⟩ :
      ∃ p_raw : Std.Array Std.U16 256#usize,
        hacspec_ml_kem.parameters.createi (256#usize : Std.Usize)
            (hacspec_ml_kem.serialize.byte_encode.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU16
              D32 D256) a = .ok p_raw
        ∧ ∀ k : Nat, k < 256 → (p_raw.val[k]!).val = cLane re d.val k := by
    simp only [hacspec_ml_kem.parameters.createi]
    rw [hfn]
    refine ⟨_, rfl, ?_⟩
    intro k hk
    rw [enc_mk_getElem (by rw [h256]; exact hk)]
    exact ha k hk
  obtain ⟨bv, hbv, hbv_get⟩ :=
    bvfb_get_gen re d D256 (by omega) (by omega) hD256 p_raw hp_get
  obtain ⟨out, hout, hout_get⟩ :=
    bits_to_bytes_get_gen D32 D256 (by rw [hD32, hD256]; ring)
      (by have h1 : D32.val ≤ 384 := by rw [hD32]; omega
          have h2 : (3072 : Nat) ≤ Std.Usize.max := by scalar_tac
          omega)
      (by rw [hD32]; omega) bv
  have e1 : ((32#usize : Std.Usize) * d : RustM Std.Usize) = .ok D32 :=
    usize_mul_lit _ _ _ (by rw [hD32]; scalar_tac) (by scalar_tac)
  have e2 : ((256#usize : Std.Usize) * d : RustM Std.Usize) = .ok D256 :=
    usize_mul_lit _ _ _ (by rw [hD256]; scalar_tac) (by scalar_tac)
  have hass : (d ≤ (12#usize : Std.Usize)) := by scalar_tac
  refine ⟨out, ?_, ?_⟩
  · unfold hacspec_ml_kem.serialize.byte_encode
    simp only [hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT, Aeneas.Std.massert,
      if_pos hass, Aeneas.Std.bind_tc_ok, e1, e2, eq_self_iff_true, if_true,
      hp_raw', hbv, hout]
  · intro n hn
    rw [hout_get n hn,
      bitSum_congr _ (fun t => cBit re d.val (8 * n + t)) 8
        (fun t ht => hbv_get (8 * n + t) (by rw [hD256]; rw [hD32] at hn; omega))]
    exact bitSum_cBit_eq_cByte re d.val hd4 n

/-- The `byte_encode_into` slice wrapper at `dv ∈ {4,5}` — the spec dispatches on
    `dv.val` and each arm is `byte_encode_gen_eq` plus `to_slice`/`copy_from_slice`. -/
theorem byte_encode_into_45_eq
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (dv : Std.Usize) (hdv : dv.val = 4 ∨ dv.val = 5)
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (ha : ∀ k : Nat, k < 256 → ((a.val[k]!).val).val = cLane re dv.val k)
    (out : Slice Std.U8) (h_len : out.val.length = 32 * dv.val) :
    ∃ s : Slice Std.U8,
      hacspec_ml_kem.serialize.byte_encode_into a dv out = .ok s
      ∧ s.val.length = 32 * dv.val
      ∧ ∀ n : Nat, n < 32 * dv.val → (s.val[n]!).val = cByte re dv.val n := by
  have hcopy : ∀ (D32 : Std.Usize) (enc : Std.Array Std.U8 D32),
      D32.val = 32 * dv.val →
      CoreModels.core.slice.Slice.copy_from_slice CoreModels.core.U8.Insts.CoreMarkerCopy out
          (Aeneas.Std.Array.to_slice enc)
        = .ok (Aeneas.Std.Array.to_slice enc) := by
    intro D32 enc hD32
    have hlen_enc : (Aeneas.Std.Array.to_slice enc).val.length = 32 * dv.val := by
      show enc.val.length = _
      have := enc.property; rw [show enc.val.length = D32.val from by simpa using this, hD32]
    -- `copy_from_slice` now routes through `rust_primitives.slice.slice_clone_from_slice`
    -- (a `mapM clone` over the source); the `Util.SliceSpecs` bridge collapses it for a
    -- `Copy` instance whose `clone` is the identity, and needs the raw length equality.
    exact libcrux_iot_ml_kem.Util.SliceSpecs.core_models_slice_Slice_copy_from_slice_eq
      _ out (Aeneas.Std.Array.to_slice enc) (by rw [h_len, hlen_enc]) (by intro x; rfl)
  rcases hdv with h4 | h5
  · have hdveq : dv = 4#usize := Aeneas.Std.UScalar.eq_of_val_eq (by scalar_tac)
    subst hdveq
    obtain ⟨enc, henc, henc_get⟩ :=
      byte_encode_gen_eq re (128#usize) (1024#usize) (4#usize) (by scalar_tac) (by scalar_tac)
        (by scalar_tac) (by scalar_tac) a ha
    refine ⟨Aeneas.Std.Array.to_slice enc, ?_, ?_, ?_⟩
    · unfold hacspec_ml_kem.serialize.byte_encode_into
      simp only [hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT, Aeneas.Std.massert,
        Aeneas.Std.bind_tc_ok, Aeneas.Std.lift,
        show ((4#usize : Std.Usize).val) = 4 from rfl, henc]
      -- (`byte_encode_into`'s `massert (d ≤ BITS_PER_COEFFICIENT)` and
      --  `massert (out.len = 32 * d)` prelude is gone from the hax v0.4.0-rc.1
      --  extraction, so the length/bound stepping that stood here is unnecessary)
      exact hcopy (128#usize) enc (by scalar_tac)
    · show enc.val.length = _
      have := enc.property
      rw [show enc.val.length = ((128#usize : Std.Usize)).val from by simpa using this]
      scalar_tac
    · intro n hn
      show (enc.val[n]!).val = _
      exact henc_get n (by scalar_tac)
  · have hdveq : dv = 5#usize := Aeneas.Std.UScalar.eq_of_val_eq (by scalar_tac)
    subst hdveq
    obtain ⟨enc, henc, henc_get⟩ :=
      byte_encode_gen_eq re (160#usize) (1280#usize) (5#usize) (by scalar_tac) (by scalar_tac)
        (by scalar_tac) (by scalar_tac) a ha
    refine ⟨Aeneas.Std.Array.to_slice enc, ?_, ?_, ?_⟩
    · unfold hacspec_ml_kem.serialize.byte_encode_into
      simp only [hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT, Aeneas.Std.massert,
        Aeneas.Std.bind_tc_ok, Aeneas.Std.lift,
        show ((5#usize : Std.Usize).val) = 5 from rfl, henc]
      -- (`byte_encode_into`'s `massert (d ≤ BITS_PER_COEFFICIENT)` and
      --  `massert (out.len = 32 * d)` prelude is gone from the hax v0.4.0-rc.1
      --  extraction, so the length/bound stepping that stood here is unnecessary)
      exact hcopy (160#usize) enc (by scalar_tac)
    · show enc.val.length = _
      have := enc.property
      rw [show enc.val.length = ((160#usize : Std.Usize)).val from by simpa using this]
      scalar_tac
    · intro n hn
      show (enc.val[n]!).val = _
      exact henc_get n (by scalar_tac)

/-- **Spec-side apex.** `Compress_dv` then `ByteEncode_dv` into the freshly-zeroed
    `V_SIZE`-array, reproducing exactly `cByte re dv`. -/
private theorem L54_spec_eq
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (C2_LEN dv : Std.Usize) (hdv : dv.val = 4 ∨ dv.val = 5)
    (hc2 : C2_LEN.val = 32 * dv.val) :
    ∃ enc : Std.Array Std.U8 C2_LEN,
      hacspec_ml_kem.serialize.compress_then_serialize_v C2_LEN (lift_poly re) dv = .ok enc
      ∧ ∀ n : Nat, n < C2_LEN.val → (enc.val[n]!).val = cByte re dv.val n := by
  have hd12 : dv.val < 12 := by rcases hdv with h | h <;> omega
  obtain ⟨a, ha, ha_get⟩ := compress_v_get re dv hd12
  have hzlen : (Aeneas.Std.Array.to_slice
      (Aeneas.Std.Array.repeat C2_LEN (0#u8 : Std.U8))).val.length = 32 * dv.val := by
    show (Aeneas.Std.Array.repeat C2_LEN (0#u8 : Std.U8)).val.length = _
    rw [Aeneas.Std.Array.repeat_val, List.length_replicate, hc2]
  obtain ⟨s1, hs1, hs1len, hs1get⟩ :=
    byte_encode_into_45_eq re dv hdv a ha_get _ hzlen
  refine ⟨Aeneas.Std.Array.from_slice
    (Aeneas.Std.Array.repeat C2_LEN (0#u8 : Std.U8)) s1, ?_, ?_⟩
  · show (do
        let a' ← hacspec_ml_kem.compress.compress (lift_poly re) dv
        let s1' ← hacspec_ml_kem.serialize.byte_encode_into a' dv
                    (Aeneas.Std.Array.to_slice (Aeneas.Std.Array.repeat C2_LEN (0#u8 : Std.U8)))
        RustM.ok (Aeneas.Std.Array.from_slice
          (Aeneas.Std.Array.repeat C2_LEN (0#u8 : Std.U8)) s1')) = _
    rw [ha]; simp only [Aeneas.Std.bind_tc_ok]
    rw [hs1]; rfl
  · intro n hn
    rw [Aeneas.Std.Array.from_slice_val _ _ (by rw [hs1len, hc2])]
    exact hs1get n (by omega)

end L54Bank

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
    -- RESTATED 2026-08-18. The previous form carried only `h_len` and was FALSE; this
    -- file proves it so (the dv-dispatch refutation). Hypotheses transcribed VERBATIM
    -- from the upstream contract (libcrux-ml-kem/src/serialize.rs):
    --   is_rank v_K /\ $COMPRESSION_FACTOR == vector_v_compression_factor v_K
    --   /\ Seq.length $out == v $OUT_LEN /\ v $OUT_LEN == 32 * v $COMPRESSION_FACTOR
    --   /\ is_bounded_poly (sz 3328) $re
    -- The LAST conjunct is the one whose absence cost $71.82 on the sibling encode
    -- obligation: `byte_encode` reads a canonicalised `FieldElement.val` while the impl
    -- adds q at most once, so an unreduced coefficient makes impl and spec disagree
    -- (witness: lane 3400 -> impl byte 0x48, spec byte 0x47).
    (h_rank : hacspec_ml_kem.parameters.is_rank K = .ok true)
    (h_cf : hacspec_ml_kem.parameters.vector_v_compression_factor K
              = .ok V_COMPRESSION_FACTOR)
    (h_len : out.length = C2_LEN.val)
    (h_c2 : C2_LEN.val = 32 * V_COMPRESSION_FACTOR.val)
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
        ((re.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 3328) :
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
  -- The dv-conjunct of the source's `requires`: `vector_v_compression_factor` is 5 at
  -- rank 4 and 4 otherwise, so `h_cf` ALONE pins dv to {4,5} — `h_rank` is not needed for
  -- this step (it is the source's own panic-freedom conjunct, kept in the transcription).
  have hdv : V_COMPRESSION_FACTOR.val = 4 ∨ V_COMPRESSION_FACTOR.val = 5 := by
    unfold hacspec_ml_kem.parameters.vector_v_compression_factor at h_cf
    by_cases hK : K = 4#usize
    · rw [if_pos hK] at h_cf
      exact Or.inr (by injection h_cf with h; rw [← h]; scalar_tac)
    · rw [if_neg hK] at h_cf
      exact Or.inl (by injection h_cf with h; rw [← h]; scalar_tac)
  have hlen' : out.val.length = C2_LEN.val := h_len
  -- SPEC side, once and for both arms: `Compress_dv` then `ByteEncode_dv` is `cByte re dv`.
  obtain ⟨enc, henc, hencget⟩ := L54_spec_eq re C2_LEN V_COMPRESSION_FACTOR hdv h_c2
  -- FIRST RUNG (`L54_dispatch_of_pre`): the `unreachable!()` arm is gone.
  rw [L54_dispatch_of_pre K V_COMPRESSION_FACTOR C2_LEN re out scratch hdv]
  rcases hdv with h4 | h5
  · rw [if_pos h4]
    rw [h4] at hencget
    have hl4 : out.val.length = 128 := by rw [hlen', h_c2, h4]
    -- IMPL side. `h_bnd` is consumed HERE and only here, inside `to_unsigned_fm_eq`.
    obtain ⟨p, hp_eq, hp⟩ := triple_exists_ok_fc (L54_impl_4_fc re h_bnd out hl4 scratch)
    obtain ⟨hplen, hpget⟩ : p.1.val.length = 128 ∧
        ∀ n : Nat, n < 2 * 4 * ((16#usize : Std.Usize)).val →
          (p.1.val[n]!).val = cByte re 4 n := by
      simp only [cInv, Aeneas.Std.RustM.holds, pure, Pure.pure, Std.Do.Triple,
        Std.Do.WP.wp, Std.Do.PredTrans.apply, Std.Do.PostCond.noThrow,
        Std.Do.SPred.pure, Std.Do.SPred.entails] at hp
      exact hp trivial
    refine triple_of_ok_fc hp_eq ⟨enc, henc, ?_, ?_⟩
    · show p.1.val.length = C2_LEN.val
      rw [hplen, h_c2, h4]
    · intro ℓ hℓ
      refine Aeneas.Std.UScalar.eq_of_val_eq ?_
      rw [hpget ℓ (by rw [h_c2, h4] at hℓ; scalar_tac), hencget ℓ hℓ]
  · rw [if_neg (by omega)]
    rw [h5] at hencget
    have hl5 : out.val.length = 160 := by rw [hlen', h_c2, h5]
    obtain ⟨p, hp_eq, hp⟩ := triple_exists_ok_fc (L54_impl_5_fc re h_bnd out hl5 scratch)
    obtain ⟨hplen, hpget⟩ : p.1.val.length = 160 ∧
        ∀ n : Nat, n < 2 * 5 * ((16#usize : Std.Usize)).val →
          (p.1.val[n]!).val = cByte re 5 n := by
      simp only [cInv, Aeneas.Std.RustM.holds, pure, Pure.pure, Std.Do.Triple,
        Std.Do.WP.wp, Std.Do.PredTrans.apply, Std.Do.PostCond.noThrow,
        Std.Do.SPred.pure, Std.Do.SPred.entails] at hp
      exact hp trivial
    refine triple_of_ok_fc hp_eq ⟨enc, henc, ?_, ?_⟩
    · show p.1.val.length = C2_LEN.val
      rw [hplen, h_c2, h5]
    · intro ℓ hℓ
      refine Aeneas.Std.UScalar.eq_of_val_eq ?_
      rw [hpget ℓ (by rw [h_c2, h5] at hℓ; scalar_tac), hencget ℓ hℓ]

/-! ## INC-2a — the `_u` per-element family at `du ∈ {10, 11}`.

    **The `_u` blocker recorded in this file's header was a NAMING artifact.** The header
    (and `plans/INC-2-scope.md` §5.1, now retired by §9) said the per-element `_u` impl
    functions had no hacspec counterpart because the only `_u` spec functions are
    whole-vector. That compared ARITIES and never checked width-genericity. The hacspec

        deserialize_then_decompress_v (serialized) (dv) := decompress (byte_decode_dyn serialized dv) dv
        compress_then_serialize_v     (V_SIZE) (v) (dv) := byte_encode_into (compress v dv) dv …

    take the width as a RUNTIME parameter, and the closure body inside the whole-vector
    `deserialize_then_decompress_u` is `decompress (byte_decode_dyn chunk du) du` —
    the same expression. The function is named after ONE of its two callers.

    **This is not a reading of ours: it is upstream's own contract.** The
    `#[hax_lib::ensures]` on `deserialize_then_decompress_ring_element_u`
    (libcrux-ml-kem/src/serialize.rs) says the result is
    `Hacspec_ml_kem.Compress.decompress (Hacspec_ml_kem.Serialize.byte_decode_dyn $serialized
    $COMPRESSION_FACTOR) $COMPRESSION_FACTOR` — which is `deserialize_then_decompress_v`'s
    body, verbatim. Writing it under that name is an abbreviation of upstream's ensures,
    nothing more. Same on the encode side, where upstream's ensures is
    `byte_encode $OUT_LEN (sz 256 *! $CF) (compress … $CF) $CF`, i.e.
    `compress_then_serialize_v`'s body at `OUT_LEN = 32 * CF`.

    ⚠ **The one thing to know before reading the spec side.** The `.pre` that hax generates
    for `deserialize_then_decompress_v` / `compress_then_serialize_v` restricts `dv` to
    `{4, 5}`, because it is transcribed from the `#[hax_lib::requires]` of the `_v` CALLER.
    That `.pre` is NOT part of these statements and is not needed by them: the extracted
    Lean `def`s are total in `dv`, `byte_decode_dyn` / `byte_encode_into` both carry real
    arms at `d = 10` and `d = 11`, and both evaluate there (falsification log,
    2026-08-20). The `.pre` documents the `_v` caller's use, not the function's domain.

    **Composition.** These two are the per-element bricks. The whole-vector
    `ind_cpa::deserialize_then_decompress_u` / `compress_then_serialize_u` obligations
    compose them through BRIDGE lemmas relating the hacspec whole-vector `_u` functions'
    `createi` cells to `_v` at the corresponding chunk (`INC-2-scope.md` §9.4) — the same
    local-restructure-and-prove pattern as `spec_deser_pk_eq` in `IndCpaFc.lean`. Note the
    impl's whole-vector decode FUSES `ntt_vector_u` into the loop, so its spec counterpart
    is `deserialize_then_decompress_u_then_ntt`, not plain `_u`.
-/

section LuBank

open Aeneas.Std
open libcrux_iot_ml_kem.Matrix.ComputeRingElementV.Impl

/-! ### `I16`-level seam toolkit — what the `d ∈ {4,5}` seams did not need.

    `deserialize_4_int` / `deserialize_5_int` do all their bit work at `U8` and widen
    once at the end, because a 4- or 5-bit lane fits in a byte. At `d ∈ {10,11}` a lane
    does NOT, so the impl widens FIRST (`as_i16` on each byte) and masks/shifts at
    `I16`. So the `u8_and_mask_val` / `u8_shl_lit` / `u8_shr_lit` trio has to be
    restated at `I16`; the shapes are identical and the payload-pinned
    `i16_shl_bvp` / `i16_shr_bvp` (from the L5.4 bank) do the `RustM` half. -/

/-- `c16 x &&& (2 ^ k - 1)` is `x % 2 ^ k`. The `I16` counterpart of
    `u8_and_mask_val`, fused with `c16_bv_toNat` because every mask in the two `_u`
    seams is applied to a freshly widened byte. -/
private theorem Lu_c16_and_mask (x : Std.U8) (c : Std.I16) (k : Nat)
    (hc : c.bv.toNat = 2 ^ k - 1) : ((c16 x &&& c : Std.I16)).bv.toNat = x.val % 2 ^ k := by
  show ((c16 x).bv &&& c.bv).toNat = _
  rw [BitVec.toNat_and, hc, Nat.and_two_pow_sub_one_eq_mod, c16_bv_toNat]

/-- `x <<< k` at `I16`, value kept symbolic as `* 2 ^ k`; the `< 65536` guard is the
    no-truncation side condition. -/
private theorem Lu_i16_shl (x : Std.I16) (t : Std.I32) (k : Nat)
    (htv : t.val = (k : Int)) (hk : k < 16) (hx : x.bv.toNat * 2 ^ k < 65536) :
    ∃ z : Std.I16, (x <<< t : RustM Std.I16) = .ok z ∧ z.bv.toNat = x.bv.toNat * 2 ^ k :=
  ⟨⟨x.bv <<< k⟩, i16_shl_bvp x t k htv hk, bv16_shl_p x.bv k hx⟩

/-- `x >>> k` at `I16`, kept symbolic as `/ 2 ^ k`; nonnegative, so arithmetic shift
    IS floor division. -/
private theorem Lu_i16_shr (x : Std.I16) (t : Std.I32) (k : Nat)
    (htv : t.val = (k : Int)) (hk : k < 16) (hx : x.bv.toNat < 32768) :
    ∃ z : Std.I16, (x >>> t : RustM Std.I16) = .ok z ∧ z.bv.toNat = x.bv.toNat / 2 ^ k :=
  ⟨⟨x.bv.sshiftRight k⟩, i16_shr_bvp x t k htv hk, bv16_sshr_p x.bv k hx⟩

/-- "OR == + when the fields are disjoint", at `I16`. The `I16` counterpart of
    `lane_or_val`; `or_shl_add` is the shared content. -/
private theorem Lu_i16_or_add (x y : Std.I16) (hi lo e : Nat)
    (hx : x.bv.toNat = hi * 2 ^ e) (hy : y.bv.toNat = lo) (hlo : lo < 2 ^ e) :
    ((x ||| y : Std.I16)).bv.toNat = hi * 2 ^ e + lo := by
  show ((x.bv ||| y.bv)).toNat = _
  rw [BitVec.toNat_or, hx, hy, or_shl_add _ _ _ hlo]

/-- Small nonnegative `I16`s: `.val` is the `BitVec.toNat`, at the width the two `_u`
    seams produce (`< 2048 < 4096`). -/
private theorem Lu_i16_val (x : Std.I16) (n : Nat) (h : x.bv.toNat = n) (hn : n < 4096) :
    x.val = (n : Int) := by
  rw [i16_val_of_toNat x (by rw [h]; exact hn), h]

/-! ### The four pure-`Nat` lane identities at `d = 10`.

    Pulled OUT of the seam proof rather than left as eight in-line `omega`s. Measured:
    in-line, each `omega` sees the seam's ~40 byte / mask / shift / window hypotheses
    and the declaration blows the 200k heartbeat budget at the sixth lane; as separate
    three-variable lemmas the whole seam is cheap. The four shapes repeat verbatim on
    the second half of the chunk (bytes 5–9), so eight lanes cost four lemmas. -/

private theorem Lu10_w0 (b0 b1 b2 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) :
    b1 % 2 ^ 2 * 2 ^ 8 + b0 % 2 ^ 8 < 4096
    ∧ b1 % 2 ^ 2 * 2 ^ 8 + b0 % 2 ^ 8
        = (b0 + 256 * b1 + 65536 * b2) % 1024 := by omega

private theorem Lu10_w1 (b1 b2 b3 : Nat) (h1 : b1 < 256) (h2 : b2 < 256) :
    b2 % 2 ^ 4 * 2 ^ 6 + b1 / 2 ^ 2 < 4096
    ∧ b2 % 2 ^ 4 * 2 ^ 6 + b1 / 2 ^ 2
        = (b1 + 256 * b2 + 65536 * b3) / 4 % 1024 := by omega

private theorem Lu10_w2 (b2 b3 b4 : Nat) (h2 : b2 < 256) (h3 : b3 < 256) :
    b3 % 2 ^ 6 * 2 ^ 4 + b2 / 2 ^ 4 < 4096
    ∧ b3 % 2 ^ 6 * 2 ^ 4 + b2 / 2 ^ 4
        = (b2 + 256 * b3 + 65536 * b4) / 16 % 1024 := by omega

private theorem Lu10_w3 (b3 b4 b5 : Nat) (h3 : b3 < 256) (h4 : b4 < 256) :
    b4 * 2 ^ 2 + b3 / 2 ^ 6 < 4096
    ∧ b4 * 2 ^ 2 + b3 / 2 ^ 6
        = (b3 + 256 * b4 + 65536 * b5) / 64 % 1024 := by omega

/-- The no-truncation guard every masked `<<<` in the two `_u` seams needs. -/
private theorem Lu_mod_shl_lt (x k e : Nat) (h : 2 ^ k * 2 ^ e ≤ 65536) :
    x % 2 ^ k * 2 ^ e < 65536 :=
  lt_of_lt_of_le
    ((Nat.mul_lt_mul_right (Nat.two_pow_pos e)).mpr (Nat.mod_lt _ (Nat.two_pow_pos k))) h

/-- Same guard for the unmasked `<<<`s (`d = 10` lanes 3, 7; `d = 11` lanes 2, 5, 7). -/
private theorem Lu_byte_shl_lt (x e : Nat) (hx : x < 256) (h : 256 * 2 ^ e ≤ 65536) :
    x * 2 ^ e < 65536 :=
  lt_of_lt_of_le ((Nat.mul_lt_mul_right (Nat.two_pow_pos e)).mpr hx) h

/-- A byte is never near the `I16` sign bit, so `>>>` is floor division. -/
private theorem Lu_byte_lt_32768 (x : Nat) (hx : x < 256) : x < 32768 := by omega

/-! The three field-width facts the `d = 11` seam feeds to `Lu_i16_or_add`. Stated as
    lemmas rather than in-line `omega`s for the reason recorded above the `d = 10`
    shape lemmas: the `d = 11` seam's branch context is larger still. -/

private theorem Lu_byte_lt_pow (x f : Nat) (hx : x < 256) (h : 256 ≤ 2 ^ f) : x < 2 ^ f :=
  lt_of_lt_of_le hx h

private theorem Lu_byte_shl_lt' (x e f : Nat) (hx : x < 256) (h : 256 * 2 ^ e ≤ 2 ^ f) :
    x * 2 ^ e < 2 ^ f :=
  lt_of_lt_of_le ((Nat.mul_lt_mul_right (Nat.two_pow_pos e)).mpr hx) h

private theorem Lu_byte_div_lt (x e f : Nat) (hx : x < 256) (h : 256 ≤ 2 ^ e * 2 ^ f) :
    x / 2 ^ e < 2 ^ f :=
  Nat.div_lt_of_lt_mul (lt_of_lt_of_le hx h)

/-! ### IMPL SEAM at `d = 10`. The SHAPE is `deserialize_5_int_lanes_eq`'s (M-C(3)):
    name every `RustM` payload existentially, push each lane to a pure `Nat`
    expression in the ten bytes, convert the spec side to `decw` with M-C(1) once, and
    close the eight identities by `omega`. Two differences from `d = 5`, both from the
    lane no longer fitting in a byte: the algebra is at `I16` (see the toolkit above),
    and every lane straddles, so all eight are `(hi_field << e) ||| (lo >> s)` — the
    `d = 4` seam's mask-only lanes have no analogue here. -/

private theorem deserialize_10_int_lanes_eq (bytes : Slice Std.U8)
    (h_len : bytes.val.length = 10) :
    ∃ v0 v1 v2 v3 v4 v5 v6 v7 : Std.I16,
      libcrux_iot_ml_kem.vector.portable.serialize.deserialize_10_int bytes
          = .ok (v0, v1, v2, v3, v4, v5, v6, v7)
      ∧ ∀ k : Nat, k < 8 →
          (([v0, v1, v2, v3, v4, v5, v6, v7] : List Std.I16)[k]!).val
            = (win bytes.val 10 k : Int) := by
  have hb0 := u8_val_lt bytes.val 0
  have hb1 := u8_val_lt bytes.val 1
  have hb2 := u8_val_lt bytes.val 2
  have hb3 := u8_val_lt bytes.val 3
  have hb4 := u8_val_lt bytes.val 4
  have hb5 := u8_val_lt bytes.val 5
  have hb6 := u8_val_lt bytes.val 6
  have hb7 := u8_val_lt bytes.val 7
  have hb8 := u8_val_lt bytes.val 8
  have hb9 := u8_val_lt bytes.val 9
  have h17 : (10:Nat) ≤ 17 := by norm_num
  have hi0 : Slice.index_usize bytes 0#usize = .ok bytes.val[0]! :=
    slice_index_usize_eq bytes 0#usize (by simp [h_len])
  have hi1 : Slice.index_usize bytes 1#usize = .ok bytes.val[1]! :=
    slice_index_usize_eq bytes 1#usize (by simp [h_len])
  have hi2 : Slice.index_usize bytes 2#usize = .ok bytes.val[2]! :=
    slice_index_usize_eq bytes 2#usize (by simp [h_len])
  have hi3 : Slice.index_usize bytes 3#usize = .ok bytes.val[3]! :=
    slice_index_usize_eq bytes 3#usize (by simp [h_len])
  have hi4 : Slice.index_usize bytes 4#usize = .ok bytes.val[4]! :=
    slice_index_usize_eq bytes 4#usize (by simp [h_len])
  have hi5 : Slice.index_usize bytes 5#usize = .ok bytes.val[5]! :=
    slice_index_usize_eq bytes 5#usize (by simp [h_len])
  have hi6 : Slice.index_usize bytes 6#usize = .ok bytes.val[6]! :=
    slice_index_usize_eq bytes 6#usize (by simp [h_len])
  have hi7 : Slice.index_usize bytes 7#usize = .ok bytes.val[7]! :=
    slice_index_usize_eq bytes 7#usize (by simp [h_len])
  have hi8 : Slice.index_usize bytes 8#usize = .ok bytes.val[8]! :=
    slice_index_usize_eq bytes 8#usize (by simp [h_len])
  have hi9 : Slice.index_usize bytes 9#usize = .ok bytes.val[9]! :=
    slice_index_usize_eq bytes 9#usize (by simp [h_len])
  -- the eight masks, `ma<byte>`
  have ma0 : ((c16 bytes.val[0]! &&& 255#i16 : Std.I16)).bv.toNat = bytes.val[0]!.val % 2 ^ 8 :=
    Lu_c16_and_mask _ _ 8 rfl
  have ma1 : ((c16 bytes.val[1]! &&& 3#i16 : Std.I16)).bv.toNat = bytes.val[1]!.val % 2 ^ 2 :=
    Lu_c16_and_mask _ _ 2 rfl
  have ma2 : ((c16 bytes.val[2]! &&& 15#i16 : Std.I16)).bv.toNat = bytes.val[2]!.val % 2 ^ 4 :=
    Lu_c16_and_mask _ _ 4 rfl
  have ma3 : ((c16 bytes.val[3]! &&& 63#i16 : Std.I16)).bv.toNat = bytes.val[3]!.val % 2 ^ 6 :=
    Lu_c16_and_mask _ _ 6 rfl
  have ma5 : ((c16 bytes.val[5]! &&& 255#i16 : Std.I16)).bv.toNat = bytes.val[5]!.val % 2 ^ 8 :=
    Lu_c16_and_mask _ _ 8 rfl
  have ma6 : ((c16 bytes.val[6]! &&& 3#i16 : Std.I16)).bv.toNat = bytes.val[6]!.val % 2 ^ 2 :=
    Lu_c16_and_mask _ _ 2 rfl
  have ma7 : ((c16 bytes.val[7]! &&& 15#i16 : Std.I16)).bv.toNat = bytes.val[7]!.val % 2 ^ 4 :=
    Lu_c16_and_mask _ _ 4 rfl
  have ma8 : ((c16 bytes.val[8]! &&& 63#i16 : Std.I16)).bv.toNat = bytes.val[8]!.val % 2 ^ 6 :=
    Lu_c16_and_mask _ _ 6 rfl
  -- the eight left shifts, one per lane; `s<lane>`
  obtain ⟨s0, hs0, hs0v⟩ := Lu_i16_shl (c16 bytes.val[1]! &&& 3#i16) 8#i32 8
    (by scalar_tac) (by norm_num) (by rw [ma1]; exact Lu_mod_shl_lt _ 2 8 (by norm_num))
  obtain ⟨s1, hs1, hs1v⟩ := Lu_i16_shl (c16 bytes.val[2]! &&& 15#i16) 6#i32 6
    (by scalar_tac) (by norm_num) (by rw [ma2]; exact Lu_mod_shl_lt _ 4 6 (by norm_num))
  obtain ⟨s2, hs2, hs2v⟩ := Lu_i16_shl (c16 bytes.val[3]! &&& 63#i16) 4#i32 4
    (by scalar_tac) (by norm_num) (by rw [ma3]; exact Lu_mod_shl_lt _ 6 4 (by norm_num))
  obtain ⟨s3, hs3, hs3v⟩ := Lu_i16_shl (c16 bytes.val[4]!) 2#i32 2
    (by scalar_tac) (by norm_num) (by rw [c16_bv_toNat]; exact Lu_byte_shl_lt _ 2 (by scalar_tac) (by norm_num))
  obtain ⟨s4, hs4, hs4v⟩ := Lu_i16_shl (c16 bytes.val[6]! &&& 3#i16) 8#i32 8
    (by scalar_tac) (by norm_num) (by rw [ma6]; exact Lu_mod_shl_lt _ 2 8 (by norm_num))
  obtain ⟨s5, hs5, hs5v⟩ := Lu_i16_shl (c16 bytes.val[7]! &&& 15#i16) 6#i32 6
    (by scalar_tac) (by norm_num) (by rw [ma7]; exact Lu_mod_shl_lt _ 4 6 (by norm_num))
  obtain ⟨s6, hs6, hs6v⟩ := Lu_i16_shl (c16 bytes.val[8]! &&& 63#i16) 4#i32 4
    (by scalar_tac) (by norm_num) (by rw [ma8]; exact Lu_mod_shl_lt _ 6 4 (by norm_num))
  obtain ⟨s7, hs7, hs7v⟩ := Lu_i16_shl (c16 bytes.val[9]!) 2#i32 2
    (by scalar_tac) (by norm_num) (by rw [c16_bv_toNat]; exact Lu_byte_shl_lt _ 2 (by scalar_tac) (by norm_num))
  -- the six right shifts; `y<byte><amount>`
  obtain ⟨y12, hy12, hy12v⟩ := Lu_i16_shr (c16 bytes.val[1]!) 2#i32 2
    (by scalar_tac) (by norm_num) (by rw [c16_bv_toNat]; exact Lu_byte_lt_32768 _ (by scalar_tac))
  obtain ⟨y24, hy24, hy24v⟩ := Lu_i16_shr (c16 bytes.val[2]!) 4#i32 4
    (by scalar_tac) (by norm_num) (by rw [c16_bv_toNat]; exact Lu_byte_lt_32768 _ (by scalar_tac))
  obtain ⟨y36, hy36, hy36v⟩ := Lu_i16_shr (c16 bytes.val[3]!) 6#i32 6
    (by scalar_tac) (by norm_num) (by rw [c16_bv_toNat]; exact Lu_byte_lt_32768 _ (by scalar_tac))
  obtain ⟨y62, hy62, hy62v⟩ := Lu_i16_shr (c16 bytes.val[6]!) 2#i32 2
    (by scalar_tac) (by norm_num) (by rw [c16_bv_toNat]; exact Lu_byte_lt_32768 _ (by scalar_tac))
  obtain ⟨y74, hy74, hy74v⟩ := Lu_i16_shr (c16 bytes.val[7]!) 4#i32 4
    (by scalar_tac) (by norm_num) (by rw [c16_bv_toNat]; exact Lu_byte_lt_32768 _ (by scalar_tac))
  obtain ⟨y86, hy86, hy86v⟩ := Lu_i16_shr (c16 bytes.val[8]!) 6#i32 6
    (by scalar_tac) (by norm_num) (by rw [c16_bv_toNat]; exact Lu_byte_lt_32768 _ (by scalar_tac))
  refine ⟨s0 ||| (c16 bytes.val[0]! &&& 255#i16), s1 ||| y12, s2 ||| y24, s3 ||| y36,
    s4 ||| (c16 bytes.val[5]! &&& 255#i16), s5 ||| y62, s6 ||| y74, s7 ||| y86, ?_, ?_⟩
  · -- the straight-line body walk: every step is one of the facts above
    simp only [libcrux_iot_ml_kem.vector.portable.serialize.deserialize_10_int,
      hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, as_i16_eq, as_i16_id,
      hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7,
      hy12, hy24, hy36, hy62, hy74, hy86, Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  · intro k hk
    -- the eight lane values, in ℕ, powers kept symbolic
    have f0 : s0.bv.toNat = bytes.val[1]!.val % 2 ^ 2 * 2 ^ 8 := by rw [hs0v, ma1]
    have f1 : s1.bv.toNat = bytes.val[2]!.val % 2 ^ 4 * 2 ^ 6 := by rw [hs1v, ma2]
    have f2 : s2.bv.toNat = bytes.val[3]!.val % 2 ^ 6 * 2 ^ 4 := by rw [hs2v, ma3]
    have f3 : s3.bv.toNat = bytes.val[4]!.val * 2 ^ 2 := by rw [hs3v, c16_bv_toNat]
    have f4 : s4.bv.toNat = bytes.val[6]!.val % 2 ^ 2 * 2 ^ 8 := by rw [hs4v, ma6]
    have f5 : s5.bv.toNat = bytes.val[7]!.val % 2 ^ 4 * 2 ^ 6 := by rw [hs5v, ma7]
    have f6 : s6.bv.toNat = bytes.val[8]!.val % 2 ^ 6 * 2 ^ 4 := by rw [hs6v, ma8]
    have f7 : s7.bv.toNat = bytes.val[9]!.val * 2 ^ 2 := by rw [hs7v, c16_bv_toNat]
    have g12 : y12.bv.toNat = bytes.val[1]!.val / 2 ^ 2 := by rw [hy12v, c16_bv_toNat]
    have g24 : y24.bv.toNat = bytes.val[2]!.val / 2 ^ 4 := by rw [hy24v, c16_bv_toNat]
    have g36 : y36.bv.toNat = bytes.val[3]!.val / 2 ^ 6 := by rw [hy36v, c16_bv_toNat]
    have g62 : y62.bv.toNat = bytes.val[6]!.val / 2 ^ 2 := by rw [hy62v, c16_bv_toNat]
    have g74 : y74.bv.toNat = bytes.val[7]!.val / 2 ^ 4 := by rw [hy74v, c16_bv_toNat]
    have g86 : y86.bv.toNat = bytes.val[8]!.val / 2 ^ 6 := by rw [hy86v, c16_bv_toNat]
    have n0 : ((s0 ||| (c16 bytes.val[0]! &&& 255#i16) : Std.I16)).bv.toNat
        = bytes.val[1]!.val % 2 ^ 2 * 2 ^ 8 + bytes.val[0]!.val % 2 ^ 8 :=
      Lu_i16_or_add _ _ _ _ 8 f0 ma0 (by omega)
    have n1 : ((s1 ||| y12 : Std.I16)).bv.toNat
        = bytes.val[2]!.val % 2 ^ 4 * 2 ^ 6 + bytes.val[1]!.val / 2 ^ 2 :=
      Lu_i16_or_add _ _ _ _ 6 f1 g12 (by omega)
    have n2 : ((s2 ||| y24 : Std.I16)).bv.toNat
        = bytes.val[3]!.val % 2 ^ 6 * 2 ^ 4 + bytes.val[2]!.val / 2 ^ 4 :=
      Lu_i16_or_add _ _ _ _ 4 f2 g24 (by omega)
    have n3 : ((s3 ||| y36 : Std.I16)).bv.toNat
        = bytes.val[4]!.val * 2 ^ 2 + bytes.val[3]!.val / 2 ^ 6 :=
      Lu_i16_or_add _ _ _ _ 2 f3 g36 (by omega)
    have n4 : ((s4 ||| (c16 bytes.val[5]! &&& 255#i16) : Std.I16)).bv.toNat
        = bytes.val[6]!.val % 2 ^ 2 * 2 ^ 8 + bytes.val[5]!.val % 2 ^ 8 :=
      Lu_i16_or_add _ _ _ _ 8 f4 ma5 (by omega)
    have n5 : ((s5 ||| y62 : Std.I16)).bv.toNat
        = bytes.val[7]!.val % 2 ^ 4 * 2 ^ 6 + bytes.val[6]!.val / 2 ^ 2 :=
      Lu_i16_or_add _ _ _ _ 6 f5 g62 (by omega)
    have n6 : ((s6 ||| y74 : Std.I16)).bv.toNat
        = bytes.val[8]!.val % 2 ^ 6 * 2 ^ 4 + bytes.val[7]!.val / 2 ^ 4 :=
      Lu_i16_or_add _ _ _ _ 4 f6 g74 (by omega)
    have n7 : ((s7 ||| y86 : Std.I16)).bv.toNat
        = bytes.val[9]!.val * 2 ^ 2 + bytes.val[8]!.val / 2 ^ 6 :=
      Lu_i16_or_add _ _ _ _ 2 f7 g86 (by omega)
    have key : ∀ v : Std.I16, v.val = (decw bytes.val (10 * k) 10 : Int) →
        v.val = (win bytes.val 10 k : Int) := by
      intro v h
      rw [win_eq_decw bytes.val 10 k h17]
      exact h
    -- `decw` at the eight offsets. Kept SEPARATE from the `omega` steps: `norm_num`
    -- rewrites `l[i]!` to `l[i]?.getD default`, and inside an `omega` goal the byte
    -- atoms would stop matching the `hb*` / `hoob10` hypotheses.
    have d0 : decw bytes.val (10 * 0) 10
        = (bytes.val[0]!.val + 256 * bytes.val[1]!.val + 65536 * bytes.val[2]!.val)
            % 1024 := by norm_num [decw]
    have d1 : decw bytes.val (10 * 1) 10
        = (bytes.val[1]!.val + 256 * bytes.val[2]!.val + 65536 * bytes.val[3]!.val)
            / 4 % 1024 := by norm_num [decw]
    have d2 : decw bytes.val (10 * 2) 10
        = (bytes.val[2]!.val + 256 * bytes.val[3]!.val + 65536 * bytes.val[4]!.val)
            / 16 % 1024 := by norm_num [decw]
    have d3 : decw bytes.val (10 * 3) 10
        = (bytes.val[3]!.val + 256 * bytes.val[4]!.val + 65536 * bytes.val[5]!.val)
            / 64 % 1024 := by norm_num [decw]
    have d4 : decw bytes.val (10 * 4) 10
        = (bytes.val[5]!.val + 256 * bytes.val[6]!.val + 65536 * bytes.val[7]!.val)
            % 1024 := by norm_num [decw]
    have d5 : decw bytes.val (10 * 5) 10
        = (bytes.val[6]!.val + 256 * bytes.val[7]!.val + 65536 * bytes.val[8]!.val)
            / 4 % 1024 := by norm_num [decw]
    have d6 : decw bytes.val (10 * 6) 10
        = (bytes.val[7]!.val + 256 * bytes.val[8]!.val + 65536 * bytes.val[9]!.val)
            / 16 % 1024 := by norm_num [decw]
    have d7 : decw bytes.val (10 * 7) 10
        = (bytes.val[8]!.val + 256 * bytes.val[9]!.val + 65536 * bytes.val[10]!.val)
            / 64 % 1024 := by norm_num [decw]
    refine key _ ?_
    interval_cases k
    · obtain ⟨p0, q0⟩ := Lu10_w0 bytes.val[0]!.val bytes.val[1]!.val bytes.val[2]!.val hb0 hb1
      show ((s0 ||| (c16 bytes.val[0]! &&& 255#i16) : Std.I16)).val = _
      rw [Lu_i16_val _ _ n0 p0, d0, q0]
    · obtain ⟨p1, q1⟩ := Lu10_w1 bytes.val[1]!.val bytes.val[2]!.val bytes.val[3]!.val hb1 hb2
      show ((s1 ||| y12 : Std.I16)).val = _
      rw [Lu_i16_val _ _ n1 p1, d1, q1]
    · obtain ⟨p2, q2⟩ := Lu10_w2 bytes.val[2]!.val bytes.val[3]!.val bytes.val[4]!.val hb2 hb3
      show ((s2 ||| y24 : Std.I16)).val = _
      rw [Lu_i16_val _ _ n2 p2, d2, q2]
    · obtain ⟨p3, q3⟩ := Lu10_w3 bytes.val[3]!.val bytes.val[4]!.val bytes.val[5]!.val hb3 hb4
      show ((s3 ||| y36 : Std.I16)).val = _
      rw [Lu_i16_val _ _ n3 p3, d3, q3]
    · obtain ⟨p4, q4⟩ := Lu10_w0 bytes.val[5]!.val bytes.val[6]!.val bytes.val[7]!.val hb5 hb6
      show ((s4 ||| (c16 bytes.val[5]! &&& 255#i16) : Std.I16)).val = _
      rw [Lu_i16_val _ _ n4 p4, d4, q4]
    · obtain ⟨p5, q5⟩ := Lu10_w1 bytes.val[6]!.val bytes.val[7]!.val bytes.val[8]!.val hb6 hb7
      show ((s5 ||| y62 : Std.I16)).val = _
      rw [Lu_i16_val _ _ n5 p5, d5, q5]
    · obtain ⟨p6, q6⟩ := Lu10_w2 bytes.val[7]!.val bytes.val[8]!.val bytes.val[9]!.val hb7 hb8
      show ((s6 ||| y74 : Std.I16)).val = _
      rw [Lu_i16_val _ _ n6 p6, d6, q6]
    · obtain ⟨p7, q7⟩ := Lu10_w3 bytes.val[8]!.val bytes.val[9]!.val bytes.val[10]!.val hb8 hb9
      show ((s7 ||| y86 : Std.I16)).val = _
      rw [Lu_i16_val _ _ n7 p7, d7, q7]

/-! ### The eight pure-`Nat` lane identities at `d = 11`.

    Eight, not four: at `d = 10` the bit offset advances by 10 ≡ 2 (mod 8) and the
    pattern repeats after four lanes, whereas at `d = 11` it advances by 3 (mod 8) and
    the cycle is the full eight. Lanes 2 and 5 are the ones that genuinely span THREE
    bytes — `(b_{i+2} & 1) << 10 | b_{i+1} << 2 | b_i >> 6` — which no seam in this
    tree previously exercised; the extra `|||` is why their left-hand sides are
    parenthesised as `(hi * 2 ^ 8 + mid) * 2 ^ 2`, i.e. one application of
    `Lu_i16_or_add` per `|||` with the accumulated field re-associated in between. -/

private theorem Lu11_w0 (b0 b1 b2 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) :
    b1 % 2 ^ 3 * 2 ^ 8 + b0 < 4096
    ∧ b1 % 2 ^ 3 * 2 ^ 8 + b0
        = (b0 + 256 * b1 + 65536 * b2) % 2048 := by omega

private theorem Lu11_w1 (b1 b2 b3 : Nat) (h1 : b1 < 256) (h2 : b2 < 256) :
    b2 % 2 ^ 6 * 2 ^ 5 + b1 / 2 ^ 3 < 4096
    ∧ b2 % 2 ^ 6 * 2 ^ 5 + b1 / 2 ^ 3
        = (b1 + 256 * b2 + 65536 * b3) / 8 % 2048 := by omega

private theorem Lu11_w2 (b2 b3 b4 : Nat) (h2 : b2 < 256) (h3 : b3 < 256) :
    (b4 % 2 ^ 1 * 2 ^ 8 + b3) * 2 ^ 2 + b2 / 2 ^ 6 < 4096
    ∧ (b4 % 2 ^ 1 * 2 ^ 8 + b3) * 2 ^ 2 + b2 / 2 ^ 6
        = (b2 + 256 * b3 + 65536 * b4) / 64 % 2048 := by omega

private theorem Lu11_w3 (b4 b5 b6 : Nat) (h4 : b4 < 256) (h5 : b5 < 256) :
    b5 % 2 ^ 4 * 2 ^ 7 + b4 / 2 ^ 1 < 4096
    ∧ b5 % 2 ^ 4 * 2 ^ 7 + b4 / 2 ^ 1
        = (b4 + 256 * b5 + 65536 * b6) / 2 % 2048 := by omega

private theorem Lu11_w4 (b5 b6 b7 : Nat) (h5 : b5 < 256) (h6 : b6 < 256) :
    b6 % 2 ^ 7 * 2 ^ 4 + b5 / 2 ^ 4 < 4096
    ∧ b6 % 2 ^ 7 * 2 ^ 4 + b5 / 2 ^ 4
        = (b5 + 256 * b6 + 65536 * b7) / 16 % 2048 := by omega

private theorem Lu11_w5 (b6 b7 b8 : Nat) (h6 : b6 < 256) (h7 : b7 < 256) :
    (b8 % 2 ^ 2 * 2 ^ 8 + b7) * 2 ^ 1 + b6 / 2 ^ 7 < 4096
    ∧ (b8 % 2 ^ 2 * 2 ^ 8 + b7) * 2 ^ 1 + b6 / 2 ^ 7
        = (b6 + 256 * b7 + 65536 * b8) / 128 % 2048 := by omega

private theorem Lu11_w6 (b8 b9 b10 : Nat) (h8 : b8 < 256) (h9 : b9 < 256) :
    b9 % 2 ^ 5 * 2 ^ 6 + b8 / 2 ^ 2 < 4096
    ∧ b9 % 2 ^ 5 * 2 ^ 6 + b8 / 2 ^ 2
        = (b8 + 256 * b9 + 65536 * b10) / 4 % 2048 := by omega

private theorem Lu11_w7 (b9 b10 b11 : Nat) (h9 : b9 < 256) (h10 : b10 < 256) :
    b10 * 2 ^ 3 + b9 / 2 ^ 5 < 4096
    ∧ b10 * 2 ^ 3 + b9 / 2 ^ 5
        = (b9 + 256 * b10 + 65536 * b11) / 32 % 2048 := by omega

/-! ### IMPL SEAM at `d = 11`. Same shape as the `d = 10` seam above; the two
    three-byte lanes are the only structural difference. -/

private theorem deserialize_11_int_lanes_eq (bytes : Slice Std.U8)
    (h_len : bytes.val.length = 11) :
    ∃ v0 v1 v2 v3 v4 v5 v6 v7 : Std.I16,
      libcrux_iot_ml_kem.vector.portable.serialize.deserialize_11_int bytes
          = .ok (v0, v1, v2, v3, v4, v5, v6, v7)
      ∧ ∀ k : Nat, k < 8 →
          (([v0, v1, v2, v3, v4, v5, v6, v7] : List Std.I16)[k]!).val
            = (win bytes.val 11 k : Int) := by
  have hb0 := u8_val_lt bytes.val 0
  have hb1 := u8_val_lt bytes.val 1
  have hb2 := u8_val_lt bytes.val 2
  have hb3 := u8_val_lt bytes.val 3
  have hb4 := u8_val_lt bytes.val 4
  have hb5 := u8_val_lt bytes.val 5
  have hb6 := u8_val_lt bytes.val 6
  have hb7 := u8_val_lt bytes.val 7
  have hb8 := u8_val_lt bytes.val 8
  have hb9 := u8_val_lt bytes.val 9
  have hb10 := u8_val_lt bytes.val 10
  have h17 : (11:Nat) ≤ 17 := by norm_num
  have hi0 : Slice.index_usize bytes 0#usize = .ok bytes.val[0]! :=
    slice_index_usize_eq bytes 0#usize (by simp [h_len])
  have hi1 : Slice.index_usize bytes 1#usize = .ok bytes.val[1]! :=
    slice_index_usize_eq bytes 1#usize (by simp [h_len])
  have hi2 : Slice.index_usize bytes 2#usize = .ok bytes.val[2]! :=
    slice_index_usize_eq bytes 2#usize (by simp [h_len])
  have hi3 : Slice.index_usize bytes 3#usize = .ok bytes.val[3]! :=
    slice_index_usize_eq bytes 3#usize (by simp [h_len])
  have hi4 : Slice.index_usize bytes 4#usize = .ok bytes.val[4]! :=
    slice_index_usize_eq bytes 4#usize (by simp [h_len])
  have hi5 : Slice.index_usize bytes 5#usize = .ok bytes.val[5]! :=
    slice_index_usize_eq bytes 5#usize (by simp [h_len])
  have hi6 : Slice.index_usize bytes 6#usize = .ok bytes.val[6]! :=
    slice_index_usize_eq bytes 6#usize (by simp [h_len])
  have hi7 : Slice.index_usize bytes 7#usize = .ok bytes.val[7]! :=
    slice_index_usize_eq bytes 7#usize (by simp [h_len])
  have hi8 : Slice.index_usize bytes 8#usize = .ok bytes.val[8]! :=
    slice_index_usize_eq bytes 8#usize (by simp [h_len])
  have hi9 : Slice.index_usize bytes 9#usize = .ok bytes.val[9]! :=
    slice_index_usize_eq bytes 9#usize (by simp [h_len])
  have hi10 : Slice.index_usize bytes 10#usize = .ok bytes.val[10]! :=
    slice_index_usize_eq bytes 10#usize (by simp [h_len])
  -- the seven masks, `ma<byte>`
  have ma1 : ((c16 bytes.val[1]! &&& 7#i16 : Std.I16)).bv.toNat = bytes.val[1]!.val % 2 ^ 3 :=
    Lu_c16_and_mask _ _ 3 rfl
  have ma2 : ((c16 bytes.val[2]! &&& 63#i16 : Std.I16)).bv.toNat = bytes.val[2]!.val % 2 ^ 6 :=
    Lu_c16_and_mask _ _ 6 rfl
  have ma4 : ((c16 bytes.val[4]! &&& 1#i16 : Std.I16)).bv.toNat = bytes.val[4]!.val % 2 ^ 1 :=
    Lu_c16_and_mask _ _ 1 rfl
  have ma5 : ((c16 bytes.val[5]! &&& 15#i16 : Std.I16)).bv.toNat = bytes.val[5]!.val % 2 ^ 4 :=
    Lu_c16_and_mask _ _ 4 rfl
  have ma6 : ((c16 bytes.val[6]! &&& 127#i16 : Std.I16)).bv.toNat = bytes.val[6]!.val % 2 ^ 7 :=
    Lu_c16_and_mask _ _ 7 rfl
  have ma8 : ((c16 bytes.val[8]! &&& 3#i16 : Std.I16)).bv.toNat = bytes.val[8]!.val % 2 ^ 2 :=
    Lu_c16_and_mask _ _ 2 rfl
  have ma9 : ((c16 bytes.val[9]! &&& 31#i16 : Std.I16)).bv.toNat = bytes.val[9]!.val % 2 ^ 5 :=
    Lu_c16_and_mask _ _ 5 rfl
  -- the ten left shifts
  obtain ⟨s0, hs0, hs0v⟩ := Lu_i16_shl (c16 bytes.val[1]! &&& 7#i16) 8#i32 8
    (by scalar_tac) (by norm_num) (by rw [ma1]; exact Lu_mod_shl_lt _ 3 8 (by norm_num))
  obtain ⟨s1, hs1, hs1v⟩ := Lu_i16_shl (c16 bytes.val[2]! &&& 63#i16) 5#i32 5
    (by scalar_tac) (by norm_num) (by rw [ma2]; exact Lu_mod_shl_lt _ 6 5 (by norm_num))
  obtain ⟨s2a, hs2a, hs2av⟩ := Lu_i16_shl (c16 bytes.val[4]! &&& 1#i16) 10#i32 10
    (by scalar_tac) (by norm_num) (by rw [ma4]; exact Lu_mod_shl_lt _ 1 10 (by norm_num))
  obtain ⟨s2b, hs2b, hs2bv⟩ := Lu_i16_shl (c16 bytes.val[3]!) 2#i32 2
    (by scalar_tac) (by norm_num)
    (by rw [c16_bv_toNat]; exact Lu_byte_shl_lt _ 2 (by scalar_tac) (by norm_num))
  obtain ⟨s3, hs3, hs3v⟩ := Lu_i16_shl (c16 bytes.val[5]! &&& 15#i16) 7#i32 7
    (by scalar_tac) (by norm_num) (by rw [ma5]; exact Lu_mod_shl_lt _ 4 7 (by norm_num))
  obtain ⟨s4, hs4, hs4v⟩ := Lu_i16_shl (c16 bytes.val[6]! &&& 127#i16) 4#i32 4
    (by scalar_tac) (by norm_num) (by rw [ma6]; exact Lu_mod_shl_lt _ 7 4 (by norm_num))
  obtain ⟨s5a, hs5a, hs5av⟩ := Lu_i16_shl (c16 bytes.val[8]! &&& 3#i16) 9#i32 9
    (by scalar_tac) (by norm_num) (by rw [ma8]; exact Lu_mod_shl_lt _ 2 9 (by norm_num))
  obtain ⟨s5b, hs5b, hs5bv⟩ := Lu_i16_shl (c16 bytes.val[7]!) 1#i32 1
    (by scalar_tac) (by norm_num)
    (by rw [c16_bv_toNat]; exact Lu_byte_shl_lt _ 1 (by scalar_tac) (by norm_num))
  obtain ⟨s6, hs6, hs6v⟩ := Lu_i16_shl (c16 bytes.val[9]! &&& 31#i16) 6#i32 6
    (by scalar_tac) (by norm_num) (by rw [ma9]; exact Lu_mod_shl_lt _ 5 6 (by norm_num))
  obtain ⟨s7, hs7, hs7v⟩ := Lu_i16_shl (c16 bytes.val[10]!) 3#i32 3
    (by scalar_tac) (by norm_num)
    (by rw [c16_bv_toNat]; exact Lu_byte_shl_lt _ 3 (by scalar_tac) (by norm_num))
  -- the seven right shifts; `y<byte><amount>`
  obtain ⟨y13, hy13, hy13v⟩ := Lu_i16_shr (c16 bytes.val[1]!) 3#i32 3
    (by scalar_tac) (by norm_num) (by rw [c16_bv_toNat]; exact Lu_byte_lt_32768 _ (by scalar_tac))
  obtain ⟨y26, hy26, hy26v⟩ := Lu_i16_shr (c16 bytes.val[2]!) 6#i32 6
    (by scalar_tac) (by norm_num) (by rw [c16_bv_toNat]; exact Lu_byte_lt_32768 _ (by scalar_tac))
  obtain ⟨y41, hy41, hy41v⟩ := Lu_i16_shr (c16 bytes.val[4]!) 1#i32 1
    (by scalar_tac) (by norm_num) (by rw [c16_bv_toNat]; exact Lu_byte_lt_32768 _ (by scalar_tac))
  obtain ⟨y54, hy54, hy54v⟩ := Lu_i16_shr (c16 bytes.val[5]!) 4#i32 4
    (by scalar_tac) (by norm_num) (by rw [c16_bv_toNat]; exact Lu_byte_lt_32768 _ (by scalar_tac))
  obtain ⟨y67, hy67, hy67v⟩ := Lu_i16_shr (c16 bytes.val[6]!) 7#i32 7
    (by scalar_tac) (by norm_num) (by rw [c16_bv_toNat]; exact Lu_byte_lt_32768 _ (by scalar_tac))
  obtain ⟨y82, hy82, hy82v⟩ := Lu_i16_shr (c16 bytes.val[8]!) 2#i32 2
    (by scalar_tac) (by norm_num) (by rw [c16_bv_toNat]; exact Lu_byte_lt_32768 _ (by scalar_tac))
  obtain ⟨y95, hy95, hy95v⟩ := Lu_i16_shr (c16 bytes.val[9]!) 5#i32 5
    (by scalar_tac) (by norm_num) (by rw [c16_bv_toNat]; exact Lu_byte_lt_32768 _ (by scalar_tac))
  refine ⟨s0 ||| c16 bytes.val[0]!, s1 ||| y13, (s2a ||| s2b) ||| y26, s3 ||| y41,
    s4 ||| y54, (s5a ||| s5b) ||| y67, s6 ||| y82, s7 ||| y95, ?_, ?_⟩
  · simp only [libcrux_iot_ml_kem.vector.portable.serialize.deserialize_11_int,
      hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, as_i16_eq,
      hs0, hs1, hs2a, hs2b, hs3, hs4, hs5a, hs5b, hs6, hs7,
      hy13, hy26, hy41, hy54, hy67, hy82, hy95,
      Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  · intro k hk
    have f0 : s0.bv.toNat = bytes.val[1]!.val % 2 ^ 3 * 2 ^ 8 := by rw [hs0v, ma1]
    have f1 : s1.bv.toNat = bytes.val[2]!.val % 2 ^ 6 * 2 ^ 5 := by rw [hs1v, ma2]
    have f2a : s2a.bv.toNat = bytes.val[4]!.val % 2 ^ 1 * 2 ^ 10 := by rw [hs2av, ma4]
    have f2b : s2b.bv.toNat = bytes.val[3]!.val * 2 ^ 2 := by rw [hs2bv, c16_bv_toNat]
    have f3 : s3.bv.toNat = bytes.val[5]!.val % 2 ^ 4 * 2 ^ 7 := by rw [hs3v, ma5]
    have f4 : s4.bv.toNat = bytes.val[6]!.val % 2 ^ 7 * 2 ^ 4 := by rw [hs4v, ma6]
    have f5a : s5a.bv.toNat = bytes.val[8]!.val % 2 ^ 2 * 2 ^ 9 := by rw [hs5av, ma8]
    have f5b : s5b.bv.toNat = bytes.val[7]!.val * 2 ^ 1 := by rw [hs5bv, c16_bv_toNat]
    have f6 : s6.bv.toNat = bytes.val[9]!.val % 2 ^ 5 * 2 ^ 6 := by rw [hs6v, ma9]
    have f7 : s7.bv.toNat = bytes.val[10]!.val * 2 ^ 3 := by rw [hs7v, c16_bv_toNat]
    have g00 : ((c16 bytes.val[0]! : Std.I16)).bv.toNat = bytes.val[0]!.val := c16_bv_toNat _
    have g13 : y13.bv.toNat = bytes.val[1]!.val / 2 ^ 3 := by rw [hy13v, c16_bv_toNat]
    have g26 : y26.bv.toNat = bytes.val[2]!.val / 2 ^ 6 := by rw [hy26v, c16_bv_toNat]
    have g41 : y41.bv.toNat = bytes.val[4]!.val / 2 ^ 1 := by rw [hy41v, c16_bv_toNat]
    have g54 : y54.bv.toNat = bytes.val[5]!.val / 2 ^ 4 := by rw [hy54v, c16_bv_toNat]
    have g67 : y67.bv.toNat = bytes.val[6]!.val / 2 ^ 7 := by rw [hy67v, c16_bv_toNat]
    have g82 : y82.bv.toNat = bytes.val[8]!.val / 2 ^ 2 := by rw [hy82v, c16_bv_toNat]
    have g95 : y95.bv.toNat = bytes.val[9]!.val / 2 ^ 5 := by rw [hy95v, c16_bv_toNat]
    have n0 : ((s0 ||| c16 bytes.val[0]! : Std.I16)).bv.toNat
        = bytes.val[1]!.val % 2 ^ 3 * 2 ^ 8 + bytes.val[0]!.val :=
      Lu_i16_or_add _ _ _ _ 8 f0 g00 (Lu_byte_lt_pow _ 8 (by scalar_tac) (by norm_num))
    have n1 : ((s1 ||| y13 : Std.I16)).bv.toNat
        = bytes.val[2]!.val % 2 ^ 6 * 2 ^ 5 + bytes.val[1]!.val / 2 ^ 3 :=
      Lu_i16_or_add _ _ _ _ 5 f1 g13 (Lu_byte_div_lt _ 3 5 (by scalar_tac) (by norm_num))
    -- lane 2, the first THREE-byte lane: one `Lu_i16_or_add` per `|||`, with the
    -- accumulated field re-associated as `(… * 2 ^ 8 + b3) * 2 ^ 2` in between.
    have n2a : ((s2a ||| s2b : Std.I16)).bv.toNat
        = (bytes.val[4]!.val % 2 ^ 1 * 2 ^ 8 + bytes.val[3]!.val) * 2 ^ 2 := by
      rw [Lu_i16_or_add _ _ _ _ 10 f2a f2b
        (Lu_byte_shl_lt' _ 2 10 (by scalar_tac) (by norm_num))]
      ring
    have n2 : (((s2a ||| s2b) ||| y26 : Std.I16)).bv.toNat
        = (bytes.val[4]!.val % 2 ^ 1 * 2 ^ 8 + bytes.val[3]!.val) * 2 ^ 2
          + bytes.val[2]!.val / 2 ^ 6 :=
      Lu_i16_or_add _ _ _ _ 2 n2a g26 (Lu_byte_div_lt _ 6 2 (by scalar_tac) (by norm_num))
    have n3 : ((s3 ||| y41 : Std.I16)).bv.toNat
        = bytes.val[5]!.val % 2 ^ 4 * 2 ^ 7 + bytes.val[4]!.val / 2 ^ 1 :=
      Lu_i16_or_add _ _ _ _ 7 f3 g41 (Lu_byte_div_lt _ 1 7 (by scalar_tac) (by norm_num))
    have n4 : ((s4 ||| y54 : Std.I16)).bv.toNat
        = bytes.val[6]!.val % 2 ^ 7 * 2 ^ 4 + bytes.val[5]!.val / 2 ^ 4 :=
      Lu_i16_or_add _ _ _ _ 4 f4 g54 (Lu_byte_div_lt _ 4 4 (by scalar_tac) (by norm_num))
    have n5a : ((s5a ||| s5b : Std.I16)).bv.toNat
        = (bytes.val[8]!.val % 2 ^ 2 * 2 ^ 8 + bytes.val[7]!.val) * 2 ^ 1 := by
      rw [Lu_i16_or_add _ _ _ _ 9 f5a f5b
        (Lu_byte_shl_lt' _ 1 9 (by scalar_tac) (by norm_num))]
      ring
    have n5 : (((s5a ||| s5b) ||| y67 : Std.I16)).bv.toNat
        = (bytes.val[8]!.val % 2 ^ 2 * 2 ^ 8 + bytes.val[7]!.val) * 2 ^ 1
          + bytes.val[6]!.val / 2 ^ 7 :=
      Lu_i16_or_add _ _ _ _ 1 n5a g67 (Lu_byte_div_lt _ 7 1 (by scalar_tac) (by norm_num))
    have n6 : ((s6 ||| y82 : Std.I16)).bv.toNat
        = bytes.val[9]!.val % 2 ^ 5 * 2 ^ 6 + bytes.val[8]!.val / 2 ^ 2 :=
      Lu_i16_or_add _ _ _ _ 6 f6 g82 (Lu_byte_div_lt _ 2 6 (by scalar_tac) (by norm_num))
    have n7 : ((s7 ||| y95 : Std.I16)).bv.toNat
        = bytes.val[10]!.val * 2 ^ 3 + bytes.val[9]!.val / 2 ^ 5 :=
      Lu_i16_or_add _ _ _ _ 3 f7 g95 (Lu_byte_div_lt _ 5 3 (by scalar_tac) (by norm_num))
    have key : ∀ v : Std.I16, v.val = (decw bytes.val (11 * k) 11 : Int) →
        v.val = (win bytes.val 11 k : Int) := by
      intro v h
      rw [win_eq_decw bytes.val 11 k h17]
      exact h
    have d0 : decw bytes.val (11 * 0) 11
        = (bytes.val[0]!.val + 256 * bytes.val[1]!.val + 65536 * bytes.val[2]!.val)
            % 2048 := by norm_num [decw]
    have d1 : decw bytes.val (11 * 1) 11
        = (bytes.val[1]!.val + 256 * bytes.val[2]!.val + 65536 * bytes.val[3]!.val)
            / 8 % 2048 := by norm_num [decw]
    have d2 : decw bytes.val (11 * 2) 11
        = (bytes.val[2]!.val + 256 * bytes.val[3]!.val + 65536 * bytes.val[4]!.val)
            / 64 % 2048 := by norm_num [decw]
    have d3 : decw bytes.val (11 * 3) 11
        = (bytes.val[4]!.val + 256 * bytes.val[5]!.val + 65536 * bytes.val[6]!.val)
            / 2 % 2048 := by norm_num [decw]
    have d4 : decw bytes.val (11 * 4) 11
        = (bytes.val[5]!.val + 256 * bytes.val[6]!.val + 65536 * bytes.val[7]!.val)
            / 16 % 2048 := by norm_num [decw]
    have d5 : decw bytes.val (11 * 5) 11
        = (bytes.val[6]!.val + 256 * bytes.val[7]!.val + 65536 * bytes.val[8]!.val)
            / 128 % 2048 := by norm_num [decw]
    have d6 : decw bytes.val (11 * 6) 11
        = (bytes.val[8]!.val + 256 * bytes.val[9]!.val + 65536 * bytes.val[10]!.val)
            / 4 % 2048 := by norm_num [decw]
    have d7 : decw bytes.val (11 * 7) 11
        = (bytes.val[9]!.val + 256 * bytes.val[10]!.val + 65536 * bytes.val[11]!.val)
            / 32 % 2048 := by norm_num [decw]
    refine key _ ?_
    interval_cases k
    · obtain ⟨p0, q0⟩ := Lu11_w0 bytes.val[0]!.val bytes.val[1]!.val bytes.val[2]!.val hb0 hb1
      show ((s0 ||| c16 bytes.val[0]! : Std.I16)).val = _
      rw [Lu_i16_val _ _ n0 p0, d0, q0]
    · obtain ⟨p1, q1⟩ := Lu11_w1 bytes.val[1]!.val bytes.val[2]!.val bytes.val[3]!.val hb1 hb2
      show ((s1 ||| y13 : Std.I16)).val = _
      rw [Lu_i16_val _ _ n1 p1, d1, q1]
    · obtain ⟨p2, q2⟩ := Lu11_w2 bytes.val[2]!.val bytes.val[3]!.val bytes.val[4]!.val hb2 hb3
      show (((s2a ||| s2b) ||| y26 : Std.I16)).val = _
      rw [Lu_i16_val _ _ n2 p2, d2, q2]
    · obtain ⟨p3, q3⟩ := Lu11_w3 bytes.val[4]!.val bytes.val[5]!.val bytes.val[6]!.val hb4 hb5
      show ((s3 ||| y41 : Std.I16)).val = _
      rw [Lu_i16_val _ _ n3 p3, d3, q3]
    · obtain ⟨p4, q4⟩ := Lu11_w4 bytes.val[5]!.val bytes.val[6]!.val bytes.val[7]!.val hb5 hb6
      show ((s4 ||| y54 : Std.I16)).val = _
      rw [Lu_i16_val _ _ n4 p4, d4, q4]
    · obtain ⟨p5, q5⟩ := Lu11_w5 bytes.val[6]!.val bytes.val[7]!.val bytes.val[8]!.val hb6 hb7
      show (((s5a ||| s5b) ||| y67 : Std.I16)).val = _
      rw [Lu_i16_val _ _ n5 p5, d5, q5]
    · obtain ⟨p6, q6⟩ := Lu11_w6 bytes.val[8]!.val bytes.val[9]!.val bytes.val[10]!.val hb8 hb9
      show ((s6 ||| y82 : Std.I16)).val = _
      rw [Lu_i16_val _ _ n6 p6, d6, q6]
    · obtain ⟨p7, q7⟩ := Lu11_w7 bytes.val[9]!.val bytes.val[10]!.val bytes.val[11]!.val hb9 hb10
      show ((s7 ||| y95 : Std.I16)).val = _
      rw [Lu_i16_val _ _ n7 p7, d7, q7]

/-! ### Impl side — one 16-lane chunk, at both `d`.

    `deserialize_10` / `deserialize_11` are `deserialize_5` with the half-chunk width
    `5 → 10 → 11`: sub-slice the low half, eight `Array.update`s, sub-slice the high
    half, eight more. REUSES `put16` / `put16_get` and `win_at_offset` from the L5.3
    bank unchanged — the only per-`d` content is the two sub-slice widths. -/

private theorem deserialize_10_eq (bytes : Slice Std.U8) (h_len : bytes.val.length = 20)
    (out : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ∃ v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector,
      libcrux_iot_ml_kem.vector.portable.serialize.deserialize_10 bytes out = .ok v
      ∧ ∀ k : Nat, k < 16 → (v.elements.val[k]!).val = (win bytes.val 10 k : Int) := by
  obtain ⟨s0, hs0, hs0len, hs0get⟩ :=
    slice_index_range_strict bytes 0#usize 10#usize (by scalar_tac) (by rw [h_len]; scalar_tac)
  obtain ⟨s1, hs1, hs1len, hs1get⟩ :=
    slice_index_range_strict bytes 10#usize 20#usize (by scalar_tac) (by rw [h_len]; scalar_tac)
  have hs0len' : s0.val.length = 10 := by rw [hs0len]; scalar_tac
  have hs1len' : s1.val.length = 10 := by rw [hs1len]; scalar_tac
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, hlo, hlow⟩ := deserialize_10_int_lanes_eq s0 hs0len'
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hhi, hhiw⟩ := deserialize_10_int_lanes_eq s1 hs1len'
  -- the two halves sit at byte offsets 0 and 10, i.e. lane offsets 0 and 8
  have hlow' : ∀ k : Nat, k < 8 →
      (([a0, a1, a2, a3, a4, a5, a6, a7] : List Std.I16)[k]!).val
        = (win bytes.val 10 k : Int) := by
    intro k hk
    rw [hlow k hk, win_at_offset bytes.val s0.val 0 10 10 k 0
      (fun t ht => by simpa using hs0get t (by scalar_tac))
      (by omega) (fun t ht => by omega), Nat.zero_add]
  have hhiw' : ∀ k : Nat, k < 8 →
      (([b0, b1, b2, b3, b4, b5, b6, b7] : List Std.I16)[k]!).val
        = (win bytes.val 10 (8 + k) : Int) := by
    intro k hk
    rw [hhiw k hk, win_at_offset bytes.val s1.val 10 10 10 k 8
      (fun t ht => by simpa using hs1get t (by scalar_tac))
      (by omega) (fun t ht => by omega)]
  have hu := fun (i : Std.Usize) (hi : i.val < 16) =>
    fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) => array_update16 A i x hi
  refine ⟨{ elements := put16 out.elements a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 },
    ?_, ?_⟩
  · unfold libcrux_iot_ml_kem.vector.portable.serialize.deserialize_10 put16
    simp only [hs0, hs1, hlo, hhi, Aeneas.Std.bind_tc_ok,
      hu 0#usize (by scalar_tac), hu 1#usize (by scalar_tac), hu 2#usize (by scalar_tac),
      hu 3#usize (by scalar_tac), hu 4#usize (by scalar_tac), hu 5#usize (by scalar_tac),
      hu 6#usize (by scalar_tac), hu 7#usize (by scalar_tac), hu 8#usize (by scalar_tac),
      hu 9#usize (by scalar_tac), hu 10#usize (by scalar_tac), hu 11#usize (by scalar_tac),
      hu 12#usize (by scalar_tac), hu 13#usize (by scalar_tac), hu 14#usize (by scalar_tac),
      hu 15#usize (by scalar_tac)]
    rfl
  · intro k hk
    show ((put16 out.elements a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7).val)[k]!.val = _
    rw [put16_get (k := k) (hk := hk)]
    interval_cases k
    · exact hlow' 0 (by omega)
    · exact hlow' 1 (by omega)
    · exact hlow' 2 (by omega)
    · exact hlow' 3 (by omega)
    · exact hlow' 4 (by omega)
    · exact hlow' 5 (by omega)
    · exact hlow' 6 (by omega)
    · exact hlow' 7 (by omega)
    · exact hhiw' 0 (by omega)
    · exact hhiw' 1 (by omega)
    · exact hhiw' 2 (by omega)
    · exact hhiw' 3 (by omega)
    · exact hhiw' 4 (by omega)
    · exact hhiw' 5 (by omega)
    · exact hhiw' 6 (by omega)
    · exact hhiw' 7 (by omega)

private theorem deserialize_11_eq (bytes : Slice Std.U8) (h_len : bytes.val.length = 22)
    (out : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ∃ v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector,
      libcrux_iot_ml_kem.vector.portable.serialize.deserialize_11 bytes out = .ok v
      ∧ ∀ k : Nat, k < 16 → (v.elements.val[k]!).val = (win bytes.val 11 k : Int) := by
  obtain ⟨s0, hs0, hs0len, hs0get⟩ :=
    slice_index_range_strict bytes 0#usize 11#usize (by scalar_tac) (by rw [h_len]; scalar_tac)
  obtain ⟨s1, hs1, hs1len, hs1get⟩ :=
    slice_index_range_strict bytes 11#usize 22#usize (by scalar_tac) (by rw [h_len]; scalar_tac)
  have hs0len' : s0.val.length = 11 := by rw [hs0len]; scalar_tac
  have hs1len' : s1.val.length = 11 := by rw [hs1len]; scalar_tac
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, hlo, hlow⟩ := deserialize_11_int_lanes_eq s0 hs0len'
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hhi, hhiw⟩ := deserialize_11_int_lanes_eq s1 hs1len'
  have hlow' : ∀ k : Nat, k < 8 →
      (([a0, a1, a2, a3, a4, a5, a6, a7] : List Std.I16)[k]!).val
        = (win bytes.val 11 k : Int) := by
    intro k hk
    rw [hlow k hk, win_at_offset bytes.val s0.val 0 11 11 k 0
      (fun t ht => by simpa using hs0get t (by scalar_tac))
      (by omega) (fun t ht => by omega), Nat.zero_add]
  have hhiw' : ∀ k : Nat, k < 8 →
      (([b0, b1, b2, b3, b4, b5, b6, b7] : List Std.I16)[k]!).val
        = (win bytes.val 11 (8 + k) : Int) := by
    intro k hk
    rw [hhiw k hk, win_at_offset bytes.val s1.val 11 11 11 k 8
      (fun t ht => by simpa using hs1get t (by scalar_tac))
      (by omega) (fun t ht => by omega)]
  have hu := fun (i : Std.Usize) (hi : i.val < 16) =>
    fun (A : Std.Array Std.I16 16#usize) (x : Std.I16) => array_update16 A i x hi
  refine ⟨{ elements := put16 out.elements a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 },
    ?_, ?_⟩
  · unfold libcrux_iot_ml_kem.vector.portable.serialize.deserialize_11 put16
    simp only [hs0, hs1, hlo, hhi, Aeneas.Std.bind_tc_ok,
      hu 0#usize (by scalar_tac), hu 1#usize (by scalar_tac), hu 2#usize (by scalar_tac),
      hu 3#usize (by scalar_tac), hu 4#usize (by scalar_tac), hu 5#usize (by scalar_tac),
      hu 6#usize (by scalar_tac), hu 7#usize (by scalar_tac), hu 8#usize (by scalar_tac),
      hu 9#usize (by scalar_tac), hu 10#usize (by scalar_tac), hu 11#usize (by scalar_tac),
      hu 12#usize (by scalar_tac), hu 13#usize (by scalar_tac), hu 14#usize (by scalar_tac),
      hu 15#usize (by scalar_tac)]
    rfl
  · intro k hk
    show ((put16 out.elements a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7).val)[k]!.val = _
    rw [put16_get (k := k) (hk := hk)]
    interval_cases k
    · exact hlow' 0 (by omega)
    · exact hlow' 1 (by omega)
    · exact hlow' 2 (by omega)
    · exact hlow' 3 (by omega)
    · exact hlow' 4 (by omega)
    · exact hlow' 5 (by omega)
    · exact hlow' 6 (by omega)
    · exact hlow' 7 (by omega)
    · exact hhiw' 0 (by omega)
    · exact hhiw' 1 (by omega)
    · exact hhiw' 2 (by omega)
    · exact hhiw' 3 (by omega)
    · exact hhiw' 4 (by omega)
    · exact hhiw' 5 (by omega)
    · exact hhiw' 6 (by omega)
    · exact hhiw' 7 (by omega)

/-! ### Impl side — the two `chunks_exact` loops.

    The SAME K1 combinator `loop_chunks_exact_pk_spec` at a new chunk size (20 / 22
    where `d = 5` has 10), and the SAME `dcplane` invariant and `chunk_decompress_ok`
    step, which are generic in `d`. Two separate proofs only because the
    machine-generated body names differ per width, exactly as at `dv ∈ {4,5}`. -/

private theorem Lu_loop_10_fc
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 320)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_10_loop
      (vectortraitsOperationsInst := portable_ops_inst)
      { iter := { cs := 20#usize, elements := serialized }, count := 0#usize } re
    ⦃ ⇓ p => ⌜ (Aeneas.Std.RustM.ok (dcplane serialized.val 10 p 16)).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_10_loop
  refine loop_chunks_exact_pk_spec _ re serialized 20#usize 16
    (fun k acc => .ok (dcplane serialized.val 10 acc k)) (by scalar_tac)
    (by simpa [Aeneas.Std.Slice.length] using h_len)
    ((holds_ok _).mpr (by intro i hi; omega)) ?_
  intro acc k rest cnt hk hcnt hrest hsuf hinv
  have hinv' : dcplane serialized.val 10 acc k := (holds_ok _).mp hinv
  have h20 : ((20#usize : Std.Usize).val) = 20 := by scalar_tac
  rw [h20] at hrest
  simp only [h20] at hsuf
  by_cases hlt : k < 16
  · have hrest20 : 20 ≤ rest.length := by
      rw [hrest]
      have h1 : 1 ≤ 16 - k := by omega
      calc (20:Nat) = 1 * 20 := by ring
      _ ≤ (16 - k) * 20 := Nat.mul_le_mul_right 20 h1
    obtain ⟨chunk, drop, cnt', hnext, hcnt', hclen, hdlen, hcget, hdget⟩ :=
      enumerate_chunks_next_cont_drop rest 20#usize cnt
        (by rw [h20]; simpa [Aeneas.Std.Slice.length] using hrest20) (by scalar_tac)
    have hcnt16 : cnt.val < 16 := by omega
    have hlen1 : cnt.val < acc.coefficients.val.length := by
      have hc : acc.coefficients.val.length = 16 := by
        have := acc.coefficients.property; simpa using this
      omega
    have hchunk_len : chunk.val.length = 20 := by
      simpa [Aeneas.Std.Slice.length] using hclen
    have hcser : ∀ m : Nat, m < 20 → chunk.val[m]! = serialized.val[20 * k + m]! := by
      intro m hm
      rw [hcget m (by rw [h20]; omega), hsuf m]
      congr 1; omega
    have hwin : ∀ ℓ : Nat, ℓ < 16 →
        win chunk.val 10 ℓ = win serialized.val 10 (16 * k + ℓ) := by
      intro ℓ hℓ
      exact win_at_offset serialized.val chunk.val (20 * k) 20 10 ℓ (16 * k)
        (fun t ht => hcser t ht) (by ring) (fun t ht => by omega)
    obtain ⟨v, hv_eq, hv⟩ :=
      deserialize_10_eq chunk hchunk_len (acc.coefficients.val[cnt.val]'hlen1)
    have hvwin : ∀ ℓ : Nat, ℓ < 16 →
        (v.elements.val[ℓ]!).val = (win serialized.val 10 (16 * k + ℓ) : Int) := by
      intro ℓ hℓ
      rw [hv ℓ hℓ, hwin ℓ hℓ]
    obtain ⟨w, hw_eq, hw⟩ :=
      chunk_decompress_ok serialized.val 10 (by omega) 10#i32 (by scalar_tac) k v hvwin
    have hlen2 : cnt.val < (Std.Array.set acc.coefficients cnt v).val.length := by
      have hc : (Std.Array.set acc.coefficients cnt v).val.length = 16 := by
        have := (Std.Array.set acc.coefficients cnt v).property; simpa using this
      omega
    have hgi : (Std.Array.set acc.coefficients cnt v).val[cnt.val]!
        = (Std.Array.set acc.coefficients cnt v).val[cnt.val]'hlen2 :=
      getElem!_pos (Std.Array.set acc.coefficients cnt v).val cnt.val hlen2
    have hself : (Std.Array.set acc.coefficients cnt v).val[cnt.val]'hlen2 = v := by
      rw [← hgi, array_set_get16 acc.coefficients cnt v cnt.val hcnt16 hcnt16, if_pos rfl]
    refine triple_of_ok_fc
      (v := .cont ({ iter := { cs := 20#usize, elements := drop }, count := cnt' },
                   { coefficients :=
                       Std.Array.set (Std.Array.set acc.coefficients cnt v) cnt w })) ?_ ?_
    · show libcrux_iot_ml_kem.serialize.deserialize_then_decompress_10_loop.body
        portable_ops_inst { iter := { cs := 20#usize, elements := rest }, count := cnt } acc = _
      unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_10_loop.body
      rw [show (CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
            (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice Std.U8)
            { iter := { cs := 20#usize, elements := rest }, count := cnt })
          = .ok (CoreModels.core.option.Option.Some (cnt, chunk),
                 { iter := { cs := 20#usize, elements := drop }, count := cnt' }) from hnext]
      show (do
          let (t, back) ← Aeneas.Std.Array.index_mut_usize acc.coefficients cnt
          let t1 ← libcrux_iot_ml_kem.vector.portable.serialize.deserialize_10 chunk t
          let (t2, back1) ← Aeneas.Std.Array.index_mut_usize (back t1) cnt
          let t3 ← libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
            10#i32 t2
          RustM.ok (ControlFlow.cont
            (({ iter := { cs := 20#usize, elements := drop }, count := cnt' } : EnumCE),
             ({ coefficients := back1 t3 } :
               libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                 libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)))) = _
      rw [array_index_mut16 acc.coefficients cnt hlen1]
      simp only [Aeneas.Std.bind_tc_ok]
      show (do
          let t1 ← libcrux_iot_ml_kem.vector.portable.serialize.deserialize_10 chunk
            (acc.coefficients.val[cnt.val]'hlen1)
          let (t2, back1) ← Aeneas.Std.Array.index_mut_usize
            (Std.Array.set acc.coefficients cnt t1) cnt
          let t3 ← libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
            10#i32 t2
          RustM.ok (ControlFlow.cont
            (({ iter := { cs := 20#usize, elements := drop }, count := cnt' } : EnumCE),
             ({ coefficients := back1 t3 } :
               libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                 libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)))) = _
      rw [hv_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [array_index_mut16 (Std.Array.set acc.coefficients cnt v) cnt hlen2]
      simp only [Aeneas.Std.bind_tc_ok]
      show (do
          let t3 ← libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
            10#i32 ((Std.Array.set acc.coefficients cnt v).val[cnt.val]'hlen2)
          RustM.ok (ControlFlow.cont
            (({ iter := { cs := 20#usize, elements := drop }, count := cnt' } : EnumCE),
             ({ coefficients :=
                 Std.Array.set (Std.Array.set acc.coefficients cnt v) cnt t3 } :
               libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                 libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)))) = _
      rw [hself, hw_eq]
      rfl
    · refine ⟨hlt, rfl, (by show cnt'.val = k + 1; rw [hcnt', hcnt]), ?_, ?_, ?_⟩
      · show drop.length = (16 - (k + 1)) * (20#usize : Std.Usize).val
        rw [h20, hdlen, hrest]
        have h : (16 - k) = (16 - (k + 1)) + 1 := by omega
        rw [h]; ring_nf; omega
      · intro ℓ
        simp only [h20]
        rw [hdget ℓ]
        simp only [h20]
        rw [hsuf (20 + ℓ)]
        congr 1 <;> omega
      · refine (holds_ok _).mpr ?_
        intro i hi ℓ hℓ
        show ((Std.Array.set (Std.Array.set acc.coefficients cnt v) cnt w).val[i]!).elements.val[ℓ]!.val
          = _
        by_cases hik : i = k
        · subst hik
          rw [array_set_get16 _ _ _ _ (by omega) (by omega), if_pos (by omega)]
          exact hw ℓ hℓ
        · rw [array_set_get16 _ _ _ _ (by omega) (by omega), if_neg (by omega),
            array_set_get16 _ _ _ _ (by omega) (by omega), if_neg (by omega)]
          exact hinv' i (by omega) ℓ hℓ
  · have hk16 : k = 16 := by omega
    subst hk16
    have hrest0 : rest.length = 0 := by simp [hrest]
    refine triple_of_ok_fc (v := .done acc) ?_ ?_
    · show libcrux_iot_ml_kem.serialize.deserialize_then_decompress_10_loop.body
        portable_ops_inst { iter := { cs := 20#usize, elements := rest }, count := cnt } acc = _
      unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_10_loop.body
      rw [show (CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
            (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice Std.U8)
            { iter := { cs := 20#usize, elements := rest }, count := cnt })
          = .ok (CoreModels.core.option.Option.None,
                 { iter := { cs := 20#usize, elements := rest }, count := cnt }) from
          enumerate_chunks_next_done rest 20#usize cnt (by rw [h20, hrest0]; omega)]
      rfl
    · exact (holds_ok _).mpr hinv'

private theorem Lu_loop_11_fc
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 352)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_11_loop
      (vectortraitsOperationsInst := portable_ops_inst)
      { iter := { cs := 22#usize, elements := serialized }, count := 0#usize } re
    ⦃ ⇓ p => ⌜ (Aeneas.Std.RustM.ok (dcplane serialized.val 11 p 16)).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_11_loop
  refine loop_chunks_exact_pk_spec _ re serialized 22#usize 16
    (fun k acc => .ok (dcplane serialized.val 11 acc k)) (by scalar_tac)
    (by simpa [Aeneas.Std.Slice.length] using h_len)
    ((holds_ok _).mpr (by intro i hi; omega)) ?_
  intro acc k rest cnt hk hcnt hrest hsuf hinv
  have hinv' : dcplane serialized.val 11 acc k := (holds_ok _).mp hinv
  have h22 : ((22#usize : Std.Usize).val) = 22 := by scalar_tac
  rw [h22] at hrest
  simp only [h22] at hsuf
  by_cases hlt : k < 16
  · have hrest22 : 22 ≤ rest.length := by
      rw [hrest]
      have h1 : 1 ≤ 16 - k := by omega
      calc (22:Nat) = 1 * 22 := by ring
      _ ≤ (16 - k) * 22 := Nat.mul_le_mul_right 22 h1
    obtain ⟨chunk, drop, cnt', hnext, hcnt', hclen, hdlen, hcget, hdget⟩ :=
      enumerate_chunks_next_cont_drop rest 22#usize cnt
        (by rw [h22]; simpa [Aeneas.Std.Slice.length] using hrest22) (by scalar_tac)
    have hcnt16 : cnt.val < 16 := by omega
    have hlen1 : cnt.val < acc.coefficients.val.length := by
      have hc : acc.coefficients.val.length = 16 := by
        have := acc.coefficients.property; simpa using this
      omega
    have hchunk_len : chunk.val.length = 22 := by
      simpa [Aeneas.Std.Slice.length] using hclen
    have hcser : ∀ m : Nat, m < 22 → chunk.val[m]! = serialized.val[22 * k + m]! := by
      intro m hm
      rw [hcget m (by rw [h22]; omega), hsuf m]
      congr 1; omega
    have hwin : ∀ ℓ : Nat, ℓ < 16 →
        win chunk.val 11 ℓ = win serialized.val 11 (16 * k + ℓ) := by
      intro ℓ hℓ
      exact win_at_offset serialized.val chunk.val (22 * k) 22 11 ℓ (16 * k)
        (fun t ht => hcser t ht) (by ring) (fun t ht => by omega)
    obtain ⟨v, hv_eq, hv⟩ :=
      deserialize_11_eq chunk hchunk_len (acc.coefficients.val[cnt.val]'hlen1)
    have hvwin : ∀ ℓ : Nat, ℓ < 16 →
        (v.elements.val[ℓ]!).val = (win serialized.val 11 (16 * k + ℓ) : Int) := by
      intro ℓ hℓ
      rw [hv ℓ hℓ, hwin ℓ hℓ]
    obtain ⟨w, hw_eq, hw⟩ :=
      chunk_decompress_ok serialized.val 11 (by omega) 11#i32 (by scalar_tac) k v hvwin
    have hlen2 : cnt.val < (Std.Array.set acc.coefficients cnt v).val.length := by
      have hc : (Std.Array.set acc.coefficients cnt v).val.length = 16 := by
        have := (Std.Array.set acc.coefficients cnt v).property; simpa using this
      omega
    have hgi : (Std.Array.set acc.coefficients cnt v).val[cnt.val]!
        = (Std.Array.set acc.coefficients cnt v).val[cnt.val]'hlen2 :=
      getElem!_pos (Std.Array.set acc.coefficients cnt v).val cnt.val hlen2
    have hself : (Std.Array.set acc.coefficients cnt v).val[cnt.val]'hlen2 = v := by
      rw [← hgi, array_set_get16 acc.coefficients cnt v cnt.val hcnt16 hcnt16, if_pos rfl]
    refine triple_of_ok_fc
      (v := .cont ({ iter := { cs := 22#usize, elements := drop }, count := cnt' },
                   { coefficients :=
                       Std.Array.set (Std.Array.set acc.coefficients cnt v) cnt w })) ?_ ?_
    · show libcrux_iot_ml_kem.serialize.deserialize_then_decompress_11_loop.body
        portable_ops_inst { iter := { cs := 22#usize, elements := rest }, count := cnt } acc = _
      unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_11_loop.body
      rw [show (CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
            (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice Std.U8)
            { iter := { cs := 22#usize, elements := rest }, count := cnt })
          = .ok (CoreModels.core.option.Option.Some (cnt, chunk),
                 { iter := { cs := 22#usize, elements := drop }, count := cnt' }) from hnext]
      show (do
          let (t, back) ← Aeneas.Std.Array.index_mut_usize acc.coefficients cnt
          let t1 ← libcrux_iot_ml_kem.vector.portable.serialize.deserialize_11 chunk t
          let (t2, back1) ← Aeneas.Std.Array.index_mut_usize (back t1) cnt
          let t3 ← libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
            11#i32 t2
          RustM.ok (ControlFlow.cont
            (({ iter := { cs := 22#usize, elements := drop }, count := cnt' } : EnumCE),
             ({ coefficients := back1 t3 } :
               libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                 libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)))) = _
      rw [array_index_mut16 acc.coefficients cnt hlen1]
      simp only [Aeneas.Std.bind_tc_ok]
      show (do
          let t1 ← libcrux_iot_ml_kem.vector.portable.serialize.deserialize_11 chunk
            (acc.coefficients.val[cnt.val]'hlen1)
          let (t2, back1) ← Aeneas.Std.Array.index_mut_usize
            (Std.Array.set acc.coefficients cnt t1) cnt
          let t3 ← libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
            11#i32 t2
          RustM.ok (ControlFlow.cont
            (({ iter := { cs := 22#usize, elements := drop }, count := cnt' } : EnumCE),
             ({ coefficients := back1 t3 } :
               libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                 libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)))) = _
      rw [hv_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [array_index_mut16 (Std.Array.set acc.coefficients cnt v) cnt hlen2]
      simp only [Aeneas.Std.bind_tc_ok]
      show (do
          let t3 ← libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
            11#i32 ((Std.Array.set acc.coefficients cnt v).val[cnt.val]'hlen2)
          RustM.ok (ControlFlow.cont
            (({ iter := { cs := 22#usize, elements := drop }, count := cnt' } : EnumCE),
             ({ coefficients :=
                 Std.Array.set (Std.Array.set acc.coefficients cnt v) cnt t3 } :
               libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                 libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)))) = _
      rw [hself, hw_eq]
      rfl
    · refine ⟨hlt, rfl, (by show cnt'.val = k + 1; rw [hcnt', hcnt]), ?_, ?_, ?_⟩
      · show drop.length = (16 - (k + 1)) * (22#usize : Std.Usize).val
        rw [h22, hdlen, hrest]
        have h : (16 - k) = (16 - (k + 1)) + 1 := by omega
        rw [h]; ring_nf; omega
      · intro ℓ
        simp only [h22]
        rw [hdget ℓ]
        simp only [h22]
        rw [hsuf (22 + ℓ)]
        congr 1 <;> omega
      · refine (holds_ok _).mpr ?_
        intro i hi ℓ hℓ
        show ((Std.Array.set (Std.Array.set acc.coefficients cnt v) cnt w).val[i]!).elements.val[ℓ]!.val
          = _
        by_cases hik : i = k
        · subst hik
          rw [array_set_get16 _ _ _ _ (by omega) (by omega), if_pos (by omega)]
          exact hw ℓ hℓ
        · rw [array_set_get16 _ _ _ _ (by omega) (by omega), if_neg (by omega),
            array_set_get16 _ _ _ _ (by omega) (by omega), if_neg (by omega)]
          exact hinv' i (by omega) ℓ hℓ
  · have hk16 : k = 16 := by omega
    subst hk16
    have hrest0 : rest.length = 0 := by simp [hrest]
    refine triple_of_ok_fc (v := .done acc) ?_ ?_
    · show libcrux_iot_ml_kem.serialize.deserialize_then_decompress_11_loop.body
        portable_ops_inst { iter := { cs := 22#usize, elements := rest }, count := cnt } acc = _
      unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_11_loop.body
      rw [show (CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
            (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice Std.U8)
            { iter := { cs := 22#usize, elements := rest }, count := cnt })
          = .ok (CoreModels.core.option.Option.None,
                 { iter := { cs := 22#usize, elements := rest }, count := cnt }) from
          enumerate_chunks_next_done rest 22#usize cnt (by rw [h22, hrest0]; omega)]
      rfl
    · exact (holds_ok _).mpr hinv'

/-- Impl apex at `d = 10`: `chunks_exact 20` + `enumerate` is the initial loop state. -/
private theorem Lu_impl_10_fc
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 320)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_10
      (vectortraitsOperationsInst := portable_ops_inst) serialized re
    ⦃ ⇓ p => ⌜ (Aeneas.Std.RustM.ok (dcplane serialized.val 10 p 16)).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_10
  rw [show (CoreModels.core.slice.Slice.chunks_exact serialized (20#usize : Std.Usize))
        = .ok { cs := 20#usize, elements := serialized } from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show (CoreModels.core.iter.traits.iterator.Iterator.enumerate.default
        (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice
          Std.U8)
        { cs := (20#usize : Std.Usize), elements := serialized })
      = .ok ({ iter := { cs := 20#usize, elements := serialized }, count := 0#usize } : EnumCE)
      from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  exact Lu_loop_10_fc serialized h_len re

/-- Impl apex at `d = 11`. -/
private theorem Lu_impl_11_fc
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 352)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_11
      (vectortraitsOperationsInst := portable_ops_inst) serialized re
    ⦃ ⇓ p => ⌜ (Aeneas.Std.RustM.ok (dcplane serialized.val 11 p 16)).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.deserialize_then_decompress_11
  rw [show (CoreModels.core.slice.Slice.chunks_exact serialized (22#usize : Std.Usize))
        = .ok { cs := 22#usize, elements := serialized } from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show (CoreModels.core.iter.traits.iterator.Iterator.enumerate.default
        (CoreModels.core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice
          Std.U8)
        { cs := (22#usize : Std.Usize), elements := serialized })
      = .ok ({ iter := { cs := 22#usize, elements := serialized }, count := 0#usize } : EnumCE)
      from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  exact Lu_loop_11_fc serialized h_len re

/-! ### Spec side — `byte_decode_dyn` at `du ∈ {10, 11}`.

    The `d`-generic decode ladder (`bytes_to_bits_gen` … `byte_decode_gen_eq`) built for
    L5.3 is REUSED verbatim: its side conditions are `d ≤ 12` and `2 ^ d ≤ 3329`, and
    `2 ^ 11 = 2048 ≤ 3329`, so both new widths are inside it. Only the `match d.val`
    dispatch is per-`d`, so this is the `byte_decode_dyn_45_eq` argument at the 10 and
    11 arms (320 / 2560 and 352 / 2816 in place of 128 / 1024 and 160 / 1280). -/

private theorem byte_decode_dyn_1011_eq (b : Slice Std.U8) (du : Std.Usize)
    (hdu : du.val = 10 ∨ du.val = 11) (hb : b.val.length = 32 * du.val) :
    ∃ arr : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize,
      hacspec_ml_kem.serialize.byte_decode_dyn b du = .ok arr
      ∧ ∀ k : Nat, k < 256 →
          arr.val[k]! = ({ val := u16OfNat (win b.val du.val k) }
                          : hacspec_ml_kem.parameters.FieldElement) := by
  rcases hdu with h | h
  · have hdu10 : du = 10#usize := Aeneas.Std.UScalar.eq_of_val_eq (by rw [h]; scalar_tac)
    subst hdu10
    have hb320 : b.val.length = ((320#usize : Std.Usize)).val := by rw [hb]; scalar_tac
    have hle : ((10#usize : Std.Usize) ≤ (12#usize : Std.Usize)) := by scalar_tac
    have h10 : ((10#usize : Std.Usize)).val = 10 := by scalar_tac
    have e2 : ((32#usize : Std.Usize) * (10#usize : Std.Usize) : RustM Std.Usize)
        = .ok (320#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
    obtain ⟨arr, harr, harrget⟩ :=
      byte_decode_gen_eq 10#usize (⟨b.val, hb320⟩ : Std.Array Std.U8 320#usize) 2560#usize
        (by scalar_tac) (by rw [h10]; norm_num) (by scalar_tac) (by scalar_tac)
    refine ⟨arr, ?_, harrget⟩
    unfold hacspec_ml_kem.serialize.byte_decode_dyn
    -- (the `massert` prelude this `simp only` discharged is gone from the
    -- hax v0.4.0-rc.1 spec extraction; `unfold` now lands directly on the
    -- `match d.val` dispatch that the `show` below selects from)
    show (do
        let r ←
          CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
            (320#usize : Std.Usize) b
        let a ←
          CoreModels.core.result.Result.unwrap
            CoreModels.core.array.TryFromSliceError.Insts.CoreFmtDebug r
        hacspec_ml_kem.serialize.byte_decode (D32 := 320#usize) 2560#usize a 10#usize) = _
    rw [show
        CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
            (320#usize : Std.Usize) b
          = .ok (CoreModels.core.result.Result.Ok
              (⟨b.val, hb320⟩ : Std.Array Std.U8 320#usize)) from by
      unfold
        CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
      rw [dif_pos (slice_len_eq_of b 320#usize hb320)]]
    simp only [Aeneas.Std.bind_tc_ok, CoreModels.core.result.Result.unwrap]
    exact harr
  · have hdu11 : du = 11#usize := Aeneas.Std.UScalar.eq_of_val_eq (by rw [h]; scalar_tac)
    subst hdu11
    have hb352 : b.val.length = ((352#usize : Std.Usize)).val := by rw [hb]; scalar_tac
    have hle : ((11#usize : Std.Usize) ≤ (12#usize : Std.Usize)) := by scalar_tac
    have h11 : ((11#usize : Std.Usize)).val = 11 := by scalar_tac
    have e2 : ((32#usize : Std.Usize) * (11#usize : Std.Usize) : RustM Std.Usize)
        = .ok (352#usize : Std.Usize) := usize_mul_lit _ _ _ (by scalar_tac) (by scalar_tac)
    obtain ⟨arr, harr, harrget⟩ :=
      byte_decode_gen_eq 11#usize (⟨b.val, hb352⟩ : Std.Array Std.U8 352#usize) 2816#usize
        (by scalar_tac) (by rw [h11]; norm_num) (by scalar_tac) (by scalar_tac)
    refine ⟨arr, ?_, harrget⟩
    unfold hacspec_ml_kem.serialize.byte_decode_dyn
    -- (the `massert` prelude this `simp only` discharged is gone from the
    -- hax v0.4.0-rc.1 spec extraction; `unfold` now lands directly on the
    -- `match d.val` dispatch that the `show` below selects from)
    show (do
        let r ←
          CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
            (352#usize : Std.Usize) b
        let a ←
          CoreModels.core.result.Result.unwrap
            CoreModels.core.array.TryFromSliceError.Insts.CoreFmtDebug r
        hacspec_ml_kem.serialize.byte_decode (D32 := 352#usize) 2816#usize a 11#usize) = _
    rw [show
        CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
            (352#usize : Std.Usize) b
          = .ok (CoreModels.core.result.Result.Ok
              (⟨b.val, hb352⟩ : Std.Array Std.U8 352#usize)) from by
      unfold
        CoreModels.core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
      rw [dif_pos (slice_len_eq_of b 352#usize hb352)]]
    simp only [Aeneas.Std.bind_tc_ok, CoreModels.core.result.Result.unwrap]
    exact harr

/-- **Spec-side apex.** `L53_spec_eq` at the other two widths: `decompress_gen_eq` and
    `decompress_closure_gen` are already generic in `d < 12`, so the ONLY change is the
    `byte_decode_dyn` citation. -/
private theorem Lu_spec_eq (serialized : Slice Std.U8) (du : Std.Usize)
    (hdu : du.val = 10 ∨ du.val = 11) (hlen : serialized.val.length = 32 * du.val)
    (p : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
           libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hdc : dcplane serialized.val du.val p 16) :
    hacspec_ml_kem.serialize.deserialize_then_decompress_v serialized du
      = .ok (lift_poly p) := by
  have hd : du.val < 12 := by rcases hdu with h | h <;> omega
  have hp2 : (2:Nat) ^ du.val ≤ 2048 := by rcases hdu with h | h <;> rw [h] <;> norm_num
  obtain ⟨arr, harr, harrget⟩ := byte_decode_dyn_1011_eq serialized du hdu hlen
  have hval : ∀ k : Nat, k < 256 → (arr.val[k]!).val.val = win serialized.val du.val k := by
    intro k hk
    rw [harrget k hk]
    exact u16OfNat_val _ (by have h1 := win_lt serialized.val du.val k; scalar_tac)
  rw [L53_spec_unfold, harr]
  simp only [Aeneas.Std.bind_tc_ok]
  refine decompress_gen_eq du arr hd p ?_ ?_
  · intro k hk
    rw [hval k hk]
    exact win_lt _ _ _
  · intro k hk
    rw [hval k hk]
    have h := hdc (k / 16) (by omega) (k % 16) (by omega)
    rw [show 16 * (k / 16) + k % 16 = k from by omega] at h
    exact h

/-! ### The dispatcher rung.

    COPIES `L53_dispatch_of_pre` (K9, private): the impl match is the same shape,
    `match U_COMPRESSION_FACTOR as u32 { 10, 11, _ => panic }`. Cheaper here than at
    L5.3, which had to DERIVE `dv ∈ {4,5}` from `h_rank` + `h_cf` through
    `vector_v_compression_factor`; upstream states the width condition directly on this
    function, so `h_cf` pins `du` with no intermediate step. -/

private theorem Lu_dispatch_eq_d10 (serialized : Slice Std.U8)
    (output : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_u
      (vectortraitsOperationsInst := portable_ops_inst) 10#usize serialized output
    = libcrux_iot_ml_kem.serialize.deserialize_then_decompress_10
        (vectortraitsOperationsInst := portable_ops_inst) serialized output := by
  simp only [libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_u,
    Aeneas.Std.lift, Aeneas.Std.bind_tc_ok, Std.UScalar.cast, Std.UScalarTy.U32_numBits_eq]
  simp

private theorem Lu_dispatch_eq_d11 (serialized : Slice Std.U8)
    (output : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_u
      (vectortraitsOperationsInst := portable_ops_inst) 11#usize serialized output
    = libcrux_iot_ml_kem.serialize.deserialize_then_decompress_11
        (vectortraitsOperationsInst := portable_ops_inst) serialized output := by
  simp only [libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_u,
    Aeneas.Std.lift, Aeneas.Std.bind_tc_ok, Std.UScalar.cast, Std.UScalarTy.U32_numBits_eq]
  simp

/-- Under `h_cf`, the dispatcher reduces to exactly one of the two real arms — the
    `unreachable!()` arm is gone. -/
private theorem Lu_dispatch_of_pre (U_COMPRESSION_FACTOR : Std.Usize)
    (serialized : Slice Std.U8)
    (output : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_du : U_COMPRESSION_FACTOR.val = 10 ∨ U_COMPRESSION_FACTOR.val = 11) :
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_u
      (vectortraitsOperationsInst := portable_ops_inst)
      U_COMPRESSION_FACTOR serialized output
    = if U_COMPRESSION_FACTOR.val = 10 then
        libcrux_iot_ml_kem.serialize.deserialize_then_decompress_10
          (vectortraitsOperationsInst := portable_ops_inst) serialized output
      else
        libcrux_iot_ml_kem.serialize.deserialize_then_decompress_11
          (vectortraitsOperationsInst := portable_ops_inst) serialized output := by
  rcases h_du with h | h
  · rw [show U_COMPRESSION_FACTOR = 10#usize from
        Aeneas.Std.UScalar.eq_of_val_eq (by scalar_tac), Lu_dispatch_eq_d10]
    simp
  · rw [show U_COMPRESSION_FACTOR = 11#usize from
        Aeneas.Std.UScalar.eq_of_val_eq (by scalar_tac), Lu_dispatch_eq_d11]
    simp

end LuBank

/-- **INC-2a.4** — `serialize.deserialize_then_decompress_ring_element_u`.

    `ByteDecode_du` then `Decompress_du` over ONE ring element, at `du ∈ {10, 11}`.
    The decode dual of L5.3 (`deserialize_then_decompress_ring_element_v_fc`) at the
    other two widths; the spec side is the SAME hacspec function, since it is
    width-generic (see the section note above).

    Hypotheses transcribed VERBATIM from the upstream contract
    (libcrux-ml-kem/src/serialize.rs, `deserialize_then_decompress_ring_element_u`):
      (COMPRESSION_FACTOR == 10 || COMPRESSION_FACTOR == 11)
      && serialized.len() == 32 * COMPRESSION_FACTOR
    Upstream states the width condition DIRECTLY here — there is no `is_rank` and no
    `vector_u_compression_factor` indirection to transcribe, unlike L5.3/L5.4 — so none
    is added. The post is upstream's `ensures` in both conjuncts: the spec equation, and
    `is_bounded_poly (sz 3328) $result`. -/
@[spec]
theorem deserialize_then_decompress_ring_element_u_fc
    (U_COMPRESSION_FACTOR : Std.Usize)
    (serialized : Slice Std.U8)
    (output : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_cf : U_COMPRESSION_FACTOR.val = 10 ∨ U_COMPRESSION_FACTOR.val = 11)
    (h_len : serialized.length = 32 * U_COMPRESSION_FACTOR.val) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_u
      (vectortraitsOperationsInst := portable_ops_inst)
      U_COMPRESSION_FACTOR serialized output
    ⦃ ⇓ p => ⌜ hacspec_ml_kem.serialize.deserialize_then_decompress_v
                  serialized U_COMPRESSION_FACTOR
                = .ok (lift_poly p)
                ∧ (∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
                    ((p.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 3328) ⌝ ⦄ := by
  have hlen' : serialized.val.length = 32 * U_COMPRESSION_FACTOR.val := h_len
  -- FIRST RUNG (`Lu_dispatch_of_pre`): the `unreachable!()` arm is gone.
  rw [Lu_dispatch_of_pre U_COMPRESSION_FACTOR serialized output h_cf]
  rcases h_cf with h10 | h11
  · rw [if_pos h10]
    have hlen10 : serialized.val.length = 320 := by rw [hlen', h10]
    obtain ⟨p, hp_eq, hp⟩ := triple_exists_ok_fc (Lu_impl_10_fc serialized hlen10 output)
    have hdc : dcplane serialized.val 10 p 16 := (holds_ok _).mp hp
    have hdc' : dcplane serialized.val U_COMPRESSION_FACTOR.val p 16 := by rw [h10]; exact hdc
    refine triple_of_ok_fc hp_eq
      ⟨Lu_spec_eq serialized U_COMPRESSION_FACTOR (Or.inl h10) hlen' p hdc', ?_⟩
    -- BOUND CONJUNCT: every lane is `(2·w·q + 2^d) / 2^(d+1)` with `w < 2^d`, hence
    -- < 3329, i.e. ≤ 3328. The tight maxima are 3326 (du = 10) / 3327 (du = 11), so
    -- the contract's 3328 is sound with one to spare.
    intro chunk hchunk ℓ hℓ
    have h := hdc chunk hchunk ℓ hℓ
    have hb := win_dec_lt (win serialized.val 10 (16 * chunk + ℓ)) 10 (win_lt _ _ _) (by omega)
    omega
  · rw [if_neg (by omega)]
    have hlen11 : serialized.val.length = 352 := by rw [hlen', h11]
    obtain ⟨p, hp_eq, hp⟩ := triple_exists_ok_fc (Lu_impl_11_fc serialized hlen11 output)
    have hdc : dcplane serialized.val 11 p 16 := (holds_ok _).mp hp
    have hdc' : dcplane serialized.val U_COMPRESSION_FACTOR.val p 16 := by rw [h11]; exact hdc
    refine triple_of_ok_fc hp_eq
      ⟨Lu_spec_eq serialized U_COMPRESSION_FACTOR (Or.inr h11) hlen' p hdc', ?_⟩
    intro chunk hchunk ℓ hℓ
    have h := hdc chunk hchunk ℓ hℓ
    have hb := win_dec_lt (win serialized.val 11 (16 * chunk + ℓ)) 11 (win_lt _ _ _) (by omega)
    omega

/-! ## PROVER bank for INC-2a.5 — the ENCODE seams at `du ∈ {10, 11}`.

    The `du ∈ {4,5}` sibling (L54Bank) is the shape; everything generic is CITED from it
    unchanged (`lanewin`, `cLane`, `cByte`, `cBit`, `bitSum_cBit_eq_cByte` = M-C(2),
    `byte_encode_gen_eq`, `compress_vec_eq`, `to_unsigned_fm_eq`, `compress_barrett_eq`).
    Only the two impl seams are new, and they are new in ONE structural way: at `d ≥ 8`
    every output byte reads at most TWO lanes, whereas at `d ∈ {4,5}` three could meet in
    one byte. Concretely: M-C(2)'s third window term carries a factor `2 ^ (2d - r)` with
    `r < d`, so `2d - r > d >= 10 > 8` and it dies under the byte truncation. Every byte of
    both widths is therefore `(hi_field <<< e) ||| (lo >>> s)` with `s + e = d` — or a
    single-lane `(lo >>> s) & 255` when the lane still has 8 bits left — and each such
    identity is one `omega` over three lane variables (`Le10_b*` / `Le11_b*` below).

    The other difference from `d ∈ {4,5}`: the bit work happens at `U8` here (the impl
    narrows each field with `as_u8` BEFORE shifting), not at `I16`, because a `d`-bit lane
    no longer fits in a byte and the impl never builds a wide intermediate. -/

section LuEncBank

open Aeneas.Std
open libcrux_iot_ml_kem.Util.LoopSpecs

/-! ### Toolkit. Four one-liners; the `I16` half is L54Bank's, restated at `U8`. -/

/-- `x &&& (2 ^ k - 1)` is `x % 2 ^ k` at `I16`. `Lu_c16_and_mask` without the `c16`:
    the encode seams mask the LANE, which is already an `I16`. -/
private theorem Le_i16_mask (x M : Std.I16) (k : Nat) (hM : M.bv.toNat = 2 ^ k - 1) :
    ((x &&& M : Std.I16)).bv.toNat = x.bv.toNat % 2 ^ k := by
  show (x.bv &&& M.bv).toNat = _
  rw [BitVec.toNat_and, hM, Nat.and_two_pow_sub_one_eq_mod]

/-- `as_u8` of a masked lane. `c8` truncates at 256, so the outer `% 256` is the cast's
    and the inner `% 2 ^ k` is the mask's. -/
private theorem Le_c8_mask (x M : Std.I16) (k : Nat) (hM : M.bv.toNat = 2 ^ k - 1) :
    (c8 (x &&& M)).val = x.bv.toNat % 2 ^ k % 256 := by
  rw [c8_val, Le_i16_mask x M k hM]

/-- The value of a `U8` left shift that does not truncate. `u8_shl_bvp` supplies the
    `RustM` half; this is the arithmetic half, and it needs no shift-amount side
    condition because the guard `hx` already rules truncation out. -/
private theorem Le_shl_val (x : Std.U8) (e : Nat) (hx : x.val * 2 ^ e < 256) :
    ((⟨x.bv <<< e⟩ : Std.U8)).val = x.val * 2 ^ e := by
  show (x.bv <<< e).toNat = _
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt (by simpa using hx)

/-- "OR == + when the fields are disjoint", at `U8`. -/
private theorem Le_u8_or_add (x y : Std.U8) (hi lo e : Nat)
    (hx : x.val = hi * 2 ^ e) (hy : y.val = lo) (hlo : lo < 2 ^ e) :
    ((x ||| y : Std.U8)).val = hi * 2 ^ e + lo := by
  rw [Std.UScalar.val_or, hx, hy, Nat.or_comm, enc_or_shift_eq_add hlo]

/-- The `U8` declassify the two `serialize_*_int` tails end with is the identity. -/
private theorem Le_declassify (x : Std.U8) :
    libcrux_secrets.traits.Declassify.Blanket.declassify x = .ok x := by
  unfold libcrux_secrets.traits.Declassify.Blanket.declassify
  simp

/-- Reading back one cell of a `Slice.set`. -/
private theorem Le_set_get (s : Slice Std.U8) (i : Std.Usize) (z : Std.U8) (n : Nat)
    (hlen : i.val < s.val.length) :
    ((s.set i z).val[n]!) = if n = i.val then z else s.val[n]! := by
  rw [Aeneas.Std.Slice.set_val_eq]
  by_cases h : n = i.val
  · subst h; simp_lists
  · simp_lists [h]

/-- **The write-back step.** `serialize_10` / `serialize_11` end in a 20- resp. 22-deep
    `Slice.update` chain; walking it with one `interval_cases` over the whole chain is
    quadratic (`s5set_get` already needs a 4M heartbeat bump at depth 10). This threads
    the written-prefix property one cell at a time instead, which is linear. -/
private theorem Le_set_step (s : Slice Std.U8) (F : Nat → Nat) (k : Nat) (i : Std.Usize)
    (hi : i.val = k) (hlen : k < s.val.length)
    (hs : ∀ n : Nat, n < k → (s.val[n]!).val = F n)
    (z : Std.U8) (hz : z.val = F k) :
    ∀ n : Nat, n < k + 1 → ((s.set i z).val[n]!).val = F n := by
  intro n hn
  rw [Le_set_get _ _ _ _ (by rw [hi]; exact hlen)]
  by_cases hnk : n = i.val
  · rw [if_pos hnk, hz]; congr 1; omega
  · rw [if_neg hnk]; exact hs n (by rw [hi] at hnk; omega)

/-- One link of the write-back chain, with the intermediate slice kept OPAQUE. That is
    the point: threading the chain through `obtain` keeps every goal the size of a single
    `Slice.update`, where writing the 20-fold `set` term out (as `s4set` / `s5set` do at
    depth 8 and 10) makes each later goal carry all its predecessors. -/
theorem Le_update_step (F : Nat → Nat) (N : Nat) (s : Slice Std.U8) (k : Nat)
    (i : Std.Usize) (z : Std.U8) (hi : i.val = k) (hk : k < N) (hslen : s.val.length = N)
    (hs : ∀ n : Nat, n < k → (s.val[n]!).val = F n) (hz : z.val = F k) :
    ∃ s' : Slice Std.U8, Aeneas.Std.Slice.update s i z = .ok s'
      ∧ s'.val.length = N
      ∧ ∀ n : Nat, n < k + 1 → (s'.val[n]!).val = F n := by
  refine ⟨s.set i z, slice_update_eq s i z (by rw [hslen, hi]; omega), ?_,
    Le_set_step s F k i hi (by rw [hslen]; omega) hs z hz⟩
  simp only [Aeneas.Std.Slice.set_val_eq, List.length_set]; exact hslen

/-! ### The five pure-`Nat` byte identities at `d = 10`.

    Pulled out as separate lemmas for the reason recorded above `Lu10_w0`: in-line, each
    `omega` would see the seam's whole mask/shift context. `a`, `b` are the two lanes the
    byte reads and `c` the (dead) third window lane. -/

private theorem Le10_b0 (a b c : Nat) (ha : a < 1024) :
    a % 2 ^ 8 % 256 = (a / 2 ^ 0 + b * 2 ^ 10 + c * 2 ^ 20) % 256 := by
  norm_num; omega

private theorem Le10_b1 (a b c : Nat) (ha : a < 1024) (hb : b < 1024) :
    b % 2 ^ 6 % 256 * 2 ^ 2 + a / 2 ^ 8 % 2 ^ 2 % 256
      = (a / 2 ^ 8 + b * 2 ^ 2 + c * 2 ^ 12) % 256 := by
  norm_num; omega

private theorem Le10_b2 (a b c : Nat) (ha : a < 1024) (hb : b < 1024) :
    b % 2 ^ 4 % 256 * 2 ^ 4 + a / 2 ^ 6 % 2 ^ 4 % 256
      = (a / 2 ^ 6 + b * 2 ^ 4 + c * 2 ^ 14) % 256 := by
  norm_num; omega

private theorem Le10_b3 (a b c : Nat) (ha : a < 1024) (hb : b < 1024) :
    b % 2 ^ 2 % 256 * 2 ^ 6 + a / 2 ^ 4 % 2 ^ 6 % 256
      = (a / 2 ^ 4 + b * 2 ^ 6 + c * 2 ^ 16) % 256 := by
  norm_num; omega

private theorem Le10_b4 (a b c : Nat) (ha : a < 1024) :
    a / 2 ^ 2 % 2 ^ 8 % 256 = (a / 2 ^ 2 + b * 2 ^ 8 + c * 2 ^ 18) % 256 := by
  norm_num; omega

/-! ### IMPL SEAM at `d = 10`, byte level. FOUR lanes to FIVE bytes — the grouping no
    existing seam in this tree uses (`serialize_4` / `serialize_5` / `serialize_11` all
    split the 16 lanes `2 × 8`). Bytes 0 and 4 are single-lane; 1, 2, 3 straddle. -/

private def e10b0 (x0 : Std.I16) : Std.U8 := c8 (x0 &&& 255#i16)

private def e10b1 (x0 x1 : Std.I16) : Std.U8 :=
  (⟨(c8 (x1 &&& 63#i16)).bv <<< 2⟩ : Std.U8)
    ||| c8 ((⟨x0.bv.sshiftRight 8⟩ : Std.I16) &&& 3#i16)

private def e10b2 (x1 x2 : Std.I16) : Std.U8 :=
  (⟨(c8 (x2 &&& 15#i16)).bv <<< 4⟩ : Std.U8)
    ||| c8 ((⟨x1.bv.sshiftRight 6⟩ : Std.I16) &&& 15#i16)

private def e10b3 (x2 x3 : Std.I16) : Std.U8 :=
  (⟨(c8 (x3 &&& 3#i16)).bv <<< 6⟩ : Std.U8)
    ||| c8 ((⟨x2.bv.sshiftRight 4⟩ : Std.I16) &&& 63#i16)

private def e10b4 (x3 : Std.I16) : Std.U8 :=
  c8 ((⟨x3.bv.sshiftRight 2⟩ : Std.I16) &&& 255#i16)

private theorem serialize_10_int_eq (v : Slice Std.I16) (h : 4 ≤ v.val.length) :
    libcrux_iot_ml_kem.vector.portable.serialize.serialize_10_int v
      = .ok (e10b0 v.val[0]!, e10b1 v.val[0]! v.val[1]!, e10b2 v.val[1]! v.val[2]!,
             e10b3 v.val[2]! v.val[3]!, e10b4 v.val[3]!) := by
  have hi0 : Aeneas.Std.Slice.index_usize v 0#usize = .ok (v.val[0]!) :=
    slice_index_usize_eq v 0#usize (by scalar_tac)
  have hi1 : Aeneas.Std.Slice.index_usize v 1#usize = .ok (v.val[1]!) :=
    slice_index_usize_eq v 1#usize (by scalar_tac)
  have hi2 : Aeneas.Std.Slice.index_usize v 2#usize = .ok (v.val[2]!) :=
    slice_index_usize_eq v 2#usize (by scalar_tac)
  have hi3 : Aeneas.Std.Slice.index_usize v 3#usize = .ok (v.val[3]!) :=
    slice_index_usize_eq v 3#usize (by scalar_tac)
  have ha : ((c8 (v.val[1]! &&& 63#i16)) <<< (2#i32) : RustM Std.U8)
      = .ok ⟨(c8 (v.val[1]! &&& 63#i16)).bv <<< 2⟩ := u8_shl_bvp _ _ 2 (by scalar_tac) (by omega)
  have hb : ((c8 (v.val[2]! &&& 15#i16)) <<< (4#i32) : RustM Std.U8)
      = .ok ⟨(c8 (v.val[2]! &&& 15#i16)).bv <<< 4⟩ := u8_shl_bvp _ _ 4 (by scalar_tac) (by omega)
  have hc : ((c8 (v.val[3]! &&& 3#i16)) <<< (6#i32) : RustM Std.U8)
      = .ok ⟨(c8 (v.val[3]! &&& 3#i16)).bv <<< 6⟩ := u8_shl_bvp _ _ 6 (by scalar_tac) (by omega)
  have hd : ((v.val[0]! >>> (8#i32)) : RustM Std.I16) = .ok ⟨v.val[0]!.bv.sshiftRight 8⟩ :=
    i16_shr_bvp _ _ 8 (by scalar_tac) (by omega)
  have he : ((v.val[1]! >>> (6#i32)) : RustM Std.I16) = .ok ⟨v.val[1]!.bv.sshiftRight 6⟩ :=
    i16_shr_bvp _ _ 6 (by scalar_tac) (by omega)
  have hf : ((v.val[2]! >>> (4#i32)) : RustM Std.I16) = .ok ⟨v.val[2]!.bv.sshiftRight 4⟩ :=
    i16_shr_bvp _ _ 4 (by scalar_tac) (by omega)
  have hg : ((v.val[3]! >>> (2#i32)) : RustM Std.I16) = .ok ⟨v.val[3]!.bv.sshiftRight 2⟩ :=
    i16_shr_bvp _ _ 2 (by scalar_tac) (by omega)
  simp only [libcrux_iot_ml_kem.vector.portable.serialize.serialize_10_int,
    hi0, hi1, hi2, hi3, as_u8_eq, ha, hb, hc, hd, he, hf, hg, Le_declassify,
    e10b0, e10b1, e10b2, e10b3, e10b4, Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]

/-! The five `.val` closed forms. The lane bound needed is only `< 32768` (so `>>>` is
    floor division); the real `< 2 ^ 10` bound enters later, in the window identities. -/

private theorem e10b0_val (x0 : Std.I16) :
    (e10b0 x0).val = x0.bv.toNat % 2 ^ 8 % 256 := Le_c8_mask x0 _ 8 rfl

private theorem e10b4_val (x3 : Std.I16) (h3 : x3.bv.toNat < 32768) :
    (e10b4 x3).val = x3.bv.toNat / 2 ^ 2 % 2 ^ 8 % 256 := by
  rw [show e10b4 x3 = c8 ((⟨x3.bv.sshiftRight 2⟩ : Std.I16) &&& 255#i16) from rfl,
    Le_c8_mask _ _ 8 rfl]
  congr 2
  exact bv16_sshr_p x3.bv 2 h3

/-- The straddling byte, generic in the two shift widths. Call sites: bytes 1, 2 and 3 of
    the `d = 10` group (`e10b1_val` / `e10b2_val` / `e10b3_val`) — and ONLY those three.
    (CORRECTED 2026-08-20 after a reviewer finding: this said it also covered `d = 11`
    bytes 1, 2, 4, 5, 6, 8, 9. It does not. Every one of those is proved by
    `Le_straddle_val'` below, the unmasked-low-field variant, because at `d = 11` the impl
    leaves the low field unmasked and the shapes do not match. Reaching for this lemma at
    `d ≥ 11` will fail.) -/
theorem Le_straddle_val (lo hi Ml Mh : Std.I16) (s e kl kh : Nat)
    (hlo : lo.bv.toNat < 32768)
    (hMl : Ml.bv.toNat = 2 ^ kl - 1) (hMh : Mh.bv.toNat = 2 ^ kh - 1)
    (hfit : hi.bv.toNat % 2 ^ kh % 256 * 2 ^ e < 256)
    (hklo : lo.bv.toNat / 2 ^ s % 2 ^ kl % 256 < 2 ^ e) :
    ((⟨(c8 (hi &&& Mh)).bv <<< e⟩ : Std.U8)
        ||| c8 ((⟨lo.bv.sshiftRight s⟩ : Std.I16) &&& Ml)).val
      = hi.bv.toNat % 2 ^ kh % 256 * 2 ^ e + lo.bv.toNat / 2 ^ s % 2 ^ kl % 256 := by
  have hxv : (c8 (hi &&& Mh)).val = hi.bv.toNat % 2 ^ kh % 256 := Le_c8_mask _ _ kh hMh
  have hyv : (c8 ((⟨lo.bv.sshiftRight s⟩ : Std.I16) &&& Ml)).val
      = lo.bv.toNat / 2 ^ s % 2 ^ kl % 256 := by
    rw [Le_c8_mask _ _ kl hMl]
    congr 2
    exact bv16_sshr_p lo.bv s hlo
  exact Le_u8_or_add _ _ _ _ e
    (by rw [Le_shl_val _ e (by rw [hxv]; exact hfit), hxv]) hyv hklo

private theorem e10b1_val (x0 x1 : Std.I16) (h0 : x0.bv.toNat < 32768) :
    (e10b1 x0 x1).val
      = x1.bv.toNat % 2 ^ 6 % 256 * 2 ^ 2 + x0.bv.toNat / 2 ^ 8 % 2 ^ 2 % 256 :=
  Le_straddle_val x0 x1 3#i16 63#i16 8 2 2 6 h0 rfl rfl (by omega) (by omega)

private theorem e10b2_val (x1 x2 : Std.I16) (h1 : x1.bv.toNat < 32768) :
    (e10b2 x1 x2).val
      = x2.bv.toNat % 2 ^ 4 % 256 * 2 ^ 4 + x1.bv.toNat / 2 ^ 6 % 2 ^ 4 % 256 :=
  Le_straddle_val x1 x2 15#i16 15#i16 6 4 4 4 h1 rfl rfl (by omega) (by omega)

private theorem e10b3_val (x2 x3 : Std.I16) (h2 : x2.bv.toNat < 32768) :
    (e10b3 x2 x3).val
      = x3.bv.toNat % 2 ^ 2 % 256 * 2 ^ 6 + x2.bv.toNat / 2 ^ 4 % 2 ^ 6 % 256 :=
  Le_straddle_val x2 x3 63#i16 3#i16 4 6 6 2 h2 rfl rfl (by omega) (by omega)

/-- **The `d = 10` chunk-local seam.** One 4-lane sub-slice of the vector produces the
    five bytes `5g … 5g+4` of the 10-bit stream, each equal to `lanewin 10 L`. -/
private theorem e10_group (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (a bnd : Std.Usize) (g : Nat) (ha : a.val = 4 * g) (hb : bnd.val = 4 * g + 4) (hg : g < 4)
    (L : Nat → Nat)
    (hv : ∀ l : Nat, l < 16 → (v.elements.val[l]!).bv.toNat = L l)
    (hL : ∀ i : Nat, L i < 1024) :
    ∃ ns : Slice Std.I16,
      CoreModels.core.Array.Insts.CoreOpsIndexIndex.index
        (CoreModels.core.Slice.Insts.CoreOpsIndexIndex
          (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I16))
        v.elements ⟨a, bnd⟩ = .ok ns
      ∧ ∃ z0 z1 z2 z3 z4 : Std.U8,
          libcrux_iot_ml_kem.vector.portable.serialize.serialize_10_int ns
              = .ok (z0, z1, z2, z3, z4)
          ∧ z0.val = lanewin 10 L (5 * g)
          ∧ z1.val = lanewin 10 L (5 * g + 1)
          ∧ z2.val = lanewin 10 L (5 * g + 2)
          ∧ z3.val = lanewin 10 L (5 * g + 3)
          ∧ z4.val = lanewin 10 L (5 * g + 4) := by
  have hE : v.elements.val.length = 16 := by have := v.elements.property; simpa using this
  obtain ⟨ns, he, hl, hget⟩ := array_index_range_strict v.elements a bnd (by omega) (by omega)
  have b0 : (ns.val[0]!).bv.toNat = L (4 * g) := by
    rw [hget 0 (by omega), ha, Nat.add_zero]; exact hv _ (by omega)
  have b1 : (ns.val[1]!).bv.toNat = L (4 * g + 1) := by
    rw [hget 1 (by omega), ha]; exact hv _ (by omega)
  have b2 : (ns.val[2]!).bv.toNat = L (4 * g + 2) := by
    rw [hget 2 (by omega), ha]; exact hv _ (by omega)
  have b3 : (ns.val[3]!).bv.toNat = L (4 * g + 3) := by
    rw [hget 3 (by omega), ha]; exact hv _ (by omega)
  have c0 := hL (4 * g); have c1 := hL (4 * g + 1); have c2 := hL (4 * g + 2)
  have c3 := hL (4 * g + 3); have c4 := hL (4 * g + 4); have c5 := hL (4 * g + 5)
  refine ⟨ns, he, _, _, _, _, _, serialize_10_int_eq ns (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · rw [e10b0_val, b0, Le10_b0 (L (4 * g)) (L (4 * g + 1)) (L (4 * g + 2)) c0]
    unfold lanewin
    rw [show 8 * (5 * g) / 10 = 4 * g from by omega,
      show 8 * (5 * g) % 10 = 0 from by omega]
  · rw [e10b1_val _ _ (by rw [b0]; omega), b0, b1,
      Le10_b1 (L (4 * g)) (L (4 * g + 1)) (L (4 * g + 2)) c0 c1]
    unfold lanewin
    rw [show 8 * (5 * g + 1) / 10 = 4 * g from by omega,
      show 8 * (5 * g + 1) % 10 = 8 from by omega]
  · rw [e10b2_val _ _ (by rw [b1]; omega), b1, b2,
      Le10_b2 (L (4 * g + 1)) (L (4 * g + 2)) (L (4 * g + 3)) c1 c2]
    unfold lanewin
    rw [show 8 * (5 * g + 2) / 10 = 4 * g + 1 from by omega,
      show 8 * (5 * g + 2) % 10 = 6 from by omega]
  · rw [e10b3_val _ _ (by rw [b2]; omega), b2, b3,
      Le10_b3 (L (4 * g + 2)) (L (4 * g + 3)) (L (4 * g + 4)) c2 c3]
    unfold lanewin
    rw [show 8 * (5 * g + 3) / 10 = 4 * g + 2 from by omega,
      show 8 * (5 * g + 3) % 10 = 4 from by omega]
  · rw [e10b4_val _ (by rw [b3]; omega), b3,
      Le10_b4 (L (4 * g + 3)) (L (4 * g + 4)) (L (4 * g + 5)) c3]
    unfold lanewin
    rw [show 8 * (5 * g + 4) / 10 = 4 * g + 3 from by omega,
      show 8 * (5 * g + 4) % 10 = 2 from by omega]


/-- **Impl-side chunk closed form at `d = 10`**: `serialize_10` writes exactly the
    `lanewin 10` bytes of the four 4-lane groups. -/
private theorem serialize_10_eq
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8) (h : out.val.length = 20) (L : Nat → Nat)
    (hv : ∀ l : Nat, l < 16 → (v.elements.val[l]!).bv.toNat = L l)
    (hL : ∀ i : Nat, L i < 1024) :
    ∃ s : Slice Std.U8,
      libcrux_iot_ml_kem.vector.portable.serialize.serialize_10 v out = .ok s
      ∧ s.val.length = 20
      ∧ ∀ n : Nat, n < 20 → (s.val[n]!).val = lanewin 10 L n := by
  have hlen : CoreModels.core.slice.Slice.len out = .ok (20#usize : Std.Usize) := by
    show RustM.ok (Aeneas.Std.Slice.len out) = _
    congr 1
    apply Std.UScalar.eq_of_val_eq
    simp [h]
  obtain ⟨ns0, he0, y00, y01, y02, y03, y04, hs0, p00, p01, p02, p03, p04⟩ :=
    e10_group v 0#usize 4#usize 0 (by scalar_tac) (by scalar_tac) (by omega) L hv hL
  norm_num at p00 p01 p02 p03 p04
  obtain ⟨ns1, he1, y10, y11, y12, y13, y14, hs1, p10, p11, p12, p13, p14⟩ :=
    e10_group v 4#usize 8#usize 1 (by scalar_tac) (by scalar_tac) (by omega) L hv hL
  norm_num at p10 p11 p12 p13 p14
  obtain ⟨ns2, he2, y20, y21, y22, y23, y24, hs2, p20, p21, p22, p23, p24⟩ :=
    e10_group v 8#usize 12#usize 2 (by scalar_tac) (by scalar_tac) (by omega) L hv hL
  norm_num at p20 p21 p22 p23 p24
  obtain ⟨ns3, he3, y30, y31, y32, y33, y34, hs3, p30, p31, p32, p33, p34⟩ :=
    e10_group v 12#usize 16#usize 3 (by scalar_tac) (by scalar_tac) (by omega) L hv hL
  norm_num at p30 p31 p32 p33 p34
  obtain ⟨t0, hu0, hl0, hq0⟩ :=
    Le_update_step (lanewin 10 L) 20 out 0 0#usize y00 (by scalar_tac) (by omega) h
      (by intro n hn; exact absurd hn (by omega)) p00
  obtain ⟨t1, hu1, hl1, hq1⟩ :=
    Le_update_step (lanewin 10 L) 20 t0 1 1#usize y01 (by scalar_tac) (by omega) hl0 hq0 p01
  obtain ⟨t2, hu2, hl2, hq2⟩ :=
    Le_update_step (lanewin 10 L) 20 t1 2 2#usize y02 (by scalar_tac) (by omega) hl1 hq1 p02
  obtain ⟨t3, hu3, hl3, hq3⟩ :=
    Le_update_step (lanewin 10 L) 20 t2 3 3#usize y03 (by scalar_tac) (by omega) hl2 hq2 p03
  obtain ⟨t4, hu4, hl4, hq4⟩ :=
    Le_update_step (lanewin 10 L) 20 t3 4 4#usize y04 (by scalar_tac) (by omega) hl3 hq3 p04
  obtain ⟨t5, hu5, hl5, hq5⟩ :=
    Le_update_step (lanewin 10 L) 20 t4 5 5#usize y10 (by scalar_tac) (by omega) hl4 hq4 p10
  obtain ⟨t6, hu6, hl6, hq6⟩ :=
    Le_update_step (lanewin 10 L) 20 t5 6 6#usize y11 (by scalar_tac) (by omega) hl5 hq5 p11
  obtain ⟨t7, hu7, hl7, hq7⟩ :=
    Le_update_step (lanewin 10 L) 20 t6 7 7#usize y12 (by scalar_tac) (by omega) hl6 hq6 p12
  obtain ⟨t8, hu8, hl8, hq8⟩ :=
    Le_update_step (lanewin 10 L) 20 t7 8 8#usize y13 (by scalar_tac) (by omega) hl7 hq7 p13
  obtain ⟨t9, hu9, hl9, hq9⟩ :=
    Le_update_step (lanewin 10 L) 20 t8 9 9#usize y14 (by scalar_tac) (by omega) hl8 hq8 p14
  obtain ⟨t10, hu10, hl10, hq10⟩ :=
    Le_update_step (lanewin 10 L) 20 t9 10 10#usize y20 (by scalar_tac) (by omega) hl9 hq9 p20
  obtain ⟨t11, hu11, hl11, hq11⟩ :=
    Le_update_step (lanewin 10 L) 20 t10 11 11#usize y21 (by scalar_tac) (by omega) hl10 hq10 p21
  obtain ⟨t12, hu12, hl12, hq12⟩ :=
    Le_update_step (lanewin 10 L) 20 t11 12 12#usize y22 (by scalar_tac) (by omega) hl11 hq11 p22
  obtain ⟨t13, hu13, hl13, hq13⟩ :=
    Le_update_step (lanewin 10 L) 20 t12 13 13#usize y23 (by scalar_tac) (by omega) hl12 hq12 p23
  obtain ⟨t14, hu14, hl14, hq14⟩ :=
    Le_update_step (lanewin 10 L) 20 t13 14 14#usize y24 (by scalar_tac) (by omega) hl13 hq13 p24
  obtain ⟨t15, hu15, hl15, hq15⟩ :=
    Le_update_step (lanewin 10 L) 20 t14 15 15#usize y30 (by scalar_tac) (by omega) hl14 hq14 p30
  obtain ⟨t16, hu16, hl16, hq16⟩ :=
    Le_update_step (lanewin 10 L) 20 t15 16 16#usize y31 (by scalar_tac) (by omega) hl15 hq15 p31
  obtain ⟨t17, hu17, hl17, hq17⟩ :=
    Le_update_step (lanewin 10 L) 20 t16 17 17#usize y32 (by scalar_tac) (by omega) hl16 hq16 p32
  obtain ⟨t18, hu18, hl18, hq18⟩ :=
    Le_update_step (lanewin 10 L) 20 t17 18 18#usize y33 (by scalar_tac) (by omega) hl17 hq17 p33
  obtain ⟨t19, hu19, hl19, hq19⟩ :=
    Le_update_step (lanewin 10 L) 20 t18 19 19#usize y34 (by scalar_tac) (by omega) hl18 hq18 p34
  refine ⟨t19, ?_, hl19, hq19⟩
  unfold libcrux_iot_ml_kem.vector.portable.serialize.serialize_10
  rw [hlen]
  simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.massert, if_true]
  rw [he0]; simp only [Aeneas.Std.bind_tc_ok]
  rw [bind_ok_quint hs0]
  rw [hu0]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu1]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu2]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu3]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu4]; simp only [Aeneas.Std.bind_tc_ok]
  rw [he1]; simp only [Aeneas.Std.bind_tc_ok]
  rw [bind_ok_quint hs1]
  rw [hu5]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu6]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu7]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu8]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu9]; simp only [Aeneas.Std.bind_tc_ok]
  rw [he2]; simp only [Aeneas.Std.bind_tc_ok]
  rw [bind_ok_quint hs2]
  rw [hu10]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu11]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu12]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu13]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu14]; simp only [Aeneas.Std.bind_tc_ok]
  rw [he3]; simp only [Aeneas.Std.bind_tc_ok]
  rw [bind_ok_quint hs3]
  rw [hu15]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu16]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu17]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu18]; simp only [Aeneas.Std.bind_tc_ok]
  exact hu19

/-! ### Toolkit additions the `d = 11` seam needs and `d = 10` did not.

    At `d = 11` the impl leaves the LOW field of a straddling byte UNMASKED — the field is
    `lane >>> s` with `s + e = 11`, and `lane < 2 ^ 11` already forces it below `2 ^ e`, so
    the mask would be dead code. That is why `Le_straddle_val'` carries the lane bound
    `< 2048` where `Le_straddle_val` needed none: at `d = 10` the mask did the work. -/

/-- `as_u8 (x >>> s)`, unmasked. -/
private theorem Le_shr_c8_val (x : Std.I16) (s : Nat) (hx : x.bv.toNat < 32768) :
    (c8 (⟨x.bv.sshiftRight s⟩ : Std.I16)).val = x.bv.toNat / 2 ^ s % 256 := by
  rw [c8_val]
  congr 1
  exact bv16_sshr_p x.bv s hx

/-- `as_u8 ((x >>> s) & (2 ^ k - 1))`. Call sites: `d = 11` bytes 3 and 7 (`e11b3_val`,
    `e11b7_val`) — and only those two. (CORRECTED 2026-08-20 after a reviewer finding: it
    also claimed `d = 10` byte 4. It cannot: `e10b4_val` sits ~215 lines EARLIER in the file
    and discharges that byte by hand. Its three-line proof IS this lemma inlined, so
    hoisting this declaration above the `d = 10` block would delete it — recorded debt.) -/
theorem Le_shr_mask_c8_val (x M : Std.I16) (s k : Nat) (hx : x.bv.toNat < 32768)
    (hM : M.bv.toNat = 2 ^ k - 1) :
    (c8 ((⟨x.bv.sshiftRight s⟩ : Std.I16) &&& M)).val = x.bv.toNat / 2 ^ s % 2 ^ k % 256 := by
  rw [Le_c8_mask _ _ k hM]
  congr 2
  exact bv16_sshr_p x.bv s hx

/-- The straddling byte with an UNMASKED low field. -/
theorem Le_straddle_val' (lo hi Mh : Std.I16) (s e kh : Nat)
    (hlo : lo.bv.toNat < 32768) (hMh : Mh.bv.toNat = 2 ^ kh - 1)
    (hfit : hi.bv.toNat % 2 ^ kh % 256 * 2 ^ e < 256)
    (hklo : lo.bv.toNat / 2 ^ s % 256 < 2 ^ e) :
    ((⟨(c8 (hi &&& Mh)).bv <<< e⟩ : Std.U8) ||| c8 (⟨lo.bv.sshiftRight s⟩ : Std.I16)).val
      = hi.bv.toNat % 2 ^ kh % 256 * 2 ^ e + lo.bv.toNat / 2 ^ s % 256 := by
  have hxv : (c8 (hi &&& Mh)).val = hi.bv.toNat % 2 ^ kh % 256 := Le_c8_mask _ _ kh hMh
  exact Le_u8_or_add _ _ _ _ e
    (by rw [Le_shl_val _ e (by rw [hxv]; exact hfit), hxv])
    (Le_shr_c8_val lo s hlo) hklo

private theorem bind_ok_11 {A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 B : Type}
    {x : RustM (A0 × A1 × A2 × A3 × A4 × A5 × A6 × A7 × A8 × A9 × A10)}
    {a0 : A0} {a1 : A1} {a2 : A2} {a3 : A3} {a4 : A4} {a5 : A5} {a6 : A6} {a7 : A7}
    {a8 : A8} {a9 : A9} {a10 : A10}
    (h : x = .ok (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10))
    (g : A0 → A1 → A2 → A3 → A4 → A5 → A6 → A7 → A8 → A9 → A10 → RustM B) :
    (do let (b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10) ← x
        g b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10)
      = g a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 := by rw [h]; rfl

/-! ### IMPL SEAM at `d = 11`, byte level. EIGHT lanes to ELEVEN bytes — the same `2 × 8`
    split `serialize_5` uses, so only the byte shapes are new. Bytes 0, 3, 7, 10 are
    single-lane; the other seven straddle, with `(s, e)` running
    `(8,3) (5,6) (10,1) (7,4) (4,7) (9,2) (6,5)` — `s + e = 11` throughout. -/

private def e11b0 (x0 : Std.I16) : Std.U8 :=
  c8 x0

private def e11b1 (x0 x1 : Std.I16) : Std.U8 :=
  (⟨(c8 (x1 &&& 31#i16)).bv <<< 3⟩ : Std.U8)
    ||| c8 (⟨x0.bv.sshiftRight 8⟩ : Std.I16)

private def e11b2 (x1 x2 : Std.I16) : Std.U8 :=
  (⟨(c8 (x2 &&& 3#i16)).bv <<< 6⟩ : Std.U8)
    ||| c8 (⟨x1.bv.sshiftRight 5⟩ : Std.I16)

private def e11b3 (x2 : Std.I16) : Std.U8 :=
  c8 ((⟨x2.bv.sshiftRight 2⟩ : Std.I16) &&& 255#i16)

private def e11b4 (x2 x3 : Std.I16) : Std.U8 :=
  (⟨(c8 (x3 &&& 127#i16)).bv <<< 1⟩ : Std.U8)
    ||| c8 (⟨x2.bv.sshiftRight 10⟩ : Std.I16)

private def e11b5 (x3 x4 : Std.I16) : Std.U8 :=
  (⟨(c8 (x4 &&& 15#i16)).bv <<< 4⟩ : Std.U8)
    ||| c8 (⟨x3.bv.sshiftRight 7⟩ : Std.I16)

private def e11b6 (x4 x5 : Std.I16) : Std.U8 :=
  (⟨(c8 (x5 &&& 1#i16)).bv <<< 7⟩ : Std.U8)
    ||| c8 (⟨x4.bv.sshiftRight 4⟩ : Std.I16)

private def e11b7 (x5 : Std.I16) : Std.U8 :=
  c8 ((⟨x5.bv.sshiftRight 1⟩ : Std.I16) &&& 255#i16)

private def e11b8 (x5 x6 : Std.I16) : Std.U8 :=
  (⟨(c8 (x6 &&& 63#i16)).bv <<< 2⟩ : Std.U8)
    ||| c8 (⟨x5.bv.sshiftRight 9⟩ : Std.I16)

private def e11b9 (x6 x7 : Std.I16) : Std.U8 :=
  (⟨(c8 (x7 &&& 7#i16)).bv <<< 5⟩ : Std.U8)
    ||| c8 (⟨x6.bv.sshiftRight 6⟩ : Std.I16)

private def e11b10 (x7 : Std.I16) : Std.U8 :=
  c8 (⟨x7.bv.sshiftRight 3⟩ : Std.I16)

/-! ### The eleven pure-`Nat` byte identities at `d = 11`. Eleven, not five: at `d = 10`
    the bit offset advances by 10 ≡ 2 (mod 8) and the pattern closes after 5 bytes; at
    `d = 11` it advances by 3 and the cycle is the full 11. -/

private theorem Le11_b0 (a b c : Nat) (ha : a < 2048) :
    a % 256
      = (a / 2 ^ 0 + b * 2 ^ 11 + c * 2 ^ 22) % 256 := by
  norm_num; omega

private theorem Le11_b1 (a b c : Nat) (ha : a < 2048) (hb : b < 2048) :
    b % 2 ^ 5 % 256 * 2 ^ 3 + a / 2 ^ 8 % 256
      = (a / 2 ^ 8 + b * 2 ^ 3 + c * 2 ^ 14) % 256 := by
  norm_num; omega

private theorem Le11_b2 (a b c : Nat) (ha : a < 2048) (hb : b < 2048) :
    b % 2 ^ 2 % 256 * 2 ^ 6 + a / 2 ^ 5 % 256
      = (a / 2 ^ 5 + b * 2 ^ 6 + c * 2 ^ 17) % 256 := by
  norm_num; omega

private theorem Le11_b3 (a b c : Nat) (ha : a < 2048) :
    a / 2 ^ 2 % 2 ^ 8 % 256
      = (a / 2 ^ 2 + b * 2 ^ 9 + c * 2 ^ 20) % 256 := by
  norm_num; omega

private theorem Le11_b4 (a b c : Nat) (ha : a < 2048) (hb : b < 2048) :
    b % 2 ^ 7 % 256 * 2 ^ 1 + a / 2 ^ 10 % 256
      = (a / 2 ^ 10 + b * 2 ^ 1 + c * 2 ^ 12) % 256 := by
  norm_num; omega

private theorem Le11_b5 (a b c : Nat) (ha : a < 2048) (hb : b < 2048) :
    b % 2 ^ 4 % 256 * 2 ^ 4 + a / 2 ^ 7 % 256
      = (a / 2 ^ 7 + b * 2 ^ 4 + c * 2 ^ 15) % 256 := by
  norm_num; omega

private theorem Le11_b6 (a b c : Nat) (ha : a < 2048) (hb : b < 2048) :
    b % 2 ^ 1 % 256 * 2 ^ 7 + a / 2 ^ 4 % 256
      = (a / 2 ^ 4 + b * 2 ^ 7 + c * 2 ^ 18) % 256 := by
  norm_num; omega

private theorem Le11_b7 (a b c : Nat) (ha : a < 2048) :
    a / 2 ^ 1 % 2 ^ 8 % 256
      = (a / 2 ^ 1 + b * 2 ^ 10 + c * 2 ^ 21) % 256 := by
  norm_num; omega

private theorem Le11_b8 (a b c : Nat) (ha : a < 2048) (hb : b < 2048) :
    b % 2 ^ 6 % 256 * 2 ^ 2 + a / 2 ^ 9 % 256
      = (a / 2 ^ 9 + b * 2 ^ 2 + c * 2 ^ 13) % 256 := by
  norm_num; omega

private theorem Le11_b9 (a b c : Nat) (ha : a < 2048) (hb : b < 2048) :
    b % 2 ^ 3 % 256 * 2 ^ 5 + a / 2 ^ 6 % 256
      = (a / 2 ^ 6 + b * 2 ^ 5 + c * 2 ^ 16) % 256 := by
  norm_num; omega

private theorem Le11_b10 (a b c : Nat) (ha : a < 2048) :
    a / 2 ^ 3 % 256
      = (a / 2 ^ 3 + b * 2 ^ 8 + c * 2 ^ 19) % 256 := by
  norm_num; omega

private theorem e11b0_val (x0 : Std.I16) :
    (e11b0 x0).val = x0.bv.toNat % 256 :=
  c8_val x0

private theorem e11b1_val (x0 x1 : Std.I16) (h0 : x0.bv.toNat < 2048) :
    (e11b1 x0 x1).val
      = x1.bv.toNat % 2 ^ 5 % 256 * 2 ^ 3 + x0.bv.toNat / 2 ^ 8 % 256 :=
  Le_straddle_val' x0 x1 31#i16 8 3 5 (by omega) rfl (by omega) (by omega)

private theorem e11b2_val (x1 x2 : Std.I16) (h1 : x1.bv.toNat < 2048) :
    (e11b2 x1 x2).val
      = x2.bv.toNat % 2 ^ 2 % 256 * 2 ^ 6 + x1.bv.toNat / 2 ^ 5 % 256 :=
  Le_straddle_val' x1 x2 3#i16 5 6 2 (by omega) rfl (by omega) (by omega)

private theorem e11b3_val (x2 : Std.I16) (h2 : x2.bv.toNat < 32768) :
    (e11b3 x2).val = x2.bv.toNat / 2 ^ 2 % 2 ^ 8 % 256 :=
  Le_shr_mask_c8_val x2 255#i16 2 8 h2 rfl

private theorem e11b4_val (x2 x3 : Std.I16) (h2 : x2.bv.toNat < 2048) :
    (e11b4 x2 x3).val
      = x3.bv.toNat % 2 ^ 7 % 256 * 2 ^ 1 + x2.bv.toNat / 2 ^ 10 % 256 :=
  Le_straddle_val' x2 x3 127#i16 10 1 7 (by omega) rfl (by omega) (by omega)

private theorem e11b5_val (x3 x4 : Std.I16) (h3 : x3.bv.toNat < 2048) :
    (e11b5 x3 x4).val
      = x4.bv.toNat % 2 ^ 4 % 256 * 2 ^ 4 + x3.bv.toNat / 2 ^ 7 % 256 :=
  Le_straddle_val' x3 x4 15#i16 7 4 4 (by omega) rfl (by omega) (by omega)

private theorem e11b6_val (x4 x5 : Std.I16) (h4 : x4.bv.toNat < 2048) :
    (e11b6 x4 x5).val
      = x5.bv.toNat % 2 ^ 1 % 256 * 2 ^ 7 + x4.bv.toNat / 2 ^ 4 % 256 :=
  Le_straddle_val' x4 x5 1#i16 4 7 1 (by omega) rfl (by omega) (by omega)

private theorem e11b7_val (x5 : Std.I16) (h5 : x5.bv.toNat < 32768) :
    (e11b7 x5).val = x5.bv.toNat / 2 ^ 1 % 2 ^ 8 % 256 :=
  Le_shr_mask_c8_val x5 255#i16 1 8 h5 rfl

private theorem e11b8_val (x5 x6 : Std.I16) (h5 : x5.bv.toNat < 2048) :
    (e11b8 x5 x6).val
      = x6.bv.toNat % 2 ^ 6 % 256 * 2 ^ 2 + x5.bv.toNat / 2 ^ 9 % 256 :=
  Le_straddle_val' x5 x6 63#i16 9 2 6 (by omega) rfl (by omega) (by omega)

private theorem e11b9_val (x6 x7 : Std.I16) (h6 : x6.bv.toNat < 2048) :
    (e11b9 x6 x7).val
      = x7.bv.toNat % 2 ^ 3 % 256 * 2 ^ 5 + x6.bv.toNat / 2 ^ 6 % 256 :=
  Le_straddle_val' x6 x7 7#i16 6 5 3 (by omega) rfl (by omega) (by omega)

private theorem e11b10_val (x7 : Std.I16) (h7 : x7.bv.toNat < 32768) :
    (e11b10 x7).val = x7.bv.toNat / 2 ^ 3 % 256 :=
  Le_shr_c8_val x7 3 h7

private theorem serialize_11_int_eq (v : Slice Std.I16) (h : 8 ≤ v.val.length) :
    libcrux_iot_ml_kem.vector.portable.serialize.serialize_11_int v
      = .ok (e11b0 v.val[0]!, e11b1 v.val[0]! v.val[1]!, e11b2 v.val[1]! v.val[2]!,
             e11b3 v.val[2]!, e11b4 v.val[2]! v.val[3]!, e11b5 v.val[3]! v.val[4]!,
             e11b6 v.val[4]! v.val[5]!, e11b7 v.val[5]!, e11b8 v.val[5]! v.val[6]!,
             e11b9 v.val[6]! v.val[7]!, e11b10 v.val[7]!) := by
  have hi0 : Aeneas.Std.Slice.index_usize v 0#usize = .ok (v.val[0]!) :=
    slice_index_usize_eq v 0#usize (by scalar_tac)
  have hi1 : Aeneas.Std.Slice.index_usize v 1#usize = .ok (v.val[1]!) :=
    slice_index_usize_eq v 1#usize (by scalar_tac)
  have hi2 : Aeneas.Std.Slice.index_usize v 2#usize = .ok (v.val[2]!) :=
    slice_index_usize_eq v 2#usize (by scalar_tac)
  have hi3 : Aeneas.Std.Slice.index_usize v 3#usize = .ok (v.val[3]!) :=
    slice_index_usize_eq v 3#usize (by scalar_tac)
  have hi4 : Aeneas.Std.Slice.index_usize v 4#usize = .ok (v.val[4]!) :=
    slice_index_usize_eq v 4#usize (by scalar_tac)
  have hi5 : Aeneas.Std.Slice.index_usize v 5#usize = .ok (v.val[5]!) :=
    slice_index_usize_eq v 5#usize (by scalar_tac)
  have hi6 : Aeneas.Std.Slice.index_usize v 6#usize = .ok (v.val[6]!) :=
    slice_index_usize_eq v 6#usize (by scalar_tac)
  have hi7 : Aeneas.Std.Slice.index_usize v 7#usize = .ok (v.val[7]!) :=
    slice_index_usize_eq v 7#usize (by scalar_tac)
  have hla : ((c8 (v.val[1]! &&& 31#i16)) <<< (3#i32) : RustM Std.U8)
      = .ok ⟨(c8 (v.val[1]! &&& 31#i16)).bv <<< 3⟩ :=
    u8_shl_bvp _ _ 3 (by scalar_tac) (by omega)
  have hlb : ((c8 (v.val[2]! &&& 3#i16)) <<< (6#i32) : RustM Std.U8)
      = .ok ⟨(c8 (v.val[2]! &&& 3#i16)).bv <<< 6⟩ :=
    u8_shl_bvp _ _ 6 (by scalar_tac) (by omega)
  have hlc : ((c8 (v.val[3]! &&& 127#i16)) <<< (1#i32) : RustM Std.U8)
      = .ok ⟨(c8 (v.val[3]! &&& 127#i16)).bv <<< 1⟩ :=
    u8_shl_bvp _ _ 1 (by scalar_tac) (by omega)
  have hld : ((c8 (v.val[4]! &&& 15#i16)) <<< (4#i32) : RustM Std.U8)
      = .ok ⟨(c8 (v.val[4]! &&& 15#i16)).bv <<< 4⟩ :=
    u8_shl_bvp _ _ 4 (by scalar_tac) (by omega)
  have hle : ((c8 (v.val[5]! &&& 1#i16)) <<< (7#i32) : RustM Std.U8)
      = .ok ⟨(c8 (v.val[5]! &&& 1#i16)).bv <<< 7⟩ :=
    u8_shl_bvp _ _ 7 (by scalar_tac) (by omega)
  have hlf : ((c8 (v.val[6]! &&& 63#i16)) <<< (2#i32) : RustM Std.U8)
      = .ok ⟨(c8 (v.val[6]! &&& 63#i16)).bv <<< 2⟩ :=
    u8_shl_bvp _ _ 2 (by scalar_tac) (by omega)
  have hlg : ((c8 (v.val[7]! &&& 7#i16)) <<< (5#i32) : RustM Std.U8)
      = .ok ⟨(c8 (v.val[7]! &&& 7#i16)).bv <<< 5⟩ :=
    u8_shl_bvp _ _ 5 (by scalar_tac) (by omega)
  have hr0_8 : ((v.val[0]! >>> (8#i32)) : RustM Std.I16)
      = .ok ⟨v.val[0]!.bv.sshiftRight 8⟩ := i16_shr_bvp _ _ 8 (by scalar_tac) (by omega)
  have hr1_5 : ((v.val[1]! >>> (5#i32)) : RustM Std.I16)
      = .ok ⟨v.val[1]!.bv.sshiftRight 5⟩ := i16_shr_bvp _ _ 5 (by scalar_tac) (by omega)
  have hr2_2 : ((v.val[2]! >>> (2#i32)) : RustM Std.I16)
      = .ok ⟨v.val[2]!.bv.sshiftRight 2⟩ := i16_shr_bvp _ _ 2 (by scalar_tac) (by omega)
  have hr2_10 : ((v.val[2]! >>> (10#i32)) : RustM Std.I16)
      = .ok ⟨v.val[2]!.bv.sshiftRight 10⟩ := i16_shr_bvp _ _ 10 (by scalar_tac) (by omega)
  have hr3_7 : ((v.val[3]! >>> (7#i32)) : RustM Std.I16)
      = .ok ⟨v.val[3]!.bv.sshiftRight 7⟩ := i16_shr_bvp _ _ 7 (by scalar_tac) (by omega)
  have hr4_4 : ((v.val[4]! >>> (4#i32)) : RustM Std.I16)
      = .ok ⟨v.val[4]!.bv.sshiftRight 4⟩ := i16_shr_bvp _ _ 4 (by scalar_tac) (by omega)
  have hr5_1 : ((v.val[5]! >>> (1#i32)) : RustM Std.I16)
      = .ok ⟨v.val[5]!.bv.sshiftRight 1⟩ := i16_shr_bvp _ _ 1 (by scalar_tac) (by omega)
  have hr5_9 : ((v.val[5]! >>> (9#i32)) : RustM Std.I16)
      = .ok ⟨v.val[5]!.bv.sshiftRight 9⟩ := i16_shr_bvp _ _ 9 (by scalar_tac) (by omega)
  have hr6_6 : ((v.val[6]! >>> (6#i32)) : RustM Std.I16)
      = .ok ⟨v.val[6]!.bv.sshiftRight 6⟩ := i16_shr_bvp _ _ 6 (by scalar_tac) (by omega)
  have hr7_3 : ((v.val[7]! >>> (3#i32)) : RustM Std.I16)
      = .ok ⟨v.val[7]!.bv.sshiftRight 3⟩ := i16_shr_bvp _ _ 3 (by scalar_tac) (by omega)
  simp only [libcrux_iot_ml_kem.vector.portable.serialize.serialize_11_int,
    hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7,
    hla, hlb, hlc, hld, hle, hlf, hlg,
    hr0_8, hr1_5, hr2_2, hr2_10, hr3_7, hr4_4, hr5_1, hr5_9, hr6_6, hr7_3,
    as_u8_eq, Le_declassify, e11b0, e11b1, e11b2, e11b3, e11b4, e11b5, e11b6, e11b7, e11b8, e11b9, e11b10,
    Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]

/-- **The `d = 11` chunk-local seam.** One 8-lane sub-slice produces the eleven bytes
    `11g … 11g+10` of the 11-bit stream, each equal to `lanewin 11 L`. -/
private theorem e11_group (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (a bnd : Std.Usize) (g : Nat) (ha : a.val = 8 * g) (hb : bnd.val = 8 * g + 8) (hg : g < 2)
    (L : Nat → Nat)
    (hv : ∀ l : Nat, l < 16 → (v.elements.val[l]!).bv.toNat = L l)
    (hL : ∀ i : Nat, L i < 2048) :
    ∃ ns : Slice Std.I16,
      CoreModels.core.Array.Insts.CoreOpsIndexIndex.index
        (CoreModels.core.Slice.Insts.CoreOpsIndexIndex
          (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I16))
        v.elements ⟨a, bnd⟩ = .ok ns
      ∧ ∃ z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 : Std.U8,
          libcrux_iot_ml_kem.vector.portable.serialize.serialize_11_int ns
              = .ok (z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10)
          ∧ z0.val = lanewin 11 L (11 * g)
          ∧ z1.val = lanewin 11 L (11 * g + 1)
          ∧ z2.val = lanewin 11 L (11 * g + 2)
          ∧ z3.val = lanewin 11 L (11 * g + 3)
          ∧ z4.val = lanewin 11 L (11 * g + 4)
          ∧ z5.val = lanewin 11 L (11 * g + 5)
          ∧ z6.val = lanewin 11 L (11 * g + 6)
          ∧ z7.val = lanewin 11 L (11 * g + 7)
          ∧ z8.val = lanewin 11 L (11 * g + 8)
          ∧ z9.val = lanewin 11 L (11 * g + 9)
          ∧ z10.val = lanewin 11 L (11 * g + 10) := by
  have hE : v.elements.val.length = 16 := by have := v.elements.property; simpa using this
  obtain ⟨ns, he, hl, hget⟩ := array_index_range_strict v.elements a bnd (by omega) (by omega)
  have w0 : (ns.val[0]!).bv.toNat = L (8 * g) := by
    rw [hget 0 (by omega), ha, Nat.add_zero]; exact hv _ (by omega)
  have w1 : (ns.val[1]!).bv.toNat = L (8 * g + 1) := by
    rw [hget 1 (by omega), ha]; exact hv _ (by omega)
  have w2 : (ns.val[2]!).bv.toNat = L (8 * g + 2) := by
    rw [hget 2 (by omega), ha]; exact hv _ (by omega)
  have w3 : (ns.val[3]!).bv.toNat = L (8 * g + 3) := by
    rw [hget 3 (by omega), ha]; exact hv _ (by omega)
  have w4 : (ns.val[4]!).bv.toNat = L (8 * g + 4) := by
    rw [hget 4 (by omega), ha]; exact hv _ (by omega)
  have w5 : (ns.val[5]!).bv.toNat = L (8 * g + 5) := by
    rw [hget 5 (by omega), ha]; exact hv _ (by omega)
  have w6 : (ns.val[6]!).bv.toNat = L (8 * g + 6) := by
    rw [hget 6 (by omega), ha]; exact hv _ (by omega)
  have w7 : (ns.val[7]!).bv.toNat = L (8 * g + 7) := by
    rw [hget 7 (by omega), ha]; exact hv _ (by omega)
  have c0 := hL (8 * g)
  have c1 := hL (8 * g + 1)
  have c2 := hL (8 * g + 2)
  have c3 := hL (8 * g + 3)
  have c4 := hL (8 * g + 4)
  have c5 := hL (8 * g + 5)
  have c6 := hL (8 * g + 6)
  have c7 := hL (8 * g + 7)
  have c8 := hL (8 * g + 8)
  have c9 := hL (8 * g + 9)
  refine ⟨ns, he, _, _, _, _, _, _, _, _, _, _, _, serialize_11_int_eq ns (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e11b0_val, w0,
      Le11_b0 (L (8 * g)) (L (8 * g + 1)) (L (8 * g + 2)) c0]
    unfold lanewin
    rw [show 8 * (11 * g) / 11 = 8 * g from by omega,
      show 8 * (11 * g) % 11 = 0 from by omega]
  · rw [e11b1_val _ _ (by rw [w0]; omega), w0, w1,
      Le11_b1 (L (8 * g)) (L (8 * g + 1)) (L (8 * g + 2)) c0 c1]
    unfold lanewin
    rw [show 8 * (11 * g + 1) / 11 = 8 * g from by omega,
      show 8 * (11 * g + 1) % 11 = 8 from by omega]
  · rw [e11b2_val _ _ (by rw [w1]; omega), w1, w2,
      Le11_b2 (L (8 * g + 1)) (L (8 * g + 2)) (L (8 * g + 3)) c1 c2]
    unfold lanewin
    rw [show 8 * (11 * g + 2) / 11 = 8 * g + 1 from by omega,
      show 8 * (11 * g + 2) % 11 = 5 from by omega]
  · rw [e11b3_val _ (by rw [w2]; omega), w2,
      Le11_b3 (L (8 * g + 2)) (L (8 * g + 3)) (L (8 * g + 4)) c2]
    unfold lanewin
    rw [show 8 * (11 * g + 3) / 11 = 8 * g + 2 from by omega,
      show 8 * (11 * g + 3) % 11 = 2 from by omega]
  · rw [e11b4_val _ _ (by rw [w2]; omega), w2, w3,
      Le11_b4 (L (8 * g + 2)) (L (8 * g + 3)) (L (8 * g + 4)) c2 c3]
    unfold lanewin
    rw [show 8 * (11 * g + 4) / 11 = 8 * g + 2 from by omega,
      show 8 * (11 * g + 4) % 11 = 10 from by omega]
  · rw [e11b5_val _ _ (by rw [w3]; omega), w3, w4,
      Le11_b5 (L (8 * g + 3)) (L (8 * g + 4)) (L (8 * g + 5)) c3 c4]
    unfold lanewin
    rw [show 8 * (11 * g + 5) / 11 = 8 * g + 3 from by omega,
      show 8 * (11 * g + 5) % 11 = 7 from by omega]
  · rw [e11b6_val _ _ (by rw [w4]; omega), w4, w5,
      Le11_b6 (L (8 * g + 4)) (L (8 * g + 5)) (L (8 * g + 6)) c4 c5]
    unfold lanewin
    rw [show 8 * (11 * g + 6) / 11 = 8 * g + 4 from by omega,
      show 8 * (11 * g + 6) % 11 = 4 from by omega]
  · rw [e11b7_val _ (by rw [w5]; omega), w5,
      Le11_b7 (L (8 * g + 5)) (L (8 * g + 6)) (L (8 * g + 7)) c5]
    unfold lanewin
    rw [show 8 * (11 * g + 7) / 11 = 8 * g + 5 from by omega,
      show 8 * (11 * g + 7) % 11 = 1 from by omega]
  · rw [e11b8_val _ _ (by rw [w5]; omega), w5, w6,
      Le11_b8 (L (8 * g + 5)) (L (8 * g + 6)) (L (8 * g + 7)) c5 c6]
    unfold lanewin
    rw [show 8 * (11 * g + 8) / 11 = 8 * g + 5 from by omega,
      show 8 * (11 * g + 8) % 11 = 9 from by omega]
  · rw [e11b9_val _ _ (by rw [w6]; omega), w6, w7,
      Le11_b9 (L (8 * g + 6)) (L (8 * g + 7)) (L (8 * g + 8)) c6 c7]
    unfold lanewin
    rw [show 8 * (11 * g + 9) / 11 = 8 * g + 6 from by omega,
      show 8 * (11 * g + 9) % 11 = 6 from by omega]
  · rw [e11b10_val _ (by rw [w7]; omega), w7,
      Le11_b10 (L (8 * g + 7)) (L (8 * g + 8)) (L (8 * g + 9)) c7]
    unfold lanewin
    rw [show 8 * (11 * g + 10) / 11 = 8 * g + 7 from by omega,
      show 8 * (11 * g + 10) % 11 = 3 from by omega]

/-- **Impl-side chunk closed form at `d = 11`**: `serialize_11` writes exactly the
    `lanewin 11` bytes of the two 8-lane groups. -/
private theorem serialize_11_eq
    (v : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8) (h : out.val.length = 22) (L : Nat → Nat)
    (hv : ∀ l : Nat, l < 16 → (v.elements.val[l]!).bv.toNat = L l)
    (hL : ∀ i : Nat, L i < 2048) :
    ∃ s : Slice Std.U8,
      libcrux_iot_ml_kem.vector.portable.serialize.serialize_11 v out = .ok s
      ∧ s.val.length = 22
      ∧ ∀ n : Nat, n < 22 → (s.val[n]!).val = lanewin 11 L n := by
  have hlen : CoreModels.core.slice.Slice.len out = .ok (22#usize : Std.Usize) := by
    show RustM.ok (Aeneas.Std.Slice.len out) = _
    congr 1
    apply Std.UScalar.eq_of_val_eq
    simp [h]
  obtain ⟨ns0, he0, y0_0, y0_1, y0_2, y0_3, y0_4, y0_5, y0_6, y0_7, y0_8, y0_9, y0_10, hs0, p0_0, p0_1, p0_2, p0_3, p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10⟩ :=
    e11_group v 0#usize 8#usize 0 (by scalar_tac) (by scalar_tac) (by omega) L hv hL
  norm_num at p0_0 p0_1 p0_2 p0_3 p0_4 p0_5 p0_6 p0_7 p0_8 p0_9 p0_10
  obtain ⟨ns1, he1, y1_0, y1_1, y1_2, y1_3, y1_4, y1_5, y1_6, y1_7, y1_8, y1_9, y1_10, hs1, p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p1_6, p1_7, p1_8, p1_9, p1_10⟩ :=
    e11_group v 8#usize 16#usize 1 (by scalar_tac) (by scalar_tac) (by omega) L hv hL
  norm_num at p1_0 p1_1 p1_2 p1_3 p1_4 p1_5 p1_6 p1_7 p1_8 p1_9 p1_10
  obtain ⟨t0, hu0, hl0, hq0⟩ :=
    Le_update_step (lanewin 11 L) 22 out 0 0#usize y0_0 (by scalar_tac) (by omega) h
      (by intro n hn; exact absurd hn (by omega)) p0_0
  obtain ⟨t1, hu1, hl1, hq1⟩ :=
    Le_update_step (lanewin 11 L) 22 t0 1 1#usize y0_1 (by scalar_tac) (by omega) hl0 hq0 p0_1
  obtain ⟨t2, hu2, hl2, hq2⟩ :=
    Le_update_step (lanewin 11 L) 22 t1 2 2#usize y0_2 (by scalar_tac) (by omega) hl1 hq1 p0_2
  obtain ⟨t3, hu3, hl3, hq3⟩ :=
    Le_update_step (lanewin 11 L) 22 t2 3 3#usize y0_3 (by scalar_tac) (by omega) hl2 hq2 p0_3
  obtain ⟨t4, hu4, hl4, hq4⟩ :=
    Le_update_step (lanewin 11 L) 22 t3 4 4#usize y0_4 (by scalar_tac) (by omega) hl3 hq3 p0_4
  obtain ⟨t5, hu5, hl5, hq5⟩ :=
    Le_update_step (lanewin 11 L) 22 t4 5 5#usize y0_5 (by scalar_tac) (by omega) hl4 hq4 p0_5
  obtain ⟨t6, hu6, hl6, hq6⟩ :=
    Le_update_step (lanewin 11 L) 22 t5 6 6#usize y0_6 (by scalar_tac) (by omega) hl5 hq5 p0_6
  obtain ⟨t7, hu7, hl7, hq7⟩ :=
    Le_update_step (lanewin 11 L) 22 t6 7 7#usize y0_7 (by scalar_tac) (by omega) hl6 hq6 p0_7
  obtain ⟨t8, hu8, hl8, hq8⟩ :=
    Le_update_step (lanewin 11 L) 22 t7 8 8#usize y0_8 (by scalar_tac) (by omega) hl7 hq7 p0_8
  obtain ⟨t9, hu9, hl9, hq9⟩ :=
    Le_update_step (lanewin 11 L) 22 t8 9 9#usize y0_9 (by scalar_tac) (by omega) hl8 hq8 p0_9
  obtain ⟨t10, hu10, hl10, hq10⟩ :=
    Le_update_step (lanewin 11 L) 22 t9 10 10#usize y0_10 (by scalar_tac) (by omega) hl9 hq9 p0_10
  obtain ⟨t11, hu11, hl11, hq11⟩ :=
    Le_update_step (lanewin 11 L) 22 t10 11 11#usize y1_0 (by scalar_tac) (by omega) hl10 hq10 p1_0
  obtain ⟨t12, hu12, hl12, hq12⟩ :=
    Le_update_step (lanewin 11 L) 22 t11 12 12#usize y1_1 (by scalar_tac) (by omega) hl11 hq11 p1_1
  obtain ⟨t13, hu13, hl13, hq13⟩ :=
    Le_update_step (lanewin 11 L) 22 t12 13 13#usize y1_2 (by scalar_tac) (by omega) hl12 hq12 p1_2
  obtain ⟨t14, hu14, hl14, hq14⟩ :=
    Le_update_step (lanewin 11 L) 22 t13 14 14#usize y1_3 (by scalar_tac) (by omega) hl13 hq13 p1_3
  obtain ⟨t15, hu15, hl15, hq15⟩ :=
    Le_update_step (lanewin 11 L) 22 t14 15 15#usize y1_4 (by scalar_tac) (by omega) hl14 hq14 p1_4
  obtain ⟨t16, hu16, hl16, hq16⟩ :=
    Le_update_step (lanewin 11 L) 22 t15 16 16#usize y1_5 (by scalar_tac) (by omega) hl15 hq15 p1_5
  obtain ⟨t17, hu17, hl17, hq17⟩ :=
    Le_update_step (lanewin 11 L) 22 t16 17 17#usize y1_6 (by scalar_tac) (by omega) hl16 hq16 p1_6
  obtain ⟨t18, hu18, hl18, hq18⟩ :=
    Le_update_step (lanewin 11 L) 22 t17 18 18#usize y1_7 (by scalar_tac) (by omega) hl17 hq17 p1_7
  obtain ⟨t19, hu19, hl19, hq19⟩ :=
    Le_update_step (lanewin 11 L) 22 t18 19 19#usize y1_8 (by scalar_tac) (by omega) hl18 hq18 p1_8
  obtain ⟨t20, hu20, hl20, hq20⟩ :=
    Le_update_step (lanewin 11 L) 22 t19 20 20#usize y1_9 (by scalar_tac) (by omega) hl19 hq19 p1_9
  obtain ⟨t21, hu21, hl21, hq21⟩ :=
    Le_update_step (lanewin 11 L) 22 t20 21 21#usize y1_10 (by scalar_tac) (by omega) hl20 hq20 p1_10
  refine ⟨t21, ?_, hl21, hq21⟩
  unfold libcrux_iot_ml_kem.vector.portable.serialize.serialize_11
  rw [hlen]
  simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.massert, if_true]
  rw [he0]; simp only [Aeneas.Std.bind_tc_ok]
  rw [bind_ok_11 hs0]
  rw [hu0]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu1]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu2]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu3]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu4]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu5]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu6]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu7]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu8]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu9]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu10]; simp only [Aeneas.Std.bind_tc_ok]
  rw [he1]; simp only [Aeneas.Std.bind_tc_ok]
  rw [bind_ok_11 hs1]
  rw [hu11]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu12]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu13]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu14]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu15]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu16]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu17]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu18]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu19]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hu20]; simp only [Aeneas.Std.bind_tc_ok]
  exact hu21


set_option maxHeartbeats 4000000 in
/-- The `d = 10` chunk loop. Written-prefix invariant `cInv` — L54Bank's, unchanged, since
    it is already stated at a general `d`. `h_bnd` is consumed HERE and only here, inside
    `to_unsigned_fm_eq`: that is the single conditional `+ q` where impl and spec can part
    company, and at these widths the witness is a NEGATIVE lane (-3330), not a positive
    unreduced one. -/
private theorem Le_loop_10_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hbnd : ∀ c : Nat, c < 16 → ∀ l : Nat, l < 16 →
      ((re.coefficients.val[c]!).elements.val[l]!).val.natAbs ≤ 3328)
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 320)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.compress_then_serialize_10_loop
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := 0#usize, «end» := 16#usize } re serialized scratch
    ⦃ ⇓ p => ⌜ (cInv re 10 320 16#usize p).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_10_loop
  refine libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
    (fun (iter1, serialized1, scratch1) =>
      libcrux_iot_ml_kem.serialize.compress_then_serialize_10_loop.body
        (vectortraitsOperationsInst := portable_ops_inst) re iter1 serialized1
          scratch1)
    (serialized, scratch) 0#usize 16#usize (cInv re 10 320) (by scalar_tac) ?_ ?_
  · show (pure _ : RustM Prop).holds
    simp only [Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp]
    intro _
    exact ⟨h_len, by intro n hn; exact absurd hn (by scalar_tac)⟩
  · intro acc k hk0 hk16 hinv
    have h16 : (16#usize : Std.Usize).val = 16 := rfl
    obtain ⟨hacc_len, hacc_done⟩ : acc.1.val.length = 320 ∧
        ∀ n : Nat, n < 2 * 10 * k.val → (acc.1.val[n]!).val = cByte re 10 n := by
      have hh := hinv
      simp only [cInv, Aeneas.Std.RustM.holds, pure, Pure.pure, Std.Do.Triple,
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
        to_unsigned_fm_eq (re.coefficients.val[k.val]!) acc.2
          (fun l hl => hbnd k.val hlt l hl)
      have hlanes : ∀ l : Nat, l < 16 →
          (sc1.elements.val[l]!).bv.toNat = encLane re (16 * k.val + l) := by
        intro l hl
        obtain ⟨hb0, hb1, hb2⟩ := hsc1 l hl
        exact uval_encLane re k.val l hlt hl _ hb0 hb1 hb2
      obtain ⟨sc2, hsc2_eq, hsc2⟩ :=
        compress_vec_eq (10#i32) 10 (by decide) (by omega) sc1
      have hclanes : ∀ l : Nat, l < 16 →
          (sc2.elements.val[l]!).bv.toNat = cLane re 10 (16 * k.val + l) := by
        intro l hl
        rw [hsc2 l hl, hlanes l hl]
        unfold cLane
        rw [compress_barrett_eq (encLane re (16 * k.val + l)) 10
          (encLane_lt re (16 * k.val + l)) (by omega)]
      obtain ⟨i1, hi1_eq, hi1⟩ := usize_mul_ok_e (20#usize : Std.Usize) k (by scalar_tac)
      obtain ⟨i2, hi2_eq, hi2⟩ := usize_add_ok_e i1 (20#usize : Std.Usize) (by scalar_tac)
      have hi1v : i1.val = 20 * k.val := by rw [hi1]; scalar_tac
      have hi2v : i2.val = 20 * k.val + 20 := by rw [hi2, hi1v]; scalar_tac
      obtain ⟨sub, wb, hmut_eq, hsub_len, hwb⟩ :=
        slice_index_mut_range_strict acc.1 i1 i2 (by omega) (by rw [hacc_len]; omega)
      have hsubw : sub.val.length = 20 := by rw [hsub_len]; omega
      obtain ⟨sres, hser_eq, hser_len, hser_get⟩ :=
        serialize_10_eq sc2 sub hsubw (fun j => cLane re 10 (16 * k.val + j)) hclanes
          (fun i => by have := cLane_lt re 10 (16 * k.val + i); simpa using this)
      refine libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.triple_of_ok_fc
        (v := .cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize), (wb sres, sc2))) ?_ ?_
      · show libcrux_iot_ml_kem.serialize.compress_then_serialize_10_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) re
          { start := k, «end» := 16#usize } acc.1 acc.2 = _
        unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_10_loop.body
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
                             portable_ops_inst t acc.2
            let scratch2 ← libcrux_iot_ml_kem.vector.portable.compress.compress
                             (10#i32 : Std.I32) scratch1
            let i1' ← (20#usize : Std.Usize) * k
            let i2' ← i1' + (20#usize : Std.Usize)
            let (sb, index_mut_back) ←
              CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
                (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                  Std.U8) acc.1 { start := i1', «end» := i2' }
            let s1 ← libcrux_iot_ml_kem.vector.portable.serialize.serialize_10 scratch2 sb
            RustM.ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
              (index_mut_back s1, scratch2)))) = _
        rw [h_idx]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hsc1_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hsc2_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hi1_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hi2_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hmut_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hser_eq]
        rfl
      · refine ⟨by rw [h16]; exact hlt, rfl, hs_val, ?_⟩
        show (cInv re 10 320 s (wb sres, sc2)).holds
        simp only [cInv, Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        have hwbv := hwb sres (by rw [hser_len]; omega)
        refine ⟨?_, ?_⟩
        · rw [hwbv, List.length_setSlice!]; exact hacc_len
        · intro n hn
          rw [hs_val] at hn
          rw [hwbv]
          by_cases hnk : n < 2 * 10 * k.val
          · rw [List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]
            exact hacc_done n hnk
          · rw [List.getElem!_setSlice!_middle _ _ _ _
              ⟨by omega, by rw [hser_len]; omega,
               by rw [hacc_len]; omega⟩]
            rw [hi1v, hser_get (n - 20 * k.val) (by omega),
              lanewin_shift re 10 k.val (n - 20 * k.val) (by omega)]
            congr 1
            omega
    · have hk : k.val = 16 := by omega
      refine libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.triple_of_ok_fc
        (v := .done acc) ?_ ?_
      · show libcrux_iot_ml_kem.serialize.compress_then_serialize_10_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) re
          { start := k, «end» := 16#usize } acc.1 acc.2 = _
        unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_10_loop.body
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
      · show (cInv re 10 320 16#usize acc).holds
        simp only [cInv, Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        exact ⟨hacc_len, by intro n hn; exact hacc_done n (by rw [hk]; rw [h16] at hn; omega)⟩

/-- `compress_then_serialize_10` = the `massert` on the caller's slice length, then the
    loop. The `massert` is what makes `h_len` load-bearing: `compress_then_serialize_5`
    has no `BLOCK_LEN` parameter and no assertion, so L5.4 needed no such hypothesis. -/
private theorem Le_impl_10_fc (BLOCK_LEN : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hbnd : ∀ c : Nat, c < 16 → ∀ l : Nat, l < 16 →
      ((re.coefficients.val[c]!).elements.val[l]!).val.natAbs ≤ 3328)
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 320)
    (hbl : BLOCK_LEN.val = 320)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.compress_then_serialize_10 BLOCK_LEN
      (vectortraitsOperationsInst := portable_ops_inst) re serialized scratch
    ⦃ ⇓ p => ⌜ (cInv re 10 320 16#usize p).holds ⌝ ⦄ := by
  have hlen : CoreModels.core.slice.Slice.len serialized = .ok BLOCK_LEN := by
    show RustM.ok (Aeneas.Std.Slice.len serialized) = _
    congr 1
    apply Std.UScalar.eq_of_val_eq
    simp [h_len, hbl]
  unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_10
  rw [hlen]
  simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.massert, if_true]
  rw [vectors_in_ring_element_eq]; simp only [Aeneas.Std.bind_tc_ok]
  exact Le_loop_10_fc re hbnd serialized h_len scratch


set_option maxHeartbeats 4000000 in
/-- The `d = 11` chunk loop. Written-prefix invariant `cInv` — L54Bank's, unchanged, since
    it is already stated at a general `d`. `h_bnd` is consumed HERE and only here, inside
    `to_unsigned_fm_eq`: that is the single conditional `+ q` where impl and spec can part
    company, and at these widths the witness is a NEGATIVE lane (-3330), not a positive
    unreduced one. -/
private theorem Le_loop_11_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hbnd : ∀ c : Nat, c < 16 → ∀ l : Nat, l < 16 →
      ((re.coefficients.val[c]!).elements.val[l]!).val.natAbs ≤ 3328)
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 352)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.compress_then_serialize_11_loop
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := 0#usize, «end» := 16#usize } re serialized scratch
    ⦃ ⇓ p => ⌜ (cInv re 11 352 16#usize p).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_11_loop
  refine libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
    (fun (iter1, serialized1, scratch1) =>
      libcrux_iot_ml_kem.serialize.compress_then_serialize_11_loop.body
        (vectortraitsOperationsInst := portable_ops_inst) re iter1 serialized1
          scratch1)
    (serialized, scratch) 0#usize 16#usize (cInv re 11 352) (by scalar_tac) ?_ ?_
  · show (pure _ : RustM Prop).holds
    simp only [Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp]
    intro _
    exact ⟨h_len, by intro n hn; exact absurd hn (by scalar_tac)⟩
  · intro acc k hk0 hk16 hinv
    have h16 : (16#usize : Std.Usize).val = 16 := rfl
    obtain ⟨hacc_len, hacc_done⟩ : acc.1.val.length = 352 ∧
        ∀ n : Nat, n < 2 * 11 * k.val → (acc.1.val[n]!).val = cByte re 11 n := by
      have hh := hinv
      simp only [cInv, Aeneas.Std.RustM.holds, pure, Pure.pure, Std.Do.Triple,
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
        to_unsigned_fm_eq (re.coefficients.val[k.val]!) acc.2
          (fun l hl => hbnd k.val hlt l hl)
      have hlanes : ∀ l : Nat, l < 16 →
          (sc1.elements.val[l]!).bv.toNat = encLane re (16 * k.val + l) := by
        intro l hl
        obtain ⟨hb0, hb1, hb2⟩ := hsc1 l hl
        exact uval_encLane re k.val l hlt hl _ hb0 hb1 hb2
      obtain ⟨sc2, hsc2_eq, hsc2⟩ :=
        compress_vec_eq (11#i32) 11 (by decide) (by omega) sc1
      have hclanes : ∀ l : Nat, l < 16 →
          (sc2.elements.val[l]!).bv.toNat = cLane re 11 (16 * k.val + l) := by
        intro l hl
        rw [hsc2 l hl, hlanes l hl]
        unfold cLane
        rw [compress_barrett_eq (encLane re (16 * k.val + l)) 11
          (encLane_lt re (16 * k.val + l)) (by omega)]
      obtain ⟨i1, hi1_eq, hi1⟩ := usize_mul_ok_e (22#usize : Std.Usize) k (by scalar_tac)
      obtain ⟨i2, hi2_eq, hi2⟩ := usize_add_ok_e i1 (22#usize : Std.Usize) (by scalar_tac)
      have hi1v : i1.val = 22 * k.val := by rw [hi1]; scalar_tac
      have hi2v : i2.val = 22 * k.val + 22 := by rw [hi2, hi1v]; scalar_tac
      obtain ⟨sub, wb, hmut_eq, hsub_len, hwb⟩ :=
        slice_index_mut_range_strict acc.1 i1 i2 (by omega) (by rw [hacc_len]; omega)
      have hsubw : sub.val.length = 22 := by rw [hsub_len]; omega
      obtain ⟨sres, hser_eq, hser_len, hser_get⟩ :=
        serialize_11_eq sc2 sub hsubw (fun j => cLane re 11 (16 * k.val + j)) hclanes
          (fun i => by have := cLane_lt re 11 (16 * k.val + i); simpa using this)
      refine libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.triple_of_ok_fc
        (v := .cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize), (wb sres, sc2))) ?_ ?_
      · show libcrux_iot_ml_kem.serialize.compress_then_serialize_11_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) re
          { start := k, «end» := 16#usize } acc.1 acc.2 = _
        unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_11_loop.body
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
            let scratch1 ← libcrux_iot_ml_kem.vector.traits.to_unsigned_representative
                             portable_ops_inst t acc.2
            let scratch2 ← libcrux_iot_ml_kem.vector.portable.compress.compress
                             (11#i32 : Std.I32) scratch1
            let i1' ← (22#usize : Std.Usize) * k
            let i2' ← i1' + (22#usize : Std.Usize)
            let (sb, index_mut_back) ←
              CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
                (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                  Std.U8) acc.1 { start := i1', «end» := i2' }
            let s1 ← libcrux_iot_ml_kem.vector.portable.serialize.serialize_11 scratch2 sb
            RustM.ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
              (index_mut_back s1, scratch2)))) = _
        rw [h_idx]; simp only [Aeneas.Std.bind_tc_ok]
        rw [← tufm_eq_tur (re.coefficients.val[k.val]!) acc.2, hsc1_eq]
        simp only [Aeneas.Std.bind_tc_ok]
        rw [hsc2_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hi1_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hi2_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hmut_eq]; simp only [Aeneas.Std.bind_tc_ok]
        rw [hser_eq]
        rfl
      · refine ⟨by rw [h16]; exact hlt, rfl, hs_val, ?_⟩
        show (cInv re 11 352 s (wb sres, sc2)).holds
        simp only [cInv, Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        have hwbv := hwb sres (by rw [hser_len]; omega)
        refine ⟨?_, ?_⟩
        · rw [hwbv, List.length_setSlice!]; exact hacc_len
        · intro n hn
          rw [hs_val] at hn
          rw [hwbv]
          by_cases hnk : n < 2 * 11 * k.val
          · rw [List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]
            exact hacc_done n hnk
          · rw [List.getElem!_setSlice!_middle _ _ _ _
              ⟨by omega, by rw [hser_len]; omega,
               by rw [hacc_len]; omega⟩]
            rw [hi1v, hser_get (n - 22 * k.val) (by omega),
              lanewin_shift re 11 k.val (n - 22 * k.val) (by omega)]
            congr 1
            omega
    · have hk : k.val = 16 := by omega
      refine libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement.triple_of_ok_fc
        (v := .done acc) ?_ ?_
      · show libcrux_iot_ml_kem.serialize.compress_then_serialize_11_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) re
          { start := k, «end» := 16#usize } acc.1 acc.2 = _
        unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_11_loop.body
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
      · show (cInv re 11 352 16#usize acc).holds
        simp only [cInv, Aeneas.Std.RustM.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        exact ⟨hacc_len, by intro n hn; exact hacc_done n (by rw [hk]; rw [h16] at hn; omega)⟩

/-- `compress_then_serialize_11` = the `massert` on the caller's slice length, then the
    loop. The `massert` is what makes `h_len` load-bearing: `compress_then_serialize_5`
    has no `BLOCK_LEN` parameter and no assertion, so L5.4 needed no such hypothesis. -/
private theorem Le_impl_11_fc (BLOCK_LEN : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hbnd : ∀ c : Nat, c < 16 → ∀ l : Nat, l < 16 →
      ((re.coefficients.val[c]!).elements.val[l]!).val.natAbs ≤ 3328)
    (serialized : Slice Std.U8) (h_len : serialized.val.length = 352)
    (hbl : BLOCK_LEN.val = 352)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.compress_then_serialize_11 BLOCK_LEN
      (vectortraitsOperationsInst := portable_ops_inst) re serialized scratch
    ⦃ ⇓ p => ⌜ (cInv re 11 352 16#usize p).holds ⌝ ⦄ := by
  have hlen : CoreModels.core.slice.Slice.len serialized = .ok BLOCK_LEN := by
    show RustM.ok (Aeneas.Std.Slice.len serialized) = _
    congr 1
    apply Std.UScalar.eq_of_val_eq
    simp [h_len, hbl]
  unfold libcrux_iot_ml_kem.serialize.compress_then_serialize_11
  rw [hlen]
  simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.massert, if_true]
  rw [vectors_in_ring_element_eq]; simp only [Aeneas.Std.bind_tc_ok]
  exact Le_loop_11_fc re hbnd serialized h_len scratch

/-! ### SPEC side. `byte_encode_gen_eq` is already generic in `d ∈ [4, 12]`, so the only
    new statement is the `byte_encode_into` slice wrapper at the two new widths — the
    `dv ∈ {4,5}` version (`byte_encode_into_45_eq`) is the shape, verbatim. -/

private theorem byte_encode_into_1011_eq
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (du : Std.Usize) (hdu : du.val = 10 ∨ du.val = 11)
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (ha : ∀ k : Nat, k < 256 → ((a.val[k]!).val).val = cLane re du.val k)
    (out : Slice Std.U8) (h_len : out.val.length = 32 * du.val) :
    ∃ s : Slice Std.U8,
      hacspec_ml_kem.serialize.byte_encode_into a du out = .ok s
      ∧ s.val.length = 32 * du.val
      ∧ ∀ n : Nat, n < 32 * du.val → (s.val[n]!).val = cByte re du.val n := by
  have hcopy : ∀ (D32 : Std.Usize) (enc : Std.Array Std.U8 D32),
      D32.val = 32 * du.val →
      CoreModels.core.slice.Slice.copy_from_slice CoreModels.core.U8.Insts.CoreMarkerCopy out
          (Aeneas.Std.Array.to_slice enc)
        = .ok (Aeneas.Std.Array.to_slice enc) := by
    intro D32 enc hD32
    have hlen_enc : (Aeneas.Std.Array.to_slice enc).val.length = 32 * du.val := by
      show enc.val.length = _
      have := enc.property; rw [show enc.val.length = D32.val from by simpa using this, hD32]
    -- `copy_from_slice` now routes through `rust_primitives.slice.slice_clone_from_slice`
    -- (a `mapM clone` over the source); the `Util.SliceSpecs` bridge collapses it for a
    -- `Copy` instance whose `clone` is the identity, and needs the raw length equality.
    exact libcrux_iot_ml_kem.Util.SliceSpecs.core_models_slice_Slice_copy_from_slice_eq
      _ out (Aeneas.Std.Array.to_slice enc) (by rw [h_len, hlen_enc]) (by intro x; rfl)
  rcases hdu with h10 | h11
  · have hdueq : du = 10#usize := Aeneas.Std.UScalar.eq_of_val_eq (by scalar_tac)
    subst hdueq
    obtain ⟨enc, henc, henc_get⟩ :=
      byte_encode_gen_eq re (320#usize) (2560#usize) (10#usize) (by scalar_tac) (by scalar_tac)
        (by scalar_tac) (by scalar_tac) a ha
    refine ⟨Aeneas.Std.Array.to_slice enc, ?_, ?_, ?_⟩
    · unfold hacspec_ml_kem.serialize.byte_encode_into
      simp only [hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT, Aeneas.Std.massert,
        Aeneas.Std.bind_tc_ok, Aeneas.Std.lift,
        show ((10#usize : Std.Usize).val) = 10 from rfl, henc]
      -- (`byte_encode_into`'s `massert (d ≤ BITS_PER_COEFFICIENT)` and
      --  `massert (out.len = 32 * d)` prelude is gone from the hax v0.4.0-rc.1
      --  extraction, so the length/bound stepping that stood here is unnecessary)
      exact hcopy (320#usize) enc (by scalar_tac)
    · show enc.val.length = _
      have := enc.property
      rw [show enc.val.length = ((320#usize : Std.Usize)).val from by simpa using this]
      scalar_tac
    · intro n hn
      show (enc.val[n]!).val = _
      exact henc_get n (by scalar_tac)
  · have hdueq : du = 11#usize := Aeneas.Std.UScalar.eq_of_val_eq (by scalar_tac)
    subst hdueq
    obtain ⟨enc, henc, henc_get⟩ :=
      byte_encode_gen_eq re (352#usize) (2816#usize) (11#usize) (by scalar_tac) (by scalar_tac)
        (by scalar_tac) (by scalar_tac) a ha
    refine ⟨Aeneas.Std.Array.to_slice enc, ?_, ?_, ?_⟩
    · unfold hacspec_ml_kem.serialize.byte_encode_into
      simp only [hacspec_ml_kem.parameters.BITS_PER_COEFFICIENT, Aeneas.Std.massert,
        Aeneas.Std.bind_tc_ok, Aeneas.Std.lift,
        show ((11#usize : Std.Usize).val) = 11 from rfl, henc]
      -- (`byte_encode_into`'s `massert (d ≤ BITS_PER_COEFFICIENT)` and
      --  `massert (out.len = 32 * d)` prelude is gone from the hax v0.4.0-rc.1
      --  extraction, so the length/bound stepping that stood here is unnecessary)
      exact hcopy (352#usize) enc (by scalar_tac)
    · show enc.val.length = _
      have := enc.property
      rw [show enc.val.length = ((352#usize : Std.Usize)).val from by simpa using this]
      scalar_tac
    · intro n hn
      show (enc.val[n]!).val = _
      exact henc_get n (by scalar_tac)

/-- **Spec-side apex.** `L54_spec_eq` at the other two widths: `Compress_du` then
    `ByteEncode_du` into the freshly-zeroed `BLOCK_LEN`-array is exactly `cByte re du`. -/
private theorem Le_spec_eq
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (BLOCK_LEN du : Std.Usize) (hdu : du.val = 10 ∨ du.val = 11)
    (hbl : BLOCK_LEN.val = 32 * du.val) :
    ∃ enc : Std.Array Std.U8 BLOCK_LEN,
      hacspec_ml_kem.serialize.compress_then_serialize_v BLOCK_LEN (lift_poly re) du = .ok enc
      ∧ ∀ n : Nat, n < BLOCK_LEN.val → (enc.val[n]!).val = cByte re du.val n := by
  have hd12 : du.val < 12 := by rcases hdu with h | h <;> omega
  obtain ⟨a, ha, ha_get⟩ := compress_v_get re du hd12
  have hzlen : (Aeneas.Std.Array.to_slice
      (Aeneas.Std.Array.repeat BLOCK_LEN (0#u8 : Std.U8))).val.length = 32 * du.val := by
    show (Aeneas.Std.Array.repeat BLOCK_LEN (0#u8 : Std.U8)).val.length = _
    rw [Aeneas.Std.Array.repeat_val, List.length_replicate, hbl]
  obtain ⟨s1, hs1, hs1len, hs1get⟩ :=
    byte_encode_into_1011_eq re du hdu a ha_get _ hzlen
  refine ⟨Aeneas.Std.Array.from_slice
    (Aeneas.Std.Array.repeat BLOCK_LEN (0#u8 : Std.U8)) s1, ?_, ?_⟩
  · show (do
        let a' ← hacspec_ml_kem.compress.compress (lift_poly re) du
        let s1' ← hacspec_ml_kem.serialize.byte_encode_into a' du
                    (Aeneas.Std.Array.to_slice
                      (Aeneas.Std.Array.repeat BLOCK_LEN (0#u8 : Std.U8)))
        RustM.ok (Aeneas.Std.Array.from_slice
          (Aeneas.Std.Array.repeat BLOCK_LEN (0#u8 : Std.U8)) s1')) = _
    rw [ha]; simp only [Aeneas.Std.bind_tc_ok]
    rw [hs1]; rfl
  · intro n hn
    rw [Aeneas.Std.Array.from_slice_val _ _ (by rw [hs1len, hbl])]
    exact hs1get n (by omega)

/-! ### The const dispatch. `match U_COMPRESSION_FACTOR as u32 { 10, 11, _ => panic }` —
    `Lu_dispatch_of_pre`'s shape on the encode side, with the extra `BLOCK_LEN` argument
    that `compress_then_serialize_10` / `_11` take and their decode counterparts do not. -/

private theorem Le_dispatch_eq_d10 (BLOCK_LEN : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (serialized : Slice Std.U8)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_u
      (vectortraitsOperationsInst := portable_ops_inst) 10#usize BLOCK_LEN re serialized scratch
    = libcrux_iot_ml_kem.serialize.compress_then_serialize_10 BLOCK_LEN
        (vectortraitsOperationsInst := portable_ops_inst) re serialized scratch := by
  simp only [libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_u,
    Aeneas.Std.lift, Aeneas.Std.bind_tc_ok, Std.UScalar.cast, Std.UScalarTy.U32_numBits_eq]
  simp

private theorem Le_dispatch_eq_d11 (BLOCK_LEN : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (serialized : Slice Std.U8)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_u
      (vectortraitsOperationsInst := portable_ops_inst) 11#usize BLOCK_LEN re serialized scratch
    = libcrux_iot_ml_kem.serialize.compress_then_serialize_11 BLOCK_LEN
        (vectortraitsOperationsInst := portable_ops_inst) re serialized scratch := by
  simp only [libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_u,
    Aeneas.Std.lift, Aeneas.Std.bind_tc_ok, Std.UScalar.cast, Std.UScalarTy.U32_numBits_eq]
  simp

private theorem Le_dispatch_of_pre (U_COMPRESSION_FACTOR BLOCK_LEN : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (serialized : Slice Std.U8)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_du : U_COMPRESSION_FACTOR.val = 10 ∨ U_COMPRESSION_FACTOR.val = 11) :
    libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_u
      (vectortraitsOperationsInst := portable_ops_inst)
      U_COMPRESSION_FACTOR BLOCK_LEN re serialized scratch
    = if U_COMPRESSION_FACTOR.val = 10 then
        libcrux_iot_ml_kem.serialize.compress_then_serialize_10 BLOCK_LEN
          (vectortraitsOperationsInst := portable_ops_inst) re serialized scratch
      else
        libcrux_iot_ml_kem.serialize.compress_then_serialize_11 BLOCK_LEN
          (vectortraitsOperationsInst := portable_ops_inst) re serialized scratch := by
  rcases h_du with h | h
  · rw [show U_COMPRESSION_FACTOR = 10#usize from
        Aeneas.Std.UScalar.eq_of_val_eq (by scalar_tac), Le_dispatch_eq_d10]
    simp
  · rw [show U_COMPRESSION_FACTOR = 11#usize from
        Aeneas.Std.UScalar.eq_of_val_eq (by scalar_tac), Le_dispatch_eq_d11]
    simp

end LuEncBank

/-- **INC-2a.5** — `serialize.compress_then_serialize_ring_element_u`.

    The encode direction of INC-2a.4, and the `du ∈ {10, 11}` sibling of L5.4
    (`compress_then_serialize_ring_element_v_fc`). The impl writes into the caller's
    `serialized` slice and threads `scratch`; the hacspec returns a fresh
    `Array U8 BLOCK_LEN`, so the post compares the returned slice bytewise against the
    spec array — exactly as L5.4 does.

    Hypotheses transcribed VERBATIM from the upstream contract
    (libcrux-ml-kem/src/serialize.rs, `compress_then_serialize_ring_element_u`):
      (v $COMPRESSION_FACTOR == 10 \/ v $COMPRESSION_FACTOR == 11)
      /\ v $OUT_LEN == 32 * v $COMPRESSION_FACTOR
      /\ Libcrux_ml_kem.Polynomial.Spec.is_bounded_poly (sz 3328) $re
    `h_len` is the additional iot-side fact that the caller's slice really has `BLOCK_LEN`
    bytes — the impl asserts it (`massert (serialized.len = BLOCK_LEN)` inside
    `compress_then_serialize_10` / `_11`), and without it the statement is false by
    panic, not by mismatch.

    `h_bnd` is the conjunct whose absence cost $71.82 on L5.6 and which L5.4 records a
    witness for: `byte_encode` reads a canonicalised `FieldElement.val` while the impl's
    `to_unsigned_field_modulus` adds q AT MOST ONCE, so an unreduced coefficient makes
    impl and spec genuinely disagree. -/
@[spec]
theorem compress_then_serialize_ring_element_u_fc
    (U_COMPRESSION_FACTOR BLOCK_LEN : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (out : Slice Std.U8)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_cf : U_COMPRESSION_FACTOR.val = 10 ∨ U_COMPRESSION_FACTOR.val = 11)
    (h_len : out.length = BLOCK_LEN.val)
    (h_block : BLOCK_LEN.val = 32 * U_COMPRESSION_FACTOR.val)
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
        ((re.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_u
      (vectortraitsOperationsInst := portable_ops_inst)
      U_COMPRESSION_FACTOR BLOCK_LEN re out scratch
    ⦃ ⇓ p => ⌜ ∃ enc : Std.Array Std.U8 BLOCK_LEN,
                  hacspec_ml_kem.serialize.compress_then_serialize_v
                      BLOCK_LEN (lift_poly re) U_COMPRESSION_FACTOR
                    = .ok enc
                  ∧ p.1.length = BLOCK_LEN.val
                  ∧ ∀ ℓ : Nat, ℓ < BLOCK_LEN.val → p.1.val[ℓ]! = enc.val[ℓ]! ⌝ ⦄ := by
  have hlen' : out.val.length = BLOCK_LEN.val := h_len
  -- SPEC side, once and for both arms: `Compress_du` then `ByteEncode_du` is `cByte re du`.
  obtain ⟨enc, henc, hencget⟩ := Le_spec_eq re BLOCK_LEN U_COMPRESSION_FACTOR h_cf h_block
  -- FIRST RUNG: the `unreachable!()`/`fail panic` arm is gone.
  rw [Le_dispatch_of_pre U_COMPRESSION_FACTOR BLOCK_LEN re out scratch h_cf]
  rcases h_cf with h10 | h11
  · rw [if_pos h10]
    rw [h10] at hencget
    have hl10 : out.val.length = 320 := by rw [hlen', h_block, h10]
    -- IMPL side. `h_bnd` is consumed inside `Le_impl_10_fc`, in `to_unsigned_fm_eq`.
    obtain ⟨p, hp_eq, hp⟩ := triple_exists_ok_fc
      (Le_impl_10_fc BLOCK_LEN re h_bnd out hl10 (by rw [h_block, h10]) scratch)
    obtain ⟨hplen, hpget⟩ : p.1.val.length = 320 ∧
        ∀ n : Nat, n < 2 * 10 * ((16#usize : Std.Usize)).val →
          (p.1.val[n]!).val = cByte re 10 n := by
      simp only [cInv, Aeneas.Std.RustM.holds, pure, Pure.pure, Std.Do.Triple,
        Std.Do.WP.wp, Std.Do.PredTrans.apply, Std.Do.PostCond.noThrow,
        Std.Do.SPred.pure, Std.Do.SPred.entails] at hp
      exact hp trivial
    refine triple_of_ok_fc hp_eq ⟨enc, henc, ?_, ?_⟩
    · show p.1.val.length = BLOCK_LEN.val
      rw [hplen, h_block, h10]
    · intro ℓ hℓ
      refine Aeneas.Std.UScalar.eq_of_val_eq ?_
      rw [hpget ℓ (by rw [h_block, h10] at hℓ; scalar_tac), hencget ℓ hℓ]
  · rw [if_neg (by omega)]
    rw [h11] at hencget
    have hl11 : out.val.length = 352 := by rw [hlen', h_block, h11]
    obtain ⟨p, hp_eq, hp⟩ := triple_exists_ok_fc
      (Le_impl_11_fc BLOCK_LEN re h_bnd out hl11 (by rw [h_block, h11]) scratch)
    obtain ⟨hplen, hpget⟩ : p.1.val.length = 352 ∧
        ∀ n : Nat, n < 2 * 11 * ((16#usize : Std.Usize)).val →
          (p.1.val[n]!).val = cByte re 11 n := by
      simp only [cInv, Aeneas.Std.RustM.holds, pure, Pure.pure, Std.Do.Triple,
        Std.Do.WP.wp, Std.Do.PredTrans.apply, Std.Do.PostCond.noThrow,
        Std.Do.SPred.pure, Std.Do.SPred.entails] at hp
      exact hp trivial
    refine triple_of_ok_fc hp_eq ⟨enc, henc, ?_, ?_⟩
    · show p.1.val.length = BLOCK_LEN.val
      rw [hplen, h_block, h11]
    · intro ℓ hℓ
      refine Aeneas.Std.UScalar.eq_of_val_eq ?_
      rw [hpget ℓ (by rw [h_block, h11] at hℓ; scalar_tac), hencget ℓ hℓ]

end libcrux_iot_ml_kem.SerializeFc
