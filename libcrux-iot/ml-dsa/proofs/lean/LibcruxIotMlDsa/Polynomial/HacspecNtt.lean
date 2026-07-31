/-
  # `Polynomial/HacspecNtt.lean` — `ntt` / `invert_ntt` equivalence to the extracted hacspec

  The poly-layer NTT impl FCs (`Polynomial/Ntt.lean::{ntt_fc, invert_ntt_montgomery_fc}`)
  post the impl result equal (through `lift_poly`) to the HAND spec `Spec.Pure.{ntt,intt}`
  (the inverse output carrying an extra `·R` from the Montgomery-domain master).

  This file proves the HAND spec equals the machine-EXTRACTED `hacspec_ml_dsa.ntt.*` spec
  (under the residue lift `lift_res`), so the extracted spec — not the hand spec — is the
  trusted reference, then composes hacspec-facing corollary FCs over the impl entry points.

  Structure (mirrors `Spec/HacspecBridge.lean`):
    (0) `zetas_bridge` — the `ZETAS` table = `Pure.zeta` under the residue lift (kernel
        `decide` in `ZMod Q`, whole-table form), plus the small Usize-arithmetic helpers.
    (1) `ntt_layer_bridge` / `intt_layer_bridge` — one extracted `createi`-layer = one
        `Pure.{ntt,intt}_layer` step (the createi-per-layer proof, à la `poly_add_bridge`).
    (2) `reduce_polynomial_bridge` — the final `·256⁻¹` scale.
    (3) `ntt_bridge` / `intt_bridge` — the 8-layer fold (+ reduce for intt).
    (4) `ntt_hacspec_eq` / `intt_hacspec_eq` plain lemmas (consume the impl-FC post) +
        `@[spec] ntt_hacspec_fc` / `intt_hacspec_fc` Triple corollaries (intt `·R`-reconciled).
-/
import LibcruxIotMlDsa.Spec.HacspecBridge
import LibcruxIotMlDsa.Polynomial.Ntt

open CoreModels Aeneas Aeneas.Std Result Std.Do
open libcrux_iot_ml_dsa.Spec
open libcrux_iot_ml_dsa.Spec.Parameters
open libcrux_iot_ml_dsa.Spec.Lift libcrux_iot_ml_dsa.Spec.Montgomery
open libcrux_iot_ml_dsa.Spec.HacspecBridge

namespace libcrux_iot_ml_dsa.Polynomial.HacspecNtt

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## (0a) The `ZETAS` table bridge: extracted table = `Pure.zeta` (residue lift). -/

set_option maxRecDepth 4000 in
set_option maxHeartbeats 16000000 in
unseal hacspec_ml_dsa.ntt.ZETAS in
/-- **The zeta-table bridge.** The extracted (clean, non-Montgomery) `ZETAS[j]`
    lifts to `Parameters.zeta j` in `Z_q`. Proven by kernel `decide` in `ZMod Q`
    over the whole bounded table (NOT `native_decide`); the `ZETAS` table is
    `@[irreducible]`, so we `unseal` it for the `decide`. -/
theorem zetas_bridge : ∀ j, j < 256 →
    ((hacspec_ml_dsa.ntt.ZETAS.val[j]!).val : Zq) = zeta j := by
  decide

/-! ## (0b) Small Usize-arithmetic value lemmas (operands `< 2¹⁶`).

The extracted layers compute `len`/`k`/`round`/`idx`/`i±len` with Rust `usize`
operators on values `< 256`; these reduce to the corresponding `Nat` ops. The
helpers are **value-keyed** (each takes `Std.Usize` arguments plus a `.val` fact),
so they match the literal forms in the extraction (`2#usize`, `128#usize`, …) and
the `⟨BitVec.ofNat _ i⟩` lane witness alike — yielding `op = .ok z ∧ z.val = nat-op`. -/

theorem nb16 : 16 ≤ System.Platform.numBits := by
  cases System.Platform.numBits_eq with
  | inl h => rw [h]; decide
  | inr h => rw [h]; decide

theorem usize_pow16_le : (65536 : Nat) ≤ 2 ^ UScalarTy.Usize.numBits := by
  rw [UScalarTy.Usize_numBits_eq]
  calc (65536 : Nat) = 2 ^ 16 := by decide
    _ ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) nb16

/-- The `.val` of a small (`< 2¹⁶`) `Usize` literal built from `BitVec.ofNat`. -/
theorem usize_val (n : Nat) (h : n < 65536) :
    (⟨BitVec.ofNat _ n⟩ : Std.Usize).val = n := by
  show (BitVec.ofNat _ n).toNat = n
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := usize_pow16_le; omega)]

/-- `x <<< y = 2^(y.val)` as a `usize` (`y.val ≤ 15`). -/
theorem usize_shl (x y : Std.Usize) (n : Nat) (hx : x.val = 1) (hy : y.val = n) (hn : n ≤ 15) :
    ∃ z : Std.Usize, (x <<< y : Result Std.Usize) = .ok z ∧ z.val = 2 ^ n := by
  have hcond : y.val < UScalarTy.Usize.numBits := by
    rw [hy]; show n < System.Platform.numBits; have := nb16; omega
  refine ⟨⟨x.bv.shiftLeft y.val⟩, ?_, ?_⟩
  · simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft, if_pos hcond]
  · show (x.bv.shiftLeft y.val).toNat = 2 ^ n
    rw [BitVec.shiftLeft_eq, BitVec.toNat_shiftLeft]
    show (x.bv.toNat <<< y.val) % 2 ^ UScalarTy.Usize.numBits = 2 ^ n
    have hxbv : x.bv.toNat = 1 := hx
    rw [hxbv, hy, Nat.shiftLeft_eq, one_mul, UScalarTy.Usize_numBits_eq,
      Nat.mod_eq_of_lt (by calc (2:Nat)^n ≤ 2^15 := Nat.pow_le_pow_right (by decide) hn
        _ < 2 ^ 16 := by decide
        _ ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) nb16)]

/-- `x * y` as a `usize` (product `< 2¹⁶`). -/
theorem usize_mul (x y : Std.Usize) (a b : Nat) (hx : x.val = a) (hy : y.val = b)
    (hab : a * b < 65536) :
    ∃ z : Std.Usize, (x * y : Result Std.Usize) = .ok z ∧ z.val = a * b := by
  have hmax : x.val * y.val ≤ UScalar.max .Usize := by
    rw [hx, hy, UScalar.max_USize_eq, Usize.max, Usize.numBits]
    have := usize_pow16_le; omega
  obtain ⟨z, hz_eq, hz_val⟩ := Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.UScalar.mul_spec hmax)
  exact ⟨z, hz_eq, by rw [hz_val, hx, hy]⟩

/-- `x / y` as a `usize` (`y.val ≠ 0`). -/
theorem usize_div (x y : Std.Usize) (a b : Nat) (hx : x.val = a) (hy : y.val = b) (hbnz : b ≠ 0) :
    ∃ z : Std.Usize, (x / y : Result Std.Usize) = .ok z ∧ z.val = a / b := by
  have hbnz' : y.val ≠ (0 : Nat) := by rw [hy]; exact hbnz
  obtain ⟨z, hz_eq, hz_val⟩ := Aeneas.Std.UScalar.div_spec _ hbnz'
  exact ⟨z, hz_eq, by rw [hz_val, hx, hy]⟩

/-- `x % y` as a `usize` (`y.val ≠ 0`). -/
theorem usize_rem (x y : Std.Usize) (a b : Nat) (hx : x.val = a) (hy : y.val = b) (hbnz : b ≠ 0) :
    ∃ z : Std.Usize, (x % y : Result Std.Usize) = .ok z ∧ z.val = a % b := by
  have hbnz' : y.val ≠ (0 : Nat) := by rw [hy]; exact hbnz
  obtain ⟨z, hz_eq, hz_val⟩ := Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.UScalar.rem_spec _ hbnz')
  exact ⟨z, hz_eq, by rw [hz_val, hx, hy]⟩

/-- `x + y` as a `usize` (sum `< 2¹⁶`). -/
theorem usize_add (x y : Std.Usize) (a b : Nat) (hx : x.val = a) (hy : y.val = b)
    (hab : a + b < 65536) :
    ∃ z : Std.Usize, (x + y : Result Std.Usize) = .ok z ∧ z.val = a + b := by
  have hmax : x.val + y.val ≤ UScalar.max .Usize := by
    rw [hx, hy, UScalar.max_USize_eq, Usize.max, Usize.numBits]
    have := usize_pow16_le; omega
  obtain ⟨z, hz_eq, hz_val⟩ := Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.UScalar.add_spec hmax)
  exact ⟨z, hz_eq, by rw [hz_val, hx, hy]⟩

/-- `x - y` as a `usize` (`y.val ≤ x.val`). -/
theorem usize_sub (x y : Std.Usize) (a b : Nat) (hx : x.val = a) (hy : y.val = b) (hba : b ≤ a) :
    ∃ z : Std.Usize, (x - y : Result Std.Usize) = .ok z ∧ z.val = a - b := by
  have hle : y.val ≤ x.val := by rw [hx, hy]; exact hba
  obtain ⟨z, hz_eq, hz_val⟩ := Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.UScalar.sub_spec hle)
  exact ⟨z, hz_eq, by rw [hz_val.1, hx, hy]⟩

/-! ## (0c) Per-lane helpers (private copies of the `HacspecBridge` privates). -/

/-- `Array.index_usize a ⟨k⟩ = .ok (a[k]!)` for `k < 256` (copy of `HacspecBridge.idx_ok`). -/
private theorem idx_ok (a : Aeneas.Std.Array Std.I32 256#usize) (k : Nat) (hk : k < 256) :
    Aeneas.Std.Array.index_usize a (⟨BitVec.ofNat _ k⟩ : Std.Usize) = .ok (a.val[k]!) := by
  have hk_us : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k := usize_val k (by omega)
  have hlen : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val < a.length := by
    rw [hk_us]; show k < a.val.length; rw [a.property]; exact hk
  have hT := Aeneas.Std.Array.index_usize_spec a (⟨BitVec.ofNat _ k⟩ : Std.Usize) hlen
  obtain ⟨v', hveq, hPv'⟩ := Aeneas.Std.WP.spec_imp_exists hT
  rw [hveq, hPv']
  simp only [hk_us]
  rw [getElem!_pos (a.val) k (by rw [a.property]; exact hk)]

/-- Sign-extending an `i32` to `i64` is always in-bounds; the `.val` is preserved
    (copy of `HacspecBridge.cast_i64_ok`). -/
private theorem cast_i64_ok (z : Std.I32) :
    ∃ w : Std.I64, Aeneas.Std.lift (Aeneas.Std.IScalar.cast .I64 z) = .ok w ∧ w.val = z.val := by
  have hb : Aeneas.Std.IScalar.min .I64 ≤ z.val ∧ z.val ≤ Aeneas.Std.IScalar.max .I64 := by
    have h1 := Aeneas.Std.IScalar.hBounds z
    simp only [IScalar.min_IScalarTy_I64_eq, IScalar.max_IScalarTy_I64_eq, Aeneas.Std.I64.min,
      Aeneas.Std.I64.max, Aeneas.Std.I64.numBits, IScalarTy.I64_numBits_eq,
      IScalarTy.I32_numBits_eq] at *
    omega
  obtain ⟨w, hweq, hwval⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.cast_inBounds_spec .I64 z hb)
  exact ⟨w, hweq, hwval⟩

/-- Canonical uniqueness (copy of `HacspecBridge.canonI32_eq_of_canonical`). -/
private theorem canonI32_eq_of_canonical (r : Std.I32) (z : Zq)
    (hlo : 0 ≤ r.val) (hhi : r.val < (Q : Int)) (hres : ((r.val : Int) : Zq) = z) :
    r = canonI32 z := by
  apply Aeneas.Std.IScalar.eq_of_val_eq
  rw [canonI32_val]
  have hz : z = ((r.val.toNat : Nat) : Zq) := by
    rw [← hres]
    have e : ((r.val.toNat : Nat) : Int) = r.val := Int.toNat_of_nonneg hlo
    rw [← e]; push_cast; rfl
  have hrt : r.val.toNat < Q := by
    have : r.val.toNat < (Q : Int).toNat := by
      rw [Int.toNat_lt_toNat (by norm_num [Q])]; exact hhi
    simpa [Q] using this
  have hzv : z.val = r.val.toNat := by rw [hz]; exact ZMod.val_natCast_of_lt hrt
  rw [hzv]; exact (Int.toNat_of_nonneg hlo).symm

/-- Cell-canonicality of a `createi` result whose index fn is `canonI32 ∘ g`
    (copy of `HacspecBridge.map_canonI32_canonical`). -/
private theorem map_canonI32_canonical (g : Nat → Zq) (i : Nat) (hi : i < 256) :
    0 ≤ ((⟨(List.range 256).map (fun k => canonI32 (g k)), by
            simp [List.length_map, List.length_range]⟩
          : Aeneas.Std.Array Std.I32 256#usize).val[i]!).val
      ∧ ((⟨(List.range 256).map (fun k => canonI32 (g k)), by
            simp [List.length_map, List.length_range]⟩
          : Aeneas.Std.Array Std.I32 256#usize).val[i]!).val < (Q : Int) := by
  have hmap : ((List.range 256).map (fun k => canonI32 (g k)))[i]! = canonI32 (g i) := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl
  show 0 ≤ (((List.range 256).map (fun k => canonI32 (g k)))[i]!).val
    ∧ (((List.range 256).map (fun k => canonI32 (g k)))[i]!).val < (Q : Int)
  rw [hmap]
  exact canonI32_canonical (g i)

/-- An i32 cast to i64 stays within `[-(2^31), 2^31)`. -/
private theorem i32_i64_bound (z : Std.I32) (w : Std.I64) (hw : w.val = z.val) :
    -2 ^ 31 ≤ w.val ∧ w.val < 2 ^ 31 := by
  have h := Aeneas.Std.IScalar.hBounds z
  simp only [IScalarTy.I32_numBits_eq] at h
  rw [hw]; omega

/-- The product of two i64s, each holding an i32 value, fits in i64. -/
private theorem i64_mul_ok (a b : Std.I64) (za zb : Std.I32)
    (ha : a.val = za.val) (hb : b.val = zb.val) :
    ∃ s : Std.I64, (a * b : Result Std.I64) = .ok s ∧ s.val = a.val * b.val := by
  obtain ⟨ha1, ha2⟩ := i32_i64_bound za a ha
  obtain ⟨hb1, hb2⟩ := i32_i64_bound zb b hb
  have hlo : (-4611686018427387904 : Int) ≤ a.val * b.val := by nlinarith
  have hhi : a.val * b.val ≤ (4611686018427387904 : Int) := by nlinarith
  have hmin : Aeneas.Std.IScalar.min .I64 ≤ a.val * b.val := by
    simp only [IScalar.min_IScalarTy_I64_eq, Aeneas.Std.I64.min, Aeneas.Std.I64.numBits,
      IScalarTy.I64_numBits_eq]; norm_num; omega
  have hmax : a.val * b.val ≤ Aeneas.Std.IScalar.max .I64 := by
    simp only [IScalar.max_IScalarTy_I64_eq, Aeneas.Std.I64.max, Aeneas.Std.I64.numBits,
      IScalarTy.I64_numBits_eq]; norm_num; omega
  obtain ⟨s, hs_eq, hs_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.mul_spec (x := a) (y := b) hmin hmax)
  exact ⟨s, hs_eq, hs_val⟩

/-- The sum of an i64 holding an i32 value and an i64 holding a `[0,Q)` value fits. -/
private theorem i64_add_canon_ok (a b : Std.I64) (za : Std.I32)
    (ha : a.val = za.val) (hb0 : 0 ≤ b.val) (hbQ : b.val < (Q : Int)) :
    ∃ s : Std.I64, (a + b : Result Std.I64) = .ok s ∧ s.val = a.val + b.val := by
  obtain ⟨ha1, ha2⟩ := i32_i64_bound za a ha
  have hQ : (Q : Int) = 8380417 := by norm_num [Q]
  rw [hQ] at hbQ
  have hmin : Aeneas.Std.IScalar.min .I64 ≤ a.val + b.val := by
    simp only [IScalar.min_IScalarTy_I64_eq, Aeneas.Std.I64.min, Aeneas.Std.I64.numBits,
      IScalarTy.I64_numBits_eq]; norm_num; omega
  have hmax : a.val + b.val ≤ Aeneas.Std.IScalar.max .I64 := by
    simp only [IScalar.max_IScalarTy_I64_eq, Aeneas.Std.I64.max, Aeneas.Std.I64.numBits,
      IScalarTy.I64_numBits_eq]; norm_num; omega
  obtain ⟨s, hs_eq, hs_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.add_spec (x := a) (y := b) hmin hmax)
  exact ⟨s, hs_eq, hs_val⟩

/-- The difference of an i64 holding an i32 value and an i64 holding a `[0,Q)` value fits. -/
private theorem i64_sub_canon_ok (a b : Std.I64) (za : Std.I32)
    (ha : a.val = za.val) (hb0 : 0 ≤ b.val) (hbQ : b.val < (Q : Int)) :
    ∃ s : Std.I64, (a - b : Result Std.I64) = .ok s ∧ s.val = a.val - b.val := by
  obtain ⟨ha1, ha2⟩ := i32_i64_bound za a ha
  have hQ : (Q : Int) = 8380417 := by norm_num [Q]
  rw [hQ] at hbQ
  have hmin : Aeneas.Std.IScalar.min .I64 ≤ a.val - b.val := by
    simp only [IScalar.min_IScalarTy_I64_eq, Aeneas.Std.I64.min, Aeneas.Std.I64.numBits,
      IScalarTy.I64_numBits_eq]; norm_num; omega
  have hmax : a.val - b.val ≤ Aeneas.Std.IScalar.max .I64 := by
    simp only [IScalar.max_IScalarTy_I64_eq, Aeneas.Std.I64.max, Aeneas.Std.I64.numBits,
      IScalarTy.I64_numBits_eq]; norm_num; omega
  obtain ⟨s, hs_eq, hs_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.sub_spec (x := a) (y := b) hmin hmax)
  exact ⟨s, hs_eq, hs_val⟩

/-- The sum of two i64s, each holding a `[0,Q)` value, fits in i64. -/
private theorem i64_add_two_canon_ok (a b : Std.I64)
    (ha0 : 0 ≤ a.val) (haQ : a.val < (Q : Int)) (hb0 : 0 ≤ b.val) (hbQ : b.val < (Q : Int)) :
    ∃ s : Std.I64, (a + b : Result Std.I64) = .ok s ∧ s.val = a.val + b.val := by
  have hQ : (Q : Int) = 8380417 := by norm_num [Q]
  rw [hQ] at haQ hbQ
  have hmin : Aeneas.Std.IScalar.min .I64 ≤ a.val + b.val := by
    simp only [IScalar.min_IScalarTy_I64_eq, Aeneas.Std.I64.min, Aeneas.Std.I64.numBits,
      IScalarTy.I64_numBits_eq]; norm_num; omega
  have hmax : a.val + b.val ≤ Aeneas.Std.IScalar.max .I64 := by
    simp only [IScalar.max_IScalarTy_I64_eq, Aeneas.Std.I64.max, Aeneas.Std.I64.numBits,
      IScalarTy.I64_numBits_eq]; norm_num; omega
  obtain ⟨s, hs_eq, hs_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.add_spec (x := a) (y := b) hmin hmax)
  exact ⟨s, hs_eq, hs_val⟩

/-- The sum of two i64s, each holding an i32 value, fits in i64. -/
private theorem i64_add_i32_ok (a b : Std.I64) (za zb : Std.I32)
    (ha : a.val = za.val) (hb : b.val = zb.val) :
    ∃ s : Std.I64, (a + b : Result Std.I64) = .ok s ∧ s.val = a.val + b.val := by
  obtain ⟨ha1, ha2⟩ := i32_i64_bound za a ha
  obtain ⟨hb1, hb2⟩ := i32_i64_bound zb b hb
  have hmin : Aeneas.Std.IScalar.min .I64 ≤ a.val + b.val := by
    simp only [IScalar.min_IScalarTy_I64_eq, Aeneas.Std.I64.min, Aeneas.Std.I64.numBits,
      IScalarTy.I64_numBits_eq]; norm_num; omega
  have hmax : a.val + b.val ≤ Aeneas.Std.IScalar.max .I64 := by
    simp only [IScalar.max_IScalarTy_I64_eq, Aeneas.Std.I64.max, Aeneas.Std.I64.numBits,
      IScalarTy.I64_numBits_eq]; norm_num; omega
  obtain ⟨s, hs_eq, hs_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.add_spec (x := a) (y := b) hmin hmax)
  exact ⟨s, hs_eq, hs_val⟩

/-- The difference of two i64s, each holding an i32 value, fits in i64. -/
private theorem i64_sub_i32_ok (a b : Std.I64) (za zb : Std.I32)
    (ha : a.val = za.val) (hb : b.val = zb.val) :
    ∃ s : Std.I64, (a - b : Result Std.I64) = .ok s ∧ s.val = a.val - b.val := by
  obtain ⟨ha1, ha2⟩ := i32_i64_bound za a ha
  obtain ⟨hb1, hb2⟩ := i32_i64_bound zb b hb
  have hmin : Aeneas.Std.IScalar.min .I64 ≤ a.val - b.val := by
    simp only [IScalar.min_IScalarTy_I64_eq, Aeneas.Std.I64.min, Aeneas.Std.I64.numBits,
      IScalarTy.I64_numBits_eq]; norm_num; omega
  have hmax : a.val - b.val ≤ Aeneas.Std.IScalar.max .I64 := by
    simp only [IScalar.max_IScalarTy_I64_eq, Aeneas.Std.I64.max, Aeneas.Std.I64.numBits,
      IScalarTy.I64_numBits_eq]; norm_num; omega
  obtain ⟨s, hs_eq, hs_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.sub_spec (x := a) (y := b) hmin hmax)
  exact ⟨s, hs_eq, hs_val⟩

/-- `parameters.Q` as an `i32` has value `8380417`. -/
private theorem paramQ_val : (hacspec_ml_dsa.parameters.Q).val = 8380417 := by
  unfold hacspec_ml_dsa.parameters.Q; decide

/-- i64 cast of `parameters.Q`: value matches the `i32` `parameters.Q`. -/
private theorem castQ_i64 :
    ∃ w : Std.I64, Aeneas.Std.lift (Aeneas.Std.IScalar.cast .I64 hacspec_ml_dsa.parameters.Q) = .ok w
      ∧ w.val = (hacspec_ml_dsa.parameters.Q).val := cast_i64_ok hacspec_ml_dsa.parameters.Q

/-- i64 `% Q`: succeeds, residue-preserving in `Z_q`, result in `(−Q, Q)`. -/
private theorem i64_rem_Q (a : Std.I64) (q : Std.I64) (hq : q.val = 8380417) :
    ∃ s : Std.I64, (a % q : Result Std.I64) = .ok s
      ∧ ((s.val : Int) : Zq) = ((a.val : Int) : Zq)
      ∧ -8380417 < s.val ∧ s.val < 8380417 := by
  have hqnz : q.val ≠ (0 : Int) := by rw [hq]; decide
  obtain ⟨s, hs_eq, hs_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.rem_spec a hqnz)
  refine ⟨s, hs_eq, ?_, ?_, ?_⟩
  · rw [hs_val, hq]
    show ((a.val.tmod (8380417 : Int) : Int) : Zq) = ((a.val : Int) : Zq)
    rw [Int.tmod_def]; push_cast; ring_nf
  · rw [hs_val, hq]
    have := Int.natAbs_tmod a.val 8380417
    have h2 : (a.val.tmod 8380417).natAbs < 8380417 := by
      rw [this]; exact Nat.mod_lt _ (by decide)
    omega
  · rw [hs_val, hq]
    have h2 : (a.val.tmod 8380417).natAbs < 8380417 := by
      rw [Int.natAbs_tmod]; exact Nat.mod_lt _ (by decide)
    omega

/-- The product of an i64 holding a `(−Q,Q)` value and an i64 holding the difference of
    two i32 values fits in i64. -/
private theorem i64_mul_canon_diff_ok (a b : Std.I64) (zb1 zb2 : Std.I32)
    (ha0 : -8380417 < a.val) (haQ : a.val < 8380417) (hb : b.val = zb1.val - zb2.val) :
    ∃ s : Std.I64, (a * b : Result Std.I64) = .ok s ∧ s.val = a.val * b.val := by
  obtain ⟨hb1lo, hb1hi⟩ := Aeneas.Std.IScalar.hBounds zb1
  obtain ⟨hb2lo, hb2hi⟩ := Aeneas.Std.IScalar.hBounds zb2
  simp only [IScalarTy.I32_numBits_eq] at hb1lo hb1hi hb2lo hb2hi
  have hblo : (-4294967296 : Int) ≤ b.val := by rw [hb]; omega
  have hbhi : b.val ≤ (4294967296 : Int) := by rw [hb]; omega
  have hlo : (-4611686018427387904 : Int) ≤ a.val * b.val := by nlinarith
  have hhi : a.val * b.val ≤ (4611686018427387904 : Int) := by nlinarith
  have hmin : Aeneas.Std.IScalar.min .I64 ≤ a.val * b.val := by
    simp only [IScalar.min_IScalarTy_I64_eq, Aeneas.Std.I64.min, Aeneas.Std.I64.numBits,
      IScalarTy.I64_numBits_eq]; norm_num; omega
  have hmax : a.val * b.val ≤ Aeneas.Std.IScalar.max .I64 := by
    simp only [IScalar.max_IScalarTy_I64_eq, Aeneas.Std.I64.max, Aeneas.Std.I64.numBits,
      IScalarTy.I64_numBits_eq]; norm_num; omega
  obtain ⟨s, hs_eq, hs_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.mul_spec (x := a) (y := b) hmin hmax)
  exact ⟨s, hs_eq, hs_val⟩

/-! ## (1a) The forward-NTT one-layer bridge. -/

set_option maxHeartbeats 16000000 in
/-- **Forward-NTT one-layer bridge.** One extracted `createi`-layer of `ntt_layer`
    equals (under `lift_res`) one `Pure.ntt_layer` step, with a canonical (`[0,Q)`)
    result. The `createi`-per-layer pattern from `HacspecBridge.poly_add_bridge`. -/
theorem ntt_layer_bridge (p : Aeneas.Std.Array Std.I32 256#usize) (layer : Nat) (hl : layer ≤ 7) :
    ∃ r, hacspec_ml_dsa.ntt.ntt_layer p ⟨BitVec.ofNat _ layer⟩ = .ok r
      ∧ lift_res r = Pure.ntt_layer (lift_res p) layer
      ∧ (∀ i, i < 256 → 0 ≤ r.val[i]!.val ∧ r.val[i]!.val < (Q : Int)) := by
  -- Resolve `len = 1 <<< layer = 2^layer` and `k = 128 / 2^layer`.
  have hlayer_val : (⟨BitVec.ofNat _ layer⟩ : Std.Usize).val = layer := usize_val layer (by omega)
  obtain ⟨len_z, hlen_eq, hlen_val⟩ :=
    usize_shl 1#usize ⟨BitVec.ofNat _ layer⟩ layer (by decide) hlayer_val (by omega)
  have hlen_pos : (0 : Nat) < 2 ^ layer := Nat.two_pow_pos layer
  have hlen_le : (2 : Nat) ^ layer ≤ 128 := by
    calc (2:Nat) ^ layer ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) hl
      _ = 128 := by decide
  -- `2 * 2^layer` divides `256` (it equals `2^(layer+1) ∣ 2^8`), used for block bounds.
  have hdvd : (2 * 2 ^ layer) ∣ 256 := by
    have : (2 : Nat) * 2 ^ layer = 2 ^ (layer + 1) := by rw [pow_succ]; ring
    rw [this, show (256 : Nat) = 2 ^ 8 from by decide]
    exact pow_dvd_pow 2 (by omega)
  obtain ⟨k_z, hk_eq, hk_val⟩ :=
    usize_div 128#usize len_z 128 (2 ^ layer) (by decide) hlen_val (by omega)
  -- The per-lane index fn.
  set f : Nat → Std.I32 :=
    fun i => canonI32 ((Pure.ntt_layer (lift_res p) layer)[i]!) with hf_def
  -- The per-call obligation.
  have hpure : ∀ i : Nat, i < (256#usize : Std.Usize).val →
      (hacspec_ml_dsa.ntt.ntt_layer.closure.Insts.CoreOpsFunctionFnTupleUsizeI32
        : CoreModels.core.ops.function.Fn _ _ _).FnMutInst.call_mut
          (p, len_z, k_z) ⟨BitVec.ofNat _ i⟩ = .ok (f i, (p, len_z, k_z)) := by
    intro i hi
    have hi' : i < 256 := hi
    -- The pure spec cell.
    have hpure_cell : (Pure.ntt_layer (lift_res p) layer)[i]!
        = (let round := i / (2 * 2 ^ layer);
           let idx := i % (2 * 2 ^ layer);
           let z := zeta (round + 128 / 2 ^ layer);
           if idx < 2 ^ layer then (lift_res p)[i]! + z * (lift_res p)[i + 2 ^ layer]!
           else (lift_res p)[i - 2 ^ layer]! - z * (lift_res p)[i]!) := by
      unfold Pure.ntt_layer
      rw [Pure.build_getElem _ i hi']
      simp only [Nat.shiftLeft_eq, one_mul]
    -- Usize: `2*len`, `round = i/(2*len)`, `idx = i%(2*len)`, `round+k`.
    obtain ⟨tl_z, htl_eq, htl_val⟩ :=
      usize_mul 2#usize len_z 2 (2 ^ layer) (by decide) hlen_val (by omega)
    obtain ⟨round_z, hround_eq, hround_val⟩ :=
      usize_div ⟨BitVec.ofNat _ i⟩ tl_z i (2 * 2 ^ layer)
        (usize_val i (by omega)) htl_val (by have := hlen_pos; omega)
    obtain ⟨idx_z, hidx_eq, hidx_val⟩ :=
      usize_rem ⟨BitVec.ofNat _ i⟩ tl_z i (2 * 2 ^ layer)
        (usize_val i (by omega)) htl_val (by have := hlen_pos; omega)
    -- `round = i / (2 * 2^layer) ≤ i / 2 < 128`, `k = 128 / 2^layer ≤ 128`, so `round+k < 256`.
    have hround_lt : i / (2 * 2 ^ layer) < 128 := by
      have h2 : 2 * 2 ^ layer ≥ 2 := by have := hlen_pos; omega
      calc i / (2 * 2 ^ layer) ≤ i / 2 := Nat.div_le_div_left h2 (by decide)
        _ < 128 := by omega
    have hk_lt : (128 : Nat) / 2 ^ layer ≤ 128 := Nat.div_le_self 128 _
    obtain ⟨rk_z, hrk_eq, hrk_val⟩ :=
      usize_add round_z k_z (i / (2 * 2 ^ layer)) (128 / 2 ^ layer)
        hround_val hk_val (by omega)
    have hrk_lt : i / (2 * 2 ^ layer) + 128 / 2 ^ layer < 256 := by omega
    -- `ZETAS[round+k]` then cast to i64; its residue is `zeta (round+k)`.
    have hzidx :
        Aeneas.Std.Array.index_usize hacspec_ml_dsa.ntt.ZETAS rk_z
          = .ok (hacspec_ml_dsa.ntt.ZETAS.val[i / (2 * 2 ^ layer) + 128 / 2 ^ layer]!) := by
      have hrk_align : rk_z = (⟨BitVec.ofNat _ (i / (2 * 2 ^ layer) + 128 / 2 ^ layer)⟩ : Std.Usize) := by
        apply Aeneas.Std.UScalar.eq_of_val_eq
        rw [hrk_val, usize_val _ (by omega)]
      rw [hrk_align]
      exact idx_ok hacspec_ml_dsa.ntt.ZETAS (i / (2 * 2 ^ layer) + 128 / 2 ^ layer) hrk_lt
    obtain ⟨wz, hwz_eq, hwz_val⟩ :=
      cast_i64_ok (hacspec_ml_dsa.ntt.ZETAS.val[i / (2 * 2 ^ layer) + 128 / 2 ^ layer]!)
    have hwz_res : ((wz.val : Int) : Zq) = zeta (i / (2 * 2 ^ layer) + 128 / 2 ^ layer) := by
      rw [hwz_val]
      exact zetas_bridge _ hrk_lt
    -- The `idx < len` boolean splits exactly as the pure spec's `i % (2*2^layer) < 2^layer`.
    have hcond : (idx_z < len_z) ↔ (i % (2 * 2 ^ layer) < 2 ^ layer) := by
      rw [Aeneas.Std.UScalar.lt_equiv, hidx_val, hlen_val]
    -- Reduce the closure to `ntt_layer_coeff` and thread the do-block.
    show hacspec_ml_dsa.ntt.ntt_layer.closure.Insts.CoreOpsFunctionFnMutTupleUsizeI32.call_mut
        (p, len_z, k_z) ⟨BitVec.ofNat _ i⟩ = .ok (f i, (p, len_z, k_z))
    unfold hacspec_ml_dsa.ntt.ntt_layer.closure.Insts.CoreOpsFunctionFnMutTupleUsizeI32.call_mut
    unfold hacspec_ml_dsa.ntt.ntt_layer.closure.Insts.CoreOpsFunctionFnTupleUsizeI32.call
    change (do
        let v ← hacspec_ml_dsa.ntt.ntt_layer_coeff p len_z k_z ⟨BitVec.ofNat _ i⟩
        Result.ok (v, (p, len_z, k_z))) = .ok (f i, (p, len_z, k_z))
    unfold hacspec_ml_dsa.ntt.ntt_layer_coeff
    rw [htl_eq]; simp only [bind_tc_ok]
    rw [hround_eq]; simp only [bind_tc_ok]
    rw [hidx_eq]; simp only [bind_tc_ok]
    rw [hrk_eq]; simp only [bind_tc_ok]
    rw [hzidx]; simp only [bind_tc_ok]
    rw [hwz_eq]; simp only [bind_tc_ok]
    by_cases hlt : idx_z < len_z
    · rw [if_pos hlt]
      -- idx < len branch: `mod_q (z * p[i+len])` then `mod_q (p[i] + that)`.
      have hilen_lt : i + 2 ^ layer < 256 := by
        have hmod := (hcond.mp hlt)
        have hdm : i = (2 * 2 ^ layer) * (i / (2 * 2 ^ layer)) + i % (2 * 2 ^ layer) :=
          (Nat.div_add_mod i (2 * 2 ^ layer)).symm
        obtain ⟨c, hc⟩ := hdvd
        have hround_bnd : i / (2 * 2 ^ layer) + 1 ≤ c := by
          by_contra hcon
          have : c ≤ i / (2 * 2 ^ layer) := by omega
          have : 256 ≤ (2 * 2 ^ layer) * (i / (2 * 2 ^ layer)) := by
            rw [hc]; exact Nat.mul_le_mul_left _ this
          omega
        have : (2 * 2 ^ layer) * (i / (2 * 2 ^ layer) + 1) ≤ 256 := by
          rw [hc]; exact Nat.mul_le_mul_left _ hround_bnd
        rw [Nat.mul_add, Nat.mul_one] at this
        omega
      obtain ⟨iadd_z, hiadd_eq, hiadd_val⟩ :=
        usize_add ⟨BitVec.ofNat _ i⟩ len_z i (2 ^ layer) (usize_val i (by omega)) hlen_val (by omega)
      rw [hiadd_eq]; simp only [bind_tc_ok]
      have hiadd_idx : Aeneas.Std.Array.index_usize p iadd_z = .ok (p.val[i + 2 ^ layer]!) := by
        have : iadd_z = (⟨BitVec.ofNat _ (i + 2 ^ layer)⟩ : Std.Usize) := by
          apply Aeneas.Std.UScalar.eq_of_val_eq
          rw [hiadd_val, usize_val (i + 2 ^ layer) (by omega)]
        rw [this]; exact idx_ok p (i + 2 ^ layer) hilen_lt
      rw [hiadd_idx]; simp only [bind_tc_ok]
      obtain ⟨wpl, hwpl_eq, hwpl_val⟩ := cast_i64_ok (p.val[i + 2 ^ layer]!)
      rw [hwpl_eq]; simp only [bind_tc_ok]
      obtain ⟨prod, hprod_eq, hprod_val⟩ := i64_mul_ok wz wpl _ _ hwz_val hwpl_val
      rw [hprod_eq]; simp only [bind_tc_ok]
      obtain ⟨t, ht_eq, ht_res, ht_lo, ht_hi⟩ := mod_q_eq prod
      rw [ht_eq]; simp only [bind_tc_ok]
      rw [idx_ok p i hi']; simp only [bind_tc_ok]
      obtain ⟨wpi, hwpi_eq, hwpi_val⟩ := cast_i64_ok (p.val[i]!)
      rw [hwpi_eq]; simp only [bind_tc_ok]
      obtain ⟨wt, hwt_eq, hwt_val⟩ := cast_i64_ok t
      rw [hwt_eq]; simp only [bind_tc_ok]
      obtain ⟨ssum, hssum_eq, hssum_val⟩ :=
        i64_add_canon_ok wpi wt _ hwpi_val (by rw [hwt_val]; exact ht_lo) (by rw [hwt_val]; exact ht_hi)
      rw [hssum_eq]; simp only [bind_tc_ok]
      obtain ⟨out, hout_eq, hout_res, hout_lo, hout_hi⟩ := mod_q_eq ssum
      rw [hout_eq]
      -- `out = f i`.
      have ht_zq : ((t.val : Int) : Zq)
          = zeta (i / (2 * 2 ^ layer) + 128 / 2 ^ layer) * (lift_res p)[i + 2 ^ layer]! := by
        rw [ht_res, hprod_val]
        push_cast
        rw [hwz_res, hwpl_val, lift_res_getElem p (i + 2 ^ layer) hilen_lt]
      have hout_fi : out = f i := by
        rw [hf_def]
        apply canonI32_eq_of_canonical out _ hout_lo hout_hi
        rw [hpure_cell]
        simp only [hcond.mp hlt, if_true]
        rw [hout_res, hssum_val]
        push_cast
        rw [hwpi_val, hwt_val, ht_zq, ← lift_res_getElem p i hi']
      rw [hout_fi]; simp only [bind_tc_ok]
    · rw [if_neg hlt]
      -- idx ≥ len branch: `mod_q (z * p[i])` then `mod_q (p[i-len] - that)`.
      have hge : ¬ (i % (2 * 2 ^ layer) < 2 ^ layer) := fun h => hlt (hcond.mpr h)
      have hidx_ge : 2 ^ layer ≤ i % (2 * 2 ^ layer) := by omega
      have hilen_ge : 2 ^ layer ≤ i := by
        have hmod : i % (2 * 2 ^ layer) ≤ i := Nat.mod_le _ _
        omega
      have hilen_lt : i - 2 ^ layer < 256 := by omega
      rw [idx_ok p i hi']; simp only [bind_tc_ok]
      obtain ⟨wpi, hwpi_eq, hwpi_val⟩ := cast_i64_ok (p.val[i]!)
      rw [hwpi_eq]; simp only [bind_tc_ok]
      obtain ⟨prod, hprod_eq, hprod_val⟩ := i64_mul_ok wz wpi _ _ hwz_val hwpi_val
      rw [hprod_eq]; simp only [bind_tc_ok]
      obtain ⟨t, ht_eq, ht_res, ht_lo, ht_hi⟩ := mod_q_eq prod
      rw [ht_eq]; simp only [bind_tc_ok]
      obtain ⟨isub_z, hisub_eq, hisub_val⟩ :=
        usize_sub ⟨BitVec.ofNat _ i⟩ len_z i (2 ^ layer) (usize_val i (by omega)) hlen_val hilen_ge
      rw [hisub_eq]; simp only [bind_tc_ok]
      -- `Array.index_usize p (i - len)`: align `isub_z` with `⟨BitVec.ofNat _ (i - 2^layer)⟩`.
      have hisub_idx : Aeneas.Std.Array.index_usize p isub_z = .ok (p.val[i - 2 ^ layer]!) := by
        have : isub_z = (⟨BitVec.ofNat _ (i - 2 ^ layer)⟩ : Std.Usize) := by
          apply Aeneas.Std.UScalar.eq_of_val_eq
          rw [hisub_val, usize_val (i - 2 ^ layer) (by omega)]
        rw [this]; exact idx_ok p (i - 2 ^ layer) hilen_lt
      rw [hisub_idx]; simp only [bind_tc_ok]
      obtain ⟨wpm, hwpm_eq, hwpm_val⟩ := cast_i64_ok (p.val[i - 2 ^ layer]!)
      rw [hwpm_eq]; simp only [bind_tc_ok]
      obtain ⟨wt, hwt_eq, hwt_val⟩ := cast_i64_ok t
      rw [hwt_eq]; simp only [bind_tc_ok]
      obtain ⟨ssub, hssub_eq, hssub_val⟩ :=
        i64_sub_canon_ok wpm wt _ hwpm_val (by rw [hwt_val]; exact ht_lo) (by rw [hwt_val]; exact ht_hi)
      rw [hssub_eq]; simp only [bind_tc_ok]
      obtain ⟨out, hout_eq, hout_res, hout_lo, hout_hi⟩ := mod_q_eq ssub
      rw [hout_eq]
      have ht_zq : ((t.val : Int) : Zq)
          = zeta (i / (2 * 2 ^ layer) + 128 / 2 ^ layer) * (lift_res p)[i]! := by
        rw [ht_res, hprod_val]
        push_cast
        rw [hwz_res, hwpi_val, lift_res_getElem p i hi']
      have hout_fi : out = f i := by
        rw [hf_def]
        apply canonI32_eq_of_canonical out _ hout_lo hout_hi
        rw [hpure_cell]
        simp only [hge, if_false]
        rw [hout_res, hssub_val]
        push_cast
        rw [hwpm_val, hwt_val, ht_zq, ← lift_res_getElem p (i - 2 ^ layer) hilen_lt]
      rw [hout_fi]; simp only [bind_tc_ok]
  -- Assemble: `createi_pure_eq` then the two conjuncts.
  have heq := createi_pure_eq (T := Std.I32)
    (F := hacspec_ml_dsa.ntt.ntt_layer.closure)
    256#usize
    hacspec_ml_dsa.ntt.ntt_layer.closure.Insts.CoreOpsFunctionFnTupleUsizeI32
    (p, len_z, k_z) f hpure
  have heq' : hacspec_ml_dsa.ntt.ntt_layer p ⟨BitVec.ofNat _ layer⟩
      = .ok ⟨(List.range (256#usize : Std.Usize).val).map f,
             by simp [List.length_map, List.length_range]⟩ := by
    unfold hacspec_ml_dsa.ntt.ntt_layer
    rw [hlen_eq]; simp only [bind_tc_ok]
    rw [hk_eq]; simp only [bind_tc_ok]
    exact heq
  refine ⟨_, heq', ?_, ?_⟩
  · conv_lhs => unfold lift_res
    apply Pure.build_congr
    intro i hi
    show (((⟨(List.range 256).map f, _⟩ : Aeneas.Std.Array Std.I32 256#usize).val[i]!).val : Zq) = _
    have hmap : ((List.range 256).map f)[i]! = f i := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl
    rw [hmap, hf_def, canonI32_lift]
    conv_lhs => unfold Pure.ntt_layer; rw [Pure.build_getElem _ i hi]
  · intro i hi
    exact map_canonI32_canonical (fun i => (Pure.ntt_layer (lift_res p) layer)[i]!) i hi

/-! ## (1b) The inverse-NTT one-layer bridge. -/

set_option maxHeartbeats 16000000 in
/-- **Inverse-NTT one-layer bridge.** One extracted `createi`-layer of `intt_layer`
    equals (under `lift_res`) one `Pure.intt_layer` step, canonical result. The odd
    half's `z = (Q − ZETAS[k−round]) % Q` reconciles to `−zeta (k−round)` in `Z_q`. -/
theorem intt_layer_bridge (p : Aeneas.Std.Array Std.I32 256#usize) (layer : Nat) (hl : layer ≤ 7) :
    ∃ r, hacspec_ml_dsa.ntt.intt_layer p ⟨BitVec.ofNat _ layer⟩ = .ok r
      ∧ lift_res r = Pure.intt_layer (lift_res p) layer
      ∧ (∀ i, i < 256 → 0 ≤ r.val[i]!.val ∧ r.val[i]!.val < (Q : Int)) := by
  -- `len = 2^layer`, `i' = 256/len`, `k = i' - 1`.
  have hlayer_val : (⟨BitVec.ofNat _ layer⟩ : Std.Usize).val = layer := usize_val layer (by omega)
  obtain ⟨len_z, hlen_eq, hlen_val⟩ :=
    usize_shl 1#usize ⟨BitVec.ofNat _ layer⟩ layer (by decide) hlayer_val (by omega)
  have hlen_pos : (0 : Nat) < 2 ^ layer := Nat.two_pow_pos layer
  have hlen_le : (2 : Nat) ^ layer ≤ 128 := by
    calc (2:Nat) ^ layer ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) hl
      _ = 128 := by decide
  have hdvd : (2 * 2 ^ layer) ∣ 256 := by
    have : (2 : Nat) * 2 ^ layer = 2 ^ (layer + 1) := by rw [pow_succ]; ring
    rw [this, show (256 : Nat) = 2 ^ 8 from by decide]
    exact pow_dvd_pow 2 (by omega)
  obtain ⟨i_z, hi_eq, hi_val⟩ :=
    usize_div 256#usize len_z 256 (2 ^ layer) (by decide) hlen_val (by omega)
  -- `256/2^layer ≥ 2` (since `2^layer ≤ 128`), so `k = 256/2^layer - 1 ≥ 1`.
  have hidiv_ge : (2 : Nat) ≤ 256 / 2 ^ layer := by
    rw [Nat.le_div_iff_mul_le hlen_pos]
    calc 2 * 2 ^ layer = 2 ^ (layer + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 256 := by decide
  obtain ⟨k_z, hk_eq, hk_val⟩ :=
    usize_sub i_z 1#usize (256 / 2 ^ layer) 1 hi_val (by decide) (by omega)
  set f : Nat → Std.I32 :=
    fun i => canonI32 ((Pure.intt_layer (lift_res p) layer)[i]!) with hf_def
  have hpure : ∀ i : Nat, i < (256#usize : Std.Usize).val →
      (hacspec_ml_dsa.ntt.intt_layer.closure.Insts.CoreOpsFunctionFnTupleUsizeI32
        : CoreModels.core.ops.function.Fn _ _ _).FnMutInst.call_mut
          (p, len_z, k_z) ⟨BitVec.ofNat _ i⟩ = .ok (f i, (p, len_z, k_z)) := by
    intro i hi
    have hi' : i < 256 := hi
    have hpure_cell : (Pure.intt_layer (lift_res p) layer)[i]!
        = (let round := i / (2 * 2 ^ layer);
           let idx := i % (2 * 2 ^ layer);
           if idx < 2 ^ layer then (lift_res p)[i]! + (lift_res p)[i + 2 ^ layer]!
           else (- zeta ((256 / 2 ^ layer - 1) - round)) * ((lift_res p)[i - 2 ^ layer]! - (lift_res p)[i]!)) := by
      unfold Pure.intt_layer
      rw [Pure.build_getElem _ i hi']
      simp only [Nat.shiftLeft_eq, one_mul]
    obtain ⟨tl_z, htl_eq, htl_val⟩ :=
      usize_mul 2#usize len_z 2 (2 ^ layer) (by decide) hlen_val (by omega)
    obtain ⟨round_z, hround_eq, hround_val⟩ :=
      usize_div ⟨BitVec.ofNat _ i⟩ tl_z i (2 * 2 ^ layer)
        (usize_val i (by omega)) htl_val (by have := hlen_pos; omega)
    obtain ⟨idx_z, hidx_eq, hidx_val⟩ :=
      usize_rem ⟨BitVec.ofNat _ i⟩ tl_z i (2 * 2 ^ layer)
        (usize_val i (by omega)) htl_val (by have := hlen_pos; omega)
    -- `round < 256/(2·len) = (256/len)/2 ≤ k = 256/len - 1`.
    have hround_lt : i / (2 * 2 ^ layer) < 256 / (2 * 2 ^ layer) :=
      Nat.div_lt_div_of_lt_of_dvd hdvd hi'
    have hdd : 256 / (2 * 2 ^ layer) = (256 / 2 ^ layer) / 2 := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
    have hround_le_k : i / (2 * 2 ^ layer) ≤ 256 / 2 ^ layer - 1 := by
      rw [hdd] at hround_lt
      have hhalf : (256 / 2 ^ layer) / 2 ≤ 256 / 2 ^ layer := Nat.div_le_self _ _
      omega
    have hcond : (idx_z < len_z) ↔ (i % (2 * 2 ^ layer) < 2 ^ layer) := by
      rw [Aeneas.Std.UScalar.lt_equiv, hidx_val, hlen_val]
    show hacspec_ml_dsa.ntt.intt_layer.closure.Insts.CoreOpsFunctionFnMutTupleUsizeI32.call_mut
        (p, len_z, k_z) ⟨BitVec.ofNat _ i⟩ = .ok (f i, (p, len_z, k_z))
    unfold hacspec_ml_dsa.ntt.intt_layer.closure.Insts.CoreOpsFunctionFnMutTupleUsizeI32.call_mut
    unfold hacspec_ml_dsa.ntt.intt_layer.closure.Insts.CoreOpsFunctionFnTupleUsizeI32.call
    change (do
        let v ← hacspec_ml_dsa.ntt.intt_layer_coeff p len_z k_z ⟨BitVec.ofNat _ i⟩
        Result.ok (v, (p, len_z, k_z))) = .ok (f i, (p, len_z, k_z))
    unfold hacspec_ml_dsa.ntt.intt_layer_coeff
    rw [htl_eq]; simp only [bind_tc_ok]
    rw [hround_eq]; simp only [bind_tc_ok]
    rw [hidx_eq]; simp only [bind_tc_ok]
    by_cases hlt : idx_z < len_z
    · rw [if_pos hlt]
      -- idx < len: `mod_q (p[i] + p[i+len])`.
      have hilen_lt : i + 2 ^ layer < 256 := by
        have hmod := (hcond.mp hlt)
        have hdm : i = (2 * 2 ^ layer) * (i / (2 * 2 ^ layer)) + i % (2 * 2 ^ layer) :=
          (Nat.div_add_mod i (2 * 2 ^ layer)).symm
        obtain ⟨c, hc⟩ := hdvd
        have hround_bnd : i / (2 * 2 ^ layer) + 1 ≤ c := by
          by_contra hcon
          have : c ≤ i / (2 * 2 ^ layer) := by omega
          have : 256 ≤ (2 * 2 ^ layer) * (i / (2 * 2 ^ layer)) := by
            rw [hc]; exact Nat.mul_le_mul_left _ this
          omega
        have : (2 * 2 ^ layer) * (i / (2 * 2 ^ layer) + 1) ≤ 256 := by
          rw [hc]; exact Nat.mul_le_mul_left _ hround_bnd
        rw [Nat.mul_add, Nat.mul_one] at this
        omega
      rw [idx_ok p i hi']; simp only [bind_tc_ok]
      obtain ⟨wpi, hwpi_eq, hwpi_val⟩ := cast_i64_ok (p.val[i]!)
      rw [hwpi_eq]; simp only [bind_tc_ok]
      obtain ⟨iadd_z, hiadd_eq, hiadd_val⟩ :=
        usize_add ⟨BitVec.ofNat _ i⟩ len_z i (2 ^ layer) (usize_val i (by omega)) hlen_val (by omega)
      rw [hiadd_eq]; simp only [bind_tc_ok]
      have hiadd_idx : Aeneas.Std.Array.index_usize p iadd_z = .ok (p.val[i + 2 ^ layer]!) := by
        have : iadd_z = (⟨BitVec.ofNat _ (i + 2 ^ layer)⟩ : Std.Usize) := by
          apply Aeneas.Std.UScalar.eq_of_val_eq
          rw [hiadd_val, usize_val (i + 2 ^ layer) (by omega)]
        rw [this]; exact idx_ok p (i + 2 ^ layer) hilen_lt
      rw [hiadd_idx]; simp only [bind_tc_ok]
      obtain ⟨wpl, hwpl_eq, hwpl_val⟩ := cast_i64_ok (p.val[i + 2 ^ layer]!)
      rw [hwpl_eq]; simp only [bind_tc_ok]
      obtain ⟨ssum, hssum_eq, hssum_val⟩ := i64_add_i32_ok wpi wpl _ _ hwpi_val hwpl_val
      rw [hssum_eq]; simp only [bind_tc_ok]
      obtain ⟨out, hout_eq, hout_res, hout_lo, hout_hi⟩ := mod_q_eq ssum
      rw [hout_eq]
      have hout_fi : out = f i := by
        rw [hf_def]
        apply canonI32_eq_of_canonical out _ hout_lo hout_hi
        rw [hpure_cell]
        simp only [hcond.mp hlt, if_true]
        rw [hout_res, hssum_val]
        push_cast
        rw [hwpi_val, hwpl_val, ← lift_res_getElem p i hi',
          ← lift_res_getElem p (i + 2 ^ layer) hilen_lt]
      rw [hout_fi]; simp only [bind_tc_ok]
    · rw [if_neg hlt]
      -- idx ≥ len: `z = (Q - ZETAS[k-round]) % Q`, then `mod_q (z * (p[i-len] - p[i]))`.
      have hge : ¬ (i % (2 * 2 ^ layer) < 2 ^ layer) := fun h => hlt (hcond.mpr h)
      have hidx_ge : 2 ^ layer ≤ i % (2 * 2 ^ layer) := by omega
      have hilen_ge : 2 ^ layer ≤ i := by
        have hmod : i % (2 * 2 ^ layer) ≤ i := Nat.mod_le _ _
        omega
      have hilen_lt : i - 2 ^ layer < 256 := by omega
      -- `i2 ← cast Q`, `i3 ← k - round`, `i4 ← ZETAS[k-round]`, ...
      obtain ⟨wq1, hwq1_eq, hwq1_val⟩ := castQ_i64
      rw [hwq1_eq]; simp only [bind_tc_ok]
      obtain ⟨kr_z, hkr_eq, hkr_val⟩ :=
        usize_sub k_z round_z (256 / 2 ^ layer - 1) (i / (2 * 2 ^ layer)) hk_val hround_val
          hround_le_k
      rw [hkr_eq]; simp only [bind_tc_ok]
      have hkr_lt : 256 / 2 ^ layer - 1 - i / (2 * 2 ^ layer) < 256 := by
        have : 256 / 2 ^ layer ≤ 256 := Nat.div_le_self _ _
        omega
      have hzidx :
          Aeneas.Std.Array.index_usize hacspec_ml_dsa.ntt.ZETAS kr_z
            = .ok (hacspec_ml_dsa.ntt.ZETAS.val[256 / 2 ^ layer - 1 - i / (2 * 2 ^ layer)]!) := by
        have hkr_align : kr_z = (⟨BitVec.ofNat _ (256 / 2 ^ layer - 1 - i / (2 * 2 ^ layer))⟩ : Std.Usize) := by
          apply Aeneas.Std.UScalar.eq_of_val_eq
          rw [hkr_val, usize_val _ (by omega)]
        rw [hkr_align]
        exact idx_ok hacspec_ml_dsa.ntt.ZETAS (256 / 2 ^ layer - 1 - i / (2 * 2 ^ layer)) hkr_lt
      rw [hzidx]; simp only [bind_tc_ok]
      obtain ⟨wz, hwz_eq, hwz_val⟩ :=
        cast_i64_ok (hacspec_ml_dsa.ntt.ZETAS.val[256 / 2 ^ layer - 1 - i / (2 * 2 ^ layer)]!)
      rw [hwz_eq]; simp only [bind_tc_ok]
      -- `i6 = Q - ZETAS[k-round]`.
      obtain ⟨wsub, hwsub_eq, hwsub_val⟩ :=
        i64_sub_i32_ok wq1 wz hacspec_ml_dsa.parameters.Q _ hwq1_val hwz_val
      rw [hwsub_eq]; simp only [bind_tc_ok]
      -- `z = i6 % Q` (the divisor is the same `wq1` Q-cast, CSE'd by aeneas).
      obtain ⟨zz, hzz_eq, hzz_res, hzz_lo, hzz_hi⟩ := i64_rem_Q wsub wq1 (hwq1_val.trans paramQ_val)
      rw [hzz_eq]; simp only [bind_tc_ok]
      have hz_zq : ((zz.val : Int) : Zq) = - zeta (256 / 2 ^ layer - 1 - i / (2 * 2 ^ layer)) := by
        rw [hzz_res, hwsub_val, hwq1_val, hwz_val, paramQ_val]
        push_cast
        have hzeta := zetas_bridge (256 / 2 ^ layer - 1 - i / (2 * 2 ^ layer)) hkr_lt
        rw [hzeta]
        show ((8380417 : Int) : Zq) - _ = - _
        rw [show ((8380417 : Int) : Zq) = ((Q : Nat) : Zq) from by norm_num [Q]]
        rw [ZMod.natCast_self]
        ring
      -- `i8 = i - len`, index `p[i-len]`.
      obtain ⟨isub_z, hisub_eq, hisub_val⟩ :=
        usize_sub ⟨BitVec.ofNat _ i⟩ len_z i (2 ^ layer) (usize_val i (by omega)) hlen_val hilen_ge
      rw [hisub_eq]; simp only [bind_tc_ok]
      have hisub_idx : Aeneas.Std.Array.index_usize p isub_z = .ok (p.val[i - 2 ^ layer]!) := by
        have : isub_z = (⟨BitVec.ofNat _ (i - 2 ^ layer)⟩ : Std.Usize) := by
          apply Aeneas.Std.UScalar.eq_of_val_eq
          rw [hisub_val, usize_val (i - 2 ^ layer) (by omega)]
        rw [this]; exact idx_ok p (i - 2 ^ layer) hilen_lt
      rw [hisub_idx]; simp only [bind_tc_ok]
      obtain ⟨wpm, hwpm_eq, hwpm_val⟩ := cast_i64_ok (p.val[i - 2 ^ layer]!)
      rw [hwpm_eq]; simp only [bind_tc_ok]
      rw [idx_ok p i hi']; simp only [bind_tc_ok]
      obtain ⟨wpi, hwpi_eq, hwpi_val⟩ := cast_i64_ok (p.val[i]!)
      rw [hwpi_eq]; simp only [bind_tc_ok]
      -- `i13 = p[i-len] - p[i]`.
      obtain ⟨wdiff, hwdiff_eq, hwdiff_val⟩ :=
        i64_sub_i32_ok wpm wpi _ _ hwpm_val hwpi_val
      rw [hwdiff_eq]; simp only [bind_tc_ok]
      -- `i14 = z * (p[i-len] - p[i])`.
      obtain ⟨prod, hprod_eq, hprod_val⟩ :=
        i64_mul_canon_diff_ok zz wdiff (p.val[i - 2 ^ layer]!) (p.val[i]!) hzz_lo hzz_hi
          (by rw [hwdiff_val, hwpm_val, hwpi_val])
      rw [hprod_eq]; simp only [bind_tc_ok]
      obtain ⟨out, hout_eq, hout_res, hout_lo, hout_hi⟩ := mod_q_eq prod
      rw [hout_eq]
      have hout_fi : out = f i := by
        rw [hf_def]
        apply canonI32_eq_of_canonical out _ hout_lo hout_hi
        rw [hpure_cell]
        simp only [hge, if_false]
        rw [hout_res, hprod_val, hwdiff_val, hwpm_val, hwpi_val]
        push_cast
        rw [hz_zq, ← lift_res_getElem p i hi', ← lift_res_getElem p (i - 2 ^ layer) hilen_lt]
      rw [hout_fi]; simp only [bind_tc_ok]
  have heq := createi_pure_eq (T := Std.I32)
    (F := hacspec_ml_dsa.ntt.intt_layer.closure)
    256#usize
    hacspec_ml_dsa.ntt.intt_layer.closure.Insts.CoreOpsFunctionFnTupleUsizeI32
    (p, len_z, k_z) f hpure
  have heq' : hacspec_ml_dsa.ntt.intt_layer p ⟨BitVec.ofNat _ layer⟩
      = .ok ⟨(List.range (256#usize : Std.Usize).val).map f,
             by simp [List.length_map, List.length_range]⟩ := by
    unfold hacspec_ml_dsa.ntt.intt_layer
    rw [hlen_eq]; simp only [bind_tc_ok]
    rw [hi_eq]; simp only [bind_tc_ok]
    rw [hk_eq]; simp only [bind_tc_ok]
    exact heq
  refine ⟨_, heq', ?_, ?_⟩
  · conv_lhs => unfold lift_res
    apply Pure.build_congr
    intro i hi
    show (((⟨(List.range 256).map f, _⟩ : Aeneas.Std.Array Std.I32 256#usize).val[i]!).val : Zq) = _
    have hmap : ((List.range 256).map f)[i]! = f i := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl
    rw [hmap, hf_def, canonI32_lift]
    conv_lhs => unfold Pure.intt_layer; rw [Pure.build_getElem _ i hi]
  · intro i hi
    exact map_canonI32_canonical (fun i => (Pure.intt_layer (lift_res p) layer)[i]!) i hi

/-! ## (2) The `reduce_polynomial` (`·256⁻¹`) bridge. -/

/-- The `Z_q` numeral `8347681` equals `Pure.inv256`. -/
private theorem const_inv256 : ((8347681 : Zq)) = Pure.inv256 := by
  unfold Pure.inv256
  show ((8347681 : Zq)) = ((Montgomery.INV256 : Nat) : Zq)
  unfold Montgomery.INV256
  norm_num

/-- `(Pure.reduce_polynomial (lift_res p))[i]! = (lift_res p)[i]! * Pure.inv256`. -/
private theorem reduce_getElem (p : Aeneas.Std.Array Std.I32 256#usize) (i : Nat) (hi : i < 256) :
    (Pure.reduce_polynomial (lift_res p))[i]! = (lift_res p)[i]! * Pure.inv256 := by
  unfold Pure.reduce_polynomial lift_res Pure.build
  rw [getElem!_pos _ i (by simp [hi]), getElem!_pos _ i (by simp [hi])]
  simp [List.getElem_map, List.getElem_range]

/-- The product `8347681#i64 * (i32 value as i64)` fits in i64. -/
private theorem i64_mul_const_ok (a : Std.I64) (za : Std.I32)
    (ha : a.val = za.val) :
    ∃ s : Std.I64, ((8347681#i64) * a : Result Std.I64) = .ok s
      ∧ s.val = (8347681 : Int) * a.val := by
  obtain ⟨ha1, ha2⟩ := i32_i64_bound za a ha
  have hc : (8347681#i64 : Std.I64).val = (8347681 : Int) := by decide
  have hlo : (-4611686018427387904 : Int) ≤ (8347681 : Int) * a.val := by nlinarith
  have hhi : (8347681 : Int) * a.val ≤ (4611686018427387904 : Int) := by nlinarith
  have hmin : Aeneas.Std.IScalar.min .I64 ≤ (8347681#i64 : Std.I64).val * a.val := by
    simp only [IScalar.min_IScalarTy_I64_eq, Aeneas.Std.I64.min, Aeneas.Std.I64.numBits,
      IScalarTy.I64_numBits_eq, hc]; norm_num; omega
  have hmax : (8347681#i64 : Std.I64).val * a.val ≤ Aeneas.Std.IScalar.max .I64 := by
    simp only [IScalar.max_IScalarTy_I64_eq, Aeneas.Std.I64.max, Aeneas.Std.I64.numBits,
      IScalarTy.I64_numBits_eq, hc]; norm_num; omega
  obtain ⟨s, hs_eq, hs_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.mul_spec (x := 8347681#i64) (y := a) hmin hmax)
  exact ⟨s, hs_eq, by rw [hs_val, hc]⟩

set_option maxHeartbeats 4000000 in
/-- **`reduce_polynomial` bridge.** The final `·256⁻¹` createi-scale equals
    `Pure.reduce_polynomial` (lane-wise `·inv256`), canonical result. -/
theorem reduce_polynomial_bridge (p : Aeneas.Std.Array Std.I32 256#usize) :
    ∃ r, hacspec_ml_dsa.ntt.reduce_polynomial p = .ok r
      ∧ lift_res r = Pure.reduce_polynomial (lift_res p)
      ∧ (∀ i, i < 256 → 0 ≤ r.val[i]!.val ∧ r.val[i]!.val < (Q : Int)) := by
  set f : Nat → Std.I32 :=
    fun i => canonI32 ((Pure.reduce_polynomial (lift_res p))[i]!) with hf_def
  have hpure : ∀ i : Nat, i < (256#usize : Std.Usize).val →
      (hacspec_ml_dsa.ntt.reduce_polynomial.closure.Insts.CoreOpsFunctionFnTupleUsizeI32
        : CoreModels.core.ops.function.Fn _ _ _).FnMutInst.call_mut
          (8347681#i64, p) ⟨BitVec.ofNat _ i⟩ = .ok (f i, (8347681#i64, p)) := by
    intro i hi
    have hi' : i < 256 := hi
    show hacspec_ml_dsa.ntt.reduce_polynomial.closure.Insts.CoreOpsFunctionFnMutTupleUsizeI32.call_mut
        (8347681#i64, p) ⟨BitVec.ofNat _ i⟩ = .ok (f i, (8347681#i64, p))
    unfold hacspec_ml_dsa.ntt.reduce_polynomial.closure.Insts.CoreOpsFunctionFnMutTupleUsizeI32.call_mut
    unfold hacspec_ml_dsa.ntt.reduce_polynomial.closure.Insts.CoreOpsFunctionFnTupleUsizeI32.call
    change (do
        let v ← (do
          let i1 ← Aeneas.Std.Array.index_usize p ⟨BitVec.ofNat _ i⟩
          let i2 ← Aeneas.Std.lift (Aeneas.Std.IScalar.cast .I64 i1)
          let i3 ← (8347681#i64) * i2
          hacspec_ml_dsa.arithmetic.mod_q i3)
        Result.ok (v, (8347681#i64, p))) = .ok (f i, (8347681#i64, p))
    rw [idx_ok p i hi']; simp only [bind_tc_ok]
    obtain ⟨wpi, hwpi_eq, hwpi_val⟩ := cast_i64_ok (p.val[i]!)
    rw [hwpi_eq]; simp only [bind_tc_ok]
    obtain ⟨prod, hprod_eq, hprod_val⟩ := i64_mul_const_ok wpi _ hwpi_val
    rw [hprod_eq]; simp only [bind_tc_ok]
    obtain ⟨out, hout_eq, hout_res, hout_lo, hout_hi⟩ := mod_q_eq prod
    rw [hout_eq]
    have hout_fi : out = f i := by
      rw [hf_def]
      apply canonI32_eq_of_canonical out _ hout_lo hout_hi
      rw [reduce_getElem p i hi']
      rw [hout_res, hprod_val, hwpi_val]
      push_cast
      rw [const_inv256, ← lift_res_getElem p i hi']
      ring
    rw [hout_fi]; simp only [bind_tc_ok]
  have heq := createi_pure_eq (T := Std.I32)
    (F := hacspec_ml_dsa.ntt.reduce_polynomial.closure)
    256#usize
    hacspec_ml_dsa.ntt.reduce_polynomial.closure.Insts.CoreOpsFunctionFnTupleUsizeI32
    (8347681#i64, p) f hpure
  have heq' : hacspec_ml_dsa.ntt.reduce_polynomial p
      = .ok ⟨(List.range (256#usize : Std.Usize).val).map f,
             by simp [List.length_map, List.length_range]⟩ := by
    unfold hacspec_ml_dsa.ntt.reduce_polynomial; exact heq
  refine ⟨_, heq', ?_, ?_⟩
  · -- `lift_res (createi result) = Pure.reduce_polynomial (lift_res p)` via per-index ext.
    have hsz1 : (lift_res ⟨(List.range (256#usize : Std.Usize).val).map f, by
        simp [List.length_map, List.length_range]⟩).size = 256 := by
      unfold lift_res Pure.build; simp
    have hsz2 : (Pure.reduce_polynomial (lift_res p)).size = 256 := by
      unfold Pure.reduce_polynomial lift_res Pure.build; simp
    apply Array.ext
    · rw [hsz1, hsz2]
    · intro i h1 h2
      rw [hsz1] at h1
      rw [← getElem!_pos _ i (by rw [hsz1]; exact h1),
        ← getElem!_pos _ i (by rw [hsz2]; exact h1)]
      rw [lift_res_getElem _ i h1]
      show (((⟨(List.range 256).map f, _⟩ : Aeneas.Std.Array Std.I32 256#usize).val[i]!).val : Zq) = _
      have hmap : ((List.range 256).map f)[i]! = f i := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h1]; rfl
      rw [hmap, hf_def, canonI32_lift]
  · intro i hi
    exact map_canonI32_canonical (fun i => (Pure.reduce_polynomial (lift_res p))[i]!) i hi

/-! ## (3) The 8-layer NTT / iNTT bridges. -/

/-- `(n#usize) = ⟨BitVec.ofNat _ n⟩` for a small literal `n`. -/
private theorem usize_lit_eq (n : Nat) (hn : n < 65536) (m : Std.Usize) (hm : m.val = n) :
    m = (⟨BitVec.ofNat _ n⟩ : Std.Usize) := by
  apply Aeneas.Std.UScalar.eq_of_val_eq
  rw [usize_val n hn, hm]

/-- **Forward-NTT bridge.** The extracted 8-layer `ntt.ntt` equals (under `lift_res`)
    the pure `Pure.ntt` (foldl over `[7,…,0]`), canonical result. -/
theorem ntt_bridge (w : Aeneas.Std.Array Std.I32 256#usize) :
    ∃ r, hacspec_ml_dsa.ntt.ntt w = .ok r
      ∧ lift_res r = Pure.ntt (lift_res w)
      ∧ (∀ i, i < 256 → 0 ≤ r.val[i]!.val ∧ r.val[i]!.val < (Q : Int)) := by
  obtain ⟨p0, hp0_eq, hp0_lift, hp0_bnd⟩ := ntt_layer_bridge w 7 (by omega)
  obtain ⟨p1, hp1_eq, hp1_lift, hp1_bnd⟩ := ntt_layer_bridge p0 6 (by omega)
  obtain ⟨p2, hp2_eq, hp2_lift, hp2_bnd⟩ := ntt_layer_bridge p1 5 (by omega)
  obtain ⟨p3, hp3_eq, hp3_lift, hp3_bnd⟩ := ntt_layer_bridge p2 4 (by omega)
  obtain ⟨p4, hp4_eq, hp4_lift, hp4_bnd⟩ := ntt_layer_bridge p3 3 (by omega)
  obtain ⟨p5, hp5_eq, hp5_lift, hp5_bnd⟩ := ntt_layer_bridge p4 2 (by omega)
  obtain ⟨p6, hp6_eq, hp6_lift, hp6_bnd⟩ := ntt_layer_bridge p5 1 (by omega)
  obtain ⟨p7, hp7_eq, hp7_lift, hp7_bnd⟩ := ntt_layer_bridge p6 0 (by omega)
  refine ⟨p7, ?_, ?_, hp7_bnd⟩
  · unfold hacspec_ml_dsa.ntt.ntt
    rw [usize_lit_eq 7 (by omega) 7#usize (by simp),
      usize_lit_eq 6 (by omega) 6#usize (by simp),
      usize_lit_eq 5 (by omega) 5#usize (by simp),
      usize_lit_eq 4 (by omega) 4#usize (by simp),
      usize_lit_eq 3 (by omega) 3#usize (by simp),
      usize_lit_eq 2 (by omega) 2#usize (by simp),
      usize_lit_eq 1 (by omega) 1#usize (by simp),
      usize_lit_eq 0 (by omega) 0#usize (by simp)]
    rw [hp0_eq]; simp only [bind_tc_ok]
    rw [hp1_eq]; simp only [bind_tc_ok]
    rw [hp2_eq]; simp only [bind_tc_ok]
    rw [hp3_eq]; simp only [bind_tc_ok]
    rw [hp4_eq]; simp only [bind_tc_ok]
    rw [hp5_eq]; simp only [bind_tc_ok]
    rw [hp6_eq]; simp only [bind_tc_ok]
    rw [hp7_eq]
  · -- `lift_res p7 = Pure.ntt (lift_res w)`: chain the per-layer lifts through the foldl.
    show lift_res p7 = [7, 6, 5, 4, 3, 2, 1, 0].foldl (fun acc layer => Pure.ntt_layer acc layer) (lift_res w)
    simp only [List.foldl_cons, List.foldl_nil]
    rw [hp7_lift, hp6_lift, hp5_lift, hp4_lift, hp3_lift, hp2_lift, hp1_lift, hp0_lift]

/-- **Inverse-NTT bridge.** The extracted 8-layer `ntt.intt` (layers `0..7` then the
    `·256⁻¹` reduce) equals (under `lift_res`) the pure `Pure.intt`, canonical result. -/
theorem intt_bridge (w : Aeneas.Std.Array Std.I32 256#usize) :
    ∃ r, hacspec_ml_dsa.ntt.intt w = .ok r
      ∧ lift_res r = Pure.intt (lift_res w)
      ∧ (∀ i, i < 256 → 0 ≤ r.val[i]!.val ∧ r.val[i]!.val < (Q : Int)) := by
  obtain ⟨p0, hp0_eq, hp0_lift, hp0_bnd⟩ := intt_layer_bridge w 0 (by omega)
  obtain ⟨p1, hp1_eq, hp1_lift, hp1_bnd⟩ := intt_layer_bridge p0 1 (by omega)
  obtain ⟨p2, hp2_eq, hp2_lift, hp2_bnd⟩ := intt_layer_bridge p1 2 (by omega)
  obtain ⟨p3, hp3_eq, hp3_lift, hp3_bnd⟩ := intt_layer_bridge p2 3 (by omega)
  obtain ⟨p4, hp4_eq, hp4_lift, hp4_bnd⟩ := intt_layer_bridge p3 4 (by omega)
  obtain ⟨p5, hp5_eq, hp5_lift, hp5_bnd⟩ := intt_layer_bridge p4 5 (by omega)
  obtain ⟨p6, hp6_eq, hp6_lift, hp6_bnd⟩ := intt_layer_bridge p5 6 (by omega)
  obtain ⟨p7, hp7_eq, hp7_lift, hp7_bnd⟩ := intt_layer_bridge p6 7 (by omega)
  obtain ⟨r, hr_eq, hr_lift, hr_bnd⟩ := reduce_polynomial_bridge p7
  refine ⟨r, ?_, ?_, hr_bnd⟩
  · unfold hacspec_ml_dsa.ntt.intt
    rw [usize_lit_eq 0 (by omega) 0#usize (by simp),
      usize_lit_eq 1 (by omega) 1#usize (by simp),
      usize_lit_eq 2 (by omega) 2#usize (by simp),
      usize_lit_eq 3 (by omega) 3#usize (by simp),
      usize_lit_eq 4 (by omega) 4#usize (by simp),
      usize_lit_eq 5 (by omega) 5#usize (by simp),
      usize_lit_eq 6 (by omega) 6#usize (by simp),
      usize_lit_eq 7 (by omega) 7#usize (by simp)]
    rw [hp0_eq]; simp only [bind_tc_ok]
    rw [hp1_eq]; simp only [bind_tc_ok]
    rw [hp2_eq]; simp only [bind_tc_ok]
    rw [hp3_eq]; simp only [bind_tc_ok]
    rw [hp4_eq]; simp only [bind_tc_ok]
    rw [hp5_eq]; simp only [bind_tc_ok]
    rw [hp6_eq]; simp only [bind_tc_ok]
    rw [hp7_eq]; simp only [bind_tc_ok]
    rw [hr_eq]
  · -- `lift_res r = Pure.intt (lift_res w)`: reduce ∘ (foldl over `[0,…,7]`).
    show lift_res r = Pure.reduce_polynomial
      ([0, 1, 2, 3, 4, 5, 6, 7].foldl (fun acc layer => Pure.intt_layer acc layer) (lift_res w))
    simp only [List.foldl_cons, List.foldl_nil]
    rw [hr_lift, hp7_lift, hp6_lift, hp5_lift, hp4_lift, hp3_lift, hp2_lift, hp1_lift, hp0_lift]

/-! ## (4) hacspec-facing plain lemmas + `@[spec]` Triple corollaries.

`ntt_hacspec_eq` consumes the impl `ntt_fc` post (`lift_poly r = Pure.ntt …`) and
concludes the extracted spec on the canonical re-encodings. The inverse one is
`·R`-reconciled: `invert_ntt_montgomery_fc`'s output carries an extra `·R` (mont domain),
so the trusted-reference output is `lift_poly_res_intt r` (the impl output with the `R`
stripped — `·RINV`). -/

/-- Triple ↔ `.ok` reflection (file-scoped §13.5 copy). -/
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

/-- **`ntt` hacspec corollary (plain).** From the impl-FC functional post
    (`lift_poly r = Pure.ntt …`), the extracted `ntt.ntt` on the canonical re-encoding
    returns `lift_poly_res r`. -/
theorem ntt_hacspec_eq
    (re r : libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
              libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (h_impl : lift_poly r = Pure.ntt (lift_poly re)) :
    hacspec_ml_dsa.ntt.ntt (lift_poly_res re) = .ok (lift_poly_res r) := by
  obtain ⟨r', hr'_eq, hr'_lift, hr'_bnd⟩ := ntt_bridge (lift_poly_res re)
  rw [hr'_eq]
  congr 1
  apply lift_res_inj r' (lift_poly_res r) hr'_bnd
    (fun i hi => lift_poly_res_canonical r i hi)
  rw [hr'_lift, lift_res_lift_poly_res re, ← h_impl, lift_res_lift_poly_res r]

/-- The right-inverse re-encoding for the inverse-NTT corollary: strip the impl's extra
    `·R` (multiply by `RINV`), then canonically re-encode each clean `Z_q` coefficient. -/
def lift_poly_res_intt
    (r : libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
           libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) :
    Aeneas.Std.Array Std.I32 256#usize :=
  ⟨(List.range 256).map (fun i => canonI32 ((lift_poly r)[i]! * (Montgomery.RINV : Zq))),
   by simp [List.length_map, List.length_range]⟩

/-- Cell access for `lift_poly_res_intt`. -/
private theorem lift_poly_res_intt_getElem
    (r : libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
           libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (i : Nat) (hi : i < 256) :
    (lift_poly_res_intt r).val[i]! = canonI32 ((lift_poly r)[i]! * (Montgomery.RINV : Zq)) := by
  show ((List.range 256).map (fun i => canonI32 ((lift_poly r)[i]! * (Montgomery.RINV : Zq))))[i]! = _
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

/-- `lift_poly_res_intt r` cells are canonical (`[0,Q)`). -/
private theorem lift_poly_res_intt_canonical
    (r : libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
           libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (i : Nat) (hi : i < 256) :
    0 ≤ (lift_poly_res_intt r).val[i]!.val ∧ (lift_poly_res_intt r).val[i]!.val < (Q : Int) := by
  rw [lift_poly_res_intt_getElem r i hi]
  exact canonI32_canonical _

/-- Lifting the `·R`-stripped re-encoding recovers `(lift_poly r) · RINV` pointwise. -/
private theorem lift_res_lift_poly_res_intt
    (r : libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
           libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) :
    lift_res (lift_poly_res_intt r) = Pure.build (fun i => (lift_poly r)[i]! * (Montgomery.RINV : Zq)) := by
  unfold lift_res
  apply Pure.build_congr
  intro i hi
  rw [lift_poly_res_intt_getElem r i hi, canonI32_lift]

/-- **`invert_ntt_montgomery` hacspec corollary (plain, `·R`-reconciled).** From the impl
    post (`lift_poly r = (Pure.intt …).map (·*R)`), the extracted `ntt.intt` on the
    canonical re-encoding returns the `·R`-stripped re-encoding `lift_poly_res_intt r`. -/
theorem intt_hacspec_eq
    (re r : libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
              libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (h_impl : lift_poly r
                = (Pure.intt (lift_poly re)).map (· * ((Montgomery.R : Nat) : Zq))) :
    hacspec_ml_dsa.ntt.intt (lift_poly_res re) = .ok (lift_poly_res_intt r) := by
  obtain ⟨r', hr'_eq, hr'_lift, hr'_bnd⟩ := intt_bridge (lift_poly_res re)
  rw [hr'_eq]
  congr 1
  apply lift_res_inj r' (lift_poly_res_intt r) hr'_bnd
    (fun i hi => lift_poly_res_intt_canonical r i hi)
  -- `lift_res r' = Pure.intt (lift_poly re)`; `lift_res (lift_poly_res_intt r) = (lift_poly r)·RINV`.
  rw [hr'_lift, lift_res_lift_poly_res re, lift_res_lift_poly_res_intt r]
  -- Per-index: `(Pure.intt (lift_poly re))[i]! = (lift_poly r)[i]! · RINV`.
  have hsz1 : (Pure.intt (lift_poly re)).size = 256 := by
    unfold Pure.intt Pure.reduce_polynomial
    rw [Array.size_map]
    simp only [List.foldl_cons, List.foldl_nil]
    unfold Pure.intt_layer Pure.build; simp
  have hsz2 : (Pure.build (fun i => (lift_poly r)[i]! * (Montgomery.RINV : Zq))).size = 256 := by
    unfold Pure.build; simp
  apply Array.ext
  · rw [hsz1, hsz2]
  · intro i h1 h2
    rw [hsz1] at h1
    rw [← getElem!_pos _ i (by rw [hsz1]; exact h1),
      ← getElem!_pos _ i (by rw [hsz2]; exact h1)]
    rw [Pure.build_getElem _ i h1]
    -- `(lift_poly r)[i]! = (Pure.intt (lift_poly re))[i]! · R` from `h_impl`.
    have hcell : (lift_poly r)[i]! = (Pure.intt (lift_poly re))[i]! * ((Montgomery.R : Nat) : Zq) := by
      rw [h_impl]
      rw [getElem!_pos _ i (by rw [Array.size_map, hsz1]; exact h1), Array.getElem_map,
        ← getElem!_pos _ i (by rw [hsz1]; exact h1)]
    rw [hcell, mul_assoc, R_RINV_cast_eq_one, mul_one]

set_option maxHeartbeats 1000000 in
/-- **`ntt.ntt` ↔ extracted `hacspec_ml_dsa.ntt.ntt`** (`@[spec]` Triple). Composes the
    impl `ntt_fc` post with `ntt_hacspec_eq`. The per-lane input bound is fixed to its
    maximum `2^31-1 - 34*2^24 = 1577058303` (the largest `B` admitted by `ntt_fc`'s
    no-overflow constraint `B + 34*2^24 ≤ 2^31-1`). -/
@[spec]
theorem ntt_hacspec_fc
    (re : libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
            libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.simd_units.val[u]!).values.val[l]!.val.natAbs ≤ 1577058303) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.ntt.ntt libcrux_iot_ml_dsa.Polynomial.Ntt.portable_ops_inst re
    ⦃ ⇓ r => ⌜ hacspec_ml_dsa.ntt.ntt (lift_poly_res re) = .ok (lift_poly_res r) ⌝ ⦄ := by
  obtain ⟨r, hr_eq, hr_lift, _hr_bnd⟩ :=
    triple_exists_ok (libcrux_iot_ml_dsa.Polynomial.Ntt.ntt_fc re 1577058303 (by norm_num) hin)
  apply triple_of_ok hr_eq
  exact ntt_hacspec_eq re r hr_lift

/--
info: 'libcrux_iot_ml_dsa.Polynomial.HacspecNtt.ntt_hacspec_fc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ntt_hacspec_fc

set_option maxHeartbeats 1000000 in
/-- **`ntt.invert_ntt_montgomery` ↔ extracted `hacspec_ml_dsa.ntt.intt`** (`@[spec]`
    Triple, `·R`-reconciled). Composes `invert_ntt_montgomery_fc` with `intt_hacspec_eq`.
    The per-lane input bound is fixed to its maximum `2^23-1 = 8388607` (the largest `B`
    admitted by `invert_ntt_montgomery_fc`'s constraint `B ≤ 2^23-1`). -/
@[spec]
theorem intt_hacspec_fc
    (re : libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
            libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.simd_units.val[u]!).values.val[l]!.val.natAbs ≤ 8388607) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.ntt.invert_ntt_montgomery
      libcrux_iot_ml_dsa.Polynomial.Ntt.portable_ops_inst re
    ⦃ ⇓ r => ⌜ hacspec_ml_dsa.ntt.intt (lift_poly_res re) = .ok (lift_poly_res_intt r) ⌝ ⦄ := by
  obtain ⟨r, hr_eq, hr_lift, _hr_bnd⟩ :=
    triple_exists_ok (libcrux_iot_ml_dsa.Polynomial.Ntt.invert_ntt_montgomery_fc re 8388607 (by norm_num) hin)
  apply triple_of_ok hr_eq
  exact intt_hacspec_eq re r hr_lift

/--
info: 'libcrux_iot_ml_dsa.Polynomial.HacspecNtt.intt_hacspec_fc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms intt_hacspec_fc

end libcrux_iot_ml_dsa.Polynomial.HacspecNtt
