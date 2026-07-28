/-
  # SHAKE128/256 + SHA3-{224,256,384,512} ema specs.

  Each of these 6 top-level digest functions is a direct instantiation of
  `keccak.keccak_keccak_spec` (in `Sponge/Keccak.lean`). The impl side
  goes through `keccakx1 RATE DELIM` which is a one-liner wrapper around
  `keccak.keccak RATE DELIM`; the spec side goes through `sha3.sha3_N` /
  `sha3.shake_N` which is a one-liner wrapper around `sponge.keccak RATE
  DELIM`. The proofs thus reduce to: unfold both wrappers, apply
  `keccak_keccak_spec`, repackage.

  ## Posts (equality-form)

  ```
  -- SHAKE (variable length):
  ⦃⌜True⌝⦄ shake128 BYTES data ⦃⇓ r => ⌜
    ∃ spec_out : Std.Array Std.U8 BYTES,
      sha3.shake128 BYTES data = .ok spec_out
      ∧ ∀ k < BYTES.val, r.val[k]! = spec_out.val[k]! ⌝⦄

  -- SHA3-ema (fixed length, side condition `digest.len = DIGEST_SIZE`):
  ⦃⌜True⌝⦄ sha224_ema digest payload ⦃⇓ r => ⌜
    ∃ spec_out : Std.Array Std.U8 28#usize,
      sha3.sha3_224 payload = .ok spec_out
      ∧ r.val.length = 28
      ∧ ∀ k < 28, r.val[k]! = spec_out.val[k]! ⌝⦄
  ```

  ## Side conditions

  - All RATE values (72, 104, 136, 144, 168) are ≤ 200 and multiples of 8.
  - All RATE values are ≥ 1.
  - For ema specs: `digest.val.length = <DIGEST_SIZE>` (28/32/48/64) and
    `payload.val.length ≤ U32.MAX` (to discharge the impl's two `massert`s).
-/
import LibcruxIotSha3.Sponge.Keccak

open Aeneas Aeneas.Std Result Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

open libcrux_iot_sha3.Foundation

-- Defensive seal re-issue: no proof in this file may unfold either side of
-- Bridge 1.
set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ## SHAKE128/256 + SHA3-{224,256,384,512} ema specs. -/

/-! ### Local helpers. -/

private theorem triple_of_ok_sh {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PredTrans.apply, hp]

/-! ### `keccakx1` is a one-liner wrapper around `keccak.keccak`. -/

private theorem keccakx1_eq_keccak
    (RATE : Std.Usize) (DELIM : Std.U8)
    (data : Slice Std.U8) (out : Slice Std.U8) :
    keccakx1 RATE DELIM data out = keccak.keccak RATE DELIM data out := by
  unfold keccakx1; rfl

/-! ### Helper: `CoreModels.core.slice.Slice.len` Result-level equation. -/

private theorem slice_len_eq_sh (s : Slice Std.U8) :
    CoreModels.core.slice.Slice.len s = .ok (Std.Slice.len s) := by
  unfold CoreModels.core.slice.Slice.len; rfl

/-! ### Helper: `lift (UScalar.cast .Usize U32.MAX) = .ok 4294967295#usize`. -/

private theorem lift_cast_U32_MAX :
    (Std.lift (Std.UScalar.cast .Usize CoreModels.core.num.U32.MAX)
      : Result Std.Usize)
      = .ok 4294967295#usize := by
  unfold Std.lift
  congr 1
  apply Std.UScalar.eq_of_val_eq
  rw [Std.U32.cast_Usize_val_eq]
  -- Goal: CoreModels.core.num.U32.MAX.val = 4294967295#usize.val.
  show CoreModels.core.num.U32.MAX.val = (4294967295#usize : Std.Usize).val
  simp only [CoreModels.core.num.U32.MAX]
  rfl

/-! ### Helper: extract Triple post into existential form. -/

private theorem triple_exists_ok_sh {α : Type} {x : Result α}
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

/-! ## SHAKE128 spec. -/

theorem shake128_spec
    (BYTES : Std.Usize) (data : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
    shake128 BYTES data
    ⦃ ⇓ r => ⌜ ∃ spec_out : Std.Array Std.U8 BYTES,
                sha3.shake128 BYTES data = .ok spec_out
                ∧ ∀ k : Nat, k < BYTES.val →
                    r.val[k]! = spec_out.val[k]! ⌝ ⦄ := by
  -- Set up the internal arrays.
  set a : Std.Array Std.U8 BYTES := Std.Array.repeat BYTES 0#u8 with ha_def
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify a
                      = (Result.ok a : Result _) := rfl
  -- `Array.to_slice_mut a = (a.to_slice, Array.from_slice a)`.
  have h_to_slice_mut :
      (Std.lift (Std.Array.to_slice_mut a)
        : Result (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 BYTES)))
        = .ok (Std.Array.to_slice a, Std.Array.from_slice a) := rfl
  set s : Slice Std.U8 := Std.Array.to_slice a with hs_def
  have h_s_len : s.val.length = BYTES.val := by
    show a.to_slice.val.length = BYTES.val
    rw [Std.Array.val_to_slice]; exact a.property
  have h_slice_len_s : Std.Slice.len s = BYTES := by
    apply Std.UScalar.eq_of_val_eq
    show s.val.length = BYTES.val; exact h_s_len
  -- Apply `keccak_keccak_spec` with RATE := 168, DELIM := 31.
  have h_RATE_mod : (168#usize : Std.Usize).val % 8 = 0 := by decide
  have h_RATE_ge_1 : 1 ≤ (168#usize : Std.Usize).val := by decide
  have h_RATE_le_200 : (168#usize : Std.Usize).val ≤ 200 := by decide
  obtain ⟨s1, h_s1_eq, spec_out_kk, h_spec_squeeze, h_s1_len, h_s1_bytes⟩ :=
    triple_exists_ok_sh
      (keccak.keccak_keccak_spec 168#usize 31#u8 data s
        h_RATE_mod h_RATE_ge_1 h_RATE_le_200)
  -- `s1.val.length = s.val.length = BYTES.val`.
  have h_s1_len_BYTES : s1.val.length = BYTES.val := by
    rw [h_s1_len]; exact h_s_len
  -- `Array.from_slice a s1 = ⟨s1.val, …⟩`, valid since `s1.val.length = BYTES.val`.
  have h_from_slice :
      Std.Array.from_slice a s1
        = ⟨s1.val, by show s1.val.length = BYTES.val; exact h_s1_len_BYTES⟩ := by
    unfold Std.Array.from_slice
    rw [dif_pos h_s1_len_BYTES]
  set out_arr : Std.Array Std.U8 BYTES :=
    ⟨s1.val, by show s1.val.length = BYTES.val; exact h_s1_len_BYTES⟩
    with hout_arr_def
  -- Impl chain: `shake128 BYTES data = .ok out_arr`.
  have h_impl_eq : shake128 BYTES data = .ok out_arr := by
    unfold shake128
    show (do
      let out ← libcrux_secrets.traits.Classify.Blanket.classify a
      let (s, to_slice_mut_back) ← Std.lift (Std.Array.to_slice_mut out)
      let s1 ← keccakx1 168#usize 31#u8 data s
      ok (to_slice_mut_back s1)) = .ok out_arr
    rw [h_classify]; simp only [bind_tc_ok]
    rw [h_to_slice_mut]; simp only [bind_tc_ok]
    rw [keccakx1_eq_keccak]
    rw [h_s1_eq]; simp only [bind_tc_ok]
    rw [h_from_slice]
  -- Spec chain: `sha3.shake128 BYTES data = sponge.keccak BYTES 168 31 data`.
  -- We bridge `(Std.Slice.len s)` to `BYTES` by direct subtype construction.
  set spec_out : Std.Array Std.U8 BYTES :=
    ⟨spec_out_kk.val, by
      have h_prop := spec_out_kk.property
      show spec_out_kk.val.length = BYTES.val
      rw [h_prop]
      exact congrArg Std.UScalar.val h_slice_len_s⟩
    with hspec_out_def
  have h_spec_eq : sha3.shake128 BYTES data = .ok spec_out := by
    unfold sha3.shake128
    show sponge.keccak BYTES sha3.SHAKE128_RATE sha3.SHAKE_DELIM data
          = .ok spec_out
    unfold sha3.SHAKE128_RATE sha3.SHAKE_DELIM
    -- Generic transport lemma: for `h : a = b`, `sponge.keccak b ... = .ok x`
    -- iff `sponge.keccak a ... = .ok (subtype-cast x via h)`.
    have h_general :
        ∀ (B : Std.Usize) (h : (Std.Slice.len s) = B)
          (x : Std.Array Std.U8 B),
          x.val = spec_out_kk.val →
          sponge.keccak B 168#usize 31#u8 data = .ok x := by
      intro B h x hx
      subst h
      have h_eq : x = spec_out_kk := Subtype.ext hx
      rw [h_eq]; exact h_spec_squeeze
    exact h_general BYTES h_slice_len_s spec_out rfl
  apply triple_of_ok_sh (v := out_arr) h_impl_eq
  refine ⟨spec_out, h_spec_eq, ?_⟩
  intro k hk
  have hk' : k < s.val.length := by rw [h_s_len]; exact hk
  have h_byte := h_s1_bytes k hk'
  show s1.val[k]! = spec_out.val[k]!
  show s1.val[k]! = spec_out_kk.val[k]!
  exact h_byte

/-! ## SHAKE256 spec. -/

theorem shake256_spec
    (BYTES : Std.Usize) (data : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
    shake256 BYTES data
    ⦃ ⇓ r => ⌜ ∃ spec_out : Std.Array Std.U8 BYTES,
                sha3.shake256 BYTES data = .ok spec_out
                ∧ ∀ k : Nat, k < BYTES.val →
                    r.val[k]! = spec_out.val[k]! ⌝ ⦄ := by
  set a : Std.Array Std.U8 BYTES := Std.Array.repeat BYTES 0#u8 with ha_def
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify a
                      = (Result.ok a : Result _) := rfl
  have h_to_slice_mut :
      (Std.lift (Std.Array.to_slice_mut a)
        : Result (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 BYTES)))
        = .ok (Std.Array.to_slice a, Std.Array.from_slice a) := rfl
  set s : Slice Std.U8 := Std.Array.to_slice a with hs_def
  have h_s_len : s.val.length = BYTES.val := by
    show a.to_slice.val.length = BYTES.val
    rw [Std.Array.val_to_slice]; exact a.property
  have h_slice_len_s : Std.Slice.len s = BYTES := by
    apply Std.UScalar.eq_of_val_eq
    show s.val.length = BYTES.val; exact h_s_len
  have h_RATE_mod : (136#usize : Std.Usize).val % 8 = 0 := by decide
  have h_RATE_ge_1 : 1 ≤ (136#usize : Std.Usize).val := by decide
  have h_RATE_le_200 : (136#usize : Std.Usize).val ≤ 200 := by decide
  obtain ⟨s1, h_s1_eq, spec_out_kk, h_spec_squeeze, h_s1_len, h_s1_bytes⟩ :=
    triple_exists_ok_sh
      (keccak.keccak_keccak_spec 136#usize 31#u8 data s
        h_RATE_mod h_RATE_ge_1 h_RATE_le_200)
  have h_s1_len_BYTES : s1.val.length = BYTES.val := by
    rw [h_s1_len]; exact h_s_len
  have h_from_slice :
      Std.Array.from_slice a s1
        = ⟨s1.val, by show s1.val.length = BYTES.val; exact h_s1_len_BYTES⟩ := by
    unfold Std.Array.from_slice
    rw [dif_pos h_s1_len_BYTES]
  set out_arr : Std.Array Std.U8 BYTES :=
    ⟨s1.val, by show s1.val.length = BYTES.val; exact h_s1_len_BYTES⟩
    with hout_arr_def
  have h_impl_eq : shake256 BYTES data = .ok out_arr := by
    unfold shake256
    show (do
      let out ← libcrux_secrets.traits.Classify.Blanket.classify a
      let (s, to_slice_mut_back) ← Std.lift (Std.Array.to_slice_mut out)
      let s1 ← keccakx1 136#usize 31#u8 data s
      ok (to_slice_mut_back s1)) = .ok out_arr
    rw [h_classify]; simp only [bind_tc_ok]
    rw [h_to_slice_mut]; simp only [bind_tc_ok]
    rw [keccakx1_eq_keccak]
    rw [h_s1_eq]; simp only [bind_tc_ok]
    rw [h_from_slice]
  set spec_out : Std.Array Std.U8 BYTES :=
    ⟨spec_out_kk.val, by
      have h_prop := spec_out_kk.property
      show spec_out_kk.val.length = BYTES.val
      rw [h_prop]
      exact congrArg Std.UScalar.val h_slice_len_s⟩
    with hspec_out_def
  have h_spec_eq : sha3.shake256 BYTES data = .ok spec_out := by
    unfold sha3.shake256
    show sponge.keccak BYTES sha3.SHAKE256_RATE sha3.SHAKE_DELIM data
          = .ok spec_out
    unfold sha3.SHAKE256_RATE sha3.SHAKE_DELIM
    have h_general :
        ∀ (B : Std.Usize) (h : (Std.Slice.len s) = B)
          (x : Std.Array Std.U8 B),
          x.val = spec_out_kk.val →
          sponge.keccak B 136#usize 31#u8 data = .ok x := by
      intro B h x hx
      subst h
      have h_eq : x = spec_out_kk := Subtype.ext hx
      rw [h_eq]; exact h_spec_squeeze
    exact h_general BYTES h_slice_len_s spec_out rfl
  apply triple_of_ok_sh (v := out_arr) h_impl_eq
  refine ⟨spec_out, h_spec_eq, ?_⟩
  intro k hk
  have hk' : k < s.val.length := by rw [h_s_len]; exact hk
  have h_byte := h_s1_bytes k hk'
  show s1.val[k]! = spec_out.val[k]!
  show s1.val[k]! = spec_out_kk.val[k]!
  exact h_byte

/-! ## SHA3 ema specs. -/

/-! ### Bridge: `sha3_N payload = sponge.keccak N RATE DELIM payload` after
    unfolding the SHA3 constant defs. -/

theorem sha224_ema_spec
    (digest : Slice Std.U8) (payload : Slice Std.U8)
    (h_payload_bnd : payload.val.length ≤ 4294967295)
    (h_digest_len : digest.val.length = 28) :
    ⦃ ⌜ True ⌝ ⦄
    sha224_ema digest payload
    ⦃ ⇓ r => ⌜ ∃ spec_out : Std.Array Std.U8 28#usize,
                sha3.sha3_224 payload = .ok spec_out
                ∧ r.val.length = 28
                ∧ ∀ k : Nat, k < 28 →
                    r.val[k]! = spec_out.val[k]! ⌝ ⦄ := by
  -- Side facts.
  have h_slice_len_payload :
      CoreModels.core.slice.Slice.len payload = .ok (Std.Slice.len payload) :=
    slice_len_eq_sh payload
  have h_slice_len_digest :
      CoreModels.core.slice.Slice.len digest = .ok (Std.Slice.len digest) :=
    slice_len_eq_sh digest
  have h_payload_len_val : (Std.Slice.len payload).val = payload.val.length :=
    Std.Slice.len_val payload
  have h_digest_len_val : (Std.Slice.len digest).val = digest.val.length :=
    Std.Slice.len_val digest
  have h_slice_len_digest_eq : Std.Slice.len digest = 28#usize := by
    apply Std.UScalar.eq_of_val_eq
    rw [h_digest_len_val, h_digest_len]; rfl
  -- The `massert (i ≤ i1)` step: `i = Slice.len payload`, `i1 = 4294967295#usize`.
  have h_le_max : (Std.Slice.len payload) ≤ (4294967295#usize : Std.Usize) := by
    show (Std.Slice.len payload).val ≤ (4294967295#usize : Std.Usize).val
    rw [h_payload_len_val]; exact h_payload_bnd
  have h_massert_le :
      (massert ((Std.Slice.len payload) ≤ (4294967295#usize : Std.Usize))
        : Result Unit) = .ok () := by
    unfold Aeneas.Std.massert
    rw [if_pos h_le_max]
  -- `SHA3_224_DIGEST_SIZE = 28#usize`.
  have h_dsize : SHA3_224_DIGEST_SIZE = 28#usize := by
    unfold SHA3_224_DIGEST_SIZE; rfl
  have h_eq_dsize : (Std.Slice.len digest) = SHA3_224_DIGEST_SIZE := by
    rw [h_slice_len_digest_eq, h_dsize]
  have h_massert_eq :
      (massert ((Std.Slice.len digest) = SHA3_224_DIGEST_SIZE)
        : Result Unit) = .ok () := by
    unfold Aeneas.Std.massert
    rw [if_pos h_eq_dsize]
  -- Apply `keccak_keccak_spec` with RATE := 144, DELIM := 6.
  have h_RATE_mod : (144#usize : Std.Usize).val % 8 = 0 := by decide
  have h_RATE_ge_1 : 1 ≤ (144#usize : Std.Usize).val := by decide
  have h_RATE_le_200 : (144#usize : Std.Usize).val ≤ 200 := by decide
  obtain ⟨r_out, h_r_out_eq, spec_out_kk, h_spec_squeeze, h_r_out_len, h_r_out_bytes⟩ :=
    triple_exists_ok_sh
      (keccak.keccak_keccak_spec 144#usize 6#u8 payload digest
        h_RATE_mod h_RATE_ge_1 h_RATE_le_200)
  -- Impl chain.
  have h_impl_eq : sha224_ema digest payload = .ok r_out := by
    unfold sha224_ema
    rw [h_slice_len_payload]; simp only [bind_tc_ok]
    rw [lift_cast_U32_MAX]; simp only [bind_tc_ok]
    rw [h_massert_le]; simp only [bind_tc_ok]
    rw [h_slice_len_digest]; simp only [bind_tc_ok]
    rw [h_massert_eq]; simp only [bind_tc_ok]
    rw [keccakx1_eq_keccak]
    exact h_r_out_eq
  -- Spec chain. `spec_out_kk : Array U8 (Std.Slice.len digest)`. Transport to
  -- `Array U8 28#usize` by direct subtype construction.
  set spec_out : Std.Array Std.U8 28#usize :=
    ⟨spec_out_kk.val, by
      have h_prop := spec_out_kk.property
      show spec_out_kk.val.length = (28#usize : Std.Usize).val
      rw [h_prop]
      exact congrArg Std.UScalar.val h_slice_len_digest_eq⟩
    with hspec_out_def
  have h_spec_eq : sha3.sha3_224 payload = .ok spec_out := by
    unfold sha3.sha3_224
    show sponge.keccak 28#usize sha3.SHA3_224_RATE sha3.SHA3_DELIM payload
          = .ok spec_out
    unfold sha3.SHA3_224_RATE sha3.SHA3_DELIM
    have h_general :
        ∀ (B : Std.Usize) (h : (Std.Slice.len digest) = B)
          (x : Std.Array Std.U8 B),
          x.val = spec_out_kk.val →
          sponge.keccak B 144#usize 6#u8 payload = .ok x := by
      intro B h x hx
      subst h
      have h_eq : x = spec_out_kk := Subtype.ext hx
      rw [h_eq]; exact h_spec_squeeze
    exact h_general 28#usize h_slice_len_digest_eq spec_out rfl
  -- Assemble.
  apply triple_of_ok_sh (v := r_out) h_impl_eq
  refine ⟨spec_out, h_spec_eq, ?_, ?_⟩
  · rw [h_r_out_len]; exact h_digest_len
  · intro k hk
    have hk' : k < digest.val.length := by rw [h_digest_len]; exact hk
    have h_byte := h_r_out_bytes k hk'
    show r_out.val[k]! = spec_out.val[k]!
    show r_out.val[k]! = spec_out_kk.val[k]!
    exact h_byte

theorem sha256_ema_spec
    (digest : Slice Std.U8) (payload : Slice Std.U8)
    (h_payload_bnd : payload.val.length ≤ 4294967295)
    (h_digest_len : digest.val.length = 32) :
    ⦃ ⌜ True ⌝ ⦄
    sha256_ema digest payload
    ⦃ ⇓ r => ⌜ ∃ spec_out : Std.Array Std.U8 32#usize,
                sha3.sha3_256 payload = .ok spec_out
                ∧ r.val.length = 32
                ∧ ∀ k : Nat, k < 32 →
                    r.val[k]! = spec_out.val[k]! ⌝ ⦄ := by
  have h_slice_len_payload :
      CoreModels.core.slice.Slice.len payload = .ok (Std.Slice.len payload) :=
    slice_len_eq_sh payload
  have h_slice_len_digest :
      CoreModels.core.slice.Slice.len digest = .ok (Std.Slice.len digest) :=
    slice_len_eq_sh digest
  have h_payload_len_val : (Std.Slice.len payload).val = payload.val.length :=
    Std.Slice.len_val payload
  have h_digest_len_val : (Std.Slice.len digest).val = digest.val.length :=
    Std.Slice.len_val digest
  have h_slice_len_digest_eq : Std.Slice.len digest = 32#usize := by
    apply Std.UScalar.eq_of_val_eq
    rw [h_digest_len_val, h_digest_len]; rfl
  have h_le_max : (Std.Slice.len payload) ≤ (4294967295#usize : Std.Usize) := by
    show (Std.Slice.len payload).val ≤ (4294967295#usize : Std.Usize).val
    rw [h_payload_len_val]; exact h_payload_bnd
  have h_massert_le :
      (massert ((Std.Slice.len payload) ≤ (4294967295#usize : Std.Usize))
        : Result Unit) = .ok () := by
    unfold Aeneas.Std.massert
    rw [if_pos h_le_max]
  have h_dsize : SHA3_256_DIGEST_SIZE = 32#usize := by
    unfold SHA3_256_DIGEST_SIZE; rfl
  have h_eq_dsize : (Std.Slice.len digest) = SHA3_256_DIGEST_SIZE := by
    rw [h_slice_len_digest_eq, h_dsize]
  have h_massert_eq :
      (massert ((Std.Slice.len digest) = SHA3_256_DIGEST_SIZE)
        : Result Unit) = .ok () := by
    unfold Aeneas.Std.massert
    rw [if_pos h_eq_dsize]
  have h_RATE_mod : (136#usize : Std.Usize).val % 8 = 0 := by decide
  have h_RATE_ge_1 : 1 ≤ (136#usize : Std.Usize).val := by decide
  have h_RATE_le_200 : (136#usize : Std.Usize).val ≤ 200 := by decide
  obtain ⟨r_out, h_r_out_eq, spec_out_kk, h_spec_squeeze, h_r_out_len, h_r_out_bytes⟩ :=
    triple_exists_ok_sh
      (keccak.keccak_keccak_spec 136#usize 6#u8 payload digest
        h_RATE_mod h_RATE_ge_1 h_RATE_le_200)
  have h_impl_eq : sha256_ema digest payload = .ok r_out := by
    unfold sha256_ema
    rw [h_slice_len_payload]; simp only [bind_tc_ok]
    rw [lift_cast_U32_MAX]; simp only [bind_tc_ok]
    rw [h_massert_le]; simp only [bind_tc_ok]
    rw [h_slice_len_digest]; simp only [bind_tc_ok]
    rw [h_massert_eq]; simp only [bind_tc_ok]
    rw [keccakx1_eq_keccak]
    exact h_r_out_eq
  set spec_out : Std.Array Std.U8 32#usize :=
    ⟨spec_out_kk.val, by
      have h_prop := spec_out_kk.property
      show spec_out_kk.val.length = (32#usize : Std.Usize).val
      rw [h_prop]
      exact congrArg Std.UScalar.val h_slice_len_digest_eq⟩
    with hspec_out_def
  have h_spec_eq : sha3.sha3_256 payload = .ok spec_out := by
    unfold sha3.sha3_256
    show sponge.keccak 32#usize sha3.SHA3_256_RATE sha3.SHA3_DELIM payload
          = .ok spec_out
    unfold sha3.SHA3_256_RATE sha3.SHA3_DELIM
    have h_general :
        ∀ (B : Std.Usize) (h : (Std.Slice.len digest) = B)
          (x : Std.Array Std.U8 B),
          x.val = spec_out_kk.val →
          sponge.keccak B 136#usize 6#u8 payload = .ok x := by
      intro B h x hx
      subst h
      have h_eq : x = spec_out_kk := Subtype.ext hx
      rw [h_eq]; exact h_spec_squeeze
    exact h_general 32#usize h_slice_len_digest_eq spec_out rfl
  apply triple_of_ok_sh (v := r_out) h_impl_eq
  refine ⟨spec_out, h_spec_eq, ?_, ?_⟩
  · rw [h_r_out_len]; exact h_digest_len
  · intro k hk
    have hk' : k < digest.val.length := by rw [h_digest_len]; exact hk
    have h_byte := h_r_out_bytes k hk'
    show r_out.val[k]! = spec_out.val[k]!
    show r_out.val[k]! = spec_out_kk.val[k]!
    exact h_byte

theorem sha384_ema_spec
    (digest : Slice Std.U8) (payload : Slice Std.U8)
    (h_payload_bnd : payload.val.length ≤ 4294967295)
    (h_digest_len : digest.val.length = 48) :
    ⦃ ⌜ True ⌝ ⦄
    sha384_ema digest payload
    ⦃ ⇓ r => ⌜ ∃ spec_out : Std.Array Std.U8 48#usize,
                sha3.sha3_384 payload = .ok spec_out
                ∧ r.val.length = 48
                ∧ ∀ k : Nat, k < 48 →
                    r.val[k]! = spec_out.val[k]! ⌝ ⦄ := by
  have h_slice_len_payload :
      CoreModels.core.slice.Slice.len payload = .ok (Std.Slice.len payload) :=
    slice_len_eq_sh payload
  have h_slice_len_digest :
      CoreModels.core.slice.Slice.len digest = .ok (Std.Slice.len digest) :=
    slice_len_eq_sh digest
  have h_payload_len_val : (Std.Slice.len payload).val = payload.val.length :=
    Std.Slice.len_val payload
  have h_digest_len_val : (Std.Slice.len digest).val = digest.val.length :=
    Std.Slice.len_val digest
  have h_slice_len_digest_eq : Std.Slice.len digest = 48#usize := by
    apply Std.UScalar.eq_of_val_eq
    rw [h_digest_len_val, h_digest_len]; rfl
  have h_le_max : (Std.Slice.len payload) ≤ (4294967295#usize : Std.Usize) := by
    show (Std.Slice.len payload).val ≤ (4294967295#usize : Std.Usize).val
    rw [h_payload_len_val]; exact h_payload_bnd
  have h_massert_le :
      (massert ((Std.Slice.len payload) ≤ (4294967295#usize : Std.Usize))
        : Result Unit) = .ok () := by
    unfold Aeneas.Std.massert
    rw [if_pos h_le_max]
  have h_dsize : SHA3_384_DIGEST_SIZE = 48#usize := by
    unfold SHA3_384_DIGEST_SIZE; rfl
  have h_eq_dsize : (Std.Slice.len digest) = SHA3_384_DIGEST_SIZE := by
    rw [h_slice_len_digest_eq, h_dsize]
  have h_massert_eq :
      (massert ((Std.Slice.len digest) = SHA3_384_DIGEST_SIZE)
        : Result Unit) = .ok () := by
    unfold Aeneas.Std.massert
    rw [if_pos h_eq_dsize]
  have h_RATE_mod : (104#usize : Std.Usize).val % 8 = 0 := by decide
  have h_RATE_ge_1 : 1 ≤ (104#usize : Std.Usize).val := by decide
  have h_RATE_le_200 : (104#usize : Std.Usize).val ≤ 200 := by decide
  obtain ⟨r_out, h_r_out_eq, spec_out_kk, h_spec_squeeze, h_r_out_len, h_r_out_bytes⟩ :=
    triple_exists_ok_sh
      (keccak.keccak_keccak_spec 104#usize 6#u8 payload digest
        h_RATE_mod h_RATE_ge_1 h_RATE_le_200)
  have h_impl_eq : sha384_ema digest payload = .ok r_out := by
    unfold sha384_ema
    rw [h_slice_len_payload]; simp only [bind_tc_ok]
    rw [lift_cast_U32_MAX]; simp only [bind_tc_ok]
    rw [h_massert_le]; simp only [bind_tc_ok]
    rw [h_slice_len_digest]; simp only [bind_tc_ok]
    rw [h_massert_eq]; simp only [bind_tc_ok]
    rw [keccakx1_eq_keccak]
    exact h_r_out_eq
  set spec_out : Std.Array Std.U8 48#usize :=
    ⟨spec_out_kk.val, by
      have h_prop := spec_out_kk.property
      show spec_out_kk.val.length = (48#usize : Std.Usize).val
      rw [h_prop]
      exact congrArg Std.UScalar.val h_slice_len_digest_eq⟩
    with hspec_out_def
  have h_spec_eq : sha3.sha3_384 payload = .ok spec_out := by
    unfold sha3.sha3_384
    show sponge.keccak 48#usize sha3.SHA3_384_RATE sha3.SHA3_DELIM payload
          = .ok spec_out
    unfold sha3.SHA3_384_RATE sha3.SHA3_DELIM
    have h_general :
        ∀ (B : Std.Usize) (h : (Std.Slice.len digest) = B)
          (x : Std.Array Std.U8 B),
          x.val = spec_out_kk.val →
          sponge.keccak B 104#usize 6#u8 payload = .ok x := by
      intro B h x hx
      subst h
      have h_eq : x = spec_out_kk := Subtype.ext hx
      rw [h_eq]; exact h_spec_squeeze
    exact h_general 48#usize h_slice_len_digest_eq spec_out rfl
  apply triple_of_ok_sh (v := r_out) h_impl_eq
  refine ⟨spec_out, h_spec_eq, ?_, ?_⟩
  · rw [h_r_out_len]; exact h_digest_len
  · intro k hk
    have hk' : k < digest.val.length := by rw [h_digest_len]; exact hk
    have h_byte := h_r_out_bytes k hk'
    show r_out.val[k]! = spec_out.val[k]!
    show r_out.val[k]! = spec_out_kk.val[k]!
    exact h_byte

theorem sha512_ema_spec
    (digest : Slice Std.U8) (payload : Slice Std.U8)
    (h_payload_bnd : payload.val.length ≤ 4294967295)
    (h_digest_len : digest.val.length = 64) :
    ⦃ ⌜ True ⌝ ⦄
    sha512_ema digest payload
    ⦃ ⇓ r => ⌜ ∃ spec_out : Std.Array Std.U8 64#usize,
                sha3.sha3_512 payload = .ok spec_out
                ∧ r.val.length = 64
                ∧ ∀ k : Nat, k < 64 →
                    r.val[k]! = spec_out.val[k]! ⌝ ⦄ := by
  have h_slice_len_payload :
      CoreModels.core.slice.Slice.len payload = .ok (Std.Slice.len payload) :=
    slice_len_eq_sh payload
  have h_slice_len_digest :
      CoreModels.core.slice.Slice.len digest = .ok (Std.Slice.len digest) :=
    slice_len_eq_sh digest
  have h_payload_len_val : (Std.Slice.len payload).val = payload.val.length :=
    Std.Slice.len_val payload
  have h_digest_len_val : (Std.Slice.len digest).val = digest.val.length :=
    Std.Slice.len_val digest
  have h_slice_len_digest_eq : Std.Slice.len digest = 64#usize := by
    apply Std.UScalar.eq_of_val_eq
    rw [h_digest_len_val, h_digest_len]; rfl
  have h_le_max : (Std.Slice.len payload) ≤ (4294967295#usize : Std.Usize) := by
    show (Std.Slice.len payload).val ≤ (4294967295#usize : Std.Usize).val
    rw [h_payload_len_val]; exact h_payload_bnd
  have h_massert_le :
      (massert ((Std.Slice.len payload) ≤ (4294967295#usize : Std.Usize))
        : Result Unit) = .ok () := by
    unfold Aeneas.Std.massert
    rw [if_pos h_le_max]
  have h_dsize : SHA3_512_DIGEST_SIZE = 64#usize := by
    unfold SHA3_512_DIGEST_SIZE; rfl
  have h_eq_dsize : (Std.Slice.len digest) = SHA3_512_DIGEST_SIZE := by
    rw [h_slice_len_digest_eq, h_dsize]
  have h_massert_eq :
      (massert ((Std.Slice.len digest) = SHA3_512_DIGEST_SIZE)
        : Result Unit) = .ok () := by
    unfold Aeneas.Std.massert
    rw [if_pos h_eq_dsize]
  have h_RATE_mod : (72#usize : Std.Usize).val % 8 = 0 := by decide
  have h_RATE_ge_1 : 1 ≤ (72#usize : Std.Usize).val := by decide
  have h_RATE_le_200 : (72#usize : Std.Usize).val ≤ 200 := by decide
  obtain ⟨r_out, h_r_out_eq, spec_out_kk, h_spec_squeeze, h_r_out_len, h_r_out_bytes⟩ :=
    triple_exists_ok_sh
      (keccak.keccak_keccak_spec 72#usize 6#u8 payload digest
        h_RATE_mod h_RATE_ge_1 h_RATE_le_200)
  have h_impl_eq : sha512_ema digest payload = .ok r_out := by
    unfold sha512_ema
    rw [h_slice_len_payload]; simp only [bind_tc_ok]
    rw [lift_cast_U32_MAX]; simp only [bind_tc_ok]
    rw [h_massert_le]; simp only [bind_tc_ok]
    rw [h_slice_len_digest]; simp only [bind_tc_ok]
    rw [h_massert_eq]; simp only [bind_tc_ok]
    rw [keccakx1_eq_keccak]
    exact h_r_out_eq
  set spec_out : Std.Array Std.U8 64#usize :=
    ⟨spec_out_kk.val, by
      have h_prop := spec_out_kk.property
      show spec_out_kk.val.length = (64#usize : Std.Usize).val
      rw [h_prop]
      exact congrArg Std.UScalar.val h_slice_len_digest_eq⟩
    with hspec_out_def
  have h_spec_eq : sha3.sha3_512 payload = .ok spec_out := by
    unfold sha3.sha3_512
    show sponge.keccak 64#usize sha3.SHA3_512_RATE sha3.SHA3_DELIM payload
          = .ok spec_out
    unfold sha3.SHA3_512_RATE sha3.SHA3_DELIM
    have h_general :
        ∀ (B : Std.Usize) (h : (Std.Slice.len digest) = B)
          (x : Std.Array Std.U8 B),
          x.val = spec_out_kk.val →
          sponge.keccak B 72#usize 6#u8 payload = .ok x := by
      intro B h x hx
      subst h
      have h_eq : x = spec_out_kk := Subtype.ext hx
      rw [h_eq]; exact h_spec_squeeze
    exact h_general 64#usize h_slice_len_digest_eq spec_out rfl
  apply triple_of_ok_sh (v := r_out) h_impl_eq
  refine ⟨spec_out, h_spec_eq, ?_, ?_⟩
  · rw [h_r_out_len]; exact h_digest_len
  · intro k hk
    have hk' : k < digest.val.length := by rw [h_digest_len]; exact hk
    have h_byte := h_r_out_bytes k hk'
    show r_out.val[k]! = spec_out.val[k]!
    show r_out.val[k]! = spec_out_kk.val[k]!
    exact h_byte

end libcrux_iot_sha3.Sponge
