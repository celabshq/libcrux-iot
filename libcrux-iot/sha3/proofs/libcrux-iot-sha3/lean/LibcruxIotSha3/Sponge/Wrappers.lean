import LibcruxIotSha3.Sponge.Shake

/-! # The wrapper entry points

`Sponge/Shake.lean` proves the six functions whose `#[ensures]` names the FIPS 202
transcript directly. This file covers the eight that wrap them:

| wrapper | wraps | contract |
|---|---|---|
| `sha224`, `sha256`, `sha384`, `sha512` | the matching `*_ema`, into a fresh array | `bytes::sha3_N` |
| `shake128_ema`, `shake256_ema` | `keccakx1` at RATE 168 / 136 | `bytes::shake{128,256}` |
| `hash` | one of the four `shaN`, by `Algorithm` | all four, via `digest_matches` |
| `keccakx1` | `keccak.keccak` | none -- see below |

Each lemma here produces the value: the `keccakLanes` characterisation falls out of
the same `keccak_keccak_spec` application that establishes the `ok`.
`Verification/ProofObligations.lean` then composes that with the `pedantic_*`
agreement lemmas to produce the generated post, so no post is weakened.

`keccakx1` is the exception, and deliberately. It is generic over `RATE` and
`DELIM`, and the transcript has no rate-and-delimiter-parameterised byte sponge to
name: it exposes `KECCAK[c]` over bit strings and the six standard functions. A
contract for it would have to spell a byte-to-bit encoding and the delimiter's
suffix bits inline, on a `pub(crate)` function no caller reads -- which is the
reason the old `keccak_fc` wrapper was deleted. It keeps its `#[requires]`, whose
obligation is freedom from panics, overflow and out-of-bounds indexing, and the
`keccakLanes` value is available here for callers that want it.

No bound on the INPUT is needed for the `ok` anywhere in this file:
`keccak.keccak_keccak_spec` asks only for `RATE % 8 = 0` and `1 ≤ RATE ≤ 200`. The
`MAX_INPUT_LEN` bounds in the preconditions are what the TRANSCRIPT needs -- it
works on bit strings, so `8 * len` plus the suffix and `pad10*1` has to stay
representable -- which is why giving `shake128_ema`/`shake256_ema` a transcript-level
post meant tightening their `#[requires]` from `out.len() <= u32::MAX` to
`MAX_INPUT_LEN` on both `out` and `data`. -/

open Aeneas Aeneas.Std RustM Std.Do libcrux_iot_sha3
open LibcruxIotSha3.LaneModel
open LibcruxIotSha3.SpongeModel

namespace libcrux_iot_sha3.Sponge

-- Defensive seal re-issue, as in `Sponge/Shake.lean`: no proof in this file may
-- unfold either side of the permutation bridge.
attribute [local irreducible] keccak.keccakf1600 keccakFLanes

/-! ## Local helpers.

    The `Sponge/*` files each keep their own copy of these two, suffixed by
    file; they are `private`, so they do not cross module boundaries. -/

private theorem triple_of_ok_wr {α : Type} {x : RustM α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PredTrans.apply, hp]

private theorem triple_exists_ok_wr {α : Type} {x : RustM α}
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

private theorem keccakx1_eq_keccak_wr
    (RATE : Std.Usize) (DELIM : Std.U8)
    (data : Slice Std.U8) (out : Slice Std.U8) :
    keccakx1 RATE DELIM data out = keccak.keccak RATE DELIM data out := by
  unfold keccakx1; rfl

private theorem slice_len_eq_wr (s : Slice Std.U8) :
    CoreModels.core.slice.Slice.len s = .ok (Std.Slice.len s) := by
  unfold CoreModels.core.slice.Slice.len; rfl

/-! ## `keccakx1`

    A one-line forwarder to `keccak.keccak`; its `#[requires]` is exactly the
    permutation spec's side conditions, narrowed to `RATE ≤ 168`. -/

theorem keccakx1_spec
    (RATE : Std.Usize) (DELIM : Std.U8)
    (data : Slice Std.U8) (out : Slice Std.U8)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_ge_1 : 1 ≤ RATE.val)
    (h_RATE_le_200 : RATE.val ≤ 200) :
    ⦃ ⌜ True ⌝ ⦄
    keccakx1 RATE DELIM data out
    ⦃ ⇓ r => ⌜ r.val.length = out.val.length
              ∧ ∀ k : Nat, k < out.val.length →
                  r.val[k]!
                    = (keccakLanes (Std.Slice.len out) RATE.val DELIM data.val).val[k]!
              ⌝ ⦄ := by
  rw [keccakx1_eq_keccak_wr]
  exact keccak.keccak_keccak_spec RATE DELIM data out
    h_RATE_mod h_RATE_ge_1 h_RATE_le_200

/-! ## `shake128_ema` / `shake256_ema`

    The caller-allocated XOF entry points: `keccakx1` at the SHAKE rates, with
    the output length taken from `out` rather than from a const generic. -/

theorem shake128_ema_spec (out : Slice Std.U8) (data : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
    shake128_ema out data
    ⦃ ⇓ r => ⌜ r.val.length = out.val.length
              ∧ ∀ k : Nat, k < out.val.length →
                  r.val[k]!
                    = (keccakLanes (Std.Slice.len out) (168#usize : Std.Usize).val 31#u8
                        data.val).val[k]!
              ⌝ ⦄ := by
  have h_eq : shake128_ema out data = keccakx1 168#usize 31#u8 data out := by
    unfold shake128_ema; rfl
  rw [h_eq]
  exact keccakx1_spec 168#usize 31#u8 data out (by decide) (by decide) (by decide)

theorem shake256_ema_spec (out : Slice Std.U8) (data : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
    shake256_ema out data
    ⦃ ⇓ r => ⌜ r.val.length = out.val.length
              ∧ ∀ k : Nat, k < out.val.length →
                  r.val[k]!
                    = (keccakLanes (Std.Slice.len out) (136#usize : Std.Usize).val 31#u8
                        data.val).val[k]!
              ⌝ ⦄ := by
  have h_eq : shake256_ema out data = keccakx1 136#usize 31#u8 data out := by
    unfold shake256_ema; rfl
  rw [h_eq]
  exact keccakx1_spec 136#usize 31#u8 data out (by decide) (by decide) (by decide)

/-! ## The allocating SHA-3 wrappers

    `shaN payload` allocates a zero digest, hands it to `shaN_ema` as a mutable
    slice, and returns the written-back array. The array dance is the one from
    `shake128_spec`: `&mut out` on an array is `Array.to_slice_mut`, which is
    definitionally the pair `(to_slice a, from_slice a)`, so the write-back is
    just `Array.from_slice`. -/

theorem sha224_spec (payload : Slice Std.U8)
    (h_payload_bnd : payload.val.length ≤ 2305843009213693695) :
    ⦃ ⌜ True ⌝ ⦄
    sha224 payload
    ⦃ ⇓ r => ⌜ ∀ k : Nat, k < 28 →
                  r.val[k]!
                    = (keccakLanes 28#usize (144#usize : Std.Usize).val 6#u8
                        payload.val).val[k]! ⌝ ⦄ := by
  set a : Std.Array Std.U8 28#usize := Std.Array.repeat 28#usize 0#u8 with ha_def
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify a
                      = (RustM.ok a : RustM _) := rfl
  have h_to_slice_mut :
      (Std.lift (Std.Array.to_slice_mut a)
        : RustM (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 28#usize)))
        = .ok (Std.Array.to_slice a, Std.Array.from_slice a) := rfl
  set s : Slice Std.U8 := Std.Array.to_slice a with hs_def
  have h_s_len : s.val.length = 28 := by
    show a.to_slice.val.length = 28
    rw [Std.Array.val_to_slice]; exact a.property
  obtain ⟨s1, h_s1_eq, h_s1_len, h_s1_bytes⟩ :=
    triple_exists_ok_wr (sha224_ema_spec s payload h_payload_bnd h_s_len)
  have h_s1_len' : s1.val.length = (28#usize : Std.Usize).val := by
    rw [h_s1_len]; decide
  have h_from_slice :
      Std.Array.from_slice a s1
        = ⟨s1.val, by show s1.val.length = (28#usize : Std.Usize).val; exact h_s1_len'⟩ := by
    unfold Std.Array.from_slice
    rw [dif_pos h_s1_len']
  set out_arr : Std.Array Std.U8 28#usize :=
    ⟨s1.val, by show s1.val.length = (28#usize : Std.Usize).val; exact h_s1_len'⟩
    with hout_arr_def
  have h_impl_eq : sha224 payload = .ok out_arr := by
    unfold sha224
    rw [← ha_def]
    simp only [h_classify, h_to_slice_mut, bind_tc_ok]
    change (do
      let s1 ← sha224_ema s payload
      ok (Std.Array.from_slice a s1)) = .ok out_arr
    rw [h_s1_eq, bind_tc_ok, h_from_slice]
  apply triple_of_ok_wr (v := out_arr) h_impl_eq
  intro k hk
  show s1.val[k]! = _
  exact h_s1_bytes k hk

theorem sha256_spec (payload : Slice Std.U8)
    (h_payload_bnd : payload.val.length ≤ 2305843009213693695) :
    ⦃ ⌜ True ⌝ ⦄
    sha256 payload
    ⦃ ⇓ r => ⌜ ∀ k : Nat, k < 32 →
                  r.val[k]!
                    = (keccakLanes 32#usize (136#usize : Std.Usize).val 6#u8
                        payload.val).val[k]! ⌝ ⦄ := by
  set a : Std.Array Std.U8 32#usize := Std.Array.repeat 32#usize 0#u8 with ha_def
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify a
                      = (RustM.ok a : RustM _) := rfl
  have h_to_slice_mut :
      (Std.lift (Std.Array.to_slice_mut a)
        : RustM (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 32#usize)))
        = .ok (Std.Array.to_slice a, Std.Array.from_slice a) := rfl
  set s : Slice Std.U8 := Std.Array.to_slice a with hs_def
  have h_s_len : s.val.length = 32 := by
    show a.to_slice.val.length = 32
    rw [Std.Array.val_to_slice]; exact a.property
  obtain ⟨s1, h_s1_eq, h_s1_len, h_s1_bytes⟩ :=
    triple_exists_ok_wr (sha256_ema_spec s payload h_payload_bnd h_s_len)
  have h_s1_len' : s1.val.length = (32#usize : Std.Usize).val := by
    rw [h_s1_len]; decide
  have h_from_slice :
      Std.Array.from_slice a s1
        = ⟨s1.val, by show s1.val.length = (32#usize : Std.Usize).val; exact h_s1_len'⟩ := by
    unfold Std.Array.from_slice
    rw [dif_pos h_s1_len']
  set out_arr : Std.Array Std.U8 32#usize :=
    ⟨s1.val, by show s1.val.length = (32#usize : Std.Usize).val; exact h_s1_len'⟩
    with hout_arr_def
  have h_impl_eq : sha256 payload = .ok out_arr := by
    unfold sha256
    rw [← ha_def]
    simp only [h_classify, h_to_slice_mut, bind_tc_ok]
    change (do
      let s1 ← sha256_ema s payload
      ok (Std.Array.from_slice a s1)) = .ok out_arr
    rw [h_s1_eq, bind_tc_ok, h_from_slice]
  apply triple_of_ok_wr (v := out_arr) h_impl_eq
  intro k hk
  show s1.val[k]! = _
  exact h_s1_bytes k hk

theorem sha384_spec (payload : Slice Std.U8)
    (h_payload_bnd : payload.val.length ≤ 2305843009213693695) :
    ⦃ ⌜ True ⌝ ⦄
    sha384 payload
    ⦃ ⇓ r => ⌜ ∀ k : Nat, k < 48 →
                  r.val[k]!
                    = (keccakLanes 48#usize (104#usize : Std.Usize).val 6#u8
                        payload.val).val[k]! ⌝ ⦄ := by
  set a : Std.Array Std.U8 48#usize := Std.Array.repeat 48#usize 0#u8 with ha_def
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify a
                      = (RustM.ok a : RustM _) := rfl
  have h_to_slice_mut :
      (Std.lift (Std.Array.to_slice_mut a)
        : RustM (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 48#usize)))
        = .ok (Std.Array.to_slice a, Std.Array.from_slice a) := rfl
  set s : Slice Std.U8 := Std.Array.to_slice a with hs_def
  have h_s_len : s.val.length = 48 := by
    show a.to_slice.val.length = 48
    rw [Std.Array.val_to_slice]; exact a.property
  obtain ⟨s1, h_s1_eq, h_s1_len, h_s1_bytes⟩ :=
    triple_exists_ok_wr (sha384_ema_spec s payload h_payload_bnd h_s_len)
  have h_s1_len' : s1.val.length = (48#usize : Std.Usize).val := by
    rw [h_s1_len]; decide
  have h_from_slice :
      Std.Array.from_slice a s1
        = ⟨s1.val, by show s1.val.length = (48#usize : Std.Usize).val; exact h_s1_len'⟩ := by
    unfold Std.Array.from_slice
    rw [dif_pos h_s1_len']
  set out_arr : Std.Array Std.U8 48#usize :=
    ⟨s1.val, by show s1.val.length = (48#usize : Std.Usize).val; exact h_s1_len'⟩
    with hout_arr_def
  have h_impl_eq : sha384 payload = .ok out_arr := by
    unfold sha384
    rw [← ha_def]
    simp only [h_classify, h_to_slice_mut, bind_tc_ok]
    change (do
      let s1 ← sha384_ema s payload
      ok (Std.Array.from_slice a s1)) = .ok out_arr
    rw [h_s1_eq, bind_tc_ok, h_from_slice]
  apply triple_of_ok_wr (v := out_arr) h_impl_eq
  intro k hk
  show s1.val[k]! = _
  exact h_s1_bytes k hk

theorem sha512_spec (payload : Slice Std.U8)
    (h_payload_bnd : payload.val.length ≤ 2305843009213693695) :
    ⦃ ⌜ True ⌝ ⦄
    sha512 payload
    ⦃ ⇓ r => ⌜ ∀ k : Nat, k < 64 →
                  r.val[k]!
                    = (keccakLanes 64#usize (72#usize : Std.Usize).val 6#u8
                        payload.val).val[k]! ⌝ ⦄ := by
  set a : Std.Array Std.U8 64#usize := Std.Array.repeat 64#usize 0#u8 with ha_def
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify a
                      = (RustM.ok a : RustM _) := rfl
  have h_to_slice_mut :
      (Std.lift (Std.Array.to_slice_mut a)
        : RustM (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 64#usize)))
        = .ok (Std.Array.to_slice a, Std.Array.from_slice a) := rfl
  set s : Slice Std.U8 := Std.Array.to_slice a with hs_def
  have h_s_len : s.val.length = 64 := by
    show a.to_slice.val.length = 64
    rw [Std.Array.val_to_slice]; exact a.property
  obtain ⟨s1, h_s1_eq, h_s1_len, h_s1_bytes⟩ :=
    triple_exists_ok_wr (sha512_ema_spec s payload h_payload_bnd h_s_len)
  have h_s1_len' : s1.val.length = (64#usize : Std.Usize).val := by
    rw [h_s1_len]; decide
  have h_from_slice :
      Std.Array.from_slice a s1
        = ⟨s1.val, by show s1.val.length = (64#usize : Std.Usize).val; exact h_s1_len'⟩ := by
    unfold Std.Array.from_slice
    rw [dif_pos h_s1_len']
  set out_arr : Std.Array Std.U8 64#usize :=
    ⟨s1.val, by show s1.val.length = (64#usize : Std.Usize).val; exact h_s1_len'⟩
    with hout_arr_def
  have h_impl_eq : sha512 payload = .ok out_arr := by
    unfold sha512
    rw [← ha_def]
    simp only [h_classify, h_to_slice_mut, bind_tc_ok]
    change (do
      let s1 ← sha512_ema s payload
      ok (Std.Array.from_slice a s1)) = .ok out_arr
    rw [h_s1_eq, bind_tc_ok, h_from_slice]
  apply triple_of_ok_wr (v := out_arr) h_impl_eq
  intro k hk
  show s1.val[k]! = _
  exact h_s1_bytes k hk

/-! ## `hash`

    The dispatcher. Its precondition ties the const generic `LEN` to
    `digest_size algorithm`, so in each branch `LEN` is the matching digest size
    and the body after the `massert` is exactly the corresponding `shaN`. That
    is what these four equations say; the caller then reuses the `shaN_spec`
    above for the value, which is what `hash`'s `#[ensures]` needs. -/

/-- A `usize` widens to a `u64` without loss: `Usize.max < 2^64` on every
    supported target. The preconditions compare `len() as u64`, so every bound
    decoded below goes through this. -/
theorem cast_u64_val (x : Std.Usize) :
    (Std.UScalar.cast Std.UScalarTy.U64 x).val = x.val := by
  rw [Std.UScalar.cast_val_eq]
  refine Nat.mod_eq_of_lt ?_
  simp only [Std.UScalarTy.U64_numBits_eq]
  have hm : Std.Usize.max < 2 ^ 64 := by
    rw [Std.Usize.max_def, Std.Usize.numBits]
    simp only [Std.UScalarTy.numBits]
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> norm_num
  have hx : x.val ≤ Std.Usize.max := by scalar_tac
  exact Nat.lt_of_le_of_lt hx hm

theorem hash_cast_val_pub (payload : Slice Std.U8) :
    (Std.UScalar.cast Std.UScalarTy.U64 (Std.Slice.len payload)).val = payload.val.length := by
  rw [cast_u64_val, Std.Slice.len_val]

private theorem hash_massert (payload : Slice Std.U8)
    (h_payload_bnd : payload.val.length ≤ 2305843009213693695) :
    (massert ((Std.UScalar.cast Std.UScalarTy.U64 (Std.Slice.len payload)) ≤ MAX_INPUT_LEN)
      : RustM Unit) = .ok () := by
  unfold Aeneas.Std.massert
  refine if_pos ((Std.UScalar.le_equiv _ _).mpr ?_)
  rw [hash_cast_val_pub, max_input_len_val]; exact h_payload_bnd

theorem hash_eq_sha224 (payload : Slice Std.U8)
    (h_payload_bnd : payload.val.length ≤ 2305843009213693695) :
    hash 28#usize Algorithm.Sha224 payload = sha224 payload := by
  have h_eq : hash 28#usize Algorithm.Sha224 payload
      = (do
          let i ← CoreModels.core.slice.Slice.len payload
          let i1 ← Std.lift (Std.UScalar.cast Std.UScalarTy.U64 i)
          massert (i1 <= MAX_INPUT_LEN)
          sha224 payload) := by
    unfold hash sha224; rfl
  have hcast : (Std.lift (Std.UScalar.cast Std.UScalarTy.U64 (Std.Slice.len payload))
      : RustM Std.U64) = ok (Std.UScalar.cast Std.UScalarTy.U64 (Std.Slice.len payload)) := rfl
  rw [h_eq, slice_len_eq_wr, bind_tc_ok, hcast, bind_tc_ok,
    hash_massert payload h_payload_bnd, bind_tc_ok]

theorem hash_eq_sha256 (payload : Slice Std.U8)
    (h_payload_bnd : payload.val.length ≤ 2305843009213693695) :
    hash 32#usize Algorithm.Sha256 payload = sha256 payload := by
  have h_eq : hash 32#usize Algorithm.Sha256 payload
      = (do
          let i ← CoreModels.core.slice.Slice.len payload
          let i1 ← Std.lift (Std.UScalar.cast Std.UScalarTy.U64 i)
          massert (i1 <= MAX_INPUT_LEN)
          sha256 payload) := by
    unfold hash sha256; rfl
  have hcast : (Std.lift (Std.UScalar.cast Std.UScalarTy.U64 (Std.Slice.len payload))
      : RustM Std.U64) = ok (Std.UScalar.cast Std.UScalarTy.U64 (Std.Slice.len payload)) := rfl
  rw [h_eq, slice_len_eq_wr, bind_tc_ok, hcast, bind_tc_ok,
    hash_massert payload h_payload_bnd, bind_tc_ok]

theorem hash_eq_sha384 (payload : Slice Std.U8)
    (h_payload_bnd : payload.val.length ≤ 2305843009213693695) :
    hash 48#usize Algorithm.Sha384 payload = sha384 payload := by
  have h_eq : hash 48#usize Algorithm.Sha384 payload
      = (do
          let i ← CoreModels.core.slice.Slice.len payload
          let i1 ← Std.lift (Std.UScalar.cast Std.UScalarTy.U64 i)
          massert (i1 <= MAX_INPUT_LEN)
          sha384 payload) := by
    unfold hash sha384; rfl
  have hcast : (Std.lift (Std.UScalar.cast Std.UScalarTy.U64 (Std.Slice.len payload))
      : RustM Std.U64) = ok (Std.UScalar.cast Std.UScalarTy.U64 (Std.Slice.len payload)) := rfl
  rw [h_eq, slice_len_eq_wr, bind_tc_ok, hcast, bind_tc_ok,
    hash_massert payload h_payload_bnd, bind_tc_ok]

theorem hash_eq_sha512 (payload : Slice Std.U8)
    (h_payload_bnd : payload.val.length ≤ 2305843009213693695) :
    hash 64#usize Algorithm.Sha512 payload = sha512 payload := by
  have h_eq : hash 64#usize Algorithm.Sha512 payload
      = (do
          let i ← CoreModels.core.slice.Slice.len payload
          let i1 ← Std.lift (Std.UScalar.cast Std.UScalarTy.U64 i)
          massert (i1 <= MAX_INPUT_LEN)
          sha512 payload) := by
    unfold hash sha512; rfl
  have hcast : (Std.lift (Std.UScalar.cast Std.UScalarTy.U64 (Std.Slice.len payload))
      : RustM Std.U64) = ok (Std.UScalar.cast Std.UScalarTy.U64 (Std.Slice.len payload)) := rfl
  rw [h_eq, slice_len_eq_wr, bind_tc_ok, hcast, bind_tc_ok,
    hash_massert payload h_payload_bnd, bind_tc_ok]

/-! ## Axiom guards -/

/--
info: 'libcrux_iot_sha3.Sponge.keccakx1_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms keccakx1_spec

/--
info: 'libcrux_iot_sha3.Sponge.hash_eq_sha224' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hash_eq_sha224

end libcrux_iot_sha3.Sponge
