import LibcruxIotSha3.Composition.Pedantic.Bytes
import LibcruxIotSha3.Composition.Pedantic.KeccakC
/-!
# The six SHA-3 functions (FIPS 202, §6.1 and §6.2)

`SHA3-d(M) = KECCAK[2d](M ‖ 01, d)` and `SHAKE(M, d) = KECCAK[c](M ‖ 1111, d)`.
This module names `KECCAK[c]` as a list function (`keccakCList`), shows that
each of the six bit-level entry points is that function at its own capacity and
suffix, and then lifts all six to the byte level through `h2b`/`b2h`.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-- `KECCAK[c](N, d)`: pad `N` to a multiple of the rate, absorb every block,
    then squeeze `d` bits (FIPS 202, §5.2 together with Algorithm 8). -/
def keccakCList (c : Nat) (n : List Bool) (d : Nat) : List Bool :=
  squeezeAll keccakF (1600 - c) d
    (absorbFrom keccakF (1600 - c) c (n ++ padBits (1600 - c) n.length)
      (List.replicate 1600 false) 0
      ((n ++ padBits (1600 - c) n.length).length / (1600 - c)))
  |>.take d

/-- Absorbing keeps the state 1600 bits wide. -/
theorem absorbFrom_len (r c : Nat) (p : List Bool) :
    ∀ (k : Nat) (s : List Bool) (i : Nat), s.length = 1600 →
      (absorbFrom keccakF r c p s i k).length = 1600 := by
  intro k
  induction k with
  | zero => intro s i hs; simpa only [absorbFrom] using hs
  | succ k ih =>
    intro s i _
    simp only [absorbFrom]
    exact ih _ _ (by simp only [absorbStep]; exact keccakF_len _)

/-- `KECCAK[c]` emits exactly `d` bits. -/
theorem keccakCList_len (c : Nat) (n : List Bool) (d : Nat) (hc : c < 1600) :
    (keccakCList c n d).length = d := by
  have hr : 0 < 1600 - c := by omega
  have hslen := absorbFrom_len (1600 - c) c (n ++ padBits (1600 - c) n.length)
    ((n ++ padBits (1600 - c) n.length).length / (1600 - c)) (List.replicate 1600 false) 0
    (by simp only [List.length_replicate])
  have hfuel : d ≤ ([] : List Bool).length + (d / (1600 - c) + 1) * (1600 - c) := by
    have h1 := Nat.div_add_mod d (1600 - c)
    have h2 := Nat.mod_lt d hr
    have hcomm : d / (1600 - c) * (1600 - c) = (1600 - c) * (d / (1600 - c)) :=
      Nat.mul_comm _ _
    simp only [List.length_nil, Nat.zero_add, Nat.succ_mul]
    omega
  have hge := squeezeFrom_len (b := 1600) keccakF (fun x _ => keccakF_len x) (1600 - c) d
    hr (by omega) (d / (1600 - c)) _ [] hslen hfuel
  simp only [keccakCList, squeezeAll, List.length_take]
  omega

/-- `keccak_c` computes `keccakCList`. -/
theorem keccak_c_list_eq (c : Std.Usize) (hc : c.val < 1600)
    (n : Slice Bool) (hn : n.val.length ≤ 4294965000)
    (d : Std.Usize) (hdb : d.val ≤ 4294965000) :
    ∃ out : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.sponge.keccak_c c n d = ok out ∧
      out.val = keccakCList c.val n.val d.val :=
  keccak_c_eq c hc n hn d hdb

/-! ### The bit-level entry points -/

/-- Every one of the six has the same shape: append a domain-separation suffix
    and call `KECCAK[c]`. -/
theorem suffix_keccak_eq (m : Slice Bool) (sfx : Slice Bool) (c d : Std.Usize)
    (hc : c.val < 1600) (hdb : d.val ≤ 4294965000)
    (hm : m.val.length + sfx.val.length ≤ 4294965000) :
    ∃ out : alloc.vec.Vec Bool,
      (do
        let v ← hacspec_sha3_pedantic.bits.concat m sfx
        let s1 ← alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref v
        hacspec_sha3_pedantic.sponge.keccak_c c s1 d) = ok out ∧
      out.val = keccakCList c.val (m.val ++ sfx.val) d.val := by
  obtain ⟨v, hv, hvv⟩ := concat_eq m sfx (by scalar_tac)
  have hvs : (⟨v.val, v.property⟩ : Slice Bool).val = m.val ++ sfx.val := hvv
  obtain ⟨out, hout, houtv⟩ := keccak_c_eq c hc ⟨v.val, v.property⟩ (by rw [hvs]; simpa using hm)
    d hdb
  refine ⟨out, ?_, ?_⟩
  · rw [hv, bind_tc_ok, vec_deref_eq, bind_tc_ok]
    exact hout
  · rw [houtv, ← hvs]
    rfl


/-- The SHA-3 domain-separation suffix `01`. -/
theorem hash_suffix_val :
    (Std.Array.to_slice hacspec_sha3_pedantic.sha3.HASH_SUFFIX).val = [false, true] := by
  simp [hacspec_sha3_pedantic.sha3.HASH_SUFFIX, Std.Array.to_slice, Std.Array.make]

/-- The SHAKE domain-separation suffix `1111`. -/
theorem xof_suffix_val :
    (Std.Array.to_slice hacspec_sha3_pedantic.sha3.XOF_SUFFIX).val = [true, true, true, true] := by
  simp [hacspec_sha3_pedantic.sha3.XOF_SUFFIX, Std.Array.to_slice, Std.Array.repeat]

/-- FIPS 202, §6.1: `SHA3-224(M) = KECCAK[448](M ‖ 01, 224)`. -/
theorem sha3_224_bits_eq (m : Slice Bool) (hm : m.val.length + 2 ≤ 4294965000) :
    ∃ out : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.sha3.sha3_224 m = ok out ∧
      out.val = keccakCList 448 (m.val ++ [false, true]) 224 := by
  obtain ⟨out, hout, houtv⟩ := suffix_keccak_eq m
    (Std.Array.to_slice hacspec_sha3_pedantic.sha3.HASH_SUFFIX) 448#usize 224#usize
    (by simp) (by simp) (by rw [hash_suffix_val]; simpa using hm)
  refine ⟨out, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.sha3.sha3_224
    exact hout
  · rw [houtv, hash_suffix_val]
    norm_num

/-- FIPS 202, §6.1: `SHA3-256(M) = KECCAK[512](M ‖ 01, 256)`. -/
theorem sha3_256_bits_eq (m : Slice Bool) (hm : m.val.length + 2 ≤ 4294965000) :
    ∃ out : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.sha3.sha3_256 m = ok out ∧
      out.val = keccakCList 512 (m.val ++ [false, true]) 256 := by
  obtain ⟨out, hout, houtv⟩ := suffix_keccak_eq m
    (Std.Array.to_slice hacspec_sha3_pedantic.sha3.HASH_SUFFIX) 512#usize 256#usize
    (by simp) (by simp) (by rw [hash_suffix_val]; simpa using hm)
  refine ⟨out, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.sha3.sha3_256
    exact hout
  · rw [houtv, hash_suffix_val]
    norm_num

/-- FIPS 202, §6.1: `SHA3-384(M) = KECCAK[768](M ‖ 01, 384)`. -/
theorem sha3_384_bits_eq (m : Slice Bool) (hm : m.val.length + 2 ≤ 4294965000) :
    ∃ out : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.sha3.sha3_384 m = ok out ∧
      out.val = keccakCList 768 (m.val ++ [false, true]) 384 := by
  obtain ⟨out, hout, houtv⟩ := suffix_keccak_eq m
    (Std.Array.to_slice hacspec_sha3_pedantic.sha3.HASH_SUFFIX) 768#usize 384#usize
    (by simp) (by simp) (by rw [hash_suffix_val]; simpa using hm)
  refine ⟨out, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.sha3.sha3_384
    exact hout
  · rw [houtv, hash_suffix_val]
    norm_num

/-- FIPS 202, §6.1: `SHA3-512(M) = KECCAK[1024](M ‖ 01, 512)`. -/
theorem sha3_512_bits_eq (m : Slice Bool) (hm : m.val.length + 2 ≤ 4294965000) :
    ∃ out : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.sha3.sha3_512 m = ok out ∧
      out.val = keccakCList 1024 (m.val ++ [false, true]) 512 := by
  obtain ⟨out, hout, houtv⟩ := suffix_keccak_eq m
    (Std.Array.to_slice hacspec_sha3_pedantic.sha3.HASH_SUFFIX) 1024#usize 512#usize
    (by simp) (by simp) (by rw [hash_suffix_val]; simpa using hm)
  refine ⟨out, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.sha3.sha3_512
    exact hout
  · rw [houtv, hash_suffix_val]
    norm_num

/-- FIPS 202, §6.2: `SHAKE128(M, d) = KECCAK[256](M ‖ 1111, d)`. -/
theorem shake128_bits_eq (m : Slice Bool) (d : Std.Usize)
    (hdb : d.val ≤ 4294965000) (hm : m.val.length + 4 ≤ 4294965000) :
    ∃ out : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.sha3.shake128 m d = ok out ∧
      out.val = keccakCList 256 (m.val ++ [true, true, true, true]) d.val := by
  obtain ⟨out, hout, houtv⟩ := suffix_keccak_eq m
    (Std.Array.to_slice hacspec_sha3_pedantic.sha3.XOF_SUFFIX) 256#usize d
    (by simp) hdb (by rw [xof_suffix_val]; simpa using hm)
  refine ⟨out, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.sha3.shake128
    exact hout
  · rw [houtv, xof_suffix_val]
    norm_num

/-- FIPS 202, §6.2: `SHAKE256(M, d) = KECCAK[512](M ‖ 1111, d)`. -/
theorem shake256_bits_eq (m : Slice Bool) (d : Std.Usize)
    (hdb : d.val ≤ 4294965000) (hm : m.val.length + 4 ≤ 4294965000) :
    ∃ out : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.sha3.shake256 m d = ok out ∧
      out.val = keccakCList 512 (m.val ++ [true, true, true, true]) d.val := by
  obtain ⟨out, hout, houtv⟩ := suffix_keccak_eq m
    (Std.Array.to_slice hacspec_sha3_pedantic.sha3.XOF_SUFFIX) 512#usize d
    (by simp) hdb (by rw [xof_suffix_val]; simpa using hm)
  refine ⟨out, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.sha3.shake256
    exact hout
  · rw [houtv, xof_suffix_val]
    norm_num

/-! ### The byte-level entry points -/

/-- `b2h` turns `n` bits into `⌈n/8⌉` bytes. -/
theorem b2hList_len (s : List Bool) :
    (b2hList s).length = (s.length + (8 - s.length % 8) % 8) / 8 := by
  simp [b2hList]

/-- Cloning a `u8` is the identity, so `mapM`-cloning a list is too. -/
theorem mapM_clone_u8 (l : List Std.U8) :
    l.mapM core.U8.Insts.CoreCloneClone.clone = ok l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.mapM_cons, core.U8.Insts.CoreCloneClone.clone, ih]
    rfl

/-- `copy_from_slice` on `u8` slices of equal length yields the source. -/
theorem copy_from_slice_eq (dest src : Slice Std.U8)
    (h : dest.val.length = src.val.length) :
    core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy dest src = ok src := by
  unfold core.slice.Slice.copy_from_slice rust_primitives.slice.slice_clone_from_slice
  rw [if_pos (show dest.length = src.length from by simpa [Std.Slice.length] using h)]
  split
  · rename_i cloned hcl
    rw [mapM_clone_u8] at hcl
    injection hcl with hcl
    subst hcl
    rfl
  · rename_i e hcl
    rw [mapM_clone_u8] at hcl
    simp at hcl
  · rename_i hcl
    rw [mapM_clone_u8] at hcl
    simp at hcl

/-- The tail shared by the four fixed-size digests: copy the digest into a
    zeroed output array. -/
theorem copy_into_array_eq {n : Std.Usize} (a : Std.Array Std.U8 n)
    (d : alloc.vec.Vec Std.U8) (hd : d.val.length = n.val) :
    (do
      let (s2, back) ← Std.lift (Std.Array.to_slice_mut a)
      let s3 ← alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref d
      let s4 ← core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy s2 s3
      ok (back s4)) = ok (Std.Array.from_slice a ⟨d.val, d.property⟩) := by
  show (do
      let s4 ← core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy
        (Std.Array.to_slice a) ⟨d.val, d.property⟩
      ok (Std.Array.from_slice a s4)) = _
  rw [copy_from_slice_eq _ _ (by simpa [Std.Array.to_slice] using hd.symm)]
  rfl

/-- `SHA3-224` on byte strings: `h2b`, the bit-level hash, then `b2h`. -/
theorem sha3_224_bytes_eq (m : Slice Std.U8) (hm : 8 * m.val.length + 2 ≤ 4294965000) :
    ∃ out : Std.Array Std.U8 28#usize,
      hacspec_sha3_pedantic.bytes.sha3_224 m = ok out ∧
      out.val = b2hList (keccakCList 448 (h2bList m.val ++ [false, true]) 224) := by
  have hmb : 8 * m.val.length ≤ Std.Usize.max := by scalar_tac
  obtain ⟨v, hv, hvv⟩ := h2b_full_eq m hmb
  have hvs : (⟨v.val, v.property⟩ : Slice Bool).val = h2bList m.val := hvv
  obtain ⟨v1, hv1, hv1v⟩ := sha3_224_bits_eq ⟨v.val, v.property⟩ (by rw [hvs, h2bList_len]; omega)
  have hv1s : (⟨v1.val, v1.property⟩ : Slice Bool).val
      = keccakCList 448 (h2bList m.val ++ [false, true]) 224 := by
    rw [show (⟨v1.val, v1.property⟩ : Slice Bool).val = v1.val from rfl, hv1v, hvs]
  have hklen : (keccakCList 448 (h2bList m.val ++ [false, true]) 224).length = 224 :=
    keccakCList_len 448 _ 224 (by omega)
  obtain ⟨digest, hdig, hdigv⟩ := b2h_eq ⟨v1.val, v1.property⟩ (by rw [hv1s, hklen]; scalar_tac)
  have hdiglen : digest.val.length = (28#usize : Std.Usize).val := by
    rw [hdigv, hv1s, b2hList_len, hklen]
    norm_num
  refine ⟨Std.Array.from_slice (Std.Array.repeat 28#usize 0#u8)
    ⟨digest.val, digest.property⟩, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.bytes.sha3_224
    rw [hv, bind_tc_ok, vec_deref_eq, bind_tc_ok, hv1, bind_tc_ok, vec_deref_eq, bind_tc_ok,
      hdig, bind_tc_ok]
    exact copy_into_array_eq _ digest hdiglen
  · rw [Std.Array.from_slice_val _ ⟨digest.val, digest.property⟩ hdiglen, hdigv, hv1s]

/-- `SHA3-256` on byte strings: `h2b`, the bit-level hash, then `b2h`. -/
theorem sha3_256_bytes_eq (m : Slice Std.U8) (hm : 8 * m.val.length + 2 ≤ 4294965000) :
    ∃ out : Std.Array Std.U8 32#usize,
      hacspec_sha3_pedantic.bytes.sha3_256 m = ok out ∧
      out.val = b2hList (keccakCList 512 (h2bList m.val ++ [false, true]) 256) := by
  have hmb : 8 * m.val.length ≤ Std.Usize.max := by scalar_tac
  obtain ⟨v, hv, hvv⟩ := h2b_full_eq m hmb
  have hvs : (⟨v.val, v.property⟩ : Slice Bool).val = h2bList m.val := hvv
  obtain ⟨v1, hv1, hv1v⟩ := sha3_256_bits_eq ⟨v.val, v.property⟩ (by rw [hvs, h2bList_len]; omega)
  have hv1s : (⟨v1.val, v1.property⟩ : Slice Bool).val
      = keccakCList 512 (h2bList m.val ++ [false, true]) 256 := by
    rw [show (⟨v1.val, v1.property⟩ : Slice Bool).val = v1.val from rfl, hv1v, hvs]
  have hklen : (keccakCList 512 (h2bList m.val ++ [false, true]) 256).length = 256 :=
    keccakCList_len 512 _ 256 (by omega)
  obtain ⟨digest, hdig, hdigv⟩ := b2h_eq ⟨v1.val, v1.property⟩ (by rw [hv1s, hklen]; scalar_tac)
  have hdiglen : digest.val.length = (32#usize : Std.Usize).val := by
    rw [hdigv, hv1s, b2hList_len, hklen]
    norm_num
  refine ⟨Std.Array.from_slice (Std.Array.repeat 32#usize 0#u8)
    ⟨digest.val, digest.property⟩, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.bytes.sha3_256
    rw [hv, bind_tc_ok, vec_deref_eq, bind_tc_ok, hv1, bind_tc_ok, vec_deref_eq, bind_tc_ok,
      hdig, bind_tc_ok]
    exact copy_into_array_eq _ digest hdiglen
  · rw [Std.Array.from_slice_val _ ⟨digest.val, digest.property⟩ hdiglen, hdigv, hv1s]

/-- `SHA3-384` on byte strings: `h2b`, the bit-level hash, then `b2h`. -/
theorem sha3_384_bytes_eq (m : Slice Std.U8) (hm : 8 * m.val.length + 2 ≤ 4294965000) :
    ∃ out : Std.Array Std.U8 48#usize,
      hacspec_sha3_pedantic.bytes.sha3_384 m = ok out ∧
      out.val = b2hList (keccakCList 768 (h2bList m.val ++ [false, true]) 384) := by
  have hmb : 8 * m.val.length ≤ Std.Usize.max := by scalar_tac
  obtain ⟨v, hv, hvv⟩ := h2b_full_eq m hmb
  have hvs : (⟨v.val, v.property⟩ : Slice Bool).val = h2bList m.val := hvv
  obtain ⟨v1, hv1, hv1v⟩ := sha3_384_bits_eq ⟨v.val, v.property⟩ (by rw [hvs, h2bList_len]; omega)
  have hv1s : (⟨v1.val, v1.property⟩ : Slice Bool).val
      = keccakCList 768 (h2bList m.val ++ [false, true]) 384 := by
    rw [show (⟨v1.val, v1.property⟩ : Slice Bool).val = v1.val from rfl, hv1v, hvs]
  have hklen : (keccakCList 768 (h2bList m.val ++ [false, true]) 384).length = 384 :=
    keccakCList_len 768 _ 384 (by omega)
  obtain ⟨digest, hdig, hdigv⟩ := b2h_eq ⟨v1.val, v1.property⟩ (by rw [hv1s, hklen]; scalar_tac)
  have hdiglen : digest.val.length = (48#usize : Std.Usize).val := by
    rw [hdigv, hv1s, b2hList_len, hklen]
    norm_num
  refine ⟨Std.Array.from_slice (Std.Array.repeat 48#usize 0#u8)
    ⟨digest.val, digest.property⟩, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.bytes.sha3_384
    rw [hv, bind_tc_ok, vec_deref_eq, bind_tc_ok, hv1, bind_tc_ok, vec_deref_eq, bind_tc_ok,
      hdig, bind_tc_ok]
    exact copy_into_array_eq _ digest hdiglen
  · rw [Std.Array.from_slice_val _ ⟨digest.val, digest.property⟩ hdiglen, hdigv, hv1s]

/-- `SHA3-512` on byte strings: `h2b`, the bit-level hash, then `b2h`. -/
theorem sha3_512_bytes_eq (m : Slice Std.U8) (hm : 8 * m.val.length + 2 ≤ 4294965000) :
    ∃ out : Std.Array Std.U8 64#usize,
      hacspec_sha3_pedantic.bytes.sha3_512 m = ok out ∧
      out.val = b2hList (keccakCList 1024 (h2bList m.val ++ [false, true]) 512) := by
  have hmb : 8 * m.val.length ≤ Std.Usize.max := by scalar_tac
  obtain ⟨v, hv, hvv⟩ := h2b_full_eq m hmb
  have hvs : (⟨v.val, v.property⟩ : Slice Bool).val = h2bList m.val := hvv
  obtain ⟨v1, hv1, hv1v⟩ := sha3_512_bits_eq ⟨v.val, v.property⟩ (by rw [hvs, h2bList_len]; omega)
  have hv1s : (⟨v1.val, v1.property⟩ : Slice Bool).val
      = keccakCList 1024 (h2bList m.val ++ [false, true]) 512 := by
    rw [show (⟨v1.val, v1.property⟩ : Slice Bool).val = v1.val from rfl, hv1v, hvs]
  have hklen : (keccakCList 1024 (h2bList m.val ++ [false, true]) 512).length = 512 :=
    keccakCList_len 1024 _ 512 (by omega)
  obtain ⟨digest, hdig, hdigv⟩ := b2h_eq ⟨v1.val, v1.property⟩ (by rw [hv1s, hklen]; scalar_tac)
  have hdiglen : digest.val.length = (64#usize : Std.Usize).val := by
    rw [hdigv, hv1s, b2hList_len, hklen]
    norm_num
  refine ⟨Std.Array.from_slice (Std.Array.repeat 64#usize 0#u8)
    ⟨digest.val, digest.property⟩, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.bytes.sha3_512
    rw [hv, bind_tc_ok, vec_deref_eq, bind_tc_ok, hv1, bind_tc_ok, vec_deref_eq, bind_tc_ok,
      hdig, bind_tc_ok]
    exact copy_into_array_eq _ digest hdiglen
  · rw [Std.Array.from_slice_val _ ⟨digest.val, digest.property⟩ hdiglen, hdigv, hv1s]

/-- `SHAKE128` on byte strings, producing `out_bytes` bytes. -/
theorem shake128_bytes_eq (m : Slice Std.U8) (out_bytes : Std.Usize)
    (hob : 8 * out_bytes.val ≤ 4294965000)
    (hm : 8 * m.val.length + 4 ≤ 4294965000) :
    ∃ out : alloc.vec.Vec Std.U8,
      hacspec_sha3_pedantic.bytes.shake128 m out_bytes = ok out ∧
      out.val = b2hList (keccakCList 256 (h2bList m.val ++ [true, true, true, true])
        (8 * out_bytes.val)) := by
  have hmb : 8 * m.val.length ≤ Std.Usize.max := by scalar_tac
  obtain ⟨v, hv, hvv⟩ := h2b_full_eq m hmb
  have hvs : (⟨v.val, v.property⟩ : Slice Bool).val = h2bList m.val := hvv
  obtain ⟨i, hi, hiv⟩ := usize_mul_eq 8#usize out_bytes (by scalar_tac)
  have hin : i.val = 8 * out_bytes.val := by rw [hiv]; simp
  obtain ⟨v1, hv1, hv1v⟩ := shake128_bits_eq ⟨v.val, v.property⟩ i (by omega)
    (by rw [hvs, h2bList_len]; omega)
  have hv1s : (⟨v1.val, v1.property⟩ : Slice Bool).val
      = keccakCList 256 (h2bList m.val ++ [true, true, true, true]) (8 * out_bytes.val) := by
    rw [show (⟨v1.val, v1.property⟩ : Slice Bool).val = v1.val from rfl, hv1v, hvs, hin]
  have hklen : (keccakCList 256 (h2bList m.val ++ [true, true, true, true])
      (8 * out_bytes.val)).length = 8 * out_bytes.val :=
    keccakCList_len 256 _ _ (by omega)
  obtain ⟨digest, hdig, hdigv⟩ := b2h_eq ⟨v1.val, v1.property⟩ (by rw [hv1s, hklen]; scalar_tac)
  refine ⟨digest, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.bytes.shake128
    rw [hv, bind_tc_ok, vec_deref_eq, bind_tc_ok, hi, bind_tc_ok, hv1, bind_tc_ok,
      vec_deref_eq, bind_tc_ok]
    exact hdig
  · rw [hdigv, hv1s]

/-- `SHAKE256` on byte strings, producing `out_bytes` bytes. -/
theorem shake256_bytes_eq (m : Slice Std.U8) (out_bytes : Std.Usize)
    (hob : 8 * out_bytes.val ≤ 4294965000)
    (hm : 8 * m.val.length + 4 ≤ 4294965000) :
    ∃ out : alloc.vec.Vec Std.U8,
      hacspec_sha3_pedantic.bytes.shake256 m out_bytes = ok out ∧
      out.val = b2hList (keccakCList 512 (h2bList m.val ++ [true, true, true, true])
        (8 * out_bytes.val)) := by
  have hmb : 8 * m.val.length ≤ Std.Usize.max := by scalar_tac
  obtain ⟨v, hv, hvv⟩ := h2b_full_eq m hmb
  have hvs : (⟨v.val, v.property⟩ : Slice Bool).val = h2bList m.val := hvv
  obtain ⟨i, hi, hiv⟩ := usize_mul_eq 8#usize out_bytes (by scalar_tac)
  have hin : i.val = 8 * out_bytes.val := by rw [hiv]; simp
  obtain ⟨v1, hv1, hv1v⟩ := shake256_bits_eq ⟨v.val, v.property⟩ i (by omega)
    (by rw [hvs, h2bList_len]; omega)
  have hv1s : (⟨v1.val, v1.property⟩ : Slice Bool).val
      = keccakCList 512 (h2bList m.val ++ [true, true, true, true]) (8 * out_bytes.val) := by
    rw [show (⟨v1.val, v1.property⟩ : Slice Bool).val = v1.val from rfl, hv1v, hvs, hin]
  have hklen : (keccakCList 512 (h2bList m.val ++ [true, true, true, true])
      (8 * out_bytes.val)).length = 8 * out_bytes.val :=
    keccakCList_len 512 _ _ (by omega)
  obtain ⟨digest, hdig, hdigv⟩ := b2h_eq ⟨v1.val, v1.property⟩ (by rw [hv1s, hklen]; scalar_tac)
  refine ⟨digest, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.bytes.shake256
    rw [hv, bind_tc_ok, vec_deref_eq, bind_tc_ok, hi, bind_tc_ok, hv1, bind_tc_ok,
      vec_deref_eq, bind_tc_ok]
    exact hdig
  · rw [hdigv, hv1s]

-- Pin the six byte-level entry points to Lean's standard three axioms.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.sha3_224_bytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sha3_224_bytes_eq

/--
info: 'LibcruxIotSha3.Composition.Pedantic.sha3_256_bytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sha3_256_bytes_eq

/--
info: 'LibcruxIotSha3.Composition.Pedantic.sha3_384_bytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sha3_384_bytes_eq

/--
info: 'LibcruxIotSha3.Composition.Pedantic.sha3_512_bytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sha3_512_bytes_eq

/--
info: 'LibcruxIotSha3.Composition.Pedantic.shake128_bytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms shake128_bytes_eq

/--
info: 'LibcruxIotSha3.Composition.Pedantic.shake256_bytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms shake256_bytes_eq

end LibcruxIotSha3.Composition.Pedantic
