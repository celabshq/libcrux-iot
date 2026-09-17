import LibcruxIotSha3.Composition.Pedantic.BitsOps
/-!
# Bytes and bits (FIPS 202, App. B.1)

`h2b` and `b2h` convert between a byte string and a bit string, least
significant bit of each byte first (Algorithms 10 and 11).  `h2b` walks the
bytes and, for each, its eight bits; `b2h` does the reverse.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-- The eight bits of a byte, least significant first. -/
def byteBits (x : Std.U8) : List Bool := (List.range 8).map (fun j => x.bv.getLsbD j)

/-- A byte string as a bit string (FIPS 202, Algorithm 10). -/
def h2bList (h : List Std.U8) : List Bool := h.flatMap byteBits

theorem byteBits_len (x : Std.U8) : (byteBits x).length = 8 := by simp [byteBits]

/-- On a `u8`, `y &&& 1 = 1` exactly when bit 0 of `y` is set. -/
theorem and_one_iff (y : Std.U8) : ((y &&& 1#u8) = 1#u8) = (y.bv.getLsbD 0) := by
  apply propext
  constructor
  · intro hy
    have hbv : (y &&& 1#u8).bv = (1#u8 : Std.U8).bv := by rw [hy]
    rw [Std.UScalar.bv_and] at hbv
    have h0 := congrArg (fun v => BitVec.getLsbD v 0) hbv
    simpa using h0
  · intro hbit
    apply (Std.UScalar.eq_equiv_bv_eq _ _).mpr
    rw [Std.UScalar.bv_and]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [BitVec.getLsbD_and]
    have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by
      simp only [Std.UScalarTy.U8_numBits_eq] at hk
      omega
    rcases hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- The bit the spec extracts, `(x >> j) & 1 == 1`, is bit `j`. -/
theorem shift_and_one (x : Std.U8) (j : Std.I32) (hj : 0 ≤ j.val) (hjb : j.val < 8) :
    ∃ y : Std.U8, x >>> j = ok y ∧ ((y &&& 1#u8) = 1#u8) = x.bv.getLsbD j.val.toNat := by
  have hs := Std.U8.ShiftRight_IScalar_spec x j
  unfold WP.partialSpec at hs
  cases hxy : (x >>> j : RustM Std.U8) with
  | ok y =>
    rw [hxy] at hs
    obtain ⟨_, hbv, _⟩ := hs
    refine ⟨y, rfl, ?_⟩
    rw [and_one_iff]
    simp only [hbv, BitVec.getLsbD_ushiftRight, Std.IScalar.toNat]
    simp
  | fail e =>
    rw [hxy] at hs
    cases e <;> simp_all [Std.IScalar.toNat] <;> omega
  | div => rw [hxy] at hs; exact hs.elim



theorem range_map_getElem' {α : Type} [Inhabited α] (l : List α) :
    (List.range l.length).map (fun i => l[i]!) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [getElem!_pos l i (by simpa using h1)]

theorem flatMap_range_getElem {α β : Type} [Inhabited α] (l : List α) (f : α → List β) :
    (List.range l.length).flatMap (fun i => f l[i]!) = l.flatMap f := by
  have hmap : (List.range l.length).flatMap (fun i => f l[i]!)
      = ((List.range l.length).map (fun i => l[i]!)).flatMap f := by
    simp [List.flatMap_map]
  rw [hmap, range_map_getElem']

/-! ### `h2b` -/

theorem h2b_inner_eq (t : alloc.vec.Vec Bool) (byte : Std.U8)
    (ht : t.val.length + 8 ≤ Std.Usize.max) :
    ∃ t' : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.bits.h2b_loop0_loop0 { start := 0#i32, «end» := 8#i32 } t byte
        = ok t' ∧ t'.val = t.val ++ byteBits byte := by
  obtain ⟨out, hloop, hout⟩ := push_loop_eq_i32
    (fun q => hacspec_sha3_pedantic.bits.h2b_loop0_loop0.body byte q.1 q.2)
    8#i32 (by simp) (fun j => byte.bv.getLsbD j) t
    (by
      intro i acc hi0 hi hinv
      have hi8 : i.val < 8 := by simpa using hi
      obtain ⟨s, hs, hnext⟩ := range_next_lt_i32 i 8#i32 hi
      obtain ⟨y, hy, hyv⟩ := shift_and_one byte i hi0 hi8
      have hacclen : acc.val.length = t.val.length + i.val.toNat := by
        rw [hinv]; simp
      refine ⟨s, ⟨acc.val ++ [byte.bv.getLsbD i.val.toNat], by simp; omega⟩, hs, by simp, ?_⟩
      have hyd : decide ((y &&& 1#u8) = 1#u8) = byte.bv.getLsbD i.val.toNat := by
        simp only [hyv]
        simp
      unfold hacspec_sha3_pedantic.bits.h2b_loop0_loop0.body
      rw [hnext]
      simp [hy, Aeneas.Std.lift, vec_push_eq acc _ (by omega), hyd])
    (by
      intro acc
      unfold hacspec_sha3_pedantic.bits.h2b_loop0_loop0.body
      rw [range_next_ge_i32 8#i32 8#i32 (le_refl _)]
      simp)
  refine ⟨out, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.bits.h2b_loop0_loop0
    exact hloop
  · rw [hout]
    simp [byteBits]

theorem h2b_outer_eq (h : Slice Std.U8) (hb : 8 * h.val.length ≤ Std.Usize.max) :
    ∃ t : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.bits.h2b_loop0
          { start := 0#usize, «end» := Std.Usize.ofNatCore h.val.length (by scalar_tac) } h
          (Aeneas.Std.alloc.vec.Vec.new Bool) = ok t ∧
      t.val = h2bList h.val := by
  obtain ⟨out, hloop, hout⟩ := append_loop_eq
    (fun q => hacspec_sha3_pedantic.bits.h2b_loop0.body h q.1 q.2)
    (Std.Usize.ofNatCore h.val.length (by scalar_tac))
    (fun i => byteBits h.val[i]!) (Aeneas.Std.alloc.vec.Vec.new Bool)
    (by
      intro i acc hi hinv
      have hi' : i.val < h.val.length := by simpa using hi
      obtain ⟨s, hs, hnext⟩ := range_next_lt i _ hi
      have hacclen : acc.val.length = 8 * i.val := by
        rw [hinv]
        simp only [vec_new_val, List.nil_append, List.length_flatMap]
        rw [show (List.range i.val).map (fun j => (byteBits h.val[j]!).length)
            = (List.range i.val).map (fun _ => 8) from by
          apply List.map_congr_left
          intro j _
          exact byteBits_len _]
        simp
        omega
      obtain ⟨t', hinner, hinnerv⟩ := h2b_inner_eq acc h.val[i.val]! (by omega)
      refine ⟨s, t', hs, hinnerv, ?_⟩
      unfold hacspec_sha3_pedantic.bits.h2b_loop0.body
      rw [hnext]
      simp only [List.getElem!_eq_getElem?_getD] at hinner
      simp [slice_index_usize_eq _ _ hi', hinner])
    (by
      intro acc
      unfold hacspec_sha3_pedantic.bits.h2b_loop0.body
      rw [range_next_ge _ _ (le_refl _)]
      simp)
  refine ⟨out, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.bits.h2b_loop0
    exact hloop
  · rw [hout]
    simp only [vec_new_val, List.nil_append, h2bList]
    rw [show (Std.Usize.ofNatCore h.val.length (by scalar_tac) : Std.Usize).val
        = h.val.length from rfl]
    exact flatMap_range_getElem h.val byteBits


theorem h2bList_len (h : List Std.U8) : (h2bList h).length = 8 * h.length := by
  simp only [h2bList, List.length_flatMap]
  rw [show h.map (fun x => (byteBits x).length) = h.map (fun _ => 8) from by
    apply List.map_congr_left
    intro x _
    exact byteBits_len x]
  simp [Nat.mul_comm]

/-- FIPS 202, Algorithm 10: the first `n` bits of a byte string. -/
theorem h2b_eq (h : Slice Std.U8) (n : Std.Usize) (hn : n.val ≤ 8 * h.val.length)
    (hb : 8 * h.val.length ≤ Std.Usize.max) :
    ∃ out : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.bits.h2b h n = ok out ∧
      out.val = (h2bList h.val).take n.val := by
  obtain ⟨t, hloop, htv⟩ := h2b_outer_eq h hb
  obtain ⟨m, hm, hmv⟩ := usize_mul_eq 8#usize
    (Std.Usize.ofNatCore h.val.length (by scalar_tac)) (by simp; omega)
  have hmn : m.val = 8 * h.val.length := by rw [hmv]; simp
  obtain ⟨out, hout, houtv⟩ := trunc_eq t n (by rw [htv, h2bList_len]; omega)
  refine ⟨out, ?_, by rw [houtv, htv]⟩
  unfold hacspec_sha3_pedantic.bits.h2b
  rw [slice_len_eq, bind_tc_ok, hm, bind_tc_ok]
  simp only [massert, if_pos (show n ≤ m from (Std.UScalar.le_equiv n m).mpr (by omega)),
    bind_tc_ok, vec_new_eq]
  show (do
      let t1 ← hacspec_sha3_pedantic.bits.h2b_loop0
        { start := 0#usize, «end» := Std.Usize.ofNatCore h.val.length (by scalar_tac) } h
        (Aeneas.Std.alloc.vec.Vec.new Bool)
      hacspec_sha3_pedantic.bits.trunc ⟨t1.val, t1.property⟩ n) = ok out
  rw [hloop, bind_tc_ok]
  exact hout

/-- FIPS 202, Algorithm 10 on a whole byte string. -/
theorem h2b_full_eq (h : Slice Std.U8) (hb : 8 * h.val.length ≤ Std.Usize.max) :
    ∃ out : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.bits.h2b_full h = ok out ∧ out.val = h2bList h.val := by
  obtain ⟨m, hm, hmv⟩ := usize_mul_eq 8#usize
    (Std.Usize.ofNatCore h.val.length (by scalar_tac)) (by simp; omega)
  have hmn : m.val = 8 * h.val.length := by rw [hmv]; simp
  obtain ⟨out, hout, houtv⟩ := h2b_eq h m (by omega) hb
  refine ⟨out, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.bits.h2b_full
    rw [slice_len_eq, bind_tc_ok, hm, bind_tc_ok]
    exact hout
  · rw [houtv, hmn, ← h2bList_len h.val]
    simp

end LibcruxIotSha3.Composition.Pedantic
