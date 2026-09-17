import LibcruxIotSha3.Composition.Pedantic.Bits
/-!
# The `bits` module: `trunc`, `zeros`, `concat`, `xor`

Four one-line operations on bit strings, each extracted as a loop that pushes
one bit per iteration.  `push_loop_eq` handles the loop; what is left per
operation is the body equation and the arithmetic of the surrounding `massert`s.

The results are the obvious list operations -- a prefix, a run of zeros, an
append, a pointwise XOR -- which is what makes the sponge readable further up.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-- The empty `Vec`, as the spec's `Vec::new` produces it. -/
theorem vec_new_eq {α : Type} :
    alloc.vec.Vec.new α = ok (Aeneas.Std.alloc.vec.Vec.new α) := rfl

@[simp]
theorem vec_new_val {α : Type} : (Aeneas.Std.alloc.vec.Vec.new α).val = [] := rfl

theorem slice_len_eq {α : Type} (s : Slice α) :
    core.slice.Slice.len s = ok (Std.Usize.ofNatCore s.val.length (by scalar_tac)) := rfl

/-! ### `trunc` -/

theorem trunc_eq (x : Slice Bool) (s : Std.Usize) (hs : s.val ≤ x.val.length) :
    ∃ out : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.bits.trunc x s = ok out ∧ out.val = x.val.take s.val := by
  have hstep : ∀ (i : Std.Usize) (acc : alloc.vec.Vec Bool), i.val < s.val →
      acc.val = (Aeneas.Std.alloc.vec.Vec.new Bool).val
        ++ (List.range i.val).map (fun i => x.val[i]!) →
      ∃ (t : Std.Usize) (acc' : alloc.vec.Vec Bool), t.val = i.val + 1 ∧
        acc'.val = acc.val ++ [x.val[i.val]!] ∧
        hacspec_sha3_pedantic.bits.trunc_loop.body x { start := i, «end» := s } acc
          = ok (.cont ({ start := t, «end» := s }, acc')) := by
    intro i acc hi hinv
    obtain ⟨t, ht, hnext⟩ := range_next_lt i s hi
    have hlt : i.val < x.val.length := by omega
    have hxb : x.val.length ≤ Std.Usize.max := x.property
    have hacclen : acc.val.length = i.val := by rw [hinv]; simp
    refine ⟨t, ⟨acc.val ++ [x.val[i.val]!], by simp; omega⟩, ht, by simp, ?_⟩
    unfold hacspec_sha3_pedantic.bits.trunc_loop.body
    rw [hnext]
    simp [slice_index_usize_eq _ _ hlt, vec_push_eq acc _ (by omega)]
  have hdone : ∀ acc : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.bits.trunc_loop.body x { start := s, «end» := s } acc
        = ok (.done acc) := by
    intro acc
    unfold hacspec_sha3_pedantic.bits.trunc_loop.body
    rw [range_next_ge s s (le_refl _)]
    simp
  obtain ⟨out, hloop, hout⟩ := push_loop_eq
    (fun p => hacspec_sha3_pedantic.bits.trunc_loop.body x p.1 p.2)
    s (fun i => x.val[i]!) (Aeneas.Std.alloc.vec.Vec.new Bool) hstep hdone
  refine ⟨out, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.bits.trunc
    rw [slice_len_eq, bind_tc_ok]
    simp only [massert, if_pos (show s ≤ Std.Usize.ofNatCore x.val.length (by scalar_tac) from by
      simp only [Std.UScalar.le_equiv]; scalar_tac), bind_tc_ok, vec_new_eq]
    exact hloop
  · rw [hout]
    simp only [List.nil_append]
    apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_take]
    rw [getElem!_pos x.val i (by simp at h1; omega)]


/-! ### `zeros` -/

theorem zeros_eq (n : Std.Usize) :
    ∃ out : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.bits.zeros n = ok out ∧ out.val = List.replicate n.val false := by
  have hstep : ∀ (i : Std.Usize) (acc : alloc.vec.Vec Bool), i.val < n.val →
      acc.val = (Aeneas.Std.alloc.vec.Vec.new Bool).val
        ++ (List.range i.val).map (fun _ => false) →
      ∃ (t : Std.Usize) (acc' : alloc.vec.Vec Bool), t.val = i.val + 1 ∧
        acc'.val = acc.val ++ [false] ∧
        hacspec_sha3_pedantic.bits.zeros_loop.body { start := i, «end» := n } acc
          = ok (.cont ({ start := t, «end» := n }, acc')) := by
    intro i acc hi hinv
    obtain ⟨t, ht, hnext⟩ := range_next_lt i n hi
    have hacclen : acc.val.length = i.val := by rw [hinv]; simp
    have hnb : n.val ≤ Std.Usize.max := by scalar_tac
    refine ⟨t, ⟨acc.val ++ [false], by simp; omega⟩, ht, by simp, ?_⟩
    unfold hacspec_sha3_pedantic.bits.zeros_loop.body
    rw [hnext]
    simp [vec_push_eq acc _ (by omega)]
  have hdone : ∀ acc : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.bits.zeros_loop.body { start := n, «end» := n } acc
        = ok (.done acc) := by
    intro acc
    unfold hacspec_sha3_pedantic.bits.zeros_loop.body
    rw [range_next_ge n n (le_refl _)]
    simp
  obtain ⟨out, hloop, hout⟩ := push_loop_eq
    (fun p => hacspec_sha3_pedantic.bits.zeros_loop.body p.1 p.2)
    n (fun _ => false) (Aeneas.Std.alloc.vec.Vec.new Bool) hstep hdone
  refine ⟨out, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.bits.zeros
    rw [vec_new_eq]
    exact hloop
  · rw [hout]
    simp

/-! ### `concat` -/

theorem range_map_getElem (v : List Bool) (n : Nat) (hn : n = v.length) :
    (List.range n).map (fun i => v[i]!) = v := by
  subst hn
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [getElem!_pos v i (by simpa using h1)]

theorem concat_eq (x y : Slice Bool) (hb : x.val.length + y.val.length ≤ Std.Usize.max) :
    ∃ out : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.bits.concat x y = ok out ∧ out.val = x.val ++ y.val := by
  have hxn : (Std.Usize.ofNatCore x.val.length (by scalar_tac) : Std.Usize).val
      = x.val.length := by simp
  have hyn : (Std.Usize.ofNatCore y.val.length (by scalar_tac) : Std.Usize).val
      = y.val.length := by simp
  -- first loop: append `x`
  obtain ⟨out1, hloop0, hout1⟩ := push_loop_eq
    (fun p => hacspec_sha3_pedantic.bits.concat_loop0.body x p.1 p.2)
    (Std.Usize.ofNatCore x.val.length (by scalar_tac)) (fun i => x.val[i]!) (Aeneas.Std.alloc.vec.Vec.new Bool)
    (by
      intro i acc hi hinv
      have hlt : i.val < x.val.length := by rw [hxn] at hi; exact hi
      have hacclen : acc.val.length = i.val := by rw [hinv]; simp
      obtain ⟨t, ht, hnext⟩ := range_next_lt i _ hi
      refine ⟨t, ⟨acc.val ++ [x.val[i.val]!], by simp; omega⟩, ht, by simp, ?_⟩
      unfold hacspec_sha3_pedantic.bits.concat_loop0.body
      rw [hnext]
      simp [slice_index_usize_eq _ _ hlt, vec_push_eq acc _ (by omega)])
    (by
      intro acc
      unfold hacspec_sha3_pedantic.bits.concat_loop0.body
      rw [range_next_ge _ _ (le_refl _)]
      simp)
  have hout1' : out1.val = x.val := by
    rw [hout1, hxn, List.nil_append]
    exact range_map_getElem x.val x.val.length rfl
  -- second loop: append `y`
  obtain ⟨out2, hloop1, hout2⟩ := push_loop_eq
    (fun p => hacspec_sha3_pedantic.bits.concat_loop1.body y p.1 p.2)
    (Std.Usize.ofNatCore y.val.length (by scalar_tac)) (fun i => y.val[i]!) out1
    (by
      intro i acc hi hinv
      have hlt : i.val < y.val.length := by rw [hyn] at hi; exact hi
      have hacclen : acc.val.length = x.val.length + i.val := by
        rw [hinv, hout1']; simp
      obtain ⟨t, ht, hnext⟩ := range_next_lt i _ hi
      refine ⟨t, ⟨acc.val ++ [y.val[i.val]!], by simp; omega⟩, ht, by simp, ?_⟩
      unfold hacspec_sha3_pedantic.bits.concat_loop1.body
      rw [hnext]
      simp [slice_index_usize_eq _ _ hlt, vec_push_eq acc _ (by omega)])
    (by
      intro acc
      unfold hacspec_sha3_pedantic.bits.concat_loop1.body
      rw [range_next_ge _ _ (le_refl _)]
      simp)
  refine ⟨out2, ?_, ?_⟩
  · show (do
        let o1 ← hacspec_sha3_pedantic.bits.concat_loop0
          { start := 0#usize, «end» := Std.Usize.ofNatCore x.val.length (by scalar_tac) } x
          (Aeneas.Std.alloc.vec.Vec.new Bool)
        hacspec_sha3_pedantic.bits.concat_loop1
          { start := 0#usize, «end» := Std.Usize.ofNatCore y.val.length (by scalar_tac) } y o1)
        = ok out2
    unfold hacspec_sha3_pedantic.bits.concat_loop0
    rw [hloop0]
    exact hloop1
  · rw [hout2, hout1', hyn, range_map_getElem y.val y.val.length rfl]


/-! ### `xor` -/

theorem range_map_zip (u v : List Bool) (h : u.length = v.length) :
    (List.range u.length).map (fun i => u[i]! ^^ v[i]!) = List.zipWith (· ^^ ·) u v := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  have hi : i < u.length := by simpa using h1
  simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [getElem!_pos u i hi, getElem!_pos v i (by omega)]

theorem xor_eq (x y : Slice Bool) (hlen : x.val.length = y.val.length) :
    ∃ out : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.bits.xor x y = ok out ∧
      out.val = List.zipWith (· ^^ ·) x.val y.val := by
  have hxn : (Std.Usize.ofNatCore x.val.length (by scalar_tac) : Std.Usize).val
      = x.val.length := by simp
  obtain ⟨out, hloop, hout⟩ := push_loop_eq
    (fun p => hacspec_sha3_pedantic.bits.xor_loop.body x y p.1 p.2)
    (Std.Usize.ofNatCore x.val.length (by scalar_tac))
    (fun i => x.val[i]! ^^ y.val[i]!) (Aeneas.Std.alloc.vec.Vec.new Bool)
    (by
      intro i acc hi hinv
      have hlt : i.val < x.val.length := by rw [hxn] at hi; exact hi
      have hacclen : acc.val.length = i.val := by rw [hinv]; simp
      have hxb : x.val.length ≤ Std.Usize.max := x.property
      obtain ⟨t, ht, hnext⟩ := range_next_lt i _ hi
      refine ⟨t, ⟨acc.val ++ [x.val[i.val]! ^^ y.val[i.val]!], by simp; omega⟩, ht, by simp, ?_⟩
      unfold hacspec_sha3_pedantic.bits.xor_loop.body
      rw [hnext]
      simp [slice_index_usize_eq _ _ hlt, slice_index_usize_eq _ _ (show i.val < y.val.length by omega),
        vec_push_eq acc _ (by omega)])
    (by
      intro acc
      unfold hacspec_sha3_pedantic.bits.xor_loop.body
      rw [range_next_ge _ _ (le_refl _)]
      simp)
  refine ⟨out, ?_, ?_⟩
  · show hacspec_sha3_pedantic.bits.xor x y = ok out
    unfold hacspec_sha3_pedantic.bits.xor
    rw [slice_len_eq, bind_tc_ok, slice_len_eq, bind_tc_ok]
    simp only [massert, if_pos (show (Std.Usize.ofNatCore x.val.length (by scalar_tac) : Std.Usize)
        = Std.Usize.ofNatCore y.val.length (by scalar_tac) from
      (Std.UScalar.eq_equiv _ _).mpr (by simp [hlen])), bind_tc_ok, vec_new_eq]
    unfold hacspec_sha3_pedantic.bits.xor_loop
    exact hloop
  · rw [hout, hxn]
    simpa using range_map_zip x.val y.val hlen

end LibcruxIotSha3.Composition.Pedantic
