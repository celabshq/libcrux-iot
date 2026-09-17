import LibcruxIotSha3.Composition.Pedantic.LoopEq
/-!
# The pedantic χ (FIPS 202, Algorithm 4)

`hacspec_sha3_pedantic`'s step mappings are transcriptions of the FIPS 202
algorithms: three nested `for` loops writing one bit of a fresh output state per
iteration.  The extraction turns each `for` into an Aeneas `loop` fixpoint over
a `Range Usize` iterator, so a characterisation of the whole mapping is a
three-level loop-invariant proof.

This module does that for χ and lands on the shape every step mapping will have:

    step_mappings.chi A = ok (mkSA (chiBit (bitAt A)))

with `chiBit` the FIPS formula `A'[x,y,z] = A[x,y,z] ⊕ ((A[x+1,y,z] ⊕ 1) ⋅ A[x+2,y,z])`
written directly over the bit function of the state array.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-- FIPS 202, Algorithm 4 (χ), on the bit function of a state array. -/
def chiBit (f : Nat → Nat → Nat → Bool) (x y z : Nat) : Bool :=
  (f x y z).xor (!f ((x + 1) % 5) y z && f ((x + 2) % 5) y z)

/-! ### Writing a single bit

The extracted loop body reaches `out.a[x][y][z]` through two
`Array.index_mut_usize` calls and one `Array.update`; composing the two
write-backs with the update is exactly `setBit`. -/

/-- `A` with `A[x, y, z]` replaced by `b`. -/
def setBit (A : SA) (x y z : Std.Usize) (b : Bool) : SA :=
  { a := A.a.set x ((A.a.val[x.val]!).set y ((A.a.val[x.val]!.val[y.val]!).set z b)) }

theorem bitAt_setBit (A : SA) (x y z : Std.Usize) (b : Bool) (x' y' z' : Nat)
    (hx : x.val < 5) (hy : y.val < 5) (hz : z.val < 64)
    (hx' : x' < 5) (hy' : y' < 5) (hz' : z' < 64) :
    bitAt (setBit A x y z b) x' y' z'
      = if x' = x.val ∧ y' = y.val ∧ z' = z.val then b else bitAt A x' y' z' := by
  have hlen5 : A.a.val.length = 5 := by simp
  have hlen5' : (A.a.val[x.val]!).val.length = 5 := by simp
  have hlen64 : (A.a.val[x.val]!.val[y.val]!).val.length = 64 := by simp
  by_cases hxx : x' = x.val <;> by_cases hyy : y' = y.val <;> by_cases hzz : z' = z.val <;>
    simp_all [bitAt, setBit]

theorem chi_body_cont (A out : SA) (x y z : Std.Usize)
    (hx : x.val < 5) (hy : y.val < 5) (hz : z.val < 64) :
    ∃ s : Std.Usize, s.val = z.val + 1 ∧
      hacspec_sha3_pedantic.step_mappings.chi_loop0_loop0_loop0.body A x y
        { start := z, «end» := 64#usize } out
        = ok (.cont ({ start := s, «end» := 64#usize },
            setBit out x y z (chiBit (bitAt A) x.val y.val z.val))) := by
  obtain ⟨s, hs, hnext⟩ := range_next_lt z 64#usize (by simpa using hz)
  refine ⟨s, hs, ?_⟩
  unfold hacspec_sha3_pedantic.step_mappings.chi_loop0_loop0_loop0.body
  rw [hnext]
  obtain ⟨x1, hx1, hx1v⟩ := usize_add_eq x 1#usize (by scalar_tac)
  obtain ⟨x1m, hx1m, hx1mv⟩ := usize_rem_eq x1 5#usize (by simp)
  obtain ⟨x2, hx2, hx2v⟩ := usize_add_eq x 2#usize (by scalar_tac)
  obtain ⟨x2m, hx2m, hx2mv⟩ := usize_rem_eq x2 5#usize (by simp)
  have hb1 : x1m.val < (5#usize).val := by simp only [hx1mv]; simp; omega
  have hb2 : x2m.val < (5#usize).val := by simp only [hx2mv]; simp; omega
  simp [index_usize_eq _ _ hb1, index_usize_eq _ _ hb2,
    index_usize_eq, array_update_eq, Std.Array.index_mut_usize,
    hx1, hx2, hx1m, hx2m, hx1v, hx2v, hx1mv, hx2mv, hx, hy, hz, setBit, chiBit, bitAt]


theorem chi_body_done (A out : SA) (x y : Std.Usize) :
    hacspec_sha3_pedantic.step_mappings.chi_loop0_loop0_loop0.body A x y
      { start := 64#usize, «end» := 64#usize } out = ok (.done (A, out)) := by
  unfold hacspec_sha3_pedantic.step_mappings.chi_loop0_loop0_loop0.body
  rw [range_next_ge 64#usize 64#usize (le_refl _)]
  simp

/-- The innermost loop of χ writes the FIPS formula into the whole lane
    `out[x][y][·]` and leaves every other lane alone. -/
theorem chi_zloop (A out : SA) (x y : Std.Usize) (hx : x.val < 5) (hy : y.val < 5) :
    ∃ out' : SA,
      hacspec_sha3_pedantic.step_mappings.chi_loop0_loop0_loop0
          { start := 0#usize, «end» := 64#usize } A out x y = ok (A, out') ∧
      ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
        bitAt out' x' y' z'
          = if x' = x.val ∧ y' = y.val then chiBit (bitAt A) x' y' z'
            else bitAt out x' y' z' := by
  have h := loop_range_eq (β := SA) (γ := SA × SA)
    (fun p => hacspec_sha3_pedantic.step_mappings.chi_loop0_loop0_loop0.body A x y p.1 p.2)
    64#usize
    (fun zU acc r => r.1 = A ∧ ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
      bitAt r.2 x' y' z'
        = if x' = x.val ∧ y' = y.val ∧ zU.val ≤ z' then chiBit (bitAt A) x' y' z'
          else bitAt acc x' y' z')
    ?hstep ?hdone 64 0#usize out (by simp)
  case hstep =>
    intro i acc hi
    obtain ⟨s, hs, hbody⟩ := chi_body_cont A acc x y i hx hy (by simpa using hi)
    refine ⟨s, setBit acc x y i (chiBit (bitAt A) x.val y.val i.val), hs, hbody, ?_⟩
    rintro r ⟨hr1, hr2⟩
    refine ⟨hr1, fun x' hx' y' hy' z' hz' => ?_⟩
    rw [hr2 x' hx' y' hy' z' hz',
      bitAt_setBit acc x y i _ x' y' z' hx hy (by simpa using hi) hx' hy' hz']
    have hsv : s.val = i.val + 1 := hs
    split_ifs with h1 h2 h3 <;>
      first
        | rfl
        | (exfalso; omega)
        | omega
        | (congr 1 <;> omega)
  case hdone =>
    refine fun acc => ⟨(A, acc), chi_body_done A acc x y, rfl, fun x' _ y' _ z' hz' => ?_⟩
    have hne : ¬ (x' = x.val ∧ y' = y.val ∧ (64#usize).val ≤ z') := by
      simp only [not_and]
      intro _ _
      simp
      omega
    simp only [hne, if_false]
  obtain ⟨r, hr, hr1, hr2⟩ := h
  refine ⟨r.2, ?_, fun x' hx' y' hy' z' hz' => ?_⟩
  · unfold hacspec_sha3_pedantic.step_mappings.chi_loop0_loop0_loop0
    rw [show ((A, r.2) : SA × SA) = r by rw [← hr1]]
    exact hr
  · rw [hr2 x' hx' y' hy' z' hz']
    simp


/-! ### The `y` loop -/

theorem chi_ybody_cont (A out : SA) (x y : Std.Usize) (hx : x.val < 5) (hy : y.val < 5) :
    ∃ (s : Std.Usize) (out' : SA), s.val = y.val + 1 ∧
      hacspec_sha3_pedantic.step_mappings.chi_loop0_loop0.body x
          { start := y, «end» := 5#usize } A out
        = ok (.cont ({ start := s, «end» := 5#usize }, A, out')) ∧
      ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
        bitAt out' x' y' z'
          = if x' = x.val ∧ y' = y.val then chiBit (bitAt A) x' y' z'
            else bitAt out x' y' z' := by
  obtain ⟨s, hs, hnext⟩ := range_next_lt y 5#usize (by simpa using hy)
  obtain ⟨out', hloop, hbits⟩ := chi_zloop A out x y hx hy
  refine ⟨s, out', hs, ?_, hbits⟩
  unfold hacspec_sha3_pedantic.step_mappings.chi_loop0_loop0.body
  rw [hnext]
  simp [hloop]

theorem chi_ybody_done (A out : SA) (x : Std.Usize) :
    hacspec_sha3_pedantic.step_mappings.chi_loop0_loop0.body x
      { start := 5#usize, «end» := 5#usize } A out = ok (.done (A, out)) := by
  unfold hacspec_sha3_pedantic.step_mappings.chi_loop0_loop0.body
  rw [range_next_ge 5#usize 5#usize (le_refl _)]
  simp

theorem chi_yloop (A out : SA) (x : Std.Usize) (hx : x.val < 5) :
    ∃ out' : SA,
      hacspec_sha3_pedantic.step_mappings.chi_loop0_loop0
          { start := 0#usize, «end» := 5#usize } A out x = ok (A, out') ∧
      ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
        bitAt out' x' y' z'
          = if x' = x.val then chiBit (bitAt A) x' y' z' else bitAt out x' y' z' := by
  have h := loop_range_eq (β := SA × SA) (γ := SA × SA)
    (fun p => hacspec_sha3_pedantic.step_mappings.chi_loop0_loop0.body x p.1 p.2.1 p.2.2)
    5#usize
    (fun yU acc r => r.1 = acc.1 ∧ ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
      bitAt r.2 x' y' z'
        = if x' = x.val ∧ yU.val ≤ y' then chiBit (bitAt acc.1) x' y' z'
          else bitAt acc.2 x' y' z')
    ?hstep ?hdone 5 0#usize (A, out) (by simp)
  case hstep =>
    intro i acc hi
    obtain ⟨s, out', hs, hbody, hbits⟩ :=
      chi_ybody_cont acc.1 acc.2 x i hx (by simpa using hi)
    refine ⟨s, (acc.1, out'), hs, hbody, ?_⟩
    rintro r ⟨hr1, hr2⟩
    refine ⟨hr1, fun x' hx' y' hy' z' hz' => ?_⟩
    rw [hr2 x' hx' y' hy' z' hz', hbits x' hx' y' hy' z' hz']
    have hsv : s.val = i.val + 1 := hs
    split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega)
  case hdone =>
    refine fun acc => ⟨(acc.1, acc.2), ?_, rfl, fun x' _ y' hy' z' _ => ?_⟩
    · exact chi_ybody_done acc.1 acc.2 x
    · have hne : ¬ (x' = x.val ∧ (5#usize).val ≤ y') := by
        simp only [not_and]
        intro _
        simp
        omega
      simp only [hne, if_false]
  obtain ⟨r, hr, hr1, hr2⟩ := h
  refine ⟨r.2, ?_, fun x' hx' y' hy' z' hz' => ?_⟩
  · unfold hacspec_sha3_pedantic.step_mappings.chi_loop0_loop0
    have hr1' : r.1 = A := hr1
    rw [show ((A, r.2) : SA × SA) = r by cases r; simp_all]
    exact hr
  · rw [hr2 x' hx' y' hy' z' hz']
    simp


/-! ### The `x` loop, and χ itself -/

theorem chi_xbody_cont (A out : SA) (x : Std.Usize) (hx : x.val < 5) :
    ∃ (s : Std.Usize) (out' : SA), s.val = x.val + 1 ∧
      hacspec_sha3_pedantic.step_mappings.chi_loop0.body
          { start := x, «end» := 5#usize } A out
        = ok (.cont ({ start := s, «end» := 5#usize }, A, out')) ∧
      ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
        bitAt out' x' y' z'
          = if x' = x.val then chiBit (bitAt A) x' y' z' else bitAt out x' y' z' := by
  obtain ⟨s, hs, hnext⟩ := range_next_lt x 5#usize (by simpa using hx)
  obtain ⟨out', hloop, hbits⟩ := chi_yloop A out x hx
  refine ⟨s, out', hs, ?_, hbits⟩
  unfold hacspec_sha3_pedantic.step_mappings.chi_loop0.body
  rw [hnext]
  simp [hloop]

/-- χ (FIPS 202, Algorithm 4): the extracted three-loop nest computes exactly the
    FIPS formula, on every bit of the state array. -/
theorem chi_eq (A : SA) :
    hacspec_sha3_pedantic.step_mappings.chi A = ok (mkSA (chiBit (bitAt A))) := by
  have h := loop_range_eq (β := SA × SA) (γ := SA)
    (fun p => hacspec_sha3_pedantic.step_mappings.chi_loop0.body p.1 p.2.1 p.2.2)
    5#usize
    (fun xU acc r => ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
      bitAt r x' y' z'
        = if xU.val ≤ x' then chiBit (bitAt acc.1) x' y' z' else bitAt acc.2 x' y' z')
    ?hstep ?hdone 5 0#usize (A, mkSA fun _ _ _ => false) (by simp)
  case hstep =>
    intro i acc hi
    obtain ⟨s, out', hs, hbody, hbits⟩ := chi_xbody_cont acc.1 acc.2 i (by simpa using hi)
    refine ⟨s, (acc.1, out'), hs, hbody, ?_⟩
    intro r hr x' hx' y' hy' z' hz'
    rw [hr x' hx' y' hy' z' hz', hbits x' hx' y' hy' z' hz']
    have hsv : s.val = i.val + 1 := hs
    split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
  case hdone =>
    refine fun acc => ⟨acc.2, ?_, fun x' hx' y' _ z' _ => ?_⟩
    · unfold hacspec_sha3_pedantic.step_mappings.chi_loop0.body
      rw [range_next_ge 5#usize 5#usize (le_refl _)]
      simp
    · have hne : ¬ ((5#usize).val ≤ x') := by simp; omega
      simp only [hne, if_false]
  obtain ⟨r, hr, hbits⟩ := h
  unfold hacspec_sha3_pedantic.step_mappings.chi
  have hzero : hacspec_sha3_pedantic.state_array.StateArray.zero 64#usize
      = ok (mkSA fun _ _ _ => false) := by
    unfold hacspec_sha3_pedantic.state_array.StateArray.zero
    apply congrArg
    refine ext (fun x y z hx hy hz => ?_)
    rw [bitAt_mkSA _ hx hy hz]
    have h5 : (5#usize : Std.Usize).val = 5 := by simp
    have h64 : (64#usize : Std.Usize).val = 64 := by simp
    simp only [bitAt, Std.Array.repeat_val, List.getElem!_eq_getElem?_getD,
      List.getElem?_replicate, h5, h64, hx, hy, hz, if_true, Option.getD_some]
  rw [hzero]
  simp only [bind_tc_ok]
  unfold hacspec_sha3_pedantic.step_mappings.chi_loop0
  rw [hr]
  apply congrArg
  refine ext (fun x y z hx hy hz => ?_)
  rw [bitAt_mkSA _ hx hy hz, hbits x hx y hy z hz]
  simp

-- Pinned by `#guard_msgs`: the build fails if this comes to depend on any axiom
-- beyond Lean's standard three.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.chi_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms chi_eq

end LibcruxIotSha3.Composition.Pedantic
