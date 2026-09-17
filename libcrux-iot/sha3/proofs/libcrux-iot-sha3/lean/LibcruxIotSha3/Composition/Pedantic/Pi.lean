import LibcruxIotSha3.Composition.Pedantic.Grid
/-!
# The pedantic π (FIPS 202, Algorithm 3)

Same three-loop nest as χ, so the same proof skeleton: body equations plus the
three applications of `loop_range_eq`.  The formula is the lane permutation
`A'[x, y, z] = A[(x + 3y) mod 5, x, z]`, which is where the `Usize`
multiplication and the modulus enter.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-- FIPS 202, Algorithm 3 (π), on the bit function of a state array. -/
def piBit (f : Nat → Nat → Nat → Bool) (x y z : Nat) : Bool := f ((x + 3 * y) % 5) x z

theorem pi_body_cont (A out : SA) (x y z : Std.Usize)
    (hx : x.val < 5) (hy : y.val < 5) (hz : z.val < 64) :
    ∃ s : Std.Usize, s.val = z.val + 1 ∧
      hacspec_sha3_pedantic.step_mappings.pi_loop0_loop0_loop0.body A x y
        { start := z, «end» := 64#usize } out
        = ok (.cont ({ start := s, «end» := 64#usize },
            setBit out x y z (piBit (bitAt A) x.val y.val z.val))) := by
  obtain ⟨s, hs, hnext⟩ := range_next_lt z 64#usize (by simpa using hz)
  refine ⟨s, hs, ?_⟩
  unfold hacspec_sha3_pedantic.step_mappings.pi_loop0_loop0_loop0.body
  rw [hnext]
  obtain ⟨t, ht, htv⟩ := usize_mul_eq 3#usize y (by scalar_tac)
  obtain ⟨u, hu, huv⟩ := usize_add_eq x t (by scalar_tac)
  obtain ⟨m, hm, hmv⟩ := usize_rem_eq u 5#usize (by simp)
  have hbm : m.val < (5#usize).val := by simp only [hmv]; simp; omega
  simp [index_usize_eq _ _ hbm, index_usize_eq, array_update_eq,
    Std.Array.index_mut_usize, ht, hu, hm, htv, huv, hmv, hx, hy, hz, setBit, piBit, bitAt]

theorem pi_body_done (A out : SA) (x y : Std.Usize) :
    hacspec_sha3_pedantic.step_mappings.pi_loop0_loop0_loop0.body A x y
      { start := 64#usize, «end» := 64#usize } out = ok (.done (A, out)) := by
  unfold hacspec_sha3_pedantic.step_mappings.pi_loop0_loop0_loop0.body
  rw [range_next_ge 64#usize 64#usize (le_refl _)]
  simp

/-- The innermost loop of χ writes the FIPS permutation of the lanes into the whole lane
    `out[x][y][·]` and leaves every other lane alone. -/
theorem pi_zloop (A out : SA) (x y : Std.Usize) (hx : x.val < 5) (hy : y.val < 5) :
    ∃ out' : SA,
      hacspec_sha3_pedantic.step_mappings.pi_loop0_loop0_loop0
          { start := 0#usize, «end» := 64#usize } A out x y = ok (A, out') ∧
      ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
        bitAt out' x' y' z'
          = if x' = x.val ∧ y' = y.val then piBit (bitAt A) x' y' z'
            else bitAt out x' y' z' := by
  have h := loop_range_eq (β := SA) (γ := SA × SA)
    (fun p => hacspec_sha3_pedantic.step_mappings.pi_loop0_loop0_loop0.body A x y p.1 p.2)
    64#usize
    (fun zU acc r => r.1 = A ∧ ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
      bitAt r.2 x' y' z'
        = if x' = x.val ∧ y' = y.val ∧ zU.val ≤ z' then piBit (bitAt A) x' y' z'
          else bitAt acc x' y' z')
    ?hstep ?hdone 64 0#usize out (by simp)
  case hstep =>
    intro i acc hi
    obtain ⟨s, hs, hbody⟩ := pi_body_cont A acc x y i hx hy (by simpa using hi)
    refine ⟨s, setBit acc x y i (piBit (bitAt A) x.val y.val i.val), hs, hbody, ?_⟩
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
    refine fun acc => ⟨(A, acc), pi_body_done A acc x y, rfl, fun x' _ y' _ z' hz' => ?_⟩
    have hne : ¬ (x' = x.val ∧ y' = y.val ∧ (64#usize).val ≤ z') := by
      simp only [not_and]
      intro _ _
      simp
      omega
    simp only [hne, if_false]
  obtain ⟨r, hr, hr1, hr2⟩ := h
  refine ⟨r.2, ?_, fun x' hx' y' hy' z' hz' => ?_⟩
  · unfold hacspec_sha3_pedantic.step_mappings.pi_loop0_loop0_loop0
    rw [show ((A, r.2) : SA × SA) = r by rw [← hr1]]
    exact hr
  · rw [hr2 x' hx' y' hy' z' hz']
    simp


/-! ### The `y` loop -/

theorem pi_ybody_cont (A out : SA) (x y : Std.Usize) (hx : x.val < 5) (hy : y.val < 5) :
    ∃ (s : Std.Usize) (out' : SA), s.val = y.val + 1 ∧
      hacspec_sha3_pedantic.step_mappings.pi_loop0_loop0.body x
          { start := y, «end» := 5#usize } A out
        = ok (.cont ({ start := s, «end» := 5#usize }, A, out')) ∧
      ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
        bitAt out' x' y' z'
          = if x' = x.val ∧ y' = y.val then piBit (bitAt A) x' y' z'
            else bitAt out x' y' z' := by
  obtain ⟨s, hs, hnext⟩ := range_next_lt y 5#usize (by simpa using hy)
  obtain ⟨out', hloop, hbits⟩ := pi_zloop A out x y hx hy
  refine ⟨s, out', hs, ?_, hbits⟩
  unfold hacspec_sha3_pedantic.step_mappings.pi_loop0_loop0.body
  rw [hnext]
  simp [hloop]

theorem pi_ybody_done (A out : SA) (x : Std.Usize) :
    hacspec_sha3_pedantic.step_mappings.pi_loop0_loop0.body x
      { start := 5#usize, «end» := 5#usize } A out = ok (.done (A, out)) := by
  unfold hacspec_sha3_pedantic.step_mappings.pi_loop0_loop0.body
  rw [range_next_ge 5#usize 5#usize (le_refl _)]
  simp

theorem pi_yloop (A out : SA) (x : Std.Usize) (hx : x.val < 5) :
    ∃ out' : SA,
      hacspec_sha3_pedantic.step_mappings.pi_loop0_loop0
          { start := 0#usize, «end» := 5#usize } A out x = ok (A, out') ∧
      ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
        bitAt out' x' y' z'
          = if x' = x.val then piBit (bitAt A) x' y' z' else bitAt out x' y' z' := by
  have h := loop_range_eq (β := SA × SA) (γ := SA × SA)
    (fun p => hacspec_sha3_pedantic.step_mappings.pi_loop0_loop0.body x p.1 p.2.1 p.2.2)
    5#usize
    (fun yU acc r => r.1 = acc.1 ∧ ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
      bitAt r.2 x' y' z'
        = if x' = x.val ∧ yU.val ≤ y' then piBit (bitAt acc.1) x' y' z'
          else bitAt acc.2 x' y' z')
    ?hstep ?hdone 5 0#usize (A, out) (by simp)
  case hstep =>
    intro i acc hi
    obtain ⟨s, out', hs, hbody, hbits⟩ :=
      pi_ybody_cont acc.1 acc.2 x i hx (by simpa using hi)
    refine ⟨s, (acc.1, out'), hs, hbody, ?_⟩
    rintro r ⟨hr1, hr2⟩
    refine ⟨hr1, fun x' hx' y' hy' z' hz' => ?_⟩
    rw [hr2 x' hx' y' hy' z' hz', hbits x' hx' y' hy' z' hz']
    have hsv : s.val = i.val + 1 := hs
    split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega)
  case hdone =>
    refine fun acc => ⟨(acc.1, acc.2), ?_, rfl, fun x' _ y' hy' z' _ => ?_⟩
    · exact pi_ybody_done acc.1 acc.2 x
    · have hne : ¬ (x' = x.val ∧ (5#usize).val ≤ y') := by
        simp only [not_and]
        intro _
        simp
        omega
      simp only [hne, if_false]
  obtain ⟨r, hr, hr1, hr2⟩ := h
  refine ⟨r.2, ?_, fun x' hx' y' hy' z' hz' => ?_⟩
  · unfold hacspec_sha3_pedantic.step_mappings.pi_loop0_loop0
    have hr1' : r.1 = A := hr1
    rw [show ((A, r.2) : SA × SA) = r by cases r; simp_all]
    exact hr
  · rw [hr2 x' hx' y' hy' z' hz']
    simp


/-! ### The `x` loop, and χ itself -/

theorem pi_xbody_cont (A out : SA) (x : Std.Usize) (hx : x.val < 5) :
    ∃ (s : Std.Usize) (out' : SA), s.val = x.val + 1 ∧
      hacspec_sha3_pedantic.step_mappings.pi_loop0.body
          { start := x, «end» := 5#usize } A out
        = ok (.cont ({ start := s, «end» := 5#usize }, A, out')) ∧
      ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
        bitAt out' x' y' z'
          = if x' = x.val then piBit (bitAt A) x' y' z' else bitAt out x' y' z' := by
  obtain ⟨s, hs, hnext⟩ := range_next_lt x 5#usize (by simpa using hx)
  obtain ⟨out', hloop, hbits⟩ := pi_yloop A out x hx
  refine ⟨s, out', hs, ?_, hbits⟩
  unfold hacspec_sha3_pedantic.step_mappings.pi_loop0.body
  rw [hnext]
  simp [hloop]

/-- π (FIPS 202, Algorithm 3): the extracted three-loop nest computes exactly the
    FIPS formula, on every bit of the state array. -/
theorem pi_eq (A : SA) :
    hacspec_sha3_pedantic.step_mappings.pi A = ok (mkSA (piBit (bitAt A))) := by
  have h := loop_range_eq (β := SA × SA) (γ := SA)
    (fun p => hacspec_sha3_pedantic.step_mappings.pi_loop0.body p.1 p.2.1 p.2.2)
    5#usize
    (fun xU acc r => ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
      bitAt r x' y' z'
        = if xU.val ≤ x' then piBit (bitAt acc.1) x' y' z' else bitAt acc.2 x' y' z')
    ?hstep ?hdone 5 0#usize (A, mkSA fun _ _ _ => false) (by simp)
  case hstep =>
    intro i acc hi
    obtain ⟨s, out', hs, hbody, hbits⟩ := pi_xbody_cont acc.1 acc.2 i (by simpa using hi)
    refine ⟨s, (acc.1, out'), hs, hbody, ?_⟩
    intro r hr x' hx' y' hy' z' hz'
    rw [hr x' hx' y' hy' z' hz', hbits x' hx' y' hy' z' hz']
    have hsv : s.val = i.val + 1 := hs
    split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
  case hdone =>
    refine fun acc => ⟨acc.2, ?_, fun x' hx' y' _ z' _ => ?_⟩
    · unfold hacspec_sha3_pedantic.step_mappings.pi_loop0.body
      rw [range_next_ge 5#usize 5#usize (le_refl _)]
      simp
    · have hne : ¬ ((5#usize).val ≤ x') := by simp; omega
      simp only [hne, if_false]
  obtain ⟨r, hr, hbits⟩ := h
  unfold hacspec_sha3_pedantic.step_mappings.pi
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
  unfold hacspec_sha3_pedantic.step_mappings.pi_loop0
  rw [hr]
  apply congrArg
  refine ext (fun x y z hx hy hz => ?_)
  rw [bitAt_mkSA _ hx hy hz, hbits x hx y hy z hz]
  simp

-- Pinned by `#guard_msgs`: the build fails if this comes to depend on any axiom
-- beyond Lean's standard three.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.pi_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pi_eq

end LibcruxIotSha3.Composition.Pedantic
