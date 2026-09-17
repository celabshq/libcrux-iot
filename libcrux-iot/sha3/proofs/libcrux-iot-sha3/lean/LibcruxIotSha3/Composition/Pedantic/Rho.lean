import LibcruxIotSha3.Composition.Pedantic.Grid
/-!
# The pedantic ρ (FIPS 202, Algorithm 2)

ρ is the odd one out among the step mappings.  The others write every lane with
one formula; ρ *walks* the lanes, `(x, y) ← (y, (2x + 3y) mod 5)` starting at
`(1, 0)`, rotating the lane reached at step `t` by `(t+1)(t+2)/2`, and leaving
`A[0, 0]` alone (Algorithm 2, steps 1-3).  The extraction keeps that shape: the
outer loop runs over `i64` and carries `(x, y)` as loop state.

So the characterisation needs the walk as a Lean function, and three finite
facts about it -- it stays in range, it is injective, and it covers every lane
but `(0, 0)` -- each settled by `decide` over the 24 steps rather than by hand.
With `rhoOffsetOf` (the offset of the lane, `0` for the lane off the walk) the
result is the usual shape,

    step_mappings.rho A = ok (mkSA (rhoBit (bitAt A)))

and `rhoBit f x y z = f x y ((z - rhoOffsetOf x y) mod 64)` is FIPS 202's
`A'[x, y, z] = A[x, y, (z - (t+1)(t+2)/2) mod w]`.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-! ### The walk -/

/-- FIPS 202, Algorithm 2 step 3: the lane visited at step `t`, starting from
    `(x, y) = (1, 0)`. -/
def rhoWalk : Nat → Nat × Nat
  | 0 => (1, 0)
  | t + 1 => ((rhoWalk t).2, (2 * (rhoWalk t).1 + 3 * (rhoWalk t).2) % 5)

/-- FIPS 202, Algorithm 2 step 3: the rotation applied at step `t`. -/
def rhoOffset (t : Nat) : Nat := (t + 1) * (t + 2) / 2

/-- The step at which the walk reaches `(x, y)`, if it ever does.  `(0, 0)` is
    the one lane it misses -- the one ρ leaves alone. -/
def rhoStepOf (x y : Nat) : Option Nat :=
  (List.range 24).find? (fun t => rhoWalk t = (x, y))

/-- The rotation of the lane at `(x, y)`: the offset of the step that reaches
    it, and `0` for `(0, 0)`, which ρ copies unchanged. -/
def rhoOffsetOf (x y : Nat) : Nat :=
  match rhoStepOf x y with
  | some t => rhoOffset t
  | none => 0

/-- `(z - off) mod 64`, on naturals. -/
def rotIndex (off z : Nat) : Nat := (z + (64 - off % 64)) % 64

/-- FIPS 202, Algorithm 2, as a function of the bits. -/
def rhoBit (f : Nat → Nat → Nat → Bool) (x y z : Nat) : Bool :=
  f x y (rotIndex (rhoOffsetOf x y) z)

/-! ### The three finite facts

The walk is 24 steps long, so these are decided rather than argued. -/

theorem rhoWalk_lt : ∀ t < 24, (rhoWalk t).1 < 5 ∧ (rhoWalk t).2 < 5 := by decide

theorem rhoStepOf_walk : ∀ t < 24, rhoStepOf (rhoWalk t).1 (rhoWalk t).2 = some t := by decide

theorem rhoStepOf_none : ∀ x < 5, ∀ y < 5, rhoStepOf x y = none → x = 0 ∧ y = 0 := by decide

theorem rhoStepOf_lt : ∀ x < 5, ∀ y < 5, ∀ t, rhoStepOf x y = some t → t < 24 := by decide

theorem rhoStepOf_eq : ∀ x < 5, ∀ y < 5, ∀ t, rhoStepOf x y = some t → rhoWalk t = (x, y) := by
  decide

theorem rotIndex_zero (z : Nat) (hz : z < 64) : rotIndex 0 z = z := by
  simp [rotIndex]
  omega


/-! ### Step 1: the lane `A[0, 0]` is copied -/

theorem rho0_body_cont (A out : SA) (z : Std.Usize) (hz : z.val < 64) :
    ∃ s : Std.Usize, s.val = z.val + 1 ∧
      hacspec_sha3_pedantic.step_mappings.rho_loop0.body A
          { start := z, «end» := 64#usize } out
        = ok (.cont ({ start := s, «end» := 64#usize },
            setBit out 0#usize 0#usize z (bitAt A 0 0 z.val))) := by
  obtain ⟨s, hs, hnext⟩ := range_next_lt z 64#usize (by simpa using hz)
  refine ⟨s, hs, ?_⟩
  unfold hacspec_sha3_pedantic.step_mappings.rho_loop0.body
  rw [hnext]
  simp [index_usize_eq, array_update_eq, Std.Array.index_mut_usize, hz, setBit, bitAt]

theorem rho0_body_done (A out : SA) :
    hacspec_sha3_pedantic.step_mappings.rho_loop0.body A
      { start := 64#usize, «end» := 64#usize } out = ok (.done (A, out)) := by
  unfold hacspec_sha3_pedantic.step_mappings.rho_loop0.body
  rw [range_next_ge 64#usize 64#usize (le_refl _)]
  simp

theorem rho0_zloop (A out : SA) :
    ∃ out' : SA,
      hacspec_sha3_pedantic.step_mappings.rho_loop0
          { start := 0#usize, «end» := 64#usize } A out = ok (A, out') ∧
      ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
        bitAt out' x' y' z'
          = if x' = 0 ∧ y' = 0 then bitAt A 0 0 z' else bitAt out x' y' z' := by
  have h := loop_range_eq (β := SA) (γ := SA × SA)
    (fun p => hacspec_sha3_pedantic.step_mappings.rho_loop0.body A p.1 p.2)
    64#usize
    (fun zU acc r => r.1 = A ∧ ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
      bitAt r.2 x' y' z'
        = if x' = 0 ∧ y' = 0 ∧ zU.val ≤ z' then bitAt A 0 0 z' else bitAt acc x' y' z')
    ?hstep ?hdone 64 0#usize out (by simp)
  case hstep =>
    intro i acc hi
    obtain ⟨s, hs, hbody⟩ := rho0_body_cont A acc i (by simpa using hi)
    refine ⟨s, setBit acc 0#usize 0#usize i (bitAt A 0 0 i.val), hs, hbody, ?_⟩
    rintro r ⟨hr1, hr2⟩
    refine ⟨hr1, fun x' hx' y' hy' z' hz' => ?_⟩
    rw [hr2 x' hx' y' hy' z' hz',
      bitAt_setBit acc 0#usize 0#usize i _ x' y' z' (by simp) (by simp)
        (by simpa using hi) hx' hy' hz']
    have hsv : s.val = i.val + 1 := hs
    have h0 : (0#usize : Std.Usize).val = 0 := by simp
    split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega) | (congr 1; omega)
  case hdone =>
    refine fun acc => ⟨(A, acc), rho0_body_done A acc, rfl, fun x' _ y' _ z' hz' => ?_⟩
    have hne : ¬ (x' = 0 ∧ y' = 0 ∧ (64#usize).val ≤ z') := by
      simp only [not_and]
      intro _ _
      simp
      omega
    simp only [hne, if_false]
  obtain ⟨r, hr, hr1, hr2⟩ := h
  refine ⟨r.2, ?_, fun x' hx' y' hy' z' hz' => ?_⟩
  · unfold hacspec_sha3_pedantic.step_mappings.rho_loop0
    rw [show ((A, r.2) : SA × SA) = r by rw [← hr1]]
    exact hr
  · rw [hr2 x' hx' y' hy' z' hz']
    simp


/-! ### Step 3: one lane of the walk, rotated -/

theorem rho1_body_cont (A out : SA) (w : Std.I64) (hw : w.val = 64)
    (x y : Std.Usize) (hx : x.val < 5) (hy : y.val < 5)
    (offset : Std.I64) (off : Nat) (hoff : offset.val = (off : Int)) (hoffb : off < 1000)
    (z : Std.Usize) (hz : z.val < 64) :
    ∃ s : Std.Usize, s.val = z.val + 1 ∧
      hacspec_sha3_pedantic.step_mappings.rho_loop1_loop0.body A w x y offset
          { start := z, «end» := 64#usize } out
        = ok (.cont ({ start := s, «end» := 64#usize },
            setBit out x y z (bitAt A x.val y.val (rotIndex off z.val)))) := by
  obtain ⟨s, hs, hnext⟩ := range_next_lt z 64#usize (by simpa using hz)
  refine ⟨s, hs, ?_⟩
  unfold hacspec_sha3_pedantic.step_mappings.rho_loop1_loop0.body
  rw [hnext]
  have hmaxI : Std.IScalar.max Std.IScalarTy.I64 = 9223372036854775807 := by
    rw [Std.IScalar.max_IScalarTy_I64_eq, Std.I64.max_eq]
  have hminI : Std.IScalar.min Std.IScalarTy.I64 = -9223372036854775808 := by
    rw [Std.IScalar.min_IScalarTy_I64_eq, Std.I64.min_eq]
  have hminN : Std.I64.min = -9223372036854775808 := Std.I64.min_eq
  have hzn : (z.val : Int) < 64 := by exact_mod_cast hz
  have hoffn : (off : Int) < 1000 := by exact_mod_cast hoffb
  obtain ⟨zi, hzi, hziv⟩ := usize_to_i64 z (by scalar_tac)
  obtain ⟨d, hd, hdv⟩ := i64_sub_eq zi offset (by omega) (by omega)
  obtain ⟨m, hm, hmv⟩ := imod_eq d w (by omega) (by omega) (by omega) (by rw [hw]; scalar_tac)
  have hmn : m.val = rotIndex off z.val := by
    have hme : (m.val : Int) = ((z.val : Int) - (off : Int)) % 64 := by
      rw [hmv, hdv, hziv, hoff, hw]
    simp only [rotIndex]
    omega
  have hbm : m.val < (64#usize).val := by
    simp only [hmn, rotIndex]
    simp
    omega
  have hma : y.val < 5 := hy
  simp [hzi, hd, hm, index_usize_eq _ _ hbm, index_usize_eq, array_update_eq,
    Std.Array.index_mut_usize, massert, hma, hmn, hx, hz, setBit, bitAt]

theorem rho1_body_done (A out : SA) (w : Std.I64) (x y : Std.Usize) (offset : Std.I64) :
    hacspec_sha3_pedantic.step_mappings.rho_loop1_loop0.body A w x y offset
      { start := 64#usize, «end» := 64#usize } out = ok (.done (A, out)) := by
  unfold hacspec_sha3_pedantic.step_mappings.rho_loop1_loop0.body
  rw [range_next_ge 64#usize 64#usize (le_refl _)]
  simp

theorem rho1_zloop (A out : SA) (w : Std.I64) (hw : w.val = 64)
    (x y : Std.Usize) (hx : x.val < 5) (hy : y.val < 5)
    (offset : Std.I64) (off : Nat) (hoff : offset.val = (off : Int)) (hoffb : off < 1000) :
    ∃ out' : SA,
      hacspec_sha3_pedantic.step_mappings.rho_loop1_loop0
          { start := 0#usize, «end» := 64#usize } A w out x y offset = ok (A, out') ∧
      ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
        bitAt out' x' y' z'
          = if x' = x.val ∧ y' = y.val then bitAt A x' y' (rotIndex off z')
            else bitAt out x' y' z' := by
  have h := loop_range_eq (β := SA) (γ := SA × SA)
    (fun p => hacspec_sha3_pedantic.step_mappings.rho_loop1_loop0.body A w x y offset p.1 p.2)
    64#usize
    (fun zU acc r => r.1 = A ∧ ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
      bitAt r.2 x' y' z'
        = if x' = x.val ∧ y' = y.val ∧ zU.val ≤ z' then bitAt A x' y' (rotIndex off z')
          else bitAt acc x' y' z')
    ?hstep ?hdone 64 0#usize out (by simp)
  case hstep =>
    intro i acc hi
    obtain ⟨s, hs, hbody⟩ :=
      rho1_body_cont A acc w hw x y hx hy offset off hoff hoffb i (by simpa using hi)
    refine ⟨s, setBit acc x y i (bitAt A x.val y.val (rotIndex off i.val)), hs, hbody, ?_⟩
    rintro r ⟨hr1, hr2⟩
    refine ⟨hr1, fun x' hx' y' hy' z' hz' => ?_⟩
    rw [hr2 x' hx' y' hy' z' hz',
      bitAt_setBit acc x y i _ x' y' z' hx hy (by simpa using hi) hx' hy' hz']
    have hsv : s.val = i.val + 1 := hs
    split_ifs with h1 h2 h3 <;>
      first | rfl | (exfalso; omega) | (congr 2 <;> omega)
  case hdone =>
    refine fun acc => ⟨(A, acc), rho1_body_done A acc w x y offset, rfl,
      fun x' _ y' _ z' hz' => ?_⟩
    have hne : ¬ (x' = x.val ∧ y' = y.val ∧ (64#usize).val ≤ z') := by
      simp only [not_and]
      intro _ _
      simp
      omega
    simp only [hne, if_false]
  obtain ⟨r, hr, hr1, hr2⟩ := h
  refine ⟨r.2, ?_, fun x' hx' y' hy' z' hz' => ?_⟩
  · unfold hacspec_sha3_pedantic.step_mappings.rho_loop1_loop0
    rw [show ((A, r.2) : SA × SA) = r by rw [← hr1]]
    exact hr
  · rw [hr2 x' hx' y' hy' z' hz']
    simp


/-! ### One step of the walk -/

theorem rho1_body_step (A out : SA) (w : Std.I64) (hw : w.val = 64)
    (x y : Std.Usize) (n : Nat) (hn : n < 24) (hxy : (x.val, y.val) = rhoWalk n)
    (t : Std.I64) (ht : t.val = (n : Int)) :
    ∃ (s : Std.I64) (out' : SA) (ny : Std.Usize),
      s.val = t.val + 1 ∧ ny.val = (2 * x.val + 3 * y.val) % 5 ∧
      hacspec_sha3_pedantic.step_mappings.rho_loop1.body w
          { start := t, «end» := 24#i64 } A out x y
        = ok (.cont ({ start := s, «end» := 24#i64 }, A, out', y, ny)) ∧
      (∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
        bitAt out' x' y' z'
          = if x' = x.val ∧ y' = y.val then bitAt A x' y' (rotIndex (rhoOffset n) z')
            else bitAt out x' y' z') := by
  have hxlt : x.val < 5 := by
    have := (rhoWalk_lt n hn).1; rw [← hxy] at this; exact this
  have hylt : y.val < 5 := by
    have := (rhoWalk_lt n hn).2; rw [← hxy] at this; exact this
  have hnn : (n : Int) < 24 := by exact_mod_cast hn
  have hmaxI : Std.IScalar.max Std.IScalarTy.I64 = 9223372036854775807 := by
    rw [Std.IScalar.max_IScalarTy_I64_eq, Std.I64.max_eq]
  have hminI : Std.IScalar.min Std.IScalarTy.I64 = -9223372036854775808 := by
    rw [Std.IScalar.min_IScalarTy_I64_eq, Std.I64.min_eq]
  have hminN : Std.I64.min = -9223372036854775808 := Std.I64.min_eq
  have hmaxN : Std.I64.max = 9223372036854775807 := Std.I64.max_eq
  obtain ⟨s, hs, hnext⟩ := range_next_lt_i64 t 24#i64 (by simp; omega)
  -- the offset `(t+1)(t+2)/2`
  obtain ⟨p1, hp1, hp1v⟩ := i64_add_eq t 1#i64 (by simp; omega) (by simp; omega)
  obtain ⟨p2, hp2, hp2v⟩ := i64_add_eq t 2#i64 (by simp; omega) (by simp; omega)
  have hp1n : p1.val = ((n + 1 : Nat) : Int) := by rw [hp1v, ht]; push_cast; simp
  have hp2n : p2.val = ((n + 2 : Nat) : Int) := by rw [hp2v, ht]; push_cast; simp
  have hprodb : (n + 1) * (n + 2) ≤ 600 := by
    have hle := Nat.mul_le_mul (show n + 1 ≤ 24 by omega) (show n + 2 ≤ 25 by omega)
    omega
  have hprod : p1.val * p2.val = (((n + 1) * (n + 2) : Nat) : Int) := by
    rw [hp1n, hp2n]; push_cast; ring
  have hmul_lb : Std.IScalar.min Std.IScalarTy.I64 ≤ p1.val * p2.val := by rw [hprod]; omega
  have hmul_ub : p1.val * p2.val ≤ Std.IScalar.max Std.IScalarTy.I64 := by rw [hprod]; omega
  obtain ⟨pm, hpm, hpmv⟩ := i64_mul_eq p1 p2 hmul_lb hmul_ub
  have hpmn : pm.val = (((n + 1) * (n + 2) : Nat) : Int) := by rw [hpmv, hprod]
  obtain ⟨off, hoffeq, hoffv⟩ := i64_div_eq pm 2#i64 (by simp) (by rw [hpmn]; omega)
  have hoffn : off.val = (rhoOffset n : Int) := by
    rw [hoffv, hpmn]
    show Int.tdiv (((n + 1) * (n + 2) : Nat) : Int) ((2 : Nat) : Int) = (rhoOffset n : Int)
    rw [show Int.tdiv (((n + 1) * (n + 2) : Nat) : Int) ((2 : Nat) : Int)
        = ((((n + 1) * (n + 2)) / 2 : Nat) : Int) from rfl]
    rfl
  obtain ⟨out', hzloop, hbits⟩ :=
    rho1_zloop A out w hw x y hxlt hylt off (rhoOffset n) hoffn
      (by simp only [rhoOffset]; omega)
  -- the next lane of the walk
  obtain ⟨u1, hu1, hu1v⟩ := usize_mul_eq 2#usize x (by scalar_tac)
  obtain ⟨u2, hu2, hu2v⟩ := usize_mul_eq 3#usize y (by scalar_tac)
  obtain ⟨u3, hu3, hu3v⟩ := usize_add_eq u1 u2 (by scalar_tac)
  obtain ⟨ny, hny, hnyv⟩ := usize_rem_eq u3 5#usize (by simp)
  refine ⟨s, out', ny, hs, ?_, ?_, hbits⟩
  · rw [hnyv, hu3v, hu1v, hu2v]
    simp
  · unfold hacspec_sha3_pedantic.step_mappings.rho_loop1.body
    rw [hnext]
    simp [hp1, hp2, hpm, hoffeq, hzloop, hu1, hu2, hu3, hny]


/-! ### The walk loop -/

theorem rho1_tloop (A out : SA) (w : Std.I64) (hw : w.val = 64) :
    ∃ r : SA,
      hacspec_sha3_pedantic.step_mappings.rho_loop1
          { start := 0#i64, «end» := 24#i64 } A w out 1#usize 0#usize = ok r ∧
      ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
        bitAt r x' y' z' =
          match rhoStepOf x' y' with
          | some t => bitAt A x' y' (rotIndex (rhoOffset t) z')
          | none => bitAt out x' y' z' := by
  have h := loop_range_eq_inv_i64 (β := SA × SA × Std.Usize × Std.Usize) (γ := SA)
    (fun p => hacspec_sha3_pedantic.step_mappings.rho_loop1.body w p.1 p.2.1 p.2.2.1
      p.2.2.2.1 p.2.2.2.2)
    24#i64
    (fun t acc => acc.1 = A ∧ 0 ≤ t.val ∧ t.val ≤ 24 ∧
      (acc.2.2.1.val, acc.2.2.2.val) = rhoWalk t.val.toNat)
    (fun t acc r => ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
      bitAt r x' y' z' =
        match rhoStepOf x' y' with
        | some t' => if t.val.toNat ≤ t' then bitAt A x' y' (rotIndex (rhoOffset t') z')
                     else bitAt acc.2.1 x' y' z'
        | none => bitAt acc.2.1 x' y' z')
    ?hstep ?hdone 24 0#i64 (A, out, 1#usize, 0#usize) (by simp)
    ⟨rfl, by simp, by simp, by simp [rhoWalk]⟩
  case hstep =>
    rintro t acc hlt ⟨hA, ht0, ht24, hwalk⟩
    have h24 : (24#i64 : Std.I64).val = 24 := by simp
    have hn : t.val.toNat < 24 := by omega
    have htn : t.val = (t.val.toNat : Int) := by omega
    obtain ⟨s, out', ny, hs, hnyv, hbody, hbits⟩ :=
      rho1_body_step acc.1 acc.2.1 w hw acc.2.2.1 acc.2.2.2 t.val.toNat hn hwalk t htn
    refine ⟨s, (acc.1, out', acc.2.2.2, ny), hs, ⟨hA, by omega, by omega, ?_⟩, ?_, ?_⟩
    · have hsn : s.val.toNat = t.val.toNat + 1 := by omega
      rw [hsn]
      show (acc.2.2.2.val, ny.val) = rhoWalk (t.val.toNat + 1)
      rw [rhoWalk, ← hwalk, hnyv]
    · exact hbody
    · intro r hr x' hx' y' hy' z' hz'
      rw [hr x' hx' y' hy' z' hz']
      have hsn : s.val.toNat = t.val.toNat + 1 := by omega
      have hx1 : acc.2.2.1.val = (rhoWalk t.val.toNat).1 := congrArg Prod.fst hwalk
      have hy1 : acc.2.2.2.val = (rhoWalk t.val.toNat).2 := congrArg Prod.snd hwalk
      rw [hA] at hbits
      cases hstep' : rhoStepOf x' y' with
      | none =>
        dsimp only
        have hne : ¬ (x' = acc.2.2.1.val ∧ y' = acc.2.2.2.val) := by
          rintro ⟨rfl, rfl⟩
          rw [hx1, hy1, rhoStepOf_walk _ hn] at hstep'
          exact absurd hstep' (by simp)
        rw [hbits x' hx' y' hy' z' hz', if_neg hne]
      | some t' =>
        have ht'lt : t' < 24 := rhoStepOf_lt x' hx' y' hy' t' hstep'
        have ht'eq : rhoWalk t' = (x', y') := rhoStepOf_eq x' hx' y' hy' t' hstep'
        dsimp only
        by_cases heq : t' = t.val.toNat
        · subst heq
          have hxx : x' = acc.2.2.1.val := by rw [hx1, ht'eq]
          have hyy : y' = acc.2.2.2.val := by rw [hy1, ht'eq]
          rw [hsn, if_neg (by omega), if_pos (le_refl _),
            hbits x' hx' y' hy' z' hz', if_pos ⟨hxx, hyy⟩]
        · have hne : ¬ (x' = acc.2.2.1.val ∧ y' = acc.2.2.2.val) := by
            rintro ⟨rfl, rfl⟩
            rw [hx1, hy1, rhoStepOf_walk _ hn] at hstep'
            exact heq (Option.some.inj hstep').symm
          by_cases hle : t.val.toNat ≤ t'
          · rw [hsn, if_pos (by omega), if_pos hle]
          · rw [hsn, if_neg (by omega), if_neg hle, hbits x' hx' y' hy' z' hz', if_neg hne]
  case hdone =>
    rintro acc ⟨hA, ht0, ht24, hwalk⟩
    refine ⟨acc.2.1, ?_, fun x' hx' y' hy' z' hz' => ?_⟩
    · unfold hacspec_sha3_pedantic.step_mappings.rho_loop1.body
      rw [range_next_ge_i64 24#i64 24#i64 (le_refl _)]
      simp
    · cases hstep' : rhoStepOf x' y' with
      | none => dsimp only
      | some t' =>
        have ht'lt : t' < 24 := rhoStepOf_lt x' hx' y' hy' t' hstep'
        have h24 : ((24#i64 : Std.I64).val).toNat = 24 := by simp
        dsimp only
        rw [if_neg (by omega)]
  obtain ⟨r, hr, hbits⟩ := h
  refine ⟨r, ?_, fun x' hx' y' hy' z' hz' => ?_⟩
  · unfold hacspec_sha3_pedantic.step_mappings.rho_loop1
    exact hr
  · rw [hbits x' hx' y' hy' z' hz']
    cases hstep' : rhoStepOf x' y' with
    | none => dsimp only
    | some t' =>
      have h0 : ((0#i64 : Std.I64).val).toNat = 0 := by simp
      dsimp only
      rw [if_pos (by omega)]


/-! ### ρ itself -/

/-- ρ (FIPS 202, Algorithm 2): the copied lane and the 24 rotations of the walk
    together rotate every lane by its own offset. -/
theorem rho_eq (A : SA) :
    hacspec_sha3_pedantic.step_mappings.rho A = ok (mkSA (rhoBit (bitAt A))) := by
  unfold hacspec_sha3_pedantic.step_mappings.rho
  obtain ⟨w, hw, hwv⟩ := usize_to_i64 64#usize (by scalar_tac)
  have hw64 : w.val = 64 := by simpa using hwv
  obtain ⟨out1, hloop0, hbits0⟩ := rho0_zloop A (mkSA fun _ _ _ => false)
  obtain ⟨r, hloop1, hbits1⟩ := rho1_tloop A out1 w hw64
  rw [hw]
  simp only [bind_tc_ok, stateArray_zero_eq, hloop0]
  show hacspec_sha3_pedantic.step_mappings.rho_loop1
      { start := 0#i64, «end» := 24#i64 } A w out1 1#usize 0#usize = _
  rw [hloop1]
  apply congrArg
  refine ext (fun x y z hx hy hz => ?_)
  rw [bitAt_mkSA _ hx hy hz, hbits1 x hx y hy z hz]
  cases hstep : rhoStepOf x y with
  | some t => simp only [rhoBit, rhoOffsetOf, hstep]
  | none =>
    obtain ⟨hx0, hy0⟩ := rhoStepOf_none x hx y hy hstep
    subst hx0
    subst hy0
    dsimp only
    rw [hbits0 0 (by omega) 0 (by omega) z hz, if_pos ⟨rfl, rfl⟩]
    simp only [rhoBit, rhoOffsetOf, hstep, rotIndex_zero z hz]

-- Pinned by `#guard_msgs`: the build fails if this comes to depend on any axiom
-- beyond Lean's standard three.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.rho_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rho_eq

end LibcruxIotSha3.Composition.Pedantic
