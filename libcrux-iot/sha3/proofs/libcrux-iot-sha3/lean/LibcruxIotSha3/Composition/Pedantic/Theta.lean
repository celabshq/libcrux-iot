import LibcruxIotSha3.Composition.Pedantic.Grid
/-!
# The pedantic θ (FIPS 202, Algorithm 1)

θ is three loop nests rather than one: it builds the column parities `C[x, z]`,
then the differences `D[x, z]`, then adds `D` into every lane.  Each nest is
handled the way χ and π were, and the three characterisations compose into

    step_mappings.theta A = ok (mkSA (thetaBit (bitAt A)))

The `D` nest is where the signed `imod` of `Composition/Pedantic/LoopEq` earns
its keep: FIPS 202 indexes `C[(x-1) mod 5, z]` and `C[(x+1) mod 5, (z-1) mod w]`,
and Rust's `%` truncates towards zero, so the spec spells the modulus out in
`i64` and `imod_eq` turns it back into `Int.emod`.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-- FIPS 202, Algorithm 1 step 1: the parity of column `(x, z)`.  The
    association matches the extracted fold, left to right. -/
def cBit (f : Nat → Nat → Nat → Bool) (x z : Nat) : Bool :=
  (((f x 0 z ^^ f x 1 z) ^^ f x 2 z) ^^ f x 3 z) ^^ f x 4 z

/-- FIPS 202, Algorithm 1 step 2. -/
def dBit (c : Nat → Nat → Bool) (x z : Nat) : Bool :=
  c ((x + 4) % 5) z ^^ c ((x + 1) % 5) ((z + 63) % 64)

/-- FIPS 202, Algorithm 1 step 3. -/
def thetaBit (f : Nat → Nat → Nat → Bool) (x y z : Nat) : Bool :=
  f x y z ^^ dBit (cBit f) x z

/-! ### The `C` nest -/

theorem theta0_body_cont (A : SA) (c : CArr) (x z : Std.Usize)
    (hx : x.val < 5) (hz : z.val < 64) :
    ∃ s : Std.Usize, s.val = z.val + 1 ∧
      hacspec_sha3_pedantic.step_mappings.theta_loop0_loop0.body A x
          { start := z, «end» := 64#usize } c
        = ok (.cont ({ start := s, «end» := 64#usize },
            setCBit c x z (cBit (bitAt A) x.val z.val))) := by
  obtain ⟨s, hs, hnext⟩ := range_next_lt z 64#usize (by simpa using hz)
  refine ⟨s, hs, ?_⟩
  unfold hacspec_sha3_pedantic.step_mappings.theta_loop0_loop0.body
  rw [hnext]
  simp [index_usize_eq, array_update_eq, Std.Array.index_mut_usize,
    hx, hz, setCBit, cBit, bitAt]

theorem theta0_body_done (A : SA) (c : CArr) (x : Std.Usize) :
    hacspec_sha3_pedantic.step_mappings.theta_loop0_loop0.body A x
      { start := 64#usize, «end» := 64#usize } c = ok (.done (A, c)) := by
  unfold hacspec_sha3_pedantic.step_mappings.theta_loop0_loop0.body
  rw [range_next_ge 64#usize 64#usize (le_refl _)]
  simp

theorem theta0_zloop (A : SA) (c : CArr) (x : Std.Usize) (hx : x.val < 5) :
    ∃ c' : CArr,
      hacspec_sha3_pedantic.step_mappings.theta_loop0_loop0
          { start := 0#usize, «end» := 64#usize } A c x = ok (A, c') ∧
      ∀ x' < 5, ∀ z' < 64,
        cAt c' x' z' = if x' = x.val then cBit (bitAt A) x' z' else cAt c x' z' := by
  have h := loop_range_eq (β := CArr) (γ := SA × CArr)
    (fun p => hacspec_sha3_pedantic.step_mappings.theta_loop0_loop0.body A x p.1 p.2)
    64#usize
    (fun zU acc r => r.1 = A ∧ ∀ x' < 5, ∀ z' < 64,
      cAt r.2 x' z'
        = if x' = x.val ∧ zU.val ≤ z' then cBit (bitAt A) x' z' else cAt acc x' z')
    ?hstep ?hdone 64 0#usize c (by simp)
  case hstep =>
    intro i acc hi
    obtain ⟨s, hs, hbody⟩ := theta0_body_cont A acc x i hx (by simpa using hi)
    refine ⟨s, setCBit acc x i (cBit (bitAt A) x.val i.val), hs, hbody, ?_⟩
    rintro r ⟨hr1, hr2⟩
    refine ⟨hr1, fun x' hx' z' hz' => ?_⟩
    rw [hr2 x' hx' z' hz',
      cAt_setCBit acc x i _ x' z' hx (by simpa using hi) hx' hz']
    have hsv : s.val = i.val + 1 := hs
    split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega) | (congr 1 <;> omega)
  case hdone =>
    refine fun acc => ⟨(A, acc), theta0_body_done A acc x, rfl, fun x' _ z' hz' => ?_⟩
    have hne : ¬ (x' = x.val ∧ (64#usize).val ≤ z') := by
      simp only [not_and]
      intro _
      simp
      omega
    simp only [hne, if_false]
  obtain ⟨r, hr, hr1, hr2⟩ := h
  refine ⟨r.2, ?_, fun x' hx' z' hz' => ?_⟩
  · unfold hacspec_sha3_pedantic.step_mappings.theta_loop0_loop0
    rw [show ((A, r.2) : SA × CArr) = r by rw [← hr1]]
    exact hr
  · rw [hr2 x' hx' z' hz']
    simp

theorem theta0_xloop (A : SA) (c : CArr) :
    hacspec_sha3_pedantic.step_mappings.theta_loop0
      { start := 0#usize, «end» := 5#usize } A c = ok (A, mkC (cBit (bitAt A))) := by
  have h := loop_range_eq (β := SA × CArr) (γ := SA × CArr)
    (fun p => hacspec_sha3_pedantic.step_mappings.theta_loop0.body p.1 p.2.1 p.2.2)
    5#usize
    (fun xU acc r => r.1 = acc.1 ∧ ∀ x' < 5, ∀ z' < 64,
      cAt r.2 x' z'
        = if xU.val ≤ x' then cBit (bitAt acc.1) x' z' else cAt acc.2 x' z')
    ?hstep ?hdone 5 0#usize (A, c) (by simp)
  case hstep =>
    intro i acc hi
    have hi' : i.val < 5 := by simpa using hi
    obtain ⟨s, hs, hnext⟩ := range_next_lt i 5#usize (by simpa using hi)
    obtain ⟨c', hloop, hbits⟩ := theta0_zloop acc.1 acc.2 i hi'
    refine ⟨s, (acc.1, c'), hs, ?_, ?_⟩
    · unfold hacspec_sha3_pedantic.step_mappings.theta_loop0.body
      rw [hnext]
      simp [hloop]
    · rintro r ⟨hr1, hr2⟩
      refine ⟨hr1, fun x' hx' z' hz' => ?_⟩
      rw [hr2 x' hx' z' hz', hbits x' hx' z' hz']
      have hsv : s.val = i.val + 1 := hs
      split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
  case hdone =>
    refine fun acc => ⟨(acc.1, acc.2), ?_, rfl, fun x' hx' z' _ => ?_⟩
    · unfold hacspec_sha3_pedantic.step_mappings.theta_loop0.body
      rw [range_next_ge 5#usize 5#usize (le_refl _)]
      simp
    · have hne : ¬ ((5#usize).val ≤ x') := by simp; omega
      simp only [hne, if_false]
  obtain ⟨r, hr, hr1, hr2⟩ := h
  unfold hacspec_sha3_pedantic.step_mappings.theta_loop0
  have hr1' : r.1 = A := hr1
  rw [show ((A, mkC (cBit (bitAt A))) : SA × CArr) = r by
    have : r.2 = mkC (cBit (bitAt A)) := by
      refine (cext (fun x z hx hz => ?_)).symm
      rw [cAt_mkC _ hx hz, hr2 x hx z hz]
      simp
    cases r
    simp_all]
  exact hr


/-! ### The `D` nest -/

theorem theta1_body_cont (w : Std.I64) (hw : w.val = 64) (c d : CArr) (x z : Std.Usize)
    (hx : x.val < 5) (hz : z.val < 64) :
    ∃ s : Std.Usize, s.val = z.val + 1 ∧
      hacspec_sha3_pedantic.step_mappings.theta_loop1_loop0.body w c x
          { start := z, «end» := 64#usize } d
        = ok (.cont ({ start := s, «end» := 64#usize },
            setCBit d x z (dBit (cAt c) x.val z.val))) := by
  obtain ⟨s, hs, hnext⟩ := range_next_lt z 64#usize (by simpa using hz)
  refine ⟨s, hs, ?_⟩
  unfold hacspec_sha3_pedantic.step_mappings.theta_loop1_loop0.body
  rw [hnext]
  -- the column index `(x - 1) mod 5`
  have h5 : (5#i64 : Std.I64).val = 5 := by simp
  have h1 : (1#i64 : Std.I64).val = 1 := by simp
  have hminN : Std.I64.min = -9223372036854775808 := Std.I64.min_eq
  have hmaxI : Std.IScalar.max Std.IScalarTy.I64 = 9223372036854775807 := by
    rw [Std.IScalar.max_IScalarTy_I64_eq, Std.I64.max_eq]
  have hxlt : (x.val : Int) < 5 := by exact_mod_cast hx
  have hzlt : (z.val : Int) < 64 := by exact_mod_cast hz
  obtain ⟨xi, hxi, hxiv⟩ := usize_to_i64 x (by scalar_tac)
  obtain ⟨xm, hxm, hxmv⟩ := i64_sub_eq xi 1#i64 (by scalar_tac) (by scalar_tac)
  have hxmn : xm.val = (x.val : Int) - 1 := by rw [hxmv, hxiv, h1]
  obtain ⟨m, hm, hmv⟩ := imod_eq xm 5#i64 (by omega) (by omega) (by omega)
    (by rw [h5]; scalar_tac)
  have hmn : m.val = (x.val + 4) % 5 := by
    have : (m.val : Int) = ((x.val : Int) - 1) % 5 := by rw [hmv, hxmn, h5]
    omega
  -- the slice index `(z - 1) mod w`
  obtain ⟨zi, hzi, hziv⟩ := usize_to_i64 z (by scalar_tac)
  obtain ⟨zm, hzm, hzmv⟩ := i64_sub_eq zi 1#i64 (by scalar_tac) (by scalar_tac)
  have hzmn : zm.val = (z.val : Int) - 1 := by rw [hzmv, hziv, h1]
  obtain ⟨n, hn, hnv⟩ := imod_eq zm w (by omega) (by omega) (by omega)
    (by rw [hw]; scalar_tac)
  have hnn : n.val = (z.val + 63) % 64 := by
    have : (n.val : Int) = ((z.val : Int) - 1) % 64 := by rw [hnv, hzmn, hw]
    omega
  -- the column index `(x + 1) mod 5`
  obtain ⟨x1, hx1, hx1v⟩ := usize_add_eq x 1#usize (by scalar_tac)
  obtain ⟨x1m, hx1m, hx1mv⟩ := usize_rem_eq x1 5#usize (by simp)
  have hx1mn : x1m.val = (x.val + 1) % 5 := by simp [hx1mv, hx1v]
  have hbm : m.val < (5#usize).val := by simp [hmn]; omega
  have hbx1m : x1m.val < (5#usize).val := by simp [hx1mn]; omega
  have hbn : n.val < (64#usize).val := by simp [hnn]; omega
  have hma : (x.val + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  simp [hxi, hxm, hm, hzi, hzm, hn, hx1, hx1m,
    index_usize_eq _ _ hbm, index_usize_eq _ _ hbx1m, index_usize_eq _ _ hbn,
    index_usize_eq, array_update_eq, Std.Array.index_mut_usize, massert, hma,
    hmn, hnn, hx1mn, hx, hz, setCBit, dBit, cAt]

theorem theta1_body_done (w : Std.I64) (c d : CArr) (x : Std.Usize) :
    hacspec_sha3_pedantic.step_mappings.theta_loop1_loop0.body w c x
      { start := 64#usize, «end» := 64#usize } d = ok (.done d) := by
  unfold hacspec_sha3_pedantic.step_mappings.theta_loop1_loop0.body
  rw [range_next_ge 64#usize 64#usize (le_refl _)]
  simp

theorem theta1_zloop (w : Std.I64) (hw : w.val = 64) (c d : CArr) (x : Std.Usize)
    (hx : x.val < 5) :
    ∃ d' : CArr,
      hacspec_sha3_pedantic.step_mappings.theta_loop1_loop0
          { start := 0#usize, «end» := 64#usize } w c d x = ok d' ∧
      ∀ x' < 5, ∀ z' < 64,
        cAt d' x' z' = if x' = x.val then dBit (cAt c) x' z' else cAt d x' z' := by
  have h := loop_range_eq (β := CArr) (γ := CArr)
    (fun p => hacspec_sha3_pedantic.step_mappings.theta_loop1_loop0.body w c x p.1 p.2)
    64#usize
    (fun zU acc r => ∀ x' < 5, ∀ z' < 64,
      cAt r x' z' = if x' = x.val ∧ zU.val ≤ z' then dBit (cAt c) x' z' else cAt acc x' z')
    ?hstep ?hdone 64 0#usize d (by simp)
  case hstep =>
    intro i acc hi
    obtain ⟨s, hs, hbody⟩ := theta1_body_cont w hw c acc x i hx (by simpa using hi)
    refine ⟨s, setCBit acc x i (dBit (cAt c) x.val i.val), hs, hbody, ?_⟩
    intro r hr x' hx' z' hz'
    rw [hr x' hx' z' hz', cAt_setCBit acc x i _ x' z' hx (by simpa using hi) hx' hz']
    have hsv : s.val = i.val + 1 := hs
    split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega) | (congr 1 <;> omega)
  case hdone =>
    refine fun acc => ⟨acc, theta1_body_done w c acc x, fun x' _ z' hz' => ?_⟩
    have hne : ¬ (x' = x.val ∧ (64#usize).val ≤ z') := by
      simp only [not_and]
      intro _
      simp
      omega
    simp only [hne, if_false]
  obtain ⟨r, hr, hr2⟩ := h
  refine ⟨r, ?_, fun x' hx' z' hz' => ?_⟩
  · unfold hacspec_sha3_pedantic.step_mappings.theta_loop1_loop0
    exact hr
  · rw [hr2 x' hx' z' hz']
    simp

theorem theta1_xloop (w : Std.I64) (hw : w.val = 64) (c d : CArr) :
    hacspec_sha3_pedantic.step_mappings.theta_loop1
      { start := 0#usize, «end» := 5#usize } w c d = ok (mkC (dBit (cAt c))) := by
  have h := loop_range_eq (β := CArr) (γ := CArr)
    (fun p => hacspec_sha3_pedantic.step_mappings.theta_loop1.body w c p.1 p.2)
    5#usize
    (fun xU acc r => ∀ x' < 5, ∀ z' < 64,
      cAt r x' z' = if xU.val ≤ x' then dBit (cAt c) x' z' else cAt acc x' z')
    ?hstep ?hdone 5 0#usize d (by simp)
  case hstep =>
    intro i acc hi
    have hi' : i.val < 5 := by simpa using hi
    obtain ⟨s, hs, hnext⟩ := range_next_lt i 5#usize (by simpa using hi)
    obtain ⟨d', hloop, hbits⟩ := theta1_zloop w hw c acc i hi'
    refine ⟨s, d', hs, ?_, ?_⟩
    · unfold hacspec_sha3_pedantic.step_mappings.theta_loop1.body
      rw [hnext]
      simp [hloop]
    · intro r hr x' hx' z' hz'
      rw [hr x' hx' z' hz', hbits x' hx' z' hz']
      have hsv : s.val = i.val + 1 := hs
      split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
  case hdone =>
    refine fun acc => ⟨acc, ?_, fun x' hx' z' _ => ?_⟩
    · unfold hacspec_sha3_pedantic.step_mappings.theta_loop1.body
      rw [range_next_ge 5#usize 5#usize (le_refl _)]
      simp
    · have hne : ¬ ((5#usize).val ≤ x') := by simp; omega
      simp only [hne, if_false]
  obtain ⟨r, hr, hr2⟩ := h
  unfold hacspec_sha3_pedantic.step_mappings.theta_loop1
  rw [show mkC (dBit (cAt c)) = r from (cext (fun x z hx hz => by
    rw [cAt_mkC _ hx hz, hr2 x hx z hz]
    simp)).symm]
  exact hr


/-! ### The `A ⊕ D` nest -/

/-- The bit `theta`'s third nest writes, given the differences `d`. -/
def addDBit (f : Nat → Nat → Nat → Bool) (d : Nat → Nat → Bool) (x y z : Nat) : Bool :=
  f x y z ^^ d x z

theorem theta2_body_cont (A : SA) (d : CArr) (out : SA) (x y z : Std.Usize)
    (hx : x.val < 5) (hy : y.val < 5) (hz : z.val < 64) :
    ∃ s : Std.Usize, s.val = z.val + 1 ∧
      hacspec_sha3_pedantic.step_mappings.theta_loop2_loop0_loop0.body A d x y
          { start := z, «end» := 64#usize } out
        = ok (.cont ({ start := s, «end» := 64#usize },
            setBit out x y z (addDBit (bitAt A) (cAt d) x.val y.val z.val))) := by
  obtain ⟨s, hs, hnext⟩ := range_next_lt z 64#usize (by simpa using hz)
  refine ⟨s, hs, ?_⟩
  unfold hacspec_sha3_pedantic.step_mappings.theta_loop2_loop0_loop0.body
  rw [hnext]
  simp [index_usize_eq, array_update_eq, Std.Array.index_mut_usize,
    hx, hy, hz, setBit, addDBit, bitAt, cAt]

theorem theta2_body_done (A : SA) (d : CArr) (out : SA) (x y : Std.Usize) :
    hacspec_sha3_pedantic.step_mappings.theta_loop2_loop0_loop0.body A d x y
      { start := 64#usize, «end» := 64#usize } out = ok (.done (A, out)) := by
  unfold hacspec_sha3_pedantic.step_mappings.theta_loop2_loop0_loop0.body
  rw [range_next_ge 64#usize 64#usize (le_refl _)]
  simp

theorem theta2_zloop (A : SA) (d : CArr) (out : SA) (x y : Std.Usize)
    (hx : x.val < 5) (hy : y.val < 5) :
    ∃ out' : SA,
      hacspec_sha3_pedantic.step_mappings.theta_loop2_loop0_loop0
          { start := 0#usize, «end» := 64#usize } A d out x y = ok (A, out') ∧
      ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
        bitAt out' x' y' z'
          = if x' = x.val ∧ y' = y.val then addDBit (bitAt A) (cAt d) x' y' z'
            else bitAt out x' y' z' := by
  have h := loop_range_eq (β := SA) (γ := SA × SA)
    (fun p => hacspec_sha3_pedantic.step_mappings.theta_loop2_loop0_loop0.body A d x y p.1 p.2)
    64#usize
    (fun zU acc r => r.1 = A ∧ ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
      bitAt r.2 x' y' z'
        = if x' = x.val ∧ y' = y.val ∧ zU.val ≤ z' then addDBit (bitAt A) (cAt d) x' y' z'
          else bitAt acc x' y' z')
    ?hstep ?hdone 64 0#usize out (by simp)
  case hstep =>
    intro i acc hi
    obtain ⟨s, hs, hbody⟩ := theta2_body_cont A d acc x y i hx hy (by simpa using hi)
    refine ⟨s, setBit acc x y i (addDBit (bitAt A) (cAt d) x.val y.val i.val), hs, hbody, ?_⟩
    rintro r ⟨hr1, hr2⟩
    refine ⟨hr1, fun x' hx' y' hy' z' hz' => ?_⟩
    rw [hr2 x' hx' y' hy' z' hz',
      bitAt_setBit acc x y i _ x' y' z' hx hy (by simpa using hi) hx' hy' hz']
    have hsv : s.val = i.val + 1 := hs
    split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega) | (congr 1 <;> omega)
  case hdone =>
    refine fun acc => ⟨(A, acc), theta2_body_done A d acc x y, rfl, fun x' _ y' _ z' hz' => ?_⟩
    have hne : ¬ (x' = x.val ∧ y' = y.val ∧ (64#usize).val ≤ z') := by
      simp only [not_and]
      intro _ _
      simp
      omega
    simp only [hne, if_false]
  obtain ⟨r, hr, hr1, hr2⟩ := h
  refine ⟨r.2, ?_, fun x' hx' y' hy' z' hz' => ?_⟩
  · unfold hacspec_sha3_pedantic.step_mappings.theta_loop2_loop0_loop0
    rw [show ((A, r.2) : SA × SA) = r by rw [← hr1]]
    exact hr
  · rw [hr2 x' hx' y' hy' z' hz']
    simp

theorem theta2_yloop (A : SA) (d : CArr) (out : SA) (x : Std.Usize) (hx : x.val < 5) :
    ∃ out' : SA,
      hacspec_sha3_pedantic.step_mappings.theta_loop2_loop0
          { start := 0#usize, «end» := 5#usize } A d out x = ok (A, out') ∧
      ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
        bitAt out' x' y' z'
          = if x' = x.val then addDBit (bitAt A) (cAt d) x' y' z' else bitAt out x' y' z' := by
  have h := loop_range_eq (β := SA × SA) (γ := SA × SA)
    (fun p => hacspec_sha3_pedantic.step_mappings.theta_loop2_loop0.body d x p.1 p.2.1 p.2.2)
    5#usize
    (fun yU acc r => r.1 = acc.1 ∧ ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
      bitAt r.2 x' y' z'
        = if x' = x.val ∧ yU.val ≤ y' then addDBit (bitAt acc.1) (cAt d) x' y' z'
          else bitAt acc.2 x' y' z')
    ?hstep ?hdone 5 0#usize (A, out) (by simp)
  case hstep =>
    intro i acc hi
    have hi' : i.val < 5 := by simpa using hi
    obtain ⟨s, hs, hnext⟩ := range_next_lt i 5#usize (by simpa using hi)
    obtain ⟨out', hloop, hbits⟩ := theta2_zloop acc.1 d acc.2 x i hx hi'
    refine ⟨s, (acc.1, out'), hs, ?_, ?_⟩
    · unfold hacspec_sha3_pedantic.step_mappings.theta_loop2_loop0.body
      rw [hnext]
      simp [hloop]
    · rintro r ⟨hr1, hr2⟩
      refine ⟨hr1, fun x' hx' y' hy' z' hz' => ?_⟩
      rw [hr2 x' hx' y' hy' z' hz', hbits x' hx' y' hy' z' hz']
      have hsv : s.val = i.val + 1 := hs
      split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega)
  case hdone =>
    refine fun acc => ⟨(acc.1, acc.2), ?_, rfl, fun x' _ y' hy' z' _ => ?_⟩
    · unfold hacspec_sha3_pedantic.step_mappings.theta_loop2_loop0.body
      rw [range_next_ge 5#usize 5#usize (le_refl _)]
      simp
    · have hne : ¬ (x' = x.val ∧ (5#usize).val ≤ y') := by
        simp only [not_and]
        intro _
        simp
        omega
      simp only [hne, if_false]
  obtain ⟨r, hr, hr1, hr2⟩ := h
  refine ⟨r.2, ?_, fun x' hx' y' hy' z' hz' => ?_⟩
  · unfold hacspec_sha3_pedantic.step_mappings.theta_loop2_loop0
    have hr1' : r.1 = A := hr1
    rw [show ((A, r.2) : SA × SA) = r by cases r; simp_all]
    exact hr
  · rw [hr2 x' hx' y' hy' z' hz']
    simp

theorem theta2_xloop (A : SA) (d : CArr) (out : SA) :
    hacspec_sha3_pedantic.step_mappings.theta_loop2
      { start := 0#usize, «end» := 5#usize } A d out
      = ok (mkSA (addDBit (bitAt A) (cAt d))) := by
  have h := loop_range_eq (β := SA × SA) (γ := SA)
    (fun p => hacspec_sha3_pedantic.step_mappings.theta_loop2.body d p.1 p.2.1 p.2.2)
    5#usize
    (fun xU acc r => ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
      bitAt r x' y' z'
        = if xU.val ≤ x' then addDBit (bitAt acc.1) (cAt d) x' y' z'
          else bitAt acc.2 x' y' z')
    ?hstep ?hdone 5 0#usize (A, out) (by simp)
  case hstep =>
    intro i acc hi
    have hi' : i.val < 5 := by simpa using hi
    obtain ⟨s, hs, hnext⟩ := range_next_lt i 5#usize (by simpa using hi)
    obtain ⟨out', hloop, hbits⟩ := theta2_yloop acc.1 d acc.2 i hi'
    refine ⟨s, (acc.1, out'), hs, ?_, ?_⟩
    · unfold hacspec_sha3_pedantic.step_mappings.theta_loop2.body
      rw [hnext]
      simp [hloop]
    · intro r hr x' hx' y' hy' z' hz'
      rw [hr x' hx' y' hy' z' hz', hbits x' hx' y' hy' z' hz']
      have hsv : s.val = i.val + 1 := hs
      split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
  case hdone =>
    refine fun acc => ⟨acc.2, ?_, fun x' hx' y' _ z' _ => ?_⟩
    · unfold hacspec_sha3_pedantic.step_mappings.theta_loop2.body
      rw [range_next_ge 5#usize 5#usize (le_refl _)]
      simp
    · have hne : ¬ ((5#usize).val ≤ x') := by simp; omega
      simp only [hne, if_false]
  obtain ⟨r, hr, hbits⟩ := h
  unfold hacspec_sha3_pedantic.step_mappings.theta_loop2
  rw [hr]
  apply congrArg
  refine ext (fun x y z hx hy hz => ?_)
  rw [bitAt_mkSA _ hx hy hz, hbits x hx y hy z hz]
  simp

/-! ### θ itself -/

/-- θ (FIPS 202, Algorithm 1): the three nests compute exactly the FIPS formula
    on every bit of the state array. -/
theorem theta_eq (A : SA) :
    hacspec_sha3_pedantic.step_mappings.theta A = ok (mkSA (thetaBit (bitAt A))) := by
  unfold hacspec_sha3_pedantic.step_mappings.theta
  obtain ⟨w, hw, hwv⟩ := usize_to_i64 64#usize (by scalar_tac)
  have hw64 : w.val = 64 := by simpa using hwv
  rw [hw]
  simp only [bind_tc_ok, theta0_xloop]
  show (do
      let d1 ← hacspec_sha3_pedantic.step_mappings.theta_loop1
        { start := 0#usize, «end» := 5#usize } w (mkC (cBit (bitAt A)))
        (Std.Array.repeat 5#usize (Std.Array.repeat 64#usize false))
      hacspec_sha3_pedantic.step_mappings.theta_loop2
        { start := 0#usize, «end» := 5#usize } A d1 A) = _
  simp only [theta1_xloop w hw64, bind_tc_ok, theta2_xloop]
  apply congrArg
  refine mkSA_congr (fun x y z hx hy hz => ?_)
  simp only [addDBit, thetaBit, cAt_mkC _ hx hz, dBit,
    cAt_mkC _ (show (x + 4) % 5 < 5 by omega) hz,
    cAt_mkC _ (show (x + 1) % 5 < 5 by omega) (show (z + 63) % 64 < 64 by omega)]

-- Pinned by `#guard_msgs`: the build fails if this comes to depend on any axiom
-- beyond Lean's standard three.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.theta_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms theta_eq

end LibcruxIotSha3.Composition.Pedantic
