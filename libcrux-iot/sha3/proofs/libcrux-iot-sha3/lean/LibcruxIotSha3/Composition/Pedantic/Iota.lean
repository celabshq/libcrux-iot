import LibcruxIotSha3.Composition.Pedantic.Grid
/-!
# The pedantic ι and its round constants (FIPS 202, Algorithms 5 and 6)

ι is the only step mapping that depends on the round index, and the dependence
runs through the linear feedback shift register of Algorithm 5: `rc(t)` is bit 0
of the register after `t mod 255` steps, and ι XORs `rc(j + 7 i_r)` into bit
`2^j - 1` of the lane `A[0, 0]`, for `j = 0 .. l`.

So this module has two halves.  The first is the register: `rcStep` transcribes
Algorithm 5's steps 3.a-3.e, and `rc_eq` says the extracted `rc` iterates it.
That proof is where the slice machinery earns its keep -- the shift is written
`shifted[1..9].copy_from_slice(&r[0..8])`, and `slice_clone_from_slice_bool`
plus the nine-element destructuring turn it into an ordinary list computation.
The second half is ι itself, ending as usual at

    step_mappings.iota A i_r = ok (mkSA (iotaBit (bitAt A) i_r))
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-! ### The linear feedback shift register (Algorithm 5) -/

/-- One step of the register, as FIPS 202 writes it: prepend a zero bit, XOR
    `R[8]` into `R[0]`, `R[4]`, `R[5]` and `R[6]`, then truncate back to eight
    bits (the ninth is cleared rather than dropped, as in the spec). -/
def rcStep (r : List Bool) : List Bool :=
  let s := false :: r.take 8
  (List.range 9).map (fun j =>
    if j = 8 then false
    else if j = 0 ∨ j = 4 ∨ j = 5 ∨ j = 6 then s[j]! ^^ s[8]! else s[j]!)

/-- The register's initial value, `R = 10000000`. -/
def rcInit : List Bool := [true, false, false, false, false, false, false, false, false]

/-- The same, as the nine-bit array the extracted `rc` starts from. -/
def rcInitArray : Std.Array Bool 9#usize := ⟨rcInit, by simp [rcInit]⟩

/-- FIPS 202, Algorithm 5: `rc(t)` is bit 0 of the register after `t mod 255`
    steps, and `1` when `t mod 255 = 0`. -/
def rcOf (t : Int) : Bool :=
  if t % 255 = 0 then true else (rcStep^[(t % 255).toNat] rcInit)[0]!

/-- The computed form of one register step, on the nine bits themselves. -/
theorem rcStep_cons (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) :
    rcStep [b0, b1, b2, b3, b4, b5, b6, b7, b8]
      = [b7, b0, b1, b2, b3 ^^ b7, b4 ^^ b7, b5 ^^ b7, b6, false] := by
  simp [rcStep, List.range, List.range.loop]

/-! ### The extracted register loop -/

/-- The nine bits of the register, spelled out: the slice operations in the body
    only compute on a literal list. -/
theorem array9_cases (r : Std.Array Bool 9#usize) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
      r.val = [b0, b1, b2, b3, b4, b5, b6, b7, b8] := by
  obtain ⟨l, hl⟩ := r
  have hl9 : l.length = 9 := by simpa using hl
  match l, hl9 with
  | [b0, b1, b2, b3, b4, b5, b6, b7, b8], _ => exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩

theorem rc_body_cont (i e : Std.Usize) (r : Std.Array Bool 9#usize) (h : i.val ≤ e.val)
    (hsafe : i.val + 1 ≤ Std.UScalar.max Std.UScalarTy.Usize) :
    ∃ (s : Std.Usize) (r' : Std.Array Bool 9#usize), s.val = i.val + 1 ∧
      r'.val = rcStep r.val ∧
      hacspec_sha3_pedantic.step_mappings.rc_loop.body { start := i, «end» := e } r
        = ok (.cont ({ start := s, «end» := e }, r')) := by
  obtain ⟨s, hs, hnext⟩ := range_incl_next_le i e h hsafe
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, hr⟩ := array9_cases r
  refine ⟨s, ⟨[b7, b0, b1, b2, b3 ^^ b7, b4 ^^ b7, b5 ^^ b7, b6, false], by simp⟩, hs, ?_, ?_⟩
  · rw [hr, rcStep_cons]
  · have hreq : r = ⟨[b0, b1, b2, b3, b4, b5, b6, b7, b8], by simp⟩ := Subtype.ext hr
    subst hreq
    unfold hacspec_sha3_pedantic.step_mappings.rc_loop.body
    rw [hnext]
    simp [index_usize_eq, array_update_eq, core.Array.Insts.CoreOpsIndexIndexMut.index_mut,
      core.Array.Insts.CoreOpsIndexIndex.index, core.Slice.Insts.CoreOpsIndexIndex.index,
      core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
      core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
      core.slice.Slice.copy_from_slice, rust_primitives.slice.slice_slice,
      slice_clone_from_slice_bool, core.array.Array.as_slice,
      core.array.Array.as_mut_slice, rust_primitives.slice.slice_slice_mut,
      rust_primitives.slice.slice_length,
      core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
      rust_primitives.slice.array_as_slice, rust_primitives.slice.array_as_mut_slice,
      core.Bool.Insts.CoreMarkerCopy, Std.Slice.subslice, Std.Array.to_slice,
      Std.Array.to_slice_mut, List.slice, List.setSlice!, Std.Array.from_slice,
      Std.Array.set, List.set]

theorem rc_body_done (i e : Std.Usize) (r : Std.Array Bool 9#usize) (h : e.val < i.val) :
    hacspec_sha3_pedantic.step_mappings.rc_loop.body { start := i, «end» := e } r
      = ok (.done r) := by
  unfold hacspec_sha3_pedantic.step_mappings.rc_loop.body
  rw [range_incl_next_gt i e h]
  simp

/-! ### The register loop, and `rc` -/

theorem rc_loop_eq (t1 : Std.Usize) (r : Std.Array Bool 9#usize)
    (hsafe : t1.val + 1 ≤ Std.UScalar.max Std.UScalarTy.Usize) :
    ∃ r' : Std.Array Bool 9#usize,
      hacspec_sha3_pedantic.step_mappings.rc_loop { start := 1#usize, «end» := t1 } r = ok r' ∧
      r'.val = rcStep^[t1.val] r.val := by
  have h := loop_range_incl_eq (β := Std.Array Bool 9#usize) (γ := Std.Array Bool 9#usize)
    (fun p => hacspec_sha3_pedantic.step_mappings.rc_loop.body p.1 p.2)
    t1
    (fun i acc r => r.val = rcStep^[t1.val + 1 - i.val] acc.val)
    ?hstep ?hdone t1.val 1#usize r (by simp; omega)
  case hstep =>
    intro i acc hi
    obtain ⟨s, acc', hs, hacc', hbody⟩ := rc_body_cont i t1 acc hi (by omega)
    refine ⟨s, acc', hs, hbody, ?_⟩
    intro r' hr'
    rw [hr', hacc', hs, ← Function.iterate_succ_apply]
    congr 1
    omega
  case hdone =>
    intro i acc hi
    refine ⟨acc, rc_body_done i t1 acc hi, ?_⟩
    rw [show t1.val + 1 - i.val = 0 by omega]
    rfl
  obtain ⟨r', hr', hbits⟩ := h
  refine ⟨r', ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.step_mappings.rc_loop
    exact hr'
  · rw [hbits]
    congr 1


/-- FIPS 202, Algorithm 5: the extracted `rc` is the register, iterated. -/
theorem rc_eq (t : Std.I64) (hmin : t.val ≠ Std.I64.min) :
    hacspec_sha3_pedantic.step_mappings.rc t = ok (rcOf t.val) := by
  have h255 : (255#i64 : Std.I64).val = 255 := by simp
  have hmaxI : Std.IScalar.max Std.IScalarTy.I64 = 9223372036854775807 := by
    rw [Std.IScalar.max_IScalarTy_I64_eq, Std.I64.max_eq]
  obtain ⟨t1, ht1, ht1v⟩ := imod_eq t 255#i64 (by omega) hmin (by omega) (by rw [h255]; scalar_tac)
  have ht1lt : t1.val < 255 := by
    have : (t1.val : Int) < 255 := by rw [ht1v, h255]; exact Int.emod_lt_of_pos _ (by omega)
    exact_mod_cast this
  unfold hacspec_sha3_pedantic.step_mappings.rc
  rw [ht1, bind_tc_ok]
  by_cases h0 : t1 = 0#usize
  · have hz : t.val % 255 = 0 := by
      rw [← h255, ← ht1v, h0]
      simp
    rw [if_pos h0, rcOf, if_pos hz]
  · have hz : ¬ (t.val % 255 = 0) := by
      intro hcontra
      apply h0
      apply (Std.UScalar.eq_equiv t1 0#usize).mpr
      have : (t1.val : Int) = 0 := by rw [ht1v, h255, hcontra]
      simpa using this
    have hval : t1.val = (t.val % 255).toNat := by
      have : (t1.val : Int) = t.val % 255 := by rw [ht1v, h255]
      omega
    rw [if_neg h0]
    have hinit : (Array.repeat 9#usize false).update 0#usize true = ok rcInitArray := by
      rw [array_update_eq _ _ _ (by simp)]
      apply congrArg
      apply Subtype.ext
      simp [rcInitArray, rcInit, Std.Array.set]
    have hnew : core.ops.range.RangeInclusive.new 1#usize t1
        = ok ({ start := 1#usize, «end» := t1 } : core.ops.range.RangeInclusive Std.Usize) := rfl
    obtain ⟨r', hloop, hbits⟩ := rc_loop_eq t1 rcInitArray (by scalar_tac)
    have hidx0 : ∀ v : Std.Array Bool 9#usize, v.index_usize 0#usize = ok v.val[0]! :=
      fun v => index_usize_eq v 0#usize (by simp)
    simp only [hinit, bind_tc_ok, hnew, hloop, hidx0, hbits, rcOf, if_neg hz, hval]
    rfl


/-! ### The round constant of a round (Algorithm 6, step 3)

`rc(j + 7 i_r)` lands in bit `2^j - 1` of the lane, for `j = 0 .. l`; every
other bit of the round constant stays zero. -/

/-- The `j` whose bit `2^j - 1` is `z`, if there is one below `l + 1 = 7`. -/
def rcIndex (z : Nat) : Option Nat := (List.range 7).find? (fun j => 2 ^ j - 1 = z)

/-- Bit `z` of the round constant of round `i_r`. -/
def rcBitAt (i_r : Int) (z : Nat) : Bool :=
  match rcIndex z with
  | some j => rcOf ((j : Int) + 7 * i_r)
  | none => false

/-- ι (FIPS 202, Algorithm 6): the round constant is XORed into `A[0, 0]`. -/
def iotaBit (f : Nat → Nat → Nat → Bool) (i_r : Int) (x y z : Nat) : Bool :=
  if x = 0 ∧ y = 0 then f x y z ^^ rcBitAt i_r z else f x y z

theorem rcIndex_pow (j : Nat) (hj : j < 7) : rcIndex (2 ^ j - 1) = some j := by
  have hj7 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hj7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem rcIndex_lt (z : Nat) (j : Nat) (h : rcIndex z = some j) : j < 7 ∧ 2 ^ j - 1 = z := by
  have hmem := List.find?_some h
  have hin := List.mem_of_find?_eq_some h
  simp only [List.mem_range] at hin
  simp only [decide_eq_true_eq] at hmem
  exact ⟨hin, hmem⟩

-- Pinned by `#guard_msgs`: the build fails if this comes to depend on any axiom
-- beyond Lean's standard three.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.rc_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rc_eq


/-! ### The round-constant loop -/

theorem iota0_body_cont (i_r : Std.I64) (hlo : -1000000000 ≤ i_r.val) (hhi : i_r.val ≤ 1000000000)
    (rcst : Std.Array Bool 64#usize) (j e : Std.Usize) (hj : j.val < 7) (hje : j.val ≤ e.val) :
    ∃ (s : Std.Usize) (rcst' : Std.Array Bool 64#usize), s.val = j.val + 1 ∧
      rcst'.val = rcst.val.set (2 ^ j.val - 1) (rcOf ((j.val : Int) + 7 * i_r.val)) ∧
      hacspec_sha3_pedantic.step_mappings.iota_loop0.body i_r { start := j, «end» := e } rcst
        = ok (.cont ({ start := s, «end» := e }, rcst')) := by
  have hmaxI : Std.IScalar.max Std.IScalarTy.I64 = 9223372036854775807 := by
    rw [Std.IScalar.max_IScalarTy_I64_eq, Std.I64.max_eq]
  have hminI : Std.IScalar.min Std.IScalarTy.I64 = -9223372036854775808 := by
    rw [Std.IScalar.min_IScalarTy_I64_eq, Std.I64.min_eq]
  have hminN : Std.I64.min = -9223372036854775808 := Std.I64.min_eq
  have hmaxN : Std.I64.max = 9223372036854775807 := Std.I64.max_eq
  have hjn : (j.val : Int) < 7 := by exact_mod_cast hj
  obtain ⟨s, hs, hnext⟩ := range_incl_next_le j e hje (by scalar_tac)
  obtain ⟨ji, hji, hjiv⟩ := usize_to_i64 j (by scalar_tac)
  obtain ⟨m, hm, hmv⟩ := i64_mul_eq 7#i64 i_r (by simp; omega) (by simp; omega)
  have hmn : m.val = 7 * i_r.val := by rw [hmv]; simp
  obtain ⟨tsum, htsum, htsumv⟩ := i64_add_eq ji m (by omega) (by omega)
  have htn : tsum.val = (j.val : Int) + 7 * i_r.val := by rw [htsumv, hjiv, hmn]
  obtain ⟨sh, hsh, hshv⟩ := usize_shl_eq 1#usize j (by
    have := Std.UScalarTy.Usize_numBits_eq
    rcases System.Platform.numBits_eq with hN | hN <;> omega)
  have hpow_le : 2 ^ j.val ≤ 64 := by
    have hle : (2:Nat) ^ j.val ≤ 2 ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    simpa using hle
  have hpow_pos : 0 < 2 ^ j.val := Nat.two_pow_pos j.val
  have hsize : (64 : Nat) < Std.Usize.size := by scalar_tac
  have hshn : sh.val = 2 ^ j.val := by
    rw [hshv, show (1#usize : Std.Usize).val = 1 from by simp, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨idx, hidx, hidxv⟩ := usize_sub_eq sh 1#usize (by
    rw [hshn, show (1#usize : Std.Usize).val = 1 from by simp]; omega)
  have hidxn : idx.val = 2 ^ j.val - 1 := by
    rw [hidxv, hshn, show (1#usize : Std.Usize).val = 1 from by simp]
  have hidxlt : idx.val < (64#usize).val := by
    rw [hidxn, show (64#usize : Std.Usize).val = 64 from by simp]
    omega
  refine ⟨s, rcst.set idx (rcOf tsum.val), hs, ?_, ?_⟩
  · simp only [Std.Array.set_val_eq, hidxn, htn]
  · unfold hacspec_sha3_pedantic.step_mappings.iota_loop0.body
    rw [hnext]
    simp [hji, hm, htsum, hsh, hidx, rc_eq tsum (by omega), array_update_eq _ _ _ hidxlt]


theorem array64_set_get (a : Std.Array Bool 64#usize) (i : Std.Usize) (v : Bool) (z : Nat)
    (hi : i.val < 64) (hz : z < 64) :
    (a.set i v).val[z]! = if z = i.val then v else a.val[z]! := by
  have hlen : a.val.length = 64 := by simp
  by_cases h : z = i.val <;> simp_all [Std.Array.set]

theorem iota0_body_done (i_r : Std.I64) (rcst : Std.Array Bool 64#usize) (j e : Std.Usize)
    (h : e.val < j.val) :
    hacspec_sha3_pedantic.step_mappings.iota_loop0.body i_r { start := j, «end» := e } rcst
      = ok (.done rcst) := by
  unfold hacspec_sha3_pedantic.step_mappings.iota_loop0.body
  rw [range_incl_next_gt j e h]
  simp

theorem iota0_loop (i_r : Std.I64) (hlo : -1000000000 ≤ i_r.val) (hhi : i_r.val ≤ 1000000000)
    (rcst : Std.Array Bool 64#usize) :
    ∃ rcst' : Std.Array Bool 64#usize,
      hacspec_sha3_pedantic.step_mappings.iota_loop0
          { start := 0#usize, «end» := 6#usize } i_r rcst = ok rcst' ∧
      ∀ z < 64, rcst'.val[z]! =
        match rcIndex z with
        | some j => rcOf ((j : Int) + 7 * i_r.val)
        | none => rcst.val[z]! := by
  have h := loop_range_incl_eq (β := Std.Array Bool 64#usize) (γ := Std.Array Bool 64#usize)
    (fun p => hacspec_sha3_pedantic.step_mappings.iota_loop0.body i_r p.1 p.2)
    6#usize
    (fun j acc r => ∀ z < 64, r.val[z]! =
      match rcIndex z with
      | some j' => if j.val ≤ j' then rcOf ((j' : Int) + 7 * i_r.val) else acc.val[z]!
      | none => acc.val[z]!)
    ?hstep ?hdone 7 0#usize rcst (by simp)
  case hstep =>
    intro j acc hj
    have hj7 : j.val < 7 := by
      have h6 : (6#usize : Std.Usize).val = 6 := by simp
      omega
    obtain ⟨s, acc', hs, hacc', hbody⟩ := iota0_body_cont i_r hlo hhi acc j 6#usize hj7 hj
    refine ⟨s, acc', hs, hbody, ?_⟩
    intro r hr z hz
    rw [hr z hz]
    have hidxlt : 2 ^ j.val - 1 < 64 := by
      have hle : (2:Nat) ^ j.val ≤ 2 ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
      simp at hle
      omega
    have hacc'z : ∀ z' < 64, acc'.val[z']!
        = if z' = 2 ^ j.val - 1 then rcOf ((j.val : Int) + 7 * i_r.val) else acc.val[z']! := by
      intro z' hz'
      rw [hacc']
      have hlen : acc.val.length = 64 := by simp
      by_cases h : z' = 2 ^ j.val - 1 <;> simp_all
    have hsv : s.val = j.val + 1 := hs
    cases hstep' : rcIndex z with
    | none =>
      dsimp only
      have hne : ¬ (z = 2 ^ j.val - 1) := by
        intro hcontra
        rw [hcontra, rcIndex_pow j.val hj7] at hstep'
        exact absurd hstep' (by simp)
      rw [hacc'z z hz, if_neg hne]
    | some j' =>
      obtain ⟨hj'7, hj'z⟩ := rcIndex_lt z j' hstep'
      dsimp only
      have hiff : (z = 2 ^ j.val - 1) = (j' = j.val) := by
        apply propext
        constructor
        · intro hz'
          rw [hz', rcIndex_pow j.val hj7] at hstep'
          exact (Option.some.inj hstep').symm
        · intro hjj
          rw [← hj'z, hjj]
      rw [hacc'z z hz]
      simp only [hiff]
      split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega) | (congr 2 <;> omega)
  case hdone =>
    intro j acc hj
    refine ⟨acc, iota0_body_done i_r acc j 6#usize hj, fun z hz => ?_⟩
    cases hstep' : rcIndex z with
    | none => dsimp only
    | some j' =>
      obtain ⟨hj'7, _⟩ := rcIndex_lt z j' hstep'
      have h6 : (6#usize : Std.Usize).val = 6 := by simp
      dsimp only
      rw [if_neg (by omega)]
  obtain ⟨r, hr, hbits⟩ := h
  refine ⟨r, ?_, fun z hz => ?_⟩
  · unfold hacspec_sha3_pedantic.step_mappings.iota_loop0
    exact hr
  · rw [hbits z hz]
    cases hstep' : rcIndex z with
    | none => dsimp only
    | some j' =>
      have h0 : (0#usize : Std.Usize).val = 0 := by simp
      dsimp only
      rw [if_pos (by omega)]


/-! ### The XOR loop, and ι itself -/

theorem iota1_body_cont (rcst lane : Std.Array Bool 64#usize) (z : Std.Usize) (hz : z.val < 64) :
    ∃ s : Std.Usize, s.val = z.val + 1 ∧
      hacspec_sha3_pedantic.step_mappings.iota_loop1.body rcst
          { start := z, «end» := 64#usize } lane
        = ok (.cont ({ start := s, «end» := 64#usize },
            lane.set z (lane.val[z.val]! ^^ rcst.val[z.val]!))) := by
  obtain ⟨s, hs, hnext⟩ := range_next_lt z 64#usize (by simpa using hz)
  refine ⟨s, hs, ?_⟩
  unfold hacspec_sha3_pedantic.step_mappings.iota_loop1.body
  rw [hnext]
  simp [index_usize_eq, array_update_eq, hz]

theorem iota1_body_done (rcst lane : Std.Array Bool 64#usize) :
    hacspec_sha3_pedantic.step_mappings.iota_loop1.body rcst
      { start := 64#usize, «end» := 64#usize } lane = ok (.done lane) := by
  unfold hacspec_sha3_pedantic.step_mappings.iota_loop1.body
  rw [range_next_ge 64#usize 64#usize (le_refl _)]
  simp

theorem iota1_loop (rcst lane : Std.Array Bool 64#usize) :
    ∃ lane' : Std.Array Bool 64#usize,
      hacspec_sha3_pedantic.step_mappings.iota_loop1
          { start := 0#usize, «end» := 64#usize } rcst lane = ok lane' ∧
      ∀ z < 64, lane'.val[z]! = (lane.val[z]! ^^ rcst.val[z]!) := by
  have h := loop_range_eq (β := Std.Array Bool 64#usize) (γ := Std.Array Bool 64#usize)
    (fun p => hacspec_sha3_pedantic.step_mappings.iota_loop1.body rcst p.1 p.2)
    64#usize
    (fun zU acc r => ∀ z < 64, r.val[z]!
      = if zU.val ≤ z then (acc.val[z]! ^^ rcst.val[z]!) else acc.val[z]!)
    ?hstep ?hdone 64 0#usize lane (by simp)
  case hstep =>
    intro i acc hi
    have hi' : i.val < 64 := by simpa using hi
    obtain ⟨s, hs, hbody⟩ := iota1_body_cont rcst acc i hi'
    refine ⟨s, acc.set i (acc.val[i.val]! ^^ rcst.val[i.val]!), hs, hbody, ?_⟩
    intro r hr z hz
    rw [hr z hz, array64_set_get acc i _ z hi' hz]
    have hsv : s.val = i.val + 1 := hs
    split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega) | (congr 2 <;> omega)
  case hdone =>
    refine fun acc => ⟨acc, iota1_body_done rcst acc, fun z hz => ?_⟩
    have h64 : (64#usize : Std.Usize).val = 64 := by simp
    rw [if_neg (by omega)]
  obtain ⟨r, hr, hbits⟩ := h
  refine ⟨r, ?_, fun z hz => ?_⟩
  · unfold hacspec_sha3_pedantic.step_mappings.iota_loop1
    exact hr
  · have h0 : (0#usize : Std.Usize).val ≤ z := by simp
    rw [hbits z hz, if_pos h0]

theorem bitAt_setLane (A : SA) (lane : Std.Array Bool 64#usize) (x y z : Nat)
    (hx : x < 5) (hy : y < 5) (hz : z < 64) :
    bitAt { a := A.a.set 0#usize ((A.a.val[0]!).set 0#usize lane) } x y z
      = if x = 0 ∧ y = 0 then lane.val[z]! else bitAt A x y z := by
  have hlen5 : A.a.val.length = 5 := by simp
  have hlen5' : (A.a.val[0]!).val.length = 5 := by simp
  have h0 : (0#usize : Std.Usize).val = 0 := by simp
  by_cases hxx : x = 0 <;> by_cases hyy : y = 0 <;> simp_all [bitAt]

/-- ι (FIPS 202, Algorithm 6): the round constant of round `i_r`, XORed into the
    lane `A[0, 0]`. -/
theorem iota_eq (A : SA) (i_r : Std.I64)
    (hlo : -1000000000 ≤ i_r.val) (hhi : i_r.val ≤ 1000000000) :
    hacspec_sha3_pedantic.step_mappings.iota A i_r
      = ok (mkSA (iotaBit (bitAt A) i_r.val)) := by
  obtain ⟨rcst, hloop0, hrc⟩ := iota0_loop i_r hlo hhi (Array.repeat 64#usize false)
  obtain ⟨lane', hloop1, hlane⟩ := iota1_loop rcst (A.a.val[0]!.val[0]!)
  have hL : hacspec_sha3_pedantic.state_array.StateArray.L 64#usize = ok 6#usize := by
    unfold hacspec_sha3_pedantic.state_array.StateArray.L
    simp
  have hnew : core.ops.range.RangeInclusive.new 0#usize 6#usize
      = ok ({ start := 0#usize, «end» := 6#usize } : core.ops.range.RangeInclusive Std.Usize) := rfl
  have hidxA : A.a.index_usize 0#usize = ok A.a.val[0]! := index_usize_eq _ _ (by simp)
  have hidxA0 : (A.a.val[0]!).index_usize 0#usize = ok (A.a.val[0]!).val[0]! :=
    index_usize_eq _ _ (by simp)
  have h5idx : (0#usize : Std.Usize).val < (5#usize).val := by simp
  unfold hacspec_sha3_pedantic.step_mappings.iota
  simp only [hL, bind_tc_ok, hnew, hloop0, hidxA, hidxA0, hloop1,
    Std.Array.index_mut_usize, array_update_eq _ _ _ h5idx]
  show ok ({ a := A.a.set 0#usize ((A.a.val[0]!).set 0#usize lane') } : SA) = _
  apply congrArg
  refine ext (fun x y z hx hy hz => ?_)
  rw [bitAt_mkSA _ hx hy hz, bitAt_setLane A lane' x y z hx hy hz, iotaBit]
  by_cases hxy : x = 0 ∧ y = 0
  · obtain ⟨hx0, hy0⟩ := hxy
    subst hx0
    subst hy0
    rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, hlane z hz, hrc z hz, rcBitAt, bitAt]
    cases hstep : rcIndex z with
    | none =>
      dsimp only
      have hzero : (Array.repeat 64#usize false).val[z]! = false := by
        simp only [Std.Array.repeat_val, List.getElem!_eq_getElem?_getD,
          List.getElem?_replicate, show (64#usize : Std.Usize).val = 64 from by simp, hz,
          if_true, Option.getD_some]
      rw [hzero]
    | some j => dsimp only
  · rw [if_neg hxy, if_neg hxy]

-- Pinned by `#guard_msgs`: the build fails if this comes to depend on any axiom
-- beyond Lean's standard three.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.iota_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms iota_eq

end LibcruxIotSha3.Composition.Pedantic
