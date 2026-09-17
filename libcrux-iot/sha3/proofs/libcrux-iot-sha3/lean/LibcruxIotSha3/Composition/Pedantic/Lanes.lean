import LibcruxIotSha3.Composition.Pedantic.Permutation
import LibcruxIotSha3.Composition.Pedantic.RoundConstants
import LibcruxIotSha3.Composition.Pedantic.KeccakC
/-!
# `hacspec_sha3`'s lane-level `Keccak-f[1600]` is the pedantic bit-level one

`hacspec_sha3` keeps the state as 25 `u64` lanes and writes each step mapping as
a `createi` over lane indices; `hacspec_sha3_pedantic` writes them as triple
loops over `(x, y, z)`.  This module shows the two agree bit for bit, so the
FIPS-faithful permutation and the one the existing proofs use are the same
function.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-! ### `createi` -/

theorem usize_ofNat_val (n : Nat) (hn : n < 4294967296) :
    (⟨BitVec.ofNat Std.UScalarTy.Usize.numBits n⟩ : Std.Usize).val = n := by
  show (BitVec.ofNat _ n).toNat = n
  simp only [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hb : Std.UScalarTy.Usize.numBits = System.Platform.numBits := rfl
  have h32 : (32 : Nat) ≤ Std.UScalarTy.Usize.numBits := by
    rw [hb]; have := System.Platform.numBits_eq; omega
  calc n < 4294967296 := hn
    _ = 2 ^ 32 := by norm_num
    _ ≤ 2 ^ Std.UScalarTy.Usize.numBits := Nat.pow_le_pow_right (by decide) h32

/-- A `FnMut` closure that neither reads nor changes its state builds the list
    `[g 0, g 1, …]`. -/
theorem array_from_fn_go_eq {T F : Type} (inst : core.ops.function.FnMut F Std.Usize T)
    (c : F) (g : Nat → T) (N : Nat) (hN : N ≤ 4294967296)
    (hcall : ∀ i : Std.Usize, i.val < N → inst.call_mut c i = ok (g i.val, c)) :
    ∀ n : Nat, n ≤ N →
      rust_primitives.slice.array_from_fn_go inst c n = ok ((List.range n).map g, c) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hnv : (⟨BitVec.ofNat Std.UScalarTy.Usize.numBits n⟩ : Std.Usize).val = n :=
      usize_ofNat_val n (by omega)
    show (do
      let p ← rust_primitives.slice.array_from_fn_go inst c n
      let q ← inst.call_mut p.2 ⟨BitVec.ofNat _ n⟩
      ok (p.1 ++ [q.1], q.2)) = _
    rw [ih (by omega), bind_tc_ok]
    show (do
      let q ← inst.call_mut c ⟨BitVec.ofNat _ n⟩
      ok ((List.range n).map g ++ [q.1], q.2)) = _
    rw [hcall ⟨BitVec.ofNat _ n⟩ (by rw [hnv]; omega), bind_tc_ok, hnv]
    simp [List.range_succ]

/-! ### Reading the lanes -/

/-- The array whose element `i` is `g i`. -/
def mkArr {T : Type} (N : Std.Usize) (g : Nat → T) : Std.Array T N :=
  ⟨(List.range N.val).map g, by simp⟩

theorem mkArr_get {T : Type} [Inhabited T] (N : Std.Usize) (g : Nat → T) {i : Nat}
    (hi : i < N.val) : (mkArr N g).val[i]! = g i := by
  show ((List.range N.val).map g)[i]! = g i
  rw [getElem!_pos _ i (by simp; omega)]
  simp

theorem laneBit_mkArr (g : Nat → Std.U64) {x y z : Nat} (hx : x < 5) (hy : y < 5) :
    laneBit (mkArr 25#usize g) x y z = (g (5 * y + x)).bv.getLsbD z := by
  rw [laneBit, mkArr_get 25#usize g (by simp; omega)]

theorem createi_eq {T F : Type} (N : Std.Usize)
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (g : Nat → T)
    (hN : N.val ≤ 4294967296)
    (hcall : ∀ i : Std.Usize, i.val < N.val → inst.call_mut c i = ok (g i.val, c)) :
    hacspec_sha3.createi N inst c = ok (mkArr N g) := by
  unfold hacspec_sha3.createi core.array.from_fn rust_primitives.slice.array_from_fn
  rw [array_from_fn_go_eq inst c g N.val hN hcall N.val (le_refl _), bind_tc_ok]
  rw [dif_pos (by simp)]
  rfl

/-- `keccak_f::get` reads the lane at `(x, y)`. -/
theorem get_eq (s : Lanes) (x y : Std.Usize) (hx : x.val < 5) (hy : y.val < 5) :
    hacspec_sha3.keccak_f.get s x y = ok s.val[5 * y.val + x.val]! := by
  obtain ⟨i, hi, hiv⟩ := usize_mul_eq 5#usize y (by scalar_tac)
  obtain ⟨j, hj, hjv⟩ := usize_add_eq i x (by scalar_tac)
  have hjn : j.val = 5 * y.val + x.val := by rw [hjv, hiv]; simp
  unfold hacspec_sha3.keccak_f.get
  rw [hi, bind_tc_ok, hj, bind_tc_ok, index_usize_eq s j (by scalar_tac), hjn]


/-! ### Bit-level arithmetic on lanes -/

theorem u64_xor_bit (a b : Std.U64) (z : Nat) :
    (a ^^^ b).bv.getLsbD z = (a.bv.getLsbD z ^^ b.bv.getLsbD z) := by
  show (a.bv ^^^ b.bv).getLsbD z = _
  simp

theorem u64_and_bit (a b : Std.U64) (z : Nat) :
    (a &&& b).bv.getLsbD z = (a.bv.getLsbD z && b.bv.getLsbD z) := by
  show (a.bv &&& b.bv).getLsbD z = _
  simp

theorem u64_not_bit (a : Std.U64) (z : Nat) (hz : z < 64) :
    (~~~ a).bv.getLsbD z = !a.bv.getLsbD z := by
  show (~~~ a.bv).getLsbD z = _
  simp [hz]

/-- Rotating a lane left by `r` moves bit `(z - r) mod 64` to bit `z`, which is
    exactly the index ρ reads from. -/
theorem rotate_left_bit (v : Std.U64) (r : Std.U32) (z : Nat) (hz : z < 64) :
    (Std.UScalar.rotate_left v r).bv.getLsbD z = v.bv.getLsbD (rotIndex r.val z) := by
  show (v.bv.rotateLeft r.val).getLsbD z = _
  rw [BitVec.getLsbD_rotateLeft]
  have hm : r.val % 64 < 64 := Nat.mod_lt _ (by omega)
  by_cases h : z < r.val % 64
  · simp only [h, decide_true, cond_true]
    congr 1
    simp only [rotIndex]
    omega
  · simp only [h, decide_false, cond_false, hz, decide_true, Bool.true_and]
    congr 1
    simp only [rotIndex]
    omega

/-! ### θ -/

/-- θ's `C[x]` (FIPS 202, Algorithm 1 step 1). -/
def cLane (s : Lanes) (x : Nat) : Std.U64 :=
  (((s.val[5 * 0 + x]! ^^^ s.val[5 * 1 + x]!) ^^^ s.val[5 * 2 + x]!) ^^^ s.val[5 * 3 + x]!)
    ^^^ s.val[5 * 4 + x]!

/-- θ's `D[x]` (step 2). -/
def dLane (c : Std.Array Std.U64 5#usize) (x : Nat) : Std.U64 :=
  c.val[(x + 4) % 5]! ^^^ Std.UScalar.rotate_left c.val[(x + 1) % 5]! 1#u32

/-- θ on lanes (step 3). -/
def thetaLanes (s : Lanes) : Lanes :=
  mkArr 25#usize (fun t => s.val[t]! ^^^ (mkArr 5#usize (dLane (mkArr 5#usize (cLane s)))).val[t % 5]!)

theorem theta_lanes_eq (s : Lanes) : hacspec_sha3.keccak_f.theta s = ok (thetaLanes s) := by
  have hc : hacspec_sha3.createi 5#usize
      hacspec_sha3.keccak_f.theta.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 s
      = ok (mkArr 5#usize (cLane s)) := by
    refine createi_eq _ _ _ _ (by simp) ?_
    intro i hi
    have hi5 : i.val < 5 := by simpa using hi
    unfold hacspec_sha3.keccak_f.theta.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
    show hacspec_sha3.keccak_f.theta.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut s i
      = _
    unfold hacspec_sha3.keccak_f.theta.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
    rw [get_eq s i 0#usize hi5 (by simp), get_eq s i 1#usize hi5 (by simp),
      get_eq s i 2#usize hi5 (by simp), get_eq s i 3#usize hi5 (by simp),
      get_eq s i 4#usize hi5 (by simp)]
    simp [Std.lift, cLane]
  have hd : hacspec_sha3.createi 5#usize
      hacspec_sha3.keccak_f.theta.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      (mkArr 5#usize (cLane s))
      = ok (mkArr 5#usize (dLane (mkArr 5#usize (cLane s)))) := by
    refine createi_eq _ _ _ _ (by simp) ?_
    intro i hi
    have hi5 : i.val < 5 := by simpa using hi
    unfold hacspec_sha3.keccak_f.theta.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
    show hacspec_sha3.keccak_f.theta.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      (mkArr 5#usize (cLane s)) i = _
    unfold hacspec_sha3.keccak_f.theta.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
    obtain ⟨a, ha, hav⟩ := usize_add_eq i 4#usize (by scalar_tac)
    obtain ⟨a1, ha1, ha1v⟩ := usize_rem_eq a 5#usize (by simp)
    obtain ⟨b, hb, hbv⟩ := usize_add_eq i 1#usize (by scalar_tac)
    obtain ⟨b1, hb1, hb1v⟩ := usize_rem_eq b 5#usize (by simp)
    have ha1n : a1.val = (i.val + 4) % 5 := by rw [ha1v, hav]; simp
    have hb1n : b1.val = (i.val + 1) % 5 := by rw [hb1v, hbv]; simp
    simp only [ha, ha1, hb, hb1, bind_tc_ok,
      index_usize_eq (mkArr 5#usize (cLane s)) a1 (by rw [ha1n]; simp; omega),
      index_usize_eq (mkArr 5#usize (cLane s)) b1 (by rw [hb1n]; simp; omega),
      core.num.U64.rotate_left, rust_primitives.arithmetic.rotate_left_u64,
      Std.lift, ha1n, hb1n, dLane]
  unfold hacspec_sha3.keccak_f.theta
  rw [hc, bind_tc_ok, hd, bind_tc_ok]
  refine createi_eq _ _ _ _ (by simp) ?_
  intro i hi
  have hi25 : i.val < 25 := by simpa using hi
  unfold hacspec_sha3.keccak_f.theta.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  show hacspec_sha3.keccak_f.theta.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
    (s, mkArr 5#usize (dLane (mkArr 5#usize (cLane s)))) i = _
  unfold hacspec_sha3.keccak_f.theta.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  obtain ⟨m, hm, hmv⟩ := usize_rem_eq i 5#usize (by simp)
  have hmn : m.val = i.val % 5 := by rw [hmv]; simp
  show (do
      let i1 ← Std.Array.index_usize s i
      let i2 ← i % 5#usize
      let i3 ← Std.Array.index_usize (mkArr 5#usize (dLane (mkArr 5#usize (cLane s)))) i2
      let i4 ← Std.lift (i1 ^^^ i3)
      ok (i4, (s, mkArr 5#usize (dLane (mkArr 5#usize (cLane s)))))) = _
  simp only [index_usize_eq s i (by simp; omega), hm, bind_tc_ok,
    index_usize_eq (mkArr 5#usize (dLane (mkArr 5#usize (cLane s)))) m
      (by rw [hmn]; simp; omega), hmn, Std.lift]
  rfl

theorem theta_bit (s : Lanes) (x y z : Nat) (hx : x < 5) (hy : y < 5) (hz : z < 64) :
    laneBit (thetaLanes s) x y z = thetaBit (laneBit s) x y z := by
  have hcb : ∀ (x' z' : Nat), x' < 5 →
      ((mkArr 5#usize (cLane s)).val[x']!).bv.getLsbD z' = cBit (laneBit s) x' z' := by
    intro x' z' hx'
    rw [mkArr_get 5#usize (cLane s) (by simp; omega)]
    simp only [cLane, cBit, laneBit, u64_xor_bit]
  have hrot : rotIndex (1#u32 : Std.U32).val z = (z + 63) % 64 := by
    simp [rotIndex]
  have hdb : ((mkArr 5#usize (dLane (mkArr 5#usize (cLane s)))).val[x]!).bv.getLsbD z
      = dBit (cBit (laneBit s)) x z := by
    rw [mkArr_get 5#usize _ (by simp; omega)]
    simp only [dLane, u64_xor_bit]
    rw [rotate_left_bit _ _ z hz, hrot, hcb ((x + 4) % 5) z (by omega),
      hcb ((x + 1) % 5) ((z + 63) % 64) (by omega)]
    rfl
  rw [thetaLanes, laneBit_mkArr _ hx hy]
  simp only [u64_xor_bit]
  rw [show (5 * y + x) % 5 = x from by omega, hdb]
  simp only [thetaBit, laneBit]


/-! ### ρ -/

/-- ρ on lanes: rotate each lane by its tabulated offset. -/
def rhoLanes (s : Lanes) : Lanes :=
  mkArr 25#usize (fun t =>
    Std.UScalar.rotate_left s.val[t]! hacspec_sha3.keccak_f.RHO_OFFSETS.val[t]!)

theorem rho_lanes_eq (s : Lanes) : hacspec_sha3.keccak_f.rho s = ok (rhoLanes s) := by
  unfold hacspec_sha3.keccak_f.rho
  refine createi_eq _ _ _ _ (by simp) ?_
  intro i hi
  have hi25 : i.val < 25 := by simpa using hi
  unfold hacspec_sha3.keccak_f.rho.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  show hacspec_sha3.keccak_f.rho.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut s i = _
  unfold hacspec_sha3.keccak_f.rho.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  simp only [index_usize_eq s i (by simp; omega),
    index_usize_eq hacspec_sha3.keccak_f.RHO_OFFSETS i (by simp; omega), bind_tc_ok,
    core.num.U64.rotate_left, rust_primitives.arithmetic.rotate_left_u64]

/-- The tabulated rotation offsets are the ones FIPS 202's ρ walk produces
    (modulo the lane width, which is all `rotIndex` sees). -/
theorem rho_offsets_table : ∀ x < 5, ∀ y < 5,
    (hacspec_sha3.keccak_f.RHO_OFFSETS.val[5 * y + x]!).val % 64 = rhoOffsetOf x y % 64 := by
  simp only [hacspec_sha3.keccak_f.RHO_OFFSETS]
  decide

theorem rho_bit (s : Lanes) (x y z : Nat) (hx : x < 5) (hy : y < 5) (hz : z < 64) :
    laneBit (rhoLanes s) x y z = rhoBit (laneBit s) x y z := by
  rw [rhoLanes, laneBit_mkArr _ hx hy, rotate_left_bit _ _ z hz]
  simp only [rhoBit, laneBit, rotIndex, rho_offsets_table x hx y hy]

/-! ### π -/

/-- π on lanes: lane `(x, y)` takes the old lane `((x + 3y) mod 5, x)`. -/
def piLanes (s : Lanes) : Lanes :=
  mkArr 25#usize (fun t => s.val[5 * (t % 5) + ((t % 5 + 3 * (t / 5)) % 5)]!)

theorem pi_lanes_eq (s : Lanes) : hacspec_sha3.keccak_f.pi s = ok (piLanes s) := by
  unfold hacspec_sha3.keccak_f.pi
  refine createi_eq _ _ _ _ (by simp) ?_
  intro i hi
  have hi25 : i.val < 25 := by simpa using hi
  unfold hacspec_sha3.keccak_f.pi.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  show hacspec_sha3.keccak_f.pi.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut s i = _
  unfold hacspec_sha3.keccak_f.pi.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  obtain ⟨yv, hy, hyv⟩ := usize_div_eq i 5#usize (by simp)
  obtain ⟨xv, hx, hxv⟩ := usize_rem_eq i 5#usize (by simp)
  obtain ⟨a, ha, hav⟩ := usize_mul_eq 3#usize yv (by scalar_tac)
  obtain ⟨b, hb, hbv⟩ := usize_add_eq xv a (by scalar_tac)
  obtain ⟨c, hc, hcv⟩ := usize_rem_eq b 5#usize (by simp)
  have hyn : yv.val = i.val / 5 := by rw [hyv]; simp
  have hxn : xv.val = i.val % 5 := by rw [hxv]; simp
  have hcn : c.val = (i.val % 5 + 3 * (i.val / 5)) % 5 := by
    rw [hcv, hbv, hav, hxn, hyn]; simp
  simp only [hy, hx, ha, hb, hc, bind_tc_ok,
    get_eq s c xv (by rw [hcn]; omega) (by rw [hxn]; omega), hcn, hxn]

theorem pi_bit (s : Lanes) (x y z : Nat) (hx : x < 5) (hy : y < 5) :
    laneBit (piLanes s) x y z = piBit (laneBit s) x y z := by
  rw [piLanes, laneBit_mkArr _ hx hy]
  rw [show (5 * y + x) % 5 = x from by omega, show (5 * y + x) / 5 = y from by omega]
  rfl

/-! ### χ -/

/-- χ on lanes (FIPS 202, Algorithm 4). -/
def chiLanes (s : Lanes) : Lanes :=
  mkArr 25#usize (fun t =>
    s.val[5 * (t / 5) + t % 5]! ^^^
      ((~~~ s.val[5 * (t / 5) + (t % 5 + 1) % 5]!) &&&
        s.val[5 * (t / 5) + (t % 5 + 2) % 5]!))

theorem chi_lanes_eq (s : Lanes) : hacspec_sha3.keccak_f.chi s = ok (chiLanes s) := by
  unfold hacspec_sha3.keccak_f.chi
  refine createi_eq _ _ _ _ (by simp) ?_
  intro i hi
  have hi25 : i.val < 25 := by simpa using hi
  unfold hacspec_sha3.keccak_f.chi.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  show hacspec_sha3.keccak_f.chi.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut s i = _
  unfold hacspec_sha3.keccak_f.chi.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  obtain ⟨yv, hy, hyv⟩ := usize_div_eq i 5#usize (by simp)
  obtain ⟨xv, hx, hxv⟩ := usize_rem_eq i 5#usize (by simp)
  obtain ⟨a, ha, hav⟩ := usize_add_eq xv 1#usize (by scalar_tac)
  obtain ⟨a1, ha1, ha1v⟩ := usize_rem_eq a 5#usize (by simp)
  obtain ⟨b, hb, hbv⟩ := usize_add_eq xv 2#usize (by scalar_tac)
  obtain ⟨b1, hb1, hb1v⟩ := usize_rem_eq b 5#usize (by simp)
  have hyn : yv.val = i.val / 5 := by rw [hyv]; simp
  have hxn : xv.val = i.val % 5 := by rw [hxv]; simp
  have ha1n : a1.val = (i.val % 5 + 1) % 5 := by rw [ha1v, hav, hxn]; simp
  have hb1n : b1.val = (i.val % 5 + 2) % 5 := by rw [hb1v, hbv, hxn]; simp
  simp only [hy, hx, ha, ha1, hb, hb1, bind_tc_ok,
    get_eq s xv yv (by rw [hxn]; omega) (by rw [hyn]; omega),
    get_eq s a1 yv (by rw [ha1n]; omega) (by rw [hyn]; omega),
    get_eq s b1 yv (by rw [hb1n]; omega) (by rw [hyn]; omega),
    Std.lift, hyn, hxn, ha1n, hb1n]

theorem chi_bit (s : Lanes) (x y z : Nat) (hx : x < 5) (hy : y < 5) (hz : z < 64) :
    laneBit (chiLanes s) x y z = chiBit (laneBit s) x y z := by
  rw [chiLanes, laneBit_mkArr _ hx hy]
  rw [show (5 * y + x) % 5 = x from by omega, show (5 * y + x) / 5 = y from by omega]
  rw [u64_xor_bit, u64_and_bit, u64_not_bit _ z hz]
  rfl

/-! ### ι -/

/-- ι on lanes: XOR the round constant into lane `(0, 0)`. -/
def iotaLanes (s : Lanes) (r : Std.Usize) : Lanes :=
  s.set 0#usize (s.val[0]! ^^^ hacspec_sha3.keccak_f.ROUND_CONSTANTS.val[r.val]!)

theorem iota_lanes_eq (s : Lanes) (r : Std.Usize) (hr : r.val < 24) :
    hacspec_sha3.keccak_f.iota s r = ok (iotaLanes s r) := by
  unfold hacspec_sha3.keccak_f.iota
  simp only [index_usize_eq hacspec_sha3.keccak_f.ROUND_CONSTANTS r (by simp; omega),
    index_usize_eq s 0#usize (by simp), bind_tc_ok, Std.lift,
    array_update_eq s 0#usize _ (by simp)]
  rfl

theorem iota_bit (s : Lanes) (r : Std.Usize) (hr : r.val < 24) (x y z : Nat)
    (hx : x < 5) (hy : y < 5) (hz : z < 64) :
    laneBit (iotaLanes s r) x y z = iotaBit (laneBit s) (r.val : Int) x y z := by
  have hset : ∀ i : Nat, i < 25 →
      (iotaLanes s r).val[i]! =
        if i = 0 then s.val[0]! ^^^ hacspec_sha3.keccak_f.ROUND_CONSTANTS.val[r.val]!
        else s.val[i]! := by
    intro i hi
    have hlen : s.val.length = 25 := s.property
    show (s.val.set 0 _)[i]! = _
    rw [getElem!_pos _ i (by simp; omega), getElem!_pos s.val i (by omega)]
    rw [List.getElem_set]
    by_cases h : i = 0 <;> simp [h]
  rw [laneBit, hset (5 * y + x) (by omega)]
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos (by omega)]
    rw [u64_xor_bit, ← rcBitAt_table r.val hr z hz]
    simp only [iotaBit, laneBit]
    simp
  · rw [if_neg (show 5 * y + x ≠ 0 from by omega)]
    simp only [iotaBit, laneBit, if_neg h]


/-! ### One round, and the 24-round permutation -/

/-- One round of `Keccak-f[1600]` on lanes. -/
def roundLanes (s : Lanes) (r : Std.Usize) : Lanes :=
  iotaLanes (chiLanes (piLanes (rhoLanes (thetaLanes s)))) r

theorem round_lanes_bit (s : Lanes) (r : Std.Usize) (hr : r.val < 24) :
    AgreeInRange (laneBit (roundLanes s r)) (roundBit (laneBit s) (r.val : Int)) := by
  have h1 : AgreeInRange (laneBit (thetaLanes s)) (thetaBit (laneBit s)) :=
    fun x hx y hy z hz => theta_bit s x y z hx hy hz
  have h2 : AgreeInRange (laneBit (rhoLanes (thetaLanes s))) (rhoBit (thetaBit (laneBit s))) :=
    AgreeInRange.trans (fun x hx y hy z hz => rho_bit _ x y z hx hy hz) (rhoBit_congr h1)
  have h3 : AgreeInRange (laneBit (piLanes (rhoLanes (thetaLanes s))))
      (piBit (rhoBit (thetaBit (laneBit s)))) :=
    AgreeInRange.trans (fun x hx y hy z _ => pi_bit _ x y z hx hy) (piBit_congr h2)
  have h4 : AgreeInRange (laneBit (chiLanes (piLanes (rhoLanes (thetaLanes s)))))
      (chiBit (piBit (rhoBit (thetaBit (laneBit s))))) :=
    AgreeInRange.trans (fun x hx y hy z hz => chi_bit _ x y z hx hy hz) (chiBit_congr h3)
  exact AgreeInRange.trans (fun x hx y hy z hz => iota_bit _ r hr x y z hx hy hz)
    (iotaBit_congr _ h4)

theorem round_body_cont (i : Std.Usize) (acc : Lanes) (hi : i.val < 24) :
    ∃ t : Std.Usize, t.val = i.val + 1 ∧
      hacspec_sha3.keccak_f.keccak_f_loop.body { start := i, «end» := 24#usize } acc
        = ok (.cont ({ start := t, «end» := 24#usize }, roundLanes acc i)) := by
  obtain ⟨t, ht, hnext⟩ := range_next_lt i 24#usize (by simpa using hi)
  refine ⟨t, ht, ?_⟩
  unfold hacspec_sha3.keccak_f.keccak_f_loop.body
  rw [hnext]
  show (do
      let a ← hacspec_sha3.keccak_f.theta acc
      let a1 ← hacspec_sha3.keccak_f.rho a
      let a2 ← hacspec_sha3.keccak_f.pi a1
      let a3 ← hacspec_sha3.keccak_f.chi a2
      let state1 ← hacspec_sha3.keccak_f.iota a3 i
      ok (ControlFlow.cont
        (({ start := t, «end» := 24#usize } : core.ops.range.Range Std.Usize), state1))) = _
  simp only [bind_tc_ok, theta_lanes_eq, rho_lanes_eq, pi_lanes_eq, chi_lanes_eq,
    iota_lanes_eq _ i hi, roundLanes]

/-- `Keccak-f[1600]` on lanes is the pedantic 24-round permutation. -/
theorem keccak_f_lanes_eq (s : Lanes) :
    ∃ s' : Lanes, hacspec_sha3.keccak_f.keccak_f s = ok s' ∧
      AgreeInRange (laneBit s') (roundsFrom (laneBit s) 0 24) := by
  have h := loop_range_eq_inv_usize (β := Lanes) (γ := Lanes)
    (fun q => hacspec_sha3.keccak_f.keccak_f_loop.body q.1 q.2)
    24#usize
    (fun i acc => AgreeInRange (laneBit acc) (roundsFrom (laneBit s) 0 i.val))
    (fun _ _ r => AgreeInRange (laneBit r) (roundsFrom (laneBit s) 0 24))
    ?hstep ?hdone 24 0#usize s (by simp) (AgreeInRange.refl (laneBit s))
  · obtain ⟨r, hr, hrv⟩ := h
    exact ⟨r, hr, hrv⟩
  case hstep =>
    intro i acc hi hinv
    have hi24 : i.val < 24 := by simpa using hi
    obtain ⟨t, ht, hbody⟩ := round_body_cont i acc hi24
    refine ⟨t, roundLanes acc i, ht, ?_, hbody, fun r hr => hr⟩
    rw [ht]
    show AgreeInRange (laneBit (roundLanes acc i))
      (roundBit (roundsFrom (laneBit s) 0 i.val) (0 + (i.val : Int)))
    rw [show (0 : Int) + (i.val : Int) = (i.val : Int) from by ring]
    exact AgreeInRange.trans (round_lanes_bit acc i hi24) (roundBit_congr _ hinv)
  case hdone =>
    intro acc hinv
    refine ⟨acc, ?_, by simpa using hinv⟩
    unfold hacspec_sha3.keccak_f.keccak_f_loop.body
    rw [range_next_ge 24#usize 24#usize (le_refl _)]
    simp


/-! ### The lane state as a flat bit string -/

/-- The 1600 bits of a 25-lane state, in the FIPS order `S[64(5y + x) + z]`. -/
def lanesToBits (s : Lanes) : List Bool :=
  (List.range 1600).map (fun p => laneBit s ((p / 64) % 5) (p / 320) (p % 64))

@[simp]
theorem lanesToBits_len (s : Lanes) : (lanesToBits s).length = 1600 := by
  simp [lanesToBits]

theorem lanesToBits_get (s : Lanes) {x y z : Nat} (hx : x < 5) (hy : y < 5) (hz : z < 64) :
    (lanesToBits s)[bitPos x y z]! = laneBit s x y z := by
  have hlt : bitPos x y z < 1600 := by simp only [bitPos]; omega
  have h1 : (bitPos x y z / 64) % 5 = x := by simp only [bitPos]; omega
  have h2 : bitPos x y z / 320 = y := by simp only [bitPos]; omega
  have h3 : bitPos x y z % 64 = z := by simp only [bitPos]; omega
  simp only [lanesToBits]
  rw [getElem!_pos _ _ (by simp only [List.length_map, List.length_range]; exact hlt)]
  simp only [List.getElem_map, List.getElem_range, h1, h2, h3]

theorem bitsOfList_lanesToBits (s : Lanes) :
    AgreeInRange (bitsOfList (lanesToBits s)) (laneBit s) :=
  fun _ hx _ hy _ hz => lanesToBits_get s hx hy hz

/-- `hacspec_sha3`'s `Keccak-f[1600]`, read as a function on the 1600 bits, is
    the `keccakF` the pedantic sponge uses. -/
theorem keccakF_lanes_eq (s : Lanes) :
    ∃ s' : Lanes, hacspec_sha3.keccak_f.keccak_f s = ok s' ∧
      keccakF (lanesToBits s) = lanesToBits s' := by
  obtain ⟨s', hs', hbit⟩ := keccak_f_lanes_eq s
  refine ⟨s', hs', ?_⟩
  have hcongr := roundsFrom_congr (0 : Int) 24 (bitsOfList_lanesToBits s)
  show keccakF (lanesToBits s)
    = (List.range 1600).map (fun p => laneBit s' ((p / 64) % 5) (p / 320) (p % 64))
  simp only [keccakF]
  apply List.map_congr_left
  intro p hp
  have hp1600 : p < 1600 := by simpa using hp
  have hx : (p / 64) % 5 < 5 := by omega
  have hy : p / 320 < 5 := by omega
  have hz : p % 64 < 64 := by omega
  rw [hcongr _ hx _ hy _ hz, ← hbit _ hx _ hy _ hz]

-- Pin the lane-level permutation bridge to Lean's standard three axioms.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.keccakF_lanes_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms keccakF_lanes_eq

end LibcruxIotSha3.Composition.Pedantic
