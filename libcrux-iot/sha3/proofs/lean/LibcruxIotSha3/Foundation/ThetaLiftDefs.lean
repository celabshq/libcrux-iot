/-
  θ-step — definitions and helper specs.

  This file contains the building blocks consumed by `theta_lift_spec`
  (the public spec-coupling theorem in `ThetaLift.lean`):
  - 11 sub-function `@[spec]`s (`theta_c_x{0..4}_z{0,1}`, `theta_d`).
  - The composed impl post `theta_comp_spec_local` (12-conjunct form
    in terms of the original `s.st` halves).
  - `lift_theta_applied` (the spec-equivalent state computed from a
    post-θ impl `r_impl`).
  - 25 `lift_getElem_bv_*` peel lemmas for the algebraic close.

  Editing `theta_lift_spec`'s proof body in `ThetaLift.lean` does not
  invalidate this file's cache.
-/
import LibcruxIotSha3.Foundation.Lift
import LibcruxIotSha3.Foundation.UScalarAC
import HacspecSha3
import Hax

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Foundation

set_option mvcgen.warning false

attribute [local spec] Aeneas.Std.uncurry

/-! ## Bridge 1: characterizing `keccak_f.{theta, rho, pi, chi}`

The hacspec definitions of `theta`/`rho`/`pi`/`chi` call `createi N inst c` —
which expands to `CoreModels.rust_primitives.slice.array_from_fn N inst.FnMutInst c` —
with closures whose `call_mut` returns `.ok (call state args, state)` (pure
closures).

We characterize each function by a pure `_applied` form through a generic
`@[spec]` lemma `createi_pure_spec` (handling `createi` for pure closures),
plus six per-closure purity lemmas (one for each of θ's 3, ρ/π/χ's 1
closures). -/

/-- Per-element foldlM evaluation for pure closures. The closure state `c`
    is invariant; the result list is `acc ++ l.map f`. -/
private theorem createi_foldlM_pure_aux
    {T F : Type}
    (inst : CoreModels.core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (l : List Nat) (acc : List T)
    (hpure : ∀ k ∈ l,
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    l.foldlM
      (fun (s : List T × F) (i : Nat) => do
        let (v, f') ← inst.call_mut s.2 ⟨BitVec.ofNat _ i⟩
        Result.ok (s.1 ++ [v], f'))
      (acc, c) = .ok (acc ++ l.map f, c) := by
  induction l generalizing acc with
  | nil =>
      simp only [List.foldlM_nil, List.map_nil, List.append_nil]
      rfl
  | cons h t ih =>
      have hh : inst.call_mut c ⟨BitVec.ofNat _ h⟩ = .ok (f h, c) :=
        hpure h List.mem_cons_self
      have ht : ∀ k ∈ t, inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) :=
        fun k hk => hpure k (List.mem_cons_of_mem _ hk)
      have hih := ih (acc ++ [f h]) ht
      simp only [List.foldlM_cons, hh, bind_tc_ok, List.map_cons]
      rw [hih]
      simp [List.append_assoc]

/-- Lean-level equation for `createi` over pure closures. Used to power
    `createi_pure_spec` (Triple form). -/
theorem createi_pure_eq
    {T F : Type} (N : Std.Usize)
    (inst : CoreModels.core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    createi N inst c =
      .ok ⟨(List.range N.val).map f,
           by simp [List.length_map, List.length_range]⟩ := by
  have hf : ∀ k ∈ List.range N.val,
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) := by
    intro k hk; exact hpure k (List.mem_range.mp hk)
  have h_fold :=
    createi_foldlM_pure_aux inst c f (List.range N.val) [] hf
  simp only [List.nil_append] at h_fold
  unfold createi CoreModels.core.array.from_fn CoreModels.rust_primitives.slice.array_from_fn
  split
  · rename_i e heq
    rw [h_fold] at heq; exact absurd heq (by simp)
  · rename_i heq
    rw [h_fold] at heq; exact absurd heq (by simp)
  · rename_i result heq
    rw [h_fold] at heq
    have hres : result = ((List.range N.val).map f, c) :=
      (Result.ok.inj heq).symm
    subst hres
    rfl

/-- **Generic pure-closure `[spec]` for `createi`.**

For any closure whose `call_mut` is pure (doesn't mutate captured state),
`createi N inst c` succeeds and its `i`-th cell is `f i`. The hypothesis
`hpure` is a Triple over each call_mut so `hax_mvcgen` can recurse into
it via per-closure `@[spec]` lemmas.

Tagged `@[spec]` so `hax_mvcgen` chains through nested `createi` calls
in `keccak_f.theta` (3 calls) and `keccak_f.{rho,pi,chi}` (1 call each). -/
@[spec]
theorem createi_pure_spec
    {T F : Type} [Inhabited T] (N : Std.Usize)
    (inst : CoreModels.core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      ⦃ ⌜ True ⌝ ⦄
      inst.call_mut c ⟨BitVec.ofNat _ k⟩
      ⦃ ⇓ r => ⌜ r = (f k, c) ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    createi N inst c
    ⦃ ⇓ a => ⌜ ∀ i : Nat, i < N.val → a.val[i]! = f i ⌝ ⦄ := by
  have hpure_eq : ∀ k : Nat, k < N.val →
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) :=
    fun k hk => result_eq_of_triple (hpure k hk)
  have heq := createi_pure_eq N inst c f hpure_eq
  rw [heq]
  simp only [Triple, WP.wp, PredTrans.apply]
  apply SPred.pure_intro
  intro i hi
  show ((List.range N.val).map f)[i]! = f i
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi]
  rfl

/-! ### Per-closure purity (Triple form, `[spec]`-tagged for `hax_mvcgen`)

Each hacspec closure used inside `theta`/`rho`/`pi`/`chi` has the shape:
`call_mut state args := do v ← call state args; ok (v, state)` (state-preserving).
We state the per-cell purity as a `@[spec]` Triple so `hax_mvcgen` chains
through it when applied to a `createi`. -/

/-- `f`-side of theta's first closure (computes column XORs).
    Under the new spec layout, `C[k] = ⊕_y state[5*y + k]`. -/
def theta_closure_c_at (state : Std.Array Std.U64 25#usize) (k : Nat) :
    Std.U64 :=
  state.val[k]! ^^^ state.val[5+k]! ^^^ state.val[10+k]! ^^^
    state.val[15+k]! ^^^ state.val[20+k]!

/-- `@[spec]` for `keccak_f.get` (new layout): `get state x y = state[5*y + x]`. -/
@[spec]
private theorem keccak_f_get_spec
    (state : Std.Array Std.U64 25#usize) (x y : Std.Usize)
    (hbound : 5 * y.val + x.val < 25) :
    ⦃ ⌜ True ⌝ ⦄ keccak_f.get state x y
    ⦃ ⇓ r => ⌜ r = state.val[5*y.val + x.val]! ⌝ ⦄ := by
  unfold keccak_f.get
  hax_mvcgen
  all_goals first | scalar_tac | simp_all

/-- Purity of theta's first closure (5 column-XORs). -/
@[spec]
theorem theta_closure_call_mut_spec
    (state : Std.Array Std.U64 25#usize) (k : Std.Usize) (hk : k.val < 5) :
    ⦃ ⌜ True ⌝ ⦄
    keccak_f.theta.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      state k
    ⦃ ⇓ r => ⌜ r = (theta_closure_c_at state k.val, state) ⌝ ⦄ := by
  unfold keccak_f.theta.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        theta_closure_c_at
  hax_mvcgen
  all_goals scalar_tac

/-- `f`-side of theta's second closure (5 d-values: `c[(k+4)%5] ^^^
    rotateLeft64(c[(k+1)%5], 1)`). -/
def theta_closure_1_d_at (c : Std.Array Std.U64 5#usize) (k : Nat) :
    Std.U64 :=
  c.val[(k + 4) % 5]! ^^^ ⟨(c.val[(k + 1) % 5]!).bv.rotateLeft 1⟩

/-- Purity of theta's second closure (5 d-values). -/
@[spec]
theorem theta_closure_1_call_mut_spec
    (c : Std.Array Std.U64 5#usize) (k : Std.Usize) (hk : k.val < 5) :
    ⦃ ⌜ True ⌝ ⦄
    keccak_f.theta.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c k
    ⦃ ⇓ r => ⌜ r = (theta_closure_1_d_at c k.val, c) ⌝ ⦄ := by
  have h4 : (k.val + 4) % 5 < c.val.length := by simp; omega
  have h1 : (k.val + 1) % 5 < c.val.length := by simp; omega
  have h4_eq : c.val[(k.val + 4) % 5]! = c.val[(k.val + 4) % 5]'h4 := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h4]; rfl
  have h1_eq : c.val[(k.val + 1) % 5]! = c.val[(k.val + 1) % 5]'h1 := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  unfold keccak_f.theta.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        theta_closure_1_d_at
  hax_mvcgen
  all_goals (first | scalar_tac | (simp; scalar_tac)
                   | (congr 1; rw [h4_eq, h1_eq];
                      apply Std.U64.bv_eq_imp_eq;
                      simp_all [Std.UScalar.bv_xor, Std.UScalar.rotate_left]))

/-- `f`-side of theta's third closure (25 final state values).
    With the `k = 5*y + x` layout, `x = k % 5` and `D[x] = d[k%5]`. -/
def theta_closure_2_at
    (sd : Std.Array Std.U64 25#usize × Std.Array Std.U64 5#usize) (k : Nat) :
    Std.U64 :=
  sd.1.val[k]! ^^^ sd.2.val[k % 5]!

/-- Purity of theta's third closure (25 final values). -/
@[spec]
theorem theta_closure_2_call_mut_spec
    (sd : Std.Array Std.U64 25#usize × Std.Array Std.U64 5#usize)
    (k : Std.Usize) (hk : k.val < 25) :
    ⦃ ⌜ True ⌝ ⦄
    keccak_f.theta.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      sd k
    ⦃ ⇓ r => ⌜ r = (theta_closure_2_at sd k.val, sd) ⌝ ⦄ := by
  have h25 : k.val < sd.1.val.length := by simp; omega
  have h5 : k.val % 5 < sd.2.val.length := by simp; omega
  have h25_eq : sd.1.val[k.val]! = sd.1.val[k.val]'h25 := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h25]; rfl
  have h5_eq : sd.2.val[k.val % 5]! = sd.2.val[k.val % 5]'h5 := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h5]; rfl
  unfold keccak_f.theta.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        theta_closure_2_at
  hax_mvcgen
  all_goals (first | scalar_tac | (simp; scalar_tac)
                   | (congr 1; rw [h25_eq, h5_eq];
                      apply Std.U64.bv_eq_imp_eq;
                      simp_all [Std.UScalar.bv_xor]))

/-- `f`-side of `rho`'s closure (25 lane-rotations). -/
def rho_closure_at (state : Std.Array Std.U64 25#usize) (k : Nat) :
    Std.U64 :=
  ⟨(state.val[k]!).bv.rotateLeft (keccak_f.RHO_OFFSETS.val[k]!).val⟩

/-- Purity of `rho`'s closure. -/
@[spec]
theorem rho_closure_call_mut_spec
    (state : Std.Array Std.U64 25#usize) (k : Std.Usize) (hk : k.val < 25) :
    ⦃ ⌜ True ⌝ ⦄
    keccak_f.rho.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      state k
    ⦃ ⇓ r => ⌜ r = (rho_closure_at state k.val, state) ⌝ ⦄ := by
  have hs : k.val < state.val.length := by simp; omega
  have hr : k.val < keccak_f.RHO_OFFSETS.val.length := by simp; omega
  have hs_eq : state.val[k.val]! = state.val[k.val]'hs := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hs]; rfl
  have hr_eq : keccak_f.RHO_OFFSETS.val[k.val]!
             = keccak_f.RHO_OFFSETS.val[k.val]'hr := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hr]; rfl
  unfold keccak_f.rho.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        rho_closure_at
  hax_mvcgen
  all_goals (first | scalar_tac | (simp; scalar_tac)
                   | (congr 1; rw [hs_eq, hr_eq];
                      simp_all [Std.UScalar.rotate_left]))

/-- `f`-side of `pi`'s closure (lane permutation). With the `5*y + x`
    layout, `A[x,y]` is at position `5*y + x`, so π's output at `k = 5*y + x`
    reads `state[5*x + (x+3y)%5]`. -/
def pi_closure_at (state : Std.Array Std.U64 25#usize) (k : Nat) :
    Std.U64 :=
  state.val[5 * (k % 5) + ((k % 5) + 3 * (k / 5)) % 5]!

/-- Purity of `pi`'s closure. -/
@[spec]
theorem pi_closure_call_mut_spec
    (state : Std.Array Std.U64 25#usize) (k : Std.Usize) (_hk : k.val < 25) :
    ⦃ ⌜ True ⌝ ⦄
    keccak_f.pi.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      state k
    ⦃ ⇓ r => ⌜ r = (pi_closure_at state k.val, state) ⌝ ⦄ := by
  unfold keccak_f.pi.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        pi_closure_at
  hax_mvcgen
  all_goals scalar_tac

/-- `f`-side of `chi`'s closure (new layout `A[x,y]` at `5*y + x`):
    `state[5y+x] ^^^ ((¬state[5y+(x+1)%5]) &&& state[5y+(x+2)%5])`,
    where `y = k/5`, `x = k%5`. -/
def chi_closure_at (state : Std.Array Std.U64 25#usize) (k : Nat) :
    Std.U64 :=
  let y := k / 5
  let x := k % 5
  state.val[5*y + x]! ^^^
    ⟨(~~~ (state.val[5*y + (x + 1) % 5]!).bv) &&&
       (state.val[5*y + (x + 2) % 5]!).bv⟩

/-- Purity of `chi`'s closure. -/
@[spec]
theorem chi_closure_call_mut_spec
    (state : Std.Array Std.U64 25#usize) (k : Std.Usize) (hk : k.val < 25) :
    ⦃ ⌜ True ⌝ ⦄
    keccak_f.chi.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      state k
    ⦃ ⇓ r => ⌜ r = (chi_closure_at state k.val, state) ⌝ ⦄ := by
  unfold keccak_f.chi.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        chi_closure_at
  hax_mvcgen
  all_goals (first
    | scalar_tac
    | (simp; scalar_tac)
    | (congr 1; apply Std.U64.bv_eq_imp_eq
       simp_all only [Std.UScalar.bv_xor, Std.UScalar.bv_not,
         show ((1#usize : Std.Usize).val) = 1 from rfl,
         show ((2#usize : Std.Usize).val) = 2 from rfl,
         show ((5#usize : Std.Usize).val) = 5 from rfl]))

/-! ### Function-value theorems: `keccak_f.X = X_applied`

Each hacspec function `keccak_f.X` is shown to produce its pure `_applied`
form. `createi_pure_spec` lets a single `hax_mvcgen` chain through createi →
per-closure `[spec]`, reaching a 25-cell array equality that the
`close_array25` macro below collapses.

### Shared closer for the 25-cell array equality

After `hax_mvcgen` recurses through the per-closure `[spec]`s, every
rho/pi/chi proof reaches the same goal shape:

  `(createi-result).val = (X_applied state).val`

where the LHS is a 25-element `r_a` whose cells satisfy
`r_a.val[i]! = X_closure_at state i` (the `ha` hypothesis introduced by
`createi_pure_spec`), and the RHS is `Std.Array.make 25 [..25 cells..]`.

The `close_array25` macro automates this collapse:
1. `apply Subtype.ext; unfold $applied; simp only [Std.Array.make]`
2. `rename_i r_a ha`
3. Specializes `ha` at each of the 25 indices.
4. Rewrites each `ha_i` via `simp only [$closure, ..extra..]` where
   `..extra..` is the per-X simp-set (div/mod literals, RHO_OFFSETS, etc.).
5. Destructs `r_a` to a 25-element list and rewrites each cell using
   the 25 `ha_i` equalities.

Theta isn't routed through this macro: it has three nested closures and
chains `hc → hd → ha` rather than a single `ha`. -/

/-- Inner helper: collapses a 25-cell array given that `r_a` and `ha`
    have already been introduced (e.g. after `rename_i` inside theta).
    Uses `set_option hygiene false in` so the introduced `ha0..ha24` /
    `v0..v24` names are visible to the caller's `$tail`. -/
syntax "close_array25_inner " ident
    " with " "[" Lean.Parser.Tactic.simpLemma,*,? "]"
    " then " tacticSeq : tactic

set_option hygiene false in
macro_rules
  | `(tactic| close_array25_inner $closure:ident
              with [ $extra,* ] then $tail:tacticSeq) =>
    `(tactic|
    (have ha0  := ha  0 (by decide); have ha1  := ha  1 (by decide)
     have ha2  := ha  2 (by decide); have ha3  := ha  3 (by decide)
     have ha4  := ha  4 (by decide); have ha5  := ha  5 (by decide)
     have ha6  := ha  6 (by decide); have ha7  := ha  7 (by decide)
     have ha8  := ha  8 (by decide); have ha9  := ha  9 (by decide)
     have ha10 := ha 10 (by decide); have ha11 := ha 11 (by decide)
     have ha12 := ha 12 (by decide); have ha13 := ha 13 (by decide)
     have ha14 := ha 14 (by decide); have ha15 := ha 15 (by decide)
     have ha16 := ha 16 (by decide); have ha17 := ha 17 (by decide)
     have ha18 := ha 18 (by decide); have ha19 := ha 19 (by decide)
     have ha20 := ha 20 (by decide); have ha21 := ha 21 (by decide)
     have ha22 := ha 22 (by decide); have ha23 := ha 23 (by decide)
     have ha24 := ha 24 (by decide)
     simp only [$closure:ident, $extra,*]
       at ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9
          ha10 ha11 ha12 ha13 ha14 ha15 ha16 ha17 ha18 ha19
          ha20 ha21 ha22 ha23 ha24
     obtain ⟨lst, hlen⟩ := r_a
     simp only [show ((25#usize : Std.Usize).val) = 25 from rfl] at hlen
     match lst, hlen with
     | [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,
        v15,v16,v17,v18,v19,v20,v21,v22,v23,v24], _ =>
       simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
         at ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9 ha10 ha11 ha12 ha13
            ha14 ha15 ha16 ha17 ha18 ha19 ha20 ha21 ha22 ha23 ha24
       (simp only [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9,
         ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19,
         ha20, ha21, ha22, ha23, ha24])
       ($tail)))

syntax "close_array25 " ident "," ident
    " with " "[" Lean.Parser.Tactic.simpLemma,*,? "]"
    " then " tacticSeq : tactic

set_option hygiene false in
macro_rules
  | `(tactic| close_array25 $applied:ident, $closure:ident
              with [ $extra,* ] then $tail:tacticSeq) =>
    `(tactic|
    (apply Subtype.ext
     unfold $applied
     simp only [Std.Array.make]
     rename_i r_a ha
     close_array25_inner $closure with [$extra,*] then $tail))



attribute [local irreducible] spread_to_even lift_lane_bv

/-! ## Theta composition (impl side)

Expresses each component of `r.d` after `keccakf1600_round0_theta` in
terms of the original `s.st` BitVec halves, and asserts that `s.st` and
`s.i` are preserved (the impl's θ step only writes `c` / `d`).

  d[x].z0 = c[(x+4)%5].z0 ⊕ rot(c[(x+1)%5].z1, 1)
  d[x].z1 = c[(x+4)%5].z1 ⊕         c[(x+1)%5].z0
  c[x].z  = ⊕_{y=0..4} st[5*x + y].z
-/

/-! ### Per-sub-function state-preservation specs

The θ step only writes the auxiliary `c` / `d` columns; `st` and `i` are
preserved. Each sub-function's spec is proved once with `mvcgen` and
registered `@[spec]` so the composed `keccakf1600_round0_theta` spec
chains them automatically. -/

@[spec]
private theorem set_lane_value_spec
    (s : state.KeccakState) (i j : Std.Usize) (v : Std.U32) {Q}
    (hi : i.val < 5) (hj : j.val < 2)
    (hpost : ∀ r : state.KeccakState,
        r.st = s.st → r.i = s.i → r.d = s.d →
        r.c = s.c.set i ((s.c.val[i.val]!).set j v) →
        (Q.1 r).down) :
    ⦃ ⌜ True ⌝ ⦄
    state.KeccakState.set_lane_value s i j v
    ⦃ Q ⦄ := by
  have h_idx : i.val < s.c.val.length := by simp; scalar_tac
  have h_eq : s.c.val[i.val]! = s.c.val[i.val]'h_idx := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h_idx]; rfl
  unfold state.KeccakState.set_lane_value
  mvcgen
  all_goals first | simpa | scalar_tac | (
    apply hpost <;> first
      | rfl
      | scalar_tac
      | (rw [h_eq]; simp_all [WP.uncurry']))

/-- `Lane2U32` array-index returns the indexed element when in bounds. Used by
    `theta_d` to read `s.c`. -/
@[spec]
private theorem lane_index_spec
    (l : lane.Lane2U32) (i : Std.Usize) {Q}
    (hi : i.val < 2)
    (hpost : ∀ v : Std.U32, v = l.val[i.val]! → (Q.1 v).down) :
    ⦃ ⌜ True ⌝ ⦄
    lane.Lane2U32.Insts.CoreOpsIndexIndexUsizeU32.index l i
    ⦃ Q ⦄ := by
  unfold lane.Lane2U32.Insts.CoreOpsIndexIndexUsizeU32.index
  mvcgen
  all_goals first | scalar_tac | (try intros; apply hpost; simp_all)

@[spec]
private theorem get_with_zeta_spec
    (s : state.KeccakState) (i j zeta : Std.Usize) {Q}
    (hi : i.val < 5) (hj : j.val < 5) (hzeta : zeta.val < 2)
    (hpost : ∀ v : Std.U32, v = (s.st.val[5 * j.val + i.val]!).val[zeta.val]! →
        (Q.1 v).down) :
    ⦃ ⌜ True ⌝ ⦄ state.KeccakState.get_with_zeta s i j zeta ⦃ Q ⦄ := by
  have h_idx : 5 * j.val + i.val < s.st.val.length := by simp; scalar_tac
  have h_eq : s.st.val[5 * j.val + i.val]! = s.st.val[5 * j.val + i.val]'h_idx := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h_idx]; rfl
  unfold state.KeccakState.get_with_zeta
  mvcgen
  all_goals first | scalar_tac | (
    try intros
    apply hpost
    rw [h_eq]
    simp_all)

/-- `CoreModels.core.num.U32.rotate_left` returns the bit-rotated value. (Local
    re-statement of the spec in `CoreModels/Specs.lean` for downstream
    consumers that haven't yet picked up the updated rust-core-models pin.) -/
@[spec]
private theorem rotate_left_u32_spec
    (x : Std.U32) (n : Std.U32) {Q}
    (hpost : ∀ v : Std.U32, v.bv = x.bv.rotateLeft n.val → (Q.1 v).down) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.num.U32.rotate_left x n
    ⦃ Q ⦄ := by
  unfold CoreModels.core.num.U32.rotate_left
    CoreModels.rust_primitives.arithmetic.rotate_left_u32
  mvcgen [Std.UScalar.rotate_left]
  apply hpost _ rfl

/-- `CoreModels.core.num.U64.rotate_left` returns the bit-rotated value. Same
    shape as `rotate_left_u32_spec`; used on the spec side of
    `theta_lift_spec` for the 5 ρ-style rotations in `keccak_f.theta`. -/
@[spec]
private theorem rotate_left_u64_spec
    (x : Std.U64) (n : Std.U32) {Q}
    (hpost : ∀ v : Std.U64, v.bv = x.bv.rotateLeft n.val → (Q.1 v).down) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.num.U64.rotate_left x n
    ⦃ Q ⦄ := by
  unfold CoreModels.core.num.U64.rotate_left
    CoreModels.rust_primitives.arithmetic.rotate_left_u64
  mvcgen [Std.UScalar.rotate_left]
  apply hpost _ rfl

/-- Tactic used for every per-sub-function state-preservation spec:
    unfold once, then chain the registered primitive specs. -/
local macro "theta_sub_preserves_st_i_proof" subfun:ident : tactic =>
  `(tactic|
    (unfold $subfun
     hax_mvcgen <;>
       scalar_tac))

/-- Tactic for the strengthened `theta_c_xX_zZ` specs: after `hax_mvcgen`
    handles the do-block, the remaining VC says the freshly-written
    `c[X][Z]` value equals the chained XOR of five `s.st` reads. The
    XOR equality is per `UScalar.eq_equiv_bv_eq` + the BitVec halves
    of `h✝` already accumulated by `mvcgen`. Shared across rounds 0-3. -/
macro "theta_c_proof" subfun:ident : tactic =>
  `(tactic|
    (unfold $subfun
     hax_mvcgen
     all_goals first
       | scalar_tac
       | (intros
          refine ⟨?_, ?_, ?_, ?_⟩
          all_goals first | assumption | (
            apply Eq.trans ‹_›
            congr 2
            apply Std.U32.bv_eq_imp_eq
            simp_all [Std.UScalar.bv_xor]))))

/-! Theta_c sub-function specs. Each ends in `set_lane_value` (only
    touches `c`), so the registered `set_lane_value_preserves_st_i`
    `@[spec]` lemma carries `st`/`i` through. -/

@[spec]
private theorem theta_c_x0_z0_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 0#usize ((s.c.val[0]!).set 0#usize
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[0]! ^^^
           s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
           s.st.val[4]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x0_z0

@[spec]
private theorem theta_c_x0_z1_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 0#usize ((s.c.val[0]!).set 1#usize
          (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[1]! ^^^
           s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
           s.st.val[4]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x0_z1

@[spec]
private theorem theta_c_x1_z0_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 1#usize ((s.c.val[1]!).set 0#usize
          (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[0]! ^^^
           s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[0]! ^^^
           s.st.val[9]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x1_z0

@[spec]
private theorem theta_c_x1_z1_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 1#usize ((s.c.val[1]!).set 1#usize
          (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[1]! ^^^
           s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[1]! ^^^
           s.st.val[9]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x1_z1

@[spec]
private theorem theta_c_x2_z0_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 2#usize ((s.c.val[2]!).set 0#usize
          (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
           s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[0]! ^^^
           s.st.val[14]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x2_z0

@[spec]
private theorem theta_c_x2_z1_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 2#usize ((s.c.val[2]!).set 1#usize
          (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
           s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[1]! ^^^
           s.st.val[14]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x2_z1

@[spec]
private theorem theta_c_x3_z0_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 3#usize ((s.c.val[3]!).set 0#usize
          (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[0]! ^^^
           s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[0]! ^^^
           s.st.val[19]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x3_z0

@[spec]
private theorem theta_c_x3_z1_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 3#usize ((s.c.val[3]!).set 1#usize
          (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[1]! ^^^
           s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[1]! ^^^
           s.st.val[19]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x3_z1

@[spec]
private theorem theta_c_x4_z0_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 4#usize ((s.c.val[4]!).set 0#usize
          (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[0]! ^^^
           s.st.val[24]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x4_z0

@[spec]
private theorem theta_c_x4_z1_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 4#usize ((s.c.val[4]!).set 1#usize
          (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[1]! ^^^
           s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[1]! ^^^
           s.st.val[24]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round0_theta_c_x4_z1

/-! `theta_d` overwrites only `s.d`. Each `r.d[x][z]` is determined by two
    cells of `s.c`, possibly with a 32-bit rotation. -/
set_option maxHeartbeats 1600000 in
@[spec]
private theorem theta_d_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round0_theta_d s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.c = s.c ∧
        r.d.val[0]!.val[0]! =
          s.c.val[4]!.val[0]! ^^^ rot32 s.c.val[1]!.val[1]! 1 ∧
        r.d.val[0]!.val[1]! =
          s.c.val[4]!.val[1]! ^^^ s.c.val[1]!.val[0]! ∧
        r.d.val[1]!.val[0]! =
          s.c.val[0]!.val[0]! ^^^ rot32 s.c.val[2]!.val[1]! 1 ∧
        r.d.val[1]!.val[1]! =
          s.c.val[0]!.val[1]! ^^^ s.c.val[2]!.val[0]! ∧
        r.d.val[2]!.val[0]! =
          s.c.val[1]!.val[0]! ^^^ rot32 s.c.val[3]!.val[1]! 1 ∧
        r.d.val[2]!.val[1]! =
          s.c.val[1]!.val[1]! ^^^ s.c.val[3]!.val[0]! ∧
        r.d.val[3]!.val[0]! =
          s.c.val[2]!.val[0]! ^^^ rot32 s.c.val[4]!.val[1]! 1 ∧
        r.d.val[3]!.val[1]! =
          s.c.val[2]!.val[1]! ^^^ s.c.val[4]!.val[0]! ∧
        r.d.val[4]!.val[0]! =
          s.c.val[3]!.val[0]! ^^^ rot32 s.c.val[0]!.val[1]! 1 ∧
        r.d.val[4]!.val[1]! =
          s.c.val[3]!.val[1]! ^^^ s.c.val[0]!.val[0]! ⌝ ⦄ := by
  unfold keccak.keccakf1600_round0_theta_d
  mvcgen
  all_goals first
    | scalar_tac
    | (refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
       (apply Std.U32.bv_eq_imp_eq
        simp_all [WP.uncurry', Std.Array.set_val_eq,
                  Std.UScalar.bv_xor, rot32]))

/-! ### Composed θ-round spec

With the 11 sub-function specs registered `@[spec]`, `hax_mvcgen`
threads the post forward. Each `r.d[x][z]` is expressed in terms of
the original `s.st` halves via the c-cell chain:

  c[x].z = ⊕_{y=0..4} st[5*x + y].z
  d[x].z0 = c[(x+4)%5].z0 ⊕ rot(c[(x+1)%5].z1, 1)
  d[x].z1 = c[(x+4)%5].z1 ⊕ c[(x+1)%5].z0
-/

set_option maxHeartbeats 4000000 in
theorem theta_comp_spec_local (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧
        -- d[0].z0 = c[4].z0 ⊕ rot(c[1].z1, 1)
        r.d.val[0]!.val[0]! =
          (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[0]! ^^^
           s.st.val[24]!.val[0]!) ^^^
          rot32 (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[1]! ^^^
                 s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[1]! ^^^
                 s.st.val[9]!.val[1]!) 1 ∧
        -- d[0].z1 = c[4].z1 ⊕ c[1].z0
        r.d.val[0]!.val[1]! =
          (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[1]! ^^^
           s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[1]! ^^^
           s.st.val[24]!.val[1]!) ^^^
          (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[0]! ^^^
           s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[0]! ^^^
           s.st.val[9]!.val[0]!) ∧
        -- d[1].z0 = c[0].z0 ⊕ rot(c[2].z1, 1)
        r.d.val[1]!.val[0]! =
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[0]! ^^^
           s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
           s.st.val[4]!.val[0]!) ^^^
          rot32 (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
                 s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[1]! ^^^
                 s.st.val[14]!.val[1]!) 1 ∧
        -- d[1].z1 = c[0].z1 ⊕ c[2].z0
        r.d.val[1]!.val[1]! =
          (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[1]! ^^^
           s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
           s.st.val[4]!.val[1]!) ^^^
          (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
           s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[0]! ^^^
           s.st.val[14]!.val[0]!) ∧
        -- d[2].z0 = c[1].z0 ⊕ rot(c[3].z1, 1)
        r.d.val[2]!.val[0]! =
          (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[0]! ^^^
           s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[0]! ^^^
           s.st.val[9]!.val[0]!) ^^^
          rot32 (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[1]! ^^^
                 s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[1]! ^^^
                 s.st.val[19]!.val[1]!) 1 ∧
        -- d[2].z1 = c[1].z1 ⊕ c[3].z0
        r.d.val[2]!.val[1]! =
          (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[1]! ^^^
           s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[1]! ^^^
           s.st.val[9]!.val[1]!) ^^^
          (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[0]! ^^^
           s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[0]! ^^^
           s.st.val[19]!.val[0]!) ∧
        -- d[3].z0 = c[2].z0 ⊕ rot(c[4].z1, 1)
        r.d.val[3]!.val[0]! =
          (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
           s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[0]! ^^^
           s.st.val[14]!.val[0]!) ^^^
          rot32 (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[1]! ^^^
                 s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[1]! ^^^
                 s.st.val[24]!.val[1]!) 1 ∧
        -- d[3].z1 = c[2].z1 ⊕ c[4].z0
        r.d.val[3]!.val[1]! =
          (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
           s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[1]! ^^^
           s.st.val[14]!.val[1]!) ^^^
          (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[0]! ^^^
           s.st.val[24]!.val[0]!) ∧
        -- d[4].z0 = c[3].z0 ⊕ rot(c[0].z1, 1)
        r.d.val[4]!.val[0]! =
          (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[0]! ^^^
           s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[0]! ^^^
           s.st.val[19]!.val[0]!) ^^^
          rot32 (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[1]! ^^^
                 s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
                 s.st.val[4]!.val[1]!) 1 ∧
        -- d[4].z1 = c[3].z1 ⊕ c[0].z0
        r.d.val[4]!.val[1]! =
          (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[1]! ^^^
           s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[1]! ^^^
           s.st.val[19]!.val[1]!) ^^^
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[0]! ^^^
           s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
           s.st.val[4]!.val[0]!) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round0_theta
  hax_mvcgen
  all_goals first
    | trivial
    | grind
    | simp_all

/-! ## θ-applied lifted state (spec-coupling side)

After impl θ, the impl's `r.st` is *unchanged* — the actual XOR-into-`st`
is deferred to π·ρ·χ. But the spec's `keccak_f.theta` *does* apply the
d-values to the state in one go. To bridge this asymmetry we define
`lift_theta_applied r_impl`, the lifted 25-lane state that the spec
would produce given the impl's post-θ d-cells. The spec-coupling
theorem then proves `keccak_f.theta (lift s) = ok (lift_theta_applied r_impl)`.
-/

/-- Helper for `lift_theta_applied`: lift a single lane given the four
    interleaved halves (state z0/z1 and column d z0/z1). XOR is applied
    on the U32 halves before lifting; equivalently, the U32 XORs land
    inside the BitVec arguments of `lift_lane_bv`. -/
private abbrev lta (st_z0 st_z1 d_z0 d_z1 : Std.U32) : Std.U64 :=
  ⟨lift_lane_bv ((st_z0 ^^^ d_z0).bv) ((st_z1 ^^^ d_z1).bv)⟩

/-- The 25-lane `u64` state that the spec's `keccak_f.theta` produces
    given the impl's post-θ scratch cells. Each spec lane `i = 5*y + x` is
    `lift_lane_bv (s.st[transpose_perm i].z0 ⊕ s.d[i%5].z0)
                  (s.st[transpose_perm i].z1 ⊕ s.d[i%5].z1)`,
    where `transpose_perm i = 5*x + y` is the impl-side index for the lane
    that lives at spec position `i`, and `i%5 = x` indexes the spec column.

    Written as a literal 25-element list (rather than `List.ofFn`) so
    that `unfold lift_theta_applied` exposes a concrete cons list — this
    aligns the RHS structurally with the LHS literal list produced by
    `hax_mvcgen` on `keccak_f.theta` and lets a 25-way `congr` peel the
    lanes pointwise. -/
def lift_theta_applied (s : state.KeccakState) : Std.Array Std.U64 25#usize :=
  let d := s.d; let st := s.st
  Std.Array.make 25#usize [
    -- i=0:  (x=0, y=0) → st[0],  d[0]
    lta (st.val[0]!).val[0]!  (st.val[0]!).val[1]!  (d.val[0]!).val[0]! (d.val[0]!).val[1]!,
    -- i=1:  (x=1, y=0) → st[5],  d[1]
    lta (st.val[5]!).val[0]!  (st.val[5]!).val[1]!  (d.val[1]!).val[0]! (d.val[1]!).val[1]!,
    -- i=2:  (x=2, y=0) → st[10], d[2]
    lta (st.val[10]!).val[0]! (st.val[10]!).val[1]! (d.val[2]!).val[0]! (d.val[2]!).val[1]!,
    -- i=3:  (x=3, y=0) → st[15], d[3]
    lta (st.val[15]!).val[0]! (st.val[15]!).val[1]! (d.val[3]!).val[0]! (d.val[3]!).val[1]!,
    -- i=4:  (x=4, y=0) → st[20], d[4]
    lta (st.val[20]!).val[0]! (st.val[20]!).val[1]! (d.val[4]!).val[0]! (d.val[4]!).val[1]!,
    -- i=5:  (x=0, y=1) → st[1],  d[0]
    lta (st.val[1]!).val[0]!  (st.val[1]!).val[1]!  (d.val[0]!).val[0]! (d.val[0]!).val[1]!,
    -- i=6:  (x=1, y=1) → st[6],  d[1]
    lta (st.val[6]!).val[0]!  (st.val[6]!).val[1]!  (d.val[1]!).val[0]! (d.val[1]!).val[1]!,
    -- i=7:  (x=2, y=1) → st[11], d[2]
    lta (st.val[11]!).val[0]! (st.val[11]!).val[1]! (d.val[2]!).val[0]! (d.val[2]!).val[1]!,
    -- i=8:  (x=3, y=1) → st[16], d[3]
    lta (st.val[16]!).val[0]! (st.val[16]!).val[1]! (d.val[3]!).val[0]! (d.val[3]!).val[1]!,
    -- i=9:  (x=4, y=1) → st[21], d[4]
    lta (st.val[21]!).val[0]! (st.val[21]!).val[1]! (d.val[4]!).val[0]! (d.val[4]!).val[1]!,
    -- i=10: (x=0, y=2) → st[2],  d[0]
    lta (st.val[2]!).val[0]!  (st.val[2]!).val[1]!  (d.val[0]!).val[0]! (d.val[0]!).val[1]!,
    -- i=11: (x=1, y=2) → st[7],  d[1]
    lta (st.val[7]!).val[0]!  (st.val[7]!).val[1]!  (d.val[1]!).val[0]! (d.val[1]!).val[1]!,
    -- i=12: (x=2, y=2) → st[12], d[2]
    lta (st.val[12]!).val[0]! (st.val[12]!).val[1]! (d.val[2]!).val[0]! (d.val[2]!).val[1]!,
    -- i=13: (x=3, y=2) → st[17], d[3]
    lta (st.val[17]!).val[0]! (st.val[17]!).val[1]! (d.val[3]!).val[0]! (d.val[3]!).val[1]!,
    -- i=14: (x=4, y=2) → st[22], d[4]
    lta (st.val[22]!).val[0]! (st.val[22]!).val[1]! (d.val[4]!).val[0]! (d.val[4]!).val[1]!,
    -- i=15: (x=0, y=3) → st[3],  d[0]
    lta (st.val[3]!).val[0]!  (st.val[3]!).val[1]!  (d.val[0]!).val[0]! (d.val[0]!).val[1]!,
    -- i=16: (x=1, y=3) → st[8],  d[1]
    lta (st.val[8]!).val[0]!  (st.val[8]!).val[1]!  (d.val[1]!).val[0]! (d.val[1]!).val[1]!,
    -- i=17: (x=2, y=3) → st[13], d[2]
    lta (st.val[13]!).val[0]! (st.val[13]!).val[1]! (d.val[2]!).val[0]! (d.val[2]!).val[1]!,
    -- i=18: (x=3, y=3) → st[18], d[3]
    lta (st.val[18]!).val[0]! (st.val[18]!).val[1]! (d.val[3]!).val[0]! (d.val[3]!).val[1]!,
    -- i=19: (x=4, y=3) → st[23], d[4]
    lta (st.val[23]!).val[0]! (st.val[23]!).val[1]! (d.val[4]!).val[0]! (d.val[4]!).val[1]!,
    -- i=20: (x=0, y=4) → st[4],  d[0]
    lta (st.val[4]!).val[0]!  (st.val[4]!).val[1]!  (d.val[0]!).val[0]! (d.val[0]!).val[1]!,
    -- i=21: (x=1, y=4) → st[9],  d[1]
    lta (st.val[9]!).val[0]!  (st.val[9]!).val[1]!  (d.val[1]!).val[0]! (d.val[1]!).val[1]!,
    -- i=22: (x=2, y=4) → st[14], d[2]
    lta (st.val[14]!).val[0]! (st.val[14]!).val[1]! (d.val[2]!).val[0]! (d.val[2]!).val[1]!,
    -- i=23: (x=3, y=4) → st[19], d[3]
    lta (st.val[19]!).val[0]! (st.val[19]!).val[1]! (d.val[3]!).val[0]! (d.val[3]!).val[1]!,
    -- i=24: (x=4, y=4) → st[24], d[4]
    lta (st.val[24]!).val[0]! (st.val[24]!).val[1]! (d.val[4]!).val[0]! (d.val[4]!).val[1]!]

/-! ## Perm/swap-aware lift_theta_applied (rounds 1–3)

`lift_theta_applied` (above) is correct only when the input convention is
the canonical `lift s` (round 0). For round k ≥ 1, the spec input is
`lift_perm s (impl_perm^[k]) (impl_swap_k k)`, and the spec output of theta
matches a **permuted/swap-aware** view of `(post-theta r_impl).st ⊕ r_impl.d`:

  spec lane i = lift_lane_maybe_swap (r_impl.st[p i]) (sw (p i))
              ⊕ lift_lane (r_impl.d[i/5])

where `p = impl_perm^[k]` and `sw = impl_swap_k k`. The d-side stays canonical
because theta computes interleaved column XORs in canonical halves regardless
of the input layout (cf. round-1's `theta_c_*` reads swap-aware halves so that
their XOR equals the canonical bit-interleaved column-XOR of the spec view).

This generalization specialises to the existing `lift_theta_applied` at
`(id, swZero)` — see `lift_theta_applied_perm_id` below.

  For example, at the post-round-1-theta state with permutation
  `impl_perm` and swap `impl_swap_k 1`:
  `keccak_f.theta (lift_perm s impl_perm (impl_swap_k 1))
   = .ok (lift_theta_applied_perm r_impl impl_perm (impl_swap_k 1))`. -/
def lift_theta_applied_perm
    (s : state.KeccakState) (p : Fin 25 → Fin 25) (sw : Fin 25 → Bool) :
    Std.Array Std.U64 25#usize :=
  ⟨List.ofFn (fun i : Fin 25 =>
    (lift_lane_maybe_swap (s.st.val[(p (transpose_perm i)).val]!)
                          (sw (p (transpose_perm i)))) ^^^
      (lift_lane (s.d.val[i.val % 5]!))),
   by simp⟩

/-- `lift_theta_applied_perm` at `(id, swZero)` equals `lift_theta_applied`.
    Bridges the round-0 proofs to the perm-aware machinery. -/
theorem lift_theta_applied_perm_id (s : state.KeccakState) :
    lift_theta_applied_perm s id (fun _ => false) = lift_theta_applied s := by
  apply Subtype.ext
  unfold lift_theta_applied_perm lift_theta_applied
  show List.ofFn _ = _
  simp only [Std.Array.make, id_eq, lift_lane_maybe_swap]
  -- 25 cells, each `lift_lane (s.st[transpose_perm i]) ^^^ lift_lane (s.d[i%5]) = lta`.
  repeat' (first | rfl | (apply List.cons_eq_cons.mpr; refine ⟨?_, ?_⟩))
  all_goals (apply Std.U64.bv_eq_imp_eq)
  all_goals (
    show (lift_lane _ ^^^ lift_lane _).bv = _
    simp [lift_lane, transpose_perm, Std.UScalar.bv_xor, lift_xor])

/-- Bridge from the lift definition: indexing `lift s` at a `Fin 25` returns
    the lifted interleaved halves of `s.st[transpose_perm k]`. Used to
    rewrite the spec-side chain hypotheses `r✝ = (lift s)[k]!` into
    BitVec form. -/
private theorem lift_getElem (s : state.KeccakState) (k : Fin 25) :
    (lift s).val[k.val]! =
      (⟨lift_lane_bv ((s.st.val[(transpose_perm k).val]!).val[0]!.bv)
                     ((s.st.val[(transpose_perm k).val]!).val[1]!.bv)⟩ : Std.U64) := by
  unfold lift lift_lane
  change (List.ofFn _)[k.val]! = _
  rw [getElem!_pos _ k.val (by simp), List.getElem_ofFn]

private theorem lift_getElem_bv (s : state.KeccakState) (k : Fin 25) :
    ((↑(lift s) : List Std.U64)[(k.val : Nat)]!).bv =
      lift_lane_bv ((s.st.val[(transpose_perm k).val]!).val[0]!.bv)
                   ((s.st.val[(transpose_perm k).val]!).val[1]!.bv) := by
  rw [lift_getElem]

/-- 25 concrete-index specialisations of `lift_getElem_bv`. Each lemma
    `lift_getElem_bv_N` reads `(↑(lift s))[N]!.bv` and exposes the
    `lift_lane_bv` of `s.st[transpose_perm N]` (impl-side index after the
    spec↔impl transpose). -/
theorem lift_getElem_bv_0 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(0 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[0]!).val[0]!.bv) ((s.st.val[0]!).val[1]!.bv) := by
  show ((lift s).val[0]!).bv = _
  exact lift_getElem_bv s ⟨0, by decide⟩
theorem lift_getElem_bv_1 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(1 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[5]!).val[0]!.bv) ((s.st.val[5]!).val[1]!.bv) := by
  show ((lift s).val[1]!).bv = _
  exact lift_getElem_bv s ⟨1, by decide⟩
theorem lift_getElem_bv_2 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(2 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[10]!).val[0]!.bv) ((s.st.val[10]!).val[1]!.bv) := by
  show ((lift s).val[2]!).bv = _
  exact lift_getElem_bv s ⟨2, by decide⟩
theorem lift_getElem_bv_3 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(3 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[15]!).val[0]!.bv) ((s.st.val[15]!).val[1]!.bv) := by
  show ((lift s).val[3]!).bv = _
  exact lift_getElem_bv s ⟨3, by decide⟩
theorem lift_getElem_bv_4 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(4 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[20]!).val[0]!.bv) ((s.st.val[20]!).val[1]!.bv) := by
  show ((lift s).val[4]!).bv = _
  exact lift_getElem_bv s ⟨4, by decide⟩
theorem lift_getElem_bv_5 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(5 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[1]!).val[0]!.bv) ((s.st.val[1]!).val[1]!.bv) := by
  show ((lift s).val[5]!).bv = _
  exact lift_getElem_bv s ⟨5, by decide⟩
theorem lift_getElem_bv_6 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(6 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[6]!).val[0]!.bv) ((s.st.val[6]!).val[1]!.bv) := by
  show ((lift s).val[6]!).bv = _
  exact lift_getElem_bv s ⟨6, by decide⟩
theorem lift_getElem_bv_7 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(7 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[11]!).val[0]!.bv) ((s.st.val[11]!).val[1]!.bv) := by
  show ((lift s).val[7]!).bv = _
  exact lift_getElem_bv s ⟨7, by decide⟩
theorem lift_getElem_bv_8 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(8 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[16]!).val[0]!.bv) ((s.st.val[16]!).val[1]!.bv) := by
  show ((lift s).val[8]!).bv = _
  exact lift_getElem_bv s ⟨8, by decide⟩
theorem lift_getElem_bv_9 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(9 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[21]!).val[0]!.bv) ((s.st.val[21]!).val[1]!.bv) := by
  show ((lift s).val[9]!).bv = _
  exact lift_getElem_bv s ⟨9, by decide⟩
theorem lift_getElem_bv_10 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(10 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[2]!).val[0]!.bv) ((s.st.val[2]!).val[1]!.bv) := by
  show ((lift s).val[10]!).bv = _
  exact lift_getElem_bv s ⟨10, by decide⟩
theorem lift_getElem_bv_11 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(11 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[7]!).val[0]!.bv) ((s.st.val[7]!).val[1]!.bv) := by
  show ((lift s).val[11]!).bv = _
  exact lift_getElem_bv s ⟨11, by decide⟩
theorem lift_getElem_bv_12 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(12 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[12]!).val[0]!.bv) ((s.st.val[12]!).val[1]!.bv) := by
  show ((lift s).val[12]!).bv = _
  exact lift_getElem_bv s ⟨12, by decide⟩
theorem lift_getElem_bv_13 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(13 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[17]!).val[0]!.bv) ((s.st.val[17]!).val[1]!.bv) := by
  show ((lift s).val[13]!).bv = _
  exact lift_getElem_bv s ⟨13, by decide⟩
theorem lift_getElem_bv_14 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(14 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[22]!).val[0]!.bv) ((s.st.val[22]!).val[1]!.bv) := by
  show ((lift s).val[14]!).bv = _
  exact lift_getElem_bv s ⟨14, by decide⟩
theorem lift_getElem_bv_15 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(15 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[3]!).val[0]!.bv) ((s.st.val[3]!).val[1]!.bv) := by
  show ((lift s).val[15]!).bv = _
  exact lift_getElem_bv s ⟨15, by decide⟩
theorem lift_getElem_bv_16 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(16 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[8]!).val[0]!.bv) ((s.st.val[8]!).val[1]!.bv) := by
  show ((lift s).val[16]!).bv = _
  exact lift_getElem_bv s ⟨16, by decide⟩
theorem lift_getElem_bv_17 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(17 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[13]!).val[0]!.bv) ((s.st.val[13]!).val[1]!.bv) := by
  show ((lift s).val[17]!).bv = _
  exact lift_getElem_bv s ⟨17, by decide⟩
theorem lift_getElem_bv_18 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(18 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[18]!).val[0]!.bv) ((s.st.val[18]!).val[1]!.bv) := by
  show ((lift s).val[18]!).bv = _
  exact lift_getElem_bv s ⟨18, by decide⟩
theorem lift_getElem_bv_19 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(19 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[23]!).val[0]!.bv) ((s.st.val[23]!).val[1]!.bv) := by
  show ((lift s).val[19]!).bv = _
  exact lift_getElem_bv s ⟨19, by decide⟩
theorem lift_getElem_bv_20 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(20 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[4]!).val[0]!.bv) ((s.st.val[4]!).val[1]!.bv) := by
  show ((lift s).val[20]!).bv = _
  exact lift_getElem_bv s ⟨20, by decide⟩
theorem lift_getElem_bv_21 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(21 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[9]!).val[0]!.bv) ((s.st.val[9]!).val[1]!.bv) := by
  show ((lift s).val[21]!).bv = _
  exact lift_getElem_bv s ⟨21, by decide⟩
theorem lift_getElem_bv_22 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(22 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[14]!).val[0]!.bv) ((s.st.val[14]!).val[1]!.bv) := by
  show ((lift s).val[22]!).bv = _
  exact lift_getElem_bv s ⟨22, by decide⟩
theorem lift_getElem_bv_23 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(23 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[19]!).val[0]!.bv) ((s.st.val[19]!).val[1]!.bv) := by
  show ((lift s).val[23]!).bv = _
  exact lift_getElem_bv s ⟨23, by decide⟩
theorem lift_getElem_bv_24 (s : state.KeccakState) :
    ((↑(lift s) : List Std.U64)[(24 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[24]!).val[0]!.bv) ((s.st.val[24]!).val[1]!.bv) := by
  show ((lift s).val[24]!).bv = _
  exact lift_getElem_bv s ⟨24, by decide⟩

/-! ## Spec-coupling theorem

After running the impl θ on `s`, the spec's `keccak_f.theta (lift s)`
produces exactly `lift_theta_applied r_impl`. The chain of equalities:

  spec lane i  = (lift s)[i] ⊕ spec_d[i/5]
              = lift_lane (s.st[i]) ⊕ spec_d[i/5]    -- by lift def
              = lift_lane (s.st[i]) ⊕ lift_lane_bv impl_d[i/5]  -- by lift_td/xor5
              = lift_lane_bv (st.z0 ⊕ d.z0) (st.z1 ⊕ d.z1)  -- by lift_xor
              = lift_theta_applied r_impl . val[i]   -- by def

The substitution from `theta_comp_spec_local`'s 12-conjunct post is
how we bridge "spec d-cell content" with "impl r.d cell content".
-/


/-! ## Spec-side `@[spec]` for `keccak_f.theta`

Kept here (not in `PrcLift.lean`) so the @[spec] registration only
applies to files that import `RoundEquiv`. Adding it to `PrcLift.lean`
caused `prc_lift_spec`'s mvcgen pass to drift past the 128M heartbeat
cap (HEAD baseline was just under). -/

/-- Pure semantics of `keccak_f.theta` (new `5*y + x` layout):
    column XOR `c_x = ⊕_y state[5*y + x]`, then
    `d_x = c_{x-1} ^ rot64(c_{x+1}, 1)`, then `state[k] ^ d_{k%5}`. -/
def theta_applied (state : Std.Array Std.U64 25#usize) :
    Std.Array Std.U64 25#usize :=
  let c0 := state.val[0]!  ^^^ state.val[5]!  ^^^ state.val[10]! ^^^ state.val[15]! ^^^ state.val[20]!
  let c1 := state.val[1]!  ^^^ state.val[6]!  ^^^ state.val[11]! ^^^ state.val[16]! ^^^ state.val[21]!
  let c2 := state.val[2]!  ^^^ state.val[7]!  ^^^ state.val[12]! ^^^ state.val[17]! ^^^ state.val[22]!
  let c3 := state.val[3]!  ^^^ state.val[8]!  ^^^ state.val[13]! ^^^ state.val[18]! ^^^ state.val[23]!
  let c4 := state.val[4]!  ^^^ state.val[9]!  ^^^ state.val[14]! ^^^ state.val[19]! ^^^ state.val[24]!
  let d0 : Std.U64 := c4 ^^^ ⟨c1.bv.rotateLeft 1⟩
  let d1 : Std.U64 := c0 ^^^ ⟨c2.bv.rotateLeft 1⟩
  let d2 : Std.U64 := c1 ^^^ ⟨c3.bv.rotateLeft 1⟩
  let d3 : Std.U64 := c2 ^^^ ⟨c4.bv.rotateLeft 1⟩
  let d4 : Std.U64 := c3 ^^^ ⟨c0.bv.rotateLeft 1⟩
  Std.Array.make 25#usize [
    state.val[0]!  ^^^ d0, state.val[1]!  ^^^ d1, state.val[2]!  ^^^ d2,
    state.val[3]!  ^^^ d3, state.val[4]!  ^^^ d4,
    state.val[5]!  ^^^ d0, state.val[6]!  ^^^ d1, state.val[7]!  ^^^ d2,
    state.val[8]!  ^^^ d3, state.val[9]!  ^^^ d4,
    state.val[10]! ^^^ d0, state.val[11]! ^^^ d1, state.val[12]! ^^^ d2,
    state.val[13]! ^^^ d3, state.val[14]! ^^^ d4,
    state.val[15]! ^^^ d0, state.val[16]! ^^^ d1, state.val[17]! ^^^ d2,
    state.val[18]! ^^^ d3, state.val[19]! ^^^ d4,
    state.val[20]! ^^^ d0, state.val[21]! ^^^ d1, state.val[22]! ^^^ d2,
    state.val[23]! ^^^ d3, state.val[24]! ^^^ d4
  ]

set_option maxHeartbeats 16000000 in
@[spec]
theorem theta_spec (state : Std.Array Std.U64 25#usize) :
    ⦃ ⌜ True ⌝ ⦄ keccak_f.theta state
    ⦃ ⇓ r => ⌜ r = theta_applied state ⌝ ⦄ := by
  unfold keccak_f.theta
  hax_mvcgen
  case vc1.f => exact theta_closure_c_at state ‹ℕ›
  case vc4.f => exact theta_closure_1_d_at ‹Std.Array Std.U64 5#usize› ‹ℕ›
  case vc8 => exact theta_closure_2_at (state, ‹Std.Array Std.U64 5#usize›) ‹ℕ›
  all_goals first
    | (rw [usize_bv_ofNat_val _ (by scalar_tac)] at *
       first | scalar_tac | assumption)
    | scalar_tac
    | assumption
    | (-- vc7: 25-cell array equality
       apply Subtype.ext
       unfold theta_applied
       simp only [Std.Array.make]
       rename_i r_c hc r_d hd r_a ha
       have hc0 := hc 0 (by decide); have hc1 := hc 1 (by decide)
       have hc2 := hc 2 (by decide); have hc3 := hc 3 (by decide)
       have hc4 := hc 4 (by decide)
       simp only [theta_closure_c_at,
         show (5 * 1 + 1 : Nat) = 6 from rfl,
         show (5 * 1 + 2 : Nat) = 7 from rfl, show (5 * 1 + 3 : Nat) = 8 from rfl,
         show (5 * 1 + 4 : Nat) = 9 from rfl,
         show (5 * 2 + 1 : Nat) = 11 from rfl,
         show (5 * 2 + 2 : Nat) = 12 from rfl, show (5 * 2 + 3 : Nat) = 13 from rfl,
         show (5 * 2 + 4 : Nat) = 14 from rfl,
         show (5 * 3 + 1 : Nat) = 16 from rfl,
         show (5 * 3 + 2 : Nat) = 17 from rfl, show (5 * 3 + 3 : Nat) = 18 from rfl,
         show (5 * 3 + 4 : Nat) = 19 from rfl,
         show (5 * 4 + 1 : Nat) = 21 from rfl,
         show (5 * 4 + 2 : Nat) = 22 from rfl, show (5 * 4 + 3 : Nat) = 23 from rfl,
         show (5 * 4 + 4 : Nat) = 24 from rfl] at hc0 hc1 hc2 hc3 hc4
       have hd0 := hd 0 (by decide); have hd1 := hd 1 (by decide)
       have hd2 := hd 2 (by decide); have hd3 := hd 3 (by decide)
       have hd4 := hd 4 (by decide)
       simp only [theta_closure_1_d_at, hc0, hc1, hc2, hc3, hc4,
         show (0 + 4) % 5 = 4 from rfl, show (0 + 1) % 5 = 1 from rfl,
         show (1 + 4) % 5 = 0 from rfl, show (1 + 1) % 5 = 2 from rfl,
         show (2 + 1) % 5 = 3 from rfl] at hd0 hd1 hd2 hd3 hd4
       close_array25_inner theta_closure_2_at with [
         show (0:Nat) % 5 = 0 from rfl,
         show (1:Nat) % 5 = 1 from rfl,
         show (2:Nat) % 5 = 2 from rfl,
         show (3:Nat) % 5 = 3 from rfl,
         show (4:Nat) % 5 = 4 from rfl,
         show (5:Nat) % 5 = 0 from rfl,
         show (6:Nat) % 5 = 1 from rfl,
         show (7:Nat) % 5 = 2 from rfl,
         show (8:Nat) % 5 = 3 from rfl,
         show (9:Nat) % 5 = 4 from rfl,
         show (10:Nat) % 5 = 0 from rfl,
         show (11:Nat) % 5 = 1 from rfl,
         show (12:Nat) % 5 = 2 from rfl,
         show (13:Nat) % 5 = 3 from rfl,
         show (14:Nat) % 5 = 4 from rfl,
         show (15:Nat) % 5 = 0 from rfl,
         show (16:Nat) % 5 = 1 from rfl,
         show (17:Nat) % 5 = 2 from rfl,
         show (18:Nat) % 5 = 3 from rfl,
         show (19:Nat) % 5 = 4 from rfl,
         show (20:Nat) % 5 = 0 from rfl,
         show (21:Nat) % 5 = 1 from rfl,
         show (22:Nat) % 5 = 2 from rfl,
         show (23:Nat) % 5 = 3 from rfl,
         show (24:Nat) % 5 = 4 from rfl,
         hd0, hd1, hd2, hd3, hd4]
         then skip)


end libcrux_iot_sha3.Foundation
