import LibcruxIotSha3.Composition.Pedantic.Padding
/-!
# The sponge (FIPS 202, Algorithm 8)

`SPONGE[f, pad, r](N, d)` pads `N` to a multiple of the rate, absorbs it block by
block into a `b`-bit state, then squeezes `r` bits at a time until `d` are out.

The two loops are characterised against pure recursions over the permutation
`F`, which stays abstract here: the spec takes it from the `Components` trait,
and `keccak_c` instantiates it with `Keccak-p[1600, 24]`.  `absorbFrom` and
`squeezeFrom` are written in the order the loops run them, so the loop
invariants need no re-association -- that is worth the fuel argument
`squeezeFrom` carries (the squeeze loop is the one loop in this development
whose exit test lives in its body rather than in a range).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-- One absorb step: XOR the next block (zero-extended to the full width) into
    the state and permute (Algorithm 8, step 6). -/
def absorbStep (F : List Bool → List Bool) (r c : Nat) (p s : List Bool) (i : Nat) : List Bool :=
  F (List.zipWith (· ^^ ·) s ((p.drop (i * r)).take r ++ List.replicate c false))

/-- Absorbing blocks `i0, i0+1, …`, `k` of them. -/
def absorbFrom (F : List Bool → List Bool) (r c : Nat) (p : List Bool) :
    List Bool → Nat → Nat → List Bool
  | s, _, 0 => s
  | s, i0, k + 1 => absorbFrom F r c p (absorbStep F r c p s i0) (i0 + 1) k

/-- Squeezing (Algorithm 8, steps 8-10): emit `r` bits, stop once `d` are out.
    The loop is a `do`-while -- it always emits at least once -- so the fuel `k`
    counts *further* iterations, and `0` means "this is the last one". -/
def squeezeFrom (F : List Bool → List Bool) (r d : Nat) :
    Nat → List Bool → List Bool → List Bool
  | 0, s, z => z ++ s.take r
  | k + 1, s, z =>
    let z' := z ++ s.take r
    if d ≤ z'.length then z' else squeezeFrom F r d k (F s) z'

/-! ### The absorb loop -/

section Absorb

variable {C : Type} (inst : hacspec_sha3_pedantic.sponge.Components C) (comps : C)
  (F : List Bool → List Bool) (b : Nat)

/-- What the abstract permutation has to satisfy: it takes `b` bits to `b` bits,
    and it is the pure function `F`. -/
def PermSpec : Prop :=
  ∀ s : Slice Bool, s.val.length = b →
    ∃ o : alloc.vec.Vec Bool, inst.f comps s = ok o ∧ o.val = F s.val ∧ (F s.val).length = b

/-- `Nat::to_usize`, the one place a length goes back down to the fixed-width
    layer. It is partial there, and that is the only partiality this file
    inherits from the machine: every call site hands it the rate, which Table 1
    bounds by 1600. -/
theorem to_usize_eq (x : Nat) (hx : x ≤ Std.Usize.max) :
    ∃ u : Std.Usize, hacspec_sha3_pedantic.nat.Nat.to_usize x = ok u ∧ u.val = x := by
  have h := Std.UScalar.tryMk_eq .Usize x
  unfold hacspec_sha3_pedantic.nat.Nat.to_usize
  cases hc : Std.UScalar.tryMk .Usize x with
  | ok u => rw [hc] at h; exact ⟨u, rfl, h.1⟩
  | fail e => rw [hc] at h; exact absurd (show Std.UScalar.inBounds .Usize x by scalar_tac) h
  | div => rw [hc] at h; exact absurd h (by simp)

theorem absorb_body_cont (hF : PermSpec inst comps F b)
    (r : Nat) (c : Std.Usize) (hrc : r + c.val = b) (_hb : b ≤ 1600)
    (p : hacspec_sha3_pedantic.bits.BitStr) (_hr : 0 < r)
    (blocks : Nat) (hblocks : blocks * r = p.length)
    (i : Nat) (hi : i < blocks)
    (s : alloc.vec.Vec Bool) (hs : s.val.length = b) :
    ∃ s' : alloc.vec.Vec Bool,
      s'.val = absorbStep F r c.val p s.val i ∧
      hacspec_sha3_pedantic.sponge.Sponge.apply_loop0.body inst ⟨comps, r⟩ comps p blocks c s i
        = ok (.cont (s', i + 1)) := by
  -- `i * r` and `(i+1) * r` are both within the string. That is all there is to
  -- check about them: the cursor is a `Nat`, so neither can overflow.
  have hir : i * r + r ≤ p.length := by
    rw [← hblocks]
    calc i * r + r = (i + 1) * r := by ring
      _ ≤ blocks * r := Nat.mul_le_mul_right _ (by omega)
  -- the block: `r` bits of `p` from `i * r`, zero-extended to the full width
  have hslice : hacspec_sha3_pedantic.bits.BitStr.slice p (i * r) r
      = ok ((p.drop (i * r)).take r) := by
    unfold hacspec_sha3_pedantic.bits.BitStr.slice
    rw [if_pos hir]
  have hsl : ((p.drop (i * r)).take r).length = r := by
    simp only [List.length_take, List.length_drop]; omega
  have hto : hacspec_sha3_pedantic.bits.BitStr.to_bits ((p.drop (i * r)).take r)
      = ok ⟨(p.drop (i * r)).take r, by rw [hsl]; scalar_tac⟩ := by
    unfold hacspec_sha3_pedantic.bits.BitStr.to_bits
    exact dif_pos (by rw [hsl]; scalar_tac)
  obtain ⟨zs, hzs, hzsv⟩ := zeros_eq c
  obtain ⟨blk, hblk, hblkv⟩ := concat_eq
    ⟨(p.drop (i * r)).take r, by rw [hsl]; scalar_tac⟩ zs (by
      simp only [hsl, hzsv, List.length_replicate]; scalar_tac)
  have hblkv' : blk.val = (p.drop (i * r)).take r ++ zs.val := by simpa using hblkv
  have hblklen : blk.val.length = b := by
    rw [hblkv']
    simp only [List.length_append, hsl, hzsv, List.length_replicate]
    omega
  -- XOR into the state and permute
  obtain ⟨xs, hxs, hxsv⟩ := xor_eq s blk (by simp [hs, hblklen])
  obtain ⟨o, ho, hov, holen⟩ := hF xs (by simp only [hxsv]; simp [hs, hblklen])
  refine ⟨o, ?_, ?_⟩
  · have hxsv' : xs.val = List.zipWith (· ^^ ·) s.val blk.val := by simpa using hxsv
    rw [hov, hxsv', hblkv', hzsv]
    rfl
  · unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop0.body
      hacspec_sha3_pedantic.nat.Nat.Insts.CoreCmpPartialOrdNat.lt
      hacspec_sha3_pedantic.nat.Nat.Insts.CoreOpsArithMulNatNat.mul
      hacspec_sha3_pedantic.nat.Nat.Insts.CoreOpsArithAddNatNat.add
      hacspec_sha3_pedantic.nat.Nat.new
    simp [hi, hslice, hto, hzs, vec_deref_eq, hblk, hxs, ho]

theorem absorb_body_done (r : Nat) (c : Std.Usize)
    (p : hacspec_sha3_pedantic.bits.BitStr)
    (blocks : Nat) (s : alloc.vec.Vec Bool) :
    hacspec_sha3_pedantic.sponge.Sponge.apply_loop0.body inst ⟨comps, r⟩ comps p blocks c s blocks
      = ok (.done s) := by
  unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop0.body
    hacspec_sha3_pedantic.nat.Nat.Insts.CoreCmpPartialOrdNat.lt
  simp

/-- The absorb loop of Algorithm 8, steps 5-6. -/
theorem absorb_loop_eq (hF : PermSpec inst comps F b)
    (r : Nat) (c : Std.Usize) (hrc : r + c.val = b) (hb : b ≤ 1600) (hr : 0 < r)
    (p : hacspec_sha3_pedantic.bits.BitStr)
    (blocks : Nat) (hblocks : blocks * r = p.length)
    (s : alloc.vec.Vec Bool) (hs : s.val.length = b) :
    ∃ s' : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.sponge.Sponge.apply_loop0 inst ⟨comps, r⟩ comps p blocks c s 0
        = ok s' ∧
      s'.val = absorbFrom F r c.val p s.val 0 blocks ∧ s'.val.length = b := by
  have h := loop_counter_eq_inv_nat (β := alloc.vec.Vec Bool) (γ := alloc.vec.Vec Bool)
    (fun q => hacspec_sha3_pedantic.sponge.Sponge.apply_loop0.body inst ⟨comps, r⟩
      comps p blocks c q.1 q.2)
    blocks
    (fun _ acc => acc.val.length = b)
    (fun i acc r' => r'.val = absorbFrom F r c.val p acc.val i (blocks - i)
      ∧ r'.val.length = b)
    ?hstep ?hdone blocks 0 s (by simp) hs
  case hstep =>
    intro i acc hi hinv
    obtain ⟨s', hs', hbody⟩ :=
      absorb_body_cont inst comps F b hF r c hrc hb p hr blocks hblocks i hi acc hinv
    refine ⟨s', ?_, hbody, ?_⟩
    · rw [hs']
      obtain ⟨o, _, hov, holen⟩ := hF ⟨List.zipWith (· ^^ ·) acc.val
          ((p.drop (i * r)).take r ++ List.replicate c.val false), by
        have := acc.property
        simp only [List.length_zipWith]
        scalar_tac⟩ (by
        simp only [List.length_zipWith, List.length_append, List.length_replicate, hinv]
        have hlen : ((p.drop (i * r)).take r).length = r := by
          have hub : i * r + r ≤ p.length := by
            rw [← hblocks]
            calc i * r + r = (i + 1) * r := by ring
              _ ≤ blocks * r := Nat.mul_le_mul_right _ (by omega)
          simp only [List.length_take, List.length_drop]
          omega
        rw [hlen]
        omega)
      simpa only [absorbStep] using holen
    · rintro r' ⟨hr', hrlen⟩
      refine ⟨?_, hrlen⟩
      rw [hr', hs', show blocks - i = (blocks - (i + 1)) + 1 by omega]
      rfl
  case hdone =>
    intro acc hinv
    refine ⟨acc, absorb_body_done inst comps r c p blocks acc, ?_, hinv⟩
    rw [show blocks - blocks = 0 by omega]
    rfl
  obtain ⟨s', hloop, hval, hlen⟩ := h
  refine ⟨s', ?_, ?_, hlen⟩
  · unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop0
    exact hloop
  · rw [hval]
    simp

end Absorb


/-! ### The squeeze loop

The only loop here that is not over a range: its exit test (`d ≤ |Z|`) lives in
its body, so the induction is on the output still owed rather than on an index. -/

section Squeeze

variable {C : Type} (inst : hacspec_sha3_pedantic.sponge.Components C) (comps : C)
  (F : List Bool → List Bool) (b : Nat)

theorem squeeze_body_eq (hF : PermSpec inst comps F b) (rU : Std.Usize) (d : Nat)
    (hr : rU.val ≤ b) (_hb : b ≤ 1600) (s : alloc.vec.Vec Bool)
    (z : hacspec_sha3_pedantic.bits.BitStr) (hs : s.val.length = b) :
    ∃ z1 : hacspec_sha3_pedantic.bits.BitStr, z1 = z ++ s.val.take rU.val ∧
      ((d ≤ z1.length ∧
          hacspec_sha3_pedantic.sponge.Sponge.apply_loop1.body inst rU d comps s z
            = ok (.done z1)) ∨
       (¬ (d ≤ z1.length) ∧ ∃ s' : alloc.vec.Vec Bool, s'.val = F s.val ∧
          hacspec_sha3_pedantic.sponge.Sponge.apply_loop1.body inst rU d comps s z
            = ok (.cont (s', z1)))) := by
  -- the rate reached the fixed-width layer once, before the loop; here it is
  -- already a `usize`, so there is no cast to justify per turn
  obtain ⟨head, hhead, hheadv⟩ := trunc_eq s rU (by omega)
  have hheadlen : head.val.length = rU.val := by
    rw [hheadv]; simp; omega
  refine ⟨z ++ head.val, by rw [hheadv], ?_⟩
  by_cases hd : d ≤ (z ++ head.val).length
  · refine Or.inl ⟨hd, ?_⟩
    have hdn : d ≤ z.length + head.val.length := by simpa using hd
    unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop1.body
      hacspec_sha3_pedantic.bits.BitStr.from_bits
      hacspec_sha3_pedantic.bits.BitStr.concat
      hacspec_sha3_pedantic.bits.BitStr.len
      hacspec_sha3_pedantic.nat.Nat.Insts.CoreCmpPartialOrdNat.le
    simp [vec_deref_eq, hhead, hdn]
  · obtain ⟨s', hs', hs'v, -⟩ := hF s (by omega)
    refine Or.inr ⟨hd, s', hs'v, ?_⟩
    have hdn : ¬ (d ≤ z.length + head.val.length) := by simpa using hd
    unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop1.body
      hacspec_sha3_pedantic.bits.BitStr.from_bits
      hacspec_sha3_pedantic.bits.BitStr.concat
      hacspec_sha3_pedantic.bits.BitStr.len
      hacspec_sha3_pedantic.nat.Nat.Insts.CoreCmpPartialOrdNat.le
    simp [vec_deref_eq, hhead, hdn, hs']


/-- The squeeze loop: it emits `r` bits per turn until `d` are out.

    The fuel is what says the loop terminates; there is no second hypothesis
    about `Z` fitting a word, because `len(Z)` is a `Nat`. -/
theorem squeeze_loop_eq (hF : PermSpec inst comps F b) (rU : Std.Usize) (d : Nat)
    (hr : rU.val ≤ b) (hb : b ≤ 1600) :
    ∀ (k : Nat) (s : alloc.vec.Vec Bool) (z : hacspec_sha3_pedantic.bits.BitStr),
      s.val.length = b →
      d ≤ z.length + (k + 1) * rU.val →
      ∃ out : hacspec_sha3_pedantic.bits.BitStr,
        hacspec_sha3_pedantic.sponge.Sponge.apply_loop1 inst rU d comps s z = ok out ∧
        out = squeezeFrom F rU.val d k s.val z := by
  intro k
  induction k with
  | zero =>
    intro s z hs hfuel
    obtain ⟨z1, hz1v, hcase⟩ :=
      squeeze_body_eq inst comps F b hF rU d hr hb s z hs
    have hd : d ≤ z1.length := by
      rw [hz1v]
      simp only [List.length_append, List.length_take]
      omega
    rcases hcase with ⟨_, hbody⟩ | ⟨hne, _⟩
    · refine ⟨z1, ?_, ?_⟩
      · unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop1
        simp [loop.eq_def, hbody]
      · rw [hz1v]
        rfl
    · exact absurd hd hne
  | succ k ih =>
    intro s z hs hfuel
    obtain ⟨z1, hz1v, hcase⟩ :=
      squeeze_body_eq inst comps F b hF rU d hr hb s z hs
    have hz1len : z1.length = z.length + rU.val := by
      rw [hz1v]
      simp only [List.length_append, List.length_take]
      omega
    rcases hcase with ⟨hd, hbody⟩ | ⟨hne, s', hs'v, hbody⟩
    · refine ⟨z1, ?_, ?_⟩
      · unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop1
        simp [loop.eq_def, hbody]
      · rw [hz1v]
        show _ = (if d ≤ (z ++ s.val.take rU.val).length then _ else _)
        rw [if_pos (by rw [← hz1v]; exact hd)]
    · obtain ⟨out, hout, houtv⟩ := ih s' z1 (by
        rw [hs'v]
        obtain ⟨_, _, _, hlen⟩ := hF s (by omega)
        exact hlen) (by
        have : (k + 1 + 1) * rU.val = rU.val + (k + 1) * rU.val := by ring
        omega)
      refine ⟨out, ?_, ?_⟩
      · unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop1
        rw [loop.eq_def]
        simp only [hbody]
        exact hout
      · rw [houtv, hz1v, hs'v]
        show _ = (if d ≤ (z ++ s.val.take rU.val).length then _ else _)
        rw [if_neg (by rw [← hz1v]; exact hne)]

end Squeeze


/-! ### The sponge -/

/-- Squeezing to completion: enough turns for `d` bits at `r` per turn. -/
def squeezeAll (F : List Bool → List Bool) (r d : Nat) (s : List Bool) : List Bool :=
  squeezeFrom F r d (d / r) s []

/-- Squeezing really does produce at least `d` bits. -/
theorem squeezeFrom_len {b : Nat} (F : List Bool → List Bool)
    (hFlen : ∀ x : List Bool, x.length = b → (F x).length = b)
    (r d : Nat) (_hr : 0 < r) (hrb : r ≤ b) :
    ∀ (k : Nat) (s z : List Bool), s.length = b → d ≤ z.length + (k + 1) * r →
      d ≤ (squeezeFrom F r d k s z).length := by
  intro k
  induction k with
  | zero =>
    intro s z hs hfuel
    simp only [squeezeFrom, List.length_append, List.length_take, hs]
    omega
  | succ k ih =>
    intro s z hs hfuel
    by_cases hd : d ≤ (z ++ s.take r).length
    · show d ≤ (List.length (if d ≤ (z ++ s.take r).length then (z ++ s.take r) else _))
      rw [if_pos hd]
      exact hd
    · show d ≤ (List.length (if d ≤ (z ++ s.take r).length then (z ++ s.take r) else _))
      rw [if_neg hd]
      refine ih (F s) (z ++ s.take r) (hFlen s hs) ?_
      simp only [List.length_append, List.length_take, hs] at *
      have : (k + 1 + 1) * r = r + (k + 1) * r := by ring
      omega

section Sponge

variable {C : Type} (inst : hacspec_sha3_pedantic.sponge.Components C) (comps : C)
  (F : List Bool → List Bool) (b : Nat)

/-- What the `Components` trait's padding has to be: FIPS 202's `pad10*1`.

    No bound on `m`, and none on `r` beyond Sec. 4's own: the lengths are
    `nat::Nat`, and `pad10*1` is total on them. -/
def PadSpec : Prop :=
  ∀ r m : Nat, 0 < r → inst.pad comps r m = ok (padBits r m)

/-- The padded message is a whole number of blocks -- the point of `pad10*1`. -/
theorem padBits_len (x m : Nat) (_hx : 0 < x) :
    (padBits x m).length = ((-(m : Int) - 2) % (x : Int)).toNat + 2 := by
  simp [padBits]

theorem padBits_length (x m : Nat) (hx : 0 < x) :
    (m + (padBits x m).length) % x = 0 := by
  have hj : (((-(m : Int) - 2) % (x : Int)).toNat : Int) = (-(m : Int) - 2) % (x : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have hint : ((m + (padBits x m).length : Nat) : Int) % (x : Int) = 0 := by
    rw [padBits_len x m hx]
    push_cast
    rw [hj]
    have hre : ((m : Int) + ((-(m : Int) - 2) % (x : Int) + 2))
        = (((m : Int) + 2) + ((-(m : Int) - 2) % (x : Int))) := by ring
    rw [hre, Int.add_emod, Int.emod_emod_of_dvd _ dvd_rfl, ← Int.add_emod]
    ring_nf
    exact Int.zero_emod _
  have hcast : (((m + (padBits x m).length) % x : Nat) : Int) = 0 := by
    rw [Int.natCast_mod]
    exact hint
  exact_mod_cast hcast

/-- `SPONGE[f, pad, r](N, d)` (FIPS 202, Algorithm 8).

    The message is an arbitrary-length `BitStr` and its length is a `nat::Nat`,
    so nothing here is bounded: what this theorem asks is Sec. 4's own
    `0 < r ≤ b` and Table 1's `b ≤ 1600`, and that is all. The two hypotheses
    it used to carry — that the padded message and the squeezed output each fit
    a `u64` — are what `MAX_INPUT_LEN` was, and they are gone. -/
theorem sponge_eq (hF : PermSpec inst comps F b) (hP : PadSpec inst comps)
    (bU : Std.Usize) (r d : Nat) (hB : inst.B = ok bU) (hbU : bU.val = b) (hb : b ≤ 1600)
    (hr0 : 0 < r) (hrb : r ≤ b)
    (n : hacspec_sha3_pedantic.bits.BitStr) :
    ∃ out : hacspec_sha3_pedantic.bits.BitStr,
      hacspec_sha3_pedantic.sponge.Sponge.apply inst ⟨comps, r⟩ n d = ok out ∧
      out =
        (squeezeAll F r d
          (absorbFrom F r (b - r) (n ++ padBits r n.length)
            (List.replicate b false) 0
            ((n ++ padBits r n.length).length / r))).take d := by
  have hFlen : ∀ x : List Bool, x.length = b → (F x).length = b := by
    intro x hx
    obtain ⟨_, _, _, hlen⟩ := hF ⟨x, by scalar_tac⟩ hx
    exact hlen
  -- 1. `len(N)`, then `pad(r, len(N))`, then `P = N || pad`. `len` is total, so
  --    the first and fourth steps are equations rather than facts about a word.
  have hnlen : hacspec_sha3_pedantic.bits.BitStr.len n = ok n.length := rfl
  have hpad : inst.pad comps r n.length = ok (padBits r n.length) := hP r n.length hr0
  set P : hacspec_sha3_pedantic.bits.BitStr := n ++ padBits r n.length with hPdef
  have hPlen : P.length = n.length + (padBits r n.length).length := by rw [hPdef]; simp
  have hplenok : hacspec_sha3_pedantic.bits.BitStr.len P = ok P.length := rfl
  have hpmod : P.length % r = 0 := by
    rw [hPlen]
    exact padBits_length r n.length hr0
  -- 2. blocks, capacity, the zero state
  have hrne : ¬ (r = 0) := by omega
  have hblocks : hacspec_sha3_pedantic.nat.Nat.Insts.CoreOpsArithDivNatNat.div P.length r
      = ok (P.length / r) := by
    unfold hacspec_sha3_pedantic.nat.Nat.Insts.CoreOpsArithDivNatNat.div
    rw [if_neg hrne]
  have hblocksn : (P.length / r) * r = P.length :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hpmod)
  obtain ⟨rU, hrU, hrUv⟩ := to_usize_eq r (by scalar_tac)
  obtain ⟨cU, hc, hcv⟩ := usize_sub_eq bU rU (by rw [hrUv]; omega)
  obtain ⟨s1, hs1, hs1v⟩ := zeros_eq bU
  have hs1len : s1.val.length = b := by rw [hs1v]; simp; omega
  -- 3. absorb, then squeeze
  obtain ⟨s2, habs, habsv, habslen⟩ :=
    absorb_loop_eq inst comps F b hF r cU (by rw [hcv, hrUv]; omega) hb hr0 P
      (P.length / r) hblocksn s1 hs1len
  obtain ⟨z1, hsq, hsqv⟩ := squeeze_loop_eq inst comps F b hF rU d (by rw [hrUv]; omega) hb
    (d / r) s2 [] habslen
    (by
      rw [hrUv]
      simp only [List.length_nil, Nat.zero_add]
      have h1 : d / r * r + d % r = d := by
        have h0 : r * (d / r) + d % r = d := Nat.div_add_mod _ _
        have hcomm : d / r * r = r * (d / r) := Nat.mul_comm _ _
        omega
      have h2 : d % r < r := Nat.mod_lt _ hr0
      have : (d / r + 1) * r = d / r * r + r := by ring
      omega)
  -- 4. the squeeze really produced `d` bits, so the final truncation is in range
  have hz1len : d ≤ z1.length := by
    rw [hsqv, hrUv]
    refine squeezeFrom_len F hFlen r d hr0 hrb _ s2.val [] habslen ?_
    have h1 : d / r * r + d % r = d := by
      have h0 : r * (d / r) + d % r = d := Nat.div_add_mod _ _
      have hcomm : d / r * r = r * (d / r) := Nat.mul_comm _ _
      omega
    have h2 : d % r < r := Nat.mod_lt _ hr0
    have : (d / r + 1) * r = d / r * r + r := by ring
    simp
    omega
  refine ⟨z1.take d, ?_, ?_⟩
  · have hcat : hacspec_sha3_pedantic.bits.BitStr.concat n (padBits r n.length) = ok P := rfl
    have hempty : (hacspec_sha3_pedantic.bits.BitStr.empty : RustM hacspec_sha3_pedantic.bits.BitStr)
        = ok ([] : List Bool) := rfl
    have hnew0 : hacspec_sha3_pedantic.nat.Nat.new 0#u64 = ok 0 := rfl
    have htr : hacspec_sha3_pedantic.bits.BitStr.trunc z1 d = ok (z1.take d) := if_pos hz1len
    unfold hacspec_sha3_pedantic.sponge.Sponge.apply
    rw [hnlen, bind_tc_ok, hpad, bind_tc_ok, hcat, bind_tc_ok, hplenok, bind_tc_ok,
      hblocks, bind_tc_ok, hrU, bind_tc_ok, hB, bind_tc_ok, hc, bind_tc_ok,
      hs1, bind_tc_ok, hnew0, bind_tc_ok, habs, bind_tc_ok, hempty, bind_tc_ok, hsq, bind_tc_ok]
    exact htr
  · rw [hsqv, habsv, hs1v]
    simp only [squeezeAll, hcv, hrUv, hbU, hPdef]

end Sponge

-- Pinned by `#guard_msgs`: the build fails if this comes to depend on any axiom
-- beyond Lean's standard three.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.sponge_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sponge_eq

end LibcruxIotSha3.Composition.Pedantic
