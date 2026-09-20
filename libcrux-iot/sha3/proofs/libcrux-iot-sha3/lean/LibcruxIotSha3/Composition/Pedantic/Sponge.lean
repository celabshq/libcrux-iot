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

theorem absorb_body_cont (hF : PermSpec inst comps F b)
    (r : Std.U64) (c : Std.Usize) (hrc : r.val + c.val = b) (_hb : b ≤ 1600)
    (p : hacspec_sha3_pedantic.bits.BitStr) (hr : 0 < r.val)
    (hpb : p.length ≤ Std.U64.max)
    (blocks : Std.U64) (hblocks : blocks.val * r.val = p.length)
    (i : Std.U64) (hi : i.val < blocks.val)
    (s : alloc.vec.Vec Bool) (hs : s.val.length = b) :
    ∃ (t : Std.U64) (s' : alloc.vec.Vec Bool), t.val = i.val + 1 ∧
      s'.val = absorbStep F r.val c.val p s.val i.val ∧
      hacspec_sha3_pedantic.sponge.Sponge.apply_loop0.body inst ⟨comps, r⟩ comps p blocks c s i
        = ok (.cont (s', t)) := by
  -- `i * r` and `(i+1) * r` are both within the string, so neither overflows
  have hir : i.val * r.val + r.val ≤ p.length := by
    rw [← hblocks]
    calc i.val * r.val + r.val = (i.val + 1) * r.val := by ring
      _ ≤ blocks.val * r.val := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨i1, hi1, hi1v⟩ := Std.WP.spec_imp_exists
    (Std.UScalar.mul_spec (x := i) (y := r) (by
      have : i.val * r.val ≤ p.length := by omega
      scalar_tac))
  obtain ⟨t, ht, htv⟩ := Std.WP.spec_imp_exists
    (Std.WP.spec_of_partialSpec (Std.UScalar.add_spec (x := i) (y := (1#u64 : Std.U64)))
      (by intro e; cases e <;> simp; scalar_tac) (by simp))
  -- the block: `r` bits of `p` from `i * r`, zero-extended to the full width
  have hslice : hacspec_sha3_pedantic.bits.BitStr.slice p i1 r
      = ok ((p.drop (i.val * r.val)).take r.val) := by
    unfold hacspec_sha3_pedantic.bits.BitStr.slice
    rw [if_pos (by rw [hi1v]; exact hir), hi1v]
  have hsl : ((p.drop (i.val * r.val)).take r.val).length = r.val := by
    simp only [List.length_take, List.length_drop]; omega
  have hto : hacspec_sha3_pedantic.bits.BitStr.to_bits ((p.drop (i.val * r.val)).take r.val)
      = ok ⟨(p.drop (i.val * r.val)).take r.val, by rw [hsl]; scalar_tac⟩ := by
    unfold hacspec_sha3_pedantic.bits.BitStr.to_bits
    exact dif_pos (by rw [hsl]; scalar_tac)
  obtain ⟨zs, hzs, hzsv⟩ := zeros_eq c
  obtain ⟨blk, hblk, hblkv⟩ := concat_eq
    ⟨(p.drop (i.val * r.val)).take r.val, by rw [hsl]; scalar_tac⟩ zs (by
      simp only [hsl, hzsv, List.length_replicate]; scalar_tac)
  have hblkv' : blk.val = (p.drop (i.val * r.val)).take r.val ++ zs.val := by simpa using hblkv
  have hblklen : blk.val.length = b := by
    rw [hblkv']
    simp only [List.length_append, hsl, hzsv, List.length_replicate]
    omega
  -- XOR into the state and permute
  obtain ⟨xs, hxs, hxsv⟩ := xor_eq s blk (by simp [hs, hblklen])
  obtain ⟨o, ho, hov, holen⟩ := hF xs (by simp only [hxsv]; simp [hs, hblklen])
  refine ⟨t, o, htv, ?_, ?_⟩
  · have hxsv' : xs.val = List.zipWith (· ^^ ·) s.val blk.val := by simpa using hxsv
    rw [hov, hxsv', hblkv', hzsv]
    rfl
  · unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop0.body
    rw [if_pos (show i < blocks from (Std.UScalar.lt_equiv i blocks).mpr hi)]
    simp [hi1, hslice, hto, hzs, vec_deref_eq, hblk, hxs, ho, ht]

theorem absorb_body_done (r : Std.U64) (c : Std.Usize)
    (p : hacspec_sha3_pedantic.bits.BitStr)
    (blocks : Std.U64) (s : alloc.vec.Vec Bool) :
    hacspec_sha3_pedantic.sponge.Sponge.apply_loop0.body inst ⟨comps, r⟩ comps p blocks c s blocks
      = ok (.done s) := by
  unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop0.body
  rw [if_neg (by simp)]

/-- The absorb loop of Algorithm 8, steps 5-6. -/
theorem absorb_loop_eq (hF : PermSpec inst comps F b)
    (r : Std.U64) (c : Std.Usize) (hrc : r.val + c.val = b) (hb : b ≤ 1600) (hr : 0 < r.val)
    (p : hacspec_sha3_pedantic.bits.BitStr) (hpb : p.length ≤ Std.U64.max)
    (blocks : Std.U64) (hblocks : blocks.val * r.val = p.length)
    (s : alloc.vec.Vec Bool) (hs : s.val.length = b) :
    ∃ s' : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.sponge.Sponge.apply_loop0 inst ⟨comps, r⟩ comps p blocks c s 0#u64
        = ok s' ∧
      s'.val = absorbFrom F r.val c.val p s.val 0 blocks.val ∧ s'.val.length = b := by
  have h := loop_counter_eq_inv_u64 (β := alloc.vec.Vec Bool) (γ := alloc.vec.Vec Bool)
    (fun q => hacspec_sha3_pedantic.sponge.Sponge.apply_loop0.body inst ⟨comps, r⟩
      comps p blocks c q.1 q.2)
    blocks
    (fun _ acc => acc.val.length = b)
    (fun i acc r' => r'.val = absorbFrom F r.val c.val p acc.val i.val (blocks.val - i.val)
      ∧ r'.val.length = b)
    ?hstep ?hdone blocks.val 0#u64 s (by simp) hs
  case hstep =>
    intro i acc hi hinv
    obtain ⟨t, s', ht, hs', hbody⟩ :=
      absorb_body_cont inst comps F b hF r c hrc hb p hr hpb blocks hblocks i hi acc hinv
    refine ⟨t, s', ht, ?_, hbody, ?_⟩
    · rw [hs']
      obtain ⟨o, _, hov, holen⟩ := hF ⟨List.zipWith (· ^^ ·) acc.val
          ((p.drop (i.val * r.val)).take r.val ++ List.replicate c.val false), by
        have := acc.property
        simp only [List.length_zipWith]
        scalar_tac⟩ (by
        simp only [List.length_zipWith, List.length_append, List.length_replicate, hinv]
        have hlen : ((p.drop (i.val * r.val)).take r.val).length = r.val := by
          have hub : i.val * r.val + r.val ≤ p.length := by
            rw [← hblocks]
            calc i.val * r.val + r.val = (i.val + 1) * r.val := by ring
              _ ≤ blocks.val * r.val := Nat.mul_le_mul_right _ (by omega)
          simp only [List.length_take, List.length_drop]
          omega
        rw [hlen]
        omega)
      simpa only [absorbStep] using holen
    · rintro r' ⟨hr', hrlen⟩
      refine ⟨?_, hrlen⟩
      rw [hr', hs', ht, show blocks.val - i.val = (blocks.val - (i.val + 1)) + 1 by omega]
      rfl
  case hdone =>
    intro acc hinv
    refine ⟨acc, absorb_body_done inst comps r c p blocks acc, ?_, hinv⟩
    rw [show blocks.val - blocks.val = 0 by omega]
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

theorem squeeze_body_eq (hF : PermSpec inst comps F b) (r d : Std.U64)
    (hr : r.val ≤ b) (_hb : b ≤ 1600) (s : alloc.vec.Vec Bool)
    (z : hacspec_sha3_pedantic.bits.BitStr) (hs : s.val.length = b)
    (hz : z.length + r.val < 2 ^ 64) :
    ∃ z1 : hacspec_sha3_pedantic.bits.BitStr, z1 = z ++ s.val.take r.val ∧
      ((d.val ≤ z1.length ∧
          hacspec_sha3_pedantic.sponge.Sponge.apply_loop1.body inst ⟨comps, r⟩ d comps s z
            = ok (.done z1)) ∨
       (¬ (d.val ≤ z1.length) ∧ ∃ s' : alloc.vec.Vec Bool, s'.val = F s.val ∧
          hacspec_sha3_pedantic.sponge.Sponge.apply_loop1.body inst ⟨comps, r⟩ d comps s z
            = ok (.cont (s', z1)))) := by
  -- `r` crosses to the fixed-width layer; it is at most 1600, so the cast is exact
  have hru : (Std.UScalar.cast Std.UScalarTy.Usize r).val = r.val := by
    rw [Std.UScalar.cast_val_eq]
    have hlt : r.val < 2 ^ System.Platform.numBits := by scalar_tac
    exact Nat.mod_eq_of_lt hlt
  obtain ⟨head, hhead, hheadv⟩ :=
    trunc_eq s (Std.UScalar.cast Std.UScalarTy.Usize r) (by rw [hru]; omega)
  have hheadlen : head.val.length = r.val := by
    rw [hheadv, hru]; simp; omega
  have hz1len : (z ++ head.val).length = z.length + r.val := by simp [hheadlen]
  -- the length of `Z` is read back as a `u64`, which it fits
  have hinner : z.length + head.val.length < 18446744073709551616 := by
    rw [hheadlen]; omega
  have hlenval : (⟨BitVec.ofNat 64 (z.length + head.val.length)⟩ : Std.U64).val
      = z.length + head.val.length := by
    show (BitVec.ofNat 64 (z.length + head.val.length)).toNat = z.length + head.val.length
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hinner
  refine ⟨z ++ head.val, by rw [hheadv, hru], ?_⟩
  by_cases hd : d.val ≤ (z ++ head.val).length
  · refine Or.inl ⟨hd, ?_⟩
    have hdn : d.val ≤ z.length + head.val.length := by
      have : (z ++ head.val).length = z.length + head.val.length := by simp
      omega
    unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop1.body
      hacspec_sha3_pedantic.bits.BitStr.from_bits
      hacspec_sha3_pedantic.bits.BitStr.concat
      hacspec_sha3_pedantic.bits.BitStr.len
    simp [vec_deref_eq, Std.lift, hhead, hinner, hlenval, hdn]
  · obtain ⟨s', hs', hs'v, -⟩ := hF s (by omega)
    refine Or.inr ⟨hd, s', hs'v, ?_⟩
    have hdn : ¬ (d.val ≤ z.length + head.val.length) := by
      have : (z ++ head.val).length = z.length + head.val.length := by simp
      omega
    unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop1.body
      hacspec_sha3_pedantic.bits.BitStr.from_bits
      hacspec_sha3_pedantic.bits.BitStr.concat
      hacspec_sha3_pedantic.bits.BitStr.len
    simp [vec_deref_eq, Std.lift, hhead, hinner, hlenval, hdn, hs']


/-- The squeeze loop: it emits `r` bits per turn until `d` are out. -/
theorem squeeze_loop_eq (hF : PermSpec inst comps F b) (r d : Std.U64)
    (hr : r.val ≤ b) (hb : b ≤ 1600) :
    ∀ (k : Nat) (s : alloc.vec.Vec Bool) (z : hacspec_sha3_pedantic.bits.BitStr),
      s.val.length = b →
      d.val ≤ z.length + (k + 1) * r.val →
      z.length + (k + 1) * r.val < 2 ^ 64 →
      ∃ out : hacspec_sha3_pedantic.bits.BitStr,
        hacspec_sha3_pedantic.sponge.Sponge.apply_loop1 inst ⟨comps, r⟩ d comps s z = ok out ∧
        out = squeezeFrom F r.val d.val k s.val z := by
  intro k
  induction k with
  | zero =>
    intro s z hs hfuel hroom
    obtain ⟨z1, hz1v, hcase⟩ :=
      squeeze_body_eq inst comps F b hF r d hr hb s z hs (by omega)
    have hd : d.val ≤ z1.length := by
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
    intro s z hs hfuel hroom
    obtain ⟨z1, hz1v, hcase⟩ :=
      squeeze_body_eq inst comps F b hF r d hr hb s z hs (by
        have : (k + 1 + 1) * r.val = r.val + (k + 1) * r.val := by ring
        omega)
    have hz1len : z1.length = z.length + r.val := by
      rw [hz1v]
      simp only [List.length_append, List.length_take]
      omega
    rcases hcase with ⟨hd, hbody⟩ | ⟨hne, s', hs'v, hbody⟩
    · refine ⟨z1, ?_, ?_⟩
      · unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop1
        simp [loop.eq_def, hbody]
      · rw [hz1v]
        show _ = (if d.val ≤ (z ++ s.val.take r.val).length then _ else _)
        rw [if_pos (by rw [← hz1v]; exact hd)]
    · obtain ⟨out, hout, houtv⟩ := ih s' z1 (by
        rw [hs'v]
        obtain ⟨_, _, _, hlen⟩ := hF s (by omega)
        exact hlen) (by
        have : (k + 1 + 1) * r.val = r.val + (k + 1) * r.val := by ring
        omega) (by
        have : (k + 1 + 1) * r.val = r.val + (k + 1) * r.val := by ring
        omega)
      refine ⟨out, ?_, ?_⟩
      · unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop1
        rw [loop.eq_def]
        simp only [hbody]
        exact hout
      · rw [houtv, hz1v, hs'v]
        show _ = (if d.val ≤ (z ++ s.val.take r.val).length then _ else _)
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

    No bound on `m`: the message length is a `u64` now, and `pad10*1` is total
    on it. -/
def PadSpec : Prop :=
  ∀ r m : Std.U64, 0 < r.val → r.val ≤ 1600 →
    inst.pad comps r m = ok (padBits r.val m.val)

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

    The message is an arbitrary-length `BitStr`. What is still bounded is what
    a `u64` has to hold: the padded message's length, and the output the
    squeeze accumulates. Neither moves with the target word size, which is the
    whole point of the type. -/
theorem sponge_eq (hF : PermSpec inst comps F b) (hP : PadSpec inst comps)
    (bU : Std.Usize) (r d : Std.U64) (hB : inst.B = ok bU) (hbU : bU.val = b) (hb : b ≤ 1600)
    (hr0 : 0 < r.val) (hrb : r.val ≤ b)
    (n : hacspec_sha3_pedantic.bits.BitStr)
    (hnb : n.length + r.val + 2 < 2 ^ 64)
    (hdb : d.val + r.val < 2 ^ 64) :
    ∃ out : hacspec_sha3_pedantic.bits.BitStr,
      hacspec_sha3_pedantic.sponge.Sponge.apply inst ⟨comps, r⟩ n d = ok out ∧
      out =
        (squeezeAll F r.val d.val
          (absorbFrom F r.val (b - r.val) (n ++ padBits r.val n.length)
            (List.replicate b false) 0
            ((n ++ padBits r.val n.length).length / r.val))).take d.val := by
  have hFlen : ∀ x : List Bool, x.length = b → (F x).length = b := by
    intro x hx
    obtain ⟨_, _, _, hlen⟩ := hF ⟨x, by scalar_tac⟩ hx
    exact hlen
  -- 1. `len(N)`, then `pad(r, len(N))`, then `P = N || pad`
  have hnlen : hacspec_sha3_pedantic.bits.BitStr.len n
      = ok ⟨BitVec.ofNat 64 n.length⟩ := if_pos (by omega)
  have hnlenv : (⟨BitVec.ofNat 64 n.length⟩ : Std.U64).val = n.length := by
    show (BitVec.ofNat 64 n.length).toNat = n.length
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hpad : inst.pad comps r ⟨BitVec.ofNat 64 n.length⟩ = ok (padBits r.val n.length) := by
    rw [hP r ⟨BitVec.ofNat 64 n.length⟩ hr0 (by omega), hnlenv]
  have hpadlen : (padBits r.val n.length).length ≤ r.val + 2 := by
    rw [padBits_len r.val n.length hr0]
    have h1 : (-(n.length : Int) - 2) % (r.val : Int) < (r.val : Int) :=
      Int.emod_lt_of_pos _ (by omega)
    omega
  set P : hacspec_sha3_pedantic.bits.BitStr := n ++ padBits r.val n.length with hPdef
  have hPlen : P.length = n.length + (padBits r.val n.length).length := by
    rw [hPdef]; simp
  have hPb : P.length < 2 ^ 64 := by omega
  have hplenok : hacspec_sha3_pedantic.bits.BitStr.len P
      = ok ⟨BitVec.ofNat 64 P.length⟩ := if_pos hPb
  have hplenv : (⟨BitVec.ofNat 64 P.length⟩ : Std.U64).val = P.length := by
    show (BitVec.ofNat 64 P.length).toNat = P.length
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hPb
  have hpmod : P.length % r.val = 0 := by
    rw [hPlen]
    exact padBits_length r.val n.length hr0
  -- 2. blocks, capacity, the zero state
  obtain ⟨blocks, hblocks, hblocksv, -⟩ :=
    Std.UScalar.div_bv_spec (⟨BitVec.ofNat 64 P.length⟩ : Std.U64) (y := r) (by
      intro h; rw [h] at hr0; exact absurd hr0 (by simp))
  have hblocksn : blocks.val * r.val = P.length := by
    rw [hblocksv, hplenv]
    exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hpmod)
  have hru : (Std.UScalar.cast Std.UScalarTy.Usize r).val = r.val := by
    rw [Std.UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by scalar_tac)
  obtain ⟨cU, hc, hcv⟩ := usize_sub_eq bU (Std.UScalar.cast Std.UScalarTy.Usize r) (by
    rw [hru]; omega)
  obtain ⟨s1, hs1, hs1v⟩ := zeros_eq bU
  have hs1len : s1.val.length = b := by rw [hs1v]; simp; omega
  -- 3. absorb, then squeeze
  obtain ⟨s2, habs, habsv, habslen⟩ :=
    absorb_loop_eq inst comps F b hF r cU (by rw [hcv, hru]; omega) hb hr0 P
      (by have : (2:Nat) ^ 64 - 1 ≤ Std.U64.max := by scalar_tac
          omega)
      blocks hblocksn s1 hs1len
  obtain ⟨z1, hsq, hsqv⟩ := squeeze_loop_eq inst comps F b hF r d hrb hb (d.val / r.val) s2
    [] habslen
    (by
      simp only [List.length_nil, Nat.zero_add]
      have h1 : d.val / r.val * r.val + d.val % r.val = d.val := by
        have h0 : r.val * (d.val / r.val) + d.val % r.val = d.val := Nat.div_add_mod _ _
        have hcomm : d.val / r.val * r.val = r.val * (d.val / r.val) := Nat.mul_comm _ _
        omega
      have h2 : d.val % r.val < r.val := Nat.mod_lt _ hr0
      have : (d.val / r.val + 1) * r.val = d.val / r.val * r.val + r.val := by ring
      omega)
    (by
      simp only [List.length_nil, Nat.zero_add]
      have h1 : d.val / r.val * r.val ≤ d.val := Nat.div_mul_le_self _ _
      have : (d.val / r.val + 1) * r.val = d.val / r.val * r.val + r.val := by ring
      omega)
  -- 4. the squeeze really produced `d` bits, so the final truncation is in range
  have hz1len : d.val ≤ z1.length := by
    rw [hsqv]
    refine squeezeFrom_len F hFlen r.val d.val hr0 hrb _ s2.val [] habslen ?_
    have h1 : d.val / r.val * r.val + d.val % r.val = d.val := by
      have h0 : r.val * (d.val / r.val) + d.val % r.val = d.val := Nat.div_add_mod _ _
      have hcomm : d.val / r.val * r.val = r.val * (d.val / r.val) := Nat.mul_comm _ _
      omega
    have h2 : d.val % r.val < r.val := Nat.mod_lt _ hr0
    have : (d.val / r.val + 1) * r.val = d.val / r.val * r.val + r.val := by ring
    simp
    omega
  refine ⟨z1.take d.val, ?_, ?_⟩
  · have hcat : hacspec_sha3_pedantic.bits.BitStr.concat n (padBits r.val n.length) = ok P := rfl
    have hempty : (hacspec_sha3_pedantic.bits.BitStr.empty : RustM hacspec_sha3_pedantic.bits.BitStr)
        = ok ([] : List Bool) := rfl
    have hliftcast : (Std.lift (Std.UScalar.cast Std.UScalarTy.Usize r) : RustM Std.Usize)
        = ok (Std.UScalar.cast Std.UScalarTy.Usize r) := rfl
    have htr : hacspec_sha3_pedantic.bits.BitStr.trunc z1 d = ok (z1.take d.val) :=
      if_pos hz1len
    unfold hacspec_sha3_pedantic.sponge.Sponge.apply
    rw [hnlen, bind_tc_ok, hpad, bind_tc_ok, hcat, bind_tc_ok, hplenok, bind_tc_ok,
      hblocks, bind_tc_ok, hliftcast, bind_tc_ok, hB, bind_tc_ok, hc, bind_tc_ok,
      hs1, bind_tc_ok, habs, bind_tc_ok, hempty, bind_tc_ok, hsq, bind_tc_ok]
    exact htr
  · have hplenv' : (⟨BitVec.ofNat 64 (n ++ padBits r.val n.length).length⟩ : Std.U64).val
        = (n ++ padBits r.val n.length).length := hplenv
    rw [hsqv, habsv, hs1v, hcv, hru, hbU]
    simp only [squeezeAll, hblocksv, hplenv', hPdef]

end Sponge

-- Pinned by `#guard_msgs`: the build fails if this comes to depend on any axiom
-- beyond Lean's standard three.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.sponge_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sponge_eq

end LibcruxIotSha3.Composition.Pedantic
