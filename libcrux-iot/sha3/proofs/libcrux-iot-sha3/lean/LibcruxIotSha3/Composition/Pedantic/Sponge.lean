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
    (r c : Std.Usize) (hrc : r.val + c.val = b) (p : alloc.vec.Vec Bool)
    (hr : 0 < r.val)
    (blocks : Std.Usize) (hblocks : blocks.val * r.val = p.val.length)
    (i : Std.Usize) (hi : i.val < blocks.val)
    (s : alloc.vec.Vec Bool) (hs : s.val.length = b) :
    ∃ (t : Std.Usize) (s' : alloc.vec.Vec Bool), t.val = i.val + 1 ∧
      s'.val = absorbStep F r.val c.val p.val s.val i.val ∧
      hacspec_sha3_pedantic.sponge.Sponge.apply_loop0.body inst ⟨comps, r⟩ comps p c
        { start := i, «end» := blocks } s
        = ok (.cont ({ start := t, «end» := blocks }, s')) := by
  obtain ⟨t, ht, hnext⟩ := range_next_lt i blocks hi
  -- the block bounds
  have hpb : p.val.length ≤ Std.Usize.max := p.property
  obtain ⟨i1, hi1, hi1v⟩ := usize_mul_eq i r (by
    have : i.val * r.val ≤ p.val.length := by
      calc i.val * r.val ≤ blocks.val * r.val := by
            exact Nat.mul_le_mul_right _ (by omega)
        _ = p.val.length := hblocks
    scalar_tac)
  obtain ⟨i2, hi2, hi2v⟩ := usize_add_eq i 1#usize (by scalar_tac)
  obtain ⟨i3, hi3, hi3v⟩ := usize_mul_eq i2 r (by
    have : i2.val * r.val ≤ p.val.length := by
      rw [hi2v]
      calc (i.val + (1#usize : Std.Usize).val) * r.val ≤ blocks.val * r.val := by
            simp
            exact Nat.mul_le_mul_right _ (by omega)
        _ = p.val.length := hblocks
    scalar_tac)
  have hi1n : i1.val = i.val * r.val := hi1v
  have hmul : (i.val + 1) * r.val = i.val * r.val + r.val := by ring
  have hi3n : i3.val = i.val * r.val + r.val := by rw [hi3v, hi2v]; simp; omega
  have hle : i1.val ≤ i3.val := by omega
  have hub : i3.val ≤ p.val.length := by
    rw [hi3n, ← hmul, ← hblocks]
    exact Nat.mul_le_mul_right _ (by omega)
  have hsl : (p.val.slice i1.val i3.val).length = r.val := by
    simp only [List.slice, List.length_take, List.length_drop]
    omega
  -- the block itself, zero-extended
  obtain ⟨zs, hzs, hzsv⟩ := zeros_eq c
  obtain ⟨blk, hblk, hblkv⟩ := concat_eq ⟨p.val.slice i1.val i3.val, by
      have := p.val.slice_length_le i1.val i3.val; scalar_tac⟩ zs (by
    simp only [hsl, hzsv, List.length_replicate]
    scalar_tac)
  have hblkv' : blk.val = p.val.slice i1.val i3.val ++ zs.val := by simpa using hblkv
  have hblklen : blk.val.length = b := by
    rw [hblkv']
    simp only [List.length_append, hsl, hzsv, List.length_replicate]
    omega
  -- XOR into the state and permute
  obtain ⟨xs, hxs, hxsv⟩ := xor_eq s blk (by simp [hs, hblklen])
  obtain ⟨o, ho, hov, holen⟩ := hF xs (by
    simp only [hxsv]
    simp [hs, hblklen])
  refine ⟨t, o, ht, ?_, ?_⟩
  · have hslice : p.val.slice i1.val i3.val = (p.val.drop (i.val * r.val)).take r.val := by
      simp only [List.slice, hi1n, hi3n]
      congr 1
      omega
    have hxsv' : xs.val = List.zipWith (· ^^ ·) s.val blk.val := by simpa using hxsv
    rw [hov, hxsv', hblkv', hzsv, hslice]
    rfl
  · unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop0.body
    rw [hnext]
    simp [hi1, hi2, hi3, vec_index_range_eq p i1 i3 hle hub, hzs, vec_deref_eq, hblk, hxs, ho]


theorem absorb_body_done (r c : Std.Usize) (p : alloc.vec.Vec Bool)
    (blocks : Std.Usize) (s : alloc.vec.Vec Bool) :
    hacspec_sha3_pedantic.sponge.Sponge.apply_loop0.body inst ⟨comps, r⟩ comps p c
      { start := blocks, «end» := blocks } s = ok (.done s) := by
  unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop0.body
  rw [range_next_ge blocks blocks (le_refl _)]
  simp

/-- The absorb loop of Algorithm 8, steps 5-6. -/
theorem absorb_loop_eq (hF : PermSpec inst comps F b)
    (r c : Std.Usize) (hrc : r.val + c.val = b) (hr : 0 < r.val)
    (p : alloc.vec.Vec Bool) (blocks : Std.Usize) (hblocks : blocks.val * r.val = p.val.length)
    (s : alloc.vec.Vec Bool) (hs : s.val.length = b) :
    ∃ s' : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.sponge.Sponge.apply_loop0 inst ⟨comps, r⟩ { start := 0#usize, «end» := blocks }
        comps p c s = ok s' ∧
      s'.val = absorbFrom F r.val c.val p.val s.val 0 blocks.val ∧ s'.val.length = b := by
  have h := loop_range_eq_inv_usize (β := alloc.vec.Vec Bool) (γ := alloc.vec.Vec Bool)
    (fun q => hacspec_sha3_pedantic.sponge.Sponge.apply_loop0.body inst ⟨comps, r⟩ comps p c q.1 q.2)
    blocks
    (fun _ acc => acc.val.length = b)
    (fun i acc r' => r'.val = absorbFrom F r.val c.val p.val acc.val i.val (blocks.val - i.val)
      ∧ r'.val.length = b)
    ?hstep ?hdone blocks.val 0#usize s (by simp) hs
  case hstep =>
    intro i acc hi hinv
    obtain ⟨t, s', ht, hs', hbody⟩ :=
      absorb_body_cont inst comps F b hF r c hrc p hr blocks hblocks i hi acc hinv
    refine ⟨t, s', ht, ?_, hbody, ?_⟩
    · rw [hs']
      obtain ⟨o, _, hov, holen⟩ := hF ⟨List.zipWith (· ^^ ·) acc.val
          ((p.val.drop (i.val * r.val)).take r.val ++ List.replicate c.val false), by
        have := acc.property
        have := p.property
        simp only [List.length_zipWith]
        scalar_tac⟩ (by
        simp only [List.length_zipWith, List.length_append, List.length_replicate, hinv]
        have hlen : ((p.val.drop (i.val * r.val)).take r.val).length = r.val := by
          have hub : i.val * r.val + r.val ≤ p.val.length := by
            rw [← hblocks]
            calc i.val * r.val + r.val = (i.val + 1) * r.val := by ring
              _ ≤ blocks.val * r.val := Nat.mul_le_mul_right _ (by omega)
          simp
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

theorem squeeze_body_eq (hF : PermSpec inst comps F b) (r d : Std.Usize)
    (hr : r.val ≤ b) (_hb : b ≤ 1600) (s z : alloc.vec.Vec Bool) (hs : s.val.length = b)
    (hz : z.val.length + r.val ≤ Std.Usize.max) :
    ∃ z1 : alloc.vec.Vec Bool, z1.val = z.val ++ s.val.take r.val ∧
      ((d.val ≤ z1.val.length ∧
          hacspec_sha3_pedantic.sponge.Sponge.apply_loop1.body inst ⟨comps, r⟩ d comps s z
            = ok (.done z1)) ∨
       (¬ (d.val ≤ z1.val.length) ∧ ∃ s' : alloc.vec.Vec Bool, s'.val = F s.val ∧
          hacspec_sha3_pedantic.sponge.Sponge.apply_loop1.body inst ⟨comps, r⟩ d comps s z
            = ok (.cont (s', z1)))) := by
  obtain ⟨head, hhead, hheadv⟩ := trunc_eq s r (by omega)
  obtain ⟨z1, hz1, hz1v⟩ := concat_eq z head (by
    rw [hheadv]
    have : (s.val.take r.val).length = r.val := by simp; omega
    omega)
  have hz1v' : z1.val = z.val ++ s.val.take r.val := by rw [hz1v, hheadv]
  refine ⟨z1, hz1v', ?_⟩
  by_cases hd : d.val ≤ z1.val.length
  · refine Or.inl ⟨hd, ?_⟩
    unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop1.body
    simp [vec_deref_eq, vec_len_eq, hhead, hz1, hd]
  · obtain ⟨s', hs', hs'v, _⟩ := hF s (by omega)
    refine Or.inr ⟨hd, s', hs'v, ?_⟩
    unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop1.body
    simp [vec_deref_eq, vec_len_eq, hhead, hz1, hd, hs']

/-- The squeeze loop: it emits `r` bits per turn until `d` are out. -/
theorem squeeze_loop_eq (hF : PermSpec inst comps F b) (r d : Std.Usize)
    (hr : r.val ≤ b) (hb : b ≤ 1600) :
    ∀ (k : Nat) (s z : alloc.vec.Vec Bool), s.val.length = b →
      d.val ≤ z.val.length + (k + 1) * r.val →
      z.val.length + (k + 1) * r.val ≤ Std.Usize.max →
      ∃ out : alloc.vec.Vec Bool,
        hacspec_sha3_pedantic.sponge.Sponge.apply_loop1 inst ⟨comps, r⟩ d comps s z = ok out ∧
        out.val = squeezeFrom F r.val d.val k s.val z.val := by
  intro k
  induction k with
  | zero =>
    intro s z hs hfuel hroom
    obtain ⟨z1, hz1v, hcase⟩ :=
      squeeze_body_eq inst comps F b hF r d hr hb s z hs (by omega)
    have hd : d.val ≤ z1.val.length := by
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
    have hz1len : z1.val.length = z.val.length + r.val := by
      rw [hz1v]
      simp only [List.length_append, List.length_take]
      omega
    rcases hcase with ⟨hd, hbody⟩ | ⟨hne, s', hs'v, hbody⟩
    · refine ⟨z1, ?_, ?_⟩
      · unfold hacspec_sha3_pedantic.sponge.Sponge.apply_loop1
        simp [loop.eq_def, hbody]
      · rw [hz1v]
        show _ = (if d.val ≤ (z.val ++ s.val.take r.val).length then _ else _)
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
        show _ = (if d.val ≤ (z.val ++ s.val.take r.val).length then _ else _)
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

/-- What the `Components` trait's padding has to be: FIPS 202's `pad10*1`. -/
def PadSpec : Prop :=
  ∀ r m : Std.Usize, 0 < r.val → r.val ≤ 1600 → m.val ≤ 4294965000 →
    ∃ v : alloc.vec.Vec Bool, inst.pad comps r m = ok v ∧ v.val = padBits r.val m.val

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

/-- `SPONGE[f, pad, r](N, d)` (FIPS 202, Algorithm 8). -/
theorem sponge_eq (hF : PermSpec inst comps F b) (hP : PadSpec inst comps)
    (bU r d : Std.Usize) (hB : inst.B = ok bU) (hbU : bU.val = b) (hb : b ≤ 1600)
    (hr0 : 0 < r.val) (hrb : r.val ≤ b)
    (n : Slice Bool) (hn : n.val.length ≤ 4294965000)
    (hdb : d.val ≤ 4294965000) :
    ∃ out : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.sponge.Sponge.apply inst ⟨comps, r⟩ n d = ok out ∧
      out.val =
        (squeezeAll F r.val d.val
          (absorbFrom F r.val (b - r.val) (n.val ++ padBits r.val n.val.length)
            (List.replicate b false) 0
            ((n.val ++ padBits r.val n.val.length).length / r.val))).take d.val := by
  have hFlen : ∀ x : List Bool, x.length = b → (F x).length = b := by
    intro x hx
    obtain ⟨_, _, _, hlen⟩ := hF ⟨x, by scalar_tac⟩ hx
    exact hlen
  have husize : (4294967295 : Nat) ≤ Std.Usize.max := by scalar_tac
  -- pad, then concatenate
  obtain ⟨v, hv, hvv⟩ := hP r (Std.Usize.ofNatCore n.val.length (by scalar_tac)) hr0 (by omega)
    (by simp; omega)
  have hpadlen : (padBits r.val n.val.length).length ≤ r.val + 2 := by
    rw [padBits_len r.val n.val.length hr0]
    have h1 : (-(n.val.length : Int) - 2) % (r.val : Int) < (r.val : Int) :=
      Int.emod_lt_of_pos _ (by omega)
    omega
  have hvv' : v.val = padBits r.val n.val.length := by simpa using hvv
  obtain ⟨p, hp, hpv⟩ := concat_eq n v (by rw [hvv']; omega)
  have hpv' : p.val = n.val ++ padBits r.val n.val.length := by rw [hpv, hvv']
  have hplen : p.val.length = n.val.length + (padBits r.val n.val.length).length := by
    rw [hpv']; simp
  have hpmod : p.val.length % r.val = 0 := by
    rw [hplen]; exact padBits_length r.val n.val.length hr0
  -- blocks, capacity, the zero state
  obtain ⟨blocks, hblocks, hblocksv⟩ :=
    usize_div_eq (Std.Usize.ofNatCore p.val.length (by scalar_tac)) r (by omega)
  have hblocksn : blocks.val * r.val = p.val.length := by
    rw [hblocksv]
    simp only [Std.Usize.ofNatCore]
    have : p.val.length / r.val * r.val = p.val.length :=
      Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hpmod)
    simpa using this
  obtain ⟨cU, hc, hcv⟩ := usize_sub_eq bU r (by omega)
  obtain ⟨s1, hs1, hs1v⟩ := zeros_eq bU
  have hs1len : s1.val.length = b := by rw [hs1v]; simp; omega
  -- absorb, then squeeze
  obtain ⟨s2, habs, habsv, habslen⟩ := absorb_loop_eq inst comps F b hF r cU (by omega) hr0 p
    blocks hblocksn s1 hs1len
  obtain ⟨z1, hsq, hsqv⟩ := squeeze_loop_eq inst comps F b hF r d hrb hb (d.val / r.val) s2
    (Aeneas.Std.alloc.vec.Vec.new Bool) habslen
    (by
      simp only [List.length_nil, Nat.zero_add]
      have h0 : r.val * (d.val / r.val) + d.val % r.val = d.val := Nat.div_add_mod _ _
      have hcomm : d.val / r.val * r.val = r.val * (d.val / r.val) := Nat.mul_comm _ _
      have h1 : d.val / r.val * r.val + d.val % r.val = d.val := by omega
      have h2 : d.val % r.val < r.val := Nat.mod_lt _ hr0
      have : (d.val / r.val + 1) * r.val = d.val / r.val * r.val + r.val := by ring
      omega)
    (by
      simp only [List.length_nil, Nat.zero_add]
      have h1 : d.val / r.val * r.val ≤ d.val := Nat.div_mul_le_self _ _
      have : (d.val / r.val + 1) * r.val = d.val / r.val * r.val + r.val := by ring
      scalar_tac)
  -- the squeeze really produced `d` bits, so the final truncation is in range
  have hz1len : d.val ≤ z1.val.length := by
    rw [hsqv]
    refine squeezeFrom_len F hFlen r.val d.val hr0 hrb _ s2.val [] habslen ?_
    have h0 : r.val * (d.val / r.val) + d.val % r.val = d.val := Nat.div_add_mod _ _
    have hcomm : d.val / r.val * r.val = r.val * (d.val / r.val) := Nat.mul_comm _ _
    have h1 : d.val / r.val * r.val + d.val % r.val = d.val := by omega
    have h2 : d.val % r.val < r.val := Nat.mod_lt _ hr0
    have : (d.val / r.val + 1) * r.val = d.val / r.val * r.val + r.val := by ring
    simp
    omega
  obtain ⟨out, hout, houtv⟩ := trunc_eq z1 d hz1len
  refine ⟨out, ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.sponge.Sponge.apply
    have hp' : hacspec_sha3_pedantic.bits.concat n ⟨v.val, v.property⟩ = ok p := hp
    rw [slice_len_eq, bind_tc_ok, hv, bind_tc_ok, vec_deref_eq, bind_tc_ok, hp', bind_tc_ok,
      vec_len_eq, bind_tc_ok, hblocks, bind_tc_ok, hB, bind_tc_ok, hc, bind_tc_ok,
      hs1, bind_tc_ok]
    rw [habs, bind_tc_ok, vec_new_eq]
    show (do
        let z1 ← hacspec_sha3_pedantic.sponge.Sponge.apply_loop1 inst ⟨comps, r⟩ d comps s2
          (Aeneas.Std.alloc.vec.Vec.new Bool)
        hacspec_sha3_pedantic.bits.trunc ⟨z1.val, z1.property⟩ d) = ok out
    rw [hsq, bind_tc_ok]
    exact hout
  · rw [houtv, hsqv, habsv, hs1v, hcv, hbU, hpv']
    simp only [squeezeAll, hblocksv]
    simp only [hplen]
    simp

end Sponge

-- Pinned by `#guard_msgs`: the build fails if this comes to depend on any axiom
-- beyond Lean's standard three.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.sponge_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sponge_eq

end LibcruxIotSha3.Composition.Pedantic
