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

/-- Squeezing, with fuel: emit `r` bits, stop once `d` are out (Algorithm 8,
    steps 8-10). -/
def squeezeFrom (F : List Bool → List Bool) (r d : Nat) :
    Nat → List Bool → List Bool → List Bool
  | 0, _, z => z
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
      hacspec_sha3_pedantic.sponge.sponge_loop0.body inst comps r p c
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
  · unfold hacspec_sha3_pedantic.sponge.sponge_loop0.body
    rw [hnext]
    simp [hi1, hi2, hi3, vec_index_range_eq p i1 i3 hle hub, hzs, vec_deref_eq, hblk, hxs, ho]


theorem absorb_body_done (r c : Std.Usize) (p : alloc.vec.Vec Bool)
    (blocks : Std.Usize) (s : alloc.vec.Vec Bool) :
    hacspec_sha3_pedantic.sponge.sponge_loop0.body inst comps r p c
      { start := blocks, «end» := blocks } s = ok (.done s) := by
  unfold hacspec_sha3_pedantic.sponge.sponge_loop0.body
  rw [range_next_ge blocks blocks (le_refl _)]
  simp

/-- The absorb loop of Algorithm 8, steps 5-6. -/
theorem absorb_loop_eq (hF : PermSpec inst comps F b)
    (r c : Std.Usize) (hrc : r.val + c.val = b) (hr : 0 < r.val)
    (p : alloc.vec.Vec Bool) (blocks : Std.Usize) (hblocks : blocks.val * r.val = p.val.length)
    (s : alloc.vec.Vec Bool) (hs : s.val.length = b) :
    ∃ s' : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.sponge.sponge_loop0 inst { start := 0#usize, «end» := blocks }
        comps r p c s = ok s' ∧
      s'.val = absorbFrom F r.val c.val p.val s.val 0 blocks.val := by
  have h := loop_range_eq_inv_usize (β := alloc.vec.Vec Bool) (γ := alloc.vec.Vec Bool)
    (fun q => hacspec_sha3_pedantic.sponge.sponge_loop0.body inst comps r p c q.1 q.2)
    blocks
    (fun _ acc => acc.val.length = b)
    (fun i acc r' => r'.val = absorbFrom F r.val c.val p.val acc.val i.val (blocks.val - i.val))
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
    · intro r' hr'
      rw [hr', hs', ht, show blocks.val - i.val = (blocks.val - (i.val + 1)) + 1 by omega]
      rfl
  case hdone =>
    intro acc hinv
    refine ⟨acc, absorb_body_done inst comps r c p blocks acc, ?_⟩
    rw [show blocks.val - blocks.val = 0 by omega]
    rfl
  obtain ⟨s', hloop, hval⟩ := h
  refine ⟨s', ?_, ?_⟩
  · unfold hacspec_sha3_pedantic.sponge.sponge_loop0
    exact hloop
  · rw [hval]
    simp

end Absorb

end LibcruxIotSha3.Composition.Pedantic
