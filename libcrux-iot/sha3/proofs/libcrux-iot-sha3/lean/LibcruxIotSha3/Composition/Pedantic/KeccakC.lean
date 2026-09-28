import LibcruxIotSha3.Composition.Pedantic.Sponge
import LibcruxIotSha3.Composition.Pedantic.KeccakP
/-!
# `KECCAK[c]` (FIPS 202, Sec. 5.2)

`KECCAK[c](N, d) = SPONGE[Keccak-p[1600, 24], pad10*1, 1600 - c](N, d)`.  Both
of the sponge's abstract members are discharged here: the permutation is the one
`Composition/Pedantic/KeccakP` pins down, and the padding is `pad10*1`.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-- A bit string read as a state array. -/
def bitsOfList (s : List Bool) : Nat → Nat → Nat → Bool := fun x y z => s[bitPos x y z]!

theorem bitsOf_eq (s : Slice Bool) : bitsOf s = bitsOfList s.val := rfl

/-- `Keccak-p[1600, 24]` as a function on bit strings. -/
def keccakF (s : List Bool) : List Bool :=
  (List.range 1600).map (fun p =>
    roundsFrom (bitsOfList s) 0 24 ((p / 64) % 5) (p / 320) (p % 64))

theorem keccakF_len (s : List Bool) : (keccakF s).length = 1600 := by
  simp [keccakF]

/-- The extracted permutation is `keccakF`. -/
theorem keccak_p_1600_eq (s : Slice Bool) (hs : s.val.length = 1600) :
    ∃ out : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.keccak_p.keccak_p 64#usize s 24#usize = ok out ∧
      out.val = keccakF s.val := by
  obtain ⟨out, hout, hlen, hbits⟩ := keccak_p_eq s hs 24#usize (by simp) (by simp)
  refine ⟨out, hout, ?_⟩
  apply List.ext_getElem (by rw [hlen, keccakF_len])
  intro p h1 h2
  rw [hlen] at h1
  have hp := hbits p h1
  rw [getElem!_pos out.val p (by omega)] at hp
  rw [hp, bitsOf_eq]
  simp only [keccakF, List.getElem_map, List.getElem_range]
  norm_num

/-- The sponge's two abstract members, for `KECCAK[c]`. -/
theorem keccak1600_perm :
    PermSpec hacspec_sha3_pedantic.sponge.Keccak1600.Insts.Hacspec_sha3_pedanticSpongeComponents
      () keccakF 1600 := by
  intro s hs
  obtain ⟨out, hout, houtv⟩ := keccak_p_1600_eq s hs
  exact ⟨out, hout, houtv, keccakF_len s.val⟩

theorem keccak1600_pad :
    PadSpec hacspec_sha3_pedantic.sponge.Keccak1600.Insts.Hacspec_sha3_pedanticSpongeComponents
      () := by
  intro r m hr0
  exact pad10_star_1_eq r m hr0


/-- `KECCAK[c](N, d)` (FIPS 202, Sec. 5.2).

    `N` is an arbitrary-length bit string and `d` a `nat::Nat`: nothing here is
    bounded but the capacity, which Sec. 5.2 bounds itself. -/
theorem keccak_c_eq (c : Std.Usize) (hc0 : 0 < c.val) (hc : c.val < 1600)
    (n : hacspec_sha3_pedantic.bits.BitStr) (d : Nat) :
    ∃ out : hacspec_sha3_pedantic.bits.BitStr,
      hacspec_sha3_pedantic.sponge.keccak_c c n d = ok out ∧
      out =
        (squeezeAll keccakF (1600 - c.val) d
          (absorbFrom keccakF (1600 - c.val) c.val
            (n ++ padBits (1600 - c.val) n.length) (List.replicate 1600 false) 0
            ((n ++ padBits (1600 - c.val) n.length).length / (1600 - c.val)))).take
          d := by
  have hB : (hacspec_sha3_pedantic.sponge.B).val = 1600 := by
    simp [hacspec_sha3_pedantic.sponge.B]
  obtain ⟨rU, hrU, hrUv⟩ := usize_sub_eq hacspec_sha3_pedantic.sponge.B c (by omega)
  have hrUn : rU.val = 1600 - c.val := by rw [hrUv, hB]
  -- the rate crosses to `nat::Nat`, where the bit lengths live
  have hfrom : hacspec_sha3_pedantic.nat.Nat.from_usize rU = ok rU.val := rfl
  -- `b` travels with `f`, as Sec. 4 says it does.
  have hBok :
      (hacspec_sha3_pedantic.sponge.Keccak1600.Insts.Hacspec_sha3_pedanticSpongeComponents).B
        = ok hacspec_sha3_pedantic.sponge.B := by
    unfold hacspec_sha3_pedantic.sponge.Keccak1600.Insts.Hacspec_sha3_pedanticSpongeComponents
      hacspec_sha3_pedantic.sponge.Keccak1600.Insts.Hacspec_sha3_pedanticSpongeComponents.B
    rfl
  obtain ⟨out, hout, houtv⟩ :=
    sponge_eq hacspec_sha3_pedantic.sponge.Keccak1600.Insts.Hacspec_sha3_pedanticSpongeComponents
      () keccakF 1600 keccak1600_perm keccak1600_pad hacspec_sha3_pedantic.sponge.B rU.val d
      hBok hB (by omega) (by omega) (by omega) n
  refine ⟨out, ?_, ?_⟩
  · -- `SPONGE[f, pad, r]` is fixed by `Sponge::new`, which checks Sec. 4's
    -- `0 < r < b` before the construction exists.
    have hnew : hacspec_sha3_pedantic.sponge.Sponge.new
        hacspec_sha3_pedantic.sponge.Keccak1600.Insts.Hacspec_sha3_pedanticSpongeComponents ()
        rU.val = ok ⟨(), rU.val⟩ := by
      unfold hacspec_sha3_pedantic.sponge.Sponge.new
        hacspec_sha3_pedantic.nat.Nat.new
        hacspec_sha3_pedantic.nat.Nat.from_usize
        hacspec_sha3_pedantic.nat.Nat.Insts.CoreCmpPartialOrdNat.gt
        hacspec_sha3_pedantic.nat.Nat.Insts.CoreCmpPartialOrdNat.lt
        Aeneas.Std.massert
      have h0 : ((0#u64 : Std.U64).val) = 0 := by simp
      -- the instance's `B` is `sponge.B` by definition; `Sponge::new` compares
      -- the rate against it directly
      have hBc :
          (hacspec_sha3_pedantic.sponge.Keccak1600.Insts.Hacspec_sha3_pedanticSpongeComponents.B).val
            = 1600 := by
        unfold hacspec_sha3_pedantic.sponge.Keccak1600.Insts.Hacspec_sha3_pedanticSpongeComponents.B
        exact hB
      have hc1 : (0 : Nat) < rU.val := by omega
      have hc2 :
          rU.val
            < (hacspec_sha3_pedantic.sponge.Keccak1600.Insts.Hacspec_sha3_pedanticSpongeComponents.B).val := by
        rw [hBc]; omega
      simp only [bind_tc_ok, decide_eq_true_eq, h0, if_pos hc1, if_pos hc2]
    unfold hacspec_sha3_pedantic.sponge.keccak_c
    rw [hrU, bind_tc_ok, hfrom, bind_tc_ok, hnew, bind_tc_ok]
    exact hout
  · rw [houtv, hrUn, show 1600 - (1600 - c.val) = c.val from by omega]

-- Pinned by `#guard_msgs`: the build fails if this comes to depend on any axiom
-- beyond Lean's standard three.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.keccak_c_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms keccak_c_eq

end LibcruxIotSha3.Composition.Pedantic
