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
  intro r m hr0 hr
  exact pad10_star_1_eq r m hr0 hr


/-- `KECCAK[c](N, d)` (FIPS 202, Sec. 5.2).

    `N` is an arbitrary-length bit string; what is bounded is what a `u64` has
    to hold, not what the target's word is. -/
theorem keccak_c_eq (c : Std.Usize) (hc0 : 0 < c.val) (hc : c.val < 1600)
    (n : hacspec_sha3_pedantic.bits.BitStr) (hn : n.length + 1602 < 2 ^ 64)
    (d : Std.U64) (hdb : d.val + 1600 < 2 ^ 64) :
    ∃ out : hacspec_sha3_pedantic.bits.BitStr,
      hacspec_sha3_pedantic.sponge.keccak_c c n d = ok out ∧
      out =
        (squeezeAll keccakF (1600 - c.val) d.val
          (absorbFrom keccakF (1600 - c.val) c.val
            (n ++ padBits (1600 - c.val) n.length) (List.replicate 1600 false) 0
            ((n ++ padBits (1600 - c.val) n.length).length / (1600 - c.val)))).take
          d.val := by
  have hB : (hacspec_sha3_pedantic.sponge.B).val = 1600 := by
    simp [hacspec_sha3_pedantic.sponge.B]
  obtain ⟨rU, hrU, hrUv⟩ := usize_sub_eq hacspec_sha3_pedantic.sponge.B c (by omega)
  have hrUn : rU.val = 1600 - c.val := by rw [hrUv, hB]
  -- the rate crosses to `u64`, where the bit lengths live
  set r : Std.U64 := Std.UScalar.cast Std.UScalarTy.U64 rU with hrdef
  have hrn : r.val = 1600 - c.val := by
    rw [hrdef, Std.UScalar.cast_val_eq, hrUn]
    exact Nat.mod_eq_of_lt (by simp only [Std.UScalarTy.U64_numBits_eq]; omega)
  have hliftcast : (Std.lift (Std.UScalar.cast Std.UScalarTy.U64 rU) : RustM Std.U64)
      = ok r := rfl
  -- `b` travels with `f`, as Sec. 4 says it does.
  have hBok :
      (hacspec_sha3_pedantic.sponge.Keccak1600.Insts.Hacspec_sha3_pedanticSpongeComponents).B
        = ok hacspec_sha3_pedantic.sponge.B := by
    unfold hacspec_sha3_pedantic.sponge.Keccak1600.Insts.Hacspec_sha3_pedanticSpongeComponents
      hacspec_sha3_pedantic.sponge.Keccak1600.Insts.Hacspec_sha3_pedanticSpongeComponents.B
    rfl
  obtain ⟨out, hout, houtv⟩ :=
    sponge_eq hacspec_sha3_pedantic.sponge.Keccak1600.Insts.Hacspec_sha3_pedanticSpongeComponents
      () keccakF 1600 keccak1600_perm keccak1600_pad hacspec_sha3_pedantic.sponge.B r d hBok hB
      (by omega) (by omega) (by omega) n (by omega) (by omega)
  refine ⟨out, ?_, ?_⟩
  · -- `SPONGE[f, pad, r]` is fixed by `Sponge::new`, which checks Sec. 4's
    -- `0 < r < b` before the construction exists.
    have hnew : hacspec_sha3_pedantic.sponge.Sponge.new
        hacspec_sha3_pedantic.sponge.Keccak1600.Insts.Hacspec_sha3_pedanticSpongeComponents () r
        = ok ⟨(), r⟩ := by
      unfold hacspec_sha3_pedantic.sponge.Sponge.new
      have h0 : (massert (r > 0#u64) : RustM Unit) = .ok () := by
        unfold Aeneas.Std.massert
        refine if_pos ((Std.UScalar.lt_equiv _ _).mpr ?_)
        show (0#u64 : Std.U64).val < r.val
        rw [hrn]; simpa using (by omega : 0 < 1600 - c.val)
      have hcastB : (Std.lift (Std.UScalar.cast Std.UScalarTy.U64 hacspec_sha3_pedantic.sponge.B)
          : RustM Std.U64) = ok (Std.UScalar.cast Std.UScalarTy.U64 hacspec_sha3_pedantic.sponge.B) :=
        rfl
      have hBval : (Std.UScalar.cast Std.UScalarTy.U64 hacspec_sha3_pedantic.sponge.B).val
          = 1600 := by
        rw [Std.UScalar.cast_val_eq, hB]
        exact Nat.mod_eq_of_lt (by simp only [Std.UScalarTy.U64_numBits_eq]; omega)
      have hlt : (massert (r < Std.UScalar.cast Std.UScalarTy.U64 hacspec_sha3_pedantic.sponge.B)
          : RustM Unit) = .ok () := by
        unfold Aeneas.Std.massert
        refine if_pos ((Std.UScalar.lt_equiv _ _).mpr ?_)
        rw [hrn, hBval]; omega
      rw [h0, bind_tc_ok, hBok, bind_tc_ok, hcastB, bind_tc_ok, hlt, bind_tc_ok]
    unfold hacspec_sha3_pedantic.sponge.keccak_c
    rw [hrU, bind_tc_ok, hliftcast, bind_tc_ok, hnew, bind_tc_ok]
    exact hout
  · rw [houtv, hrn, show 1600 - (1600 - c.val) = c.val from by omega]

-- Pinned by `#guard_msgs`: the build fails if this comes to depend on any axiom
-- beyond Lean's standard three.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.keccak_c_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms keccak_c_eq

end LibcruxIotSha3.Composition.Pedantic
