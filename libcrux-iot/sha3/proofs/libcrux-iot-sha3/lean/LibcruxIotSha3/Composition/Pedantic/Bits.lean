import LibcruxIotSha3.Composition.Pedantic.Grid
/-!
# The state array and the bit string (FIPS 202, Sec. 3.1.2 and 3.1.3)

`Keccak-p` receives a string of `b` bits and returns one, and converts to the
state array at each end: `A[x, y, z] = S[w(5y + x) + z]`.  The spec transcribes
that as two triple loop nests, one pushing the bits out in that order
(`to_bits`) and one reading them in (`from_bits`).

Both are characterised *pointwise* -- the length of the string, plus the bit at
each position -- rather than as a closed-form list.  That is the shape the
sponge needs (it indexes into the string), and it keeps the loop invariants to
one equation about the length and one about the bits written so far.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-- The position of `A[x, y, z]` in the bit string, `w(5y + x) + z` at `w = 64`. -/
def bitPos (x y z : Nat) : Nat := 64 * (5 * y + x) + z

/-- Every bit of `s` so far is the state array's, at the position it sits in. -/
def BitsPrefix (A : SA) (s : List Bool) : Prop :=
  ∀ p < s.length, s[p]! = bitAt A ((p / 64) % 5) (p / 320) (p % 64)

theorem bitsPrefix_push (A : SA) (s : List Bool) (x y z : Nat)
    (hx : x < 5) (_hy : y < 5) (hz : z < 64)
    (hlen : s.length = bitPos x y z) (h : BitsPrefix A s) :
    BitsPrefix A (s ++ [bitAt A x y z]) := by
  intro p hp
  simp only [List.length_append, List.length_cons, List.length_nil] at hp
  by_cases hlt : p < s.length
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hlt,
      ← List.getElem!_eq_getElem?_getD]
    exact h p hlt
  · have hpe : p = s.length := by omega
    subst hpe
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    congr 1
    · simp only [hlen, bitPos]; omega
    · simp only [hlen, bitPos]; omega
    · simp only [hlen, bitPos]; omega

/-! ### `to_bits` -/

theorem to_bits_zloop (A : SA) (s : alloc.vec.Vec Bool) (x y : Std.Usize)
    (hx : x.val < 5) (hy : y.val < 5)
    (hlen : s.val.length = bitPos x.val y.val 0) (hpre : BitsPrefix A s.val) :
    ∃ s' : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.state_array.StateArray.to_bits_loop0_loop0_loop0
          { start := 0#usize, «end» := 64#usize } A s y x = ok (A, s') ∧
      s'.val.length = bitPos x.val y.val 64 ∧ BitsPrefix A s'.val := by
  have h := loop_range_eq_inv_usize (β := alloc.vec.Vec Bool) (γ := SA × alloc.vec.Vec Bool)
    (fun p => hacspec_sha3_pedantic.state_array.StateArray.to_bits_loop0_loop0_loop0.body
      A y x p.1 p.2)
    64#usize
    (fun zU acc => acc.val.length = bitPos x.val y.val zU.val ∧ BitsPrefix A acc.val)
    (fun _ _ r => r.1 = A ∧ r.2.val.length = bitPos x.val y.val 64 ∧ BitsPrefix A r.2.val)
    ?hstep ?hdone 64 0#usize s (by simp) ⟨by simpa using hlen, hpre⟩
  case hstep =>
    rintro i acc hi ⟨hlen', hpre'⟩
    have hi' : i.val < 64 := by simpa using hi
    have hsmall : acc.val.length < Std.Usize.max := by
      rw [hlen']
      simp only [bitPos]
      scalar_tac
    obtain ⟨t, ht, hnext⟩ := range_next_lt i 64#usize (by simpa using hi)
    refine ⟨t, ⟨acc.val ++ [bitAt A x.val y.val i.val], by simp; scalar_tac⟩, ht, ⟨?_, ?_⟩, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil, hlen', bitPos, ht]
      omega
    · exact bitsPrefix_push A acc.val x.val y.val i.val hx hy hi' hlen' hpre'
    · unfold hacspec_sha3_pedantic.state_array.StateArray.to_bits_loop0_loop0_loop0.body
      rw [hnext]
      simp [index_usize_eq, hx, hy, hi', bitAt, vec_push_eq acc _ hsmall]
    · exact fun r hr => hr
  case hdone =>
    rintro acc ⟨hlen', hpre'⟩
    refine ⟨(A, acc), ?_, rfl, ?_, hpre'⟩
    · unfold hacspec_sha3_pedantic.state_array.StateArray.to_bits_loop0_loop0_loop0.body
      rw [range_next_ge 64#usize 64#usize (le_refl _)]
      simp
    · rw [hlen']
      simp
  obtain ⟨r, hr, hr1, hr2, hr3⟩ := h
  refine ⟨r.2, ?_, hr2, hr3⟩
  unfold hacspec_sha3_pedantic.state_array.StateArray.to_bits_loop0_loop0_loop0
  rw [show ((A, r.2) : SA × alloc.vec.Vec Bool) = r by rw [← hr1]]
  exact hr


theorem to_bits_xloop (A : SA) (s : alloc.vec.Vec Bool) (y : Std.Usize) (hy : y.val < 5)
    (hlen : s.val.length = 320 * y.val) (hpre : BitsPrefix A s.val) :
    ∃ s' : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.state_array.StateArray.to_bits_loop0_loop0
          { start := 0#usize, «end» := 5#usize } A s y = ok (A, s') ∧
      s'.val.length = 320 * (y.val + 1) ∧ BitsPrefix A s'.val := by
  have h := loop_range_eq_inv_usize (β := SA × alloc.vec.Vec Bool)
    (γ := SA × alloc.vec.Vec Bool)
    (fun p => hacspec_sha3_pedantic.state_array.StateArray.to_bits_loop0_loop0.body
      y p.1 p.2.1 p.2.2)
    5#usize
    (fun xU acc => acc.1 = A ∧ acc.2.val.length = bitPos xU.val y.val 0 ∧
      BitsPrefix A acc.2.val)
    (fun _ _ r => r.1 = A ∧ r.2.val.length = 320 * (y.val + 1) ∧ BitsPrefix A r.2.val)
    ?hstep ?hdone 5 0#usize (A, s) (by simp) ⟨rfl, by simp only [bitPos]; simp; omega, hpre⟩
  case hstep =>
    rintro i acc hi ⟨hA, hlen', hpre'⟩
    have hi' : i.val < 5 := by simpa using hi
    obtain ⟨t, ht, hnext⟩ := range_next_lt i 5#usize (by simpa using hi)
    obtain ⟨s', hloop, hlen'', hpre''⟩ := to_bits_zloop A acc.2 i y hi' hy hlen' hpre'
    refine ⟨t, (A, s'), ht, ⟨rfl, ?_, hpre''⟩, ?_, fun r hr => hr⟩
    · rw [hlen'']
      simp only [bitPos, ht]
      omega
    · unfold hacspec_sha3_pedantic.state_array.StateArray.to_bits_loop0_loop0.body
      rw [hnext, hA]
      simp [hloop]
  case hdone =>
    rintro acc ⟨hA, hlen', hpre'⟩
    refine ⟨(acc.1, acc.2), ?_, hA, ?_, hpre'⟩
    · unfold hacspec_sha3_pedantic.state_array.StateArray.to_bits_loop0_loop0.body
      rw [range_next_ge 5#usize 5#usize (le_refl _)]
      simp
    · rw [hlen']
      have h5 : (5#usize : Std.Usize).val = 5 := by simp
      simp only [bitPos, h5]
      omega
  obtain ⟨r, hr, hr1, hr2, hr3⟩ := h
  refine ⟨r.2, ?_, hr2, hr3⟩
  unfold hacspec_sha3_pedantic.state_array.StateArray.to_bits_loop0_loop0
  rw [show ((A, r.2) : SA × alloc.vec.Vec Bool) = r by rw [← hr1]]
  exact hr

theorem to_bits_yloop (A : SA) (s : alloc.vec.Vec Bool)
    (hlen : s.val.length = 0) (hpre : BitsPrefix A s.val) :
    ∃ s' : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.state_array.StateArray.to_bits_loop0
          { start := 0#usize, «end» := 5#usize } A s = ok s' ∧
      s'.val.length = 1600 ∧ BitsPrefix A s'.val := by
  have h := loop_range_eq_inv_usize (β := SA × alloc.vec.Vec Bool) (γ := alloc.vec.Vec Bool)
    (fun p => hacspec_sha3_pedantic.state_array.StateArray.to_bits_loop0.body p.1 p.2.1 p.2.2)
    5#usize
    (fun yU acc => acc.1 = A ∧ acc.2.val.length = 320 * yU.val ∧ BitsPrefix A acc.2.val)
    (fun _ _ r => r.val.length = 1600 ∧ BitsPrefix A r.val)
    ?hstep ?hdone 5 0#usize (A, s) (by simp) ⟨rfl, by simpa using hlen, hpre⟩
  case hstep =>
    rintro i acc hi ⟨hA, hlen', hpre'⟩
    have hi' : i.val < 5 := by simpa using hi
    obtain ⟨t, ht, hnext⟩ := range_next_lt i 5#usize (by simpa using hi)
    obtain ⟨s', hloop, hlen'', hpre''⟩ := to_bits_xloop A acc.2 i hi' hlen' hpre'
    refine ⟨t, (A, s'), ht, ⟨rfl, ?_, hpre''⟩, ?_, fun r hr => hr⟩
    · rw [hlen'', ht]
    · unfold hacspec_sha3_pedantic.state_array.StateArray.to_bits_loop0.body
      rw [hnext, hA]
      simp [hloop]
  case hdone =>
    rintro acc ⟨hA, hlen', hpre'⟩
    refine ⟨acc.2, ?_, ?_, hpre'⟩
    · unfold hacspec_sha3_pedantic.state_array.StateArray.to_bits_loop0.body
      rw [range_next_ge 5#usize 5#usize (le_refl _)]
      simp
    · rw [hlen']
      simp
  obtain ⟨r, hr, hr1, hr2⟩ := h
  refine ⟨r, ?_, hr1, hr2⟩
  unfold hacspec_sha3_pedantic.state_array.StateArray.to_bits_loop0
  exact hr

/-- FIPS 202, Sec. 3.1.3: the state array laid out as a bit string. -/
theorem to_bits_eq (A : SA) :
    ∃ s : alloc.vec.Vec Bool,
      hacspec_sha3_pedantic.state_array.StateArray.to_bits A = ok s ∧
      s.val.length = 1600 ∧
      ∀ p < 1600, s.val[p]! = bitAt A ((p / 64) % 5) (p / 320) (p % 64) := by
  have hcap : alloc.vec.Vec.with_capacity Bool 1600#usize
      = ok (⟨[], by simp⟩ : alloc.vec.Vec Bool) := rfl
  obtain ⟨s', hloop, hlen, hpre⟩ :=
    to_bits_yloop A ⟨[], by simp⟩ (by simp) (by
      intro p hp
      simp at hp)
  obtain ⟨b, hb, hbv⟩ := usize_mul_eq 25#usize 64#usize (by scalar_tac)
  refine ⟨s', ?_, hlen, fun p hp => hpre p (by omega)⟩
  unfold hacspec_sha3_pedantic.state_array.StateArray.to_bits
    hacspec_sha3_pedantic.state_array.StateArray.B
  rw [hb]
  simp only [bind_tc_ok]
  rw [show b = 1600#usize from
      (Std.UScalar.eq_equiv b 1600#usize).mpr (by rw [hbv]; simp), hcap]
  exact hloop


/-! ### `from_bits` -/

theorem from_bits_body_cont (s : Slice Bool) (hslen : s.val.length = 1600)
    (out : SA) (x y z : Std.Usize) (hx : x.val < 5) (hy : y.val < 5) (hz : z.val < 64) :
    ∃ t : Std.Usize, t.val = z.val + 1 ∧
      hacspec_sha3_pedantic.state_array.StateArray.from_bits_loop0_loop0_loop0.body s x y
          { start := z, «end» := 64#usize } out
        = ok (.cont ({ start := t, «end» := 64#usize },
            setBit out x y z s.val[bitPos x.val y.val z.val]!)) := by
  obtain ⟨t, ht, hnext⟩ := range_next_lt z 64#usize (by simpa using hz)
  refine ⟨t, ht, ?_⟩
  unfold hacspec_sha3_pedantic.state_array.StateArray.from_bits_loop0_loop0_loop0.body
  rw [hnext]
  obtain ⟨p1, hp1, hp1v⟩ := usize_mul_eq 5#usize y (by scalar_tac)
  obtain ⟨p2, hp2, hp2v⟩ := usize_add_eq p1 x (by scalar_tac)
  obtain ⟨p3, hp3, hp3v⟩ := usize_mul_eq 64#usize p2 (by
    have : p2.val < 25 := by simp [hp2v, hp1v]; omega
    scalar_tac)
  obtain ⟨p4, hp4, hp4v⟩ := usize_add_eq p3 z (by
    have h2 : p2.val < 25 := by simp [hp2v, hp1v]; omega
    have : p3.val < 1600 := by simp [hp3v]; omega
    scalar_tac)
  have hp4n : p4.val = bitPos x.val y.val z.val := by
    simp only [bitPos, hp4v, hp3v, hp2v, hp1v]
    simp
  have hp4lt : p4.val < s.val.length := by
    rw [hp4n, hslen]
    simp only [bitPos]
    omega
  simp [hp1, hp2, hp3, hp4, slice_index_usize_eq _ _ hp4lt, hp4n,
    index_usize_eq, array_update_eq, Std.Array.index_mut_usize, hx, hy, hz, setBit]


theorem from_bits_body_done (s : Slice Bool) (out : SA) (x y : Std.Usize) :
    hacspec_sha3_pedantic.state_array.StateArray.from_bits_loop0_loop0_loop0.body s x y
      { start := 64#usize, «end» := 64#usize } out = ok (.done out) := by
  unfold hacspec_sha3_pedantic.state_array.StateArray.from_bits_loop0_loop0_loop0.body
  rw [range_next_ge 64#usize 64#usize (le_refl _)]
  simp

theorem from_bits_zloop (s : Slice Bool) (hslen : s.val.length = 1600) (out : SA)
    (x y : Std.Usize) (hx : x.val < 5) (hy : y.val < 5) :
    ∃ out' : SA,
      hacspec_sha3_pedantic.state_array.StateArray.from_bits_loop0_loop0_loop0
          { start := 0#usize, «end» := 64#usize } s out x y = ok out' ∧
      ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
        bitAt out' x' y' z'
          = if x' = x.val ∧ y' = y.val then s.val[bitPos x' y' z']!
            else bitAt out x' y' z' := by
  have h := loop_range_eq (β := SA) (γ := SA)
    (fun p => hacspec_sha3_pedantic.state_array.StateArray.from_bits_loop0_loop0_loop0.body
      s x y p.1 p.2)
    64#usize
    (fun zU acc r => ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
      bitAt r x' y' z'
        = if x' = x.val ∧ y' = y.val ∧ zU.val ≤ z' then s.val[bitPos x' y' z']!
          else bitAt acc x' y' z')
    ?hstep ?hdone 64 0#usize out (by simp)
  case hstep =>
    intro i acc hi
    have hi' : i.val < 64 := by simpa using hi
    obtain ⟨t, ht, hbody⟩ := from_bits_body_cont s hslen acc x y i hx hy hi'
    refine ⟨t, setBit acc x y i s.val[bitPos x.val y.val i.val]!, ht, hbody, ?_⟩
    intro r hr x' hx' y' hy' z' hz'
    rw [hr x' hx' y' hy' z' hz',
      bitAt_setBit acc x y i _ x' y' z' hx hy hi' hx' hy' hz']
    have htv : t.val = i.val + 1 := ht
    split_ifs with h1 h2 h3 <;>
      first | rfl | (exfalso; omega) | (congr 2 <;> omega)
  case hdone =>
    refine fun acc => ⟨acc, from_bits_body_done s acc x y, fun x' _ y' _ z' hz' => ?_⟩
    have hne : ¬ (x' = x.val ∧ y' = y.val ∧ (64#usize).val ≤ z') := by
      simp only [not_and]
      intro _ _
      simp
      omega
    simp only [hne, if_false]
  obtain ⟨r, hr, hbits⟩ := h
  refine ⟨r, ?_, fun x' hx' y' hy' z' hz' => ?_⟩
  · unfold hacspec_sha3_pedantic.state_array.StateArray.from_bits_loop0_loop0_loop0
    exact hr
  · rw [hbits x' hx' y' hy' z' hz']
    simp

theorem from_bits_yloop (s : Slice Bool) (hslen : s.val.length = 1600) (out : SA)
    (x : Std.Usize) (hx : x.val < 5) :
    ∃ out' : SA,
      hacspec_sha3_pedantic.state_array.StateArray.from_bits_loop0_loop0
          { start := 0#usize, «end» := 5#usize } s out x = ok out' ∧
      ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
        bitAt out' x' y' z'
          = if x' = x.val then s.val[bitPos x' y' z']! else bitAt out x' y' z' := by
  have h := loop_range_eq (β := SA) (γ := SA)
    (fun p => hacspec_sha3_pedantic.state_array.StateArray.from_bits_loop0_loop0.body
      s x p.1 p.2)
    5#usize
    (fun yU acc r => ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
      bitAt r x' y' z'
        = if x' = x.val ∧ yU.val ≤ y' then s.val[bitPos x' y' z']! else bitAt acc x' y' z')
    ?hstep ?hdone 5 0#usize out (by simp)
  case hstep =>
    intro i acc hi
    have hi' : i.val < 5 := by simpa using hi
    obtain ⟨t, ht, hnext⟩ := range_next_lt i 5#usize (by simpa using hi)
    obtain ⟨out', hloop, hbits⟩ := from_bits_zloop s hslen acc x i hx hi'
    refine ⟨t, out', ht, ?_, ?_⟩
    · unfold hacspec_sha3_pedantic.state_array.StateArray.from_bits_loop0_loop0.body
      rw [hnext]
      simp [hloop]
    · intro r hr x' hx' y' hy' z' hz'
      rw [hr x' hx' y' hy' z' hz', hbits x' hx' y' hy' z' hz']
      have htv : t.val = i.val + 1 := ht
      split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega)
  case hdone =>
    refine fun acc => ⟨acc, ?_, fun x' _ y' hy' z' _ => ?_⟩
    · unfold hacspec_sha3_pedantic.state_array.StateArray.from_bits_loop0_loop0.body
      rw [range_next_ge 5#usize 5#usize (le_refl _)]
      simp
    · have hne : ¬ (x' = x.val ∧ (5#usize).val ≤ y') := by
        simp only [not_and]
        intro _
        simp
        omega
      simp only [hne, if_false]
  obtain ⟨r, hr, hbits⟩ := h
  refine ⟨r, ?_, fun x' hx' y' hy' z' hz' => ?_⟩
  · unfold hacspec_sha3_pedantic.state_array.StateArray.from_bits_loop0_loop0
    exact hr
  · rw [hbits x' hx' y' hy' z' hz']
    simp

theorem from_bits_xloop (s : Slice Bool) (hslen : s.val.length = 1600) (out : SA) :
    ∃ out' : SA,
      hacspec_sha3_pedantic.state_array.StateArray.from_bits_loop0
          { start := 0#usize, «end» := 5#usize } s out = ok out' ∧
      ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
        bitAt out' x' y' z' = s.val[bitPos x' y' z']! := by
  have h := loop_range_eq (β := SA) (γ := SA)
    (fun p => hacspec_sha3_pedantic.state_array.StateArray.from_bits_loop0.body s p.1 p.2)
    5#usize
    (fun xU acc r => ∀ x' < 5, ∀ y' < 5, ∀ z' < 64,
      bitAt r x' y' z'
        = if xU.val ≤ x' then s.val[bitPos x' y' z']! else bitAt acc x' y' z')
    ?hstep ?hdone 5 0#usize out (by simp)
  case hstep =>
    intro i acc hi
    have hi' : i.val < 5 := by simpa using hi
    obtain ⟨t, ht, hnext⟩ := range_next_lt i 5#usize (by simpa using hi)
    obtain ⟨out', hloop, hbits⟩ := from_bits_yloop s hslen acc i hi'
    refine ⟨t, out', ht, ?_, ?_⟩
    · unfold hacspec_sha3_pedantic.state_array.StateArray.from_bits_loop0.body
      rw [hnext]
      simp [hloop]
    · intro r hr x' hx' y' hy' z' hz'
      rw [hr x' hx' y' hy' z' hz', hbits x' hx' y' hy' z' hz']
      have htv : t.val = i.val + 1 := ht
      split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
  case hdone =>
    refine fun acc => ⟨acc, ?_, fun x' hx' y' _ z' _ => ?_⟩
    · unfold hacspec_sha3_pedantic.state_array.StateArray.from_bits_loop0.body
      rw [range_next_ge 5#usize 5#usize (le_refl _)]
      simp
    · have hne : ¬ ((5#usize).val ≤ x') := by simp; omega
      simp only [hne, if_false]
  obtain ⟨r, hr, hbits⟩ := h
  refine ⟨r, ?_, fun x' hx' y' hy' z' hz' => ?_⟩
  · unfold hacspec_sha3_pedantic.state_array.StateArray.from_bits_loop0
    exact hr
  · rw [hbits x' hx' y' hy' z' hz', if_pos (by simp)]

/-- FIPS 202, Sec. 3.1.2: the bit string read into a state array. -/
theorem from_bits_eq (s : Slice Bool) (hslen : s.val.length = 1600) :
    ∃ A : SA,
      hacspec_sha3_pedantic.state_array.StateArray.from_bits 64#usize s = ok A ∧
      ∀ x < 5, ∀ y < 5, ∀ z < 64, bitAt A x y z = s.val[bitPos x y z]! := by
  obtain ⟨A, hloop, hbits⟩ := from_bits_xloop s hslen (mkSA fun _ _ _ => false)
  refine ⟨A, ?_, hbits⟩
  unfold hacspec_sha3_pedantic.state_array.StateArray.from_bits
  obtain ⟨b, hb, hbv⟩ := usize_mul_eq 25#usize 64#usize (by scalar_tac)
  have hlen : core.slice.Slice.len s = ok (Std.Usize.ofNatCore s.val.length (by scalar_tac)) := rfl
  simp only [hlen, bind_tc_ok, hb, stateArray_zero_eq]
  rw [show (Std.Usize.ofNatCore s.val.length (by scalar_tac) : Std.Usize) = b from
    (Std.UScalar.eq_equiv _ b).mpr (by simp [hbv, hslen])]
  simp only [massert]
  exact hloop

end LibcruxIotSha3.Composition.Pedantic
