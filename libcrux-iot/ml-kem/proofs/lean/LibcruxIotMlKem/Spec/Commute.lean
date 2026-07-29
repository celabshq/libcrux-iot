/-
  # `Spec/Commute.lean` — M.2 commute lemmas (Block A).

  Layer-0 scalar `Std.I16 → ZMod 3329` field-element commute lemmas.
  Each lemma consumes an impl-level "value-equation" precondition
  (already produced by L0/L1 Triples in the `Equivalence/` tree) and
  produces the matching `ZMod 3329` algebraic equation through one of
  the M.1 lane lifts `i16_to_spec_fe_{plain,mont}`.

  Port of `Hacspec_ml_kem.Commute.Chunk.fst` lines 35-680 (the
  Layer-0 / "scalar" portion of Block A); blocks B, C, D are
  deferred.

  ## Discipline

  Each lemma carries `@[scoped grind]` and lives inside the
  `libcrux_iot_ml_kem.Spec.Commute` namespace, so consumers
  enable `grind` over the commute set with
  `open libcrux_iot_ml_kem.Spec.Commute` (no global pollution).

  ## File-shape notes

  - F* uses `v r % 3329 == ... % 3329` (Int arithmetic mod q). We
    translate by stating the precondition directly as a `ZMod 3329`
    equation — the M.1 lane lifts already give us the cast.
  - F* uses `v r == v a + v b` (strict Int equality) for the strict
    `_plain`/`_mont` variants. We mirror this with `r.val = a.val + b.val`
    on `Std.I16.val : Int`.
  - In `ZMod 3329`, `mont_i16_to_spec_fe x = x.val · 169` and
    `i16_to_spec_fe_plain x = x.val`, so each F* `lemma_mod_*_distr_*`
    chain collapses to a single `rw [hr]; ring`.
-/
import LibcruxIotMlKem.Spec
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

namespace libcrux_iot_ml_kem.Spec.Commute
open CoreModels Aeneas Aeneas.Std
open libcrux_iot_ml_kem.Spec

/-! ### Local `Inhabited` instances (mirror of `Spec.lean`).

    The `PolynomialRingElement V`-and-`PortableVector` chunk types
    need an `Inhabited` instance for the `coefficients.val[i]!` /
    `elements.val[j]!` indexing patterns used by Block-C poly lemma
    statements. `Spec.lean` declares the same instances as `local`, so
    they don't propagate here; we redeclare them `local` for this file. -/

local instance instInhabitedPortableVector_bitMlKemCommute :
    Inhabited libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
  ⟨{ elements := Std.Array.make 16#usize (List.replicate 16 (0#i16 : Std.I16))
        (by simp) }⟩

local instance instInhabitedPolynomialRingElement_bitMlKemCommute
    {Vector : Type} [Inhabited Vector] :
    Inhabited (libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector) :=
  ⟨{ coefficients := Std.Array.make 16#usize (List.replicate 16 default) (by simp) }⟩

/-! ## A.1 / A.2 — pointwise addition commutes (plain and Mont). -/

/-- A.1 `lemma_add_fe_commute_plain` (F*: Chunk.fst:35). Strict
    Int-equality precondition: the impl returns the exact integer
    sum (no overflow), and the plain-domain lift respects this. -/
@[scoped grind .]
theorem lemma_add_fe_commute_plain (a b r : Std.I16)
    (hr : r.val = a.val + b.val) :
    i16_to_spec_fe_plain a + i16_to_spec_fe_plain b = i16_to_spec_fe_plain r := by
  unfold i16_to_spec_fe_plain
  rw [hr]; push_cast; ring

/-- A.2 `lemma_add_fe_commute_mont` (F*: Chunk.fst:41). Same shape
    as A.1 but lifts through `mont` (extra `· 169` factor). -/
@[scoped grind .]
theorem lemma_add_fe_commute_mont (a b r : Std.I16)
    (hr : r.val = a.val + b.val) :
    i16_to_spec_fe_mont a + i16_to_spec_fe_mont b = i16_to_spec_fe_mont r := by
  unfold i16_to_spec_fe_mont
  rw [hr]; push_cast; ring

/-! ## A.3 / A.4 — pointwise subtraction commutes. -/

/-- A.3 `lemma_sub_fe_commute_plain` (F*: Chunk.fst:48). -/
@[scoped grind .]
theorem lemma_sub_fe_commute_plain (a b r : Std.I16)
    (hr : r.val = a.val - b.val) :
    i16_to_spec_fe_plain a - i16_to_spec_fe_plain b = i16_to_spec_fe_plain r := by
  unfold i16_to_spec_fe_plain
  rw [hr]; push_cast; ring

/-- A.4 `lemma_sub_fe_commute_mont` (F*: Chunk.fst:54). -/
@[scoped grind .]
theorem lemma_sub_fe_commute_mont (a b r : Std.I16)
    (hr : r.val = a.val - b.val) :
    i16_to_spec_fe_mont a - i16_to_spec_fe_mont b = i16_to_spec_fe_mont r := by
  unfold i16_to_spec_fe_mont
  rw [hr]; push_cast; ring

/-! ## A.5 — Barrett reduction commutes (plain). -/

/-- A.5 `lemma_barrett_fe_commute` (F*: Chunk.fst:63). Barrett
    reduction preserves residue mod q, so the plain lift is identity
    on the reduced value.

    Statement uses `r = a` order (matching F*) — that is,
    `i16_to_spec_fe_plain r = i16_to_spec_fe_plain a`. -/
@[scoped grind .]
theorem lemma_barrett_fe_commute (a r : Std.I16)
    (hr : (r.val : ZMod 3329) = (a.val : ZMod 3329)) :
    i16_to_spec_fe_plain r = i16_to_spec_fe_plain a := by
  unfold i16_to_spec_fe_plain
  exact hr

/-! ## A.6 — Mont zeta cancellation (mont ↔ plain bridge). -/

/-- A.6 `lemma_mont_zeta_cancel` (F*: Chunk.fst:71). The impl stores
    zetas pre-multiplied by `R`, so the Mont lift recovers the plain
    abstract zeta when paired with a residue-equality precondition. -/
@[scoped grind .]
theorem lemma_mont_zeta_cancel (zeta_mont zeta_plain : Std.I16)
    (hr : (zeta_mont.val : ZMod 3329) * 169 = (zeta_plain.val : ZMod 3329)) :
    i16_to_spec_fe_mont zeta_mont = i16_to_spec_fe_plain zeta_plain := by
  unfold i16_to_spec_fe_mont i16_to_spec_fe_plain
  exact hr

/-! ## A.7 / A.8 — mod-aware add/sub commutes (residue precondition). -/

/-- A.7 `lemma_add_fe_commute_mont_mod` (F*: Chunk.fst:151). The
    precondition is a `ZMod 3329` equality rather than a strict Int
    sum — used by butterfly outputs whose impl post is mod q. -/
@[scoped grind .]
theorem lemma_add_fe_commute_mont_mod (a b r : Std.I16)
    (hr : (r.val : ZMod 3329) = (a.val : ZMod 3329) + (b.val : ZMod 3329)) :
    i16_to_spec_fe_mont a + i16_to_spec_fe_mont b = i16_to_spec_fe_mont r := by
  unfold i16_to_spec_fe_mont
  rw [hr]; ring

/-- A.8 `lemma_sub_fe_commute_mont_mod` (F*: Chunk.fst:159). -/
@[scoped grind .]
theorem lemma_sub_fe_commute_mont_mod (a b r : Std.I16)
    (hr : (r.val : ZMod 3329) = (a.val : ZMod 3329) - (b.val : ZMod 3329)) :
    i16_to_spec_fe_mont a - i16_to_spec_fe_mont b = i16_to_spec_fe_mont r := by
  unfold i16_to_spec_fe_mont
  rw [hr]; ring

/-! ## A.9 / A.10 — butterfly commute (plus and minus halves). -/

/-- A.9 `lemma_butterfly_fe_commute_plus` (F*: Chunk.fst:187). The
    `+` output of a `ntt_layer_*_step` butterfly: in the Mont domain,
    the impl post `result_i ≡ vec_i + vec_j · zeta · 169 (mod q)`
    collapses to the FE equation `mont_fe result_i = mont_fe vec_i +
    mont_fe zeta · mont_fe vec_j` because the Montgomery factor
    cancels exactly with the `· 169` in the residue. -/
@[scoped grind .]
theorem lemma_butterfly_fe_commute_plus
    (vec_i vec_j zeta result_i : Std.I16)
    (hr : (result_i.val : ZMod 3329) =
          (vec_i.val : ZMod 3329) +
          (vec_j.val : ZMod 3329) * (zeta.val : ZMod 3329) * 169) :
    i16_to_spec_fe_mont result_i =
      i16_to_spec_fe_mont vec_i +
      i16_to_spec_fe_mont zeta * i16_to_spec_fe_mont vec_j := by
  unfold i16_to_spec_fe_mont
  rw [hr]; ring

/-- A.10 `lemma_butterfly_fe_commute_minus` (F*: Chunk.fst:217). -/
@[scoped grind .]
theorem lemma_butterfly_fe_commute_minus
    (vec_i vec_j zeta result_j : Std.I16)
    (hr : (result_j.val : ZMod 3329) =
          (vec_i.val : ZMod 3329) -
          (vec_j.val : ZMod 3329) * (zeta.val : ZMod 3329) * 169) :
    i16_to_spec_fe_mont result_j =
      i16_to_spec_fe_mont vec_i -
      i16_to_spec_fe_mont zeta * i16_to_spec_fe_mont vec_j := by
  unfold i16_to_spec_fe_mont
  rw [hr]; ring

/-! ## A.11 — combined butterfly pair (both halves). -/

/-- A.11 `lemma_butterfly_pair_commute` (F*: Chunk.fst:234). Bundles
    A.9 and A.10 into a single ∧ — one call per butterfly pair
    instead of two. The F* version threads through `Seq.index`; we
    stay scalar at Block A and take the four `Std.I16` lanes
    directly. Block B re-introduces the array machinery. -/
@[scoped grind .]
theorem lemma_butterfly_pair_commute
    (vec_i vec_j result_i result_j zeta : Std.I16)
    (hr_i : (result_i.val : ZMod 3329) =
            (vec_i.val : ZMod 3329) +
            (vec_j.val : ZMod 3329) * (zeta.val : ZMod 3329) * 169)
    (hr_j : (result_j.val : ZMod 3329) =
            (vec_i.val : ZMod 3329) -
            (vec_j.val : ZMod 3329) * (zeta.val : ZMod 3329) * 169) :
    i16_to_spec_fe_mont result_i =
      i16_to_spec_fe_mont vec_i +
      i16_to_spec_fe_mont zeta * i16_to_spec_fe_mont vec_j
    ∧
    i16_to_spec_fe_mont result_j =
      i16_to_spec_fe_mont vec_i -
      i16_to_spec_fe_mont zeta * i16_to_spec_fe_mont vec_j := by
  exact ⟨lemma_butterfly_fe_commute_plus vec_i vec_j zeta result_i hr_i,
         lemma_butterfly_fe_commute_minus vec_i vec_j zeta result_j hr_j⟩

/-! ## A.12 — inverse butterfly multiply-diff. -/

/-- A.12 `lemma_inv_butterfly_fe_commute_mul_diff` (F*: Chunk.fst:279).
    The `j` output of the Gentleman–Sande inverse butterfly. -/
@[scoped grind .]
theorem lemma_inv_butterfly_fe_commute_mul_diff
    (vec_i vec_j zeta result_j : Std.I16)
    (hr : (result_j.val : ZMod 3329) =
          ((vec_j.val : ZMod 3329) - (vec_i.val : ZMod 3329)) *
          (zeta.val : ZMod 3329) * 169) :
    i16_to_spec_fe_mont result_j =
      i16_to_spec_fe_mont zeta *
      (i16_to_spec_fe_mont vec_j - i16_to_spec_fe_mont vec_i) := by
  unfold i16_to_spec_fe_mont
  rw [hr]; ring

/-! ## A.16 / A.17 — base-case multiply commutes (even and odd halves).

    These are the upstream `Z3rlimit 400` lemmas (~80 LOC F* each
    with explicit `lemma_mod_*_distr_*` chains). In Lean the same
    statement falls to `rw [hr]; ring` in `ZMod 3329` because the
    Montgomery-factor algebra is just commutative-ring distribution. -/

/-- A.16 `lemma_base_case_mult_even_fe_commute` (F*: Chunk.fst:414). -/
@[scoped grind .]
theorem lemma_base_case_mult_even_fe_commute
    (a0 b0 a1 b1 zeta result : Std.I16)
    (hr : (result.val : ZMod 3329) =
          ((a0.val : ZMod 3329) * (b0.val : ZMod 3329) +
           (a1.val : ZMod 3329) * (b1.val : ZMod 3329) *
           (zeta.val : ZMod 3329) * 169) * 169) :
    i16_to_spec_fe_mont result =
      i16_to_spec_fe_mont a0 * i16_to_spec_fe_mont b0 +
      i16_to_spec_fe_mont a1 * i16_to_spec_fe_mont b1 *
      i16_to_spec_fe_mont zeta := by
  unfold i16_to_spec_fe_mont
  rw [hr]; ring

/-- A.17 `lemma_base_case_mult_odd_fe_commute` (F*: Chunk.fst:523). -/
@[scoped grind .]
theorem lemma_base_case_mult_odd_fe_commute
    (a0 b1 a1 b0 result : Std.I16)
    (hr : (result.val : ZMod 3329) =
          ((a0.val : ZMod 3329) * (b1.val : ZMod 3329) +
           (a1.val : ZMod 3329) * (b0.val : ZMod 3329)) * 169) :
    i16_to_spec_fe_mont result =
      i16_to_spec_fe_mont a0 * i16_to_spec_fe_mont b1 +
      i16_to_spec_fe_mont a1 * i16_to_spec_fe_mont b0 := by
  unfold i16_to_spec_fe_mont
  rw [hr]; ring

/-! ## A.18 — combined base-case multiply pair (both halves). -/

/-- A.18 `lemma_base_case_mult_pair_commute` (F*: Chunk.fst:547).
    Bundles A.16 / A.17 — one call per binomial pair. -/
@[scoped grind .]
theorem lemma_base_case_mult_pair_commute
    (a0 b0 a1 b1 zeta result_even result_odd : Std.I16)
    (hr_e : (result_even.val : ZMod 3329) =
            ((a0.val : ZMod 3329) * (b0.val : ZMod 3329) +
             (a1.val : ZMod 3329) * (b1.val : ZMod 3329) *
             (zeta.val : ZMod 3329) * 169) * 169)
    (hr_o : (result_odd.val : ZMod 3329) =
            ((a0.val : ZMod 3329) * (b1.val : ZMod 3329) +
             (a1.val : ZMod 3329) * (b0.val : ZMod 3329)) * 169) :
    i16_to_spec_fe_mont result_even =
      i16_to_spec_fe_mont a0 * i16_to_spec_fe_mont b0 +
      i16_to_spec_fe_mont a1 * i16_to_spec_fe_mont b1 *
      i16_to_spec_fe_mont zeta
    ∧
    i16_to_spec_fe_mont result_odd =
      i16_to_spec_fe_mont a0 * i16_to_spec_fe_mont b1 +
      i16_to_spec_fe_mont a1 * i16_to_spec_fe_mont b0 := by
  exact ⟨lemma_base_case_mult_even_fe_commute a0 b0 a1 b1 zeta result_even hr_e,
         lemma_base_case_mult_odd_fe_commute a0 b1 a1 b0 result_odd hr_o⟩

/-! ## A.19 / A.20 — Montgomery multiplication commutes. -/

/-- A.19 `lemma_mont_mul_fe_commute_mont_mont` (F*: Chunk.fst:615).
    Two Mont-domain operands: the impl's `· R⁻¹` cancels the Mont
    lift's extra factor, yielding plain FE multiplication. -/
@[scoped grind .]
theorem lemma_mont_mul_fe_commute_mont_mont (a b r : Std.I16)
    (hr : (r.val : ZMod 3329) =
          (a.val : ZMod 3329) * (b.val : ZMod 3329) * 169) :
    i16_to_spec_fe_mont a * i16_to_spec_fe_mont b = i16_to_spec_fe_mont r := by
  unfold i16_to_spec_fe_mont
  rw [hr]; ring

/-- A.20 `lemma_mont_mul_fe_commute_mont_plain` (F*: Chunk.fst:624).
    Mixed mode: `a` Mont, `b` plain, result plain. -/
@[scoped grind .]
theorem lemma_mont_mul_fe_commute_mont_plain (a b r : Std.I16)
    (hr : (r.val : ZMod 3329) =
          (a.val : ZMod 3329) * (b.val : ZMod 3329) * 169) :
    i16_to_spec_fe_mont a * i16_to_spec_fe_plain b = i16_to_spec_fe_plain r := by
  unfold i16_to_spec_fe_mont i16_to_spec_fe_plain
  rw [hr]; ring

/-! ## A.21 — plain multiplication by a constant. -/

/-- A.21 `lemma_mul_const_fe_commute_plain` (F*: Chunk.fst:633).
    Strict Int-product precondition (no overflow), plain-domain
    lift on both sides. -/
@[scoped grind .]
theorem lemma_mul_const_fe_commute_plain (a c r : Std.I16)
    (hr : r.val = a.val * c.val) :
    i16_to_spec_fe_plain a * i16_to_spec_fe_plain c = i16_to_spec_fe_plain r := by
  unfold i16_to_spec_fe_plain
  rw [hr]; push_cast; ring

/-! ## A.22 — combined inverse-butterfly pair. -/

/-- A.22 `lemma_inv_butterfly_pair_commute` (F*: Chunk.fst:588).
    Bundles the `add_mont_mod` (lane `i`) and `mul_diff` (lane `j`)
    sides of one Gentleman–Sande inverse butterfly. -/
@[scoped grind .]
theorem lemma_inv_butterfly_pair_commute
    (vec_i vec_j result_i result_j zeta : Std.I16)
    (hr_i : (result_i.val : ZMod 3329) =
            (vec_j.val : ZMod 3329) + (vec_i.val : ZMod 3329))
    (hr_j : (result_j.val : ZMod 3329) =
            ((vec_j.val : ZMod 3329) - (vec_i.val : ZMod 3329)) *
            (zeta.val : ZMod 3329) * 169) :
    i16_to_spec_fe_mont result_i =
      i16_to_spec_fe_mont vec_i + i16_to_spec_fe_mont vec_j
    ∧
    i16_to_spec_fe_mont result_j =
      i16_to_spec_fe_mont zeta *
      (i16_to_spec_fe_mont vec_j - i16_to_spec_fe_mont vec_i) := by
  refine ⟨?_, ?_⟩
  · -- Reuse A.7 with operands swapped via `add_comm`; A.7's ensures is
    -- `mont_fe a + mont_fe b = mont_fe r`, so the goal direction needs `.symm`.
    have hr_i' : (result_i.val : ZMod 3329) =
        (vec_i.val : ZMod 3329) + (vec_j.val : ZMod 3329) := by
      rw [hr_i]; ring
    exact (lemma_add_fe_commute_mont_mod vec_i vec_j result_i hr_i').symm
  · exact lemma_inv_butterfly_fe_commute_mul_diff vec_i vec_j zeta result_j hr_j

/-! ## Block B — chunk-level commutes.

    Port of `Hacspec_ml_kem.Commute.Chunk.fst` lines 671–950. Each
    Block-B lemma takes the impl post as an explicit per-lane
    hypothesis `hr : ∀ j : Fin 16, …` (in lieu of the F* `Operations`
    trait `T.f_repr`/`T.f_*` machinery — see M.1 Spec.lean note I.2)
    and lifts the corresponding Block-A scalar commute to the
    `Vector.ofFn (n := 16) (fun j => …)` shape used by M.4's poly-level
    aggregation.

    The shape is uniformly:
        Vector.ofFn (lift ∘ getLane r) = Vector.ofFn (combine ∘ lift ∘ getLane lhs ∘ …)
    closed by `Vector.ext` + `Vector.getElem_ofFn` + one Block-A apply.

    ### Why no `@[scoped grind]` on Block B

    The Block-A scalar lemmas accept `@[scoped grind]` because
    `grind` can pattern on `i16_to_spec_fe_X _` directly in the
    conclusion. The Block-B conclusions wrap the lifts inside a
    `Vector.ofFn (n := 16) (fun j => i16_to_spec_fe_X ...)`, which puts
    the only candidate pattern under a binder; `grind` rejects this
    with "failed to find an usable pattern using different modifiers"
    regardless of `=`/`←`/`→` modifier or `grind_pattern` (the binders
    leave `lhs`/`rhs`/`r` un-instantiable). Block-B lemmas are therefore
    consumed explicitly by Block-C / M.4 poly aggregation via
    `exact`/`apply` rather than via `grind`.

    B.11–B.14 (compress/decompress chunks) deferred; see comment block
    at end of file.
-/

/-! ### B.1 / B.2 — pointwise addition (plain and Mont). -/

/-- B.1 `lemma_add_chunk_commutes_plain` (F*: Chunk.fst:671). -/
theorem lemma_add_chunk_commutes_plain
    (lhs rhs r : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hr : ∀ j : Fin 16,
            (r.elements.val[j.val]!).val =
            (lhs.elements.val[j.val]!).val + (rhs.elements.val[j.val]!).val) :
    Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_plain (r.elements.val[j.val]!))
    = Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_plain (lhs.elements.val[j.val]!) +
        i16_to_spec_fe_plain (rhs.elements.val[j.val]!)) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn]
  exact (lemma_add_fe_commute_plain _ _ _ (hr ⟨j, hj⟩)).symm

/-- B.2 `lemma_add_chunk_commutes_mont` (F*: Chunk.fst:700). -/
theorem lemma_add_chunk_commutes_mont
    (lhs rhs r : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hr : ∀ j : Fin 16,
            (r.elements.val[j.val]!).val =
            (lhs.elements.val[j.val]!).val + (rhs.elements.val[j.val]!).val) :
    Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_mont (r.elements.val[j.val]!))
    = Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_mont (lhs.elements.val[j.val]!) +
        i16_to_spec_fe_mont (rhs.elements.val[j.val]!)) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn]
  exact (lemma_add_fe_commute_mont _ _ _ (hr ⟨j, hj⟩)).symm

/-! ### B.3 / B.4 — pointwise subtraction (plain and Mont). -/

/-- B.3 `lemma_sub_chunk_commutes_plain` (F*: Chunk.fst:729). -/
theorem lemma_sub_chunk_commutes_plain
    (lhs rhs r : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hr : ∀ j : Fin 16,
            (r.elements.val[j.val]!).val =
            (lhs.elements.val[j.val]!).val - (rhs.elements.val[j.val]!).val) :
    Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_plain (r.elements.val[j.val]!))
    = Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_plain (lhs.elements.val[j.val]!) -
        i16_to_spec_fe_plain (rhs.elements.val[j.val]!)) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn]
  exact (lemma_sub_fe_commute_plain _ _ _ (hr ⟨j, hj⟩)).symm

/-- B.4 `lemma_sub_chunk_commutes_mont` (F*: Chunk.fst:758). -/
theorem lemma_sub_chunk_commutes_mont
    (lhs rhs r : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hr : ∀ j : Fin 16,
            (r.elements.val[j.val]!).val =
            (lhs.elements.val[j.val]!).val - (rhs.elements.val[j.val]!).val) :
    Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_mont (r.elements.val[j.val]!))
    = Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_mont (lhs.elements.val[j.val]!) -
        i16_to_spec_fe_mont (rhs.elements.val[j.val]!)) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn]
  exact (lemma_sub_fe_commute_mont _ _ _ (hr ⟨j, hj⟩)).symm

/-! ### B.5 — multiply-by-constant (plain × plain). -/

/-- B.5 `lemma_multiply_by_constant_chunk_commutes` (F*: Chunk.fst:790). -/
theorem lemma_multiply_by_constant_chunk_commutes
    (vec r : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Std.I16)
    (hr : ∀ j : Fin 16,
            (r.elements.val[j.val]!).val =
            (vec.elements.val[j.val]!).val * c.val) :
    Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_plain (r.elements.val[j.val]!))
    = Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_plain (vec.elements.val[j.val]!) *
        i16_to_spec_fe_plain c) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn]
  exact (lemma_mul_const_fe_commute_plain _ _ _ (hr ⟨j, hj⟩)).symm

/-! ### B.6 / B.7 — Montgomery multiply-by-constant. -/

/-- B.6 `lemma_montgomery_multiply_by_constant_chunk_commutes_mont_mont`
    (F*: Chunk.fst:818). Both operands lifted Mont; result lifted Mont. -/
theorem lemma_montgomery_multiply_by_constant_chunk_commutes_mont_mont
    (vec r : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Std.I16)
    (hr : ∀ j : Fin 16,
            ((r.elements.val[j.val]!).val : ZMod 3329) =
            ((vec.elements.val[j.val]!).val : ZMod 3329) *
            (c.val : ZMod 3329) * 169) :
    Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_mont (r.elements.val[j.val]!))
    = Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_mont (vec.elements.val[j.val]!) *
        i16_to_spec_fe_mont c) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn]
  exact (lemma_mont_mul_fe_commute_mont_mont _ _ _ (hr ⟨j, hj⟩)).symm

/-- B.7 `lemma_montgomery_multiply_by_constant_chunk_commutes_mont_plain`
    (F*: Chunk.fst:847). `vec` lifted Mont, `c` lifted plain, result
    lifted plain. -/
theorem lemma_montgomery_multiply_by_constant_chunk_commutes_mont_plain
    (vec r : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Std.I16)
    (hr : ∀ j : Fin 16,
            ((r.elements.val[j.val]!).val : ZMod 3329) =
            ((vec.elements.val[j.val]!).val : ZMod 3329) *
            (c.val : ZMod 3329) * 169) :
    Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_plain (r.elements.val[j.val]!))
    = Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_mont (vec.elements.val[j.val]!) *
        i16_to_spec_fe_plain c) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn]
  exact (lemma_mont_mul_fe_commute_mont_plain _ _ _ (hr ⟨j, hj⟩)).symm

/-! ### B.8 / B.9 / B.10 — identity-on-plain-lift ops.

    Barrett reduce, conditional `q`-subtract, and "to unsigned
    representative" all preserve the residue class mod q. Their chunk
    commutes have a simpler shape: both sides of the equation are the
    same `Vector.ofFn (i16_to_spec_fe_plain ∘ getLane _)` modulo a
    `(r.val : ZMod 3329) = (vec.val : ZMod 3329)` per-lane precond. -/

/-- B.8 `lemma_barrett_reduce_chunk_commutes` (F*: Chunk.fst:878). -/
theorem lemma_barrett_reduce_chunk_commutes
    (vec r : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hr : ∀ j : Fin 16,
            ((r.elements.val[j.val]!).val : ZMod 3329) =
            ((vec.elements.val[j.val]!).val : ZMod 3329)) :
    Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_plain (r.elements.val[j.val]!))
    = Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_plain (vec.elements.val[j.val]!)) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn]
  exact lemma_barrett_fe_commute _ _ (hr ⟨j, hj⟩)

/-- B.9 `lemma_cond_subtract_3329_chunk_commutes` (F*: Chunk.fst:902).
    Same shape as B.8 — the impl conditionally subtracts q, which is a
    no-op mod q. -/
theorem lemma_cond_subtract_3329_chunk_commutes
    (vec r : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hr : ∀ j : Fin 16,
            ((r.elements.val[j.val]!).val : ZMod 3329) =
            ((vec.elements.val[j.val]!).val : ZMod 3329)) :
    Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_plain (r.elements.val[j.val]!))
    = Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_plain (vec.elements.val[j.val]!)) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn]
  exact lemma_barrett_fe_commute _ _ (hr ⟨j, hj⟩)

/-- B.10 `lemma_to_unsigned_representative_chunk_commutes`
    (F*: Chunk.fst:925). The impl projects to canonical `[0, q)`
    representative — identity mod q. -/
theorem lemma_to_unsigned_representative_chunk_commutes
    (vec r : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hr : ∀ j : Fin 16,
            ((r.elements.val[j.val]!).val : ZMod 3329) =
            ((vec.elements.val[j.val]!).val : ZMod 3329)) :
    Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_plain (r.elements.val[j.val]!))
    = Vector.ofFn (n := 16) (fun (j : Fin 16) =>
        i16_to_spec_fe_plain (vec.elements.val[j.val]!)) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn]
  exact lemma_barrett_fe_commute _ _ (hr ⟨j, hj⟩)

/-! ### B.11–B.14 deferred per arch plan §C.2 / Open Question I.4.

    The compress / decompress chunk commutes
    (`lemma_compress_chunk_commutes`, `lemma_decompress_chunk_commutes`,
    `lemma_compress_message_chunk_commutes`,
    `lemma_decompress_message_chunk_commutes`) are blocked by Open
    Question I.4: `HacspecMlKem.compress.compress_d` is
    `Result`-monadic, and the lift design (pure-vs-Result return type,
    `Vector (Fin (2^d)) 256` vs `Vector (ZMod 3329) 256` shape) is not
    pinned down. M.1's `bit_compress` / `bit_decompress` are
    placeholder stubs, so any chunk commute stated against them would
    be vacuous. They land in a follow-up dispatch once I.4 is resolved.
-/

/-! ## Block C — poly-level commutes.

    Port of `Hacspec_ml_kem.Commute.Chunk.fst` lines 1376-2583. Each
    Block-C lemma takes the impl post as an explicit per-lane
    hypothesis `hr : ∀ i j : Fin 16, …` and conclusion is stated in
    BIT-SIDE terms (`bit_<op>` from M.1), not in `HP.<op>` terms (those
    are `Result`-monadic in the hacspec spec; a later pass will bridge
    `bit_*` ↔ `HP.*`).

    ### `@[scoped grind]` policy (matches Block B).

    Block-C conclusions wrap the lifts inside `to_spec_poly_*` (which
    is itself a `Vector.ofFn (n := 256)`); the only candidate pattern
    is under a binder, which `grind` rejects. We therefore omit
    `@[scoped grind]` and consume these lemmas via explicit
    `exact`/`apply` from M.4 poly aggregation.

    The main hammer is `lemma_to_spec_poly_*_eq_of_coeffs` (M.1 spec).
    Each Block-C statement reduces to "per-lane Block-A/B lemma gives
    the same value on both sides".
-/

/-! ### C.1 — Barrett reduce is identity at the poly level. -/

/-- C.1 `lemma_poly_barrett_reduce_id` (F*: Chunk.fst:1376). Since
    `bit_barrett_reduce p = p` definitionally in M.1, this is `rfl`. -/
theorem lemma_poly_barrett_reduce_id (p : MontPoly) :
    bit_barrett_reduce p = p := rfl

/-! ### C.2 — Barrett reduce poly commute (per-lane residue ↦ plain
        lift identity). -/

/-- C.2 `lemma_poly_barrett_reduce_commute` (F*: Chunk.fst:1401). The
    per-lane residue equality lifts to the plain-domain poly equality
    via `lemma_to_spec_poly_plain_eq_of_coeffs` + per-lane A.5
    (`lemma_barrett_fe_commute`). Combined with C.1 the conclusion can
    equivalently be stated as
    `to_spec_poly_plain result = to_spec_poly_plain myself`. -/
theorem lemma_poly_barrett_reduce_commute
    (myself result :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hr : ∀ i j : Fin 16,
            ((result.coefficients.val[i.val]!).elements.val[j.val]!).val
              = ((myself.coefficients.val[i.val]!).elements.val[j.val]!).val
            ∨
            (((result.coefficients.val[i.val]!).elements.val[j.val]!).val
              : ZMod 3329)
              = (((myself.coefficients.val[i.val]!).elements.val[j.val]!).val
                  : ZMod 3329)) :
    to_spec_poly_plain result
      = bit_barrett_reduce (to_spec_poly_plain myself) := by
  rw [lemma_poly_barrett_reduce_id]
  apply lemma_to_spec_poly_plain_eq_of_coeffs
  intro i j
  rcases hr i j with h | h
  · exact lemma_barrett_fe_commute _ _ (by rw [h])
  · exact lemma_barrett_fe_commute _ _ h

/-! ### C.3 — pointwise addition at the poly level (plain domain). -/

/-- C.3 `lemma_add_to_ring_element_commute` (F*: Chunk.fst:1447). Per-lane
    strict-add hypothesis lifts to the plain-domain poly equality
    `to_spec_poly_plain result = bit_add (to_spec_poly_plain myself)
    (to_spec_poly_plain rhs)` via `Vector.ext` + per-lane A.1.

    `maxRecDepth 2000` is required because the per-lane unifier
    threads through three nested `Vector.ofFn` bodies (LHS
    `to_spec_poly_plain` + two RHS `to_spec_poly_plain` inside
    `bit_add`'s `Vector.ofFn`). -/
theorem lemma_add_to_ring_element_commute
    (myself rhs result :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hr : ∀ i j : Fin 16,
            ((result.coefficients.val[i.val]!).elements.val[j.val]!).val
              = ((myself.coefficients.val[i.val]!).elements.val[j.val]!).val
              + ((rhs.coefficients.val[i.val]!).elements.val[j.val]!).val) :
    to_spec_poly_plain result
      = bit_add (to_spec_poly_plain myself) (to_spec_poly_plain rhs) := by
  unfold to_spec_poly_plain bit_add
  apply Vector.ext
  intro k hk
  -- After unfolding both sides we have nested `Vector.ofFn`s. The outer
  -- `Vector.ofFn` of `bit_add` indexes at `[k]'hk`; reducing it via
  -- `Vector.getElem_ofFn` substitutes `⟨k, hk⟩` into the body, which then
  -- contains `(Vector.ofFn _)[⟨k, hk⟩]` for the two `to_spec_poly_plain`
  -- arguments. Those Fin-indexed accesses are definitionally `[k]'hk`
  -- accesses, so rewrite via `rfl` then fire the simp lemma again.
  simp only [Vector.getElem_ofFn]
  -- Introduce the Fin-form lemma `(Vector.ofFn f)[⟨k, hk⟩] = (Vector.ofFn f)[k]'hk`
  -- as a local hypothesis via `rfl`, since the two forms are definitionally equal.
  have my_eq :
      (Vector.ofFn fun (j : Fin 256) =>
            i16_to_spec_fe_plain
              ((myself.coefficients.val[j.val / 16]!).elements.val[j.val % 16]!))[(⟨k, hk⟩ : Fin 256)]
        = (Vector.ofFn fun (j : Fin 256) =>
            i16_to_spec_fe_plain
              ((myself.coefficients.val[j.val / 16]!).elements.val[j.val % 16]!))[k]'hk := rfl
  have rhs_eq :
      (Vector.ofFn fun (j : Fin 256) =>
            i16_to_spec_fe_plain
              ((rhs.coefficients.val[j.val / 16]!).elements.val[j.val % 16]!))[(⟨k, hk⟩ : Fin 256)]
        = (Vector.ofFn fun (j : Fin 256) =>
            i16_to_spec_fe_plain
              ((rhs.coefficients.val[j.val / 16]!).elements.val[j.val % 16]!))[k]'hk := rfl
  rw [my_eq, rhs_eq]
  simp only [Vector.getElem_ofFn]
  have hdiv_lt : k / 16 < 16 := by omega
  have hmod_lt : k % 16 < 16 := Nat.mod_lt k (by decide)
  exact (lemma_add_fe_commute_plain _ _ _
            (hr ⟨k / 16, hdiv_lt⟩ ⟨k % 16, hmod_lt⟩)).symm

/-! ### C.4 — INTT-Mont finalize core (KEYSTONE). -/

/-- C.4 `lemma_intt_mont_form_post` (F*: Chunk.fst:1540). KEYSTONE. The
    per-lane INTT-Mont finalize identity: given the INTT-Mont form
    precondition `(b.val : ZMod 3329) * 2285 = b_real_val * 128`
    (i.e., `b` represents `b_real_val * 128 * R⁻¹` post-INTT) and the
    `mont_mul(b, 1441)` post `(r.val : ZMod 3329) = (b.val : ZMod 3329)
    * 1441 * 169`, conclude `(r.val : ZMod 3329) = b_real_val`.

    Proof via three keystones (all `by decide`):
    - `(1441 * 169 : ZMod 3329) = 512`
    - `(2285 * 169 : ZMod 3329) = 1`
    - `(128 * 169 * 512 : ZMod 3329) = 1`
    plus `ring` glue. -/
theorem lemma_intt_mont_form_post
    (b r : Std.I16) (b_real_val : ZMod 3329)
    (hb : (b.val : ZMod 3329) * 2285 = b_real_val * 128)
    (hr : (r.val : ZMod 3329) = (b.val : ZMod 3329) * 1441 * 169) :
    (r.val : ZMod 3329) = b_real_val := by
  have k1 : (1441 * 169 : ZMod 3329) = 512 := by decide
  have k2 : (2285 * 169 : ZMod 3329) = 1 := by decide
  have k3 : (128 * 169 * 512 : ZMod 3329) = 1 := by decide
  -- From hb: multiply both sides by 169.
  -- (b.val * 2285) * 169 = (b_real_val * 128) * 169
  -- ⇒ b.val * (2285 * 169) = b_real_val * (128 * 169)
  -- ⇒ b.val = b_real_val * 128 * 169                         (since 2285·169=1)
  have hb2 : (b.val : ZMod 3329) = b_real_val * 128 * 169 := by
    have := congrArg (· * (169 : ZMod 3329)) hb
    simp only at this
    -- this : (b.val * 2285) * 169 = (b_real_val * 128) * 169
    have h1 : (b.val : ZMod 3329) * 2285 * 169
            = (b.val : ZMod 3329) * (2285 * 169) := by ring
    rw [h1, k2, mul_one] at this
    exact this
  -- Now substitute into hr and reduce via k1 and k3.
  rw [hr, hb2]
  -- Goal: b_real_val * 128 * 169 * 1441 * 169 = b_real_val
  have h2 : b_real_val * 128 * 169 * 1441 * 169
          = b_real_val * (128 * 169 * (1441 * 169)) := by ring
  rw [h2, k1]
  -- Goal: b_real_val * (128 * 169 * 512) = b_real_val
  rw [k3, mul_one]

/-! ### C.5 — Per-lane INTT-Mont finalize wrapper. -/

/-- C.5 `lemma_intt_mont_finalize_fe` (F*: Chunk.fst:1666). Per-lane
    wrap of C.4: given the same hypotheses, the plain-domain lift
    `i16_to_spec_fe_plain r` equals the `b_real_val`. -/
theorem lemma_intt_mont_finalize_fe
    (b r : Std.I16) (b_real_val : ZMod 3329)
    (hb : (b.val : ZMod 3329) * 2285 = b_real_val * 128)
    (hr : (r.val : ZMod 3329) = (b.val : ZMod 3329) * 1441 * 169) :
    i16_to_spec_fe_plain r = b_real_val := by
  unfold i16_to_spec_fe_plain
  exact lemma_intt_mont_form_post b r b_real_val hb hr

/-! ### C.7 — to_standard_domain finalize at the FE level. -/

/-- C.7 `lemma_to_standard_domain_finalize_fe` (F*: Chunk.fst:2019).
    Given the standard-domain form `(myself.val : ZMod 3329) * 2285
    = plain_real_val` (i.e., `myself` represents `α · R⁻¹`) and the
    `mont_mul(myself, 1353)` post `(r.val : ZMod 3329) = (myself.val
    : ZMod 3329) * 1353 * 169`, conclude `i16_to_spec_fe_mont r
    = plain_real_val * 2285` (the "Mont-lift of `r` recovers `α · R`").

    Note: we state the conclusion via `i16_to_spec_fe_mont` (×169) on
    the Mont domain lift. The keystone `(1353 * 169 : ZMod 3329) = 2285`
    (R² · R⁻¹ = R) combined with the precondition gives the result. -/
theorem lemma_to_standard_domain_finalize_fe
    (myself r : Std.I16) (plain_real_val : ZMod 3329)
    (hm : (myself.val : ZMod 3329) * 2285 = plain_real_val)
    (hr : (r.val : ZMod 3329)
            = (myself.val : ZMod 3329) * 1353 * 169) :
    i16_to_spec_fe_plain r = plain_real_val := by
  have k1 : (1353 * 169 : ZMod 3329) = 2285 := by decide
  unfold i16_to_spec_fe_plain
  rw [hr]
  -- Goal: myself.val * 1353 * 169 = plain_real_val
  have h1 : (myself.val : ZMod 3329) * 1353 * 169
          = (myself.val : ZMod 3329) * (1353 * 169) := by ring
  rw [h1, k1, hm]

/-! ### C.8 — Mont form post (standard-domain analogue of C.4). -/

/-- C.8 `lemma_mont_form_post` (F*: Chunk.fst:1943). Analogous to C.4
    but for the standard-domain (matrix-mul track) form. Given
    `(myself.val : ZMod 3329) * 2285 = plain_real_val` (standard-domain
    form) and `(r.val : ZMod 3329) = (myself.val : ZMod 3329) * 1353
    * 169` (mont_mul-by-1353), conclude `(r.val : ZMod 3329)
    = plain_real_val`.

    Keystone: `(1353 * 169 : ZMod 3329) = 2285`. -/
theorem lemma_mont_form_post
    (myself r : Std.I16) (plain_real_val : ZMod 3329)
    (hm : (myself.val : ZMod 3329) * 2285 = plain_real_val)
    (hr : (r.val : ZMod 3329)
            = (myself.val : ZMod 3329) * 1353 * 169) :
    (r.val : ZMod 3329) = plain_real_val := by
  have k1 : (1353 * 169 : ZMod 3329) = 2285 := by decide
  rw [hr]
  have h1 : (myself.val : ZMod 3329) * 1353 * 169
          = (myself.val : ZMod 3329) * (1353 * 169) := by ring
  rw [h1, k1, hm]

/-! ## Block C Tier 2 — poly-level lemmas with composite ops.

    These three lemmas extend Block C with the "composite" poly-level
    commutes that thread through more than one impl op (subtract +
    mont_mul-by-1441, add + mont_mul-by-1353 + barrett, and the
    `createi`-equality bridge that pairs with C.6).

    ### Framing decision: post-keystone form on the impl precondition.

    For C.6, the impl chain is `result_lane = mont_mul(rhs - myself, 1441)`,
    which in `ZMod 3329` collapses to `result_lane.val = (rhs.val -
    myself.val) · 1441 · 169 = (rhs.val - myself.val) · 512` (via the
    C.4 keystone `1441 · 169 = 512`). We state the per-lane impl
    precondition in the **post-keystone form** `result.val =
    (rhs.val - myself.val) · 512` so the conclusion against M.1's
    `bit_subtract_reduce` (whose body is `(q[i] - p[i]) · 512` on
    `MontPoly`) reduces by pure `ring`. Callers chain through C.4 first.

    For C.9, the impl chain is `result_lane = barrett (myself + error)`,
    with the per-lane post being a `ZMod 3329` residue equality. We
    state it directly as `result.val ≡ myself.val + error.val (mod q)`
    and conclude `to_spec_poly_plain result = bit_add_to_ring_element
    (to_spec_poly_plain myself) (to_spec_poly_plain error)`.

    For C.10, this is the `Vector.ofFn`-equality bridge — given two
    impl polys with equal coefficients, the scaled-by-1441 createis
    coincide. In Lean this is essentially `congrArg` on top of
    `lemma_to_spec_poly_mont_eq_of_coeffs`. -/

/-! ### C.6 — subtract-reduce poly commute (post-keystone form). -/

/-- C.6 `lemma_subtract_reduce_commute` (F*: Chunk.fst:1852). Poly-level
    commute for the subtract-then-finalize-INTT chain.

    Per-lane impl precondition is stated in **post-keystone form**: the
    impl's `mont_mul(rhs - myself, 1441)` already collapses to
    `(rhs.val - myself.val) · 512` in `ZMod 3329` via the C.4 keystone
    `(1441 · 169 : ZMod 3329) = 512`. Callers  apply C.4 once per
    lane and feed the post-keystone equality here, avoiding redoing the
    1441-keystone chain inside this lemma.

    Conclusion is stated against M.1's `bit_subtract_reduce` (which is
    itself `(q[i] - p[i]) · 512` on `MontPoly`) lifted through
    `to_spec_poly_mont` on both sides. -/
theorem lemma_subtract_reduce_commute
    (myself rhs result :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hr : ∀ i j : Fin 16,
            ((result.coefficients.val[i.val]!).elements.val[j.val]!).val
              = (((rhs.coefficients.val[i.val]!).elements.val[j.val]!).val
                  - ((myself.coefficients.val[i.val]!).elements.val[j.val]!).val)
                * 512) :
    to_spec_poly_mont result
      = bit_subtract_reduce (to_spec_poly_mont myself) (to_spec_poly_mont rhs) := by
  unfold to_spec_poly_mont bit_subtract_reduce
  apply Vector.ext
  intro k hk
  -- Strip the outer `Vector.ofFn` on both sides; LHS body is
  --   `i16_to_spec_fe_mont (result.coef[k/16].elt[k%16])`
  -- and RHS body is
  --   `((to_spec_poly_mont rhs)[k] - (to_spec_poly_mont myself)[k]) * 512`.
  simp only [Vector.getElem_ofFn]
  -- The two `(Vector.ofFn _)[⟨k, hk⟩]` accesses inside the RHS body are
  -- definitionally `[k]'hk` accesses; identify the two `Fin`-form
  -- accesses to the plain `[k]'hk` form (same trick as C.3).
  have my_eq :
      (Vector.ofFn fun (j : Fin 256) =>
            i16_to_spec_fe_mont
              ((myself.coefficients.val[j.val / 16]!).elements.val[j.val % 16]!))[(⟨k, hk⟩ : Fin 256)]
        = (Vector.ofFn fun (j : Fin 256) =>
            i16_to_spec_fe_mont
              ((myself.coefficients.val[j.val / 16]!).elements.val[j.val % 16]!))[k]'hk := rfl
  have rhs_eq :
      (Vector.ofFn fun (j : Fin 256) =>
            i16_to_spec_fe_mont
              ((rhs.coefficients.val[j.val / 16]!).elements.val[j.val % 16]!))[(⟨k, hk⟩ : Fin 256)]
        = (Vector.ofFn fun (j : Fin 256) =>
            i16_to_spec_fe_mont
              ((rhs.coefficients.val[j.val / 16]!).elements.val[j.val % 16]!))[k]'hk := rfl
  rw [my_eq, rhs_eq]
  simp only [Vector.getElem_ofFn]
  -- Goal:  i16_to_spec_fe_mont result.coef[k/16].elt[k%16]
  --      = (i16_to_spec_fe_mont rhs.coef[k/16].elt[k%16]
  --         - i16_to_spec_fe_mont myself.coef[k/16].elt[k%16]) * 512
  -- Unfold the Mont lift to expose the `· 169` factor on each lane,
  -- then substitute `hr` on the LHS and close with `ring`.
  unfold i16_to_spec_fe_mont
  have hdiv_lt : k / 16 < 16 := by omega
  have hmod_lt : k % 16 < 16 := Nat.mod_lt k (by decide)
  have h := hr ⟨k / 16, hdiv_lt⟩ ⟨k % 16, hmod_lt⟩
  -- `h : result.val = (rhs.val - myself.val) * 512` as `Int`.
  -- Cast to `ZMod 3329` and combine with `ring`.
  have hz :
      ((((result.coefficients.val[k / 16]!).elements.val[k % 16]!).val : ZMod 3329))
        = ((((rhs.coefficients.val[k / 16]!).elements.val[k % 16]!).val : ZMod 3329)
            - (((myself.coefficients.val[k / 16]!).elements.val[k % 16]!).val : ZMod 3329))
          * 512 := by
    have := congrArg (Int.cast (R := ZMod 3329)) h
    push_cast at this
    exact this
  rw [hz]; ring

/-! ### C.9 — add-standard-error-reduce poly commute. -/

/-- C.9 `lemma_add_standard_error_reduce_commute` (F*: Chunk.fst:2135).
    Poly-level commute for the `add + barrett` chain. Per-lane impl
    precondition is the residue equality
    `result.val ≡ myself.val + error.val (mod q)` (the impl's barrett
    reduction collapses to identity at the `ZMod` level — A.7's shape).

    Conclusion: `to_spec_poly_plain result = bit_add_to_ring_element
    (to_spec_poly_plain myself) (to_spec_poly_plain error)`, where
    `bit_add_to_ring_element = bit_add` is the M.1 pointwise add on
    `MontPoly`. -/
theorem lemma_add_standard_error_reduce_commute
    (myself error result :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hr : ∀ i j : Fin 16,
            (((result.coefficients.val[i.val]!).elements.val[j.val]!).val
                : ZMod 3329)
              = (((myself.coefficients.val[i.val]!).elements.val[j.val]!).val
                  : ZMod 3329)
                + (((error.coefficients.val[i.val]!).elements.val[j.val]!).val
                  : ZMod 3329)) :
    to_spec_poly_plain result
      = bit_add_to_ring_element
          (to_spec_poly_plain myself) (to_spec_poly_plain error) := by
  unfold bit_add_to_ring_element bit_add to_spec_poly_plain
  apply Vector.ext
  intro k hk
  simp only [Vector.getElem_ofFn]
  have my_eq :
      (Vector.ofFn fun (j : Fin 256) =>
            i16_to_spec_fe_plain
              ((myself.coefficients.val[j.val / 16]!).elements.val[j.val % 16]!))[(⟨k, hk⟩ : Fin 256)]
        = (Vector.ofFn fun (j : Fin 256) =>
            i16_to_spec_fe_plain
              ((myself.coefficients.val[j.val / 16]!).elements.val[j.val % 16]!))[k]'hk := rfl
  have err_eq :
      (Vector.ofFn fun (j : Fin 256) =>
            i16_to_spec_fe_plain
              ((error.coefficients.val[j.val / 16]!).elements.val[j.val % 16]!))[(⟨k, hk⟩ : Fin 256)]
        = (Vector.ofFn fun (j : Fin 256) =>
            i16_to_spec_fe_plain
              ((error.coefficients.val[j.val / 16]!).elements.val[j.val % 16]!))[k]'hk := rfl
  rw [my_eq, err_eq]
  simp only [Vector.getElem_ofFn]
  -- Goal: i16_to_spec_fe_plain result.coef[k/16].elt[k%16]
  --     = i16_to_spec_fe_plain myself.coef[k/16].elt[k%16]
  --       + i16_to_spec_fe_plain error.coef[k/16].elt[k%16]
  unfold i16_to_spec_fe_plain
  have hdiv_lt : k / 16 < 16 := by omega
  have hmod_lt : k % 16 < 16 := Nat.mod_lt k (by decide)
  exact hr ⟨k / 16, hdiv_lt⟩ ⟨k % 16, hmod_lt⟩

/-! ### C.10 — `Vector.ofFn`-equality bridge for the C.6 conclusion. -/

/-- C.10 `lemma_subtract_reduce_scaled_eq` (F*: Chunk.fst:2533). The F*
    version exists to paper over Z3 not auto-deriving equality of two
    `createi`s from equality of their per-lane bodies. In Lean,
    `Vector.ofFn` already enjoys congruence under `funext`, so once we
    know the inner `to_spec_poly_mont` lifts coincide (by
    `lemma_to_spec_poly_mont_eq_of_coeffs`), the outer scaled-by-1441
    `Vector.ofFn`s coincide by `congrArg`.

    Stated against the M.1 idiom (pointwise multiply via `*` in
    `ZMod 3329`, not the F* `impl_FieldElement__mul`). -/
theorem lemma_subtract_reduce_scaled_eq
    (p q :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h : ∀ i j : Fin 16,
            i16_to_spec_fe_mont
              ((p.coefficients.val[i.val]!).elements.val[j.val]!)
            = i16_to_spec_fe_mont
              ((q.coefficients.val[i.val]!).elements.val[j.val]!)) :
    (Vector.ofFn (n := 256) fun (j : Fin 256) =>
        (to_spec_poly_mont p)[j.val]'j.isLt * (1441 : ZMod 3329))
      = (Vector.ofFn (n := 256) fun (j : Fin 256) =>
        (to_spec_poly_mont q)[j.val]'j.isLt * (1441 : ZMod 3329)) := by
  have hpq : to_spec_poly_mont p = to_spec_poly_mont q :=
    lemma_to_spec_poly_mont_eq_of_coeffs p q h
  rw [hpq]

end libcrux_iot_ml_kem.Spec.Commute