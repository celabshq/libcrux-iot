/-
  # `Spec.lean` — pure-Lean intermediate spec for ML-KEM.

  Mirrors `HacspecMlKem`'s `ntt`, `multiply_ntts`, `compress`, …,
  but works on `MontPoly = Vector (ZMod 3329) 256` so that
  `ring`/`field_simp` close the algebraic commute lemmas without
  poking raw `% 3329` arithmetic.

  No `Aeneas.Std.Result`, no `mvcgen`, no impl-side Triple
  obligations — only `Vector`, `ZMod 3329`, and the `bit_<op>`
  function signatures whose algebraic equivalence to the hacspec
  spec lives.

  Design notes:
  - `MontPoly := Vector (ZMod 3329) 256` is the algebraic working type.
    The parallel `SpecPoly := Vector parameters.FieldElement 256` lives
    below.
  - `vector.traits.Operations` has no `repr` field; concrete impls
    (e.g. `vector.portable.vector_type.PortableVector`) carry an
    `elements : Array Std.I16 16` field accessed directly via
    `re.coefficients.val[i]!.elements.val[j]!`. The lift functions
    therefore specialize to `PortableVector`.
  - hacspec spec functions return `Result`; bit-side `bit_<op>` are
    pure; `AlgEquiv` bridges via `Spec.<op>_pure` aliases.
  - The NTT family (`bit_ntt`, `bit_ntt_layer_*`, `bit_invert_ntt_*`,
    `bit_butterfly`, …) ships as identity placeholders so downstream
    code can reference them by name; a later pass replaces these stubs
    with real bodies and proves the algebraic equivalence.
-/
import LibcruxIotMlKem.Spec.NumericKeystones
import LibcruxIotMlKem.Spec.ModularArith
import LibcruxIotMlKem.Spec.Montgomery
import LibcruxIotMlKem.Extraction.Funs
import HacspecMlKem.Extraction.Funs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

namespace libcrux_iot_ml_kem.Spec
open CoreModels Aeneas Aeneas.Std

/-! ### `Inhabited` instances for `.val[j]!` projections.

    The `PolynomialRingElement V`-and-`PortableVector` chunk types
    need an `Inhabited` instance for the `coefficients.val[i]!` /
    `elements.val[j]!` indexing patterns in `to_spec_poly_*` and the
    `bit_*_form_poly` predicates. Declared `local` to avoid colliding
    with the identically-shaped instances in `Equivalence/L3` and
    `Equivalence/L6` files; both can coexist because they're scoped
    to their respective files. -/

local instance instInhabitedPortableVector_bitMlKem :
    Inhabited libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
  ⟨{ elements := Std.Array.make 16#usize (List.replicate 16 (0#i16 : Std.I16))
        (by simp) }⟩

local instance instInhabitedPolynomialRingElement_bitMlKem
    {Vector : Type} [Inhabited Vector] :
    Inhabited (libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector) :=
  ⟨{ coefficients := Std.Array.make 16#usize (List.replicate 16 default) (by simp) }⟩

/-! ## §B.2 Type skeleton -/

/-- The algebraic working type for Layer-M commute proofs. Each ML-KEM
    ring element is a 256-coefficient vector over `ZMod 3329`, so
    `ring` / `field_simp` discharge the bulk of upstream's
    `lemma_mod_*_distr_*` chains directly.

    Lifts from the impl side (a 16 × 16 `Array (PortableVector)`)
    project each lane via `i16_to_spec_fe_{plain,mont}` below. -/
abbrev MontPoly : Type := Vector (ZMod 3329) 256

/-! ## §B.5 — `SpecPoly` + lane coercions. -/

/-- The hacspec interface type: a 256-coefficient vector of
    `parameters.FieldElement` (which wraps a `Std.U16` carrying a
    canonical-form residue mod q). M.4 AlgEquiv lemmas bridge between
    `bit_<op>` (on `MontPoly`) and `Spec.<op>` (on `SpecPoly`). -/
abbrev SpecPoly : Type :=
  Vector hacspec_ml_kem.parameters.FieldElement 256

/-- `parameters.FieldElement → ZMod 3329` lane coercion. -/
def zmodOfFE (fe : hacspec_ml_kem.parameters.FieldElement) : ZMod 3329 :=
  (fe.val.val : ZMod 3329)

/-- `ZMod 3329 → parameters.FieldElement` lane coercion. Takes
    `z.val : Fin 3329 ⊂ Fin 65536`, lifts to a `Std.U16`, and wraps. -/
def feOfZMod (z : ZMod 3329) : hacspec_ml_kem.parameters.FieldElement :=
  { val := ⟨BitVec.ofNat 16 z.val⟩ }

/-- Round-trip identity: lifting `z : ZMod 3329` to a FieldElement and
    back yields `z`. Bridges M.4's "M.1 def equals hacspec spec value"
    statements through the FE lift. -/
theorem zmodOfFE_feOfZMod (z : ZMod 3329) : zmodOfFE (feOfZMod z) = z := by
  unfold zmodOfFE feOfZMod
  -- z.val < 3329 ≤ 65535, so BitVec.ofNat 16 z.val .toNat = z.val.
  have h_lt : z.val < 65536 :=
    Nat.lt_of_lt_of_le (ZMod.val_lt z) (by decide)
  have h_unfold : (BitVec.ofNat 16 z.val).toNat = z.val := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt]
  change ((BitVec.ofNat 16 z.val).toNat : ZMod 3329) = z
  rw [h_unfold]; exact ZMod.natCast_zmod_val z

/-- `MontPoly → SpecPoly` via per-lane `feOfZMod`. -/
def MontPoly.toSpecPoly (m : MontPoly) : SpecPoly := m.map feOfZMod

/-- `SpecPoly → MontPoly` via per-lane `zmodOfFE`. -/
def SpecPoly.toMontPoly (s : SpecPoly) : MontPoly := s.map zmodOfFE

/-! ## §B.4 (part) Lane-level lifts from `Std.I16` (impl side) -/

/-- Plain-domain lane lift: the i16 stores an integer representative
    (possibly signed) of a value mod q. Cast through `Int → ZMod 3329`
    and we're done. -/
def i16_to_spec_fe_plain (x : Std.I16) : ZMod 3329 :=
  (x.val : ZMod 3329)

/-- Mont-domain lane lift: the i16 stores `a · R mod q` for some
    `a : ZMod 3329`; we strip the Montgomery factor by multiplying by
    `R⁻¹ = 169`. -/
def i16_to_spec_fe_mont (x : Std.I16) : ZMod 3329 :=
  ((x.val : ZMod 3329)) * (169 : ZMod 3329)

/-- Unfold rule: `i16_to_spec_fe_plain` is the cast. Re-exported so
    downstream Triple bodies can rewrite without re-unfolding the
    definition. -/
theorem i16_to_spec_fe_plain_unfold (x : Std.I16) :
    i16_to_spec_fe_plain x = (x.val : ZMod 3329) := rfl

/-- Unfold rule: `i16_to_spec_fe_mont` is `x.val · 169`. -/
theorem i16_to_spec_fe_mont_unfold (x : Std.I16) :
    i16_to_spec_fe_mont x = (x.val : ZMod 3329) * 169 := rfl

/-! ## §B.4 (part) Poly-level lifts from `PolynomialRingElement PortableVector` -/

/-- Plain-domain poly lift: project each of the 16 chunks × 16 lanes
    into `ZMod 3329` via `i16_to_spec_fe_plain`. The result is a
    256-element `Vector (ZMod 3329) 256`. -/
def to_spec_poly_plain
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    MontPoly :=
  Vector.ofFn (n := 256) fun j =>
    let i := j.val / 16
    let k := j.val % 16
    let chunk := re.coefficients.val[i]!
    let lane := chunk.elements.val[k]!
    i16_to_spec_fe_plain lane

/-- Mont-domain poly lift: same indexing scheme, but each lane is
    multiplied by `R⁻¹ = 169` to strip the Montgomery factor. -/
def to_spec_poly_mont
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    MontPoly :=
  Vector.ofFn (n := 256) fun j =>
    let i := j.val / 16
    let k := j.val % 16
    let chunk := re.coefficients.val[i]!
    let lane := chunk.elements.val[k]!
    i16_to_spec_fe_mont lane

/-! ## §B.3 — the 34 `bit_<op>` defs.

    Convention:
    - "trivial" ops (`add`, `sub`, `barrett_reduce`, `multiply_*`,
      `to_unsigned_*`, `cond_subtract_3329`) ship with REAL bodies
      because they are 5-line pointwise vector maps.
    - "complex" ops (NTT family, INTT, multiply_ntts, compress,
      byte_encode, byte_decode) ship with STUBBED identity bodies
      because their real bodies are 30-60 LOC and would expand the M.1
      dispatch beyond its single-agent budget. M.4 (AlgEquiv) will
      replace each stub with the real body (and prove algebraic
      equivalence to the hacspec spec). Each stub is marked
      .
-/

/-! ### #1-2 — pointwise add / sub (real bodies, 5 LOC each) -/

/-- `#1 bit_add`: pointwise `(p, q) ↦ p + q` in `ZMod 3329`. Used by
    L6.2 (`add_*_reduce` family). -/
def bit_add (p q : MontPoly) : MontPoly :=
  Vector.ofFn (n := 256) fun i => p[i] + q[i]

/-- `#2 bit_sub`: pointwise `(p, q) ↦ p - q` in `ZMod 3329`. Used by
    L6.4 `subtract_reduce`. -/
def bit_sub (p q : MontPoly) : MontPoly :=
  Vector.ofFn (n := 256) fun i => p[i] - q[i]

/-! ### #3 — Barrett reduce (identity on `ZMod 3329`) -/

/-- `#3 bit_barrett_reduce`: identity on `ZMod 3329`, because Barrett
    reduction takes an `I16` in `[-q·t, q·t]` and returns its
    canonical residue mod q, which is the same `ZMod 3329` element. -/
def bit_barrett_reduce (p : MontPoly) : MontPoly := p

/-! ### #4-5 — multiply by constant (real bodies, 5 LOC each) -/

/-- `#4 bit_montgomery_multiply_by_constant`: pointwise `(p, c) ↦
    p · c · R⁻¹` in `ZMod 3329`. The `R⁻¹` factor is already absorbed
    by the calling convention — the constant `c` is passed in the
    Montgomery domain (`c · R`), so `c · R · R⁻¹ = c` and the result is
    `p · c`. -/
def bit_montgomery_multiply_by_constant (p : MontPoly) (c : ZMod 3329) :
    MontPoly :=
  Vector.ofFn (n := 256) fun i => p[i] * c

/-- `#5 bit_multiply_by_constant`: pointwise `(p, c) ↦ p · c` in
    `ZMod 3329` (no Mont stripping; both operands in plain domain). -/
def bit_multiply_by_constant (p : MontPoly) (c : ZMod 3329) : MontPoly :=
  Vector.ofFn (n := 256) fun i => p[i] * c

/-! ### #6 — to_unsigned_representative (identity on `ZMod 3329`) -/

/-- `#6 bit_to_unsigned_representative`: identity on `ZMod 3329`. The
    underlying impl reduces a signed I16 to its `[0, q)` canonical
    representative, which is the same `ZMod 3329` element. -/
def bit_to_unsigned_representative (p : MontPoly) : MontPoly := p

/-! ### #7 — to_standard_domain (× R, equivalently × 2285 in canonical
    form / × 1353 via the mont representation) -/

/-- `#7 bit_to_standard_domain`: pointwise `(p) ↦ p · R` in
    `ZMod 3329`. In the hacspec spec, this is `compose with
    montgomery_multiply(·, 1353)`, where `1353 = R² mod q` (B.4) —
    composing with one mont reduce strips one `R⁻¹` and leaves
    `· R²·R⁻¹ = · R`. -/
def bit_to_standard_domain (p : MontPoly) : MontPoly :=
  Vector.ofFn (n := 256) fun i => p[i] * (2285 : ZMod 3329)

/-! ### #8-12 — NTT layer family (STUBBED, real bodies) -/

/-- `#8 bit_ntt_layer_1` STUB. Real body: a butterfly pass over 128
    `(a, b)` pairs spaced 128 apart, using the layer-1 zetas
    `Vector (ZMod 3329) 64`. M.4 fills the real body. -/
def bit_ntt_layer_1 (p : MontPoly) (_zetas : Vector (ZMod 3329) 64) :
    MontPoly := p
  -- replace with real butterfly-pass body.

/-- `#9 bit_ntt_layer_2` STUB. Real body: butterfly pass spaced 64,
    32-zeta argument. M.4 fills the real body. -/
def bit_ntt_layer_2 (p : MontPoly) (_zetas : Vector (ZMod 3329) 32) :
    MontPoly := p
  -- replace with real butterfly-pass body.

/-- `#10 bit_ntt_layer_3` STUB. Real body: butterfly pass spaced 32,
    16-zeta argument. M.4 fills the real body. -/
def bit_ntt_layer_3 (p : MontPoly) (_zetas : Vector (ZMod 3329) 16) :
    MontPoly := p
  -- replace with real butterfly-pass body.

/-- `#11 bit_ntt_layer_4_to_7` STUB. Parametric over layer index
    `4 ≤ layer ≤ 7`; each layer halves the butterfly spacing. M.4
    fills the real body. -/
def bit_ntt_layer_4_to_7 (p : MontPoly) (_layer : Nat) : MontPoly := p
  -- replace with real layer-parametric butterfly body.

/-- `#12 bit_ntt` STUB. Real body: 7-fold composition of the layer
    NTT passes. M.4 fills the real body and proves equivalence to
    `Spec.ntt_pure`. -/
def bit_ntt (p : MontPoly) : MontPoly := p
  -- replace with `bit_ntt_layer_1 ∘ … ∘ bit_ntt_layer_4_to_7 7`.

/-! ### #13-17 — INTT family (STUBBED) -/

/-- `#13 bit_invert_ntt_layer_1` STUB. Real body: inverse-butterfly
    pass mirroring `bit_ntt_layer_1`. M.4 fills the real body. -/
def bit_invert_ntt_layer_1 (p : MontPoly) (_zetas : Vector (ZMod 3329) 64) :
    MontPoly := p
  -- replace with real inverse-butterfly body.

/-- `#14 bit_invert_ntt_layer_2` STUB. -/
def bit_invert_ntt_layer_2 (p : MontPoly) (_zetas : Vector (ZMod 3329) 32) :
    MontPoly := p
  -- replace with real inverse-butterfly body.

/-- `#15 bit_invert_ntt_layer_3` STUB. -/
def bit_invert_ntt_layer_3 (p : MontPoly) (_zetas : Vector (ZMod 3329) 16) :
    MontPoly := p
  -- replace with real inverse-butterfly body.

/-- `#16 bit_invert_ntt_layer_4_to_7` STUB. -/
def bit_invert_ntt_layer_4_to_7 (p : MontPoly) (_layer : Nat) : MontPoly := p
  -- replace with real layer-parametric inverse body.

/-- `#17 bit_invert_ntt_montgomery` STUB. Real body: 7-fold inverse
    composition WITHOUT the final `· 1441 · R⁻¹` normalization (the
    "INTT-Mont" form). The `bit_intt_mont_form_lane` predicate below
    is the load-bearing per-lane invariant for this output. -/
def bit_invert_ntt_montgomery (p : MontPoly) : MontPoly := p
  -- replace with real INTT-without-finalize body.

/-! ### #18-19 — multiply (STUBBED) -/

/-- `#18 bit_ntt_multiply_n` STUB. Real body: per-pair base-case
    multiply across 128 `(a₀, a₁, b₀, b₁)` quartets, using
    64-element zeta argument. M.4 fills the real body. -/
def bit_ntt_multiply_n (p q : MontPoly) (_zetas : Vector (ZMod 3329) 64) :
    MontPoly := p + q -- harmless placeholder; replaced
  -- replace with real per-pair base-case multiply body.

/-- `#19 bit_multiply_ntts` STUB. Real body: wrapper around
    `bit_ntt_multiply_n` with the hacspec zeta table. M.4 fills it. -/
def bit_multiply_ntts (p q : MontPoly) : MontPoly := p + q
  -- replace with real body.

/-! ### #20-23 — per-quartet base cases (STUBBED) -/

/-- `#20 bit_base_case_multiply_even`: per-quartet helper for
    `bit_ntt_multiply_n`. Real body: `a₀·b₀ + zeta·a₁·b₁`. M.4
    fills it. -/
def bit_base_case_multiply_even
    (_a0 _a1 _b0 _b1 _zeta : ZMod 3329) : ZMod 3329 := 0
  -- replace with `a0*b0 + zeta*a1*b1`.

/-- `#21 bit_base_case_multiply_odd`: per-quartet helper. Real body:
    `a₀·b₁ + a₁·b₀`. M.4 fills it. -/
def bit_base_case_multiply_odd
    (_a0 _a1 _b0 _b1 : ZMod 3329) : ZMod 3329 := 0
  -- replace with `a0*b1 + a1*b0`.

/-- `#22 bit_butterfly`: per-pair NTT butterfly. Real body:
    `(a + zeta·b, a - zeta·b)`. M.4 fills it. -/
def bit_butterfly (_zeta a b : ZMod 3329) :
    ZMod 3329 × ZMod 3329 := (a, b)
  -- replace with `(a + zeta*b, a - zeta*b)`.

/-- `#23 bit_inv_butterfly`: per-pair inverse butterfly. Real body:
    `((a+b)/2, zeta·(a-b)/2)` modulo the Mont-domain bookkeeping.
    M.4 fills it. -/
def bit_inv_butterfly (_zeta a b : ZMod 3329) :
    ZMod 3329 × ZMod 3329 := (a, b)
  -- replace with the real inv-butterfly body.

/-! ### #24-25 — poly ops (REAL where trivial, STUBBED where not) -/

/-- `#24 bit_add_to_ring_element`: pointwise add, same as `bit_add`.
    Provided as an alias for the L7.2 caller chain. -/
def bit_add_to_ring_element (p q : MontPoly) : MontPoly := bit_add p q

/-- `#25 bit_subtract_reduce`: pointwise `(p, q) ↦ (q - p) · (R/128)`
    in `ZMod 3329` — the L6.4 "subtract and finalize INTT" operation.
    The `R/128` factor is exactly `1441 · R⁻¹ = 512` (mod q) by
    `mont_128_169_512`. M.4 fills the real body. -/
def bit_subtract_reduce (p q : MontPoly) : MontPoly :=
  Vector.ofFn (n := 256) fun i => (q[i] - p[i]) * (512 : ZMod 3329)

/-! ### #26-29 — compress / decompress family (STUBBED) -/

/-- `#26 bit_compress`: compression by `d` bits. Real body: per-lane
    `(2^d · x + ⌈q/2⌉) / q mod 2^d`. M.4 fills it (the spec uses
    `Result` plumbing; the bit-side version is pure). -/
def bit_compress (_p : MontPoly) (_d : Nat) : Vector (ZMod 3329) 256 :=
  Vector.replicate 256 (0 : ZMod 3329)
  -- replace with real per-lane compression body; return type
  -- should be `Vector (Fin (2^d)) 256` in the final shape — using
  -- `Vector (ZMod 3329) 256` here as a uniform placeholder.

/-- `#27 bit_decompress`: inverse compression. Real body: per-lane
    `⌈q · y / 2^d⌉` for `y ∈ [0, 2^d)`. -/
def bit_decompress (_c : Vector (ZMod 3329) 256) (_d : Nat) : MontPoly :=
  Vector.replicate 256 (0 : ZMod 3329)
  -- replace with real per-lane decompression body.

/-- `#28 bit_compress_message`: compress with `d = 1`. -/
def bit_compress_message (p : MontPoly) : Vector (ZMod 3329) 256 :=
  bit_compress p 1

/-- `#29 bit_decompress_message`: decompress with `d = 1`. -/
def bit_decompress_message (c : Vector (ZMod 3329) 256) : MontPoly :=
  bit_decompress c 1

/-! ### #30-31 — byte encode / decode (STUBBED) -/

/-- `#30 bit_byte_encode`: serialize a poly with `d` bits per
    coefficient. Real body: bit-packing per FIPS-203. M.4 fills it
    (likely via `bv_decide`). The output size is `32 * d` bytes; the
    return type is parametric in `d` which makes a real signature
    awkward here, so we ship a uniform placeholder. -/
def bit_byte_encode (_p : MontPoly) (_d : Nat) : List Std.U8 := []
  -- real signature is `Vector Std.U8 (32 * d)`; replace
  -- with the bit-packing body.

/-- `#31 bit_byte_decode`: inverse of `bit_byte_encode`. -/
def bit_byte_decode (_bytes : List Std.U8) (_d : Nat) : MontPoly :=
  Vector.replicate 256 (0 : ZMod 3329)
  -- real signature is `Vector Std.U8 (32 * d) → MontPoly`;
  -- replace with the bit-unpacking body.

/-! ### #32 — cond_subtract_3329 (identity in `ZMod 3329`) -/

/-- `#32 bit_cond_subtract_3329`: identity on `ZMod 3329`. The impl
    conditionally subtracts `q = 3329` when the lane is ≥ q, which is
    a no-op modulo q. -/
def bit_cond_subtract_3329 (p : MontPoly) : MontPoly := p

/-! ### #33 — per-step helper (STUBBED) -/

/-- `#33 bit_ntt_layer_int_vec_step`: per-step helper extracted from
    the L3.4 inner-loop sketch. Apply a single butterfly group with
    spacing `group` and zeta `zeta`. M.4 fills the real body. -/
def bit_ntt_layer_int_vec_step
    (p : MontPoly) (_group : Nat) (_zeta : ZMod 3329) : MontPoly := p
  -- replace with the per-step butterfly body.

/-! ### #34 — accumulating multiply (STUBBED) -/

/-- `#34 bit_accumulating_ntt_multiply`: per-vector base case used by
    L2.8 (`accumulating_ntt_multiply`). Real body returns an
    accumulator update of 8 `(ZMod 3329)` values per call. M.4 fills
    the real body. -/
def bit_accumulating_ntt_multiply
    (_a _b : Vector (ZMod 3329) 8) (_acc : Vector (ZMod 3329) 8)
    (_zeta : ZMod 3329) : Vector (ZMod 3329) 8 :=
  Vector.replicate 8 (0 : ZMod 3329)
  -- replace with the per-pair base-case accumulator body.

/-! ## §B.4 Opaque predicates anchoring impl ↔ MontPoly per-lane facts -/

/-- "Lane carries an i16 in canonical Montgomery domain w.r.t. the
    spec FE `expected`": `(lane.val · 169) ≡ expected (mod 3329)`.

    Marked `@[irreducible]` so L0+ Triple body proofs don't
    accidentally unfold the predicate and trigger Z3 quantifier
    cascades — they reveal it explicitly via
    `bit_mont_form_lane_intro` / `…_reveal` below. -/
@[irreducible]
def bit_mont_form_lane (lane : Std.I16) (expected : ZMod 3329) : Prop :=
  ((lane.val : ZMod 3329) * 169) = expected

/-- "Lane carries an i16 in post-INTT-without-finalize Mont domain":
    `(lane.val · 2285) ≡ (expected · 128) (mod 3329)`, where `2285 ≡
    R (mod q)` (B.3) and `128` reflects the deferred 1/128 normalization
    from INTT.

    Marked `@[irreducible]` for the same reason as
    `bit_mont_form_lane`. -/
@[irreducible]
def bit_intt_mont_form_lane (lane : Std.I16) (expected : ZMod 3329) : Prop :=
  ((lane.val : ZMod 3329) * 2285) = expected * 128

/-! ### Per-chunk / per-poly wraps -/

/-- "Every lane of a 16-lane PortableVector chunk is in canonical Mont
    form w.r.t. the corresponding lane of the 16-element expected
    vector". Used by the chunk-level commutes in M.2 Block B. -/
def bit_mont_form_chunk
    (chunk : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (expected : Vector (ZMod 3329) 16) : Prop :=
  ∀ i : Fin 16, bit_mont_form_lane (chunk.elements.val[i.val]!) (expected[i.val])

/-- "Every lane of every chunk of the polynomial is in canonical Mont
    form w.r.t. the corresponding lane of the 256-element expected
    MontPoly". Used by the poly-level commutes in M.2 Block C. -/
def bit_mont_form_poly
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (expected : MontPoly) : Prop :=
  ∀ i : Fin 16, ∀ j : Fin 16,
    bit_mont_form_lane
      ((re.coefficients.val[i.val]!).elements.val[j.val]!)
      (expected[16 * i.val + j.val]'(by
        have hi : i.val < 16 := i.isLt
        have hj : j.val < 16 := j.isLt
        omega))

/-- Per-chunk INTT-Mont form, mirroring `bit_mont_form_chunk`. -/
def bit_intt_mont_form_chunk
    (chunk : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (expected : Vector (ZMod 3329) 16) : Prop :=
  ∀ i : Fin 16, bit_intt_mont_form_lane (chunk.elements.val[i.val]!) (expected[i.val])

/-- Per-poly INTT-Mont form, mirroring `bit_mont_form_poly`. -/
def bit_intt_mont_form_poly
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (expected : MontPoly) : Prop :=
  ∀ i : Fin 16, ∀ j : Fin 16,
    bit_intt_mont_form_lane
      ((re.coefficients.val[i.val]!).elements.val[j.val]!)
      (expected[16 * i.val + j.val]'(by
        have hi : i.val < 16 := i.isLt
        have hj : j.val < 16 := j.isLt
        omega))

/-! ### Reveal / intro lemmas for the opaque predicates.

    Mirrors the SHA-3 BitKeccak idiom (§5.7 Idiom 2): predicates are
    `@[irreducible]` and consumers reveal them via these named
    lemmas, never via direct `unfold`. -/

theorem bit_mont_form_lane_intro (lane : Std.I16) (expected : ZMod 3329)
    (h : ((lane.val : ZMod 3329) * 169) = expected) :
    bit_mont_form_lane lane expected := by
  unfold bit_mont_form_lane; exact h

theorem bit_mont_form_lane_reveal (lane : Std.I16) (expected : ZMod 3329)
    (h : bit_mont_form_lane lane expected) :
    ((lane.val : ZMod 3329) * 169) = expected := by
  unfold bit_mont_form_lane at h; exact h

theorem bit_intt_mont_form_lane_intro (lane : Std.I16) (expected : ZMod 3329)
    (h : ((lane.val : ZMod 3329) * 2285) = expected * 128) :
    bit_intt_mont_form_lane lane expected := by
  unfold bit_intt_mont_form_lane; exact h

theorem bit_intt_mont_form_lane_reveal (lane : Std.I16) (expected : ZMod 3329)
    (h : bit_intt_mont_form_lane lane expected) :
    ((lane.val : ZMod 3329) * 2285) = expected * 128 := by
  unfold bit_intt_mont_form_lane at h; exact h

/-! ## §B.5 Bridge lemmas — `to_spec_poly_*` projection lemmas.

    These collapse the `Vector.ofFn` definition of the lift back to the
    per-lane formula. The four lemmas cover {plain, mont} × {chunk,
    poly} and are used by M.2 / M.4 to push the lift inside per-lane
    arithmetic.
-/

/-- Plain-domain poly lift unfolds to the per-lane formula at index
    `16 i + j` for `i, j < 16`. -/
theorem lemma_to_spec_poly_plain_unfold
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (i j : Fin 16) :
    (to_spec_poly_plain re)[16 * i.val + j.val]'(by
        have hi : i.val < 16 := i.isLt
        have hj : j.val < 16 := j.isLt
        omega)
      = i16_to_spec_fe_plain
          ((re.coefficients.val[i.val]!).elements.val[j.val]!) := by
  unfold to_spec_poly_plain
  -- `Vector.getElem_ofFn` rewrites the LHS to the body of `ofFn`.
  simp only [Vector.getElem_ofFn]
  -- Reduce `(16*i+j)/16` to `i` and `(16*i+j)%16` to `j` via `omega`.
  have hi : i.val < 16 := i.isLt
  have hj : j.val < 16 := j.isLt
  have hdiv : (16 * i.val + j.val) / 16 = i.val := by omega
  have hmod : (16 * i.val + j.val) % 16 = j.val := by omega
  rw [hdiv, hmod]

/-- Mont-domain poly lift unfolds to the per-lane formula. -/
theorem lemma_to_spec_poly_mont_unfold
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (i j : Fin 16) :
    (to_spec_poly_mont re)[16 * i.val + j.val]'(by
        have hi : i.val < 16 := i.isLt
        have hj : j.val < 16 := j.isLt
        omega)
      = i16_to_spec_fe_mont
          ((re.coefficients.val[i.val]!).elements.val[j.val]!) := by
  unfold to_spec_poly_mont
  simp only [Vector.getElem_ofFn]
  have hi : i.val < 16 := i.isLt
  have hj : j.val < 16 := j.isLt
  have hdiv : (16 * i.val + j.val) / 16 = i.val := by omega
  have hmod : (16 * i.val + j.val) % 16 = j.val := by omega
  rw [hdiv, hmod]

/-- Plain-domain poly lift agrees lane-by-lane with any
    pointwise-defined function that matches at every `(i, j)`. Used by
    M.2 chunk/poly commutes to lift a Block-A lane fact to the full
    256-element vector. -/
theorem lemma_to_spec_poly_plain_eq_of_coeffs
    (re re' : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h : ∀ i j : Fin 16,
            i16_to_spec_fe_plain
              ((re.coefficients.val[i.val]!).elements.val[j.val]!)
            = i16_to_spec_fe_plain
              ((re'.coefficients.val[i.val]!).elements.val[j.val]!)) :
    to_spec_poly_plain re = to_spec_poly_plain re' := by
  unfold to_spec_poly_plain
  apply Vector.ext
  intro k hk
  simp only [Vector.getElem_ofFn]
  -- Decompose k = 16 * (k/16) + (k%16) with k/16 < 16 and k%16 < 16.
  have hdiv_lt : k / 16 < 16 := by omega
  have hmod_lt : k % 16 < 16 := Nat.mod_lt k (by decide)
  exact h ⟨k / 16, hdiv_lt⟩ ⟨k % 16, hmod_lt⟩

/-- Mont-domain analogue of `lemma_to_spec_poly_plain_eq_of_coeffs`. -/
theorem lemma_to_spec_poly_mont_eq_of_coeffs
    (re re' : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h : ∀ i j : Fin 16,
            i16_to_spec_fe_mont
              ((re.coefficients.val[i.val]!).elements.val[j.val]!)
            = i16_to_spec_fe_mont
              ((re'.coefficients.val[i.val]!).elements.val[j.val]!)) :
    to_spec_poly_mont re = to_spec_poly_mont re' := by
  unfold to_spec_poly_mont
  apply Vector.ext
  intro k hk
  simp only [Vector.getElem_ofFn]
  have hdiv_lt : k / 16 < 16 := by omega
  have hmod_lt : k % 16 < 16 := Nat.mod_lt k (by decide)
  exact h ⟨k / 16, hdiv_lt⟩ ⟨k % 16, hmod_lt⟩

end libcrux_iot_ml_kem.Spec