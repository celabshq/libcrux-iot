-- ML-DSA `PolynomialRingElement` layer: impl ↔ spec equivalence (aeneas-lean).
-- See `LibcruxIotMlDsa/README.md` for the top-level theorems and trust boundary.

-- Self-contained spec reference (clean Z_q) — builds without an extraction.
import LibcruxIotMlDsa.Spec.Parameters
import LibcruxIotMlDsa.Spec.Montgomery
import LibcruxIotMlDsa.Spec.Pure
import LibcruxIotMlDsa.Spec.Lift
-- Build-time spec validation (round-trip + Rust ZETAS cross-check, axiom-free).
import LibcruxIotMlDsa.Spec.Validation

-- The machine-EXTRACTED clean-Z_q ML-DSA hacspec.
-- The poly-layer spec-bridge lemmas prove the hand `Spec.Pure.*`
-- equals these `hacspec_ml_dsa.*` defs, so the extracted spec — not the hand
-- spec — is the trusted reference.
import HacspecMlDsa.Extraction.Funs

-- Extraction + generic Util specs.
import LibcruxIotMlDsa.Extraction.Funs
import LibcruxIotMlDsa.Util.SliceSpecs
import LibcruxIotMlDsa.Util.LoopSpecs
-- L0 scalar Montgomery reduction keystone (montgomery_reduce_element_spec).
import LibcruxIotMlDsa.Vector.Portable.Arithmetic
-- L1 elementwise loop infra + Coefficients add/subtract Triples.
import LibcruxIotMlDsa.Util.LoopHelper
import LibcruxIotMlDsa.Vector.Portable.Element
import LibcruxIotMlDsa.Vector.Portable.Ntt           -- L2 butterflies
import LibcruxIotMlDsa.Vector.Portable.InvNtt        -- L0 inverse butterflies
import LibcruxIotMlDsa.Vector.Portable.NttDriver     -- L3 forward NTT layer drivers
import LibcruxIotMlDsa.Vector.Portable.InvNttDriver  -- L2 inverse NTT within-unit driver
import LibcruxIotMlDsa.Vector.Portable.NttMaster     -- forward NTT master (8-layer compose)
import LibcruxIotMlDsa.Vector.Portable.InvNttMaster  -- inverse NTT master (8-layer + finalize)
import LibcruxIotMlDsa.Vector.Portable.Rounding      -- decompose dual-output keystone
import LibcruxIotMlDsa.Polynomial.Ntt                -- poly-layer NTT FCs (ntt / invert_ntt_montgomery)
import LibcruxIotMlDsa.Polynomial.Arithmetic         -- poly-layer add / subtract FCs
import LibcruxIotMlDsa.Polynomial.NttArith            -- poly-layer ntt_multiply_montgomery / reduce FCs
import LibcruxIotMlDsa.Polynomial.Convert             -- poly-layer zero / to_i32_array / from_i32_array FCs
import LibcruxIotMlDsa.Polynomial.InfinityNorm        -- poly-layer infinity_norm_exceeds rejection FC (bug-fixed)
-- Spec-extraction: hand spec = EXTRACTED hacspec bridge + extracted-hacspec FCs.
import LibcruxIotMlDsa.Spec.HacspecBridge              -- createi/mod_q/lift_res + poly_{add,sub,mul} hand↔extracted bridges
import LibcruxIotMlDsa.Polynomial.HacspecFC            -- @[spec] poly_{add,sub,mul}_hacspec_fc (extracted-spec posts)
import LibcruxIotMlDsa.Polynomial.HacspecNtt           -- ntt/intt_layer + ntt/intt bridges + @[spec] ntt/intt_hacspec_fc
import LibcruxIotMlDsa.Polynomial.HacspecNorm          -- coeff_norm/poly_infinity_norm bridges + @[spec] infinity_norm_exceeds_hacspec_fc
