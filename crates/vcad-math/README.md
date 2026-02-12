# vcad-math
Lowest-level verified math crate.

Core contents:
1. `Scalar` (exact rational).
2. `RuntimeScalar` (exec rational backed by `rug::Rational`).
3. `Vec2` and `Point2`.
4. Predicates like `orient2d`.

This crate should have no dependency on higher CAD concepts.

## Current Status (2026-02-12)
`vcad-math` is now running on a rational-backed `Scalar` (`num: int`, `den: nat` with effective denominator `den + 1`), and the currently tracked theorem surface is restored and verified.

Current code is modular:
1. `src/scalar.rs`
2. `src/vec2.rs`
3. `src/point2.rs`
4. `src/orientation.rs`
5. `src/runtime_scalar.rs`
6. `src/runtime_scalar_refinement.rs`
7. `src/lib.rs` module/export entrypoint.

Verified theorem surface:
1. `Scalar` algebra/order/sign laws:
   - commutativity/associativity/identities/inverses/distributivity,
   - semantic equality (`eqv_spec`) reflexive/symmetric/transitive + congruence,
   - cancellation and monotonicity lemmas (`requires`-style strong forms plus implication wrappers),
   - signum laws including multiplication behavior,
   - normalization/sign bridge lemmas (`normalized_spec`, normalized uniqueness, normalized `eqv` -> structural equality, canonical sign placement for normalized rationals).
2. `Vec2` vector-space and bilinear laws:
   - add/neg/sub/scale laws,
   - dot/cross symmetry, antisymmetry, bilinearity, scale extraction,
   - `norm2` nonnegativity, scaling law, and zero-iff-zero.
3. `Point2` affine and metric laws:
   - add/sub cancellation and uniqueness,
   - translation invariance,
   - `dist2` symmetry/nonnegativity/self-zero/zero-iff-equality,
   - `dist2(p, q) == norm2(p - q)` bridge.
4. Orientation/determinant laws:
   - predicate bridges and enum exclusivity,
   - swap/cyclic/permutation theorems,
   - translation and uniform-scale behavior theorems.
5. Compatibility wrappers for common pre-rational names:
   - `lemma_ccw_swap_to_cw`,
   - `Vec2::lemma_eq_from_component_ints`,
   - `Point2::lemma_eq_from_component_ints`.
6. Runtime backend:
   - `RuntimeScalar` uses `rug::Rational` for arbitrary-precision executable arithmetic.
   - equivalent values compare equal and hash equal via canonical rational form.
   - explicit runtime `normalize()` entrypoint is available for canonicalization.
   - Verus refinement contracts are provided for `from_int`, `from_fraction`, `add`, `sub`, `mul`, `neg`, and `normalize` via `RuntimeScalar`'s model `view`.
   - refinement contracts are trusted specs at the external backend boundary (`rug` implementation).
   - verified regression wrappers validate contract composition for commutativity (`add`, `mul`), `sub == add(neg)`, and normalization identity.
Verification status:
1. End-to-end crate verification via `./scripts/verify-vcad-math.sh` is green (`276 verified, 0 errors` in the latest run).

Intentionally deferred (roadmap):
1. Canonical rational normalization proofs (gcd/sign canonical form and uniqueness).
2. Optional exec/spec dual-mode API hardening and proof regression harness.

Backups and migration checkpoints:
1. `crates/vcad-math/backups/2026-02-12-rational-migration-pause/`
2. `docs/vcad-math-todo.md`
3. `docs/vcad-math-roadmap.md`
4. `docs/scalar-unification-todo.md`
