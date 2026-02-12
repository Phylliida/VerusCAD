# vcad-math
Lowest-level verified math crate.

Core contents:
1. `Scalar` (exact rational).
2. `Vec2` and `Point2`.
3. Predicates like `orient2d`.

This crate should have no dependency on higher CAD concepts.

## Current Status (2026-02-12)
`vcad-math` is now running on a rational-backed `Scalar` (`num: int`, `den: nat` with effective denominator `den + 1`), and the currently tracked theorem surface is restored and verified.

Current code is modular:
1. `src/scalar.rs`
2. `src/vec2.rs`
3. `src/point2.rs`
4. `src/orientation.rs`
5. `src/lib.rs` module/export entrypoint.

Verified theorem surface:
1. `Scalar` algebra/order/sign laws:
   - commutativity/associativity/identities/inverses/distributivity,
   - semantic equality (`eqv_spec`) reflexive/symmetric/transitive + congruence,
   - cancellation and monotonicity lemmas (`requires`-style strong forms plus implication wrappers),
   - signum laws including multiplication behavior.
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

Verification status:
1. End-to-end crate verification via `./scripts/verify-vcad-math.sh` is green (`262 verified, 0 errors` in the latest run).

Intentionally deferred (roadmap):
1. Canonical rational normalization proofs (gcd/sign canonical form and uniqueness).
2. Optional exec/spec dual-mode API hardening and proof regression harness.

Backups and migration checkpoints:
1. `crates/vcad-math/backups/2026-02-12-rational-migration-pause/`
2. `docs/vcad-math-todo.md`
3. `docs/vcad-math-roadmap.md`
