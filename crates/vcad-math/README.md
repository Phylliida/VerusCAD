# vcad-math
Lowest-level verified math crate.

Planned contents:
1. `Scalar` (exact rational).
2. `Vec2` and `Point2`.
3. Predicates like `orient2d`.

This crate should have no dependency on higher CAD concepts.

## Current Status (2026-02-12)
`vcad-math` is in an active migration from integer-backed `Scalar` to rational-backed `Scalar`.

Current code is modular:
1. `src/scalar.rs`
2. `src/vec2.rs`
3. `src/point2.rs`
4. `src/orientation.rs`
5. `src/lib.rs` module/export entrypoint.

What is currently verified:
1. Rational `Scalar` representation (`num: int`, `den: nat` storing denominator-minus-one).
2. Core `Scalar` operations (`add/sub/mul/neg`) and sign classification (`signum`).
3. `Vec2`, `Point2`, and `orient2d` executable/spec constructors.
4. Orientation classification helpers and predicate/enum bridge lemmas.
5. End-to-end crate verification via `./scripts/verify-vcad-math.sh`.

What is intentionally in-progress:
1. Re-adding the full pre-migration theorem surface (vector-space, metric, determinant permutation/scaling suites).
2. Strengthening rational semantic-equivalence laws (`eqv_spec` and `as_real` bridges).
3. Deciding and proving normalization/canonical-form invariants.

Backups and migration checkpoints:
1. `crates/vcad-math/backups/2026-02-12-rational-migration-pause/`
2. `docs/vcad-math-todo.md`
3. `docs/vcad-math-roadmap.md`
