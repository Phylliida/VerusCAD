# vcad-math
Lowest-level verified math crate.

Planned contents:
1. `Scalar` (exact rational).
2. `Vec2` and `Point2`.
3. Predicates like `orient2d`.

This crate should have no dependency on higher CAD concepts.

## Prototype status
First prototype now exists in `src/lib.rs` with:
1. `Scalar` backed by exact integers (temporary stand-in for rationals),
2. verified `Vec2` dot/cross operations,
3. verified `Point2` subtraction/addition with vectors,
4. verified `orient2d`.
5. proof/spec-oriented APIs (not exec runtime APIs yet).
6. proved law sets:
   - `Scalar`: commutativity, associativity, distributivity, identities, inverse/sub relation, cancellation, zero-product, order monotonicity, and signum interaction (`signum(-a)`, `signum(a*b)`)
   - `Vec2`: add identities/associativity/commutativity, left/right dot/cross linearity, scale extraction for dot/cross, additive inverse, negation/scale compatibility, `v x v = 0`
   - `Point2`: add/sub cancellation, translation identity/associativity, uniqueness of translation vectors
   - `orient2d`: swap antisymmetry, cyclic invariance, translation invariance, full 6-permutation table, uniform-scaling behavior, degeneracy with repeated points
7. orientation classification helpers:
   - `is_ccw`, `is_cw`, `is_collinear`
   - plus proofs of equivalence to orientation sign, exhaustive/disjoint classification, and swap behavior
8. first-class orientation classifier:
   - `Orientation` enum (`Cw | Collinear | Ccw`)
   - `orientation_spec` and proved `orientation` constructor with classification bridge lemmas
9. scalar sign helper:
   - `Scalar::signum` with proved equivalence lemmas to positive/negative/zero tests
   - orientation predicates now use signum-based classification
10. vector-space and metric seed layer:
   - `Vec2::scale_spec` with distributivity/associativity/identity lemmas
   - `Vec2::norm2_spec` and non-negativity proof
   - `dist2_spec(p, q)` with symmetry, translation invariance, and non-negativity proofs

Next step is upgrading `Scalar` internals from integer to normalized rational
while preserving the same geometry-facing APIs.

Current proof-lemma TODO status: complete (`docs/vcad-math-todo.md`).
Longer-horizon architecture milestones are tracked in `docs/vcad-math-roadmap.md`.
