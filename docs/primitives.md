# Primitive Plan
This document defines the minimal primitive set for a verified CAD foundation.

Current prototype note:
`vcad-math` currently uses an integer-backed `Scalar` to validate the proof
workflow quickly. The target design remains a normalized rational `Scalar`.

## Design constraints
1. Keep runtime data small and total functions explicit.
2. Make invalid states unrepresentable where practical.
3. Pair each executable function with a clear spec function and proof lemmas.
4. Prefer exact arithmetic over floating point in the verified core.

## Layer 0: Numeric base
### `Scalar`
Runtime idea: rational number, e.g. `(num: int, den: nat)`.

Required invariants:
1. `den > 0`.
2. Fraction is normalized (canonical sign and reduced by gcd).

Required proofs:
1. Normalization is idempotent.
2. Arithmetic operations preserve validity.
3. Equality in runtime representation matches mathematical equality.

## Layer 1: Geometry primitives
### `Vec2`
Runtime idea: `{ x: Scalar, y: Scalar }`.

Required proofs:
1. Addition/subtraction closure.
2. Dot product symmetry.
3. Cross product antisymmetry.

### `Point2`
Runtime idea: `{ x: Scalar, y: Scalar }`.

Required proofs:
1. `Point2 + Vec2 -> Point2` correctness.
2. `Point2 - Point2 -> Vec2` correctness.

### `Segment2`
Runtime idea: `{ a: Point2, b: Point2 }`.

Required invariant:
1. `a != b`.

Required proofs:
1. Parametric point construction stays on segment for `t in [0,1]`.
2. Bounding box encloses both endpoints.

### `Aabb2`
Runtime idea: `{ min: Point2, max: Point2 }`.

Required invariants:
1. `min.x <= max.x`.
2. `min.y <= max.y`.

Required proofs:
1. `contains(p)` is sound.
2. Merge/union preserves invariants.

### `SimplePolygon2`
Runtime idea: ordered vertex sequence.

Required invariants:
1. At least 3 distinct vertices.
2. Closed loop semantics.
3. Non-self-intersection.

Required proofs:
1. Shoelace area function matches spec area definition.
2. Orientation sign agrees with area sign.

## Layer 2: Topology seed types
Keep these minimal at first.

### `VertexId`, `EdgeId`, `FaceId`
Purpose: stable references for topology maps.
Proof focus: index validity and map consistency.

### `Wire`
Runtime idea: cyclic sequence of oriented edges.
Proof focus: adjacency consistency and closure.

### `Face`
Runtime idea: outer wire plus optional inner wires.
Proof focus: hole containment and boundary disjointness.

## Kernel predicates to prioritize
1. `orient2d(a, b, c)` with correctness relative to signed area.
2. `point_on_segment(p, s)` with endpoint and collinearity cases.
3. `segment_intersection(s1, s2)` with soundness and completeness over finite segments.
4. `polygon_area(poly)` with validity assumptions made explicit.

## Out of scope for the first iteration
1. NURBS and high-order curves.
2. Floating-point tolerant geometry.
3. Full Boolean solid operations.
4. Advanced meshing and rendering.
