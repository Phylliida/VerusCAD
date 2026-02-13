# VerusCAD
VerusCAD is a from-scratch CAD kernel in Rust with Verus proofs.

The short-term goal is a minimal, verified 2D sketch kernel that can become the foundation for 3D modeling.

## First milestone scope
Build a verified 2D core that can:

1. Represent points, vectors, segments, and simple polygons using exact arithmetic.
2. Check key validity properties (non-zero vectors, non-degenerate segments, simple closed polygons).
3. Compute basic derived values (orientation, area, bounding boxes) with machine-checked correctness.
4. Provide a small set of geometric predicates that later topology/modeling code can trust.

## Minimal primitives (proposal)
These are the smallest building blocks worth implementing first.

1. `Scalar` (exact rational)
Purpose: deterministic, proof-friendly arithmetic.
Proof focus: normalized representation (`den > 0`, reduced fraction), closure under `+ - * /` where defined.

2. `Vec2` and `Point2`
Purpose: 2D affine geometry.
Proof focus: point/vector algebra laws (identity, associativity where relevant), no invalid states.

3. `Segment2`
Purpose: first curve primitive.
Proof focus: endpoints are distinct, midpoint lies on segment, segment length is non-negative.

4. `Aabb2`
Purpose: broad-phase spatial checks.
Proof focus: `min <= max` per axis, enclosure predicates are sound.

5. `SimplePolygon2`
Purpose: first area-bearing sketch region.
Proof focus: closed loop, no self-intersections, signed-area relationship with orientation.

6. Core predicates/functions
`orient2d`, `point_on_segment`, `segment_intersection`, `polygon_area`.
Proof focus: each implementation matches its mathematical spec.

## Folder layout
```text
VerusCAD/
  README.md
  docs/
    primitives.md       # primitive definitions, invariants, and proof obligations
    roadmap.md          # phased build plan
    proof-guidelines.md # conventions for specs, exec code, and lemmas
  crates/
    README.md           # planned crate split
    vcad-math/
      README.md
    vcad-geometry/
      README.md
    vcad-sketch/
      README.md
    vcad-topology/
      README.md
    vcad-kernel/
      README.md
    vcad-cli/
      README.md
  examples/
    README.md
  tests/
    README.md
  scripts/
    README.md
```

## Why this split
1. `vcad-math` stays small and heavily proved. Everything else depends on it.
2. `vcad-geometry` centralizes geometric predicates and geometric-meaning theorems, reusing `vcad-math`.
3. `vcad-sketch` owns 2D entities and sketch-level constraints.
4. `vcad-topology` introduces IDs, incidence, and manifold-style constraints.
5. `vcad-kernel` hosts modeling operations built on the verified lower layers.
6. `vcad-cli` gives a simple executable surface for demos and regression checks.

## Next implementation target
Start with `vcad-math` and prove:

1. normalized `Scalar`,
2. `Vec2` operations and dot/cross properties,
3. `orient2d` correctness.

After that, add `Segment2` and `SimplePolygon2`.

See `docs/primitives.md` and `docs/roadmap.md` for the detailed plan.

## Local setup
For this repository's Verus workflow, see:

1. `docs/verus-setup.md`
2. `scripts/setup-verus.sh`
3. `scripts/verify-vcad-math.sh`
