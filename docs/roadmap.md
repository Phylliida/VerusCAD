# Roadmap
Phased plan for building VerusCAD from minimal verified primitives upward.

## Phase 0: Scaffolding
Deliverables:
1. Repository layout and architecture docs.
2. Crate boundaries defined.
3. Proof style conventions documented.

Exit criteria:
1. Team can point to one canonical plan for primitives and proofs.

## Phase 1: Verified math core (`vcad-math`)
Deliverables:
1. `Scalar` with normalization invariant.
2. `Vec2` and `Point2` with core algebra operations.
3. `orient2d` plus basic lemmas.

Exit criteria:
1. Core algebra operations verify.
2. Orientation predicate is proved against its spec.

## Phase 2: Verified sketch geometry (`vcad-sketch`)
Deliverables:
1. `Segment2`, `Aabb2`, `SimplePolygon2`.
2. Predicates: `point_on_segment`, segment intersection.
3. Area and bounding box utilities with proofs.

Exit criteria:
1. Segment and polygon validity checks verify.
2. Area and intersection routines verify under documented preconditions.

## Phase 3: Topology foundation (`vcad-topology`)
Deliverables:
1. IDs and incidence maps for vertex/edge/face.
2. `Wire` and `Face` validity invariants.
3. Construction helpers that preserve invariants.

Exit criteria:
1. Topology construction API enforces consistency by proof.

## Phase 4: Kernel operations (`vcad-kernel`)
Deliverables:
1. Minimal modeling operations built on verified primitives.
2. First operation target: verified extrusion from `SimplePolygon2` to a prism-like solid model.

Exit criteria:
1. Operation correctness statements are verified.
2. Regression examples capture expected behavior.

## Phase 5: Tooling (`vcad-cli`, tests, examples)
Deliverables:
1. Command-line playground for sample operations.
2. Proof regression checks in CI.
3. Examples that double as executable documentation.

Exit criteria:
1. New contributors can run examples and verification checks with documented commands.
