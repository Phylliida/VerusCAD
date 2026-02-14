# vcad-geometry Verification TODO
Goal: remove trusted proof boundaries so all `vcad-geometry` runtime behavior is justified by explicit specs + proofs.

## Baseline Snapshot (2026-02-13)
- [x] `vcad-geometry` verifies with `verus-proofs` enabled (`87 verified, 0 errors`).
- [x] Trusted refinement assumptions removed (`assume_specification[...]` no longer present in `src/`).
- [x] Sign wrapper APIs have explicit proof contracts.

## Recommended Work Order
- [x] 1) Orientation runtime boundary.
- [x] 2) Collinearity/coplanarity boundary.
- [x] 3) Sidedness boundary.
- [x] 4) Convex polygon boundary.
- [x] 5) Final de-trusting and verification gate.

## A. Orientation Runtime Boundary
File: `src/runtime_orientation_predicates_refinement.rs`
- [x] Replace `assume_specification[ orientation_predicates::orient2d_value ]` with proved refinement.
- [x] Replace `assume_specification[ orientation_predicates::orient3d_value ]` with proved refinement.
- [x] Replace `assume_specification[ orientation_predicates::orient2d_class ]` with proved refinement.
- [x] Replace `assume_specification[ orientation_predicates::orient3d_class ]` with proved refinement.

File: `src/orientation_predicates.rs`
- [x] Add/verify spec+proof bridge for `orient2d_sign` (exact sign relation to `orient2d_spec`).
- [x] Add/verify spec+proof bridge for `orient3d_sign` (exact sign relation to `orient3d_spec`).

## B. Collinearity/Coplanarity Runtime Boundary
File: `src/runtime_collinearity_coplanarity_refinement.rs`
- [x] Replace `assume_specification[ collinearity_coplanarity::collinear2d ]` with proved refinement.
- [x] Replace `assume_specification[ collinearity_coplanarity::collinear3d ]` with proved refinement.
- [x] Replace `assume_specification[ collinearity_coplanarity::coplanar ]` with proved refinement.

## C. Sidedness Runtime Boundary
File: `src/runtime_sidedness_refinement.rs`
- [x] Replace `assume_specification[ sidedness::point_above_plane ]` with proved refinement.
- [x] Replace `assume_specification[ sidedness::point_below_plane ]` with proved refinement.
- [x] Replace `assume_specification[ sidedness::point_on_plane ]` with proved refinement.
- [x] Replace `assume_specification[ sidedness::segment_crosses_plane_strict ]` with proved refinement.
- [x] Replace `assume_specification[ sidedness::segment_plane_intersection_parameter_strict ]` with proved refinement.
- [x] Replace `assume_specification[ sidedness::segment_plane_intersection_point_strict ]` with proved refinement.

## D. Convex Polygon Runtime Boundary
File: `src/runtime_convex_polygon_refinement.rs`
- [x] Replace `assume_specification[ convex_polygon::point_in_convex_polygon_2d ]` with proved refinement.
- [x] Replace `assume_specification[ convex_polygon::point_strictly_in_convex_polygon_2d ]` with proved refinement.

## E. Completion Gates
- [x] `rg -n "assume_specification\\[" crates/vcad-geometry/src` shows no trusted assumptions for `vcad-geometry` runtime behavior.
- [x] Full crate verification succeeds:
  - `cargo verus verify --manifest-path crates/vcad-geometry/Cargo.toml -p vcad-geometry --features verus-proofs -- --triggers-mode silent`
- [x] Keep/extend runtime unit tests for representative geometric cases while proofs are being migrated.

## F. Proof Quality Hardening
- [x] Remove termination waivers from `vcad-geometry` proof code:
  - `rg -n "exec_allows_no_decreases_clause" crates/vcad-geometry/src` returns no matches.
  - Loop termination is justified with explicit `decreases` clauses in convex polygon proofs.
- [x] Reduce witness-proof duplication and make quantifier instantiation explicit:
  - Reuse helper lemmas for existential witness construction in sidedness refinements.
  - Keep explicit `#[trigger]` terms on witness point-parameter predicates.

## G. Next Geometry Kernel Backlog (2026-02-14)
Goal: add high-value geometric predicates/constructions that are currently not covered by `vcad-topology` (which focuses on combinatorial half-edge validity).

## Recommended Build Order (Phase 5+)
- [ ] 1) 2D segment-segment intersection classification.
- [ ] 2) General (non-convex) point-in-polygon classification.
- [ ] 3) 3D segment/ray-triangle intersection with barycentric witness.
- [ ] 4) 2D convex polygon clipping/intersection.
- [ ] 5) Distance/projection kernels.
- [ ] 6) Triangle primitives + normal/area consistency lemmas.
- [ ] 7) Typed classification enums for geometry relations.
- [ ] 8) Affine invariance lemmas (translation/scaling, with sign effects).

## H. 2D Segment-Segment Intersection (Start Here)
Proposed file: `src/segment_intersection.rs` (+ `src/runtime_segment_intersection_refinement.rs` if runtime/proof split is needed)
- [ ] Define relation enum (disjoint/proper/endpoint/collinear-overlap).
- [ ] Add exact spec predicates for each case and prove mutual exclusivity.
- [ ] Implement runtime classifier and prove refinement to spec.
- [ ] Add witness extraction API for intersection point(s) where applicable.
- [ ] Add representative runtime tests (crossing, touching endpoint, parallel disjoint, overlap).

## I. General Point-in-Polygon
Proposed file: `src/polygon_general.rs`
- [ ] Define boundary-inclusive and strict-inside specs for simple polygons.
- [ ] Implement ray-crossing (or winding) runtime algorithm with exact arithmetic.
- [ ] Prove runtime result matches spec classification.
- [ ] Add handling for boundary edge/vertex hits as explicit cases.

## J. Segment/Ray-Triangle (3D)
Proposed file: `src/triangle_intersection.rs`
- [ ] Define spec for intersection existence and barycentric witness constraints.
- [ ] Implement segment-triangle intersection using exact orientation/sidedness predicates.
- [ ] Implement ray-triangle variant and prove implication relations.
- [ ] Prove witness validity (on segment/ray and inside triangle).

## K. Convex Polygon Clipping / Intersection
Proposed file: `src/convex_polygon_clip.rs`
- [ ] Define spec for output polygon validity and point-membership equivalence.
- [ ] Implement clipping pipeline (Sutherland-Hodgman style with exact arithmetic).
- [ ] Prove closure/invariant lemmas per clipping step.
- [ ] Add runtime tests for empty/partial/full containment cases.

## L. Distance / Projection Kernels
Proposed file: `src/distance_projection.rs`
- [ ] Add `point_segment_dist2`, `point_plane_signed_distance_num`, and projection parameter APIs.
- [ ] Specify exact relationships (non-negativity, zero-iff, clamping/witness bounds).
- [ ] Prove core algebraic lemmas linking dot products and squared distances.

## M. Cross-Cutting Proof Layer
Proposed file: `src/geometry_relations.rs` and/or lemma modules
- [ ] Introduce shared relation enums used by multiple predicates.
- [ ] Add affine invariance lemmas reused by intersection and polygon proofs.
- [ ] Keep fast-script defaults updated as new modules land.
- [ ] Gate each milestone with:
  - `./scripts/verify-vcad-geometry-fast.sh <module>`
  - `./scripts/verify-vcad-geometry.sh`
