# vcad-topology Phase 5: Geometric-Topological Consistency TODO
Purpose: formally verify that mesh geometry and topology agree for closed solids, matching Phase 5 in `VerusCAD/docs/full-roadmap.md`.

## Scope
Phase 5 target from roadmap:
1. face coplanarity
2. face convexity
3. outward face-normal orientation
4. no face-face intersections except at shared edges/vertices
5. computed face planes are correct and orientation-consistent

This doc expands those targets into executable TODOs aligned with the current `vcad-topology` proof structure.

## Dependencies and Ground Rules
- [ ] Keep Phase 4 validity (`Mesh::is_valid`) as a required precondition for all Phase 5 geometric theorems/checkers.
- [x] Reuse `vcad-geometry` predicates/lemmas (`orient2d`, `orient3d`, coplanarity, side tests, intersection helpers) rather than duplicating math proofs in `vcad-topology`.
- [ ] Keep exact arithmetic path only (`RuntimePoint3`/`Scalar`); do not add floating-point fallback logic in verified paths.
- [ ] Remove trusted boundaries for any new Phase 5 APIs (no new `assume_specification` debt).

## P5.0 Geometry Model Surface
- [ ] Add mesh-geometry spec helpers that map each face cycle to ordered vertex positions.
- [ ] Add spec-level adjacency relations:
  - shared vertex
  - shared edge
  - disjoint boundary
- [ ] Add per-face non-degeneracy preconditions needed by Phase 5 predicates (at least one non-collinear triple per face).
- [ ] Add bridge specs from runtime mesh to any kernel geometry checker representation used for proofs.

## P5.1 Invariant: Face Coplanarity (Roadmap)
- [ ] Spec: define `mesh_face_coplanar_spec(m, f)` (equivalent to orient3d = 0 for all face-vertex quadruples).
- [ ] Spec: define aggregate `mesh_all_faces_coplanar_spec(m)`.
- [x] Runtime checker: implement `check_face_coplanarity` (or equivalent) over all faces.
- [ ] Proof: runtime checker correctness vs spec (sound + complete under documented preconditions).
- [ ] Proof: coplanarity is stable under cyclic reindexing of a face cycle.

## P5.2 Invariant: Edge Straightness (Implied by Phase 5 Intro)
- [ ] Spec: each half-edge geometrically denotes the segment between `vertex(h)` and `vertex(next(h))`.
- [ ] Spec: twin half-edges denote the same segment with opposite orientation.
- [x] Runtime checker: reject zero-length geometric edges (in addition to topological non-degeneracy).
- [ ] Proof: edge-geometry facts are derivable from mesh model + vertex positions.

## P5.3 Invariant: Face Convexity (Roadmap)
- [ ] Choose deterministic face-to-2D projection strategy for convexity tests (for example dominant-axis drop from face normal).
- [ ] Spec: projected consecutive `orient2d` signs are globally consistent per face.
- [ ] Runtime checker: implement `check_face_convexity`.
- [ ] Proof: runtime checker correctness vs convexity spec.
- [ ] Proof: convexity checker uses only legally projected points from a coplanar face.
- [ ] Proof: triangle faces satisfy convexity trivially.

## P5.4 Invariant: Outward Face Normals (Roadmap)
- [ ] Define oriented face-normal spec from face winding and plane normal.
- [ ] Define component-level outwardness criterion for closed meshes (document chosen witness, for example interior reference point / signed volume convention).
- [ ] Runtime checker: implement global orientation check (`check_outward_normals` or equivalent).
- [ ] Proof: local orientation consistency across adjacent faces via shared edges.
- [ ] Proof: global outwardness criterion implies all faces point outward for each closed component.

## P5.5 Invariant: No Self-Intersection Except Shared Boundary (Roadmap)
- [ ] Spec: define allowed contact relation between two faces (shared edge, shared vertex, or disjoint).
- [ ] Spec: define forbidden intersection relation for non-adjacent face pairs.
- [ ] Runtime checker: implement pairwise face intersection check with adjacency exemptions.
- [ ] Proof: checker soundness (if checker passes, forbidden intersections do not exist).
- [ ] Proof: checker completeness for convex coplanar-face assumptions used by Phase 5.
- [ ] Proof: shared-edge and shared-vertex contacts are never misclassified as forbidden intersections.

## P5.6 Plane Computation (Roadmap)
- [ ] Runtime API: compute face plane `(normal, offset)` from face vertices via cross product + dot product.
- [ ] Handle face-normal seed selection robustly (first non-collinear triple or explicit precondition).
- [ ] Spec: `face_plane_contains_vertex_spec` for every vertex on the face.
- [ ] Proof: computed plane contains all vertices of that face (using coplanarity invariant).
- [ ] Proof: computed normal direction matches face orientation/winding.
- [ ] Proof: twin/adjacent orientation interactions agree with plane-normal conventions.

## P5.7 Validity Gate Integration
- [x] Add an explicit Phase 5 aggregate predicate/checker, for example:
  - `mesh_geometric_topological_consistency_spec`
  - `Mesh::check_geometric_topological_consistency()`
- [x] Define final gate composition (for example `is_valid_phase5 = is_valid && geometric_consistency`).
- [x] Keep existing optional `geometry-checks` feature behavior coherent with new verified gate (document if Phase 5 stays feature-gated or becomes default).
- [ ] Prove aggregate checker equivalence to aggregate Phase 5 spec.

## P5.8 Proof-Layer Integration (Current Refinement Layout)
- [ ] Extend `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs` with Phase 5 geometry specs.
- [ ] Add Phase 5 bridge lemmas alongside `src/runtime_halfedge_mesh_refinement/kernel_bridge_lemmas.rs`.
- [ ] Add runtime constructive check wrappers analogous to current structural check wrappers.
- [ ] If kernelized checkers are added, extend `src/verified_checker_kernels.rs` and prove bridge equivalence.
- [ ] Ensure new proof modules are included from `src/runtime_halfedge_mesh_refinement.rs`.

## P5.9 Tests and Counterexamples
- [x] Positive fixtures: tetrahedron, cube, triangular prism pass Phase 5 gate.
- [x] Negative fixture: non-coplanar face fails coplanarity checker.
- [x] Negative fixture: zero-length geometric edge fails edge-straightness checker.
- [ ] Negative fixture: concave polygon face fails convexity checker.
- [ ] Negative fixture: flipped face winding fails outward-normal checker.
- [ ] Negative fixture: non-adjacent face intersection fails self-intersection checker.
- [x] Regression tests under:
  - default build
  - `--features geometry-checks`
  - `--features "geometry-checks,verus-proofs"`

## Burndown Log
- 2026-02-18: Follow-up validation pass reran the full `vcad-topology` matrix (`cargo test` default/`geometry-checks`/`geometry-checks,verus-proofs`, plus both fast verify scripts and full verify script) after landing the P5.2 zero-length edge checker; all remained green with no new failures.
- 2026-02-18: Implemented `Mesh::check_face_coplanarity()` in `src/halfedge_mesh/validation.rs`, using `vcad_geometry::collinearity_coplanarity::coplanar` on each face cycle with a fixed local `(a,b,c)` plane basis and checking all remaining face vertices against that plane.
- 2026-02-18: Added `Mesh::check_geometric_topological_consistency()` as a Phase-5-in-progress aggregate checker (initially `corner_non_collinearity && face_coplanarity`) and updated `Mesh::is_valid_with_geometry()` to require this aggregate.
- 2026-02-18: Extended `src/halfedge_mesh/tests.rs`:
  - positive fixtures (`tetrahedron`, `cube`, `triangular_prism`) now assert `check_face_coplanarity()` and the aggregate checker;
  - added `noncoplanar_quad_faces_fail_face_coplanarity` negative test;
  - strengthened collinear negative test to assert coplanarity can still pass while aggregate fails.
- 2026-02-18: Implemented `Mesh::check_no_zero_length_geometric_edges()` in `src/halfedge_mesh/validation.rs`, rejecting any half-edge whose endpoint vertex positions are exactly equal in `RuntimePoint3` exact arithmetic.
- 2026-02-18: Updated `Mesh::check_geometric_topological_consistency()` to require `check_no_zero_length_geometric_edges() && check_face_corner_non_collinearity() && check_face_coplanarity()`.
- 2026-02-18: Extended `src/halfedge_mesh/tests.rs` geometry coverage:
  - positive fixtures now also assert `check_no_zero_length_geometric_edges()`;
  - added `coincident_edge_endpoints_fail_zero_length_geometric_edge_check` as a P5.2 negative fixture;
  - documented that Phase 5 runtime geometric checks remain opt-in behind `--features geometry-checks` (core `Mesh::is_valid()` stays topology-only).
- 2026-02-18: Verification/test commands run after changes:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (192 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (227 verified, 0 errors)
- 2026-02-18: Failed attempts: none in this pass.

## Suggested File Landing Zones
- Runtime checks: `src/halfedge_mesh/validation.rs`
- Proof model/specs: `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`
- Bridge lemmas: `src/runtime_halfedge_mesh_refinement/kernel_bridge_lemmas.rs`
- Optional new refinement modules:
  - `src/runtime_halfedge_mesh_refinement/phase5_geometry_specs_and_lemmas.rs`
  - `src/runtime_halfedge_mesh_refinement/phase5_runtime_checks.rs`
- Kernel checker support (if needed): `src/verified_checker_kernels.rs`
- Tests: `src/halfedge_mesh/tests.rs`

## Exit Criteria
- [ ] Every roadmap Phase 5 checkbox is implemented and proved in `vcad-topology`.
- [ ] No trusted assumptions remain for Phase 5 APIs.
- [x] Verification passes:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels`
  - `./scripts/verify-vcad-topology.sh`
- [x] Runtime tests pass for all relevant feature combinations.
