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
- [x] Keep Phase 4 validity (`Mesh::is_valid`) as a required precondition for all Phase 5 geometric theorems/checkers.
- [x] Reuse `vcad-geometry` predicates/lemmas (`orient2d`, `orient3d`, coplanarity, side tests, intersection helpers) rather than duplicating math proofs in `vcad-topology`.
- [ ] Keep exact arithmetic path only (`RuntimePoint3`/`Scalar`); do not add floating-point fallback logic in verified paths.
- [ ] Remove trusted boundaries for any new Phase 5 APIs (no new `assume_specification` debt).

## P5.0 Geometry Model Surface
- [ ] Add mesh-geometry spec helpers that map each face cycle to ordered vertex positions.
- [ ] Add spec-level adjacency relations:
  - shared vertex
  - shared edge
  - disjoint boundary
- [x] Add per-face non-degeneracy preconditions needed by Phase 5 predicates (at least one non-collinear triple per face).
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
- [x] Choose deterministic face-local orientation strategy for convexity tests (implemented with per-face reference normal + `orient3d_sign`, without 2D projection).
- [ ] Spec: projected consecutive `orient2d` signs are globally consistent per face.
- [x] Runtime checker: implement `check_face_convexity`.
- [ ] Proof: runtime checker correctness vs convexity spec.
- [ ] Proof: convexity checker uses only legally projected points from a coplanar face.
- [ ] Proof: triangle faces satisfy convexity trivially.

## P5.4 Invariant: Outward Face Normals (Roadmap)
- [ ] Define oriented face-normal spec from face winding and plane normal.
- [x] Define component-level outwardness criterion for closed meshes (document chosen witness, for example interior reference point / signed volume convention).
- [x] Runtime checker: implement global orientation check (`check_outward_normals` or equivalent).
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
- [x] Runtime API: compute face plane `(normal, offset)` from face vertices via cross product + dot product.
- [x] Handle face-normal seed selection robustly (first non-collinear triple or explicit precondition).
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
- [x] Negative fixture: concave polygon face fails convexity checker.
- [x] Negative fixture: flipped face winding fails outward-normal checker.
- [ ] Negative fixture: non-adjacent face intersection fails self-intersection checker.
- [x] Regression tests under:
  - default build
  - `--features geometry-checks`
  - `--features "geometry-checks,verus-proofs"`

## Burndown Log
- 2026-02-18: Implemented P5.6 runtime plane computation in `src/halfedge_mesh/validation.rs`:
  - added `Mesh::compute_face_plane(face_id) -> Option<(RuntimeVec3, RuntimeScalar)>`, computing `normal . p = offset` in exact arithmetic;
  - seed selection now scans each face cycle for the first non-collinear consecutive triple and returns `None` when no such triple exists.
- 2026-02-18: Added `Mesh::check_face_plane_consistency()` and integrated it into `Mesh::check_geometric_topological_consistency()`, requiring every face vertex to satisfy its computed plane equation.
- 2026-02-18: Extended `src/halfedge_mesh/tests.rs` for P5.6 runtime coverage:
  - positive fixtures (`tetrahedron`, `cube`, `triangular_prism`) now assert `check_face_plane_consistency()`;
  - added `compute_face_plane_returns_expected_values_for_cube_bottom_face`;
  - strengthened degeneracy tests to assert `compute_face_plane(..).is_none()` and plane-consistency failure when no valid plane seed exists.
- 2026-02-18: Failed attempts from this P5.6 pass: none.
- 2026-02-18: Tightened `Mesh::check_face_coplanarity()` to require face non-degeneracy (`check_face_corner_non_collinearity()`) before testing coplanarity, so degenerate collinear faces no longer vacuously pass due a collinear base triple.
- 2026-02-18: Updated degeneracy tests in `src/halfedge_mesh/tests.rs` to match the stronger coplanarity precondition:
  - `collinear_triangle_faces_fail_geometric_nondegeneracy` now expects `check_face_coplanarity() == false`;
  - `coincident_edge_endpoints_fail_zero_length_geometric_edge_check` now expects `check_face_coplanarity() == false`.
- 2026-02-18: Normalized built-in positive fixtures to the outward-orientation convention used by `check_outward_face_normals()` by reversing all face cycles in `Mesh::cube()` and `Mesh::triangular_prism()` (in `src/halfedge_mesh/construction.rs`), so `tetrahedron`, `cube`, and `triangular_prism` now agree on the same signed-volume polarity.
- 2026-02-18: Extended `src/halfedge_mesh/tests.rs` outward-orientation coverage:
  - positive fixtures now assert `check_outward_face_normals()`;
  - added `flipped_face_winding_fails_outward_normal_check` as the explicit flipped-winding counterexample and aggregate-gate regression.
- 2026-02-18: Revalidated after outward-orientation and winding normalization changes:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (192 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (227 verified, 0 errors)
- 2026-02-18: Failed attempt: first pass treated positive signed six-volume as outward, which inverted expectations on existing fixtures (`tetrahedron` failed while fully flipped tetrahedron passed); corrected by keeping the negative signed-volume convention and aligning fixture winding.
- 2026-02-18: Enforced the Phase 4 validity dependency in all current Phase 5 runtime geometry checkers by requiring `Mesh::is_valid()` up front in `check_no_zero_length_geometric_edges`, `check_face_corner_non_collinearity`, `check_face_coplanarity`, `check_face_convexity`, `check_outward_face_normals`, and in the aggregate `check_geometric_topological_consistency`.
- 2026-02-18: Added `phase5_geometry_checks_require_phase4_validity` in `src/halfedge_mesh/tests.rs` to lock the new precondition behavior: if `is_valid()` fails, every Phase 5 geometry checker returns `false`.
- 2026-02-18: Reconciled the burndown checklist with already-landed outward-normal work:
  - runtime checker `Mesh::check_outward_face_normals()` uses per-component signed six-volume accumulation (negative orientation convention);
  - `flipped_face_winding_fails_outward_normal_check` is present as the P5.9 negative fixture.
- 2026-02-18: Implemented `Mesh::check_face_convexity()` in `src/halfedge_mesh/validation.rs` using exact arithmetic only: per-face reference normal from the first corner (`(p1 - p0) x (p2 - p1)`), witness point `p0 + normal`, and per-corner `vcad_geometry::orientation_predicates::orient3d_sign(prev, cur, next, witness)` sign consistency checks around each face cycle.
- 2026-02-18: Updated `Mesh::check_geometric_topological_consistency()` to additionally require `check_face_convexity()`.
- 2026-02-18: Extended `src/halfedge_mesh/tests.rs` for convexity coverage:
  - positive fixtures (`tetrahedron`, `cube`, `triangular_prism`) now assert `check_face_convexity()`;
  - existing coplanarity/non-collinearity negative fixtures now also assert convexity failure when preconditions are violated;
  - added `concave_polygon_faces_fail_face_convexity` as the P5.9 concavity counterexample.
- 2026-02-18: Follow-up validation pass reran the full `vcad-topology` matrix (`cargo test` default/`geometry-checks`/`geometry-checks,verus-proofs`, plus both fast verify scripts and full verify script) after landing the P5.2 zero-length edge checker; all remained green with no new failures.
- 2026-02-18: Implemented `Mesh::check_face_coplanarity()` in `src/halfedge_mesh/validation.rs`, using `vcad_geometry::collinearity_coplanarity::coplanar` on each face cycle with a fixed local `(a,b,c)` plane basis and checking all remaining face vertices against that plane.
- 2026-02-18: Added `Mesh::check_geometric_topological_consistency()` as a Phase-5-in-progress aggregate checker (initially `corner_non_collinearity && face_coplanarity`) and updated `Mesh::is_valid_with_geometry()` to require this aggregate.
- 2026-02-18: Extended `src/halfedge_mesh/tests.rs`:
  - positive fixtures (`tetrahedron`, `cube`, `triangular_prism`) now assert `check_face_coplanarity()` and the aggregate checker;
  - added `noncoplanar_quad_faces_fail_face_coplanarity` negative test;
  - strengthened collinear negative test coverage for aggregate failure (later tightened so coplanarity itself fails under the explicit non-degeneracy precondition).
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
- 2026-02-18: Failed attempts from the zero-length-edge/coplanarity pass: none (superseded by the later outward-sign convention attempt documented above).

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
