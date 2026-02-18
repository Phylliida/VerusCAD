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
- [x] Add mesh-geometry spec helpers that map each face cycle to ordered vertex positions.
- [x] Add spec-level adjacency relations:
  - shared vertex
  - shared edge
  - disjoint boundary
- [x] Add per-face non-degeneracy preconditions needed by Phase 5 predicates (at least one non-collinear triple per face).
- [x] Add bridge specs from runtime mesh to any kernel geometry checker representation used for proofs.

## P5.1 Invariant: Face Coplanarity (Roadmap)
- [x] Spec: define `mesh_face_coplanar_spec(m, f)` (equivalent to orient3d = 0 for all face-vertex quadruples).
- [x] Spec: define aggregate `mesh_all_faces_coplanar_spec(m)`.
- [x] Runtime checker: implement `check_face_coplanarity` (or equivalent) over all faces.
- [ ] Proof: runtime checker correctness vs spec (sound + complete under documented preconditions).
- [x] Proof: coplanarity is stable under cyclic reindexing of a face cycle.

## P5.2 Invariant: Edge Straightness (Implied by Phase 5 Intro)
- [x] Spec: each half-edge geometrically denotes the segment between `vertex(h)` and `vertex(next(h))`.
- [x] Spec: twin half-edges denote the same segment with opposite orientation.
- [x] Runtime checker: reject zero-length geometric edges (in addition to topological non-degeneracy).
- [x] Proof: edge-geometry facts are derivable from mesh model + vertex positions.

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
- [x] Runtime checker: add explicit shared-edge local orientation consistency check (adjacent faces induce opposite direction on the same geometric edge).
- [ ] Proof: local orientation consistency across adjacent faces via shared edges.
- [ ] Proof: global outwardness criterion implies all faces point outward for each closed component.
- [ ] Proof: signed-volume outwardness criterion is independent of the chosen reference origin.

## P5.5 Invariant: No Self-Intersection Except Shared Boundary (Roadmap)
- [ ] Spec: define allowed contact relation between two faces (shared edge, shared vertex, or disjoint).
- [ ] Spec: define forbidden intersection relation for non-adjacent face pairs.
- [x] Runtime checker: implement pairwise face intersection check with adjacency exemptions.
- [ ] Runtime checker: tighten adjacency exemptions to the exact allowed-contact spec (avoid broad "shared vertex => always exempt" behavior).
- [ ] Runtime checker: reject adjacent-face overlap beyond declared shared boundary (for example coplanar interior overlap with shared edge/vertex).
- [ ] Proof: checker soundness (if checker passes, forbidden intersections do not exist).
- [ ] Proof: checker completeness for convex coplanar-face assumptions used by Phase 5.
- [ ] Proof: shared-edge and shared-vertex contacts are never misclassified as forbidden intersections.
- [ ] Proof: adjacency-exemption implementation is equivalent to the allowed-contact spec.

## P5.6 Plane Computation (Roadmap)
- [x] Runtime API: compute face plane `(normal, offset)` from face vertices via cross product + dot product.
- [x] Handle face-normal seed selection robustly (first non-collinear triple or explicit precondition).
- [x] Spec: `face_plane_contains_vertex_spec` for every vertex on the face.
- [x] Define canonical face-plane representation for comparisons (`normal` sign/scale normalization policy).
- [ ] Proof: computed plane contains all vertices of that face (using coplanarity invariant).
- [ ] Proof: computed normal direction matches face orientation/winding.
- [ ] Proof: twin/adjacent orientation interactions agree with plane-normal conventions.
- [ ] Proof: canonicalized plane is stable under cyclic face reindexing and seed-triple choice.

## P5.7 Validity Gate Integration
- [x] Add an explicit Phase 5 aggregate predicate/checker, for example:
  - `mesh_geometric_topological_consistency_spec`
  - `Mesh::check_geometric_topological_consistency()`
- [x] Define final gate composition (for example `is_valid_phase5 = is_valid && geometric_consistency`).
- [x] Keep existing optional `geometry-checks` feature behavior coherent with new verified gate (document if Phase 5 stays feature-gated or becomes default).
- [ ] Prove aggregate checker equivalence to aggregate Phase 5 spec.

## P5.8 Proof-Layer Integration (Current Refinement Layout)
- [x] Extend `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs` with Phase 5 geometry specs.
- [x] Add Phase 5 bridge lemmas alongside `src/runtime_halfedge_mesh_refinement/kernel_bridge_lemmas.rs`.
- [x] Add runtime constructive check wrappers analogous to current structural check wrappers.
- [ ] If kernelized checkers are added, extend `src/verified_checker_kernels.rs` and prove bridge equivalence.
- [ ] Ensure new proof modules are included from `src/runtime_halfedge_mesh_refinement.rs`.

## P5.9 Tests and Counterexamples
- [x] Positive fixtures: tetrahedron, cube, triangular prism pass Phase 5 gate.
- [x] Negative fixture: non-coplanar face fails coplanarity checker.
- [x] Negative fixture: zero-length geometric edge fails edge-straightness checker.
- [x] Negative fixture: concave polygon face fails convexity checker.
- [x] Negative fixture: flipped face winding fails outward-normal checker.
- [x] Negative fixture: non-adjacent face intersection fails self-intersection checker.
- [x] Regression tests under:
  - default build
  - `--features geometry-checks`
  - `--features "geometry-checks,verus-proofs"`

## P5.10 Degeneracy Policy and Contract Hardening
- [ ] Write an explicit Phase 5 degeneracy policy (accepted vs rejected cases) for:
  - coplanar neighboring faces
  - vertex-touch-only contacts between components
  - zero-volume or near-degenerate closed components (in exact arithmetic terms)
- [ ] Ensure each runtime checker contract and precondition text matches that policy (no implicit checker-specific behavior).
- [ ] Add policy-lock tests: at least one positive and one negative fixture for each documented boundary case.

## P5.11 Diagnostics and Scalability Guardrails
- [ ] Add diagnostic checker variants that return a first failing witness (face id / edge id / face-pair + reason), not only `bool`.
- [ ] Prove diagnostic and boolean checker equivalence (diagnostic success iff boolean passes).
- [ ] Document checker complexity and asymptotic bounds (especially face-pair intersection path).
- [ ] Add broad-phase culling for face-pair checks (for example plane-side/AABB prefilters) with soundness proof (no false negatives).
- [ ] Add stress fixtures (higher face counts) to lock checker behavior and runtime envelope.

## P5.12 Invariance, Policy, and Phase-6 Readiness
- [ ] Checker-result invariance:
  - prove/tests that Phase 5 outcomes are invariant under face-cycle start index changes, face iteration order changes, and consistent mesh index relabeling.
- [ ] Rigid-transform invariance:
  - prove/tests that translation + rotation preserve all Phase 5 checks;
  - document and test expected behavior under reflection (orientation-sensitive checks should flip as intended).
- [ ] Connected-component interaction policy:
  - explicitly define whether disconnected closed components may touch at vertex/edge/face contact;
  - enforce that policy in intersection/outwardness gate behavior.
- [ ] Witness-grade failure APIs:
  - add optional first-failure witness payloads (offending face/edge/face-pair + reason code);
  - add witness-validity tests proving returned witnesses are real counterexamples.
- [ ] Differential/property-based verification harness:
  - generate random valid closed meshes + adversarial perturbations;
  - compare optimized runtime checkers against a simple brute-force oracle for consistency.
- [ ] Phase 6 handoff lemmas:
  - state/prove preservation lemmas for Phase 5 invariants under topology-only edits that do not move coordinates;
  - document which Euler-operator preconditions must preserve geometric invariants versus recheck them.

## Burndown Log
- 2026-02-18: Completed the P5.8 runtime constructive-wrapper item by adding Phase 5 constructive gate witnesses and wrappers:
  - in `src/runtime_halfedge_mesh_refinement/components_and_validity_specs.rs`:
    - added `GeometricTopologicalConsistencyGateWitness` + `geometric_topological_consistency_gate_witness_spec`/`geometric_topological_consistency_gate_model_link_spec`;
    - added `ValidWithGeometryGateWitness` + `valid_with_geometry_gate_witness_spec`/`valid_with_geometry_gate_model_link_spec`;
    - added lemma `lemma_valid_with_geometry_gate_witness_api_ok_implies_mesh_valid`.
  - in `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`:
    - added `check_geometric_topological_consistency_constructive(m)` (feature-gated on `geometry-checks`), returning a constructive witness that mirrors the runtime Phase 5 checker conjunction;
    - added `is_valid_with_geometry_constructive(m)` (feature-gated on `geometry-checks`), composing Phase 4 validity witness + geometric consistency witness into a combined constructive gate witness.
- 2026-02-18: Failed attempts in this P5.8 constructive-wrapper pass: none.
- 2026-02-18: Revalidated after P5.8 constructive-wrapper additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (208 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (243 verified, 0 errors)
- 2026-02-18: Completed the P5.6 canonical face-plane representation item in `src/halfedge_mesh/validation.rs`:
  - added `Mesh::canonicalize_plane(normal, offset)` with explicit deterministic policy:
    - pivot = first non-zero normal component in `(x, y, z)` order;
    - normalize by dividing both normal and offset by that pivot so pivot becomes `1`;
  - added `Mesh::compute_face_plane_canonical(face_id)` as the canonicalized variant of `compute_face_plane`.
- 2026-02-18: Extended `src/halfedge_mesh/tests.rs` for canonical plane coverage:
  - added `canonicalize_plane_normalizes_sign_and_scale`, locking sign/scale invariance (`(n, d)` equals canonicalized `(-3n, -3d)`);
  - added `compute_face_plane_canonical_returns_expected_values_for_cube_bottom_face` (expects canonical `(0, 0, 1)` and `-1`);
  - strengthened `phase5_checks_are_invariant_under_face_cycle_start_rotation` to assert canonical face planes are unchanged across per-face cycle-start rotations.
- 2026-02-18: Failed attempts in this P5.6 canonical-plane pass: none.
- 2026-02-18: Revalidated after the P5.6 canonical-plane additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (205 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (240 verified, 0 errors)
- 2026-02-18: Completed the P5.0 runtime-to-kernel geometry bridge-spec item across the refinement layer:
  - in `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`, added `kernel_mesh_runtime_geometry_bridge_spec(km, m)` to model a combined kernel-topology/runtime-geometry bridge for kernel geometry-checker inputs;
  - in `src/runtime_halfedge_mesh_refinement/kernel_bridge_lemmas.rs`, added `lemma_kernel_mesh_runtime_geometry_bridge_holds`, deriving the new bridge spec from `kernel_mesh_matches_mesh_model_spec` plus `lemma_mesh_runtime_geometry_bridge_holds`;
  - in `src/runtime_halfedge_mesh_refinement/kernel_component_runtime_checks.rs`, added constructive wrapper `runtime_mesh_to_kernel_mesh_geometry_bridge` that returns a kernel mesh with the new geometry bridge guarantee.
- 2026-02-18: Failed attempts in this P5.0 pass: none.
- 2026-02-18: Revalidated after the P5.0 bridge-spec additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (205 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology.sh` (240 verified, 0 errors)
- 2026-02-18: Completed the P5.8 Phase 5 bridge-lemma item in `src/runtime_halfedge_mesh_refinement/kernel_bridge_lemmas.rs`:
  - added runtime geometry bridge lemma `lemma_mesh_runtime_geometry_bridge_holds`, proving `mesh_runtime_geometry_bridge_spec(m)`;
  - added face-cycle bridge lemmas tying model cycle iteration to runtime geometry sequences:
    - `lemma_mesh_face_cycle_half_edge_or_default_matches_model`
    - `lemma_mesh_face_cycle_vertex_index_or_default_matches_model`
    - `lemma_mesh_runtime_face_cycle_vertex_position_matches_runtime_positions`
    - `lemma_mesh_runtime_face_ordered_vertex_positions_match_cycle`.
- 2026-02-18: Failed attempt in this P5.8 pass: initial lemma signatures omitted explicit face-index bounds (`0 <= f < mesh_face_count_spec(..)`), and the proof attempted to assert half-edge bounds directly from face-cycle witnesses; Verus rejected those assertions. Resolved by adding explicit face-index preconditions and discharging half-edge bounds via `lemma_mesh_next_iter_in_bounds`.
- 2026-02-18: Revalidated after the P5.8 bridge-lemma additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (203 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (238 verified, 0 errors)
- 2026-02-18: Completed a P5.2 spec/proof pass in `src/runtime_halfedge_mesh_refinement/from_face_cycles_specs_and_lemmas.rs`:
  - added geometry-level half-edge segment specs over vertex positions (`mesh_half_edge_from_position_spec`, `mesh_half_edge_to_position_spec`, `mesh_half_edge_segment_geometry_at_spec`, and aggregate `mesh_all_half_edges_segment_geometry_spec`);
  - added geometry-level twin reversed-segment specs (`mesh_twin_half_edges_reverse_segment_at_spec` and aggregate `mesh_all_twin_half_edges_reverse_segments_spec`);
  - proved these facts are derivable from model assumptions and runtime vertex positions via:
    - `lemma_mesh_half_edge_segment_geometry_at_from_model_and_positions`
    - `lemma_mesh_all_half_edges_segment_geometry_from_model_and_positions`
    - `lemma_mesh_twin_half_edges_reverse_segment_at_from_model_and_positions`
    - `lemma_mesh_all_twin_half_edges_reverse_segments_from_model_and_positions`.
- 2026-02-18: Failed attempt in this P5.2 pass: first version of `lemma_mesh_twin_half_edges_reverse_segment_at_from_model_and_positions` hit Verus rlimit during `./scripts/verify-vcad-topology.sh`; resolved by simplifying `mesh_twin_half_edges_reverse_segment_at_spec` to avoid nested segment-spec expansion and proving index/position equalities directly.
- 2026-02-18: Revalidated after the P5.2 edge-segment spec/proof additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (198 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (233 verified, 0 errors)
- 2026-02-18: Completed the P5.1 cyclic-reindexing coplanarity proof item in `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added `mesh_face_cycle_shift_index_spec` and `lemma_mesh_face_cycle_shift_index_in_bounds`;
  - proved `lemma_mesh_face_coplanar_witness_stable_under_cyclic_reindexing`, showing that any cyclic shift of face-cycle indices preserves the coplanarity witness relation.
- 2026-02-18: Added runtime regression coverage for cycle-start invariance in `src/halfedge_mesh/tests.rs`:
  - new `phase5_checks_are_invariant_under_face_cycle_start_rotation` builds two geometrically identical cubes with per-face cycle starts rotated by one and asserts identical outcomes for all current Phase 5 runtime checkers, including the aggregate gate.
- 2026-02-18: Failed attempt in this P5.1 pass: first proof revision used `nonlinear_arith` directly for shift-index bounds and failed to discharge integer inequalities in Verus; resolved by rewriting the bounds proof with explicit linear inequality steps.
- 2026-02-18: Revalidated after the P5.1 cyclic-reindexing proof + invariance regression additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (194 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (229 verified, 0 errors)
- 2026-02-18: Implemented the P5.4 shared-edge local orientation runtime checker in `src/halfedge_mesh/validation.rs`:
  - added `Mesh::check_shared_edge_local_orientation_consistency()`, requiring each twin half-edge pair to induce opposite geometric segment directions (`start/end` swapped in exact arithmetic) and to belong to different faces;
  - integrated this check into `Mesh::check_geometric_topological_consistency()`.
- 2026-02-18: Extended `src/halfedge_mesh/tests.rs` for shared-edge local orientation coverage:
  - positive fixtures (`tetrahedron`, `cube`, `triangular_prism`) now assert `check_shared_edge_local_orientation_consistency()`;
  - `phase5_geometry_checks_require_phase4_validity` now asserts this checker returns `false` when Phase 4 validity fails;
  - orientation-independent negatives (`flipped_face_winding_fails_outward_normal_check`, `nonadjacent_face_intersection_fails_self_intersection_checker`) now explicitly assert local shared-edge orientation still passes.
- 2026-02-18: Failed attempt in this P5.4 pass: tried to construct a dedicated Phase-4-valid counterexample where twin half-edges do not reverse shared-edge direction, but this relation is already enforced by the current structural ring constraints (`check_twin_involution` + `check_vertex_manifold_single_cycle` via `twin/next` traversal), so no additional Phase-4-valid negative fixture was added.
- 2026-02-18: Revalidated after P5.4 local-orientation checker integration:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (192 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (227 verified, 0 errors)
- 2026-02-18: Implemented P5.5 runtime self-intersection checker in `src/halfedge_mesh/validation.rs`:
  - added `Mesh::check_no_forbidden_face_face_intersections()` and integrated it into `Mesh::check_geometric_topological_consistency()`;
  - checker behavior: for each non-adjacent face pair (shared-vertex pairs exempt), test edge-vs-face intersections in exact arithmetic, including coplanar overlap/touch handling via dominant-axis 2D projection and `vcad_geometry` segment intersection predicates.
- 2026-02-18: Extended `src/halfedge_mesh/tests.rs` for P5.5 coverage:
  - positive fixtures (`tetrahedron`, `cube`, `triangular_prism`) now assert `check_no_forbidden_face_face_intersections()`;
  - added `nonadjacent_face_intersection_fails_self_intersection_checker` using two overlapping closed tetrahedra (topologically valid but geometrically intersecting) as the explicit P5.9 self-intersection counterexample.
- 2026-02-18: Failed attempts in this P5.5 pass: none.
- 2026-02-18: Revalidated after P5.5 runtime checker/test integration:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (192 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (227 verified, 0 errors)
- 2026-02-18: Completed a P5.8/P5.0/P5.1 spec-layer pass in `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added Phase 5 geometry model helpers for ordered face-cycle vertex positions and runtime vertex-position bridging (`mesh_runtime_vertex_positions_spec`, `mesh_runtime_geometry_bridge_spec`, and face-cycle position accessors);
  - added adjacency specs (`mesh_faces_share_vertex_spec`, `mesh_faces_share_edge_spec`, `mesh_faces_disjoint_boundary_spec`);
  - finalized coplanarity/plane specs (`mesh_face_coplanar_spec`, `mesh_all_faces_coplanar_spec`, `face_plane_contains_vertex_spec`) with explicit face-index guards so witness specs are well-scoped.
- 2026-02-18: Failed attempt in this spec-layer pass: first revision left two competing `mesh_face_coplanar_spec`/`mesh_all_faces_coplanar_spec` definitions in the same module, causing Verus compile failure (`E0428` duplicate definitions) in `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`; resolved by consolidating to a single canonical coplanarity spec family.
- 2026-02-18: Revalidated after the Phase 5 spec-layer integration changes:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (192 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (227 verified, 0 errors)
- 2026-02-18: Implemented P5.6 runtime plane computation in `src/halfedge_mesh/validation.rs`:
  - added `Mesh::compute_face_plane(face_id) -> Option<(RuntimeVec3, RuntimeScalar)>`, computing `normal . p = offset` in exact arithmetic;
  - seed selection now scans each face cycle for the first non-collinear consecutive triple and returns `None` when no such triple exists.
- 2026-02-18: Added `Mesh::check_face_plane_consistency()` and integrated it into `Mesh::check_geometric_topological_consistency()`, requiring every face vertex to satisfy its computed plane equation.
- 2026-02-18: Extended `src/halfedge_mesh/tests.rs` for P5.6 runtime coverage:
  - positive fixtures (`tetrahedron`, `cube`, `triangular_prism`) now assert `check_face_plane_consistency()`;
  - added `compute_face_plane_returns_expected_values_for_cube_bottom_face`;
  - strengthened degeneracy tests to assert `compute_face_plane(..).is_none()` and plane-consistency failure when no valid plane seed exists.
- 2026-02-18: Failed attempt in this P5.6 pass: initially asserted concave coplanar faces should fail `check_face_plane_consistency()`, but this was incorrect (concavity does not invalidate plane containment); test expectation was corrected to pass plane-consistency while still failing convexity.
- 2026-02-18: Revalidated after P5.6 runtime plane changes:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (192 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (227 verified, 0 errors)
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
- [ ] Phase 5 degeneracy policy and checker contracts are explicit and test-locked.
- [x] Verification passes:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels`
  - `./scripts/verify-vcad-topology.sh`
- [x] Runtime tests pass for all relevant feature combinations.
