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
- [x] Keep exact arithmetic path only (`RuntimePoint3`/`Scalar`); do not add floating-point fallback logic in verified paths.
- [x] Remove trusted boundaries for any new Phase 5 APIs (no new `assume_specification` debt).

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
- [x] Proof groundwork: bridge full coplanarity witnesses to fixed-seed runtime-style witnesses and seed-plane containment.
- [x] Proof: coplanarity is stable under cyclic reindexing of a face cycle.

## P5.2 Invariant: Edge Straightness (Implied by Phase 5 Intro)
- [x] Spec: each half-edge geometrically denotes the segment between `vertex(h)` and `vertex(next(h))`.
- [x] Spec: twin half-edges denote the same segment with opposite orientation.
- [x] Runtime checker: reject zero-length geometric edges (in addition to topological non-degeneracy).
- [x] Proof: edge-geometry facts are derivable from mesh model + vertex positions.

## P5.3 Invariant: Face Convexity (Roadmap)
- [x] Choose deterministic face-local orientation strategy for convexity tests (implemented with per-face reference normal + `orient3d_sign`, without 2D projection).
- [x] Spec: projected consecutive `orient2d` signs are globally consistent per face.
- [x] Runtime checker: implement `check_face_convexity`.
- [ ] Proof: runtime checker correctness vs convexity spec.
- [x] Proof: convexity checker uses only legally projected points from a coplanar face.
- [x] Proof: triangle faces satisfy convexity trivially.

## P5.4 Invariant: Outward Face Normals (Roadmap)
- [x] Define oriented face-normal spec from face winding and plane normal.
- [x] Define component-level outwardness criterion for closed meshes (document chosen witness, for example interior reference point / signed volume convention).
- [x] Runtime checker: implement global orientation check (`check_outward_normals` or equivalent).
- [x] Runtime checker: add explicit shared-edge local orientation consistency check (adjacent faces induce opposite direction on the same geometric edge).
- [x] Proof: local orientation consistency across adjacent faces via shared edges.
- [ ] Proof: global outwardness criterion implies all faces point outward for each closed component.
- [ ] Proof: signed-volume outwardness criterion is independent of the chosen reference origin.

## P5.5 Invariant: No Self-Intersection Except Shared Boundary (Roadmap)
- [x] Spec: define allowed contact relation between two faces (shared edge, shared vertex, or disjoint).
- [x] Spec: define forbidden intersection relation for non-adjacent face pairs.
- [x] Runtime checker: implement pairwise face intersection check with adjacency exemptions.
- [x] Runtime checker: tighten adjacency exemptions to the exact allowed-contact spec (avoid broad "shared vertex => always exempt" behavior).
- [x] Runtime checker: reject adjacent-face overlap beyond declared shared boundary (for example coplanar interior overlap with shared edge/vertex).
- [ ] Proof: checker soundness (if checker passes, forbidden intersections do not exist).
- [ ] Proof: checker completeness for convex coplanar-face assumptions used by Phase 5.
- [x] Proof: shared-edge and shared-vertex contacts are never misclassified as forbidden intersections.
- [x] Proof: adjacency-exemption implementation is equivalent to the allowed-contact spec.

## P5.6 Plane Computation (Roadmap)
- [x] Runtime API: compute face plane `(normal, offset)` from face vertices via cross product + dot product.
- [x] Handle face-normal seed selection robustly (first non-collinear triple or explicit precondition).
- [x] Spec: `face_plane_contains_vertex_spec` for every vertex on the face.
- [x] Define canonical face-plane representation for comparisons (`normal` sign/scale normalization policy).
- [x] Proof: computed plane contains all vertices of that face (using coplanarity invariant).
- [x] Proof: computed normal direction matches face orientation/winding.
- [x] Proof: twin/adjacent orientation interactions agree with plane-normal conventions.
- [x] Proof: canonicalized plane is stable under cyclic face reindexing and seed-triple choice.

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
- [x] If kernelized checkers are added, extend `src/verified_checker_kernels.rs` and prove bridge equivalence.
- [x] Ensure new proof modules are included from `src/runtime_halfedge_mesh_refinement.rs`.

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
- [x] Write an explicit Phase 5 degeneracy policy (accepted vs rejected cases) for:
  - coplanar neighboring faces
  - vertex-touch-only contacts between components
  - zero-volume or near-degenerate closed components (in exact arithmetic terms)
- [x] Ensure each runtime checker contract and precondition text matches that policy (no implicit checker-specific behavior).
- [x] Add policy-lock tests: at least one positive and one negative fixture for each documented boundary case.

Current explicit policy (runtime behavior locked by tests):
- Coplanar neighboring faces:
  - accepted only when pairwise face contact matches the exact allowed-contact topology (disjoint boundary, one shared vertex, or one shared edge) and geometric intersection is limited to that declared shared boundary;
  - rejected when pairwise shared boundary is broader than allowed (for example, coincident/double-face boundaries with multiple shared edges) or when overlap extends beyond the declared shared boundary.
- Vertex-touch-only contacts between components:
  - rejected when the touch is geometric only (coincident positions with distinct vertex indices), because allowed-contact exemptions are topological (shared indices) and geometric coincidence alone is non-exempt;
  - accepted when disconnected components are geometrically disjoint.
- Zero-volume / near-degenerate closed components:
  - exact arithmetic only (no floating-point epsilon path, so "near-degenerate" means exact degeneracy in this checker set);
  - rejected when component signed volume is zero (or positive) under the outward convention;
  - rejected earlier for exact face/edge degeneracy by non-collinearity and zero-length edge checks.

## P5.11 Diagnostics and Scalability Guardrails
- [x] Add diagnostic checker variants that return a first failing witness (face id / edge id / face-pair + reason), not only `bool`.
- [x] Prove diagnostic and boolean checker equivalence (diagnostic success iff boolean passes).
- [x] Document checker complexity and asymptotic bounds (especially face-pair intersection path).
- [x] Add broad-phase culling for face-pair checks (for example plane-side/AABB prefilters) with soundness proof (no false negatives).
- [x] Add stress fixtures (higher face counts) to lock checker behavior and runtime envelope.

Current complexity notes (runtime implementation in `src/halfedge_mesh/validation.rs`):
- Symbols:
  - `F` = number of faces;
  - `H` = number of half-edges (`H = sum_f d_f`, where `d_f` is face `f` cycle length);
  - `d_max` = `max_f d_f`.
- Linear-time per-half-edge checks:
  - `check_no_zero_length_geometric_edges`, `check_face_corner_non_collinearity`, `check_face_coplanarity`, `check_face_convexity`, and `check_shared_edge_local_orientation_consistency` each run in `O(H)` time with `O(1)` auxiliary space (excluding input mesh storage).
- Plane consistency:
  - public `compute_face_plane` remains a guard-checked API and is `O(H)` worst-case per call.
  - internal prevalidated plane extraction (used by aggregate checker internals) runs in
    `O(sum_f d_f) = O(H)` total for one full-face sweep.
  - `check_face_plane_consistency` is now `O(H)` time with `O(1)` auxiliary space (excluding input storage).
- Face-pair intersection path:
  - `check_no_forbidden_face_face_intersections` performs `O(H)` per-face preprocessing plus all non-adjacent face pairs.
  - each pair first applies a broad-phase prefilter (`AABB` overlap + strict plane-side separation) in `O(d_a + d_b)` time; rejected pairs skip the narrow phase.
  - Pair cost is `O(d_a * d_b)` for faces `a, b` (segment-vs-face tests + shared-vertex screening).
  - Total pair cost is `O(sum_{a<b} d_a d_b)`, bounded by `O(F^2 * d_max^2)`; for bounded face degree this is `O(F^2)`.
  - Auxiliary space is `O(H)` for cached per-face vertex cycles and normals.
- Aggregate Phase 5 gate:
  - `check_geometric_topological_consistency_diagnostic` is dominated by face-pair intersection and is currently `O(H + F^2 * d_max^2)` worst-case.

## P5.12 Invariance, Policy, and Phase-6 Readiness
- [x] Checker-result invariance:
  - prove/tests that Phase 5 outcomes are invariant under face-cycle start index changes, face iteration order changes, and consistent mesh index relabeling.
- [x] Rigid-transform invariance:
  - prove/tests that translation + rotation preserve all Phase 5 checks;
  - document and test expected behavior under reflection (orientation-sensitive checks should flip as intended).
- [x] Connected-component interaction policy:
  - explicitly define whether disconnected closed components may touch at vertex/edge/face contact;
  - enforce that policy in intersection/outwardness gate behavior.
- [x] Witness-grade failure APIs:
  - add optional first-failure witness payloads (offending face/edge/face-pair + reason code);
  - add witness-validity tests proving returned witnesses are real counterexamples.
- [x] Differential/property-based verification harness:
  - generate random valid closed meshes + adversarial perturbations;
  - compare optimized runtime checkers against a simple brute-force oracle for consistency.
- [x] Phase 6 handoff lemmas:
  - state/prove preservation lemmas for Phase 5 invariants under topology-only edits that do not move coordinates;
  - document which Euler-operator preconditions must preserve geometric invariants versus recheck them.

Current connected-component interaction policy (runtime behavior locked by tests):
- disconnected closed components are accepted only when geometrically disjoint;
- disconnected components touching at a vertex, along an edge, or across a face (with distinct vertex indices) are rejected by `check_no_forbidden_face_face_intersections` and therefore by the aggregate Phase 5 gate.

Current rigid-transform policy (runtime behavior locked by tests):
- rigid transforms with determinant `+1` (tested: exact 90-degree axis rotation plus integer translation) preserve full Phase 5 checker signatures for both passing and failing fixtures;
- reflection transforms with determinant `-1` preserve local geometric checks, but intentionally flip outward-orientation-sensitive outcomes (`check_outward_face_normals`, aggregate geometric-consistency gate, and `is_valid_with_geometry`).

Current differential/property-based harness policy (runtime behavior locked by tests):
- deterministic seeded randomized fixtures (40 cases) generate valid disconnected closed tetrahedra configurations, rigid transforms, and adversarial coordinate perturbations (exact overlap + vertex-touch);
- optimized intersection checking (`check_no_forbidden_face_face_intersections`) is asserted equivalent to a no-cull brute-force oracle path (`check_no_forbidden_face_face_intersections_without_broad_phase_for_testing`) across all generated fixtures.

Current Phase 6 handoff policy (spec-level guidance for upcoming Euler operators):
- precondition-preserved (no mandatory full recheck) when an operator provides explicit proof witnesses that:
  - preserved half-edges keep endpoint positions unchanged (captures edge straightness direction-vector stability); and
  - preserved faces keep ordered face-cycle position traces unchanged (captures face coplanarity witness stability).
- must be rechecked (or discharged by stronger operator-specific proofs) on affected regions for:
  - face convexity;
  - outward-orientation/global signed-volume criteria;
  - forbidden face-face intersection policy;
  - aggregate geometric-topological consistency gate.

## Burndown Log
- 2026-02-19: Worked P5.5 (`Proof: checker soundness (if checker passes, forbidden intersections do not exist)` and `Proof: checker completeness for convex coplanar-face assumptions used by Phase 5`) with an inverse-branch forbidden-policy decomposition increment in:
  - `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`;
  - `src/halfedge_mesh/tests.rs`.
  - added new inverse corollaries on top of the existing runtime pair-policy decomposition:
    - `lemma_mesh_not_runtime_forbidden_policy_implies_allowed_contact_relation`;
    - `lemma_mesh_not_runtime_forbidden_policy_implies_allowed_contact_runtime_branch_classifier`;
    - `lemma_mesh_disjoint_boundary_and_not_runtime_forbidden_policy_imply_no_intersection`.
  - added runtime regression coverage for the inverse branch (`non-forbidden => allowed-contact topology`) in:
    - helper `assert_non_forbidden_pairs_are_allowed_contact_topology`;
    - integrated into:
      - `shared_edge_contacts_are_not_misclassified_as_forbidden_intersections`;
      - `shared_vertex_only_contacts_are_not_misclassified_as_forbidden_intersections`;
      - `disjoint_boundary_pair_policy_branch_matches_expected_forbidden_classification`.
  - outcome:
    - P5.5 now has direct reusable proof hooks for reasoning backward from `!mesh_face_pair_runtime_forbidden_intersection_policy_spec(...)` into allowed-contact and disjoint/no-intersection facts, reducing contradiction boilerplate in remaining soundness/completeness work;
    - runtime regressions now explicitly lock the corresponding inverse classification implication on deterministic fixtures.
- 2026-02-19: Failed attempts in this P5.5 inverse-branch forbidden-policy pass: none.
- 2026-02-19: Revalidated after the P5.5 inverse-branch forbidden-policy increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (63 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (86 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks shared_edge_contacts_are_not_misclassified_as_forbidden_intersections` (1 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks shared_vertex_only_contacts_are_not_misclassified_as_forbidden_intersections` (1 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks disjoint_boundary_pair_policy_branch_matches_expected_forbidden_classification` (1 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (357 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (394 verified, 0 errors)
- 2026-02-19: Worked P5.7 (`Prove aggregate checker equivalence to aggregate Phase 5 spec`) with a geometry-aware aggregate-spec strengthening increment in:
  - `src/runtime_halfedge_mesh_refinement/components_and_validity_specs.rs`.
  - added geometry-linked aggregate gate specs:
    - `geometric_topological_consistency_gate_geometry_model_link_spec`;
    - `mesh_geometric_topological_consistency_with_geometry_spec`;
    - `mesh_runtime_geometric_topological_consistency_with_geometry_spec`.
  - added bridge lemmas from aggregate witnesses/bundles into the new geometry-aware aggregate spec:
    - `lemma_geometric_topological_consistency_gate_witness_api_ok_implies_mesh_geometric_topological_consistency_with_geometry`;
    - `lemma_mesh_geometric_topological_consistency_with_geometry_implies_mesh_geometric_topological_consistency`;
    - `lemma_mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_implies_mesh_geometric_topological_consistency_with_geometry`.
  - outcome:
    - aggregate proof layering now has an explicit geometry-aware spec target (seed0 coplanarity-plane bundle + Phase 4 validity + shared-edge local orientation), instead of routing only through the weaker topology-only aggregate characterization;
    - `check_geometric_topological_consistency_constructive` and `runtime_check_geometric_topological_consistency_sound_bridge` now prove into that stronger geometry-aware aggregate spec.
- 2026-02-19: Failed attempts in this P5.7 geometry-aware aggregate-spec pass: none.
- 2026-02-19: Revalidated after the P5.7 geometry-aware aggregate-spec increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (63 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (86 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (354 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (391 verified, 0 errors)
- 2026-02-19: Worked P5.5 (`Proof: checker soundness (if checker passes, forbidden intersections do not exist)` and `Proof: checker completeness for convex coplanar-face assumptions used by Phase 5`) with an unconditional exact-two-vertex symmetry bridge increment in:
  - `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`.
  - added new relation-level symmetry lemmas:
    - `lemma_mesh_faces_share_exactly_two_vertices_spec_symmetric_under_vertex_index_symmetry`;
    - `lemma_mesh_faces_share_exactly_two_vertices_spec_symmetric`.
  - upgraded downstream symmetry plumbing to remove external exact-two-vertex symmetry assumptions:
    - `lemma_mesh_faces_allowed_contact_runtime_branch_classifier_spec_symmetric_under_two_vertex_symmetry` is now unconditional and derives exact-two-vertex symmetry internally;
    - `lemma_mesh_face_pair_runtime_forbidden_intersection_policy_spec_symmetric` is now unconditional and no longer requires
      `mesh_faces_share_exactly_two_vertices_spec(m, f1, f2) == mesh_faces_share_exactly_two_vertices_spec(m, f2, f1)`.
  - outcome:
    - P5.5 pair-order symmetry bridges for runtime allowed-contact classification and forbidden-policy classification now compose without the prior caller-supplied exact-two-vertex symmetry precondition;
    - this reduces assumption plumbing at remaining soundness/completeness call sites while keeping the two open P5.5 checklist items unchanged.
- 2026-02-19: Failed attempt in this P5.5 unconditional exact-two-vertex symmetry pass:
  - first verifier run failed with trigger inference on the new `choose` witness for
    `lemma_mesh_faces_share_exactly_two_vertices_spec_symmetric_under_vertex_index_symmetry`;
  - resolved by adding explicit `#[trigger]` annotations on the witness-side
    `mesh_faces_share_vertex_index_spec(...)` terms.
- 2026-02-19: Revalidated after the P5.5 unconditional exact-two-vertex symmetry increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (63 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (86 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (351 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (388 verified, 0 errors)
- 2026-02-19: Worked P5.5 (`Proof: checker soundness (if checker passes, forbidden intersections do not exist)` and `Proof: checker completeness for convex coplanar-face assumptions used by Phase 5`) with a low-cost policy-symmetry factoring increment in:
  - `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`.
  - added a new reusable policy-symmetry helper under explicit classifier parity:
    - `lemma_mesh_face_pair_runtime_forbidden_intersection_policy_spec_symmetric_under_classifier_symmetry`.
  - rewired the existing two-vertex-assumption wrapper:
    - `lemma_mesh_face_pair_runtime_forbidden_intersection_policy_spec_symmetric` now derives classifier parity via
      `lemma_mesh_faces_allowed_contact_runtime_branch_classifier_spec_symmetric_under_two_vertex_symmetry`,
      then delegates to the new helper.
  - outcome:
    - P5.5 now has both:
      - a direct classifier-parity policy symmetry bridge for low-cost reuse at call sites that already have classifier symmetry, and
      - the existing relation-level (`exactly_two_vertices`) wrapper path.
    - runtime-halfedge refinement verification count increased by one verified item in this pass.
- 2026-02-19: Failed attempt in this P5.5 symmetry factoring pass:
  - attempted to prove unconditional local symmetry
    `lemma_mesh_faces_share_exactly_two_vertices_spec_symmetric`
    and remove the two-vertex symmetry precondition entirely from classifier/policy symmetry lemmas;
  - Verus hit persistent rlimit blow-ups on the exact-two-vertex symmetry proof, including retries with `#[verifier::spinoff_prover]` and elevated `#[verifier::rlimit(...)]`;
  - resolved by rolling back the high-cost lemma and landing the lower-cost policy-symmetry factoring helper above.
- 2026-02-19: Revalidated after the P5.5 policy-symmetry factoring increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (63 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (86 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (349 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (386 verified, 0 errors)
- 2026-02-19: Worked P5.5 (`Proof: checker soundness (if checker passes, forbidden intersections do not exist)` and `Proof: checker completeness for convex coplanar-face assumptions used by Phase 5`) with a lower-cost symmetry-precondition normalization increment in:
  - `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`.
  - added a new classifier symmetry bridge under an explicit two-vertex relation symmetry assumption:
    - `lemma_mesh_faces_allowed_contact_runtime_branch_classifier_spec_symmetric_under_two_vertex_symmetry`.
  - narrowed the policy-symmetry lemma precondition from full classifier parity to relation-level parity:
    - `lemma_mesh_face_pair_runtime_forbidden_intersection_policy_spec_symmetric` now requires
      `mesh_faces_share_exactly_two_vertices_spec(m, f1, f2) == mesh_faces_share_exactly_two_vertices_spec(m, f2, f1)`,
      and derives classifier parity internally via the new helper.
  - also stabilized an unrelated proof hotspot hit during this pass by switching a fragile trigger-heavy quad-coplanarity assertion to local aliases (`p0`, `p1`, `p2`, `p3`) in:
    - `lemma_mesh_face_seed0_fixed_witness_and_quad_cycle_imply_face_coplanar_spec`.
  - outcome:
    - P5.5 symmetry plumbing is now stated at a lower-level relation assumption (exactly-two-vertex symmetry) instead of requiring full classifier parity as an external precondition;
    - runtime-halfedge refinement verification count increased by one verified item in this pass.
- 2026-02-19: Failed attempt in this P5.5 symmetry-precondition normalization pass:
  - attempted to reintroduce full quantified symmetry for `mesh_faces_share_exactly_two_vertices_spec` and then remove all symmetry assumptions from classifier/policy symmetry lemmas;
  - Verus again hit an rlimit blow-up on the quantified two-vertex symmetry proof;
  - resolved by rolling back the high-cost unconditional symmetry approach and landing the lower-cost precondition-normalization helper above.
- 2026-02-19: Revalidated after the P5.5 symmetry-precondition normalization increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (63 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (86 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (348 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (385 verified, 0 errors)
- 2026-02-19: Worked P5.5 (`Proof: checker soundness (if checker passes, forbidden intersections do not exist)` and `Proof: checker completeness for convex coplanar-face assumptions used by Phase 5`) with a low-cost forbidden-policy pair-order symmetry bridge increment in:
  - `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`.
  - added a new policy-level symmetry lemma with an explicit classifier-symmetry assumption:
    - `lemma_mesh_face_pair_runtime_forbidden_intersection_policy_spec_symmetric`.
  - this lemma proves swapped-argument parity for
    `mesh_face_pair_runtime_forbidden_intersection_policy_spec(m, f1, f2, geometric_intersection_exists)`
    under the precondition
    `mesh_faces_allowed_contact_runtime_branch_classifier_spec(m, f1, f2) == mesh_faces_allowed_contact_runtime_branch_classifier_spec(m, f2, f1)`.
  - outcome:
    - P5.5 now has a direct reusable policy-level symmetry hook for face-pair forbidden classification without re-expanding branch decomposition at each call site;
    - existing runtime regressions already lock the required classifier-symmetry precondition (`assert_face_pair_policy_classifiers_are_symmetric_under_face_argument_swap`), so the new proof bridge composes with current pair-order parity coverage.
- 2026-02-19: Failed attempt in this P5.5 policy-symmetry pass:
  - attempted to add full quantified symmetry for `mesh_faces_share_exactly_two_vertices_spec` and derived unconditional allowed-contact/runtime-policy symmetry lemmas;
  - Verus hit an rlimit blow-up on the quantified two-vertex symmetry lemma, and the fallback `spinoff_prover` + elevated `#[verifier::rlimit(...)]` variant was too costly for practical burndown verification throughput;
  - resolved by removing the high-cost lemmas and landing the lower-cost policy-level symmetry bridge above.
- 2026-02-19: Revalidated after the P5.5 policy-level symmetry bridge increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (63 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (86 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (347 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (384 verified, 0 errors)
- 2026-02-19: Worked P5.5 (`Proof: checker soundness (if checker passes, forbidden intersections do not exist)` and `Proof: checker completeness for convex coplanar-face assumptions used by Phase 5`) with a pair-order symmetry groundwork increment in:
  - `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`;
  - `src/halfedge_mesh/tests.rs`.
  - added relation-level symmetry lemmas over the face-pair topology/contact surface:
    - `lemma_mesh_faces_share_vertex_spec_symmetric`;
    - `lemma_mesh_faces_share_edge_spec_symmetric`;
    - `lemma_mesh_faces_share_vertex_index_spec_symmetric`;
    - `lemma_mesh_faces_share_edge_index_spec_symmetric`;
    - `lemma_mesh_faces_share_exactly_one_vertex_spec_symmetric`;
    - `lemma_mesh_faces_share_exactly_one_edge_spec_symmetric`;
    - `lemma_mesh_faces_disjoint_boundary_spec_symmetric`;
    - `lemma_mesh_faces_share_zero_or_one_vertices_spec_symmetric`;
    - `lemma_mesh_non_adjacent_face_pair_forbidden_intersection_relation_spec_symmetric`.
  - added runtime parity lock coverage for swapped face-pair argument order:
    - helper `assert_face_pair_policy_classifiers_are_symmetric_under_face_argument_swap`;
    - integrated into `allowed_contact_topology_classifier_matches_edge_index_oracle`.
  - outcome:
    - P5.5 proof surface now has explicit symmetry lemmas for core pair relations used by forbidden-policy decomposition;
    - runtime regression coverage now locks classifier invariance under `(face_a, face_b)` vs `(face_b, face_a)` for allowed-contact topology and forbidden-intersection pair hooks.
- 2026-02-19: Failed attempt in this P5.5 pair-order symmetry pass:
  - initial pass added higher-order symmetry lemmas for full two-vertex and full runtime-policy relations (`mesh_faces_share_exactly_two_vertices_spec` and derived classifier/policy symmetry), but Verus hit an rlimit blow-up on the quantified two-vertex symmetry lemma;
  - resolved by trimming those high-cost lemmas and keeping the lower-level symmetry layer that verifies quickly.
- 2026-02-19: Revalidated after the P5.5 pair-order symmetry increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (63 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (86 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (346 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
- 2026-02-19: Worked P5.5 (`Proof: checker soundness (if checker passes, forbidden intersections do not exist)` and `Proof: checker completeness for convex coplanar-face assumptions used by Phase 5`) with a disjoint-boundary policy-branch lock + relation-level corollary increment in:
  - `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`;
  - `src/halfedge_mesh/tests.rs`.
  - added relation-level forbidden-policy corollaries:
    - `lemma_mesh_faces_shared_boundary_allowed_contact_relation_not_runtime_forbidden_policy`;
    - `lemma_mesh_disjoint_boundary_and_allowed_contact_relation_and_no_intersection_imply_not_runtime_forbidden_policy`;
    - `lemma_mesh_disjoint_boundary_and_allowed_contact_relation_and_intersection_imply_runtime_forbidden_policy`.
  - added pair-level disjoint-boundary regression coverage:
    - helper `assert_disjoint_boundary_pairs_match_forbidden_classification`;
    - test `disjoint_boundary_pair_policy_branch_matches_expected_forbidden_classification`.
  - outcome:
    - P5.5 now has direct relation-level corollaries for shared-boundary non-forbidden behavior and disjoint-boundary intersection/non-intersection classification, reducing classifier-surface plumbing in remaining soundness/completeness proofs;
    - runtime regressions now explicitly lock the disjoint-boundary branch used by those proofs (including broad-phase/no-cull parity).
- 2026-02-19: Failed attempts in this P5.5 disjoint-boundary policy-branch pass: none.
- 2026-02-19: Revalidated after the P5.5 disjoint-boundary policy-branch increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (63 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (86 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (337 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (374 verified, 0 errors)
- 2026-02-19: Worked P5.5 (`Proof: checker soundness (if checker passes, forbidden intersections do not exist)` and `Proof: checker completeness for convex coplanar-face assumptions used by Phase 5`) with an allowed-contact-spec normalization increment in:
  - `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`.
  - added high-level allowed-contact decomposition lemmas for runtime forbidden-policy classification:
    - `lemma_mesh_face_pair_runtime_forbidden_policy_iff_not_allowed_contact_relation_or_disjoint_boundary_and_intersection`;
    - `lemma_mesh_not_allowed_contact_relation_implies_runtime_forbidden_policy`;
    - `lemma_mesh_disjoint_boundary_and_allowed_contact_relation_imply_runtime_forbidden_policy_iff_intersection`.
  - outcome:
    - P5.5 forbidden-policy proof decomposition is now available directly over the high-level
      `mesh_faces_allowed_contact_relation_spec` surface (not only the runtime branch-classifier surface);
    - this reduces branch-classifier plumbing in downstream soundness/completeness arguments while keeping the checklist items open.
- 2026-02-19: Failed attempts in this P5.5 allowed-contact normalization pass:
  - first verification runs failed due parser errors from trailing commas inside two new `assert(...)` expressions in `model_and_bridge_specs.rs`;
  - resolved by removing those trailing commas and rerunning verification/tests.
- 2026-02-19: Revalidated after the P5.5 allowed-contact normalization increment:
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" non_allowed_contact_topology_pairs_are_classified_as_forbidden` (1 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (85 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (334 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
- 2026-02-19: Worked P5.7 (`Prove aggregate checker equivalence to aggregate Phase 5 spec`) with a kernel-shared-edge characterization-gap lock increment for zero-length-edge fixtures in:
  - `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`;
  - `src/halfedge_mesh/tests.rs`.
  - added a new constructive bridge entry point:
    - `runtime_check_phase4_valid_and_kernel_shared_edge_local_orientation_imply_geometric_topological_consistency_spec`.
  - this bridge proves aggregate model-spec admission from:
    - Phase 4 validity witness (`is_valid_constructive`);
    - kernel shared-edge local-orientation bridge witness (`runtime_check_shared_edge_local_orientation_kernel_bridge`);
    - without requiring the runtime shared-edge checker precondition path.
  - added zero-length aggregate-spec gap lock coverage:
    - helper fixture `build_zero_length_single_triangle_pair_mesh`;
    - helper assertion `assert_phase4_kernel_shared_edge_spec_zero_length_gap`;
    - deterministic regression:
      - `zero_length_fixture_keeps_phase4_and_kernel_shared_edge_spec_but_fails_aggregate_gate`;
    - randomized differential harness:
      - `differential_randomized_zero_length_phase4_kernel_shared_edge_spec_gap_harness` (base + rigid transform + reflected variants).
  - outcome:
    - P5.7 gap coverage now explicitly includes the previously blocked zero-length class via kernel shared-edge characterization, showing:
      - aggregate model spec still admits the fixture under Phase4+kernel-shared-edge assumptions;
      - runtime aggregate gate deterministically rejects it at `ZeroLengthGeometricEdge`.
    - this tightens blocker visibility for aggregate checker/spec equivalence without changing the current open status of the P5.7 proof item.
- 2026-02-19: Failed attempts in this P5.7 kernel-shared-edge zero-length gap pass:
  - first pass left `build_zero_length_single_triangle_pair_mesh` behind `#[cfg(feature = "geometry-checks")]`, producing a dead-code warning in geometry-only test builds;
  - resolved by tightening the helper gate to `#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]`.
- 2026-02-19: Revalidated after the P5.7 kernel-shared-edge zero-length gap increment:
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" phase4_kernel_shared_edge_spec` (1 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" zero_length_fixture_keeps_phase4_and_kernel_shared_edge_spec_but_fails_aggregate_gate` (1 passed, 0 failed)
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (62 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (85 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (331 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (368 verified, 0 errors)
- 2026-02-19: Worked P5.1 (`Proof: runtime checker correctness vs spec (sound + complete under documented preconditions)`) with a high-arity (`k >= 5`) coplanarity parity-lock increment in:
  - `src/halfedge_mesh/tests.rs`.
  - added reusable high-arity closed-face fixtures:
    - `build_single_pentagon_double_face_mesh_with_apex_lift`;
    - `build_coplanar_single_pentagon_double_face_mesh`;
    - `build_noncoplanar_single_pentagon_double_face_mesh_with_lift`.
  - extended coplanarity checker/spec parity coverage to include pentagon-face (`k = 5`) closed fixtures:
    - deterministic exhaustive-oracle parity now includes both:
      - coplanar high-arity pentagon face-pair fixture;
      - noncoplanar lifted high-arity pentagon face-pair fixture.
    - randomized differential coplanarity harness now additionally:
      - includes the noncoplanar high-arity pentagon in failing fixtures;
      - exercises rigid-transform/relabel/reflection parity on the coplanar high-arity pentagon fixture.
  - extended constructive/bridge parity surface with the same high-arity fixtures:
    - `geometric_consistency_constructive_gate_matches_runtime_boolean_gate`;
    - `face_coplanarity_seed0_bridge_matches_runtime_checker`;
    - `face_coplanarity_seed0_sound_bridge_matches_runtime_checker`.
  - outcome:
    - the P5.1 high-arity path now has explicit `k = 5` runtime-vs-exhaustive-oracle and seed0-bridge parity locks (including transformed/relabelled variants), reducing regression risk on the remaining unrestricted-arity proof gap;
    - full formal checker/spec equivalence proof for unrestricted face arity remains open.
- 2026-02-19: Failed attempt in this P5.1 high-arity parity-lock pass:
  - attempted to run formatter via `cargo fmt --all`, but `cargo fmt`/`rustfmt` are unavailable in this environment (`no such command: fmt`, `rustfmt: command not found`).
- 2026-02-19: Revalidated after the P5.1 high-arity parity-lock increment:
  - `cargo test -p vcad-topology --features geometry-checks` (62 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (83 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (331 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (368 verified, 0 errors)
- 2026-02-19: Worked P5.5 (`Proof: checker soundness (if checker passes, forbidden intersections do not exist)` and `Proof: checker completeness for convex coplanar-face assumptions used by Phase 5`) with an aggregate/pairwise classification parity-lock increment in:
  - `src/halfedge_mesh/tests.rs`.
  - added a reusable explicit pairwise oracle:
    - helper `no_forbidden_face_face_intersections_pairwise_oracle`.
  - strengthened broad-phase parity coverage:
    - `assert_forbidden_face_face_checker_broad_phase_sound` now additionally asserts:
      - aggregate broad-phase checker result matches explicit all-face-pairs oracle evaluation with broad-phase enabled;
      - aggregate no-cull checker result matches explicit all-face-pairs oracle evaluation with broad-phase disabled;
      - broad-phase and no-cull aggregate outcomes remain equal.
  - outcome:
    - P5.5 checker behavior is now locked against an explicit pairwise decomposition path in both culling modes (not only broad-vs-no-cull parity), reducing regression risk in aggregate/pair integration while formal soundness/completeness proofs remain open.
- 2026-02-19: Failed attempts in this P5.5 aggregate/pairwise parity-lock pass: none.
- 2026-02-19: Revalidated after the P5.5 aggregate/pairwise parity-lock increment:
  - `cargo test -p vcad-topology --features geometry-checks broad_phase_face_pair_culling_matches_no_cull_oracle` (1 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks differential_randomized_forbidden_intersection_checker_harness` (1 passed, 0 failed)
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (62 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (83 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (331 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (368 verified, 0 errors)
- 2026-02-19: Worked P5.5 (`Proof: checker soundness (if checker passes, forbidden intersections do not exist)`) with a runtime-policy decomposition + non-allowed-topology lock increment in:
  - `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`;
  - `src/halfedge_mesh/tests.rs`.
  - added a reusable runtime face-pair forbidden-policy spec surface:
    - `mesh_face_pair_runtime_forbidden_intersection_policy_spec`;
    - decomposition lemmas:
      - `lemma_mesh_face_pair_runtime_forbidden_policy_iff_not_allowed_or_disjoint_boundary_and_intersection`;
      - `lemma_mesh_not_allowed_contact_runtime_branch_classifier_implies_runtime_forbidden_policy`;
      - `lemma_mesh_faces_shared_boundary_runtime_branch_classifier_not_runtime_forbidden_policy`;
      - `lemma_mesh_disjoint_boundary_and_runtime_allowed_contact_imply_runtime_forbidden_policy_iff_intersection`.
  - added runtime regression coverage for the topological early-reject branch:
    - helper `assert_non_allowed_contact_topology_pairs_are_forbidden`;
    - test `non_allowed_contact_topology_pairs_are_classified_as_forbidden` (coincident double-face fixture + rigid/reflection/relabel variants), asserting pair-level forbidden classification is stable with and without broad-phase culling and that aggregate forbidden-face checking rejects those meshes.
  - outcome:
    - the P5.5 soundness surface now has a named spec decomposition that explicitly captures the runtime pair-policy split between topological rejection and non-adjacent geometric-intersection rejection;
    - runtime regressions now lock the non-allowed shared-boundary branch directly at pair level (not only through aggregate rejection).
- 2026-02-19: Failed attempt in this P5.5 runtime-policy decomposition pass:
  - first prover run regressed in existing quad-coplanarity plumbing (`lemma_mesh_face_seed0_fixed_witness_and_quad_cycle_imply_face_coplanar_spec`, assertion on `is_coplanar(p0,p1,p2,p3)`), causing `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` to fail with one proof error;
  - resolved by restoring a direct `by`-block fixed-witness instantiation at concrete index `d = 3` for that assertion, which stabilized trigger instantiation.
- 2026-02-19: Revalidated after the P5.5 runtime-policy decomposition + non-allowed-topology lock increment:
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" non_allowed_contact_topology_pairs_are_classified_as_forbidden` (1 passed, 0 failed)
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (62 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (83 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (331 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (368 verified, 0 errors)
- 2026-02-19: Worked P5.5 (`Proof: checker soundness (if checker passes, forbidden intersections do not exist)`) with a forbidden-relation decomposition + shared-boundary exclusion refactor increment in:
  - `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`.
  - added reusable forbidden-relation decomposition lemmas:
    - `lemma_mesh_non_adjacent_face_pair_forbidden_relation_implies_disjoint_boundary_and_intersection`;
    - `lemma_mesh_disjoint_boundary_and_intersection_imply_non_adjacent_face_pair_forbidden_relation`;
    - `lemma_mesh_non_adjacent_face_pair_forbidden_relation_iff_disjoint_boundary_and_intersection`;
    - `lemma_mesh_non_disjoint_boundary_implies_not_non_adjacent_face_pair_forbidden_relation`.
  - refactored:
    - `lemma_mesh_faces_shared_boundary_runtime_branch_classifier_not_non_adjacent_forbidden_relation`
    - to route through the new non-disjoint-boundary exclusion lemma instead of the previous local contradiction-only proof.
  - outcome:
    - the P5.5 proof surface now has an explicit iff decomposition for the non-adjacent forbidden relation and a reusable non-disjoint-boundary exclusion lemma;
    - this reduces duplicated case-splitting for the remaining open checker soundness/completeness work.
- 2026-02-19: Failed attempt in this P5.5 forbidden-relation decomposition pass:
  - first prover run introduced a trigger-instantiation regression in existing quad-cycle plumbing (`lemma_mesh_face_seed0_fixed_witness_and_quad_cycle_imply_face_coplanar_spec`, assertion on `is_coplanar(p0,p1,p2,p3)`), causing `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` to fail with one proof error;
  - resolved by replacing the fragile `by` instantiation with a direct fixed-witness assertion at the concrete indices (`0,1,2,3`), restoring stable verification.
- 2026-02-19: Revalidated after the P5.5 forbidden-relation decomposition/refactor increment:
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" face_coplanarity_seed0_triangle_or_quad_sound_complete_bridge_matches_runtime_checker` (1 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" shared_edge_contacts_are_not_misclassified_as_forbidden_intersections` (1 passed, 0 failed)
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (61 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (82 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (327 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (364 verified, 0 errors)
- 2026-02-19: Worked P5.3 (`Proof: runtime checker correctness vs convexity spec`) with a triangle-face sound-bridge contract-hardening + parity-surface expansion increment in:
  - `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`;
  - `src/halfedge_mesh/tests.rs`.
  - strengthened `runtime_check_face_convexity_triangle_projected_turn_sound_bridge` postconditions so successful runs now additionally export:
    - `mesh_valid_spec(m@)`;
    - `mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m)`;
    - `mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)`;
    - `mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m)`;
    - `mesh_runtime_all_faces_oriented_seed0_planes_spec(m)`;
    - alongside the existing projected-turn consequence
      `mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m)`.
  - expanded convexity bridge parity coverage by wiring
    `assert_face_convexity_triangle_projected_turn_sound_bridge_parity` into
    `assert_constructive_phase5_gate_parity` for all-triangle fixtures.
  - outcome:
    - the triangle convexity sound bridge now exposes the full seed-0 coplanarity/validity artifacts it already depends on, reducing downstream proof-plumbing friction;
    - triangle-only convexity bridge/runtime parity now rides on the shared deterministic + seeded-randomized constructive parity harness surface, tightening regression lock while the mixed/high-arity P5.3 checker/spec proof remains open.
- 2026-02-19: Failed attempts in this P5.3 triangle-face contract-hardening/parity pass: none.
- 2026-02-19: Revalidated after the P5.3 triangle-face contract-hardening/parity increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (61 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (82 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (323 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (360 verified, 0 errors)
- 2026-02-19: Worked P5.1 (`Proof: runtime checker correctness vs spec (sound + complete under documented preconditions)`) with a triangle/quad sound+complete bridge consolidation increment in:
  - `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`;
  - `src/halfedge_mesh/tests.rs`.
  - strengthened the base seed-0 coplanarity sound bridge:
    - `runtime_check_face_coplanarity_seed0_fixed_witness_sound_bridge` now additionally proves `out ==> mesh_valid_spec(m@)` by threading a constructive Phase-4 witness (`is_valid_constructive`) through `lemma_validity_gate_witness_api_ok_implies_mesh_valid`;
    - propagated the same `out ==> mesh_valid_spec(m@)` guarantee through `runtime_check_face_coplanarity_seed0_fixed_witness_triangle_or_quad_sound_bridge`.
  - added a composed triangle/quad bridge:
    - `runtime_check_face_coplanarity_seed0_fixed_witness_triangle_or_quad_sound_complete_bridge`;
    - this wrapper composes:
      - triangle/quad soundness (`runtime_check_face_coplanarity_seed0_fixed_witness_triangle_or_quad_sound_bridge`);
      - triangle/quad oriented-seed-plane completeness (`runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_and_triangle_or_quad_face_preconditions`);
    - and exposes both `mesh_valid_spec(m@)` and full triangle/quad coplanarity/spec bridge outputs on success.
  - extended regression/parity coverage:
    - helper `assert_face_coplanarity_seed0_triangle_or_quad_sound_complete_bridge_parity`;
    - test `face_coplanarity_seed0_triangle_or_quad_sound_complete_bridge_matches_runtime_checker`;
    - integrated the new parity assertion into `assert_constructive_phase5_gate_parity` for all triangle/quad fixtures.
  - outcome:
    - the P5.1 triangle/quad path now carries explicit Phase-4 validity in its soundness output and has a dedicated composed sound+complete bridge locked against runtime parity;
    - the remaining open P5.1 work is unchanged: full unrestricted (`k > 4`) checker/spec equivalence.
- 2026-02-19: Failed attempts in this P5.1 triangle/quad sound+complete consolidation pass: none.
- 2026-02-19: Revalidated after the P5.1 triangle/quad sound+complete consolidation increment:
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" face_coplanarity_seed0_triangle_or_quad_sound_complete_bridge_matches_runtime_checker` (1 passed, 0 failed)
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (61 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (82 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (323 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (360 verified, 0 errors)
- 2026-02-19: Worked P5.3 (`Proof: runtime checker correctness vs convexity spec`) with a triangle-face projected-turn soundness increment in:
  - `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`;
  - `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`;
  - `src/halfedge_mesh/tests.rs`.
  - added projected-turn proof/model bridge lemmas:
    - `lemma_triangle_face_seed0_projected_turn_sign_nonzero_from_nonzero_seed_normal`;
    - `lemma_mesh_all_faces_seed0_corner_non_collinear_and_triangle_cycles_imply_all_faces_projected_turn_sign_consistency`;
    - `lemma_mesh_runtime_all_faces_seed0_corner_non_collinear_and_triangle_cycles_imply_all_faces_projected_turn_sign_consistency`;
    - runtime alias spec `mesh_runtime_all_faces_projected_turn_sign_consistency_spec`.
  - added constructive runtime wrapper:
    - `runtime_check_face_convexity_triangle_projected_turn_sound_bridge`, proving triangle-face convexity runtime success implies projected-turn-sign consistency spec.
  - added regression parity coverage:
    - helper `assert_face_convexity_triangle_projected_turn_sound_bridge_parity`;
    - test `face_convexity_triangle_projected_turn_sound_bridge_matches_runtime_checker` (triangle fixtures: tetrahedron, overlapping tetrahedra, collinear triangle-pair failure, zero-length-edge triangle-pair failure).
  - outcome:
    - P5.3 now has a direct verified runtime-to-projected-turn-spec sound bridge for the all-triangle face class;
    - mixed/high-arity face correctness-vs-spec proof remains open.
- 2026-02-19: Failed attempt in this P5.3 triangle-face soundness pass:
  - first proof draft called non-public `vcad_math::Scalar` lemmas (`lemma_sub_swap_neg`, `lemma_signum_zero_iff`, `lemma_eqv_zero_iff_num_zero`) and failed under `verus_keep_ghost` verification;
  - resolved by rewriting those steps using public lemmas (`lemma_sub_antisymmetric`, `lemma_eqv_signum`) plus direct signum/num case reasoning.
- 2026-02-19: Revalidated after the P5.3 triangle-face projected-turn soundness increment:
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" face_convexity_triangle_projected_turn_sound_bridge_matches_runtime_checker` (1 passed, 0 failed)
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (61 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (81 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (323 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (360 verified, 0 errors)
- 2026-02-19: Worked P5.7 (`Prove aggregate checker equivalence to aggregate Phase 5 spec`) by extending the existing spec/runtime characterization-gap lock surface in:
  - `src/halfedge_mesh/tests.rs`.
  - added a new deterministic + randomized gap class for the currently missing aggregate-spec coverage of face-corner non-collinearity:
    - helper fixture `build_collinear_single_triangle_pair_mesh`;
    - new `Phase4SharedEdgeSpecGapFailure::CollinearCorner` branch in `assert_phase4_shared_edge_spec_characterization_gap`;
    - new regression `collinear_fixture_keeps_phase4_and_shared_edge_orientation_but_fails_aggregate_gate`;
    - extended randomized multiclass gap harness (`differential_randomized_multiclass_phase4_shared_edge_spec_gap_harness`) to include the collinear class.
  - outcome:
    - aggregate-spec gap coverage now explicitly includes all of:
      - face non-coplanarity;
      - face non-convexity;
      - forbidden face-face intersection;
      - inward/degenerate outwardness failure;
      - face-corner collinearity.
    - this tightens blocker visibility for P5.7 while preserving the current open status (runtime checker/spec equivalence still not proved).
- 2026-02-19: Failed attempt in this P5.7 gap pass:
  - first attempted to add a zero-length-edge gap class, but the fixture cannot satisfy the shared-edge-local-orientation precondition used by the current aggregate-spec characterization helper (`check_shared_edge_local_orientation_consistency()` explicitly requires `check_no_zero_length_geometric_edges()`), so that class was not a valid Phase4+shared-edge characterization counterexample and was replaced by the collinear-corner class above.
- 2026-02-19: Revalidated after the P5.7 gap-harness extension:
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" collinear_fixture_keeps_phase4_and_shared_edge_orientation_but_fails_aggregate_gate` (1 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" differential_randomized_multiclass_phase4_shared_edge_spec_gap_harness` (1 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (80 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (320 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (357 verified, 0 errors)
- 2026-02-19: Worked P5.1 (`Proof: runtime checker correctness vs spec (sound + complete under documented preconditions)`) by scoping the remaining `k > 4` completeness gap and adding a blocker-lock regression in:
  - `src/halfedge_mesh/tests.rs`.
  - added regression:
    - `seed0_fixed_witness_without_noncollinear_seed_is_insufficient_for_k_ge_5`.
  - regression purpose:
    - encodes a concrete 5-point counterexample where a collinear seed triple `(p0,p1,p2)` makes all seed-fixed witness checks `is_coplanar(p0,p1,p2,pd)` pass for `d in {0,1,2,3,4}`, but full all-quadruple coplanarity fails (`!is_coplanar(p0,p1,p3,p4)`).
  - outcome:
    - formally locks the key proof blocker: for `k >= 5`, seed-fixed witness alone is insufficient without a non-collinear seed (or equivalent oriented-plane strength), so remaining P5.1 completeness work must keep that stronger precondition explicit.
- 2026-02-19: Failed attempt in this P5.1 `k > 4` scoping pass:
  - first attempted to generalize triangle/quad completeness from `mesh_face_coplanar_seed0_fixed_witness_spec` alone to arbitrary face arity;
  - blocked by the collinear-seed counterexample above, so the pass pivoted to adding the explicit regression lock instead of landing an unsound generalization.
- 2026-02-19: Revalidated after the P5.1 `k > 4` blocker-lock regression:
  - `cargo test -p vcad-topology --features geometry-checks seed0_fixed_witness_without_noncollinear_seed_is_insufficient_for_k_ge_5` (1 passed, 0 failed)
- 2026-02-19: Worked P5.1 (`Proof: runtime checker correctness vs spec (sound + complete under documented preconditions)`) with a triangle/quad soundness bridge increment in:
  - `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`;
  - `src/halfedge_mesh/tests.rs`.
  - added constructive soundness wrapper:
    - `runtime_check_face_coplanarity_seed0_fixed_witness_triangle_or_quad_sound_bridge`, proving:
      - if `Mesh::check_face_coplanarity()` passes and all faces are triangle/quad cycles, then `mesh_runtime_all_faces_coplanar_spec(m)` holds;
      - along with existing seed0 coplanarity/oriented-plane bridge obligations.
  - added regression parity coverage:
    - helper `assert_face_coplanarity_runtime_seed0_triangle_or_quad_sound_bridge_parity`;
    - test `face_coplanarity_seed0_triangle_or_quad_sound_bridge_matches_runtime_checker` (triangle/quad passing and failing fixtures: tetrahedron, cube, triangular prism, overlapping tetrahedra, reflected-cube outward failure, noncoplanar quad pair, collinear triangle pair, zero-length-edge triangle pair).
  - outcome: P5.1 now has a direct runtime-to-full-spec soundness route for triangle/quad meshes; combined with the existing triangle/quad completeness wrappers, checker/spec correctness is now locked for that documented precondition class, while the high-arity face (`k > 4`) proof gap remains.
- 2026-02-19: Failed attempts in this P5.1 triangle/quad soundness pass: none.
- 2026-02-19: Revalidated after the P5.1 triangle/quad soundness increment:
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" face_coplanarity_seed0_triangle_or_quad_sound_bridge_matches_runtime_checker` (1 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (78 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (320 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (357 verified, 0 errors)
- 2026-02-19: Worked P5.1 (`Proof: runtime checker correctness vs spec (sound + complete under documented preconditions)`) with a mixed triangle/quad completeness bridge increment in:
  - `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`;
  - `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`;
  - `src/halfedge_mesh/tests.rs`.
  - added mixed face-cycle proof/model surface:
    - `mesh_all_faces_triangle_or_quad_cycles_spec`;
    - `mesh_runtime_all_faces_triangle_or_quad_cycles_spec`;
    - `lemma_mesh_all_faces_coplanar_seed0_fixed_witness_and_triangle_or_quad_cycles_imply_all_faces_coplanar`;
    - `lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_and_triangle_or_quad_cycles_imply_all_faces_coplanar`;
    - `lemma_mesh_runtime_all_faces_oriented_seed0_planes_and_triangle_or_quad_cycles_imply_all_faces_coplanar`.
  - added constructive wrapper:
    - `runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_and_triangle_or_quad_face_preconditions`, proving full `mesh_runtime_all_faces_coplanar_spec` completeness from:
      - Phase 4 validity;
      - all-face oriented seed0 planes; and
      - all-face triangle-or-quad cycle preconditions.
  - added regression parity coverage:
    - helper `mesh_all_faces_are_triangles_or_quads`;
    - helper `assert_face_coplanarity_seed0_oriented_plane_triangle_or_quad_completeness_bridge_parity`;
    - test `face_coplanarity_seed0_oriented_plane_triangle_or_quad_completeness_bridge_matches_geometric_sound_bridge` (triangle-only, quad-only, and mixed fixtures: tetrahedron, cube, triangular prism, overlapping tetrahedra, reflected-cube outward failure, noncoplanar single-quad double-face lift).
  - outcome: the P5.1 completeness surface now has a direct oriented-seed-plane route for meshes whose faces are all triangles or quads; the remaining non-triangle completeness gap is narrowed to higher-arity faces (`k > 4`).
- 2026-02-19: Failed attempt in this P5.1 mixed triangle/quad bridge pass:
  - first verification run failed in `lemma_mesh_face_seed0_fixed_witness_and_quad_cycle_imply_face_coplanar_spec` at a quantified `assert(forall|d| ...)` used to recover the `d = 3` coplanarity witness from `mesh_face_coplanar_fixed_seed_witness_spec`;
  - resolved by replacing that quantifier assertion with a direct fixed-witness instantiation in the `d = 3` branch (`assert(mesh_face_coplanar_fixed_seed_witness_spec(...)); assert(0 <= 3 < 4);`), which restored stable trigger instantiation under full Verus verification.
- 2026-02-19: Revalidated after the P5.1 mixed triangle/quad completeness increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (60 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (77 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" face_coplanarity_seed0_oriented_plane_triangle_or_quad_completeness_bridge_matches_geometric_sound_bridge` (1 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (320 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (357 verified, 0 errors)
- 2026-02-19: Worked P5.1 (`Proof: runtime checker correctness vs spec (sound + complete under documented preconditions)`) with a quad-cycle completeness bridge increment in:
  - `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`;
  - `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`;
  - `src/halfedge_mesh/tests.rs`.
  - added quad-cycle proof/model surface:
    - `mesh_all_faces_quad_cycles_spec`;
    - `mesh_runtime_all_faces_quad_cycles_spec`;
    - `mesh_quad_point_at_index_spec`;
    - index-combinatorics lemmas for `{0,1,2,3}` permutation reasoning:
      - `lemma_mesh_indices_in_0_1_2_3`;
      - `lemma_mesh_three_pairwise_distinct_indices_in_0_1_2_cover_all`;
      - `lemma_mesh_four_pairwise_distinct_indices_in_0_1_2_impossible`;
      - `lemma_mesh_quad_indices_pairwise_distinct_and_in_range_imply_contains_3`;
    - coplanarity bridge lemmas:
      - `lemma_mesh_quad_permutation_of_base_coplanar`;
      - `lemma_mesh_face_seed0_fixed_witness_and_quad_cycle_imply_face_coplanar_spec`;
      - `lemma_mesh_all_faces_coplanar_seed0_fixed_witness_and_quad_cycles_imply_all_faces_coplanar`;
      - `lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_and_quad_cycles_imply_all_faces_coplanar`;
      - `lemma_mesh_runtime_all_faces_oriented_seed0_planes_and_quad_cycles_imply_all_faces_coplanar`.
  - added constructive wrapper:
    - `runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_and_quad_face_preconditions`.
  - added regression parity coverage:
    - helper `assert_face_coplanarity_seed0_oriented_plane_quad_completeness_bridge_parity`;
    - helper `mesh_all_faces_are_quads`;
    - test `face_coplanarity_seed0_oriented_plane_quad_completeness_bridge_matches_geometric_sound_bridge` (quad-only passing/failing fixtures: cube, reflected-cube outward failure, noncoplanar single-quad double-face lift).
  - outcome: the P5.1 completeness surface now includes a direct oriented-seed-plane route to full coplanarity on quad-only meshes; the remaining non-triangle completeness gap is now concentrated on higher-arity faces (`k > 4`).
- 2026-02-19: Failed attempt in this P5.1 quad-cycle completeness pass:
  - initial proof body used `assert forall ... ==> ... by { ... }` in
    `lemma_mesh_face_seed0_fixed_witness_and_quad_cycle_imply_face_coplanar_spec`, which does not assume the antecedent inside `assert forall` and caused failed preconditions for `lemma_mesh_indices_in_0_1_2_3` during full Verus verification;
  - resolved by switching the quantified assertion to `implies`, so range hypotheses are available in the quantified body.
- 2026-02-19: Revalidated after the P5.1 quad-cycle completeness increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (60 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (76 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" face_coplanarity_seed0_oriented_plane_quad_completeness_bridge_matches_geometric_sound_bridge` (1 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (317 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (354 verified, 0 errors)
- 2026-02-19: Worked P5.1 (`Proof: runtime checker correctness vs spec (sound + complete under documented preconditions)`) with an oriented-seed-plane + triangle-cycle completeness bridge increment in:
  - `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`;
  - `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`;
  - `src/halfedge_mesh/tests.rs`.
  - added composed runtime lemma:
    - `lemma_mesh_runtime_all_faces_oriented_seed0_planes_and_triangle_cycles_imply_all_faces_coplanar`.
  - added constructive wrapper:
    - `runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_and_triangle_face_preconditions`, proving full `mesh_runtime_all_faces_coplanar_spec` completeness from:
      - Phase 4 validity;
      - all-face oriented seed0 planes; and
      - all-face triangle-cycle preconditions.
  - added regression parity coverage:
    - helper `assert_face_coplanarity_seed0_oriented_plane_triangle_completeness_bridge_parity`;
    - test `face_coplanarity_seed0_oriented_plane_triangle_completeness_bridge_matches_geometric_sound_bridge` (triangle-only passing/failing fixtures: tetrahedron, overlapping tetrahedra, reflected tetrahedron).
  - outcome: the P5.1 completeness surface now has a direct runtime bridge from oriented-seed-plane preconditions to full coplanarity on triangle-only meshes; the non-triangle (`k > 3`) checker/spec completeness gap remains open.
- 2026-02-19: Failed attempts in this P5.1 oriented+triangle bridge pass: none.
- 2026-02-19: Revalidated after the P5.1 oriented+triangle completeness increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (60 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (75 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" face_coplanarity_seed0_oriented_plane_triangle_completeness_bridge_matches_geometric_sound_bridge` (1 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (308 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (345 verified, 0 errors)
- 2026-02-19: Worked P5.5 (`Proof: shared-edge and shared-vertex contacts are never misclassified as forbidden intersections`) in `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added explicit corollary lemmas that discharge the two concrete allowed-contact cases against the forbidden non-adjacent relation:
    - `lemma_mesh_faces_shared_vertex_only_not_non_adjacent_forbidden_relation`;
    - `lemma_mesh_faces_shared_exactly_one_edge_not_non_adjacent_forbidden_relation`.
  - both corollaries route through the existing combined shared-boundary lemma and make the two non-misclassification obligations directly reusable by name for later checker soundness plumbing.
- 2026-02-19: Failed attempt while scoping this pass:
  - initially targeted P5.7 aggregate checker/spec equivalence, but `mesh_geometric_topological_consistency_spec` is currently characterized by `mesh_valid_spec && mesh_shared_edge_local_orientation_consistency_spec`, which is intentionally weaker than the runtime aggregate checker (`check_geometric_topological_consistency`) and therefore not directly equivalent without a broader spec-model-link strengthening pass.
  - pivoted to the narrower P5.5 shared-boundary non-misclassification proof task above.
- 2026-02-19: Revalidated after the P5.5 shared-boundary non-misclassification corollary increment:
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (74 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (307 verified, 0 errors)
- 2026-02-19: Worked P5.1 (`Proof: runtime checker correctness vs spec (sound + complete under documented preconditions)`) with an all-triangle completeness bridge increment in:
  - `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`;
  - `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`.
  - added triangle-cycle coplanarity bridge surface:
    - `mesh_all_faces_triangle_cycles_spec`;
    - `mesh_runtime_all_faces_triangle_cycles_spec`;
    - `lemma_mesh_face_seed0_fixed_witness_and_triangle_cycle_imply_face_coplanar_spec`;
    - `lemma_mesh_all_faces_coplanar_seed0_fixed_witness_and_triangle_cycles_imply_all_faces_coplanar`;
    - `lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_and_triangle_cycles_imply_all_faces_coplanar`.
  - added constructive wrapper:
    - `runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_triangle_face_preconditions`, proving full `mesh_runtime_all_faces_coplanar_spec` completeness from:
      - Phase 4 validity;
      - seed0 fixed-witness coplanarity;
      - seed0 non-collinearity;
      - all-face triangle-cycle preconditions.
  - outcome: the P5.1 completeness surface now has an explicit route from seed0 witness completeness to full coplanarity on triangle-only meshes, narrowing the remaining gap to non-triangle faces (`k > 3`).
- 2026-02-19: Failed attempt in this P5.1 all-triangle completeness pass:
  - initial quantifier instantiation in `lemma_mesh_face_seed0_fixed_witness_implies_coplanar_witness_for_triangle_face` stalled on proving `is_coplanar(p0, p1, p2, pd)` from the fixed-witness premise inside the quantified body;
  - resolved by replacing that direct instantiation with an explicit `d ∈ {0,1,2}` case split plus `lemma_mesh_orient3d_any_repeated_implies_coplanar`.
- 2026-02-19: Revalidated after the P5.1 all-triangle completeness increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (60 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (74 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (305 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (342 verified, 0 errors)
- 2026-02-19: Worked P5.1 (`Proof: runtime checker correctness vs spec (sound + complete under documented preconditions)`) with orient3d permutation/repeated-point coplanarity proof-plumbing in `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added reusable helper lemmas:
    - `lemma_mesh_scalar_signum_zero_iff_neg_signum_zero`;
    - `lemma_mesh_orient3d_coplanar_invariant_under_swap_ab`;
    - `lemma_mesh_orient3d_coplanar_invariant_under_swap_ac`;
    - `lemma_mesh_orient3d_coplanar_invariant_under_swap_ad`;
    - `lemma_mesh_orient3d_coplanar_invariant_under_swap_bc`;
    - `lemma_mesh_orient3d_coplanar_invariant_under_swap_bd`;
    - `lemma_mesh_orient3d_coplanar_invariant_under_swap_cd`;
    - `lemma_mesh_orient3d_any_repeated_implies_coplanar`.
  - integrated the new repeated-point helper into
    `lemma_mesh_face_seed0_fixed_witness_implies_coplanar_witness_for_triangle_face`
    so the degenerate/duplicate-index branch now routes through the generalized
    four-argument repeated-point coplanarity characterization (instead of only
    the first-three-repeated helper).
  - outcome: the P5.1 proof surface now has explicit reusable orient3d
    coplanarity invariance under all argument swaps and a single generalized
    repeated-point coplanarity lemma, reducing permutation/repetition plumbing
    in the remaining non-triangle (`k > 3`) checker/spec equivalence work.
- 2026-02-19: Failed attempt in this P5.1 permutation/repeated-point plumbing pass:
  - after expanding the triangle proof branch condition to include repeated-index
    cases involving `d`, Verus stopped discharging a quantified
    `assert(forall|dp| ... is_coplanar(..., dp))` in the triangle theorem body;
  - resolved by replacing that broad quantifier assertion with a direct
    instantiation on the required `d` witness (`assert(is_coplanar(..., pd)) by { assert(0 <= d < 3); }`).
- 2026-02-19: Revalidated after the P5.1 permutation/repeated-point plumbing increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (60 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (74 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (302 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (339 verified, 0 errors)
- 2026-02-19: Worked P5.1 (`Proof: runtime checker correctness vs spec (sound + complete under documented preconditions)`) with a triangle-face full-coplanarity bridge increment in `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added helper lemmas:
    - `lemma_mesh_indices_in_0_1_2`;
    - `lemma_mesh_orient3d_first_three_repeated_implies_coplanar`.
  - added theorem:
    - `lemma_mesh_face_seed0_fixed_witness_implies_coplanar_witness_for_triangle_face`, proving that for `k = 3` faces, seed0 fixed-witness coplanarity is sufficient to recover the full face-coplanarity witness (`mesh_face_coplanar_witness_spec`), including all first-triple permutation cases.
  - outcome: the remaining P5.1 full-spec completeness gap is now reduced to non-triangle faces (`k > 3`), where a reusable proof that seed0-plane membership implies arbitrary-triple coplanarity is still missing.
- 2026-02-19: Failed attempt in this P5.1 pass:
  - attempted to generalize seed0-fixed-witness-to-full-coplanarity from triangles to arbitrary polygon face cycles in one theorem; this stalled on the missing intermediate lemma for `k > 3` that lifts shared seed-plane membership to arbitrary first-triple `orient3d = 0` across all quadruples.
- 2026-02-19: Revalidated after the P5.1 triangle-face bridge increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (60 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (74 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (294 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (331 verified, 0 errors)
- 2026-02-19: Worked P5.5 (`Proof: shared-edge and shared-vertex contacts are never misclassified as forbidden intersections`) with a generalized shared-boundary classifier-exclusion theorem increment in `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added generalized theorem
    `lemma_mesh_faces_shared_boundary_runtime_branch_classifier_not_non_adjacent_forbidden_relation`, proving that for any face pair already accepted by the runtime allowed-contact branch classifier, if the pair shares any boundary (`share_vertex || share_edge`) then it cannot satisfy `mesh_non_adjacent_face_pair_forbidden_intersection_relation_spec` for any `geometric_intersection_exists` flag;
  - refactored
    `lemma_mesh_faces_shared_boundary_allowed_contact_not_non_adjacent_forbidden_relation`
    to route through the generalized theorem after discharging the shared-boundary premise from the exact-one-shared-vertex / exact-one-shared-edge branches.
  - outcome: the shared-boundary non-misclassification proof surface now includes an explicit branch-classifier-level exclusion theorem reusable by future checker-soundness work; the broader P5.5 checker soundness/completeness checklist items remain open.
- 2026-02-19: Failed attempts in this P5.5 shared-boundary classifier-exclusion pass: none.
- 2026-02-19: Revalidated after the P5.5 shared-boundary classifier-exclusion increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (60 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (74 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (291 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (328 verified, 0 errors)
- 2026-02-19: Worked P5.5 (`Proof: shared-edge and shared-vertex contacts are never misclassified as forbidden intersections`) with a spec-level non-adjacent-forbidden exclusion theorem increment in `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added helper lemmas:
    - `lemma_mesh_faces_share_exactly_one_vertex_implies_share_vertex`;
    - `lemma_mesh_faces_share_exactly_one_edge_implies_share_edge`.
  - added theorem:
    - `lemma_mesh_faces_shared_boundary_allowed_contact_not_non_adjacent_forbidden_relation`, proving that for distinct in-bounds face pairs in either shared-boundary allowed-contact branch:
      - exactly-one-shared-vertex with no shared edge; or
      - exactly-one-shared-edge with exactly-two-shared-vertices;
      the pair:
      - satisfies `mesh_faces_allowed_contact_relation_spec`;
      - satisfies `mesh_faces_allowed_contact_runtime_branch_classifier_spec`; and
      - cannot satisfy `mesh_non_adjacent_face_pair_forbidden_intersection_relation_spec` for any `geometric_intersection_exists` flag (because shared-boundary contact contradicts the disjoint-boundary requirement in the forbidden non-adjacent relation).
  - outcome: the model surface now has an explicit formal theorem locking shared-boundary non-adjacent-forbidden exclusion and classifier parity for shared-edge/shared-vertex allowed-contact topologies; the full runtime-checker misclassification proof item remains open because geometric narrow-phase acceptance for shared-boundary contacts is not yet formally bridged.
- 2026-02-19: Failed attempts in this P5.5 shared-boundary non-adjacent-forbidden exclusion pass: none.
- 2026-02-19: Revalidated after the P5.5 shared-boundary non-adjacent-forbidden exclusion increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (60 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (74 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (290 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (327 verified, 0 errors)
- 2026-02-19: Worked P5.1 (`Proof: runtime checker correctness vs spec (sound + complete under documented preconditions)`) with an oriented-seed-plane completeness bridge increment in `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`:
  - added
    `runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_preconditions`;
  - bridge preconditions:
    - `mesh_valid_spec(m@)`;
    - `mesh_runtime_all_faces_oriented_seed0_planes_spec(m)`;
  - bridge proof path:
    - derives runtime geometry bridge + index/face-cycle obligations from `mesh_valid_spec(m@)`;
    - uses
      `lemma_mesh_runtime_all_faces_oriented_seed0_planes_and_index_bounds_and_face_cycles_iff_seed0_fixed_witness_and_seed0_non_collinear`
      to recover seed0-fixed coplanarity witnesses and seed0 non-collinearity;
    - discharges checker completeness by reusing
      `runtime_check_face_coplanarity_seed0_fixed_witness_complete_under_preconditions`.
  - added parity coverage in `src/halfedge_mesh/tests.rs`:
    - helper `assert_face_coplanarity_seed0_oriented_plane_completeness_bridge_parity`;
    - regression `face_coplanarity_seed0_oriented_plane_completeness_bridge_matches_geometric_sound_bridge`;
    - integrated oriented-plane completeness parity into `assert_constructive_phase5_gate_parity`.
  - outcome: runtime coplanarity completeness is now proved from the oriented-seed-plane formulation (not only from full-coplanarity or Phase-5-bundle preconditions), reducing the remaining P5.1 equivalence gap to proving oriented-seed-plane/seed0 witnesses imply the full `mesh_runtime_all_faces_coplanar_spec` formulation.
- 2026-02-19: Failed attempts in this P5.1 oriented-plane completeness pass: none.
- 2026-02-19: Revalidated after the P5.1 oriented-plane completeness increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (60 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (74 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" face_coplanarity_seed0_oriented_plane_completeness_bridge_matches_geometric_sound_bridge` (1 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (287 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (324 verified, 0 errors)
- 2026-02-19: Completed P5.5 (`Proof: adjacency-exemption implementation is equivalent to the allowed-contact spec`) in `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - normalized `mesh_faces_disjoint_boundary_spec(m, f1, f2)` to the equivalent no-shared-boundary formulation (`!share_vertex && !share_edge`) while preserving face-index bounds;
  - added proof theorem
    `lemma_mesh_faces_allowed_contact_relation_iff_runtime_branch_classifier`, proving
    `mesh_faces_allowed_contact_relation_spec(m, f1, f2)` iff
    `mesh_faces_allowed_contact_runtime_branch_classifier_spec(m, f1, f2)`;
  - outcome: the allowed-contact spec now has a formal equivalence theorem to the runtime branch-structured adjacency classifier spec, closing this P5.5 checklist item.
- 2026-02-19: Failed attempts in this P5.5 equivalence-closure pass:
  - initial theorem drafts against the original quantified disjoint-boundary encoding stalled on quantifier-trigger instantiation;
  - resolved by proving over the equivalent normalized disjoint-boundary form already used by the classifier-level reasoning.
- 2026-02-19: Revalidated after the P5.5 adjacency-exemption equivalence closure:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (60 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (73 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (287 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (324 verified, 0 errors)
- 2026-02-19: Worked P5.5 (`Proof: adjacency-exemption implementation is equivalent to the allowed-contact spec`) with a spec-normalization increment in `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added `mesh_faces_share_zero_or_one_vertices_spec(m, f1, f2)` to encode the runtime no-shared-edge branch cardinality condition (`0/1` shared vertices);
  - added `mesh_faces_allowed_contact_runtime_branch_classifier_spec(m, f1, f2)` as a branch-structured Phase 5 allowed-contact classifier spec:
    - no shared edge + `0/1` shared vertices; or
    - exactly one shared edge + exactly two shared vertices.
  - outcome: the runtime adjacency-exemption branch policy is now explicitly represented in the proof model surface, narrowing the remaining P5.5 equivalence gap to proving this normalized classifier matches `mesh_faces_allowed_contact_relation_spec`.
- 2026-02-19: Failed attempt in this P5.5 classifier-normalization pass:
  - attempted to land a full theorem
    `lemma_mesh_faces_allowed_contact_relation_iff_runtime_branch_classifier`
    (including a disjoint-boundary characterization bridge), but Verus repeatedly failed quantifier-trigger instantiation around `mesh_faces_disjoint_boundary_spec` witness extraction;
  - rolled back the failing theorem/bridge lemmas to keep the tree green, while retaining the new classifier specs as a stable proof target for follow-up.
- 2026-02-19: Revalidated after the P5.5 classifier-normalization increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (60 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (73 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (324 verified, 0 errors)
- 2026-02-19: Worked P5.4 (`Proof: global outwardness criterion implies all faces point outward for each closed component`) with an independent per-face outwardness oracle increment in `src/halfedge_mesh/tests.rs`:
  - added convex-component outwardness oracle helpers:
    - `component_faces_and_vertices_from_start_half_edge`;
    - `sum_mesh_vertex_positions`;
    - `scale_point3_by_usize`;
    - `assert_signed_volume_component_sign_matches_per_face_normal_alignment`.
  - oracle strategy (exact arithmetic only):
    - for each connected component, compute signed-volume sign with existing component traversal;
    - compute each face normal via `compute_face_plane`;
    - compare face-normal alignment against a scaled centroid-direction vector
      (`|V_component| * face_vertex_sum - |V_face| * component_vertex_sum`) so no division is needed;
    - assert per-face alignment sign matches the component signed-volume sign, and assert component sign is reference-origin invariant over a supplied reference set.
  - added deterministic and seeded-randomized regressions:
    - `outward_signed_volume_sign_matches_per_face_normal_alignment_for_convex_components`;
    - `differential_randomized_outward_signed_volume_per_face_alignment_harness` (40 cases, including rigid transforms, reflections, and consistent vertex-index relabelings).
  - outcome: stronger executable evidence that the current global signed-volume outwardness criterion tracks per-face outward orientation on convex closed components under orientation-preserving and orientation-flipping transforms, while the formal P5.4 theorem remains open.
- 2026-02-19: Failed attempts in this P5.4 per-face outwardness-oracle pass: none.
- 2026-02-19: Revalidated after the P5.4 per-face outwardness-oracle increment:
  - `cargo test -p vcad-topology --features geometry-checks outward_signed_volume_sign_matches_per_face_normal_alignment_for_convex_components`
  - `cargo test -p vcad-topology --features geometry-checks differential_randomized_outward_signed_volume_per_face_alignment_harness`
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (60 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (73 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Worked P5.1 (`Proof: runtime checker correctness vs spec`) with a reflection-and-relabeling differential-oracle increment in `src/halfedge_mesh/tests.rs`:
  - strengthened deterministic coplanarity/oracle parity coverage in
    `face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle` by adding:
    - consistent vertex-index-relabeled variants for each existing fixture family;
    - reflected variants for each fixture family;
    - reflected+relabelled variants for each fixture family.
  - extended
    `differential_randomized_face_coplanarity_checker_exhaustive_quadruple_oracle_harness`
    so each seeded case now validates coplanarity checker/oracle parity not only on base,
    rigid, and perturbed fixtures, but also on:
    - relabeled disjoint/rigid/perturbed variants;
    - reflected disjoint/perturbed variants;
    - reflected+relabelled disjoint/perturbed variants;
    - relabeled transformed failing fixtures and reflected(+relabelled) transformed failing fixtures.
  - outcome: tighter executable lock that `check_face_coplanarity()` remains equivalent to the
    exhaustive face-quadruple oracle under orientation-flipping transforms and topology-preserving
    index isomorphisms, while the formal P5.1 checker/spec theorem remains open.
- 2026-02-19: Failed attempts in this P5.1 reflection-and-relabeling coplanarity harness pass: none.
- 2026-02-19: Revalidated after the P5.1 reflection-and-relabeling coplanarity harness increment:
  - `cargo test -p vcad-topology --features geometry-checks face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle`
  - `cargo test -p vcad-topology --features geometry-checks differential_randomized_face_coplanarity_checker_exhaustive_quadruple_oracle_harness`
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (60 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (73 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Worked P5.4 (`Proof: signed-volume outwardness criterion is independent of the chosen reference origin`) with relabeling-aware outwardness invariance harness increments in `src/halfedge_mesh/tests.rs`:
  - added helper `assert_component_signed_volume_reference_invariance_with_expected_sign` to lock both:
    - reference-origin invariance of per-component signed six-volume; and
    - expected orientation polarity (`-1` for outward fixtures, `+1` for reflected fixtures).
  - strengthened deterministic and seeded-randomized outward invariance tests to include vertex-relabeling variants:
    - `outward_face_normals_checker_is_reference_origin_invariant`;
    - `differential_randomized_outward_checker_reference_origin_invariance_harness`;
    - `outward_signed_volume_is_reference_origin_invariant_per_component`;
    - `differential_randomized_outward_signed_volume_reference_origin_invariance_harness`.
  - extended signed-volume invariance coverage to reflected (orientation-flipped) randomized fixtures, asserting reference-origin invariance under both outward and reflected polarity.
  - outcome: stronger executable lock that outwardness and component signed-volume reference-origin invariance are stable under topology-preserving index relabelings (and reflected polarity flips), while the formal P5.4 proof item remains open.
- 2026-02-19: Failed attempts in this P5.4 relabeling-aware outward invariance pass: none.
- 2026-02-19: Revalidated after the P5.4 relabeling-aware outward invariance harness increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (58 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (71 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Worked P5.3 (`Proof: runtime checker correctness vs convexity spec`) with a reflection-and-relabeling differential-harness increment in `src/halfedge_mesh/tests.rs`:
  - strengthened deterministic convexity/spec parity coverage in
    `face_convexity_checker_matches_projected_orient2d_sign_oracle` by adding reflected variants of:
    - positive fixtures (`tetrahedron`, `cube`, `triangular_prism`, disconnected stress, overlapping tetrahedra);
    - failing fixtures (`concave_face`, `noncoplanar_face`, `collinear_face`, `zero_length_edge`).
  - added a deterministic reverse-index relabeling check in the same test for every fixture (both passing and failing families), asserting Phase 4 validity preservation plus convexity checker parity against the projected `orient2d` oracle.
  - extended
    `differential_randomized_face_convexity_checker_projected_orient2d_oracle_harness`
    so each seeded case now checks projected-oracle parity not only on base and relabeled meshes, but also on reflected and reflected+relabeled variants for:
    - disjoint fixtures;
    - rigid transformed fixtures;
    - adversarial perturbed fixtures;
    - rigidly transformed failing fixtures.
  - outcome: tighter regression lock that the runtime convexity checker remains equivalent to the projected `orient2d` oracle under orientation-flipping transforms and topology-preserving index isomorphisms, while the formal P5.3 proof obligation remains open.
- 2026-02-19: Failed attempts in this P5.3 reflection-and-relabeling convexity harness pass: none.
- 2026-02-19: Revalidated after the P5.3 reflection-and-relabeling convexity harness increment:
  - `cargo test -p vcad-topology --features geometry-checks face_convexity_checker_matches_projected_orient2d_sign_oracle`
  - `cargo test -p vcad-topology --features geometry-checks differential_randomized_face_convexity_checker_projected_orient2d_oracle_harness`
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (58 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (71 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Worked P5.5 (`Proof: shared-edge and shared-vertex contacts are never misclassified as forbidden intersections`) with a relabeling-aware differential-harness increment in `src/halfedge_mesh/tests.rs`:
  - extended
    `differential_randomized_shared_boundary_contact_non_misclassification_harness`
    so each randomized rigid and reflected shared-boundary fixture now also exercises a consistent random vertex-index relabeling;
  - for each relabeled variant (shared-edge and shared-vertex families), added parity checks for:
    - Phase 4 validity preservation;
    - allowed-contact classifier/oracle equivalence via
      `assert_allowed_contact_topology_classifier_matches_edge_index_oracle`;
    - intersection-checker acceptance
      (`check_no_forbidden_face_face_intersections()` remains `true`);
    - shared-boundary non-misclassification via existing pair-level witness assertions.
  - additionally extended
    `face_convexity_checker_matches_projected_orient2d_sign_oracle`
    to include reflected deterministic fixtures (for both passing and failing convexity cases), and
    extended
    `differential_randomized_face_convexity_checker_projected_orient2d_oracle_harness`
    with reflected and consistent random vertex-index-relabeled variants across disjoint, rigidly
    transformed, perturbed, and transformed-failing fixtures.
  - outcome: broader regression lock that:
    - shared-boundary adjacency exemptions remain stable under topology-preserving index
      isomorphisms composed with rigid/reflection transforms (P5.5 evidence); and
    - convexity checker/oracle parity remains stable under the same relabeling class (P5.3
      evidence),
    while the formal P5.5/P5.3 proof obligations remain open.
- 2026-02-19: Failed attempts in this P5.5 relabeling-aware shared-boundary harness pass: none.
- 2026-02-19: Revalidated after the P5.5 relabeling-aware shared-boundary harness increment:
  - `cargo test -p vcad-topology --features geometry-checks differential_randomized_shared_boundary_contact_non_misclassification_harness`
  - `cargo test -p vcad-topology --features geometry-checks differential_randomized_face_convexity_checker_projected_orient2d_oracle_harness`
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (58 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (71 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Worked P5.5 (`Proof: adjacency-exemption implementation is equivalent to the allowed-contact spec`) with an index-relabeling differential-harness increment in `src/halfedge_mesh/tests.rs`:
  - added relabeling-oriented harness helpers:
    - `mesh_vertices_and_face_cycles_for_relabeling`;
    - `relabel_mesh_vertices_for_testing`;
    - `random_permutation`.
  - extended
    `differential_randomized_allowed_contact_topology_classifier_harness`
    so each seeded randomized case now validates classifier/oracle parity not only on:
    - disjoint meshes;
    - rigidly transformed meshes;
    - adversarial perturbed meshes;
    but also on consistent random vertex-index relabelings of each of those three variants.
  - outcome: stronger regression lock that the runtime allowed-contact topology classifier remains equivalent to the independent edge-index oracle under topology-preserving index isomorphisms, narrowing the remaining formal P5.5 adjacency-exemption proof gap.
- 2026-02-19: Failed attempts in this P5.5 index-relabeling differential-harness pass: none.
- 2026-02-19: Revalidated after the P5.5 index-relabeling differential-harness increment:
  - `cargo test -p vcad-topology --features geometry-checks differential_randomized_allowed_contact_topology_classifier_harness`
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (58 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (71 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Worked P5.5 (`Proof: shared-edge and shared-vertex contacts are never misclassified as forbidden intersections`) with a reflection-aware differential harness increment in `src/halfedge_mesh/tests.rs`:
  - expanded deterministic shared-boundary non-misclassification fixtures to include reflected variants:
    - `shared_edge_contacts_are_not_misclassified_as_forbidden_intersections` now includes reflected tetrahedron/cube/triangular-prism meshes;
    - `shared_vertex_only_contacts_are_not_misclassified_as_forbidden_intersections` now includes reflected octahedron variants.
  - strengthened these deterministic paths to also assert adjacency classifier/spec parity via
    `assert_allowed_contact_topology_classifier_matches_edge_index_oracle`.
  - extended `differential_randomized_shared_boundary_contact_non_misclassification_harness` so each randomized rigid case is also reflected, and both the original and reflected meshes are checked for:
    - Phase 4 validity;
    - allowed-contact classifier parity vs the edge-index oracle;
    - `check_no_forbidden_face_face_intersections()` pass;
    - shared-edge/shared-vertex non-misclassification.
  - outcome: tighter regression lock that adjacency-exempt shared-boundary contacts remain non-forbidden under orientation-flipping transforms, with P5.5 formal proof obligations still open.
- 2026-02-19: Failed attempts in this P5.5 reflection-aware harness pass: none.
- 2026-02-19: Revalidated after the P5.5 reflection-aware harness increment:
  - `cargo test -p vcad-topology --features geometry-checks shared_edge_contacts_are_not_misclassified_as_forbidden_intersections`
  - `cargo test -p vcad-topology --features geometry-checks shared_vertex_only_contacts_are_not_misclassified_as_forbidden_intersections`
  - `cargo test -p vcad-topology --features geometry-checks differential_randomized_shared_boundary_contact_non_misclassification_harness`
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (58 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (71 passed, 0 failed)
- 2026-02-19: Worked P5.7 (`Prove aggregate checker equivalence to aggregate Phase 5 spec`) with
  a multiclass model/runtime-gap codification increment in `src/halfedge_mesh/tests.rs`:
  - generalized `assert_phase4_shared_edge_spec_characterization_gap` from a noncoplanar-only
    assertion into a failure-classed gap checker
    (`Phase4SharedEdgeSpecGapFailure::{NonCoplanar, NonConvex, ForbiddenIntersection, InwardOrDegenerate}`),
    while preserving the core boundary claim:
    `(is_valid && shared-edge-local-orientation)` still implies the current aggregate model spec,
    but does not imply runtime aggregate checker success;
  - added reusable fixtures:
    - `build_concave_single_face_pair_mesh`;
    - `build_reflected_cube_outward_failure_mesh`;
  - added deterministic regression locks for three additional geometric failure families beyond
    noncoplanarity:
    - `concave_fixture_keeps_phase4_and_shared_edge_orientation_but_fails_aggregate_gate`;
    - `overlapping_fixture_keeps_phase4_and_shared_edge_orientation_but_fails_aggregate_gate`;
    - `reflected_fixture_keeps_phase4_and_shared_edge_orientation_but_fails_aggregate_gate`;
  - added seeded randomized rigid-transform stress coverage across all four gap families:
    - `differential_randomized_multiclass_phase4_shared_edge_spec_gap_harness` (40 cases).
  - outcome: the remaining P5.7 blocker is now regression-locked across coplanarity, convexity,
    forbidden-intersection, and outward-orientation failure classes (not only a single noncoplanar
    fixture), reducing the risk of re-attempting full equivalence against the still-weaker aggregate
    model characterization.
- 2026-02-19: Failed attempts in this P5.7 multiclass gap-codification pass: none.
- 2026-02-19: Revalidated after the P5.7 multiclass gap-codification increment:
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" noncoplanar_fixture_keeps_phase4_and_shared_edge_orientation_but_fails_aggregate_gate`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" concave_fixture_keeps_phase4_and_shared_edge_orientation_but_fails_aggregate_gate`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" overlapping_fixture_keeps_phase4_and_shared_edge_orientation_but_fails_aggregate_gate`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" reflected_fixture_keeps_phase4_and_shared_edge_orientation_but_fails_aggregate_gate`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" differential_randomized_multiclass_phase4_shared_edge_spec_gap_harness`
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (58 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (71 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Worked P5.7 (`Prove aggregate checker equivalence to aggregate Phase 5 spec`) by
  tightening the existing non-coplanar spec/runtime gap harness in
  `src/halfedge_mesh/tests.rs`:
  - extended `assert_phase4_shared_edge_spec_characterization_gap` to assert the aggregate
    diagnostic first-failure witness stays
    `GeometricTopologicalConsistencyFailure::FaceNonCoplanar { .. }`, pinning the mismatch to the
    expected coplanarity stage instead of later checks;
  - expanded
    `differential_randomized_noncoplanar_phase4_shared_edge_spec_gap_harness`
    with reflected variants (across the YZ plane, then rigid Z-quarter-turn + translation), in
    addition to the existing lifted and rigid cases.
  - outcome: stronger regression lock on the precise P5.7 blocker boundary
    (model-level Phase4+shared-edge characterization stays true while runtime aggregate Phase 5
    gate fails specifically at coplanarity), with the formal equivalence proof item still open.
- 2026-02-19: Failed attempts in this P5.7 harness-tightening pass: none.
- 2026-02-19: Revalidated after the P5.7 harness-tightening increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (58 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (67 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Worked P5.7 (`Prove aggregate checker equivalence to aggregate Phase 5 spec`) by codifying the current model/runtime mismatch boundary in `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs` and `src/halfedge_mesh/tests.rs`:
  - added verified bridge helper
    `runtime_check_phase4_valid_and_shared_edge_local_orientation_imply_geometric_topological_consistency_spec`;
  - helper proves at runtime that `(Phase 4 validity && shared-edge local orientation consistency)` implies the current model-level
    `mesh_geometric_topological_consistency_spec`;
  - extended
    `noncoplanar_fixture_keeps_phase4_and_shared_edge_orientation_but_fails_aggregate_gate`
    to assert the new bridge passes on the noncoplanar fixture while
    `check_geometric_topological_consistency()` and the existing aggregate sound bridge both fail.
  - factored reusable noncoplanar-gap helpers in test space:
    - `build_noncoplanar_single_quad_double_face_mesh_with_lift`;
    - `assert_phase4_shared_edge_spec_characterization_gap`.
  - added `differential_randomized_noncoplanar_phase4_shared_edge_spec_gap_harness` (40 deterministic seeded cases), including rigid rotation+translation variants, to lock this gap signature over a broader fixture set.
  - outcome: locked the exact remaining P5.7 blocker in executable/verified form (current model spec characterization is weaker than the runtime aggregate checker), reducing repeat proof attempts against the wrong equivalence target while the formal P5.7 equivalence obligation remains open.
- 2026-02-19: Failed attempts in this P5.7 boundary-codification pass: none.
- 2026-02-19: Revalidated after the P5.7 boundary-codification increment:
  - `cargo test -p vcad-topology` (13 passed, 0 failed)
  - `cargo test -p vcad-topology --features geometry-checks` (58 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (67 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Worked P5.1 (`Proof: runtime checker correctness vs spec`) with a differential
  stress-oracle increment in `src/halfedge_mesh/tests.rs`:
  - factored the exhaustive coplanarity oracle parity assertion into
    `assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle`;
  - added
    `differential_randomized_face_coplanarity_checker_exhaustive_quadruple_oracle_harness`
    (40 deterministic seeded cases) to compare `check_face_coplanarity()` against the exhaustive
    face-quadruple oracle across:
    - valid disconnected closed-component fixtures;
    - rigid rotation + translation transforms;
    - adversarial component-coordinate perturbations (exact overlap and vertex/edge-touch modes);
    - rigidly transformed negative fixtures (non-coplanar face, collinear seed corner, zero-length
      geometric edge).
  - outcome: stronger executable evidence that the optimized coplanarity checker matches the full
    face-quadruple oracle under documented runtime preconditions (Phase 4 validity + seed-0 corner
    non-collinearity), while the remaining formal P5.1 proof obligation stays open.
- 2026-02-19: Failed attempt in this P5.1 pass:
  - tried to close the missing formal reverse direction
    (`seed0-fixed witness + seed0 non-collinear -> mesh_runtime_all_faces_coplanar_spec`) in
    `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`;
  - blocker: no existing upstream lemma in the current proof stack to discharge the generic
    “all face vertices satisfy one non-degenerate seed plane implies arbitrary face-vertex
    quadruple coplanarity” step without introducing new trusted assumptions.
- 2026-02-19: Revalidated after the P5.1 coplanarity-oracle stress-harness increment:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks` (58 passed, 0 failed)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` (66 passed, 0 failed)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Completed a P5.4 outward signed-volume traversal dedup + checker/diagnostic parity cleanup in
  `src/halfedge_mesh/validation.rs`:
  - added shared helper `first_component_with_non_negative_signed_volume_relative_to_reference()`
    and routed both paths through it:
    - `check_outward_face_normals_relative_to_reference_impl`;
    - `first_inward_or_degenerate_component_failure`.
  - replaced per-component `HashSet` face dedup with a dense face-tag array (`Vec<usize>` +
    component epoch), removing repeated hash allocations while preserving exact component-volume
    semantics.
  - removed redundant `face_signed_volume_six_relative_to_origin()` after moving all origin
    call-sites onto the shared reference-parameterized traversal.
  - outcome: the outward-orientation boolean checker and diagnostic first-failure witness now share
    one signed-volume component traversal implementation, reducing drift risk while the remaining
    unchecked P5.4 proof obligations stay open.
- 2026-02-19: Failed attempts in this P5.4 outward traversal dedup pass: none.
- 2026-02-19: Revalidated after the P5.4 outward traversal dedup cleanup:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Completed a P5.11 scalability constant-factor cleanup in
  `src/halfedge_mesh/validation.rs`:
  - removed redundant `check_no_zero_length_geometric_edges()` and
    `check_face_coplanarity()` pre-gates from intersection-checker paths already gated by
    `check_face_convexity()`:
    - `check_no_forbidden_face_face_intersections_impl`;
    - `face_pair_has_forbidden_intersection_for_testing`.
  - rationale: `check_face_convexity()` already requires `is_valid()` and internally enforces
    coplanarity/non-collinearity prerequisites, so these extra top-level pre-gates were duplicate
    full-mesh traversals with no behavioral effect.
- 2026-02-19: Failed attempts in this P5.11 intersection-precheck dedup pass: none.
- 2026-02-19: Revalidated after the P5.11 intersection-precheck dedup cleanup:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Completed a P5.11 scalability constant-factor cleanup in
  `src/halfedge_mesh/validation.rs`:
  - removed redundant `check_index_bounds()` / `check_face_cycles()` pre-gates from
    geometry-checker paths already gated by `is_valid()`:
    - `check_face_corner_non_collinearity`;
    - `check_no_zero_length_geometric_edges`;
    - `check_face_coplanarity`;
    - `check_face_convexity`;
    - `compute_face_plane`;
    - `check_face_plane_consistency`;
    - `check_outward_face_normals_relative_to_reference_impl`;
    - `check_shared_edge_local_orientation_consistency`;
    - `check_no_forbidden_face_face_intersections_impl`;
    - `face_pair_has_forbidden_intersection_for_testing`;
    - `check_geometric_topological_consistency_diagnostic`.
  - rationale: phase-4 validity already enforces index bounds and face-cycle integrity, so these
    extra checks were duplicate whole-mesh passes with no behavioral effect.
- 2026-02-19: Failed attempts in this P5.11 validity-precheck dedup pass: none.
- 2026-02-19: Revalidated after the P5.11 validity-precheck dedup cleanup:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Completed a P5.11 scalability constant-factor cleanup in
  `src/halfedge_mesh/validation.rs`:
  - removed redundant `check_face_corner_non_collinearity()` pre-gates from Phase 5 checkers
    that already require `check_face_coplanarity()`:
    - `check_face_convexity`;
    - `check_face_plane_consistency`;
    - `check_outward_face_normals_relative_to_reference_impl`;
    - `check_no_forbidden_face_face_intersections_impl`;
    - `face_pair_has_forbidden_intersection_for_testing`.
  - rationale: `check_face_coplanarity()` already rejects seed-0 collinear faces, so these extra
    pre-gates were duplicate full-face passes with no behavioral effect; this keeps checker outputs
    unchanged while reducing repeated O(H) traversals in coplanarity-dependent paths.
- 2026-02-19: Failed attempts in this P5.11 constant-factor cleanup pass: none.
- 2026-02-19: Revalidated after the P5.11 constant-factor cleanup:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
- 2026-02-19: Completed a P5.1 runtime-checker-correctness completeness-precondition tightening
  increment across
  `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs` and
  `src/halfedge_mesh/tests.rs`:
  - added a new completeness entrypoint that consumes the existing Phase-5 runtime bundle directly
    (without re-requiring full coplanarity):
    - `runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_phase5_runtime_bundle_preconditions`;
    - this wrapper now derives index/cycle/runtime-geometry prerequisites from
      `mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec`.
  - retained compatibility for the existing helper
    `runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_phase5_runtime_bundle_and_full_coplanarity_preconditions`,
    but normalized its implementation to delegate through the new bundle-only completeness wrapper.
  - added a runtime-facing bridge wrapper to make the bundle-only completeness path executable from
    parity tests:
    - `runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_phase5_runtime_bundle_sound_bridge`.
  - extended `geometry-checks + verus-proofs` parity coverage:
    - new helper
      `assert_face_coplanarity_seed0_phase5_runtime_bundle_completeness_bridge_parity`;
    - wired into `assert_constructive_phase5_gate_parity`;
    - added focused regression
      `face_coplanarity_seed0_phase5_runtime_bundle_completeness_bridge_matches_geometric_sound_bridge`.
  - outcome: the P5.1 completeness direction now has a stricter precondition-lift path from the
    already-proved Phase-5 runtime bundle, reducing redundant coplanarity assumptions at call sites
    while keeping runtime/constructive parity locked.
- 2026-02-19: Failed attempts in this P5.1 completeness-precondition tightening pass: none.
- 2026-02-19: Revalidated after the P5.1 completeness-precondition tightening additions:
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" face_coplanarity_seed0_phase5_runtime_bundle_completeness_bridge_matches_geometric_sound_bridge`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" geometric_consistency_constructive_gate_matches_runtime_boolean_gate`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" differential_randomized_constructive_geometric_gate_parity_harness`
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Completed a P5.1 runtime-checker-correctness sound-bridge API increment across
  `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs` and
  `src/halfedge_mesh/tests.rs`:
  - added a dedicated runtime coplanarity sound bridge:
    - `runtime_check_face_coplanarity_seed0_fixed_witness_sound_bridge`;
    - bridge shape now explicitly routes through `Mesh::check_face_coplanarity()` first, then
      requires the verified seed-0 witness bridge to succeed before returning `true`;
    - proof postconditions export the full currently-proved seed-0 coplanarity bundle:
      - `mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec`;
      - `mesh_runtime_all_faces_seed0_corner_non_collinear_spec`;
      - `mesh_runtime_all_faces_seed0_plane_contains_vertices_spec`;
      - `mesh_runtime_all_faces_oriented_seed0_planes_spec`.
  - expanded `geometry-checks + verus-proofs` parity coverage for the new API:
    - added helper `assert_face_coplanarity_runtime_seed0_sound_bridge_parity`;
    - wired that helper into `assert_constructive_phase5_gate_parity`;
    - added focused regression
      `face_coplanarity_seed0_sound_bridge_matches_runtime_checker`;
    - strengthened
      `noncoplanar_fixture_keeps_phase4_and_shared_edge_orientation_but_fails_aggregate_gate`
      to assert the new sound bridge returns `false` on the noncoplanar counterexample.
  - outcome: P5.1 now has an explicit runtime-facing coplanarity sound-bridge entrypoint (mirroring
    the existing aggregate-gate sound bridge pattern) with deterministic and randomized parity locks
    against runtime checker behavior while the full checker/spec equivalence theorem remains open.
- 2026-02-19: Failed attempts in this P5.1 sound-bridge API pass: none.
- 2026-02-19: Revalidated after the P5.1 sound-bridge API additions:
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" face_coplanarity_seed0_sound_bridge_matches_runtime_checker`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" face_coplanarity_seed0_bridge_matches_runtime_checker`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" geometric_consistency_constructive_gate_matches_runtime_boolean_gate`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" differential_randomized_constructive_geometric_gate_parity_harness`
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Completed a P5.7 aggregate-checker-equivalence witness-bit parity increment in
  `src/halfedge_mesh/tests.rs`:
  - strengthened `assert_constructive_phase5_gate_parity` so
    `check_geometric_topological_consistency_constructive(..)` witness fields are now asserted
    equal to their corresponding runtime checkers (not only aggregate parity + one-way implications):
    - `no_zero_length_geometric_edges_ok` ↔ `check_no_zero_length_geometric_edges()`;
    - `face_corner_non_collinearity_ok` ↔ `check_face_corner_non_collinearity()`;
    - `face_coplanarity_ok` ↔ `check_face_coplanarity()`;
    - `face_convexity_ok` ↔ `check_face_convexity()`;
    - `face_plane_consistency_ok` ↔ `check_face_plane_consistency()`;
    - `shared_edge_local_orientation_ok` ↔ `check_shared_edge_local_orientation_consistency()`;
    - `no_forbidden_face_face_intersections_ok` ↔
      `check_no_forbidden_face_face_intersections()`;
    - `outward_face_normals_ok` ↔ `check_outward_face_normals()`.
  - because this helper is reused by both deterministic and seeded-randomized constructive/runtime
    parity tests, the stronger per-bit parity assertions now lock broader aggregate-gate behavior
    against drift while the formal P5.7 aggregate checker/spec equivalence theorem remains open.
- 2026-02-19: Failed attempts in this P5.7 witness-bit parity pass: none.
- 2026-02-19: Revalidated after the P5.7 witness-bit parity additions:
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" geometric_consistency_constructive_gate_matches_runtime_boolean_gate`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" differential_randomized_constructive_geometric_gate_parity_harness`
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Completed a P5.1 runtime-checker-correctness completeness-precondition-lift increment in
  `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`:
  - added two new proof-side wrappers that reuse the existing full-coplanarity completeness bridge
    while reducing caller-side precondition plumbing:
    - `runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_full_coplanarity_preconditions`;
    - `runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_phase5_runtime_bundle_and_full_coplanarity_preconditions`.
  - the first wrapper lifts from `mesh_valid_spec(m@)` (plus full runtime coplanarity +
    seed-0 non-collinearity) by deriving:
    - `mesh_runtime_geometry_bridge_spec(m)` via `lemma_mesh_runtime_geometry_bridge_holds`;
    - `mesh_index_bounds_spec(m@)` and `mesh_face_next_cycles_spec(m@)` from
      `mesh_structurally_valid_spec(m@)`.
  - the second wrapper composes directly from
    `mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m)` plus full
    runtime coplanarity, so aggregate-gate-side proofs can route into the same completeness path
    without re-expanding lower-level validity obligations.
  - outcome: P5.1 completeness-direction entrypoints now compose more directly with both Phase-4
    validity and existing Phase-5 runtime bundle artifacts, reducing proof call-site friction for
    remaining checker/spec equivalence work.
- 2026-02-19: Failed attempts in this P5.1 completeness-precondition-lift pass: none.
- 2026-02-19: Revalidated after the P5.1 completeness-precondition-lift additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
- 2026-02-19: Completed a P5.1 runtime-checker-correctness completeness-lift increment in
  `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`:
  - added a new proof-side helper:
    - `runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_full_coplanarity_preconditions`;
  - the helper lifts full runtime coplanarity preconditions directly into the existing seed-0
    completeness bridge by proving:
    - `mesh_runtime_all_faces_coplanar_spec(m) ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m)`
      via `lemma_mesh_runtime_all_faces_coplanar_spec_implies_all_faces_seed0_fixed_witness`;
  - after that normalization step, it reuses
    `runtime_check_face_coplanarity_seed0_fixed_witness_complete_under_preconditions` unchanged.
  - outcome: P5.1 completeness-direction plumbing now has an explicit entrypoint from the
    roadmap-level full coplanarity runtime spec (plus documented non-collinearity/index/cycle
    preconditions), reducing proof friction toward full checker/spec equivalence.
- 2026-02-19: Failed attempts in this P5.1 completeness-lift pass: none.
- 2026-02-19: Revalidated after the P5.1 completeness-lift additions:
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Completed a P5.1 runtime-checker-correctness completeness-direction increment in
  `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`:
  - added a new proof-side runtime helper:
    - `runtime_check_face_coplanarity_seed0_fixed_witness_complete_under_preconditions`;
  - the helper executes the same face-loop coplanarity core and proves it cannot fail when the
    documented preconditions are already established:
    - index bounds + face-cycle witnesses;
    - runtime geometry bridge;
    - all-face seed-0 fixed coplanarity witnesses;
    - all-face seed-0 corner non-collinearity;
  - postconditions additionally export the expected seed-0 coplanarity bundle artifacts:
    - `mesh_runtime_all_faces_seed0_plane_contains_vertices_spec`;
    - `mesh_runtime_all_faces_oriented_seed0_planes_spec`.
  - outcome: P5.1 now has an explicit formal completeness-direction bridge for the runtime-style
    coplanarity loop under documented preconditions, reducing remaining proof gap plumbing for full
    checker/spec equivalence.
- 2026-02-19: Failed attempt in this P5.1 completeness-direction pass:
  - attempted to close the full checklist item directly, but this pass did not prove a direct
    end-to-end theorem tying `Mesh::check_face_coplanarity()` itself to
    `mesh_all_faces_coplanar_spec`; the new result is a preconditioned completeness bridge for the
    verified runtime-style seed-0 checker core.
- 2026-02-19: Revalidated after the P5.1 completeness-direction additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Completed a P5.3 runtime-checker-correctness randomized-oracle increment in
  `src/halfedge_mesh/tests.rs`:
  - added a reusable convexity-oracle parity helper:
    - `assert_face_convexity_checker_matches_projected_orient2d_oracle`;
  - refactored `face_convexity_checker_matches_projected_orient2d_sign_oracle` to use
    fixture-labeled helper assertions for clearer counterexample reporting;
  - added a seeded randomized differential harness:
    - `differential_randomized_face_convexity_checker_projected_orient2d_oracle_harness`
      (40 cases);
    - per-case coverage now includes:
      - randomized disconnected valid tetrahedra fixtures;
      - randomized rigid quarter-turn `z` rotations plus integer translations;
      - adversarial disconnected-component coordinate perturbations (exact overlap and
        boundary-touch placements);
      - rigidly transformed failing fixtures (concave face, noncoplanar face, collinear face,
        zero-length edge).
  - outcome: P5.3 convexity runtime behavior is now additionally regression-locked against an
    independent projected-`orient2d` oracle under broader deterministic-randomized variation,
    reducing drift risk while the formal soundness/completeness theorem remains open.
- 2026-02-19: Failed attempts in this P5.3 randomized-oracle pass: none.
- 2026-02-19: Revalidated after the P5.3 randomized-oracle additions:
  - `cargo test -p vcad-topology --features geometry-checks face_convexity_checker_matches_projected_orient2d_sign_oracle`
  - `cargo test -p vcad-topology --features geometry-checks differential_randomized_face_convexity_checker_projected_orient2d_oracle_harness`
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Completed a P5.1 runtime-checker-correctness bridge-parity increment in
  `src/halfedge_mesh/tests.rs`:
  - imported `runtime_check_face_coplanarity_seed0_fixed_witness_bridge` into the
    `geometry-checks + verus-proofs` test harness;
  - added a reusable parity helper:
    - `assert_face_coplanarity_runtime_seed0_bridge_parity`;
  - strengthened the constructive/runtime aggregate parity helper:
    - `assert_constructive_phase5_gate_parity` now always asserts
      `Mesh::check_face_coplanarity()` parity with
      `runtime_check_face_coplanarity_seed0_fixed_witness_bridge(..)`;
  - added a focused deterministic regression:
    - `face_coplanarity_seed0_bridge_matches_runtime_checker`
      (tetrahedron/cube/prism, overlapping disconnected tetrahedra, noncoplanar face,
      collinear face, zero-length-edge face).
  - outcome: coplanarity runtime behavior is now additionally regression-locked against the
    verified seed-0 bridge on representative fixtures and across the existing randomized
    constructive parity harness cases.
- 2026-02-19: Failed attempts in this P5.1 bridge-parity pass: none.
- 2026-02-19: Revalidated after the P5.1 bridge-parity additions:
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" face_coplanarity_seed0_bridge_matches_runtime_checker`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" geometric_consistency_constructive_gate_matches_runtime_boolean_gate`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" differential_randomized_constructive_geometric_gate_parity_harness`
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Completed a P5.7 aggregate-checker-equivalence proof-decomposition + strictness-gap
  regression increment across
  `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs` and
  `src/halfedge_mesh/tests.rs`:
  - strengthened `runtime_check_geometric_topological_consistency_sound_bridge` postconditions to
    expose the currently-proved aggregate consequences directly:
    - `out ==> mesh_valid_spec(m@)`;
    - `out ==> mesh_shared_edge_local_orientation_consistency_spec(m@)`;
    - retained existing ensures for runtime seed-0 coplanarity bundle + aggregate spec witness.
  - added a focused `geometry-checks + verus-proofs` regression that locks a concrete noncoplanar
    fixture where:
    - `is_valid()` and `check_shared_edge_local_orientation_consistency()` both pass;
    - `check_face_coplanarity()` and aggregate `check_geometric_topological_consistency()` fail:
      - `noncoplanar_fixture_keeps_phase4_and_shared_edge_orientation_but_fails_aggregate_gate`.
  - outcome: P5.7 soundness output now exports explicit phase-4/shared-edge facts at the bridge API
    boundary, and the current runtime-vs-aggregate-spec strictness gap is regression-locked to
    prevent accidental drift while full equivalence remains open.
- 2026-02-19: Failed attempt in this P5.7 proof-decomposition/equivalence pass:
  - attempted to close the full aggregate checker equivalence checklist item directly, but the
    current aggregate spec characterization still only guarantees
    `(mesh_valid_spec && mesh_shared_edge_local_orientation_consistency_spec)` and does not yet
    encode the full geometric checker family (coplanarity/convexity/intersection/outwardness);
    this pass therefore landed explicit decomposition + gap-lock regression instead of a final
    equivalence theorem.
- 2026-02-19: Revalidated after the P5.7 proof-decomposition + strictness-gap additions:
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" noncoplanar_fixture_keeps_phase4_and_shared_edge_orientation_but_fails_aggregate_gate`
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Completed a P5.7 aggregate-checker soundness/parity increment across
  `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs` and
  `src/halfedge_mesh/tests.rs`:
  - added a constructive soundness bridge wrapper:
    - `runtime_check_geometric_topological_consistency_sound_bridge`;
    - proven postconditions now expose `out ==> mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m)` and `out ==> mesh_geometric_topological_consistency_spec(m@)`.
  - strengthened the shared constructive/runtime parity helper:
    - `assert_constructive_phase5_gate_parity` now additionally checks
      `runtime_check_geometric_topological_consistency_sound_bridge(mesh)` parity with
      `mesh.check_geometric_topological_consistency()`.
  - added a seeded differential randomized parity harness:
    - `differential_randomized_constructive_geometric_gate_parity_harness` (40 cases);
    - per case coverage now includes:
      - disjoint multi-component closed meshes;
      - randomized rigid quarter-turn `z` rotations plus integer translations;
      - adversarial component perturbations (exact overlap and boundary-touch placements).
  - outcome: aggregate Phase-5 gate behavior is now additionally locked by a verified
    soundness bridge entrypoint plus broader randomized constructive/runtime parity regression
    coverage; the formal unchecked P5.7 full equivalence theorem remains open.
- 2026-02-19: Failed attempts in this P5.7 aggregate-checker soundness/parity pass: none.
- 2026-02-19: Revalidated after the P5.7 aggregate-checker soundness/parity additions:
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" differential_randomized_constructive_geometric_gate_parity_harness`
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Completed a P5.1 seed-0 witness cycle-length normalization increment across
  `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs` and
  `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`:
  - added model-level normalization lemmas that convert existential seed-0 fixed coplanarity
    witnesses into concrete face-cycle-length witnesses:
    - `lemma_mesh_face_coplanar_seed0_fixed_witness_and_face_cycle_witness_imply_fixed_witness_at_cycle_len`;
    - `lemma_mesh_all_faces_coplanar_seed0_fixed_witness_and_face_next_cycles_witness_imply_all_faces_seed0_fixed_witness_at_cycle_lens`;
  - added the runtime-alias companion normalization lemma:
    - `lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_and_face_next_cycles_witness_imply_all_faces_seed0_fixed_witness_at_cycle_lens`;
  - strengthened `runtime_check_face_coplanarity_seed0_fixed_witness_bridge` postconditions to
    export an explicit face-cycle witness sequence whose per-face cycle lengths carry concrete
    seed-0 fixed coplanarity witnesses.
  - outcome: successful runtime seed-0 bridge runs now expose concrete per-face cycle-length
    coplanarity witnesses directly (not only existential per-face seed-0 witnesses), reducing
    completeness-side proof plumbing for the remaining unchecked P5.1 checker-correctness item.
- 2026-02-19: Failed attempts in this P5.1 seed-0 cycle-length normalization pass: none.
- 2026-02-19: Revalidated after the P5.1 seed-0 cycle-length normalization additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (286 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (323 verified, 0 errors)
- 2026-02-19: Completed a P5.3 runtime-checker-correctness proof-plumbing increment in
  `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added a fixed-seed legal-projection bridge lemma for projected-turn convexity witnesses:
    - `lemma_mesh_face_projected_turn_sign_witness_and_coplanar_fixed_seed_witness_use_legal_projection_inputs`;
  - refactored the existing full-coplanarity legal-projection lemma to normalize through the new
    fixed-seed bridge path:
    - `lemma_mesh_face_projected_turn_sign_witness_uses_legal_projection_inputs` now derives
      `mesh_face_coplanar_fixed_seed_witness_spec(..)` via
      `lemma_mesh_face_coplanar_witness_implies_fixed_seed_witness` and delegates;
  - outcome: convexity proof obligations that consume runtime-style fixed-seed coplanarity
    witnesses can now discharge legal-projection side conditions directly, reducing friction toward
    the remaining P5.3 checker soundness/completeness proof.
- 2026-02-19: Failed attempts in this P5.3 fixed-seed legal-projection pass: none.
- 2026-02-19: Revalidated after the P5.3 fixed-seed legal-projection additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (283 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (320 verified, 0 errors)
- 2026-02-19: Completed a P5.5 shared-boundary non-misclassification randomized-harness
  increment in `src/halfedge_mesh/tests.rs`:
  - added a seeded randomized regression harness that stress-checks allowed shared-boundary
    contacts under rigid transforms:
    - `differential_randomized_shared_boundary_contact_non_misclassification_harness`.
  - harness coverage now repeatedly validates both contact classes against the pair-level
    forbidden-intersection hook (with broad-phase/no-cull parity locked by existing helpers):
    - shared-edge adjacent face pairs on `tetrahedron`, `cube`, and `triangular_prism`;
    - shared-vertex-only adjacent face pairs on `octahedron`;
    - randomized per-case quarter-turn `z` rotations + integer translations.
  - outcome: P5.5 `shared-edge/shared-vertex non-misclassification` behavior is now additionally
    regression-locked under deterministic randomized rigid-transform variation, reducing drift risk
    while the formal proof checkbox remains open.
- 2026-02-19: Failed attempts in this P5.5 randomized non-misclassification pass: none.
- 2026-02-19: Revalidated after the P5.5 randomized non-misclassification harness additions:
  - `cargo test -p vcad-topology --features geometry-checks differential_randomized_shared_boundary_contact_non_misclassification_harness`
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (282 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (319 verified, 0 errors)
- 2026-02-19: Completed a P5.1 runtime-checker-correctness proof-plumbing increment in
  `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added a face-cycle witness length uniqueness lemma:
    - `lemma_mesh_face_cycle_witness_length_unique`;
  - added model-level normalization lemmas that pin existential face-coplanarity witnesses to a
    concrete face-cycle length witness:
    - `lemma_mesh_face_coplanar_spec_and_face_cycle_witness_imply_coplanar_witness_at_cycle_len`;
    - `lemma_mesh_face_coplanar_spec_and_face_cycle_witness_imply_seed0_fixed_witness_at_cycle_len`;
  - added a runtime-alias aggregate lemma to lift full runtime coplanarity + face-cycle witnesses
    into per-face seed-0 fixed witnesses at those exact cycle lengths:
    - `lemma_mesh_runtime_all_faces_coplanar_spec_and_face_next_cycles_witness_imply_all_faces_seed0_fixed_witness_at_cycle_lens`.
  - outcome: P5.1 completeness-side obligations can now rewrite existential coplanarity witnesses
    into the concrete cycle lengths used by runtime loops, reducing the remaining gap to a full
    runtime checker soundness/completeness theorem.
- 2026-02-19: Failed attempt in this P5.1 witness-normalization pass:
  - initial `lemma_mesh_face_cycle_witness_length_unique` draft failed due insufficiently explicit
    face-index bounds and quantifier instantiation for the no-repeat cycle clause; resolved by
    adding an explicit face-index precondition and explicit `i=0`/`j=k` instantiations in each
    contradiction branch.
- 2026-02-19: Revalidated after the P5.1 witness-normalization additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (282 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (319 verified, 0 errors)
- 2026-02-19: Completed a P5.5 shared-boundary non-misclassification differential-oracle
  increment across `src/halfedge_mesh/validation.rs` and `src/halfedge_mesh/tests.rs`:
  - added a test-only pair-level runtime hook that exposes the forbidden-intersection decision
    for a specific face pair without changing production behavior:
    - `Mesh::face_pair_has_forbidden_intersection_for_testing(face_a, face_b, use_broad_phase)`.
  - added reusable edge-index-oracle helpers and pair assertions that lock checker behavior on
    allowed shared-boundary contacts:
    - `face_pair_shared_boundary_counts_edge_index_oracle`;
    - `assert_shared_edge_contacts_not_misclassified_as_forbidden_intersections`;
    - `assert_shared_vertex_only_contacts_not_misclassified_as_forbidden_intersections`.
  - added deterministic regressions that assert allowed contacts are not misclassified:
    - `shared_edge_contacts_are_not_misclassified_as_forbidden_intersections` (tetrahedron/cube/prism);
    - `shared_vertex_only_contacts_are_not_misclassified_as_forbidden_intersections`
      (octahedron + rigid transform).
  - outcome: P5.5 shared-edge/shared-vertex non-misclassification behavior is now regression-locked
    at face-pair granularity (including broad-phase/no-cull parity per checked pair), reducing
    drift risk while the formal proof item remains open.
- 2026-02-19: Failed attempts in this P5.5 shared-boundary non-misclassification pass: none.
- 2026-02-19: Revalidated after the P5.5 shared-boundary non-misclassification additions:
  - `cargo test -p vcad-topology --features geometry-checks shared_edge_contacts_are_not_misclassified_as_forbidden_intersections`
  - `cargo test -p vcad-topology --features geometry-checks shared_vertex_only_contacts_are_not_misclassified_as_forbidden_intersections`
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (278 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (315 verified, 0 errors)
- 2026-02-19: Completed a P5.4 signed-volume-origin-independence checker-parity increment across
  `src/halfedge_mesh/validation.rs` and `src/halfedge_mesh/tests.rs`:
  - refactored outward-normal signed-volume accumulation to a shared reference-parameterized path:
    - `Mesh::face_signed_volume_six_relative_to_reference`;
    - `Mesh::check_outward_face_normals_relative_to_reference_impl`.
  - kept production behavior unchanged (`check_outward_face_normals` still uses origin `(0,0,0)`)
    while exposing a test-only reference-shifted checker hook:
    - `Mesh::check_outward_face_normals_relative_to_reference_for_testing`.
  - added reusable checker-invariance assertions and new deterministic + randomized differential
    regressions:
    - `assert_outward_face_normals_checker_reference_invariance`;
    - `outward_face_normals_checker_is_reference_origin_invariant`;
    - `differential_randomized_outward_checker_reference_origin_invariance_harness`.
  - outcome: outward-face-normal checker results are now regression-locked as reference-origin
    invariant across both passing meshes and orientation-flipped failing meshes, reducing drift
    risk while the formal P5.4 origin-independence proof remains open.
- 2026-02-19: Failed attempts in this P5.4 checker-parity/origin-invariance pass: none.
- 2026-02-19: Revalidated after the P5.4 checker-parity/origin-invariance additions:
  - `cargo test -p vcad-topology --features geometry-checks outward_face_normals_checker_is_reference_origin_invariant`
  - `cargo test -p vcad-topology --features geometry-checks outward_checker_reference_origin_invariance`
  - `cargo test -p vcad-topology --features geometry-checks outward_signed_volume_reference_origin_invariance`
  - `cargo test -p vcad-topology --features geometry-checks outward_signed_volume_is_reference_origin_invariant_per_component`
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (278 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (315 verified, 0 errors)
- 2026-02-19: Completed a P5.4 signed-volume-origin-independence differential-harness increment in
  `src/halfedge_mesh/tests.rs`:
  - added a reusable per-component assertion helper for reference-point invariance checks:
    - `assert_component_signed_volume_reference_invariance`;
  - added a deterministic randomized regression harness (40 cases) that checks per-component
    signed-six-volume invariance across multiple reference points on:
    - randomized valid disconnected tetrahedra fixtures;
    - rigidly transformed variants of those fixtures:
      - `differential_randomized_outward_signed_volume_reference_origin_invariance_harness`.
  - outcome: outward signed-volume origin-independence coverage is now broadened from a single
    deterministic fixture to a seeded randomized harness spanning mixed component layouts and rigid
    transforms, reducing regression risk while the formal P5.4 origin-independence theorem remains open.
- 2026-02-19: Failed attempts in this P5.4 signed-volume-origin-independence differential-harness pass: none.
- 2026-02-19: Revalidated after the P5.4 signed-volume-origin-independence differential-harness additions:
  - `cargo test -p vcad-topology --features geometry-checks differential_randomized_outward_signed_volume_reference_origin_invariance_harness`
  - `cargo test -p vcad-topology --features geometry-checks outward_signed_volume_is_reference_origin_invariant_per_component`
  - `cargo test -p vcad-topology --features geometry-checks reflection_flips_outward_orientation_sensitive_phase5_checks`
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (278 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (315 verified, 0 errors)
- 2026-02-19: Completed a P5.5 adjacency-exemption topology-classifier differential-oracle
  increment across `src/halfedge_mesh/validation.rs` and `src/halfedge_mesh/tests.rs`:
  - added a test-only runtime hook that exposes the checker’s per-face-pair allowed-contact
    topology classifier without changing production behavior:
    - `Mesh::face_pair_has_allowed_contact_topology_for_testing`.
  - added an independent face-pair allowed-contact oracle in tests that derives shared-boundary
    classification from face-cycle edge indices + vertex indices (not the checker’s internal
    normalized vertex-pair edge-key helper):
    - `ordered_face_boundary_vertices_and_edge_indices`;
    - `face_pair_allowed_contact_topology_edge_index_oracle`;
    - `assert_allowed_contact_topology_classifier_matches_edge_index_oracle`.
  - added deterministic + randomized differential regressions that assert parity between the
    runtime classifier and the independent oracle across representative valid fixtures and
    randomized disconnected/rigidly transformed/perturbed tetrahedra configurations:
    - `allowed_contact_topology_classifier_matches_edge_index_oracle`;
    - `differential_randomized_allowed_contact_topology_classifier_harness`.
  - outcome: adjacency-exemption topology behavior is now regression-locked against an
    independently computed allowed-contact oracle, reducing drift risk for the remaining open
    P5.5 proofs (`shared-edge/shared-vertex non-misclassification` and
    `adjacency-exemption equivalence`).
- 2026-02-19: Failed attempts in this P5.5 adjacency-exemption differential-oracle pass: none.
- 2026-02-19: Revalidated after the P5.5 adjacency-exemption differential-oracle additions:
  - `cargo test -p vcad-topology --features geometry-checks allowed_contact_topology_classifier_matches_edge_index_oracle`
  - `cargo test -p vcad-topology --features geometry-checks differential_randomized_allowed_contact_topology_classifier_harness`
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (278 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (315 verified, 0 errors)
- 2026-02-19: Completed a P5.3 runtime-checker-correctness differential-oracle increment in
  `src/halfedge_mesh/tests.rs`:
  - added deterministic projected-orientation helpers for convexity oracle comparisons:
    - `face_projection_axis_from_reference_normal`;
    - `project_point3_to_2d_for_face_axis`;
  - added an independent projected-`orient2d` convexity oracle that mirrors the documented
    checker preconditions while avoiding the runtime checker’s `orient3d_sign` implementation:
    - `check_face_convexity_projected_orient2d_oracle`;
  - added a differential regression test asserting parity between
    `Mesh::check_face_convexity()` and the projected-`orient2d` oracle across representative
    passing and failing fixtures (tetrahedron/cube/prism, overlapping disconnected tetrahedra,
    disconnected stress mesh, concave faces, noncoplanar faces, collinear faces, zero-length-edge
    faces):
    - `face_convexity_checker_matches_projected_orient2d_sign_oracle`.
  - outcome: runtime convexity-checker behavior is now regression-locked against an explicit
    projected-`orient2d` oracle across mixed valid/invalid geometric cases, reducing regression
    risk while the formal P5.3 soundness/completeness theorem remains open.
- 2026-02-19: Failed attempt in this P5.3 differential-oracle pass:
  - initial oracle revision called private methods (`check_index_bounds` and `check_face_cycles`)
    and failed to compile (`E0624: method is private`);
  - resolved by aligning with publicly available checker preconditions (`is_valid` +
    face-coplanarity/non-collinearity gates) and removing private method calls from the oracle.
- 2026-02-19: Revalidated after the P5.3 differential-oracle additions:
  - `cargo test -p vcad-topology --features geometry-checks face_convexity_checker_matches_projected_orient2d_sign_oracle`
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (278 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (315 verified, 0 errors)
- 2026-02-19: Completed a P5.7 aggregate-checker-equivalence staging increment in
  `src/halfedge_mesh/tests.rs`:
  - added `geometry-checks + verus-proofs` differential parity coverage between the runtime
    aggregate gates and constructive witness gates:
    - `geometric_consistency_constructive_gate_matches_runtime_boolean_gate`;
  - added a reusable test helper to compare constructive and runtime outcomes for both
    aggregate APIs:
    - `assert_constructive_phase5_gate_parity`;
  - parity assertions now lock:
    - `check_geometric_topological_consistency_constructive(...).api_ok`
      against `Mesh::check_geometric_topological_consistency()`;
    - `is_valid_with_geometry_constructive(...).api_ok`
      against `Mesh::is_valid_with_geometry()`;
    - witness-field consistency for the phase-4 bit and constructive-vs-runtime implications on
      coplanarity/shared-edge witness bits.
  - fixture coverage includes representative passing and failing cases
    (tetrahedron/cube/prism, overlapping disconnected tetrahedra, disconnected stress mesh,
    noncoplanar quad), so runtime/constructive aggregate drift is now regression-locked while the
    formal P5.7 equivalence theorem remains open.
- 2026-02-19: Failed attempts in this P5.7 aggregate-checker-equivalence staging pass: none.
- 2026-02-19: Revalidated after the P5.7 constructive/runtime parity additions:
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs" geometric_consistency_constructive_gate_matches_runtime_boolean_gate`
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (278 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (315 verified, 0 errors)
- 2026-02-19: Completed a P5.1 runtime-checker-correctness differential-oracle increment in
  `src/halfedge_mesh/tests.rs`:
  - added a reusable face-cycle extraction helper for checker-oracle comparisons:
    - `ordered_face_vertex_cycle_indices`;
  - added an exhaustive face-quadruple coplanarity oracle that mirrors the documented
    checker preconditions (`is_valid` + non-collinear face-corner gate):
    - `check_face_coplanarity_exhaustive_face_quadruple_oracle`;
  - added a differential regression that asserts parity between
    `Mesh::check_face_coplanarity()` and the exhaustive oracle across representative
    positive and negative fixtures (tetrahedron/cube/prism, overlapping disconnected tetrahedra,
    disconnected stress mesh, noncoplanar quad faces, collinear faces, zero-length-edge faces):
    - `face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle`.
  - outcome: runtime coplanarity checker behavior is now test-locked against an explicit
    exhaustive face-quadruple oracle across mixed valid/invalid geometric cases, reducing
    regression risk while the formal P5.1 soundness/completeness theorem remains open.
- 2026-02-19: Failed attempts in this P5.1 differential-oracle pass: none.
- 2026-02-19: Revalidated after the P5.1 differential-oracle additions:
  - `cargo test -p vcad-topology --features geometry-checks face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle`
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (278 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (315 verified, 0 errors)
- 2026-02-19: Completed a P5.4 signed-volume-origin-independence runtime-test staging increment in
  `src/halfedge_mesh/tests.rs`:
  - generalized the existing test-side component signed-six-volume helper to accept an explicit
    reference point:
    - `component_signed_volume_six_from_start_half_edge_relative_to_reference`;
  - kept the existing origin-based helper as a wrapper for current witness checks:
    - `component_signed_volume_six_from_start_half_edge`;
  - added a component traversal helper for deterministic per-component checks in invariance tests:
    - `component_start_half_edges`;
  - added a new regression test that locks per-component signed-six-volume invariance under
    reference-point changes:
    - `outward_signed_volume_is_reference_origin_invariant_per_component`.
  - outcome: outward-orientation signed-volume behavior now has explicit test coverage that the
    computed per-component signed six-volume is unchanged across multiple reference-point choices,
    reducing regression risk while the formal P5.4 origin-independence proof remains open.
- 2026-02-19: Failed attempt in this P5.4 signed-volume-origin-independence staging pass:
  - attempted to close the checklist item as a proof, but this pass did not land a Verus theorem;
    current refinement layers still lack a dedicated outward signed-volume model/spec bridge to
    prove origin-independence end-to-end.
- 2026-02-19: Revalidated after the P5.4 signed-volume-origin-independence staging additions:
  - `cargo test -p vcad-topology --features geometry-checks outward_signed_volume_is_reference_origin_invariant_per_component`
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (278 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (315 verified, 0 errors)
- 2026-02-19: Completed a P5.1 face-level oriented-seed0/plane-contains characterization increment in
  `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added a direct face-level iff lemma:
    - `lemma_mesh_face_oriented_seed0_plane_iff_seed0_plane_contains_vertices_and_seed0_non_collinear`;
  - added a runtime face-level seed-0 plane-containment alias spec:
    - `mesh_runtime_face_seed0_plane_contains_vertices_spec`;
  - added the runtime face-level iff companion lemma:
    - `lemma_mesh_runtime_face_oriented_seed0_plane_iff_seed0_plane_contains_vertices_and_seed0_non_collinear`.
  - outcome: face-level oriented seed-0 plane witnesses can now be rewritten directly as
    `(seed0 plane containment + seed0 corner non-collinearity)` without routing through
    seed-0 fixed-witness intermediates, reducing proof-plumbing friction in the remaining
    unchecked P5.1 checker-correctness work.
- 2026-02-19: Failed attempts in this P5.1 face-level oriented/plane characterization pass: none.
- 2026-02-19: Revalidated after the P5.1 face-level oriented/plane characterization additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (278 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (315 verified, 0 errors)
- 2026-02-19: Completed a P5.7/P5.1 aggregate-runtime-spec staging increment across
  `src/runtime_halfedge_mesh_refinement/components_and_validity_specs.rs` and
  `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`:
  - added a runtime-aware aggregate spec for the currently-proved seed-0 coplanarity bridge bundle:
    - `mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec`.
  - added a witness-to-runtime-bundle lemma:
    - `lemma_geometric_topological_consistency_gate_witness_api_ok_implies_mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle`;
    - this lemma lifts `api_ok` plus existing constructive coplanarity bridge implications into a
      single runtime aggregate bundle (`mesh_valid_spec`, shared-edge local orientation consistency,
      seed-0 fixed-witness coplanarity, seed-0 non-collinearity, seed-0 plane containment, and
      oriented seed-0 planes).
  - strengthened `check_geometric_topological_consistency_constructive` postconditions to export:
    - `w.api_ok ==> mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m)`.
  - outcome: the aggregate constructive Phase-5 gate now exposes a single machine-checked
    runtime-side proof bundle at the `api_ok` boundary, reducing proof-plumbing friction for the
    remaining unchecked P5.1 checker-correctness and P5.7 aggregate-equivalence obligations.
- 2026-02-19: Failed attempts in this P5.7/P5.1 aggregate-runtime-spec staging pass: none.
- 2026-02-19: Revalidated after the P5.7/P5.1 aggregate-runtime-spec staging additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (276 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (313 verified, 0 errors)
- 2026-02-19: Completed a P5.1 runtime-checker-alignment increment in
  `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`:
  - refactored the per-face inner loop in
    `runtime_check_face_coplanarity_seed0_fixed_witness_bridge` to start from
    the 4th cycle vertex (`h = next(next(next(h0)))`, `steps = 3`), matching the
    execution order used by `Mesh::check_face_coplanarity()`;
  - added an explicit ghost base-case proof that the seed-0 plane witness holds
    for `d = 0, 1, 2` using orientation-cycle identities plus repeated-point
    coplanarity degeneracy lemmas before entering the runtime loop;
  - retained the existing loop invariant shape (`forall d < steps`) while
    removing the previous `steps == 0` bootstrap branch.
  - outcome: the P5.1 bridge now structurally mirrors the runtime checker path
    more closely and avoids three redundant runtime coplanarity predicate calls
    per face within the constructive bridge loop.
- 2026-02-19: Failed attempts in this P5.1 runtime-checker-alignment pass: none.
- 2026-02-19: Revalidated after the P5.1 runtime-checker-alignment refactor:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (275 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (312 verified, 0 errors)
- 2026-02-19: Completed a P5.1 runtime-checker-correctness staging increment in
  `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added a face-level characterization lemma for oriented seed-0 plane semantics:
    - `lemma_mesh_face_oriented_seed0_plane_iff_seed0_fixed_witness_and_seed0_non_collinear`;
  - added runtime-alias specs to reduce repeated long-form terms in downstream proof obligations:
    - `mesh_runtime_face_seed0_corner_non_collinear_spec`;
    - `mesh_runtime_face_oriented_seed0_plane_spec`;
  - added the runtime-alias face-level characterization lemma:
    - `lemma_mesh_runtime_face_oriented_seed0_plane_iff_seed0_fixed_witness_and_seed0_non_collinear`.
  - outcome: P5.1 reverse-bridge obligations can now swap oriented seed-0 faces and
    `(seed0 fixed witness + seed0 non-collinearity)` at face granularity directly, reducing
    per-face proof expansion overhead in the remaining checker-correctness work.
- 2026-02-19: Failed attempts in this P5.1 face-level oriented-seed0 characterization pass: none.
- 2026-02-19: Revalidated after the P5.1 face-level oriented-seed0 characterization additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (275 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (312 verified, 0 errors)
- 2026-02-19: Completed a P5.11 face-plane preprocessing refactor in
  `src/halfedge_mesh/validation.rs`:
  - added internal helper `Mesh::compute_face_plane_prevalidated(face_id)` for call paths where
    phase-4 validity and index/cycle guards are already established;
  - preserved public API behavior of `Mesh::compute_face_plane(face_id)` (still guard-checked);
  - switched internal per-face plane consumers to the prevalidated helper:
    - `check_face_plane_consistency`;
    - `check_no_forbidden_face_face_intersections_impl`;
    - `first_face_plane_inconsistent_failure`;
    - `first_forbidden_face_face_intersection_failure`.
  - outcome: internal face-plane preprocessing no longer repeats global
    `is_valid`/index/cycle checks once per face, removing the prior hidden `O(FH)` term from
    those internal paths while keeping external semantics unchanged.
- 2026-02-19: Failed attempts in this P5.11 face-plane preprocessing refactor: none.
- 2026-02-19: Revalidated after the P5.11 face-plane preprocessing refactor:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (273 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (310 verified, 0 errors)
- 2026-02-19: Completed a P5.1 runtime-soundness bridge normalization increment in
  `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added a model-level equivalence lemma:
    - `lemma_mesh_all_faces_oriented_seed0_planes_and_index_bounds_and_face_cycles_iff_seed0_plane_contains_vertices_and_seed0_non_collinear`;
  - added a runtime-alias equivalence lemma:
    - `lemma_mesh_runtime_all_faces_oriented_seed0_planes_and_index_bounds_and_face_cycles_iff_seed0_plane_contains_vertices_and_seed0_non_collinear`;
  - outcome: under existing index-bounds + face-cycle preconditions, the oriented seed-0 bundle is
    now directly characterizable as:
    - all-faces seed-0 plane containment; and
    - all-faces seed-0 corner non-collinearity;
    eliminating an extra fixed-witness intermediate in downstream P5.1 proof plumbing.
  - this advances the unchecked P5.1 checker-correctness item by making oriented-seed-plane
    runtime consequences directly interchangeable with the plane-containment/non-collinearity pair
    used by later full-coplanarity reconstruction obligations.
- 2026-02-19: Failed attempts in this P5.1 bridge-normalization pass: none.
- 2026-02-19: Revalidated after the P5.1 bridge-normalization additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (273 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology.sh` (310 verified, 0 errors)
- 2026-02-19: Completed a P5.1 full-coplanarity-to-oriented-seed0 bridge increment in
  `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added a face-level bridge lemma from full coplanarity + seed-0 non-collinearity to oriented
    seed-0 plane semantics:
    - `lemma_mesh_face_coplanar_spec_and_seed0_non_collinear_imply_oriented_seed0_plane`;
  - added an all-faces aggregate bridge lemma:
    - `lemma_mesh_all_faces_coplanar_spec_and_seed0_non_collinear_imply_all_faces_oriented_seed0_planes`;
  - added a runtime-alias aggregate bridge lemma:
    - `lemma_mesh_runtime_all_faces_coplanar_spec_and_seed0_non_collinear_imply_all_faces_oriented_seed0_planes`.
  - outcome: the proof stack now has a direct path from the roadmap-level full coplanarity spec
    (under the explicit seed-0 non-collinearity precondition already enforced by the runtime
    checker) into the oriented seed-0 plane bundle used by constructive/runtime bridges, reducing
    intermediate conversion plumbing in the remaining P5.1 checker-correctness work.
- 2026-02-19: Failed attempts in this P5.1 full-coplanarity-to-oriented-seed0 bridge pass: none.
- 2026-02-19: Revalidated after the P5.1 full-coplanarity-to-oriented-seed0 bridge additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (271 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (308 verified, 0 errors)
- 2026-02-19: Completed a P5.1 runtime-soundness reverse-bridge characterization increment in
  `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added face-level reverse lemmas from oriented seed-0 plane witnesses:
    - `lemma_mesh_face_oriented_seed0_plane_implies_seed0_plane_contains_vertices`;
    - `lemma_mesh_face_oriented_seed0_plane_implies_seed0_non_collinear`;
    - `lemma_mesh_face_oriented_seed0_plane_implies_seed0_fixed_witness`.
  - added all-faces reverse lemmas:
    - `lemma_mesh_all_faces_oriented_seed0_planes_imply_all_faces_seed0_fixed_witness`;
    - `lemma_mesh_all_faces_oriented_seed0_planes_and_index_bounds_and_face_cycles_imply_all_faces_seed0_corner_non_collinear`.
  - added runtime-alias reverse lemmas and a guarded iff characterization:
    - `lemma_mesh_runtime_all_faces_oriented_seed0_planes_imply_all_faces_seed0_fixed_witness`;
    - `lemma_mesh_runtime_all_faces_oriented_seed0_planes_and_index_bounds_and_face_cycles_imply_all_faces_seed0_corner_non_collinear`;
    - `lemma_mesh_runtime_all_faces_oriented_seed0_planes_and_index_bounds_and_face_cycles_iff_seed0_fixed_witness_and_seed0_non_collinear`.
  - outcome: the seed-0 oriented-plane consequence exported by the constructive/runtime coplanarity
    bridge is now machine-checkably reversible (under explicit index-bounds/face-cycle preconditions)
    back into seed-0 fixed coplanarity witness and seed-0 non-collinearity obligations.
  - this advances the unchecked P5.1 checker-correctness item by reducing one-way proof plumbing in
    the runtime seed-0 bundle and making oriented-plane witnesses usable as bidirectional
    intermediate proof artifacts.
- 2026-02-19: Failed attempt in this P5.1 oriented-seed0 reverse-characterization pass:
  - the first revision used a nested existential assertion with manual trigger annotations in
    `lemma_mesh_face_oriented_seed0_plane_implies_seed0_non_collinear`, which failed trigger
    inference (`Could not automatically infer triggers for this quantifier`);
  - fixed by replacing that step with a direct multi-binder `choose|k: int, seed_i: int| ...`
    witness extraction, matching established patterns used elsewhere in the codebase.
- 2026-02-19: Revalidated after the P5.1 oriented-seed0 reverse-characterization additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (268 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology.sh` (305 verified, 0 errors)
- 2026-02-19: Completed an Exit-Criteria trust-surface hardening pass for
  `No trusted assumptions remain for Phase 5 APIs` in `src/halfedge_mesh/tests.rs`:
  - strengthened `topology_sources_contain_no_trusted_verification_boundaries` to additionally
    reject `#[verifier::external]` markers in `vcad-topology/src` (alongside existing checks for
    `assume_specification`, `external_fn_specification`, `admit`,
    `#[verifier::external_body]`, and `verus::trusted`);
  - outcome: accidental introduction of verifier external-body style boundaries is now blocked by a
    direct regression test, and the current source tree remains clean under the tightened check.
- 2026-02-19: Failed attempt in this Exit-Criteria trust-surface hardening pass:
  - initial version also rejected `external_type_specification` tokens and failed on the existing
    six top-level refinement wrappers in `src/runtime_halfedge_mesh_refinement.rs`;
  - rolled that part back after confirming the repository-level trust-surface policy already tracks
    those wrappers explicitly (and constrains them to that single file).
- 2026-02-19: Revalidated after the Exit-Criteria trust-surface hardening changes:
  - `cargo test -p vcad-topology topology_sources_contain_no_trusted_verification_boundaries`
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (260 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (297 verified, 0 errors)
- 2026-02-19: Completed a P5.1/P5.7 constructive coplanarity-bridge integration increment in
  `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`:
  - strengthened `runtime_check_face_coplanarity_seed0_fixed_witness_bridge` to additionally prove:
    - `out ==> mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m)`;
  - in the same bridge tail proof, explicitly derived the new guarantee via:
    - `lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_implies_all_faces_seed0_plane_contains_vertices`;
  - strengthened `check_geometric_topological_consistency_constructive` so the constructive
    `face_coplanarity_ok` witness path now includes the proved seed-0 bridge bundle:
    - evaluates both `m.check_face_coplanarity()` and
      `runtime_check_face_coplanarity_seed0_fixed_witness_bridge(m)`;
    - uses their conjunction for `face_coplanarity_ok`;
    - exports new witness implications:
      - `w.face_coplanarity_ok ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m)`;
      - `w.face_coplanarity_ok ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)`;
      - `w.face_coplanarity_ok ==> mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m)`;
      - `w.face_coplanarity_ok ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m)`.
  - outcome: the aggregate constructive Phase 5 witness now carries a machine-checked coplanarity
    proof bundle at the point where `face_coplanarity_ok` is asserted, reducing later proof plumbing
    for the remaining unchecked P5.1 runtime checker correctness and P5.7 aggregate-equivalence work.
- 2026-02-19: Failed attempts in this P5.1/P5.7 constructive coplanarity-bridge integration pass: none.
- 2026-02-19: Revalidated after the P5.1/P5.7 constructive coplanarity-bridge integration additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (260 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (297 verified, 0 errors)
- 2026-02-19: Completed a P5.1 runtime-soundness/oriented-seed-plane groundwork increment across
  `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs` and
  `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`:
  - added aggregate seed-0 non-collinearity specs:
    - `mesh_all_faces_seed0_corner_non_collinear_spec`;
    - `mesh_runtime_all_faces_seed0_corner_non_collinear_spec`.
  - added aggregate oriented seed-0 plane specs:
    - `mesh_all_faces_oriented_seed0_planes_spec`;
    - `mesh_runtime_all_faces_oriented_seed0_planes_spec`.
  - added aggregate composition lemmas:
    - `lemma_mesh_all_faces_coplanar_seed0_fixed_witness_and_seed0_non_collinear_imply_all_faces_oriented_seed0_planes`;
    - `lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_and_seed0_non_collinear_imply_all_faces_oriented_seed0_planes`.
  - added a dedicated constructive/runtime bridge:
    - `runtime_check_face_seed0_corner_non_collinearity_bridge`, proving
      `out ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)`.
  - strengthened the existing coplanarity constructive/runtime bridge:
    - `runtime_check_face_coplanarity_seed0_fixed_witness_bridge` now additionally proves
      `out ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)` and
      `out ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m)`.
  - outcome: a successful executable coplanarity bridge pass now exports a stronger seed-0 proof bundle
    (fixed-witness coplanarity + seed-0 non-collinearity + oriented seed-0 planes) for all faces, reducing
    future checker/spec proof steps to the remaining conversion from this bundle into full
    `mesh_runtime_all_faces_coplanar_spec`.
  - this advances the unchecked P5.1 checker-correctness item by making the runtime-side seed-0
    non-collinearity precondition explicit and machine-checked, and by wiring oriented-seed-plane
    consequences directly from executable checker success.
- 2026-02-19: Failed attempts in this P5.1 seed-0 non-collinearity/oriented-plane groundwork pass: none.
- 2026-02-19: Revalidated after the P5.1 seed-0 non-collinearity/oriented-plane groundwork additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (260 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (297 verified, 0 errors)
- 2026-02-19: Completed a P5.1 runtime-soundness bridge increment in
  `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`:
  - added a dedicated constructive/runtime bridge:
    - `runtime_check_face_coplanarity_seed0_fixed_witness_bridge`;
  - the new bridge checks face coplanarity with seed-0 triples across each full face cycle and proves:
    - `out ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m)`;
  - proof structure ties executable traversal state to model face-cycle witnesses
    (`mesh_face_next_cycles_witness_spec`) and runtime geometry/model alignment
    (`mesh_runtime_geometry_bridge_spec`) so each checked runtime point maps to the corresponding
    face-cycle spec point;
  - outcome: this closes the previously deferred “dedicated verified runtime bridge from
    `Mesh::check_face_coplanarity()` shape to the seed-0 witness layer” gap and makes the
    seed-0 coplanarity witness path available directly from an executable checker.
  - this advances the unchecked P5.1 checker-correctness item by providing a machine-checked
    runtime-to-seed0-witness soundness bridge; remaining work is still full runtime checker/spec
    equivalence against `mesh_all_faces_coplanar_spec` (soundness + completeness).
- 2026-02-19: Failed attempts in this P5.1 runtime-soundness bridge pass:
  - initial implementation used chained inequalities and a trailing comma inside `assert(...)`
    expressions in `constructive_gates_and_examples.rs`, causing parse errors
    (`expected ','` / `expected ')'`);
  - fixed by rewriting chained comparisons into explicit conjunctions and removing the trailing
    comma from the assertion expression.
- 2026-02-19: Revalidated after the P5.1 runtime-soundness bridge addition:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (258 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology.sh` (295 verified, 0 errors)
- 2026-02-19: Completed a P5.1 bridge-characterization increment in
  `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added face-level iff characterization lemma:
    - `lemma_mesh_face_seed0_fixed_witness_iff_seed0_plane_contains_vertices`;
  - added all-faces iff characterization lemma:
    - `lemma_mesh_all_faces_seed0_fixed_witness_iff_all_faces_seed0_plane_contains_vertices`;
  - added runtime-alias iff characterization lemma:
    - `lemma_mesh_runtime_all_faces_seed0_fixed_witness_iff_all_faces_seed0_plane_contains_vertices`;
  - outcome: the seed-0 coplanarity bridge layer now has explicit two-way characterizations at face scope,
    aggregate scope, and runtime-alias scope (instead of only directional lemmas), which reduces proof
    plumbing for future checker/spec correctness steps.
  - this advances the unchecked P5.1 checker-correctness item by making the seed-0 witness/plane-containment
    bridge reusable as direct equivalences in later runtime-soundness/completeness proofs.
- 2026-02-19: Failed attempt in this P5.1 bridge-characterization pass:
  - initial proof edit left trailing commas inside `assert(...)` implication expressions in
    `model_and_bridge_specs.rs`, causing a parse error (`expected ')'` near line 2198);
  - fixed by removing those trailing commas and re-running verification.
- 2026-02-19: Revalidated after the P5.1 bridge-characterization additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (258 verified, 0 errors)
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
- 2026-02-19: Completed a P5.7 aggregate-spec characterization increment in
  `src/runtime_halfedge_mesh_refinement/components_and_validity_specs.rs`:
  - added aggregate-spec consequence lemma:
    - `lemma_mesh_geometric_topological_consistency_implies_mesh_valid_and_shared_edge_local_orientation`;
  - added aggregate-spec reconstruction lemma:
    - `lemma_mesh_valid_and_shared_edge_local_orientation_implies_mesh_geometric_topological_consistency`;
  - added aggregate-spec iff characterization lemma:
    - `lemma_mesh_geometric_topological_consistency_spec_characterization`;
  - outcome: the current aggregate refinement target now has an explicit proved characterization:
    `mesh_geometric_topological_consistency_spec(m)` is equivalent to
    `(mesh_valid_spec(m) && mesh_shared_edge_local_orientation_consistency_spec(m))`;
  - this advances the unchecked P5.7 aggregate-equivalence item by making the present proof boundary
    explicit and machine-checked, so remaining equivalence work is now clearly localized to adding
    model-link obligations for the other Phase 5 component checks and proving the concrete runtime
    API path against those stronger links.
- 2026-02-19: Failed attempt in this P5.7 aggregate-spec characterization pass:
  - initial proof edit left trailing commas inside `assert(...)` implication expressions in
    `components_and_validity_specs.rs`, causing a parse error; fixed by removing those trailing
    commas and re-running verification.
- 2026-02-19: Revalidated after the P5.7 aggregate-spec characterization additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (255 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology.sh` (292 verified, 0 errors)
- 2026-02-19: Completed a P5.1 runtime-soundness groundwork increment in
  `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added fixed-seed/non-collinear oriented-plane bridge lemma:
    - `lemma_mesh_face_coplanar_fixed_seed_witness_non_collinear_seed_implies_oriented_seed_plane`;
  - added seed-0 corollary:
    - `lemma_mesh_face_coplanar_seed0_fixed_witness_non_collinear_seed0_implies_oriented_seed0_plane`;
  - outcome: the coplanarity bridge stack now directly supports
    `fixed-seed witness + non-collinear seed -> oriented seed plane` at face scope, without first
    re-lifting through the full coplanar-witness form;
  - this advances the unchecked P5.1 checker-correctness item by closing another gap between
    fixed-seed runtime-shaped witnesses and downstream oriented-plane proof obligations; remaining
    work is still the full `check_face_coplanarity` soundness/completeness proof against
    `mesh_all_faces_coplanar_spec`.
- 2026-02-19: Failed attempts in this P5.1 fixed-seed/non-collinear oriented-plane pass: none.
- 2026-02-19: Revalidated after the P5.1 fixed-seed/non-collinear oriented-plane additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (252 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology.sh` (289 verified, 0 errors)
- 2026-02-19: Completed a P5.1 runtime-soundness groundwork increment in
  `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added point-pair plane-orthogonality bridge lemma:
    - `lemma_mesh_points_on_same_plane_relative_to_origin_imply_normal_orthogonal_delta`;
  - added face-witness lift lemma:
    - `lemma_mesh_face_plane_contains_vertex_witness_implies_normal_orthogonal_face_chords`;
  - this advances the unchecked P5.1 checker-correctness item by exporting reusable algebra from
    face-plane containment witnesses: any face-cycle chord vector between two witnessed points is
    now proven orthogonal to the witness plane normal, which reduces future fixed-seed-to-full
    coplanarity obligations to orientation/permutation plumbing instead of repeated scalar-plane
    arithmetic.
- 2026-02-19: Failed attempts in this P5.1 plane-orthogonality groundwork pass:
  - the first proof revision attempted to conclude `x == y` directly from
    `x + (-y) == 0` using a single `nonlinear_arith` step inside the `eqv_spec` proof block;
    Verus failed that obligation;
  - resolved by explicitly proving the equivalence between the equality form
    `(x == y)` and the zero-difference form `(x + (-y) == 0)` before instantiating `eqv_spec`.
- 2026-02-19: Revalidated after the P5.1 plane-orthogonality groundwork additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (250 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology.sh` (287 verified, 0 errors)
- 2026-02-19: Completed a P5.1 seed-plane/fixed-witness reverse-bridge increment in
  `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added core reverse bridge lemma:
    - `lemma_mesh_face_seed_plane_contains_vertices_witness_implies_coplanar_fixed_seed_witness`;
  - added seed-0 face/all-face reverse corollaries:
    - `lemma_mesh_face_seed0_plane_contains_vertices_implies_seed0_fixed_witness`;
    - `lemma_mesh_all_faces_seed0_plane_contains_vertices_implies_all_faces_seed0_fixed_witness`;
  - added runtime-alias reverse corollary:
    - `lemma_mesh_runtime_all_faces_seed0_plane_contains_vertices_implies_all_faces_seed0_fixed_witness`;
  - outcome: the seed-0 bridge layer is now two-way at both model and runtime-alias levels
    (`seed0 fixed witness -> seed0 plane containment` and
    `seed0 plane containment -> seed0 fixed witness`).
  - this advances the unchecked P5.1 checker-correctness item by eliminating a prior one-way gap in
    the fixed-seed witness chain; remaining work is still the full checker/spec correctness proof
    (`check_face_coplanarity` soundness+completeness against `mesh_all_faces_coplanar_spec`).
- 2026-02-19: Failed attempts in this P5.1 seed-plane/fixed-witness reverse-bridge pass: none.
- 2026-02-19: Revalidated after the P5.1 seed-plane/fixed-witness reverse-bridge additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (244 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology.sh` (281 verified, 0 errors)
- 2026-02-19: Completed a P5.7 aggregate-spec soundness increment in
  `src/runtime_halfedge_mesh_refinement/components_and_validity_specs.rs` and
  `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`:
  - added explicit aggregate refinement specs:
    - `mesh_geometric_topological_consistency_spec`;
    - `mesh_valid_with_geometry_spec`.
  - added aggregate witness-to-spec bridge lemma:
    - `lemma_geometric_topological_consistency_gate_witness_api_ok_implies_mesh_geometric_topological_consistency`.
  - strengthened `lemma_valid_with_geometry_gate_witness_api_ok_implies_mesh_valid` to also establish:
    - `mesh_valid_with_geometry_spec`.
  - strengthened constructive gate contracts/proofs:
    - `check_geometric_topological_consistency_constructive` now proves
      `w.api_ok ==> mesh_geometric_topological_consistency_spec(m@)`;
    - `is_valid_with_geometry_constructive` now proves
      `w.api_ok ==> mesh_valid_with_geometry_spec(m@)`.
  - this advances the unchecked P5.7 aggregate-equivalence item by making the aggregate target
    predicate explicit and proving constructive soundness into it; remaining work is full checker/spec
    equivalence (including completeness against the concrete runtime API path).
- 2026-02-19: Failed attempts in this P5.7 aggregate-spec soundness pass: none.
- 2026-02-19: Revalidated after the P5.7 aggregate-spec soundness additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (240 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology.sh` (277 verified, 0 errors)
- 2026-02-19: Completed the remaining P5.8 kernelized-checker integration item across
  `src/verified_checker_kernels.rs`,
  `src/runtime_halfedge_mesh_refinement/kernel_bridge_lemmas.rs`,
  `src/runtime_halfedge_mesh_refinement/kernel_component_runtime_checks.rs`,
  and `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`:
  - added a new kernelized Phase 5 shared-edge local-orientation checker path:
    - `kernel_twin_faces_distinct_*` specs;
    - `kernel_twin_endpoint_correspondence_*` specs;
    - `kernel_shared_edge_local_orientation_consistency_*` specs;
    - `kernel_check_shared_edge_local_orientation_consistency` with exact checker/spec equivalence (`out == total_spec`);
  - added kernel-to-mesh bridge lemmas for the new checker semantics:
    - twin-face distinctness and twin-endpoint correspondence bridges in both directions;
    - aggregate bridge equivalence lemma:
      - `lemma_kernel_shared_edge_local_orientation_matches_mesh`;
    - aggregate soundness bridge used by runtime wrapper:
      - `lemma_kernel_shared_edge_local_orientation_total_implies_mesh_shared_edge_local_orientation`;
  - added runtime kernel-bridge wrapper:
    - `runtime_check_shared_edge_local_orientation_kernel_bridge`;
  - wired the constructive Phase 5 gate to use the new kernel bridge wrapper for the shared-edge local-orientation proof link.
- 2026-02-19: Failed attempts in this P5.8 kernelized-checker pass:
  - initial endpoint-correspondence bridge proofs failed without explicit index-bounds preconditions on kernel/mesh `next` traversals;
    resolved by tightening lemma preconditions and reusing existing kernel->mesh index-bounds bridging;
  - initial checker loop strengthening attempted to re-establish universal invariants even when `ok == false`;
    resolved by guarding the strengthening step under `if ok`.
- 2026-02-19: Revalidated after the P5.8 kernelized-checker additions:
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (37 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (239 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology.sh` (276 verified, 0 errors)
- 2026-02-19: Completed a P5.1 runtime-soundness groundwork increment in
  `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added an aggregate seed-plane containment spec derived from the seed-0 face plane:
    - `mesh_all_faces_seed0_plane_contains_vertices_spec`;
  - added bridge lemmas from the existing seed-0 fixed coplanarity witness layer to seed-0 plane containment:
    - `lemma_mesh_face_coplanar_seed0_fixed_witness_implies_seed0_plane_contains_vertices`;
    - `lemma_mesh_all_faces_coplanar_seed0_fixed_witness_implies_all_faces_seed0_plane_contains_vertices`;
  - added runtime aliases + bridge lemma for the same aggregate seed-0 plane-containment layer:
    - `mesh_runtime_all_faces_seed0_plane_contains_vertices_spec`;
    - `lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_implies_all_faces_seed0_plane_contains_vertices`;
  - this advances the unchecked P5.1 checker-correctness item by extending the fixed-seed witness bridge chain from:
    runtime coplanarity witness shape -> per-face seed-plane containment -> aggregate all-face seed-plane containment.
- 2026-02-19: Failed attempts in this P5.1 seed-0 plane-containment pass: none.
- 2026-02-19: Revalidated after the P5.1 seed-0 plane-containment additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (232 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (267 verified, 0 errors)
- 2026-02-19: Completed a P5.1 runtime-soundness groundwork increment in
  `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added seed-0 fixed-witness face coplanarity specs:
    - `mesh_face_coplanar_seed0_fixed_witness_spec`;
    - `mesh_all_faces_coplanar_seed0_fixed_witness_spec`;
  - added bridge lemmas from the existing full coplanarity spec to the new seed-0 witness layer:
    - `lemma_mesh_face_coplanar_spec_implies_seed0_fixed_witness`;
    - `lemma_mesh_all_faces_coplanar_spec_implies_all_faces_seed0_fixed_witness`;
  - added runtime aliases + bridge lemma for the same seed-0 witness layer:
    - `mesh_runtime_face_coplanar_seed0_fixed_witness_spec`;
    - `mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec`;
    - `lemma_mesh_runtime_all_faces_coplanar_spec_implies_all_faces_seed0_fixed_witness`;
  - this advances the unchecked P5.1 checker-correctness item by exporting a reusable aggregate witness shape that matches the runtime checker's fixed-seed structure.
- 2026-02-19: Failed attempt in this P5.1 groundwork increment:
  - attempted to directly wire `face_coplanarity_ok` in the aggregate geometric gate to the new seed-0 witness layer;
  - deferred because that still needs a dedicated verified runtime bridge from `Mesh::check_face_coplanarity()` (or an equivalent constructive checker) to the seed-0 witness aggregate spec.
- 2026-02-19: Revalidated after the P5.1 seed-0 witness groundwork increment:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (229 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (264 verified, 0 errors)
- 2026-02-19: Completed the remaining P5.12 Phase 6 handoff-lemma item across
  `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs` and
  `src/runtime_halfedge_mesh_refinement/from_face_cycles_specs_and_lemmas.rs`:
  - added face-cycle trace preservation spec:
    - `mesh_face_cycle_position_trace_preserved_across_meshes_spec`;
  - added coplanarity preservation bridge under trace-preservation preconditions:
    - `lemma_mesh_face_coplanar_witness_preserved_under_face_cycle_position_trace`;
  - added half-edge endpoint-position preservation spec:
    - `mesh_half_edge_endpoint_positions_preserved_across_meshes_at_spec`;
  - added half-edge direction-vector preservation bridge under endpoint-preservation preconditions:
    - `lemma_mesh_half_edge_direction_vector_preserved_across_meshes_from_endpoint_positions`;
  - documented explicit Phase 6 handoff policy under `## P5.12`, splitting invariants into:
    - those preserved by operator preconditions/proofs;
    - those requiring recheck (or stronger operator-specific discharge).
- 2026-02-19: Failed attempts in this P5.12 Phase 6 handoff pass: none.
- 2026-02-19: Revalidated after the P5.12 Phase 6 handoff-lemma additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (226 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (261 verified, 0 errors)
- 2026-02-19: Completed a P5.1 runtime-soundness groundwork pass in `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added fixed-seed coplanarity witness spec:
    - `mesh_face_coplanar_fixed_seed_witness_spec`, which captures the runtime checker's fixed-base shape (`seed_i, seed_i+1, seed_i+2` coplanar with every face-cycle point);
  - added bridge lemma from the existing full witness to the fixed-seed witness:
    - `lemma_mesh_face_coplanar_witness_implies_fixed_seed_witness`;
  - generalized the seed-plane containment bridge to accept fixed-seed witnesses directly:
    - added `lemma_mesh_face_coplanar_fixed_seed_witness_implies_seed_plane_contains_vertices`;
    - refactored `lemma_mesh_face_coplanar_witness_seed_plane_contains_vertices` to route through the new fixed-seed bridge;
  - this advances the remaining unchecked P5.1 checker-correctness item by aligning proof vocabulary with the runtime algorithm's seed choice.
- 2026-02-19: Failed attempt in this P5.1 groundwork pass:
  - attempted to close full runtime-checker soundness immediately by deriving arbitrary quadruple coplanarity from fixed-seed coplanarity in one step;
  - deferred because that requires an additional reusable lemma showing that all points on one non-degenerate seed plane imply `is_coplanar` for every quadruple drawn from that set.
- 2026-02-19: Revalidated after the P5.1 fixed-seed witness groundwork:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (224 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology.sh` (259 verified, 0 errors)
- 2026-02-19: Completed the remaining P5.3 legal-projection-input proof item in `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added `lemma_mesh_face_cycle_prev_next_indices_in_bounds`, proving cyclic `prev`/`next` corner indices remain in `[0, k)` for any valid face-cycle index;
  - added `mesh_face_projected_turn_legal_projection_inputs_witness_spec`, making the projected-turn legality contract explicit:
    - projected `prev`/`curr`/`next` turn points are face-cycle points; and
    - all three points satisfy the face seed-plane equation;
  - added `lemma_mesh_face_projected_turn_sign_witness_uses_legal_projection_inputs`, deriving the legality witness from:
    - projected-turn sign consistency witness; plus
    - coplanarity witness for the same face cycle.
  - this discharges the checklist item:
    - P5.3 `Proof: convexity checker uses only legally projected points from a coplanar face`.
- 2026-02-19: Failed attempt in this P5.3 legal-projection pass:
  - first revision used `#[trigger]` on `let`-bound quantifier locals inside Verus quantified formulas; Verus rejects let-bound trigger terms.
  - resolved by rewriting triggers to direct function terms over quantified indices.
- 2026-02-19: Revalidated after the P5.3 legal-projection proof additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (222 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology.sh` (257 verified, 0 errors)
- 2026-02-18: Completed the remaining P5.6 twin/adjacent orientation interaction proof item across
  `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs` and
  `src/runtime_halfedge_mesh_refinement/from_face_cycles_specs_and_lemmas.rs`:
  - added explicit seed-plane decomposition helpers:
    - `mesh_face_seed_plane_edge_direction_spec`;
    - `mesh_face_seed_plane_corner_direction_spec`;
    - `lemma_mesh_face_seed_plane_normal_decomposes_into_seed_directions`.
  - added twin-edge direction-vector specs and bridge lemmas:
    - `mesh_half_edge_direction_vector_spec`;
    - `mesh_twin_half_edges_opposite_direction_vectors_at_spec`;
    - `mesh_all_twin_half_edges_opposite_direction_vectors_spec`;
    - `lemma_mesh_twin_half_edges_opposite_direction_vectors_at_from_model_and_positions`;
    - `lemma_mesh_all_twin_half_edges_opposite_direction_vectors_from_model_and_positions`.
  - this locks that twin half-edges induce opposite directed geometric edge vectors, consistent with the
    plane-normal seed convention (seed normal built from directed edge factor `p1 - p0`).
  - marked the P5.6 checklist item complete:
    - proof that twin/adjacent orientation interactions agree with plane-normal conventions.
- 2026-02-18: Failed attempts in this P5.6 twin/adjacent orientation interaction pass: none.
- 2026-02-18: Revalidated after the P5.6 twin/adjacent orientation interaction proof additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (220 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology.sh` (255 verified, 0 errors)
- 2026-02-18: Completed the remaining P5.6 oriented-normal proof item in `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added `lemma_mesh_non_collinear_seed_normal_self_dot_sign_is_positive`, proving that a non-collinear seed triple yields positive self-dot sign (`signum == 1`) for the seed face normal;
  - added `lemma_mesh_face_coplanar_witness_non_collinear_seed_implies_oriented_seed_plane`, proving that for a coplanar face cycle and any non-collinear seed triple:
    - the seed plane contains all face vertices; and
    - the seed normal satisfies `mesh_face_winding_orients_plane_normal_with_seed_spec`;
  - this discharges `mesh_face_oriented_plane_normal_spec` for the computed seed plane `(normal, offset)`, completing:
    - P5.6 `Proof: computed normal direction matches face orientation/winding`.
- 2026-02-18: Failed attempts in this P5.6 oriented-normal proof pass: none.
- 2026-02-18: Revalidated after the P5.6 oriented-normal proof additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (217 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (252 verified, 0 errors)
- 2026-02-18: Completed the remaining P5.6 canonical-plane stability item in `src/halfedge_mesh/tests.rs`:
  - added `canonical_face_plane_is_stable_under_cycle_rotation_with_collinear_seed_prefix`;
  - new fixture builds a closed pentagonal prism whose bottom face has a collinear leading triple, then compares three cycle starts for that face:
    - baseline start where `compute_face_plane` skips a collinear seed-triple prefix;
    - rotated start where the first triple is already non-collinear;
    - second rotated start where the first non-collinear seed triple changes and yields a different raw `(normal, offset)` scale;
  - locked that `compute_face_plane_canonical(0)` is identical across all three starts, while raw non-canonical `compute_face_plane(0)` may differ by scale under seed-triple choice.
  - marked the P5.6 checklist item complete:
    - canonicalized plane stability under cyclic face reindexing and seed-triple choice.
- 2026-02-18: Failed attempts in this P5.6 canonical-plane stability pass: none.
- 2026-02-18: Revalidated after the P5.6 canonical-plane stability additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks canonical_face_plane_is_stable_under_cycle_rotation_with_collinear_seed_prefix`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (215 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (250 verified, 0 errors)
- 2026-02-18: Completed a P5.4/P5.5 spec pass in `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added oriented face-normal specs from winding + plane containment:
    - `mesh_face_winding_orients_plane_normal_with_seed_spec`;
    - `mesh_face_oriented_plane_normal_spec`;
    - `mesh_runtime_face_oriented_plane_normal_spec`.
  - added explicit allowed-contact topology specs for face pairs:
    - `mesh_faces_share_vertex_index_spec`;
    - `mesh_faces_share_edge_index_spec`;
    - `mesh_faces_share_exactly_one_vertex_spec`;
    - `mesh_faces_share_exactly_two_vertices_spec`;
    - `mesh_faces_share_exactly_one_edge_spec`;
    - `mesh_faces_allowed_contact_relation_spec`.
  - added non-adjacent forbidden-intersection relation spec:
    - `mesh_non_adjacent_face_pair_forbidden_intersection_relation_spec`.
  - marked checklist items complete for:
    - P5.4 oriented face-normal spec definition;
    - P5.5 allowed-contact relation spec definition;
    - P5.5 forbidden non-adjacent intersection relation spec definition.
- 2026-02-18: Failed attempts in this P5.4/P5.5 spec pass: none.
- 2026-02-18: Revalidated after the P5.4/P5.5 spec additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/check-vcad-topology-trust-surface.sh`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (215 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (250 verified, 0 errors)
- 2026-02-18: Completed a P5.12/ground-rules differential-harness + trust-boundary guardrail pass in `src/halfedge_mesh/tests.rs`:
  - added deterministic randomized fixture helpers:
    - `DeterministicRng`;
    - `random_well_separated_component_origins`;
    - `pick_distinct_indices`;
    - `rotate_point3_z_quarter_turns`;
    - `rigid_rotate_z_quarter_turns_then_translate`;
  - added `differential_randomized_forbidden_intersection_checker_harness`, which runs 40 seeded cases over:
    - random valid disconnected closed meshes;
    - rigidly transformed variants;
    - adversarial perturbations (exact overlap and vertex-touch);
    - and in each case compares optimized `check_no_forbidden_face_face_intersections()` with the no-cull brute-force oracle plus boolean/diagnostic consistency for `check_geometric_topological_consistency()`.
  - added `topology_sources_contain_no_trusted_verification_boundaries`, which recursively scans `crates/vcad-topology/src` (excluding `tests.rs`) and fails on trusted-boundary token usage (`assume_specification`, `external_fn_specification`, `admit`, and external-body/trusted markers).
  - marked checklist items complete for:
    - P5.12 differential/property-based verification harness;
    - dependencies/ground-rules trusted-boundary removal for new Phase 5 APIs.
- 2026-02-18: Failed attempts in this P5.12/ground-rules pass:
  - first revision of `topology_sources_contain_no_trusted_verification_boundaries` used literal forbidden-token strings and tripped the trust-surface pre-scan in `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`; fixed by constructing those token strings from non-contiguous fragments in the test source.
- 2026-02-18: Revalidated after the P5.12/ground-rules differential-harness + trust-boundary guardrail additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/check-vcad-topology-trust-surface.sh`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (215 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (250 verified, 0 errors)
- 2026-02-18: Completed a P5.11 broad-phase culling pass in `src/halfedge_mesh/validation.rs` and `src/halfedge_mesh/tests.rs`:
  - refactored the face-pair intersection path through `check_no_forbidden_face_face_intersections_impl(use_broad_phase)` so the production checker keeps broad-phase enabled while tests can run a no-cull oracle path;
  - added pair-level broad-phase culling helpers:
    - per-face `AABB` bounds (`face_axis_aligned_bounding_box`);
    - `AABB` overlap rejection (`axis_aligned_bounding_boxes_overlap`);
    - strict same-side plane rejection (`face_vertices_strictly_on_one_side_of_plane`);
    - combined prefilter (`face_pair_may_intersect_broad_phase`);
  - added `broad_phase_face_pair_culling_matches_no_cull_oracle`, locking soundness by asserting checker-equivalence between broad-phase and no-cull paths across passing/failing and stress fixtures (including rigid transforms);
  - marked the P5.11 broad-phase culling checklist item complete.
- 2026-02-18: Failed attempts in this P5.11 broad-phase culling pass: none.
- 2026-02-18: Revalidated after the P5.11 broad-phase culling additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks broad_phase_face_pair_culling_matches_no_cull_oracle`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (215 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (250 verified, 0 errors)
- 2026-02-18: Completed a P5.8/ground-rules guardrail pass in `src/halfedge_mesh/tests.rs`:
  - added `runtime_refinement_include_list_covers_all_refinement_modules` (`--features "geometry-checks,verus-proofs"`), which enforces that `src/runtime_halfedge_mesh_refinement.rs` `include!` entries exactly match `src/runtime_halfedge_mesh_refinement/*.rs`;
  - added `topology_sources_remain_exact_arithmetic_only`, which recursively scans `crates/vcad-topology/src` (excluding `tests.rs`) and fails on `f32`/`f64` identifier tokens to block floating-point fallback paths in Phase 5 code;
  - marked checklist items complete for:
    - exact-arithmetic-only Phase 5 paths;
    - refinement proof-module inclusion wiring from `src/runtime_halfedge_mesh_refinement.rs`.
- 2026-02-18: Failed attempts in this P5.8/ground-rules guardrail pass: none.
- 2026-02-18: Revalidated after the guardrail additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (215 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (250 verified, 0 errors)
- 2026-02-18: Completed a P5.5 adjacency-exemption tightening and boundary-overlap rejection pass in `src/halfedge_mesh/validation.rs` and `src/halfedge_mesh/tests.rs`:
  - replaced broad "shared vertex => skip pair" logic in `Mesh::check_no_forbidden_face_face_intersections()`/diagnostic path with an explicit allowed-contact runtime relation:
    - allowed: disjoint boundary, exactly one shared vertex, or exactly one shared edge;
    - rejected: broader shared boundaries (for example, multiple shared edges / coincident double-face boundaries).
  - added boundary-aware segment-vs-face filtering so shared-vertex/shared-edge contact is accepted only when geometric intersection stays on the declared shared boundary, while overlap beyond that boundary is rejected.
  - updated policy-lock tests:
    - `coplanar_neighboring_faces_policy_coincident_double_face_is_rejected` now fails at the intersection checker (`ForbiddenFaceFaceIntersection`) instead of relying on outward-volume rejection;
    - `zero_volume_policy_planar_closed_component_is_rejected` now locks the same earlier forbidden-intersection failure;
    - added `shared_vertex_only_face_contact_is_allowed_when_geometrically_limited_to_that_vertex` (octahedron) as a positive shared-vertex-only contact case.
  - adjusted diagnostic witness-validation test helper to permit forbidden-intersection witnesses on shared-vertex/edge pairs when overlap exceeds allowed boundary.
  - marked the two remaining P5.5 runtime checker tasks complete:
    - tighten adjacency exemptions to exact allowed-contact spec;
    - reject adjacent-face overlap beyond declared shared boundary.
- 2026-02-18: Failed attempts in this P5.5 tightening pass:
  - first revision of the new octahedron positive fixture used inward face winding and failed `check_outward_face_normals()`; fixed by reversing all octahedron face cycles.
  - `cargo fmt --all` could not be run in this environment (`cargo fmt` subcommand unavailable), so no formatter pass was applied.
- 2026-02-18: Revalidated after the P5.5 adjacency/boundary tightening changes:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (215 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (250 verified, 0 errors)
- 2026-02-18: Completed a P5.12 rigid-transform invariance pass in `src/halfedge_mesh/tests.rs`:
  - added exact-arithmetic transform helpers:
    - `transform_mesh_positions`;
    - `translate_point3`;
    - `rotate_point3_z_90`;
    - `rigid_rotate_z_90_then_translate`;
    - `reflect_point3_across_yz_plane`;
  - added `phase5_checks_are_invariant_under_rigid_translation_and_rotation`, locking that full Phase 5 checker signatures are unchanged under a rigid transform (90-degree rotation + translation) for:
    - a passing fixture (`Mesh::cube()`);
    - a failing fixture (`build_overlapping_tetrahedra_mesh()`).
  - added `reflection_flips_outward_orientation_sensitive_phase5_checks`, locking expected reflection behavior:
    - local geometric checks remain invariant;
    - outward-orientation-sensitive checks fail as intended, with diagnostic witness `InwardOrDegenerateComponent`.
  - marked the P5.12 rigid-transform invariance checklist item complete.
- 2026-02-18: Failed attempts in this P5.12 rigid-transform pass: none.
- 2026-02-18: Revalidated after the P5.12 rigid-transform additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (215 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (250 verified, 0 errors)
- 2026-02-18: Completed a P5.12 witness-grade failure validation pass in `src/halfedge_mesh/tests.rs`:
  - added helper `diagnostic_witness_is_real_counterexample`, which validates diagnostic payloads against concrete geometric/topological conditions (zero-length edge endpoints, collinear corner witness, non-coplanar witness corner, non-convex turn witness, forbidden pair witness shape, and non-outward component signed-volume witness);
  - expanded `geometric_consistency_diagnostic_returns_first_failure_witness` to assert witness validity for:
    - `Phase4Validity`;
    - `ZeroLengthGeometricEdge`;
    - `FaceCornerCollinear`;
    - `FaceNonCoplanar`;
    - `FaceNonConvex`;
    - `ForbiddenFaceFaceIntersection`;
    - `InwardOrDegenerateComponent`;
  - added `geometric_consistency_diagnostic_rejects_fabricated_witnesses`, locking that fabricated `FacePlaneInconsistent`, `SharedEdgeOrientationInconsistent`, and `InternalInconsistency` payloads are rejected on a valid tetrahedron;
  - marked the P5.12 witness-grade failure API checklist item complete.
- 2026-02-18: Failed attempt in this P5.12 witness-grade pass:
  - first revision of the test helper called private `validation.rs` internals (`check_index_bounds`, `ordered_face_vertex_cycle`, `face_pair_has_forbidden_intersection`, and others), which broke `cargo test -p vcad-topology --features geometry-checks`; fixed by replacing those calls with test-local geometry computations plus public checker APIs.
- 2026-02-18: Revalidated after the P5.12 witness-grade additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (215 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (250 verified, 0 errors)
- 2026-02-18: Completed a P5.12 connected-component interaction policy pass in `src/halfedge_mesh/validation.rs` and `src/halfedge_mesh/tests.rs`:
  - in `Mesh::check_no_forbidden_face_face_intersections()` docs, clarified that disconnected-component geometric contact is non-exempt for vertex, edge, and face contact (when vertex indices are distinct);
  - added `edge_touch_only_components_policy_is_rejected`, locking that disconnected tetrahedra that touch only along a geometric edge fail the intersection checker and return `ForbiddenFaceFaceIntersection` in the diagnostic gate;
  - added `face_touch_only_components_policy_is_rejected`, locking the same behavior for disconnected tetrahedra that touch across an entire geometric face;
  - marked the P5.12 connected-component interaction policy checklist item complete and documented the explicit accept/reject policy under `## P5.12`.
- 2026-02-18: Failed attempts in this P5.12 connected-component policy pass: none.
- 2026-02-18: Revalidated after the P5.12 connected-component policy additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (215 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (250 verified, 0 errors)
- 2026-02-18: Completed a P5.12 checker-result invariance test pass in `src/halfedge_mesh/tests.rs`:
  - added helper `phase5_checker_signature` to compare full Phase 5 runtime outcomes (`check_*` stage checks, aggregate geometric-consistency gate, and `is_valid_with_geometry`) across equivalent meshes;
  - added helper `relabel_vertices_in_face_cycles` to construct consistently vertex-reindexed face-cycle fixtures;
  - added `phase5_checks_are_invariant_under_face_iteration_order`, proving Phase 5 outcomes are unchanged when face-cycle list order is permuted;
  - added `phase5_checks_are_invariant_under_consistent_vertex_index_relabeling`, proving Phase 5 outcomes are unchanged under a consistent vertex-index bijection for both a passing cube and a failing intersecting-components fixture.
  - marked the P5.12 checker-result invariance checklist item complete (cycle-start invariance already covered by `phase5_checks_are_invariant_under_face_cycle_start_rotation`).
- 2026-02-18: Failed attempts in this P5.12 invariance pass: none.
- 2026-02-18: Revalidated after the P5.12 invariance additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (215 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (250 verified, 0 errors)
- 2026-02-18: Completed a P5.11 scalability/complexity pass:
  - in `src/halfedge_mesh/tests.rs`, added high-face-count stress fixtures and tests:
    - `stress_many_disconnected_components_geometric_consistency_passes` (24 disconnected tetrahedra; 96 faces) to lock large positive behavior;
    - `stress_many_components_with_one_overlap_fails_intersection_checker` (same scale, one intentional overlapping component) to lock large negative intersection behavior and diagnostic failure classification.
  - in this Phase 5 burndown doc, marked the P5.11 complexity and stress-fixture checklist items complete and recorded explicit asymptotic bounds for the current runtime implementation (including face-pair intersection path).
- 2026-02-18: Failed attempts in this P5.11 scalability/complexity pass: none.
- 2026-02-18: Revalidated after the P5.11 scalability/complexity additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (215 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (250 verified, 0 errors)
- 2026-02-18: Completed a P5.11 diagnostics pass in `src/halfedge_mesh/validation.rs` and `src/halfedge_mesh/mod.rs`:
  - added `GeometricTopologicalConsistencyFailure` with first-failure witness payloads (`half_edge`, `face`, `face_a/face_b`, and component-start witnesses);
  - added `Mesh::check_geometric_topological_consistency_diagnostic() -> Result<(), GeometricTopologicalConsistencyFailure>`;
  - added first-failure witness finders for each Phase 5 gate stage (zero-length edge, corner collinearity, coplanarity, convexity, plane consistency, shared-edge orientation, forbidden face-pair intersection, outward signed-volume);
  - changed `Mesh::check_geometric_topological_consistency()` to delegate to the diagnostic API (`is_ok()`), making boolean/diagnostic equivalence hold by construction.
- 2026-02-18: Extended `src/halfedge_mesh/tests.rs` for P5.11 coverage:
  - added `geometric_consistency_diagnostic_agrees_with_boolean_gate`;
  - added `geometric_consistency_diagnostic_returns_first_failure_witness`, locking witness-grade failure categories (`Phase4Validity`, `ZeroLengthGeometricEdge`, `FaceNonConvex`, `ForbiddenFaceFaceIntersection`).
- 2026-02-18: Failed attempt in this P5.11 pass:
  - first revision imported `GeometricTopologicalConsistencyFailure` unconditionally in `validation.rs`, which broke non-`geometry-checks` builds (`cargo test -p vcad-topology`); fixed by feature-gating the import.
- 2026-02-18: Revalidated after the P5.11 diagnostics additions:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (215 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (250 verified, 0 errors)
- 2026-02-18: Completed the P5.10 degeneracy-policy and contract-hardening pass:
  - in `src/halfedge_mesh/validation.rs`, documented explicit checker-contract policy in runtime APIs:
    - `Mesh::check_no_forbidden_face_face_intersections()` now states adjacency exemption is index-based (shared vertex index), and geometric-only position coincidence across distinct vertex indices is not exempt;
    - `Mesh::check_outward_face_normals()` now states zero signed-volume components are rejected in exact arithmetic (no epsilon tolerance path).
  - in `src/halfedge_mesh/tests.rs`, added policy-lock fixtures (positive + negative for each documented boundary class):
    - coplanar neighboring faces:
      - `coplanar_neighboring_faces_policy_split_prism_side_is_accepted`
      - `coplanar_neighboring_faces_policy_coincident_double_face_is_rejected`
    - vertex-touch-only component contact:
      - `vertex_touch_only_components_policy_separated_components_are_accepted`
      - `vertex_touch_only_components_policy_position_touch_is_rejected`
    - zero-volume boundary:
      - `zero_volume_policy_nonzero_tetrahedron_is_accepted`
      - `zero_volume_policy_planar_closed_component_is_rejected`
  - in this Phase 5 burndown doc, marked all P5.10 checklist items complete and recorded explicit accepted/rejected policy statements under `## P5.10`.
- 2026-02-18: Failed attempts in this P5.10 policy-hardening pass: none.
- 2026-02-18: Revalidated after the P5.10 policy and tests pass:
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (215 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `./scripts/verify-vcad-topology.sh` (250 verified, 0 errors)
- 2026-02-18: Completed the P5.4 local-orientation proof item by adding explicit shared-edge orientation specs and constructive proof wiring:
  - in `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
    - added `mesh_twin_faces_distinct_at_spec`, `mesh_twin_faces_distinct_spec`, and aggregate `mesh_shared_edge_local_orientation_consistency_spec`;
  - in `src/runtime_halfedge_mesh_refinement/core_runtime_checks_and_bridges.rs`:
    - added `runtime_check_twin_faces_distinct` (`out ==> mesh_twin_faces_distinct_spec(m@)`);
    - added `runtime_check_shared_edge_local_orientation_consistency` (`out ==> mesh_shared_edge_local_orientation_consistency_spec(m@)`), composed from the new twin-face-distinct checker plus existing `runtime_check_twin_endpoint_correspondence`;
  - in `src/runtime_halfedge_mesh_refinement/components_and_validity_specs.rs`:
    - strengthened `geometric_topological_consistency_gate_model_link_spec` with
      `w.shared_edge_local_orientation_ok ==> mesh_shared_edge_local_orientation_consistency_spec(m)`;
  - in `src/runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs`:
    - wired `check_geometric_topological_consistency_constructive` to require the new verified wrapper signal for `shared_edge_local_orientation_ok`, then discharged the strengthened model-link implication in proof.
- 2026-02-18: Runtime alignment for the same P5.4 pass in `src/halfedge_mesh/validation.rs`:
  - tightened `Mesh::check_shared_edge_local_orientation_consistency()` to check opposite endpoint-vertex order on twin half-edges (and distinct incident faces), matching the new refinement spec vocabulary used in proofs.
- 2026-02-18: Failed attempts in this P5.4 proof pass: none.
- 2026-02-18: Revalidated after the P5.4 local-orientation proof/linking pass:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (215 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology.sh` (250 verified, 0 errors)
- 2026-02-18: Completed the P5.3 projected-turn convexity spec + triangle-trivial proof item in `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added face-local projected convexity spec helpers:
    - `mesh_face_projection_axis_from_normal_spec`
    - `mesh_project_point3_to_2d_for_face_axis_spec`
    - `mesh_face_cycle_prev_index_spec`
    - `mesh_face_cycle_next_index_spec`
    - `mesh_face_projected_turn_sign_at_spec`
  - added projected turn-sign consistency specs:
    - `mesh_face_projected_turn_sign_consistency_witness_spec`
    - `mesh_face_projected_turn_sign_consistency_spec`
    - `mesh_all_faces_projected_turn_sign_consistency_spec`
  - added triangle lemma `lemma_triangle_face_projected_turn_sign_consistency_trivial`, proving the triangle case discharges to the projected-turn convexity spec under explicit nondegenerate witness preconditions.
- 2026-02-18: Failed attempts in this P5.3 projected-turn pass: none.
- 2026-02-18: Revalidated after the P5.3 projected-turn convexity additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (212 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology.sh` (247 verified, 0 errors)
- 2026-02-18: Completed the P5.6 plane-containment proof item in `src/runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs`:
  - added seed-plane helpers:
    - `mesh_face_seed_plane_normal_spec`
    - `mesh_face_seed_plane_offset_relative_to_origin_spec`
  - added algebra bridge lemma `lemma_mesh_point_plane_value_relative_to_origin_matches_relative_dot`, proving the origin-offset plane-value form is equivalent to `normal · (point - plane_point)`;
  - proved `lemma_mesh_face_coplanar_witness_seed_plane_contains_vertices`, deriving per-face plane containment from any coplanarity witness + seed index;
  - added wrapper lemma `lemma_mesh_face_coplanar_spec_implies_seed0_plane_contains_vertices`, producing `face_plane_contains_vertex_spec` from `mesh_face_coplanar_spec`.
- 2026-02-18: Failed attempts in this P5.6 plane-containment pass:
  - first proof revision had Verus parser failures from malformed multiline `assert(...)` punctuation in the new lemma block;
  - after fixing parser issues, one helper-lemma step still failed (`dot_point_from_origin.eqv_spec(...)`) due a missing explicit transitive `eqv` chain; resolved by introducing an intermediate split-dot term and `Scalar::lemma_eqv_transitive`.
- 2026-02-18: Revalidated after the P5.6 plane-containment proof additions:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` (211 verified, 0 errors)
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` (35 verified, 0 errors)
  - `cargo test -p vcad-topology`
  - `cargo test -p vcad-topology --features geometry-checks`
  - `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
  - `./scripts/verify-vcad-topology.sh` (246 verified, 0 errors)
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
- [x] No trusted assumptions remain for Phase 5 APIs.
- [x] Phase 5 degeneracy policy and checker contracts are explicit and test-locked.
- [x] Verification passes:
  - `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
  - `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels`
  - `./scripts/verify-vcad-topology.sh`
- [x] Runtime tests pass for all relevant feature combinations.
