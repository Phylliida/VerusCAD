# vcad-topology Verification TODO
Goal: eliminate trusted gaps until all topology behavior is justified by explicit specs + proofs.

## A. Remove Trusted Runtime Boundary (Highest Priority)
- [x] Remove trusted boundary `assume_specification[ Mesh::is_structurally_valid ]` from refinement surface.
  - semantic correctness is tracked under sections D/F (`check_*` and `is_structurally_valid` verification in `src/halfedge_mesh.rs`).
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Remove trusted boundary `assume_specification[ Mesh::check_euler_formula_closed_components ]` from refinement surface.
  - semantic correctness is tracked under section E/F (`check_euler_formula_closed_components` verification in `src/halfedge_mesh.rs`).
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Replace `assume_specification[ Mesh::is_valid ]` with proven refinement.
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Remove trusted boundary `assume_specification[ Mesh::component_count ]` from refinement surface.
  - semantic correctness is tracked under section E (`component_count` / BFS verification in `src/halfedge_mesh.rs`).
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Remove trusted boundary `assume_specification[ Mesh::tetrahedron ]` from refinement surface.
  - semantic correctness is tracked under section G (constructor verification in `src/halfedge_mesh.rs`).
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Remove trusted boundary `assume_specification[ Mesh::cube ]` from refinement surface.
  - semantic correctness is tracked under section G (constructor verification in `src/halfedge_mesh.rs`).
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Remove trusted boundary `assume_specification[ Mesh::triangular_prism ]` from refinement surface.
  - semantic correctness is tracked under section G (constructor verification in `src/halfedge_mesh.rs`).
  - file: `src/runtime_halfedge_mesh_refinement.rs`

## A1. Runtime/Verus Bridge Prerequisite
- [x] Add an explicit bridge from runtime mesh structs in `src/halfedge_mesh.rs` to verus-checkable kernel representations.
  - implemented conversion helper: `to_kernel_mesh_for_verification`.
  - implemented bridge executables: `check_index_bounds_via_kernel`, `check_twin_involution_via_kernel`.
  - implemented runtime sanity helper: `bridge_index_and_twin_checks_agree`.
  - file: `src/halfedge_mesh.rs`
- [x] Prove bridge correctness/equivalence for `check_index_bounds` and `check_twin_involution` in `verus-proofs` builds by construction.
  - runtime methods now delegate directly to kernel checkers in proof-enabled builds.
  - file: `src/halfedge_mesh.rs`
- [x] Extend bridge correctness/equivalence to `check_prev_inverse_of_next` and `check_no_degenerate_edges` in `verus-proofs` builds by construction.
  - runtime methods now delegate directly to kernel checkers in proof-enabled builds.
  - file: `src/halfedge_mesh.rs`
- [x] Extend bridge-equivalence strategy to remaining runtime checker bodies.
  - all structural runtime checkers now delegate to kernel executables in `verus-proofs` builds.
  - semantic proof strength still differs by checker (see section D notes).

## B. Replace Abstract Spec Predicates
- [x] Define `mesh_edge_exactly_two_half_edges_spec` explicitly (currently uninterpreted).
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Define `mesh_face_next_cycles_spec` explicitly (currently uninterpreted).
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Define `mesh_vertex_manifold_single_cycle_spec` explicitly (currently uninterpreted).
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Define `mesh_euler_closed_components_spec` explicitly (currently uninterpreted).
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Define `mesh_component_count_spec` explicitly (currently uninterpreted).
  - file: `src/runtime_halfedge_mesh_refinement.rs`

## C. Verify Core Construction Pipeline
- [x] Add model-level spec for `Mesh::from_face_cycles`.
  - includes explicit incidence-model semantics and failure-condition semantics:
    `from_face_cycles_incidence_model_spec`, `from_face_cycles_success_spec`, `from_face_cycles_failure_spec`.
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [ ] Prove face-cycle construction assigns coherent `next/prev/face` fields.
  - foundation added: `from_face_cycles_next_prev_face_coherent_spec` with projection lemmas from
    `from_face_cycles_incidence_model_spec` / `from_face_cycles_success_spec`.
  - executable bridge added: `ex_mesh_from_face_cycles` maps runtime `Result` outcomes to
    `from_face_cycles_success_spec` / `from_face_cycles_failure_spec`.
  - note: the bridge currently uses `#[verifier::external_fn_specification]` (trusted); replace with
    constructive proof from implementation as this section advances.
  - file: `src/halfedge_mesh.rs`
- [ ] Prove twin assignment is total for closed inputs and involutive.
  - file: `src/halfedge_mesh.rs`
- [ ] Prove undirected-edge grouping induces exactly-two-half-edges per edge.
  - file: `src/halfedge_mesh.rs`
- [ ] Prove vertex representative (`vertex.half_edge`) is valid and non-isolated.
  - file: `src/halfedge_mesh.rs`

## D. Verify Invariant Checker Functions
- [x] Verify checker kernel `kernel_check_index_bounds` against explicit spec (`kernel_index_bounds_spec`).
  - file: `src/verified_checker_kernels.rs`
  - note: runtime `Mesh::check_index_bounds` now delegates to this kernel checker in `verus-proofs` builds.
- [x] Verify checker kernel `kernel_check_twin_involution` against explicit spec (`kernel_twin_involution_total_spec`).
  - file: `src/verified_checker_kernels.rs`
  - note: runtime `Mesh::check_twin_involution` now delegates to this kernel checker in `verus-proofs` builds.
- [x] Verify checker kernel `kernel_check_prev_inverse_of_next` against explicit spec (`kernel_prev_next_inverse_total_spec`).
  - file: `src/verified_checker_kernels.rs`
  - note: runtime `Mesh::check_prev_inverse_of_next` now delegates to this kernel checker in `verus-proofs` builds.
- [x] Verify checker kernel `kernel_check_no_degenerate_edges` against explicit spec (`kernel_no_degenerate_edges_total_spec`).
  - file: `src/verified_checker_kernels.rs`
  - note: runtime `Mesh::check_no_degenerate_edges` now delegates to this kernel checker in `verus-proofs` builds.
- [x] Verify checker kernel `kernel_check_edge_has_exactly_two_half_edges` against explicit spec (`kernel_edge_exactly_two_half_edges_total_spec`).
  - file: `src/verified_checker_kernels.rs`
  - note: runtime `Mesh::check_edge_has_exactly_two_half_edges` now delegates to this kernel checker in `verus-proofs` builds.
- [x] Add bridge kernel executable `kernel_check_face_cycles` and delegate runtime checker in `verus-proofs` builds.
  - file: `src/verified_checker_kernels.rs`
  - note: current proved contract is bounds-soundness (`out ==> kernel_index_bounds_spec`); full face-cycle semantic contract is pending.
- [x] Add bridge kernel executable `kernel_check_vertex_manifold_single_cycle` and delegate runtime checker in `verus-proofs` builds.
  - file: `src/verified_checker_kernels.rs`
  - note: current proved contract is bounds-soundness (`out ==> kernel_index_bounds_spec`); full vertex-manifold semantic contract is pending.
- [x] Verify `check_index_bounds`.
  - in `verus-proofs` builds, this is delegated to verified kernel checker.
  - file: `src/halfedge_mesh.rs`
- [x] Verify `check_twin_involution`.
  - in `verus-proofs` builds, this is delegated to verified kernel checker.
  - file: `src/halfedge_mesh.rs`
- [x] Verify `check_prev_inverse_of_next`.
  - in `verus-proofs` builds, this is delegated to verified kernel checker.
  - file: `src/halfedge_mesh.rs`
- [ ] Verify `check_face_cycles` (closure + no overlap + min cycle length).
  - in `verus-proofs` builds, this now delegates to kernel executable `kernel_check_face_cycles`.
  - semantic contract strengthening in kernel proof is still pending.
  - attempted path (rolled back): direct monolithic strengthening of `kernel_check_face_cycles` to
    `out ==> kernel_face_representative_cycles_total_spec` with a large in-loop existential witness invariant.
    this triggered unstable quantifier-trigger obligations and brittle loop-body proof failures under full verification.
    avoid repeating this monolithic approach; prefer factoring into small helper lemmas (next-iter progression, per-face witness construction, and existential lifting) before re-strengthening the executable postcondition.
  - next substeps:
    - strengthen `kernel_check_face_cycles` postcondition from `out ==> kernel_index_bounds_spec` to `out ==> kernel_face_representative_cycles_total_spec`.
    - add per-face cycle-length witness threading invariant (`forall fp < f. exists k ...`) in outer loop.
    - prove representative-cycle witness construction at face loop boundary (`k = steps`).
  - file: `src/halfedge_mesh.rs`
- [x] Verify `check_no_degenerate_edges`.
  - in `verus-proofs` builds, this is delegated to verified kernel checker.
  - file: `src/halfedge_mesh.rs`
- [ ] Verify `check_vertex_manifold_single_cycle`.
  - in `verus-proofs` builds, this now delegates to kernel executable `kernel_check_vertex_manifold_single_cycle`.
  - semantic contract strengthening in kernel proof is still pending.
  - next substeps:
    - strengthen `kernel_check_vertex_manifold_single_cycle` postcondition from `out ==> kernel_index_bounds_spec` to `out ==> kernel_vertex_manifold_single_cycle_total_spec`.
    - add per-vertex cycle witness threading invariant (`forall vp < v. exists k ...`) in outer loop.
    - prove representative-ring witness construction at vertex loop boundary (`k = steps`).
  - file: `src/halfedge_mesh.rs`
- [x] Verify `check_edge_has_exactly_two_half_edges`.
  - in `verus-proofs` builds, this is delegated to a verified kernel checker.
  - file: `src/halfedge_mesh.rs`

## E. Verify Connectivity + Euler Computation
- [ ] Verify `half_edge_components` BFS soundness and completeness.
  - file: `src/halfedge_mesh.rs`
- [ ] Verify `component_count` equals number of connected components.
  - file: `src/halfedge_mesh.rs`
- [ ] Verify `euler_characteristics_per_component` computes `V - E + F` per BFS component.
  - file: `src/halfedge_mesh.rs`
- [ ] Verify `check_euler_formula_closed_components` iff all closed components have characteristic `2`.
  - file: `src/halfedge_mesh.rs`

## F. Verify Top-Level APIs
- [ ] Verify `is_structurally_valid` exactly matches conjunction of structural invariants.
  - file: `src/halfedge_mesh.rs`
- [ ] Verify `is_valid` exactly matches `is_structurally_valid && check_euler_formula_closed_components`.
  - file: `src/halfedge_mesh.rs`

## G. Verify Reference Mesh Constructors End-to-End
- [ ] Prove `tetrahedron` builds and satisfies `is_valid`.
  - prove counts: `V=4, E=6, F=4, H=12`.
  - file: `src/halfedge_mesh.rs`
- [ ] Prove `cube` builds and satisfies `is_valid`.
  - prove counts: `V=8, E=12, F=6, H=24`.
  - file: `src/halfedge_mesh.rs`
- [ ] Prove `triangular_prism` builds and satisfies `is_valid`.
  - prove counts: `V=6, E=9, F=5, H=18`.
  - file: `src/halfedge_mesh.rs`

## H. Reuse-Focused Hardening (No Reinventing)
- [ ] Reuse `vcad-math` proof surfaces for arithmetic/cardinality/order where applicable.
- [ ] Reuse `vcad-geometry` predicates for optional geometric non-degeneracy extensions (face area > 0, etc.).

## Exit Condition
- [x] No `assume_specification` remains in `vcad-topology` for runtime mesh behavior.
- [x] No uninterpreted spec predicate remains for currently implemented invariants.
- [x] `verify-vcad-topology-fast.sh` and `verify-vcad-topology.sh` both green.
