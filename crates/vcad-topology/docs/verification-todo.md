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
- [ ] Add an explicit bridge from runtime mesh structs in `src/halfedge_mesh.rs` to verus-checkable representations.
  - goal: enable direct body-equivalence proofs for runtime checker implementations without opaque-type blocking.
  - candidate paths: migrate core mesh structs into verus-aware definitions, or add verified conversion into the kernel model.

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
- [ ] Add model-level spec for `Mesh::from_face_cycles`.
  - include exact incidence map semantics and failure-condition semantics.
  - file: `src/halfedge_mesh.rs`
- [ ] Prove face-cycle construction assigns coherent `next/prev/face` fields.
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
  - note: this is a verus-native kernel mirror; runtime `Mesh::check_index_bounds` body-equivalence is still pending.
- [x] Verify checker kernel `kernel_check_twin_involution` against explicit spec (`kernel_twin_involution_total_spec`).
  - file: `src/verified_checker_kernels.rs`
  - note: this is a verus-native kernel mirror; runtime `Mesh::check_twin_involution` body-equivalence is still pending.
- [ ] Verify `check_index_bounds`.
  - file: `src/halfedge_mesh.rs`
- [ ] Verify `check_twin_involution`.
  - file: `src/halfedge_mesh.rs`
- [ ] Verify `check_prev_inverse_of_next`.
  - file: `src/halfedge_mesh.rs`
- [ ] Verify `check_face_cycles` (closure + no overlap + min cycle length).
  - file: `src/halfedge_mesh.rs`
- [ ] Verify `check_no_degenerate_edges`.
  - file: `src/halfedge_mesh.rs`
- [ ] Verify `check_vertex_manifold_single_cycle`.
  - file: `src/halfedge_mesh.rs`
- [ ] Verify `check_edge_has_exactly_two_half_edges`.
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
