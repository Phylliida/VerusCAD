# vcad-topology Phase 4: Topological Data Structure and Invariants
Purpose: define and validate the half-edge topological representation layer before mutation operations.

## Reuse-First Rule
`vcad-topology` should reuse lower layers where possible:
1. `vcad-math` point/scalar runtime types for geometric payloads on topology entities.
2. `vcad-geometry` predicates for future geometry-aware topology checks (not required for pure incidence invariants).

## Indexing Strategy
Arena indexing with `usize` IDs into stable vectors:
1. `Mesh.vertices: Vec<Vertex>`
2. `Mesh.edges: Vec<Edge>`
3. `Mesh.faces: Vec<Face>`
4. `Mesh.half_edges: Vec<HalfEdge>`

This avoids reference aliasing complexity and keeps structural invariants first-order and checkable.

## Phase 4 Surface
### P4.1 Data Structure Definition
- [x] `HalfEdge` fields: `twin`, `next`, `prev`, `vertex`, `edge`, `face`.
- [x] `Vertex`, `Edge`, `Face`, `Mesh` runtime structs.
- [x] Construction helper from explicit face cycles:
  - `Mesh::from_face_cycles`.

### P4.2 Structural Invariants
Implemented checks:
- [x] `twin(twin(h)) == h`.
- [x] `prev(next(h)) == h` and `next(prev(h)) == h`.
- [x] Face cycles close under `next` and each face cycle length >= 3.
- [x] All half-edges in a face cycle reference that face.
- [x] `vertex(h) != vertex(twin(h))` (plus no self-loop half-edge).
- [x] Vertex manifold condition: all outgoing half-edges at a vertex form one cycle via `next(twin(h))`.
- [x] Each edge has exactly two half-edges that are twins.

Validity API:
- [x] `Mesh::is_structurally_valid()` for structural invariants.
- [x] Verus refinement surface (`runtime_halfedge_mesh_refinement`) with explicit model predicates for structural validity, connectivity components, and Euler relation.
  - runtime-method semantic correctness is tracked in the backlog for direct body verification in `src/halfedge_mesh.rs`.
  - verified checker kernels are staged in `src/verified_checker_kernels.rs` for `index_bounds` and `twin_involution`.
  - (`component_count` semantic correctness is tracked in the verification backlog for direct body verification).
  - (reference constructor correctness is tracked in the verification backlog for direct body verification).

### P4.3 Euler Formula and Connectivity
- [x] Component counting via BFS on half-edge graph (`twin/next/prev` adjacency).
- [x] Per-component Euler characteristic `V - E + F`.
- [x] Closed-component gate `V - E + F = 2` (sphere-like components):
  - `Mesh::check_euler_formula_closed_components()`.
- [x] Unified validity gate:
  - `Mesh::is_valid() = structural invariants + Euler gate`.

### P4.4 Test Meshes
- [x] Hand-constructed tetrahedron (`Mesh::tetrahedron`).
- [x] Hand-constructed cube (`Mesh::cube`).
- [x] Hand-constructed triangular prism (`Mesh::triangular_prism`).
- [x] Unit tests proving these constructors satisfy `is_valid()`.

## Remaining Hardening Work
1. Optional generalized Euler handling for higher-genus closed components (`V - E + F = 2 - 2g`).
2. Geometry-aware non-degeneracy checks for faces/volumes using `vcad-geometry` predicates.
3. Full exhaustive verification backlog is tracked in:
   - `docs/verification-todo.md`
