# vcad-topology
Verified topological representation layer.

Current scope (Phase 4 foundation):
1. Half-edge data model (`Mesh`, `HalfEdge`, `Vertex`, `Edge`, `Face`) using arena indices.
2. Structural invariant checks:
   - twin involution,
   - next/prev inverses,
   - per-face next-cycle closure and cycle length >= 3,
   - non-degenerate edge endpoints,
   - manifold single-cycle around each vertex via `twin/next`,
   - exactly two half-edges per edge.
3. Connectivity and Euler checks:
   - component counting by BFS over the half-edge graph,
   - per-component Euler characteristic,
   - `V - E + F = 2` gate for closed sphere-like components.
4. Hand-constructed regression meshes:
   - tetrahedron,
   - cube,
   - triangular prism.
5. Verus refinement boundary (`runtime_halfedge_mesh_refinement`) for validity contracts.

Planning document:
1. `docs/phase4-topology.md`
