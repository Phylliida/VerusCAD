

# Verified B-Rep Kernel — Verification Todo List

Ordered by dependency. Each phase builds on the one above it.

---

## Phase 1 — Exact Arithmetic Foundation (rug)

Wrap `rug::Integer` and `rug::Rational` with the interface the kernel needs. State the algebraic properties as trusted axioms since GMP is unverified C.

Status (2026-02-18): partially complete in `vcad-math`; core wrappers and arithmetic law surface are in place, while conversion/testing hardening items remain open.

**Wrapper types**

- [x] Define thin wrappers around `rug::Integer` and `rug::Rational` with the operations the kernel uses
- [ ] Document which `rug` operations are used and what properties are assumed about each
- [ ] Implement `From`/`Into` conversions for i64, f64 → Rational

**Axiomatized properties**

- [x] State as axioms: Rational forms an ordered field (commutativity, associativity, distributivity, multiplicative inverse, total order compatibility)
- [x] State as axioms: sign rules (positive × positive = positive, etc.)
- [x] State as axioms: comparison compatibility with arithmetic (a ≤ b ⟹ a+c ≤ b+c, etc.)
- [x] State as axiom: division is exact (a/b × b = a for b ≠ 0)
- [x] Document trust boundary explicitly: "we assume GMP is correct"

**Sanity tests**

- [ ] Property-based tests: random arithmetic identities hold (e.g. (a+b)×c = a×c + b×c for random rationals)
- [ ] Edge cases: zero, negative zero normalization, very large numerators/denominators

---

## Phase 2 — Points, Vectors, and Core Geometry

Define geometric primitives over exact rationals. No matrices — just the specific operations the predicates need.

Status (2026-02-18): implemented and formally verified in `vcad-math`.

**Primitives**

- [x] Define Point2, Point3, Vec2, Vec3 over Rational. Points and vectors as distinct types.
- [x] Vector operations: add, sub, scale. Prove basic properties (linearity, etc.) from the axioms.
- [x] Dot product. Prove bilinearity and commutativity: a·b = b·a
- [x] Cross product (3D). Prove anti-commutativity: a×b = -(b×a)
- [x] Prove cross product orthogonality: a·(a×b) = 0

**Helper expressions for predicates**

- [x] Implement 2D signed-area formula: (bx - ax)(cy - ay) - (by - ay)(cx - ax). This is the polynomial that orient2d evaluates.
- [x] Implement 3D signed-volume formula: the explicit expansion of the 3×3 determinant of edge vectors from orient3d. Write it out directly, no matrix type.
- [x] Prove: signed-area formula flips sign when any two input points are swapped (antisymmetry)
- [x] Prove: signed-volume formula flips sign when any two input points are swapped (antisymmetry)
- [x] Prove: signed-area = 0 iff the three points are collinear (vectors linearly dependent)
- [x] Prove: signed-volume = 0 iff the four points are coplanar (vectors linearly dependent)

---

## Phase 3 — Geometric Predicates

The critical layer. Every topological decision invokes these. Verify both computation and geometric meaning.

Status (2026-02-18): implemented and formally verified in `vcad-geometry` (with refinement bridges to `vcad-math`).

**Orientation predicates**

- [x] orient2d(a, b, c): wraps signed-area formula from Phase 2. Returns +1 (CCW), -1 (CW), 0 (collinear). Prove = 2× signed area of triangle abc.
- [x] orient3d(a, b, c, d): wraps signed-volume formula from Phase 2. Returns +1/−1/0. Prove = 6× signed volume of tetrahedron abcd.
- [x] Prove orient3d geometric meaning: positive iff d is on positive side of plane(a,b,c)

**Sidedness and separation**

- [x] point_above_plane(p, plane) — reduce to orient3d, prove equivalence
- [x] Prove: if orient3d(a,b,c,d) > 0 and orient3d(a,b,c,e) < 0 then segment de crosses plane abc
- [x] Segment-plane intersection point: compute exact rational intersection parameter t. Prove 0 < t < 1 when crossing confirmed.

**Collinearity and coplanarity**

- [x] collinear(a, b, c): orient2d = 0 (2D) or cross product = zero vector (3D). Verify.
- [x] coplanar(a, b, c, d): orient3d = 0. Verify.
- [x] Prove transitivity-like property: if {a,b,c,d} coplanar and {a,b,c,e} coplanar and a,b,c non-collinear, then {a,b,c,d,e} coplanar.

**Point-in-convex-polygon (2D projected)**

- [x] Implement: reduce to sequence of orient2d tests against each edge
- [x] Prove: returns true iff point is on or inside the convex polygon

---

## Phase 4 — Topological Data Structure & Invariants

Define the half-edge data structure and formalize what "valid mesh" means. No mutation yet — just representation and checking.

Status (2026-02-18): implemented and formally verified in `vcad-topology` (see `crates/vcad-topology/docs/verification-todo.md`, sections F/G).

**Data structure definition**

- [x] Define HalfEdge, Vertex, Edge, Face, Mesh types. Half-edge stores: twin, next, prev, vertex, edge, face.
- [x] Choose indexing strategy (arena indices vs references) and document

**Structural invariants**

- [x] Inv: twin(twin(h)) = h for all half-edges h
- [x] Inv: next-cycle is a valid cycle (following next from h returns to h). Prove cycle length ≥ 3 per face.
- [x] Inv: prev is the inverse of next (prev(next(h)) = h)
- [x] Inv: vertex(h) ≠ vertex(twin(h)) — no degenerate edges
- [x] Inv: all half-edges around a vertex form a single cycle via twin/next (manifold condition)
- [x] Inv: each face's half-edges all reference that face
- [x] Inv: each edge has exactly two half-edges (its twin pair)

**Euler formula and connectivity**

- [x] Implement component counting (BFS/DFS on half-edge graph)
- [x] State and verify Euler's formula: V - E + F = 2 per closed component
- [x] Implement is_valid(mesh) → bool checking all invariants. Prove soundness.

**Test meshes**

- [x] Construct tetrahedron by hand, prove is_valid
- [x] Construct cube by hand, prove is_valid
- [x] Construct triangular prism by hand, prove is_valid

---

## Phase 5 — Geometric-Topological Consistency Invariants

Tie geometry to topology: vertices have coordinates, faces are planar and convex, edges are straight.

**Invariants to formalize**

- [ ] Inv: each face's vertices are coplanar (orient3d = 0 for all quads of face vertices)
- [ ] Inv: each face is a convex polygon (all consecutive orient2d tests agree in sign)
- [ ] Inv: face normals point outward (consistent orientation across the whole mesh)
- [ ] Inv: no two faces of the same solid intersect except at shared edges/vertices

**Plane computation**

- [ ] Compute face plane from vertices: normal = cross product of two edge vectors, offset = dot with vertex.
- [ ] Prove computed plane contains all face vertices (using coplanarity invariant)
- [ ] Prove normal direction matches face orientation

---

## Phase 6 — Euler Operators (Primitive Topology Mutations)

Implement the small atomic operations that modify the mesh. Each one must preserve all invariants.

**Operator implementation and verification**

- [ ] Make Vertex-Edge (MVE / split-edge): insert vertex in middle of edge. Prove: valid in → valid out.
- [ ] Make Edge-Face (MEF / split-face): connect two vertices on same face, splitting it. Prove: valid in → valid out.
- [ ] Kill Edge-Make Ring (KEMR): remove edge to merge faces — inverse of MEF. Prove: valid in → valid out.
- [ ] Kill Edge-Vertex (KEV / join-edge): remove vertex merging two edges — inverse of MVE. Prove: valid in → valid out.
- [ ] Make Face-Kill Ring-Hole (MFKRH): for solids with holes/handles — defer if only handling genus-0 initially.

**Geometric validity through operators**

- [ ] Prove: MVE preserves coplanarity of affected faces
- [ ] Prove: MEF preserves convexity of both result faces (given preconditions)
- [ ] Prove: MEF input precondition checker is correct (two vertices on same face, split yields convex faces)

**Composition lemmas**

- [ ] Prove: sequence of valid Euler ops on valid mesh yields valid mesh (induction)
- [ ] Prove Euler formula is preserved by each operator (ΔV - ΔE + ΔF = 0)

---

## Phase 7 — Boolean Operations (Intersection Phase)

Compute how two solids' boundaries intersect. This is the most complex phase.

**Face-face intersection**

- [ ] Implement plane-plane intersection → line (or parallel/coincident classification). Two plane normals, cross product gives line direction, solve for a point on the line — all exact rational.
- [ ] Clip intersection line to both face polygons → segment (or empty)
- [ ] Prove: if result is a segment, both endpoints lie on boundary edges of the respective faces
- [ ] Prove: if result is empty, faces don't intersect (using sidedness predicates)
- [ ] Handle all face-face configurations: crossing, touching at edge, touching at vertex, coplanar overlap

**Intersection graph construction**

- [ ] Collect all face-face intersection segments into an intersection graph
- [ ] Prove: intersection graph vertices that lie on an edge of solid A are correctly computed
- [ ] Prove: intersection graph forms closed loops on each face (for proper intersections)

---

## Phase 8 — Boolean Operations (Split & Classify Phase)

Split faces along intersection curves, classify faces as in/out/on, assemble result.

**Face splitting**

- [ ] Insert intersection points as new vertices on face boundary edges (MVE)
- [ ] Split each intersected face along intersection segments (MEF)
- [ ] Prove: after splitting, each sub-face is a valid convex polygon
- [ ] Prove: the split mesh is a valid mesh (all invariants preserved)

**Face classification**

- [ ] For each sub-face of solid A, classify as inside/outside/on-boundary of solid B
- [ ] Implement point-in-solid test: cast ray, count crossings using orient3d
- [ ] Prove: classification is well-defined (independent of chosen interior point)
- [ ] Prove: ray casting gives correct parity (using predicate lemmas from Phase 3)

**Face selection and stitching**

- [ ] Select faces based on Boolean op: union keeps outside+on, intersection keeps inside+on, etc.
- [ ] Orient selected faces consistently (flip faces from solid B in union, etc.)
- [ ] Stitch selected faces into result mesh along shared intersection edges
- [ ] Prove: result mesh is a valid closed 2-manifold
- [ ] Prove: result mesh bounds the correct point set (the ultimate correctness theorem)

---

## Phase 9 — Degeneracy Handling

Extend all of the above to handle degenerate inputs: coplanar faces, touching edges, coincident vertices.

**Approach decision**

- [ ] Decide: Simulation of Simplicity (SoS) vs. case-by-case degeneracy handling
- [ ] If SoS: implement perturbation scheme and prove it resolves all degeneracies consistently
- [ ] If case-by-case: enumerate degenerate configurations for each predicate/operation

**Key degenerate cases**

- [ ] Coplanar face pairs in Boolean operations — compute 2D polygon intersection
- [ ] Edge-on-edge intersections — T-junction and cross configurations
- [ ] Vertex-on-face and vertex-on-edge contacts
- [ ] Prove: degenerate handling is consistent (no contradictory decisions from different code paths)

---

## Phase 10 — Adaptive Precision (Optimization)

Replace exact rationals with adaptive floating-point predicates for performance. Verified exact path is the fallback.

**Floating-point foundations**

- [ ] Model IEEE 754 f64 semantics at the spec level
- [ ] Verify Two-Sum: prove a + b = s + e exactly
- [ ] Verify Two-Product (or Two-Product-FMA): prove a × b = p + e exactly

**Expansion arithmetic**

- [ ] Implement expansion-sum (merge two non-overlapping expansions)
- [ ] Implement scale-expansion (multiply expansion by float)
- [ ] Prove: expansion components are non-overlapping after each operation
- [ ] Prove: sign of expansion = sign of most significant component

**Adaptive predicates**

- [ ] Implement adaptive orient2d with Stage A / B / C error bounds
- [ ] Prove: if Stage A bound is satisfied, float result sign = exact sign
- [ ] Prove: Stage C (full expansion) gives exact sign
- [ ] Implement adaptive orient3d with same structure
- [ ] Implement adaptive in-circle / in-sphere if needed
- [ ] Implement fallback: if adaptive is uncertain, call verified exact rational predicate from rug

---

## Phase 11 — Infrastructure & Polish

Non-critical items that don't block verification but are needed for a usable system.

**I/O and conversion**

- [ ] Parse STL files → mesh (unverified is fine; verify the validator catches bad input)
- [ ] Parse/export OBJ, OFF, or other formats
- [ ] Convert f64 coordinates to exact rational on input via `rug::Rational::from_f64`
- [ ] Convert exact rational coordinates to f64 on output (verified rounding)

**Spatial indexing (unverified optimization)**

- [ ] BVH or octree for face-face intersection candidate pruning

**Testing and validation**

- [ ] Property-based tests: random meshes through Booleans, verify result validity
- [ ] Regression test suite of known-tricky inputs (near-degenerate, large coordinates, etc.)
- [ ] Benchmark suite comparing exact vs. adaptive performance

---

**Notes:**

- **Trust boundary.** GMP (via `rug`) is treated as a correct oracle for exact rational arithmetic. This is the one unverified component in the stack. If you ever want to close this gap, Phase 1 becomes "reimplement and verify bignum from scratch" — but that's a separate project.
- **Phases 1–3** are the foundations. Phase 1 is mostly wiring now that rug handles the heavy lifting; the real verification work starts at Phase 2.
- **Phases 4–6** are where the B-Rep kernel takes shape. You can build and test small examples (tetrahedron, cube) here.
- **Phases 7–8** are the summit. Expect to iterate back to earlier phases when you discover your invariant definitions need adjustment.
- **Phases 9–11** can be deferred. Assume general position for v1 to get a working verified Boolean pipeline sooner, then harden.
- **No matrix types.** Predicates use explicit polynomial expressions over coordinates.
- **No rotations in the kernel.** Apply transformations at the API boundary and feed resulting coordinates in as exact rationals.
