# vcad-geometry Phase 3: Geometric Predicates
Purpose: define the predicate layer that every topological decision will call, while reusing `vcad-math` proofs instead of duplicating algebra.

## Reuse-First Rule
`vcad-geometry` should treat `vcad-math` as the source of truth for:
1. Scalar arithmetic/order/sign laws.
2. Vector/point algebra laws.
3. `orient2d` / `orient3d` model definitions and invariance/permutation lemmas.
4. Collinearity/coplanarity equivalence surfaces already proved in `vcad-math`.

Do not reprove determinant expansion or vector-space identities in `vcad-geometry`; import and compose.

## Planned Surface
### P3.1 Orientation Predicates
- [x] `orient2d_sign(a, b, c) -> int` (`+1`, `-1`, `0`) runtime wrapper.
- [x] `orient3d_sign(a, b, c, d) -> int` (`+1`, `-1`, `0`) runtime wrapper.
- [x] Prove 2D geometric quantity mapping:
  - `orient2d_spec(a,b,c)` equals the signed double-area polynomial from `vcad-math` (`signed_area2_poly_spec`).
  - expose this as "signed double area" to avoid introducing extra division machinery.
- [x] Prove 3D geometric quantity mapping:
  - `orient3d_spec(a,b,c,d)` equals the signed six-volume polynomial from `vcad-math` (`signed_volume3_poly_spec`).
- [x] Prove plane-side wrapper meaning:
  - `point_above_plane(p, a, b, c)` is equivalent to `(orientation3_spec(a,b,c,p) is Positive)`.
- [ ] Prove full plane-side geometric meaning:
  - with `a,b,c` non-collinear, `orient3d(a,b,c,d) > 0` iff `d` is on the positive side of plane `(a,b,c)`.

vcad-math reuse targets:
1. `orientation::lemma_signed_area2_poly_matches_orient2d`
2. `orientation3::lemma_signed_volume3_poly_matches_orient3d`
3. `orientation::lemma_orientation_spec_matches_predicates`
4. `orientation3::lemma_orientation3_spec_matches_predicates`

### P3.2 Sidedness and Separation
- [x] `point_above_plane(p, a, b, c)` defined via `orient3d_sign(a,b,c,p) > 0`.
- [x] Prove wrapper equivalence: `point_above_plane` iff positive orient3d class.
- [x] Prove strict opposite-side crossing criterion:
  - if `orient3d(a,b,c,d) > 0` and `orient3d(a,b,c,e) < 0`, then segment `de` crosses plane `(a,b,c)`.
- [x] Define exact rational segment-plane parameter `t` for `x(t) = d + t (e-d)` (runtime implemented).
- [ ] Prove `0 < t < 1` under strict crossing preconditions.

vcad-math reuse targets:
1. `orientation3` sign/exclusivity lemmas.
2. `point3` subtraction/translation laws.
3. `vec3` dot/cross linearity and scale extraction lemmas.
4. `scalar` monotonicity/cancellation/signum lemmas.

### P3.3 Collinearity and Coplanarity
- [x] `collinear2d(a,b,c)` wrapper via `orient2d = 0`.
- [x] `collinear3d(a,b,c)` wrapper via edge-cross zero vector criterion.
- [x] `coplanar(a,b,c,d)` wrapper via `orient3d = 0`.
- [x] Prove wrapper equivalences against underlying orient/cross criteria (2D collinearity + 3D coplanarity).
- [ ] Prove coplanarity extension lemma:
  - if `{a,b,c,d}` coplanar and `{a,b,c,e}` coplanar and `a,b,c` non-collinear, then `{a,b,c,d,e}` lie in one plane.

vcad-math reuse targets:
1. `orientation::lemma_is_collinear_iff_edge_vectors_linear_dependent`
2. `orientation3::lemma_is_coplanar_iff_edge_vectors_linear_dependent`
3. `orientation3::lemma_orient3d_zero_iff_edge_vectors_linear_dependent`
4. `vec3` cross/dot law surface for dependence rewrites.

### P3.4 Point in Convex Polygon (2D)
- [ ] Implement `point_in_convex_polygon_2d` using edge-wise `orient2d` sign tests.
- [ ] Define clear boundary policy: points on edges/vertices count as inside.
- [ ] Prove soundness/completeness with convexity precondition:
  - returns `true` iff point is inside or on boundary.

vcad-math reuse targets:
1. `orientation` swap/cyclic/permutation/sign lemmas.
2. `point2` affine translation lemmas.
3. `scalar` sign and order lemmas.

## Proposed vcad-geometry Layout
When crate is created:
1. `src/orientation_predicates.rs`
2. `src/sidedness.rs`
3. `src/collinearity_coplanarity.rs`
4. `src/convex_polygon.rs`
5. `src/runtime_*_refinement.rs` wrappers where runtime APIs are introduced

## Exit Criteria
1. All Phase 3 predicates have executable APIs and model specs.
2. Geometric-meaning lemmas are proved without re-deriving existing `vcad-math` algebra.
3. Crossing/parameter theorem includes strict/non-strict edge-case split.
4. `point_in_convex_polygon_2d` soundness/completeness theorem is proved under explicit convexity assumptions.
5. Verification for new `vcad-geometry` modules is green in focused and full runs.

## Verification Workflow (when vcad-geometry exists)
1. Fast module checks during iteration.
2. Full crate verification gate before merge.
