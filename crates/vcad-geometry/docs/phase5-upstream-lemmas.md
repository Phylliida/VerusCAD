# vcad-geometry Phase 5 Upstream Lemmas TODO
Purpose: land algebraic/geometric lemmas in `vcad-geometry` that currently block remaining Phase 5 proof items in `vcad-topology`.

Reference downstream tracker:
- `crates/vcad-topology/docs/phase5-geometric-topology-consistency.md`

## Why These Block Phase 5
The remaining open proof items in `vcad-topology` Phase 5 bottom out on missing facts about `orient3d`, `orient2d`, determinants, and plane membership. Those facts belong in `vcad-geometry` because they are pure geometry/algebra and do not depend on half-edge topology structure.

## L1: Plane Membership Implies Orient3d Zero
Blocks: `P5.1` coplanarity checker correctness for `k > 4`.

- [x] Define `points_on_common_plane_spec(a, b, c, d, normal, offset)` where all four satisfy `normal · p = offset`.
  - Landed in `crates/vcad-geometry/src/phase5_upstream_lemmas.rs` (2026-02-19).
- [ ] Prove: if `normal` is nonzero and all four points lie on the plane, then `orient3d(a, b, c, d) == 0`.
  - Partial (2026-02-19): proved `lemma_points_on_common_plane_with_aligned_normal_implies_orient3d_zero` under extra alignment precondition `normal == (b-a) x (c-a)`.
- [ ] Proof sketch:
  - `orient3d` is `det3((b-a), (c-a), (d-a))`.
  - If all four share a plane with nonzero normal `n`, then:
    - `n · (b-a) = 0`
    - `n · (c-a) = 0`
    - `n · (d-a) = 0`
  - So the three column vectors are in a 2D subspace orthogonal to `n`, hence determinant is zero.
- [ ] Intermediate lemma: if three vectors are all orthogonal to one nonzero vector, they are linearly dependent (equivalently `det3 == 0`).
  - Partial (2026-02-19): proved `lemma_three_vectors_orthogonal_to_aligned_nonzero_normal_implies_det_zero` with extra precondition `normal == u x v`.
  - Failed attempt note: did not finish the fully general `normal != 0` orthogonality-to-determinant proof (without the alignment precondition). Remaining gap is the generic 3D subspace/dimension argument or equivalent algebraic elimination.
  - Failed attempt note (2026-02-19, later pass): explored a component-elimination proof path (derive `normal.x * det == 0`/`normal.y * det == 0`/`normal.z * det == 0` from orthogonality constraints, then cancel nonzero component), but did not land a clean reusable proof script yet.

## L2: Orient3d / Orient2d Projection Factoring
Blocks: `P5.3` convexity checker correctness.

- [ ] Define `witness_along_normal_spec(p0, p1, p2, witness, normal)` where `witness = p0 + normal` and `normal` is the chosen face normal from `(p1 - p0) x (p2 - p1)`.
- [ ] Prove:
  - `orient3d(prev, curr, next, witness) = (normal · normal) * orient2d(prev', curr', next')`
  - where `prev'`, `curr'`, `next'` are projections onto the plane orthogonal to `normal` along a chosen dominant axis.
- [ ] Proof sketch:
  - Expand `orient3d` determinant by cofactor along the witness row/column.
  - Decompose witness-minus-vertex vectors into in-plane + normal components.
  - Factor normal component as `normal · normal` times the 2D determinant.
- [ ] Corollary: for nondegenerate faces, `normal · normal > 0`, so `sign(orient3d) == sign(orient2d)`.

## L3: Determinant Trilinearity / Linearity in Origin
Blocks: `P5.4` signed-volume origin independence.

- [x] Prove linearity in each determinant argument, e.g. `det3(a + t, b, c) = det3(a, b, c) + det3(t, b, c)`.
  - Landed (2026-02-19): added `det3_spec` plus
    `lemma_det3_linear_first_argument`,
    `lemma_det3_linear_second_argument`,
    `lemma_det3_linear_third_argument`
    in `crates/vcad-geometry/src/phase5_upstream_lemmas.rs`.
- [ ] Prove:
  - for a closed oriented surface mesh with opposite-direction twin edge usage,
  - `sum_faces det3(v0 - O', v1 - O', v2 - O') = sum_faces det3(v0 - O, v1 - O, v2 - O)`.
- [ ] Proof sketch:
  - Expand origin shift by trilinearity into terms involving `(O - O')`.
  - Group terms as signed edge contributions.
  - Use closed-mesh edge pairing (already proved in `vcad-topology`) to cancel all shift terms.
- [ ] Intermediate lemma: `det3` antisymmetry under argument swap (if missing from existing surface).

## L4: Consistent Orientation + Signed-Volume Sign -> All Normals Outward
Blocks: `P5.4` global outwardness.

- [ ] Prove: flipping all face orientations negates signed volume.
- [ ] Prove: consistent local orientation implies exactly two global orientation classes (outward vs inward).
- [ ] Prove: by convention, the negative signed-volume class corresponds to outward normals.
- [ ] Split plan:
  - keep algebraic sign-flip lemma in `vcad-geometry`;
  - compose with topology orientation-consistency facts in `vcad-topology` via an explicit interface/spec hook.

## L5: AABB / Plane Separation Soundness
Blocks: `P5.5` intersection checker soundness (broad phase).

- [ ] Prove: if two AABBs are separated on at least one axis, then the contained convex sets are disjoint.
- [ ] Prove: if all vertices of face `A` are strictly on one side of face `B` plane, then `A` and `B` do not intersect.
- [ ] Proof sketch for plane separation:
  - If all polygon vertices evaluate strictly positive under a plane equation, every convex combination is strictly positive.
  - Any intersection point on face `B` must satisfy plane value `0`.
  - A point cannot be both `> 0` and `= 0`, contradiction.
- [ ] Intermediate lemma: convex combination of strictly positive values is strictly positive.

## L6: Segment-Face Intersection Predicate Correctness
Blocks: `P5.5` intersection checker soundness (narrow phase).

- [ ] Audit which `vcad-geometry` segment/face predicates are used by `vcad-topology` narrow phase.
- [ ] For each used predicate, ensure there is a proved iff-style spec (add missing proofs/specs as needed):
  - [ ] segment-triangle intersection (`ray/segment-plane parameter` + barycentric containment);
  - [ ] coplanar segment-segment intersection (2D projection + interval overlap);
  - [ ] coplanar segment-polygon overlap (dominant-axis projection + edge-crossing containment tests).
- [ ] Proof shape: predicate returns `true` iff a witness point exists satisfying all geometric constraints simultaneously.

## Suggested Landing Order
1. [ ] `L1` first (simplest; immediate unblock for coplanarity with `k > 4`).
2. [ ] `L2` next (unblocks convexity; can reuse determinant expansion scaffolding).
3. [ ] `L3` then (trilinearity/origin-shift machinery).
4. [ ] `L5` and `L6` in parallel (independent tracks).
5. [ ] `L4` last (compose algebra from `L3` with topology consistency facts).

## Exit Criteria
- [ ] Each lemma family above is verified in `vcad-geometry` with no trusted assumptions.
- [ ] Lemma signatures/specs are importable by `vcad-topology` Phase 5 proof modules.
- [ ] Re-attempt the remaining open Phase 5 proof items in `vcad-topology` using this upstream lemma surface.
