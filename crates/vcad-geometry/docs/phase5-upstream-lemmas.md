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

- [x] Define `witness_along_normal_spec(p0, p1, p2, witness, normal)` where `witness = p0 + normal` and `normal` is the chosen face normal from `(p1 - p0) x (p2 - p1)`.
  - Landed (2026-02-19): added `witness_along_normal_spec` and helper
    `lemma_witness_along_normal_implies_witness_offset` in
    `crates/vcad-geometry/src/phase5_upstream_lemmas.rs`.
- [ ] Prove:
  - `orient3d(prev, curr, next, witness) = (normal · normal) * orient2d(prev', curr', next')`
  - where `prev'`, `curr'`, `next'` are projections onto the plane orthogonal to `normal` along a chosen dominant axis.
- [ ] Proof sketch:
  - Expand `orient3d` determinant by cofactor along the witness row/column.
  - Decompose witness-minus-vertex vectors into in-plane + normal components.
  - Factor normal component as `normal · normal` times the 2D determinant.
- [ ] Corollary: for nondegenerate faces, `normal · normal > 0`, so `sign(orient3d) == sign(orient2d)`.
  - Verification attempt note (2026-02-19): `RUSTFLAGS='--cfg verus_keep_ghost' cargo test -p vcad-geometry`
    still fails on stable due Verus macro crates requiring nightly-only `#![feature(proc_macro_...)]`;
    this environment has no `rustup`, so ghost-proof checking remains blocked here.

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
- [x] Intermediate lemma: `det3` antisymmetry under argument swap (if missing from existing surface).
  - Landed (2026-02-19): added
    `lemma_det3_swap_first_second_argument`,
    `lemma_det3_swap_second_third_argument`,
    `lemma_det3_swap_first_third_argument`
    in `crates/vcad-geometry/src/phase5_upstream_lemmas.rs`.
  - Failed attempt note (2026-02-19): `RUSTFLAGS='--cfg verus_keep_ghost' cargo test -p vcad-geometry`
    fails in this environment on stable due Verus macro crates requiring nightly-only
    `#![feature(proc_macro_...)]`; `rustup` is unavailable here, so toolchain switching was not possible.

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

- [x] Prove: if two AABBs are separated on at least one axis, then the contained convex sets are disjoint.
  - Landed (2026-02-19, AABB separation pass): added
    `point_in_aabb3_spec`, `aabb_separated_on_some_axis_spec`,
    `lemma_aabb_separation_implies_no_common_point`, and
    `lemma_aabb_separation_implies_disjoint_aabbs` in
    `crates/vcad-geometry/src/phase5_upstream_lemmas.rs`.
  - Landed (2026-02-19, containment-wrapper pass): added
    `shape_contained_in_aabb3_spec` and
    `lemma_aabb_separation_and_containment_implies_disjoint_sets` in
    `crates/vcad-geometry/src/phase5_upstream_lemmas.rs`, packaging the
    contradiction into a reusable containment-to-disjointness theorem
    (`separated AABBs` + per-shape AABB containment => disjoint shapes).
  - Verification attempt note (2026-02-19, AABB separation pass):
    `cargo test -p vcad-geometry` passes in this environment.
  - Verification attempt note (2026-02-19, containment-wrapper pass):
    `cargo test -p vcad-geometry` passes in this environment.
  - Verification attempt note (2026-02-19, containment-wrapper pass):
    `cargo test -p vcad-geometry --features verus-proofs` fails here without
    `--cfg verus_keep_ghost` due unresolved ghost-module imports from
    `vcad-math`; the proof build still needs both the cfg and a nightly-capable
    Verus toolchain.
  - Verification attempt note (2026-02-19, containment-wrapper pass):
    `RUSTFLAGS='--cfg verus_keep_ghost' cargo test -p vcad-geometry --features verus-proofs`
    still fails on stable due Verus macro crates requiring nightly-only
    `#![feature(proc_macro_...)]`, and `rustup` is unavailable in this environment.
- [ ] Prove: if all vertices of face `A` are strictly on one side of face `B` plane, then `A` and `B` do not intersect.
- [ ] Proof sketch for plane separation:
  - If all polygon vertices evaluate strictly positive under a plane equation, every convex combination is strictly positive.
  - Any intersection point on face `B` must satisfy plane value `0`.
  - A point cannot be both `> 0` and `= 0`, contradiction.
- [ ] Intermediate lemma: convex combination of strictly positive values is strictly positive.

## L6: Segment-Face Intersection Predicate Correctness
Blocks: `P5.5` intersection checker soundness (narrow phase).

- [x] Audit which `vcad-geometry` segment/face predicates are used by `vcad-topology` narrow phase.
  - Landed (2026-02-19): audited `crates/vcad-topology/src/halfedge_mesh/validation.rs` narrow-phase path.
  - Used predicates:
    - `sidedness::segment_plane_intersection_point_strict` (non-coplanar segment-vs-face branch).
    - `segment_intersection::segment_intersection_kind_2d` and
      `segment_intersection::segment_intersection_point_2d` (coplanar projected segment-vs-edge branch).
    - `convex_polygon::point_in_convex_polygon_2d` (coplanar branch endpoint-in-polygon checks).
  - Current upstream proof surface status:
    - `segment_plane_intersection_point_strict` already exports an iff/existence shape in
      `crates/vcad-geometry/src/runtime_sidedness_refinement.rs`
      (`is_some() <==> strict_opposite_sides_spec` and existential parameter witness).
    - `segment_intersection_kind_2d` already exports exact classifier refinement and
      kind-partition lemmas in `crates/vcad-geometry/src/runtime_segment_intersection_refinement.rs`.
    - `point_in_convex_polygon_2d` already exports runtime/spec equality plus convex-geometric iff wrappers in
      `crates/vcad-geometry/src/runtime_convex_polygon_refinement.rs`.
    - Landed (2026-02-19, later pass): `segment_intersection_point_2d` now has a
      `verus_keep_ghost` contract in `crates/vcad-geometry/src/segment_intersection.rs`
      and a runtime wrapper in
      `crates/vcad-geometry/src/runtime_segment_intersection_refinement.rs`
      (`runtime_segment_intersection_point_refines_spec`) that:
      - guarantees `None` for `Disjoint` and `CollinearOverlap` classifier results;
      - guarantees `EndpointTouch && Some(p) -> point_on_both_segments_spec(p, ...)`.
    - Update (2026-02-19, latest pass): classifier/spec now encode endpoint-touch using
      explicit endpoint-on-both-segments witnesses, and both
      `segment_intersection_point_2d` plus
      `runtime_segment_intersection_point_refines_spec` now prove
      `EndpointTouch -> out.is_some()`.
    - Update (2026-02-19, proper-totality pass): `segment_intersection_point_2d` and
      `runtime_segment_intersection_point_refines_spec` now also prove
      `Proper -> out.is_some()` via new helpers
      `lemma_segment_intersection_kind_spec_proper_implies_straddling_signs` and
      `lemma_proper_straddling_implies_nonzero_direction_cross`, which establish the
      proper-case straddling sign pattern and nonzero line-direction denominator.
    - Update (2026-02-19, support-line pass): added
      `point_on_segment_supporting_line_spec` in
      `crates/vcad-geometry/src/segment_intersection.rs`, and strengthened both
      `segment_intersection_point_2d` and
      `runtime_segment_intersection_point_refines_spec` with
      `Proper && Some(p) -> orient2d_spec(a, b, p).signum() == 0`
      (returned witness is proven collinear with segment `[a,b]`'s supporting line).
    - Update (2026-02-19, dual-support-line pass): strengthened
      `proper_intersection_point_runtime` and propagated contracts through
      `segment_intersection_point_2d` plus
      `runtime_segment_intersection_point_refines_spec` so `Proper && Some(p)` now also proves
      `orient2d_spec(c, d, p).signum() == 0` (witness is collinear with both supporting lines).
      Remaining formal gap is closed-segment bound inclusion on both segments.
    - Verification attempt note (2026-02-19, dual-support-line pass): `cargo test -p vcad-geometry`
      passes in this environment.
    - Verification attempt note (2026-02-19, proper-totality pass):
      `RUSTFLAGS='--cfg verus_keep_ghost' cargo test -p vcad-geometry --features verus-proofs`
      still fails on stable because Verus macro crates require nightly-only `#![feature(proc_macro_...)]`.
    - Verification attempt note (2026-02-19, proper-totality pass): running
      `cargo test -p vcad-geometry --features verus-proofs` without `--cfg verus_keep_ghost`
      fails with unresolved ghost-module imports from `vcad-math`; the proof build needs both
      the `verus_keep_ghost` cfg and a nightly-capable Verus toolchain.
    - Remaining gap from this audit: no `Proper`-case
      `Some(p) -> point_on_both_segments_spec` proof yet.
- [x] Add `segment_intersection_point_2d` witness-soundness contracts for endpoint-touch outputs.
  - Landed (2026-02-19): added `verus_keep_ghost` `segment_intersection_point_2d`,
    plus endpoint helper `endpoint_touch_point_runtime` proving returned endpoint witnesses
    satisfy `point_on_both_segments_spec`.
- [ ] For each used predicate, ensure there is a proved iff-style spec (add missing proofs/specs as needed):
  - [ ] segment-triangle intersection (`ray/segment-plane parameter` + barycentric containment).
    - Audit note (2026-02-19): topology currently composes plane crossing/intersection with a local
      in-face boundary test; upstream still needs a unified iff wrapper at the geometry boundary.
  - [ ] coplanar segment-segment intersection (2D projection + interval overlap).
    - Update (2026-02-19, proper-totality pass): endpoint-touch witness-soundness plus
      `EndpointTouch -> is_some` and `Proper -> is_some` totality are now landed; remaining
      open piece is the `Proper`-case witness-on-both proof.
    - Update (2026-02-19, runtime-guard pass): added runtime `debug_assert!` checks in
      `proper_intersection_point_runtime` and added regression tests in
      `crates/vcad-geometry/src/segment_intersection.rs` that exercise non-integer proper
      intersections and assert returned witnesses lie on both source segments at runtime.
      Formal ghost proof for `Proper`-case witness-on-both remains open.
    - Update (2026-02-19, support-line pass): formalized an intermediate `Proper` witness fact:
      the computed witness is collinear with `[a,b]`'s supporting line; remaining formal gap is
      proving collinearity with `[c,d]` and closed-segment bound inclusion to recover full
      `point_on_both_segments_spec`.
    - Update (2026-02-19, dual-support-line pass): upgraded the intermediate `Proper` witness fact
      to collinearity with both supporting lines `[a,b]` and `[c,d]`; remaining formal gap is now
      proving closed-segment bound inclusion for both segments to recover full
      `point_on_both_segments_spec`.
  - [ ] coplanar segment-polygon overlap (dominant-axis projection + edge-crossing containment tests).
    - Audit note (2026-02-19): ingredient predicates are present, but their composed
      dominant-axis overlap witness proof is not yet packaged upstream.
    - Update (2026-02-19, packaging pass): added
      `segment_overlaps_convex_polygon_2d` in
      `crates/vcad-geometry/src/segment_polygon_overlap.rs`, packaging the
      coplanar projected overlap composition already used downstream:
      endpoint-in-polygon checks plus per-edge segment intersection-kind scan.
    - Update (2026-02-19, packaging pass): added runtime regression tests in
      `crates/vcad-geometry/src/segment_polygon_overlap.rs` covering short
      polygon rejection, endpoint-inside, proper crossing, endpoint touch,
      collinear edge overlap, and disjoint cases.
    - Update (2026-02-19, composed-spec pass): upgraded
      `crates/vcad-geometry/src/segment_polygon_overlap.rs` with a
      `verus_keep_ghost` composed-spec contract
      (`segment_overlaps_convex_polygon_composed_spec`) plus a proved
      implementation of `segment_overlaps_convex_polygon_2d`:
      `out == spec` (short-polygon reject, endpoint-inside shortcut, and
      edge-hit scan all modeled/proved).
    - Update (2026-02-19, composed-spec pass): added
      `crates/vcad-geometry/src/runtime_segment_polygon_overlap_refinement.rs`
      and wired it in `crates/vcad-geometry/src/lib.rs` so downstream proofs
      can import an explicit runtime refinement wrapper:
      `runtime_segment_overlaps_convex_polygon_refines_spec`.
    - Remaining gap (post-composed-spec pass): still missing the stronger
      point-witness-level iff (`true <==> exists witness point` satisfying all
      geometric constraints simultaneously). Current upstream contract is a
      structured disjunction witness (endpoint-in-polygon or non-disjoint
      per-edge segment classifier witness).
    - Verification attempt note (2026-02-19, packaging pass):
      `cargo test -p vcad-geometry` passes in this environment.
    - Verification attempt note (2026-02-19, composed-spec pass):
      `cargo test -p vcad-geometry` passes in this environment.
    - Verification attempt note (2026-02-19, composed-spec pass):
      `cargo test -p vcad-geometry --features verus-proofs` still fails here
      without `--cfg verus_keep_ghost` due unresolved ghost-module imports from
      `vcad-math`.
    - Verification attempt note (2026-02-19, composed-spec pass):
      `RUSTFLAGS='--cfg verus_keep_ghost' cargo test -p vcad-geometry --features verus-proofs`
      still fails on stable due Verus macro crates requiring nightly-only
      `#![feature(proc_macro_...)]` and this environment has no `rustup`.
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
