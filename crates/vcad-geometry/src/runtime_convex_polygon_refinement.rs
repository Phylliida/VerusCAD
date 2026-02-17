#![cfg(feature = "verus-proofs")]

use crate::convex_polygon;
use vcad_math::orientation::orient2d_spec;
use vcad_math::point2::Point2;
use vcad_math::runtime_point2::RuntimePoint2;
use vcad_math::scalar::Scalar;
use vstd::prelude::*;

verus! {

pub open spec fn polygon_next_index_spec(polygon: Seq<RuntimePoint2>, i: int) -> int
    recommends
        polygon.len() > 0,
        0 <= i < polygon.len() as int,
{
    if i + 1 < polygon.len() as int { i + 1 } else { 0 }
}

pub open spec fn polygon_edge_orient_sign_spec(p: Point2, polygon: Seq<RuntimePoint2>, i: int) -> int
    recommends
        polygon.len() >= 3,
        0 <= i < polygon.len() as int,
{
    orient2d_spec(
        polygon[i]@,
        polygon[polygon_next_index_spec(polygon, i)]@,
        p,
    ).signum()
}

pub open spec fn polygon_vertex_turn_sign_spec(polygon: Seq<RuntimePoint2>, i: int) -> int
    recommends
        polygon.len() >= 3,
        0 <= i < polygon.len() as int,
{
    let j = polygon_next_index_spec(polygon, i);
    let k = polygon_next_index_spec(polygon, j);
    orient2d_spec(
        polygon[i]@,
        polygon[j]@,
        polygon[k]@,
    ).signum()
}

pub open spec fn polygon_has_positive_edge_sign_spec(p: Point2, polygon: Seq<RuntimePoint2>) -> bool
    recommends
        polygon.len() >= 3,
{
    exists|i: int| 0 <= i < polygon.len() as int && polygon_edge_orient_sign_spec(p, polygon, i) > 0
}

pub open spec fn polygon_has_negative_edge_sign_spec(p: Point2, polygon: Seq<RuntimePoint2>) -> bool
    recommends
        polygon.len() >= 3,
{
    exists|i: int| 0 <= i < polygon.len() as int && polygon_edge_orient_sign_spec(p, polygon, i) < 0
}

pub open spec fn polygon_has_zero_edge_sign_spec(p: Point2, polygon: Seq<RuntimePoint2>) -> bool
    recommends
        polygon.len() >= 3,
{
    exists|i: int| 0 <= i < polygon.len() as int && polygon_edge_orient_sign_spec(p, polygon, i) == 0
}

pub open spec fn polygon_all_edge_sign_positive_spec(p: Point2, polygon: Seq<RuntimePoint2>) -> bool
    recommends
        polygon.len() >= 3,
{
    forall|i: int| 0 <= i < polygon.len() as int ==> polygon_edge_orient_sign_spec(p, polygon, i) > 0
}

pub open spec fn polygon_all_edge_sign_negative_spec(p: Point2, polygon: Seq<RuntimePoint2>) -> bool
    recommends
        polygon.len() >= 3,
{
    forall|i: int| 0 <= i < polygon.len() as int ==> polygon_edge_orient_sign_spec(p, polygon, i) < 0
}

pub open spec fn polygon_all_edge_sign_nonnegative_spec(p: Point2, polygon: Seq<RuntimePoint2>) -> bool
    recommends
        polygon.len() >= 3,
{
    forall|i: int| 0 <= i < polygon.len() as int ==> polygon_edge_orient_sign_spec(p, polygon, i) >= 0
}

pub open spec fn polygon_all_edge_sign_nonpositive_spec(p: Point2, polygon: Seq<RuntimePoint2>) -> bool
    recommends
        polygon.len() >= 3,
{
    forall|i: int| 0 <= i < polygon.len() as int ==> polygon_edge_orient_sign_spec(p, polygon, i) <= 0
}

pub open spec fn polygon_all_vertex_turns_nonnegative_spec(polygon: Seq<RuntimePoint2>) -> bool
    recommends
        polygon.len() >= 3,
{
    forall|i: int| 0 <= i < polygon.len() as int ==> polygon_vertex_turn_sign_spec(polygon, i) >= 0
}

pub open spec fn polygon_all_vertex_turns_nonpositive_spec(polygon: Seq<RuntimePoint2>) -> bool
    recommends
        polygon.len() >= 3,
{
    forall|i: int| 0 <= i < polygon.len() as int ==> polygon_vertex_turn_sign_spec(polygon, i) <= 0
}

pub open spec fn polygon_all_vertex_turns_positive_spec(polygon: Seq<RuntimePoint2>) -> bool
    recommends
        polygon.len() >= 3,
{
    forall|i: int| 0 <= i < polygon.len() as int ==> polygon_vertex_turn_sign_spec(polygon, i) > 0
}

pub open spec fn polygon_all_vertex_turns_negative_spec(polygon: Seq<RuntimePoint2>) -> bool
    recommends
        polygon.len() >= 3,
{
    forall|i: int| 0 <= i < polygon.len() as int ==> polygon_vertex_turn_sign_spec(polygon, i) < 0
}

/// Weak convexity + consistent cyclic ordering:
/// every consecutive vertex turn has the same sign-or-zero.
pub open spec fn polygon_convex_consistent_order_spec(polygon: Seq<RuntimePoint2>) -> bool {
    &&& polygon.len() >= 3
    &&& (
        polygon_all_vertex_turns_nonnegative_spec(polygon)
            || polygon_all_vertex_turns_nonpositive_spec(polygon)
    )
}

/// Strict convexity + consistent cyclic ordering:
/// every consecutive vertex turn is strictly positive or strictly negative.
pub open spec fn polygon_strict_convex_consistent_order_spec(polygon: Seq<RuntimePoint2>) -> bool {
    &&& polygon.len() >= 3
    &&& (
        polygon_all_vertex_turns_positive_spec(polygon)
            || polygon_all_vertex_turns_negative_spec(polygon)
    )
}

/// Exact model of the runtime algorithm in `convex_polygon::point_in_convex_polygon_2d`:
/// polygons with at least 3 vertices are "inside" iff no edge-orientation signs
/// of opposite nonzero sign are observed.
pub open spec fn point_in_convex_polygon_edge_sign_consistent_spec(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
) -> bool {
    &&& polygon.len() >= 3
    &&& !(polygon_has_positive_edge_sign_spec(p, polygon) && polygon_has_negative_edge_sign_spec(p, polygon))
}

/// Boundary policy: points on edges/vertices (zero orientation for one or more
/// edges) are counted as inside, as long as no mixed positive/negative signs appear.
pub open spec fn point_in_convex_polygon_boundary_inclusive_spec(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
) -> bool {
    point_in_convex_polygon_edge_sign_consistent_spec(p, polygon)
}

/// Exact model of the strict runtime algorithm:
/// no mixed positive/negative edge signs and no zero edge sign.
pub open spec fn point_strictly_in_convex_polygon_edge_sign_consistent_spec(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
) -> bool {
    &&& polygon.len() >= 3
    &&& !(polygon_has_positive_edge_sign_spec(p, polygon) && polygon_has_negative_edge_sign_spec(p, polygon))
    &&& !polygon_has_zero_edge_sign_spec(p, polygon)
}

/// Edge-halfspace characterization ("inside or on boundary") used for convex polygons.
/// This is winding-independent: all edge tests are nonnegative or all are nonpositive.
pub open spec fn point_in_convex_polygon_edge_halfspace_spec(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
) -> bool {
    &&& polygon.len() >= 3
    &&& (
        polygon_all_edge_sign_nonnegative_spec(p, polygon)
            || polygon_all_edge_sign_nonpositive_spec(p, polygon)
    )
}

/// Geometric meaning under convex + consistent-order precondition.
pub open spec fn point_in_convex_polygon_geometric_spec(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
) -> bool {
    &&& polygon_convex_consistent_order_spec(polygon)
    &&& point_in_convex_polygon_edge_halfspace_spec(p, polygon)
}

/// Strict edge-halfspace characterization ("strictly inside"):
/// all edge tests are strictly positive or all strictly negative.
pub open spec fn point_strictly_in_convex_polygon_edge_halfspace_spec(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
) -> bool {
    &&& polygon.len() >= 3
    &&& (
        polygon_all_edge_sign_positive_spec(p, polygon)
            || polygon_all_edge_sign_negative_spec(p, polygon)
    )
}

pub open spec fn point_strictly_in_convex_polygon_geometric_spec(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
) -> bool {
    &&& polygon_strict_convex_consistent_order_spec(polygon)
    &&& point_strictly_in_convex_polygon_edge_halfspace_spec(p, polygon)
}

pub open spec fn point_on_convex_polygon_boundary_spec(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
) -> bool {
    &&& point_in_convex_polygon_edge_halfspace_spec(p, polygon)
    &&& polygon_has_zero_edge_sign_spec(p, polygon)
}

proof fn lemma_all_edge_nonnegative_implies_no_negative(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
)
    requires
        polygon.len() >= 3,
        polygon_all_edge_sign_nonnegative_spec(p, polygon),
    ensures
        !polygon_has_negative_edge_sign_spec(p, polygon),
{
    if polygon_has_negative_edge_sign_spec(p, polygon) {
        let i = choose|i: int|
            0 <= i < polygon.len() as int
                && polygon_edge_orient_sign_spec(p, polygon, i) < 0;
        assert(0 <= i < polygon.len() as int);
        assert(polygon_all_edge_sign_nonnegative_spec(p, polygon));
        assert(polygon_edge_orient_sign_spec(p, polygon, i) >= 0);
        assert(polygon_edge_orient_sign_spec(p, polygon, i) < 0);
        assert(false);
    }
}

proof fn lemma_all_edge_nonpositive_implies_no_positive(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
)
    requires
        polygon.len() >= 3,
        polygon_all_edge_sign_nonpositive_spec(p, polygon),
    ensures
        !polygon_has_positive_edge_sign_spec(p, polygon),
{
    if polygon_has_positive_edge_sign_spec(p, polygon) {
        let i = choose|i: int|
            0 <= i < polygon.len() as int
                && polygon_edge_orient_sign_spec(p, polygon, i) > 0;
        assert(0 <= i < polygon.len() as int);
        assert(polygon_all_edge_sign_nonpositive_spec(p, polygon));
        assert(polygon_edge_orient_sign_spec(p, polygon, i) <= 0);
        assert(polygon_edge_orient_sign_spec(p, polygon, i) > 0);
        assert(false);
    }
}

proof fn lemma_all_edge_positive_implies_no_negative(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
)
    requires
        polygon.len() >= 3,
        polygon_all_edge_sign_positive_spec(p, polygon),
    ensures
        !polygon_has_negative_edge_sign_spec(p, polygon),
{
    if polygon_has_negative_edge_sign_spec(p, polygon) {
        let i = choose|i: int|
            0 <= i < polygon.len() as int
                && polygon_edge_orient_sign_spec(p, polygon, i) < 0;
        assert(0 <= i < polygon.len() as int);
        assert(polygon_all_edge_sign_positive_spec(p, polygon));
        assert(polygon_edge_orient_sign_spec(p, polygon, i) > 0);
        assert(polygon_edge_orient_sign_spec(p, polygon, i) < 0);
        assert(false);
    }
}

proof fn lemma_all_edge_positive_implies_no_zero(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
)
    requires
        polygon.len() >= 3,
        polygon_all_edge_sign_positive_spec(p, polygon),
    ensures
        !polygon_has_zero_edge_sign_spec(p, polygon),
{
    if polygon_has_zero_edge_sign_spec(p, polygon) {
        let i = choose|i: int|
            0 <= i < polygon.len() as int
                && polygon_edge_orient_sign_spec(p, polygon, i) == 0;
        assert(0 <= i < polygon.len() as int);
        assert(polygon_all_edge_sign_positive_spec(p, polygon));
        assert(polygon_edge_orient_sign_spec(p, polygon, i) > 0);
        assert(polygon_edge_orient_sign_spec(p, polygon, i) == 0);
        assert(false);
    }
}

proof fn lemma_all_edge_negative_implies_no_positive(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
)
    requires
        polygon.len() >= 3,
        polygon_all_edge_sign_negative_spec(p, polygon),
    ensures
        !polygon_has_positive_edge_sign_spec(p, polygon),
{
    if polygon_has_positive_edge_sign_spec(p, polygon) {
        let i = choose|i: int|
            0 <= i < polygon.len() as int
                && polygon_edge_orient_sign_spec(p, polygon, i) > 0;
        assert(0 <= i < polygon.len() as int);
        assert(polygon_all_edge_sign_negative_spec(p, polygon));
        assert(polygon_edge_orient_sign_spec(p, polygon, i) < 0);
        assert(polygon_edge_orient_sign_spec(p, polygon, i) > 0);
        assert(false);
    }
}

proof fn lemma_all_edge_negative_implies_no_zero(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
)
    requires
        polygon.len() >= 3,
        polygon_all_edge_sign_negative_spec(p, polygon),
    ensures
        !polygon_has_zero_edge_sign_spec(p, polygon),
{
    if polygon_has_zero_edge_sign_spec(p, polygon) {
        let i = choose|i: int|
            0 <= i < polygon.len() as int
                && polygon_edge_orient_sign_spec(p, polygon, i) == 0;
        assert(0 <= i < polygon.len() as int);
        assert(polygon_all_edge_sign_negative_spec(p, polygon));
        assert(polygon_edge_orient_sign_spec(p, polygon, i) < 0);
        assert(polygon_edge_orient_sign_spec(p, polygon, i) == 0);
        assert(false);
    }
}

proof fn lemma_no_negative_implies_all_edge_nonnegative(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
)
    requires
        polygon.len() >= 3,
        !polygon_has_negative_edge_sign_spec(p, polygon),
    ensures
        polygon_all_edge_sign_nonnegative_spec(p, polygon),
{
    assert forall|i: int|
        0 <= i < polygon.len() as int implies polygon_edge_orient_sign_spec(p, polygon, i) >= 0 by {
        if 0 <= i < polygon.len() as int {
            if polygon_edge_orient_sign_spec(p, polygon, i) < 0 {
                assert(0 <= i < polygon.len() as int);
                assert(
                    exists|j: int|
                        0 <= j < polygon.len() as int
                            && polygon_edge_orient_sign_spec(p, polygon, j) < 0
                ) by {
                    assert(0 <= i < polygon.len() as int && polygon_edge_orient_sign_spec(p, polygon, i) < 0);
                }
                assert(polygon_has_negative_edge_sign_spec(p, polygon));
                assert(false);
            }
            assert(polygon_edge_orient_sign_spec(p, polygon, i) >= 0);
        }
    }
}

proof fn lemma_no_positive_implies_all_edge_nonpositive(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
)
    requires
        polygon.len() >= 3,
        !polygon_has_positive_edge_sign_spec(p, polygon),
    ensures
        polygon_all_edge_sign_nonpositive_spec(p, polygon),
{
    assert forall|i: int|
        0 <= i < polygon.len() as int implies polygon_edge_orient_sign_spec(p, polygon, i) <= 0 by {
        if 0 <= i < polygon.len() as int {
            if polygon_edge_orient_sign_spec(p, polygon, i) > 0 {
                assert(0 <= i < polygon.len() as int);
                assert(
                    exists|j: int|
                        0 <= j < polygon.len() as int
                            && polygon_edge_orient_sign_spec(p, polygon, j) > 0
                ) by {
                    assert(0 <= i < polygon.len() as int && polygon_edge_orient_sign_spec(p, polygon, i) > 0);
                }
                assert(polygon_has_positive_edge_sign_spec(p, polygon));
                assert(false);
            }
            assert(polygon_edge_orient_sign_spec(p, polygon, i) <= 0);
        }
    }
}

proof fn lemma_no_negative_no_zero_implies_all_edge_positive(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
)
    requires
        polygon.len() >= 3,
        !polygon_has_negative_edge_sign_spec(p, polygon),
        !polygon_has_zero_edge_sign_spec(p, polygon),
    ensures
        polygon_all_edge_sign_positive_spec(p, polygon),
{
    assert forall|i: int|
        0 <= i < polygon.len() as int implies polygon_edge_orient_sign_spec(p, polygon, i) > 0 by {
        if 0 <= i < polygon.len() as int {
            let s = polygon_edge_orient_sign_spec(p, polygon, i);
            if s > 0 {
            } else if s < 0 {
                assert(
                    exists|j: int|
                        0 <= j < polygon.len() as int
                            && polygon_edge_orient_sign_spec(p, polygon, j) < 0
                ) by {
                    assert(0 <= i < polygon.len() as int && polygon_edge_orient_sign_spec(p, polygon, i) < 0);
                }
                assert(polygon_has_negative_edge_sign_spec(p, polygon));
                assert(false);
            } else {
                assert(s == 0);
                assert(
                    exists|j: int|
                        0 <= j < polygon.len() as int
                            && polygon_edge_orient_sign_spec(p, polygon, j) == 0
                ) by {
                    assert(0 <= i < polygon.len() as int && polygon_edge_orient_sign_spec(p, polygon, i) == 0);
                }
                assert(polygon_has_zero_edge_sign_spec(p, polygon));
                assert(false);
            }
        }
    }
}

proof fn lemma_no_positive_no_zero_implies_all_edge_negative(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
)
    requires
        polygon.len() >= 3,
        !polygon_has_positive_edge_sign_spec(p, polygon),
        !polygon_has_zero_edge_sign_spec(p, polygon),
    ensures
        polygon_all_edge_sign_negative_spec(p, polygon),
{
    assert forall|i: int|
        0 <= i < polygon.len() as int implies polygon_edge_orient_sign_spec(p, polygon, i) < 0 by {
        if 0 <= i < polygon.len() as int {
            let s = polygon_edge_orient_sign_spec(p, polygon, i);
            if s > 0 {
                assert(
                    exists|j: int|
                        0 <= j < polygon.len() as int
                            && polygon_edge_orient_sign_spec(p, polygon, j) > 0
                ) by {
                    assert(0 <= i < polygon.len() as int && polygon_edge_orient_sign_spec(p, polygon, i) > 0);
                }
                assert(polygon_has_positive_edge_sign_spec(p, polygon));
                assert(false);
            } else if s < 0 {
            } else {
                assert(s == 0);
                assert(
                    exists|j: int|
                        0 <= j < polygon.len() as int
                            && polygon_edge_orient_sign_spec(p, polygon, j) == 0
                ) by {
                    assert(0 <= i < polygon.len() as int && polygon_edge_orient_sign_spec(p, polygon, i) == 0);
                }
                assert(polygon_has_zero_edge_sign_spec(p, polygon));
                assert(false);
            }
        }
    }
}

proof fn lemma_edge_sign_consistent_iff_edge_halfspace(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
)
    ensures
        point_in_convex_polygon_edge_sign_consistent_spec(p, polygon)
            == point_in_convex_polygon_edge_halfspace_spec(p, polygon),
{
    if polygon.len() < 3 {
        assert(!point_in_convex_polygon_edge_sign_consistent_spec(p, polygon));
        assert(!point_in_convex_polygon_edge_halfspace_spec(p, polygon));
    } else {
        assert(point_in_convex_polygon_edge_sign_consistent_spec(p, polygon)
            == !(polygon_has_positive_edge_sign_spec(p, polygon) && polygon_has_negative_edge_sign_spec(
            p,
            polygon,
        )));
        assert(point_in_convex_polygon_edge_halfspace_spec(p, polygon)
            == (
            polygon_all_edge_sign_nonnegative_spec(p, polygon)
                || polygon_all_edge_sign_nonpositive_spec(p, polygon)
        ));

        if point_in_convex_polygon_edge_halfspace_spec(p, polygon) {
            if polygon_all_edge_sign_nonnegative_spec(p, polygon) {
                lemma_all_edge_nonnegative_implies_no_negative(p, polygon);
                assert(!polygon_has_negative_edge_sign_spec(p, polygon));
            } else {
                assert(polygon_all_edge_sign_nonpositive_spec(p, polygon));
                lemma_all_edge_nonpositive_implies_no_positive(p, polygon);
                assert(!polygon_has_positive_edge_sign_spec(p, polygon));
            }
            assert(!(polygon_has_positive_edge_sign_spec(p, polygon) && polygon_has_negative_edge_sign_spec(
                p,
                polygon,
            )));
            assert(point_in_convex_polygon_edge_sign_consistent_spec(p, polygon));
        }

        if point_in_convex_polygon_edge_sign_consistent_spec(p, polygon) {
            if polygon_has_positive_edge_sign_spec(p, polygon) {
                if polygon_has_negative_edge_sign_spec(p, polygon) {
                    assert(false);
                }
                lemma_no_negative_implies_all_edge_nonnegative(p, polygon);
                assert(polygon_all_edge_sign_nonnegative_spec(p, polygon));
            } else {
                lemma_no_positive_implies_all_edge_nonpositive(p, polygon);
                assert(polygon_all_edge_sign_nonpositive_spec(p, polygon));
            }
            assert(point_in_convex_polygon_edge_halfspace_spec(p, polygon));
        }
    }
}

proof fn lemma_edge_sign_strict_consistent_iff_strict_halfspace(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
)
    ensures
        point_strictly_in_convex_polygon_edge_sign_consistent_spec(p, polygon)
            == point_strictly_in_convex_polygon_edge_halfspace_spec(p, polygon),
{
    if polygon.len() < 3 {
        assert(!point_strictly_in_convex_polygon_edge_sign_consistent_spec(p, polygon));
        assert(!point_strictly_in_convex_polygon_edge_halfspace_spec(p, polygon));
    } else {
        assert(point_strictly_in_convex_polygon_edge_sign_consistent_spec(p, polygon)
            == (
            !(polygon_has_positive_edge_sign_spec(p, polygon) && polygon_has_negative_edge_sign_spec(p, polygon))
                && !polygon_has_zero_edge_sign_spec(p, polygon)
        ));
        assert(point_strictly_in_convex_polygon_edge_halfspace_spec(p, polygon)
            == (
            polygon_all_edge_sign_positive_spec(p, polygon)
                || polygon_all_edge_sign_negative_spec(p, polygon)
        ));

        if point_strictly_in_convex_polygon_edge_halfspace_spec(p, polygon) {
            if polygon_all_edge_sign_positive_spec(p, polygon) {
                lemma_all_edge_positive_implies_no_negative(p, polygon);
                lemma_all_edge_positive_implies_no_zero(p, polygon);
                assert(!polygon_has_negative_edge_sign_spec(p, polygon));
                assert(!polygon_has_zero_edge_sign_spec(p, polygon));
            } else {
                assert(polygon_all_edge_sign_negative_spec(p, polygon));
                lemma_all_edge_negative_implies_no_positive(p, polygon);
                lemma_all_edge_negative_implies_no_zero(p, polygon);
                assert(!polygon_has_positive_edge_sign_spec(p, polygon));
                assert(!polygon_has_zero_edge_sign_spec(p, polygon));
            }
            assert(point_strictly_in_convex_polygon_edge_sign_consistent_spec(p, polygon));
        }

        if point_strictly_in_convex_polygon_edge_sign_consistent_spec(p, polygon) {
            if polygon_has_positive_edge_sign_spec(p, polygon) {
                if polygon_has_negative_edge_sign_spec(p, polygon) {
                    assert(false);
                }
                lemma_no_negative_no_zero_implies_all_edge_positive(p, polygon);
                assert(polygon_all_edge_sign_positive_spec(p, polygon));
            } else {
                lemma_no_positive_no_zero_implies_all_edge_negative(p, polygon);
                assert(polygon_all_edge_sign_negative_spec(p, polygon));
            }
            assert(point_strictly_in_convex_polygon_edge_halfspace_spec(p, polygon));
        }
    }
}

proof fn lemma_signum_gt_zero_iff_eq_one(s: Scalar)
    ensures
        (s.signum() > 0) == (s.signum() == 1),
{
    Scalar::lemma_signum_cases(s);
    if s.signum() == 1 {
        assert(s.signum() > 0);
    } else if s.signum() == -1 {
        assert(!(s.signum() > 0));
    } else {
        assert(s.signum() == 0);
        assert(!(s.signum() > 0));
    }
}

proof fn lemma_signum_lt_zero_iff_eq_minus_one(s: Scalar)
    ensures
        (s.signum() < 0) == (s.signum() == -1),
{
    Scalar::lemma_signum_cases(s);
    if s.signum() == -1 {
        assert(s.signum() < 0);
    } else if s.signum() == 1 {
        assert(!(s.signum() < 0));
    } else {
        assert(s.signum() == 0);
        assert(!(s.signum() < 0));
    }
}

proof fn lemma_local_and_convex_edge_sign_equal(p: Point2, polygon: Seq<RuntimePoint2>, i: int)
    requires
        polygon.len() >= 3,
        0 <= i < polygon.len() as int,
    ensures
        polygon_edge_orient_sign_spec(p, polygon, i)
            == convex_polygon::polygon_edge_orient_sign_spec(p, polygon, i),
{
    assert(polygon_next_index_spec(polygon, i) == convex_polygon::polygon_next_index_spec(polygon, i));
}

proof fn lemma_local_positive_edge_predicate_equiv_convex(p: Point2, polygon: Seq<RuntimePoint2>, i: int)
    requires
        polygon.len() >= 3,
        0 <= i < polygon.len() as int,
    ensures
        (polygon_edge_orient_sign_spec(p, polygon, i) > 0)
            == (convex_polygon::polygon_edge_orient_sign_spec(p, polygon, i) == 1),
{
    let s = orient2d_spec(polygon[i]@, polygon[polygon_next_index_spec(polygon, i)]@, p);
    lemma_signum_gt_zero_iff_eq_one(s);
    assert(polygon_edge_orient_sign_spec(p, polygon, i) == s.signum());
    assert((polygon_edge_orient_sign_spec(p, polygon, i) > 0)
        == (polygon_edge_orient_sign_spec(p, polygon, i) == 1));
    lemma_local_and_convex_edge_sign_equal(p, polygon, i);
    assert((polygon_edge_orient_sign_spec(p, polygon, i) == 1)
        == (convex_polygon::polygon_edge_orient_sign_spec(p, polygon, i) == 1));
}

proof fn lemma_local_negative_edge_predicate_equiv_convex(p: Point2, polygon: Seq<RuntimePoint2>, i: int)
    requires
        polygon.len() >= 3,
        0 <= i < polygon.len() as int,
    ensures
        (polygon_edge_orient_sign_spec(p, polygon, i) < 0)
            == (convex_polygon::polygon_edge_orient_sign_spec(p, polygon, i) == -1),
{
    let s = orient2d_spec(polygon[i]@, polygon[polygon_next_index_spec(polygon, i)]@, p);
    lemma_signum_lt_zero_iff_eq_minus_one(s);
    assert(polygon_edge_orient_sign_spec(p, polygon, i) == s.signum());
    assert((polygon_edge_orient_sign_spec(p, polygon, i) < 0)
        == (polygon_edge_orient_sign_spec(p, polygon, i) == -1));
    lemma_local_and_convex_edge_sign_equal(p, polygon, i);
    assert((polygon_edge_orient_sign_spec(p, polygon, i) == -1)
        == (convex_polygon::polygon_edge_orient_sign_spec(p, polygon, i) == -1));
}

proof fn lemma_local_zero_edge_predicate_equiv_convex(p: Point2, polygon: Seq<RuntimePoint2>, i: int)
    requires
        polygon.len() >= 3,
        0 <= i < polygon.len() as int,
    ensures
        (polygon_edge_orient_sign_spec(p, polygon, i) == 0)
            == (convex_polygon::polygon_edge_orient_sign_spec(p, polygon, i) == 0),
{
    lemma_local_and_convex_edge_sign_equal(p, polygon, i);
}

proof fn lemma_local_and_convex_has_positive_edge_sign_equiv(p: Point2, polygon: Seq<RuntimePoint2>)
    requires
        polygon.len() >= 3,
    ensures
        polygon_has_positive_edge_sign_spec(p, polygon)
            == convex_polygon::polygon_has_positive_edge_sign_spec(p, polygon),
{
    if polygon_has_positive_edge_sign_spec(p, polygon) {
        let i = choose|i: int| 0 <= i < polygon.len() as int && polygon_edge_orient_sign_spec(p, polygon, i) > 0;
        lemma_local_positive_edge_predicate_equiv_convex(p, polygon, i);
        assert(convex_polygon::polygon_edge_orient_sign_spec(p, polygon, i) == 1);
        assert(convex_polygon::polygon_has_positive_edge_sign_spec(p, polygon));
    }
    if convex_polygon::polygon_has_positive_edge_sign_spec(p, polygon) {
        let i = choose|i: int|
            0 <= i < polygon.len() as int && convex_polygon::polygon_edge_orient_sign_spec(p, polygon, i) == 1;
        lemma_local_positive_edge_predicate_equiv_convex(p, polygon, i);
        assert(polygon_edge_orient_sign_spec(p, polygon, i) > 0);
        assert(polygon_has_positive_edge_sign_spec(p, polygon));
    }
}

proof fn lemma_local_and_convex_has_negative_edge_sign_equiv(p: Point2, polygon: Seq<RuntimePoint2>)
    requires
        polygon.len() >= 3,
    ensures
        polygon_has_negative_edge_sign_spec(p, polygon)
            == convex_polygon::polygon_has_negative_edge_sign_spec(p, polygon),
{
    if polygon_has_negative_edge_sign_spec(p, polygon) {
        let i = choose|i: int| 0 <= i < polygon.len() as int && polygon_edge_orient_sign_spec(p, polygon, i) < 0;
        lemma_local_negative_edge_predicate_equiv_convex(p, polygon, i);
        assert(convex_polygon::polygon_edge_orient_sign_spec(p, polygon, i) == -1);
        assert(convex_polygon::polygon_has_negative_edge_sign_spec(p, polygon));
    }
    if convex_polygon::polygon_has_negative_edge_sign_spec(p, polygon) {
        let i = choose|i: int|
            0 <= i < polygon.len() as int && convex_polygon::polygon_edge_orient_sign_spec(p, polygon, i) == -1;
        lemma_local_negative_edge_predicate_equiv_convex(p, polygon, i);
        assert(polygon_edge_orient_sign_spec(p, polygon, i) < 0);
        assert(polygon_has_negative_edge_sign_spec(p, polygon));
    }
}

proof fn lemma_local_and_convex_has_zero_edge_sign_equiv(p: Point2, polygon: Seq<RuntimePoint2>)
    requires
        polygon.len() >= 3,
    ensures
        polygon_has_zero_edge_sign_spec(p, polygon)
            == convex_polygon::polygon_has_zero_edge_sign_spec(p, polygon),
{
    if polygon_has_zero_edge_sign_spec(p, polygon) {
        let i = choose|i: int| 0 <= i < polygon.len() as int && polygon_edge_orient_sign_spec(p, polygon, i) == 0;
        lemma_local_zero_edge_predicate_equiv_convex(p, polygon, i);
        assert(convex_polygon::polygon_edge_orient_sign_spec(p, polygon, i) == 0);
        assert(convex_polygon::polygon_has_zero_edge_sign_spec(p, polygon));
    }
    if convex_polygon::polygon_has_zero_edge_sign_spec(p, polygon) {
        let i = choose|i: int|
            0 <= i < polygon.len() as int && convex_polygon::polygon_edge_orient_sign_spec(p, polygon, i) == 0;
        lemma_local_zero_edge_predicate_equiv_convex(p, polygon, i);
        assert(polygon_edge_orient_sign_spec(p, polygon, i) == 0);
        assert(polygon_has_zero_edge_sign_spec(p, polygon));
    }
}

proof fn lemma_local_and_convex_boundary_inclusive_spec_equiv(p: Point2, polygon: Seq<RuntimePoint2>)
    ensures
        point_in_convex_polygon_boundary_inclusive_spec(p, polygon)
            == convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(p, polygon),
{
    if polygon.len() < 3 {
        assert(!point_in_convex_polygon_boundary_inclusive_spec(p, polygon));
        assert(!convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(p, polygon));
    } else {
        lemma_local_and_convex_has_positive_edge_sign_equiv(p, polygon);
        lemma_local_and_convex_has_negative_edge_sign_equiv(p, polygon);
        assert(point_in_convex_polygon_boundary_inclusive_spec(p, polygon)
            == !(polygon_has_positive_edge_sign_spec(p, polygon) && polygon_has_negative_edge_sign_spec(p, polygon)));
        assert(convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(p, polygon)
            == !(convex_polygon::polygon_has_positive_edge_sign_spec(p, polygon)
                && convex_polygon::polygon_has_negative_edge_sign_spec(p, polygon)));
        assert(polygon_has_positive_edge_sign_spec(p, polygon)
            == convex_polygon::polygon_has_positive_edge_sign_spec(p, polygon));
        assert(polygon_has_negative_edge_sign_spec(p, polygon)
            == convex_polygon::polygon_has_negative_edge_sign_spec(p, polygon));
    }
}

proof fn lemma_local_and_convex_strict_spec_equiv(p: Point2, polygon: Seq<RuntimePoint2>)
    ensures
        point_strictly_in_convex_polygon_edge_sign_consistent_spec(p, polygon)
            == convex_polygon::point_strictly_in_convex_polygon_edge_sign_consistent_spec(p, polygon),
{
    if polygon.len() < 3 {
        assert(!point_strictly_in_convex_polygon_edge_sign_consistent_spec(p, polygon));
        assert(!convex_polygon::point_strictly_in_convex_polygon_edge_sign_consistent_spec(p, polygon));
    } else {
        lemma_local_and_convex_has_positive_edge_sign_equiv(p, polygon);
        lemma_local_and_convex_has_negative_edge_sign_equiv(p, polygon);
        lemma_local_and_convex_has_zero_edge_sign_equiv(p, polygon);
        assert(point_strictly_in_convex_polygon_edge_sign_consistent_spec(p, polygon)
            == (
            !(polygon_has_positive_edge_sign_spec(p, polygon) && polygon_has_negative_edge_sign_spec(p, polygon))
                && !polygon_has_zero_edge_sign_spec(p, polygon)
        ));
        assert(convex_polygon::point_strictly_in_convex_polygon_edge_sign_consistent_spec(p, polygon)
            == (
            !(convex_polygon::polygon_has_positive_edge_sign_spec(p, polygon)
                && convex_polygon::polygon_has_negative_edge_sign_spec(p, polygon))
                && !convex_polygon::polygon_has_zero_edge_sign_spec(p, polygon)
        ));
        assert(polygon_has_positive_edge_sign_spec(p, polygon)
            == convex_polygon::polygon_has_positive_edge_sign_spec(p, polygon));
        assert(polygon_has_negative_edge_sign_spec(p, polygon)
            == convex_polygon::polygon_has_negative_edge_sign_spec(p, polygon));
        assert(polygon_has_zero_edge_sign_spec(p, polygon)
            == convex_polygon::polygon_has_zero_edge_sign_spec(p, polygon));
    }
}

#[allow(dead_code)]
pub fn runtime_point_in_convex_polygon_matches_spec(
    p: &RuntimePoint2,
    polygon: &[RuntimePoint2],
) -> (out: bool)
    requires
        p.witness_wf_spec(),
        forall|j: int| 0 <= j < polygon@.len() ==> polygon@[j].witness_wf_spec(),
    ensures
        out == point_in_convex_polygon_edge_sign_consistent_spec(p@, polygon@),
        out == point_in_convex_polygon_boundary_inclusive_spec(p@, polygon@),
{
    let out = convex_polygon::point_in_convex_polygon_2d(p, polygon);
    proof {
        lemma_local_and_convex_boundary_inclusive_spec_equiv(p@, polygon@);
        assert(out == convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(p@, polygon@));
        assert(out == point_in_convex_polygon_boundary_inclusive_spec(p@, polygon@));
        assert(point_in_convex_polygon_boundary_inclusive_spec(p@, polygon@)
            == point_in_convex_polygon_edge_sign_consistent_spec(p@, polygon@));
    }
    out
}

#[allow(dead_code)]
pub fn runtime_point_in_convex_polygon_short_polygon_false(
    p: &RuntimePoint2,
    polygon: &[RuntimePoint2],
) -> (out: bool)
    requires
        p.witness_wf_spec(),
        forall|j: int| 0 <= j < polygon@.len() ==> polygon@[j].witness_wf_spec(),
        polygon@.len() < 3,
    ensures
        !out,
{
    let out = convex_polygon::point_in_convex_polygon_2d(p, polygon);
    proof {
        lemma_local_and_convex_boundary_inclusive_spec_equiv(p@, polygon@);
        assert(out == convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(p@, polygon@));
        assert(out == point_in_convex_polygon_boundary_inclusive_spec(p@, polygon@));
        if out {
            assert(point_in_convex_polygon_boundary_inclusive_spec(p@, polygon@));
            assert(polygon@.len() >= 3);
            assert(false);
        }
    }
    out
}

#[allow(dead_code)]
pub fn runtime_point_in_convex_polygon_true_implies_no_mixed_signs(
    p: &RuntimePoint2,
    polygon: &[RuntimePoint2],
) -> (out: bool)
    requires
        p.witness_wf_spec(),
        forall|j: int| 0 <= j < polygon@.len() ==> polygon@[j].witness_wf_spec(),
    ensures
        out == point_in_convex_polygon_boundary_inclusive_spec(p@, polygon@),
        out ==> !(polygon_has_positive_edge_sign_spec(p@, polygon@) && polygon_has_negative_edge_sign_spec(
            p@,
            polygon@,
        )),
{
    let out = convex_polygon::point_in_convex_polygon_2d(p, polygon);
    proof {
        lemma_local_and_convex_boundary_inclusive_spec_equiv(p@, polygon@);
        assert(out == convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(p@, polygon@));
        assert(out == point_in_convex_polygon_boundary_inclusive_spec(p@, polygon@));
        if out {
            assert(point_in_convex_polygon_boundary_inclusive_spec(p@, polygon@));
            assert(!(polygon_has_positive_edge_sign_spec(p@, polygon@) && polygon_has_negative_edge_sign_spec(
                p@,
                polygon@,
            )));
        }
    }
    out
}

#[allow(dead_code)]
pub fn runtime_point_strictly_in_convex_polygon_matches_spec(
    p: &RuntimePoint2,
    polygon: &[RuntimePoint2],
) -> (out: bool)
    requires
        p.witness_wf_spec(),
        forall|j: int| 0 <= j < polygon@.len() ==> polygon@[j].witness_wf_spec(),
    ensures
        out == point_strictly_in_convex_polygon_edge_sign_consistent_spec(p@, polygon@),
{
    let out = convex_polygon::point_strictly_in_convex_polygon_2d(p, polygon);
    proof {
        lemma_local_and_convex_strict_spec_equiv(p@, polygon@);
        assert(out == convex_polygon::point_strictly_in_convex_polygon_edge_sign_consistent_spec(p@, polygon@));
        assert(out == point_strictly_in_convex_polygon_edge_sign_consistent_spec(p@, polygon@));
    }
    out
}

#[allow(dead_code)]
pub fn runtime_point_in_convex_polygon_convex_geometric_iff(
    p: &RuntimePoint2,
    polygon: &[RuntimePoint2],
) -> (out: bool)
    requires
        p.witness_wf_spec(),
        forall|j: int| 0 <= j < polygon@.len() ==> polygon@[j].witness_wf_spec(),
        polygon_convex_consistent_order_spec(polygon@),
    ensures
        out == point_in_convex_polygon_geometric_spec(p@, polygon@),
{
    let out = convex_polygon::point_in_convex_polygon_2d(p, polygon);
    proof {
        lemma_local_and_convex_boundary_inclusive_spec_equiv(p@, polygon@);
        assert(out == convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(p@, polygon@));
        assert(out == point_in_convex_polygon_boundary_inclusive_spec(p@, polygon@));
        lemma_edge_sign_consistent_iff_edge_halfspace(p@, polygon@);
        assert(out == point_in_convex_polygon_boundary_inclusive_spec(p@, polygon@));
        assert(point_in_convex_polygon_boundary_inclusive_spec(p@, polygon@)
            == point_in_convex_polygon_edge_sign_consistent_spec(p@, polygon@));
        assert(point_in_convex_polygon_edge_sign_consistent_spec(p@, polygon@)
            == point_in_convex_polygon_edge_halfspace_spec(p@, polygon@));
        assert(point_in_convex_polygon_geometric_spec(p@, polygon@)
            == (polygon_convex_consistent_order_spec(polygon@)
                && point_in_convex_polygon_edge_halfspace_spec(p@, polygon@)));
        assert(polygon_convex_consistent_order_spec(polygon@));
        assert(point_in_convex_polygon_geometric_spec(p@, polygon@)
            == point_in_convex_polygon_edge_halfspace_spec(p@, polygon@));
        assert(out == point_in_convex_polygon_geometric_spec(p@, polygon@));
    }
    out
}

#[allow(dead_code)]
pub fn runtime_point_strictly_in_convex_polygon_convex_geometric_iff(
    p: &RuntimePoint2,
    polygon: &[RuntimePoint2],
) -> (out: bool)
    requires
        p.witness_wf_spec(),
        forall|j: int| 0 <= j < polygon@.len() ==> polygon@[j].witness_wf_spec(),
        polygon_strict_convex_consistent_order_spec(polygon@),
    ensures
        out == point_strictly_in_convex_polygon_geometric_spec(p@, polygon@),
{
    let out = convex_polygon::point_strictly_in_convex_polygon_2d(p, polygon);
    proof {
        lemma_local_and_convex_strict_spec_equiv(p@, polygon@);
        assert(out == convex_polygon::point_strictly_in_convex_polygon_edge_sign_consistent_spec(p@, polygon@));
        assert(out == point_strictly_in_convex_polygon_edge_sign_consistent_spec(p@, polygon@));
        lemma_edge_sign_strict_consistent_iff_strict_halfspace(p@, polygon@);
        assert(out == point_strictly_in_convex_polygon_edge_sign_consistent_spec(p@, polygon@));
        assert(point_strictly_in_convex_polygon_edge_sign_consistent_spec(p@, polygon@)
            == point_strictly_in_convex_polygon_edge_halfspace_spec(p@, polygon@));
        assert(point_strictly_in_convex_polygon_geometric_spec(p@, polygon@)
            == (
            polygon_strict_convex_consistent_order_spec(polygon@)
                && point_strictly_in_convex_polygon_edge_halfspace_spec(p@, polygon@)
        ));
        assert(polygon_strict_convex_consistent_order_spec(polygon@));
        assert(point_strictly_in_convex_polygon_geometric_spec(p@, polygon@)
            == point_strictly_in_convex_polygon_edge_halfspace_spec(p@, polygon@));
        assert(out == point_strictly_in_convex_polygon_geometric_spec(p@, polygon@));
    }
    out
}

} // verus!
