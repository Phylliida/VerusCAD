use crate::convex_polygon::point_in_convex_polygon_2d;
use crate::segment_intersection::{segment_intersection_kind_2d, SegmentIntersection2dKind};
use vcad_math::runtime_point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use crate::{convex_polygon, segment_intersection};
#[cfg(verus_keep_ghost)]
use vcad_math::point2::Point2;
#[cfg(verus_keep_ghost)]
use vcad_math::runtime_wf as wf;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {

pub open spec fn polygon_next_index_spec(polygon: Seq<RuntimePoint2>, i: int) -> int
    recommends
        polygon.len() > 0,
        0 <= i < polygon.len() as int,
{
    if i + 1 < polygon.len() as int { i + 1 } else { 0 }
}

pub open spec fn segment_hits_polygon_edge_spec(
    seg_start: Point2,
    seg_end: Point2,
    polygon: Seq<RuntimePoint2>,
    i: int,
) -> bool
    recommends
        polygon.len() >= 3,
        0 <= i < polygon.len() as int,
{
    let j = polygon_next_index_spec(polygon, i);
    !(segment_intersection::segment_intersection_kind_spec(seg_start, seg_end, polygon[i]@, polygon[j]@) is Disjoint)
}

pub open spec fn segment_prefix_hits_polygon_edge_spec(
    seg_start: Point2,
    seg_end: Point2,
    polygon: Seq<RuntimePoint2>,
    upto: int,
) -> bool
    recommends
        polygon.len() >= 3,
        0 <= upto <= polygon.len() as int,
{
    exists|i: int| 0 <= i < upto && segment_hits_polygon_edge_spec(seg_start, seg_end, polygon, i)
}

pub open spec fn segment_hits_some_polygon_edge_spec(
    seg_start: Point2,
    seg_end: Point2,
    polygon: Seq<RuntimePoint2>,
) -> bool
    recommends
        polygon.len() >= 3,
{
    segment_prefix_hits_polygon_edge_spec(seg_start, seg_end, polygon, polygon.len() as int)
}

/// Exact model of `segment_overlaps_convex_polygon_2d`:
/// overlap holds iff one segment endpoint is inside the convex polygon (boundary-inclusive)
/// or the segment intersects at least one polygon edge in a non-disjoint classifier mode.
pub open spec fn segment_overlaps_convex_polygon_composed_spec(
    seg_start: Point2,
    seg_end: Point2,
    polygon: Seq<RuntimePoint2>,
) -> bool {
    &&& polygon.len() >= 3
    &&& (
        convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(seg_start, polygon)
            || convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(seg_end, polygon)
            || segment_hits_some_polygon_edge_spec(seg_start, seg_end, polygon)
    )
}

proof fn lemma_segment_prefix_hits_polygon_edge_step(
    seg_start: Point2,
    seg_end: Point2,
    polygon: Seq<RuntimePoint2>,
    i: int,
)
    requires
        polygon.len() >= 3,
        0 <= i < polygon.len() as int,
    ensures
        segment_prefix_hits_polygon_edge_spec(seg_start, seg_end, polygon, i + 1)
            == (segment_prefix_hits_polygon_edge_spec(seg_start, seg_end, polygon, i)
                || segment_hits_polygon_edge_spec(seg_start, seg_end, polygon, i)),
{
    if segment_prefix_hits_polygon_edge_spec(seg_start, seg_end, polygon, i + 1) {
        let j = choose|j: int|
            0 <= j < i + 1 && segment_hits_polygon_edge_spec(seg_start, seg_end, polygon, j);
        if j < i {
            assert(segment_prefix_hits_polygon_edge_spec(seg_start, seg_end, polygon, i));
        } else {
            assert(j == i);
            assert(segment_hits_polygon_edge_spec(seg_start, seg_end, polygon, i));
        }
    }

    if segment_prefix_hits_polygon_edge_spec(seg_start, seg_end, polygon, i)
        || segment_hits_polygon_edge_spec(seg_start, seg_end, polygon, i)
    {
        if segment_prefix_hits_polygon_edge_spec(seg_start, seg_end, polygon, i) {
            let j = choose|j: int|
                0 <= j < i && segment_hits_polygon_edge_spec(seg_start, seg_end, polygon, j);
            assert(0 <= j < i + 1);
            assert(segment_prefix_hits_polygon_edge_spec(seg_start, seg_end, polygon, i + 1));
        } else {
            assert(0 <= i < i + 1);
            assert(segment_prefix_hits_polygon_edge_spec(seg_start, seg_end, polygon, i + 1));
        }
    }
}

} // verus!

/// Returns whether a closed segment intersects a closed convex polygon in 2D.
///
/// This is the composed predicate used by coplanar segment-vs-face checks after
/// 3D points are projected onto a dominant axis plane.
#[cfg(not(verus_keep_ghost))]
pub fn segment_overlaps_convex_polygon_2d(
    seg_start: &RuntimePoint2,
    seg_end: &RuntimePoint2,
    polygon: &[RuntimePoint2],
) -> bool {
    if polygon.len() < 3 {
        return false;
    }

    if point_in_convex_polygon_2d(seg_start, polygon) || point_in_convex_polygon_2d(seg_end, polygon) {
        return true;
    }

    for i in 0..polygon.len() {
        let a = &polygon[i];
        let b = &polygon[(i + 1) % polygon.len()];
        let kind = segment_intersection_kind_2d(seg_start, seg_end, a, b);
        match kind {
            SegmentIntersection2dKind::Disjoint => {}
            SegmentIntersection2dKind::Proper
            | SegmentIntersection2dKind::EndpointTouch
            | SegmentIntersection2dKind::CollinearOverlap => return true,
        }
    }

    false
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn segment_overlaps_convex_polygon_2d(
    seg_start: &RuntimePoint2,
    seg_end: &RuntimePoint2,
    polygon: &[RuntimePoint2],
) -> (out: bool)
    requires
        wf::point2_wf2_spec(seg_start, seg_end),
        convex_polygon::point2_seq_wf_spec(polygon@),
    ensures
        out == segment_overlaps_convex_polygon_composed_spec(seg_start@, seg_end@, polygon@),
{
    if polygon.len() < 3 {
        proof {
            assert(!(polygon@.len() >= 3));
            assert(!segment_overlaps_convex_polygon_composed_spec(seg_start@, seg_end@, polygon@));
        }
        return false;
    }

    let start_inside = point_in_convex_polygon_2d(seg_start, polygon);
    let end_inside = point_in_convex_polygon_2d(seg_end, polygon);

    if start_inside || end_inside {
        proof {
            assert(start_inside
                == convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(seg_start@, polygon@));
            assert(end_inside
                == convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(seg_end@, polygon@));
            assert(polygon@.len() >= 3);
            assert(segment_overlaps_convex_polygon_composed_spec(seg_start@, seg_end@, polygon@));
        }
        return true;
    }

    let n = polygon.len();
    let mut i: usize = 0;
    let mut saw_edge_hit = false;
    while i < n
        invariant
            n == polygon.len(),
            n >= 3,
            0 <= i <= n,
            wf::point2_wf2_spec(seg_start, seg_end),
            convex_polygon::point2_seq_wf_spec(polygon@),
            start_inside == convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(seg_start@, polygon@),
            end_inside == convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(seg_end@, polygon@),
            !start_inside,
            !end_inside,
            saw_edge_hit == segment_prefix_hits_polygon_edge_spec(seg_start@, seg_end@, polygon@, i as int),
        decreases n as int - i as int,
    {
        let a = &polygon[i];
        let next = if i + 1 < n { i + 1 } else { 0 };
        let b = &polygon[next];
        let kind = segment_intersection_kind_2d(seg_start, seg_end, a, b);
        let edge_hit = match kind {
            SegmentIntersection2dKind::Disjoint => false,
            SegmentIntersection2dKind::Proper
            | SegmentIntersection2dKind::EndpointTouch
            | SegmentIntersection2dKind::CollinearOverlap => true,
        };

        let prev_i = i;
        let new_saw = saw_edge_hit || edge_hit;
        proof {
            let idx = prev_i as int;
            assert(0 <= idx < n as int);
            assert(a@ == polygon@[idx]@);
            if prev_i + 1 < n {
                assert(next == prev_i + 1);
                assert(b@ == polygon@[(idx + 1)]@);
                assert(polygon_next_index_spec(polygon@, idx) == idx + 1);
            } else {
                assert(prev_i + 1 == n);
                assert(next == 0);
                assert(b@ == polygon@[0]@);
                assert(polygon_next_index_spec(polygon@, idx) == 0);
            }

            assert(kind@ == segment_intersection::segment_intersection_kind_spec(seg_start@, seg_end@, a@, b@));
            segment_intersection::lemma_segment_intersection_kind_spec_exhaustive(seg_start@, seg_end@, a@, b@);
            match kind {
                SegmentIntersection2dKind::Disjoint => {
                    assert(kind@ is Disjoint);
                    assert(!edge_hit);
                    assert(!segment_hits_polygon_edge_spec(seg_start@, seg_end@, polygon@, idx));
                }
                SegmentIntersection2dKind::Proper => {
                    assert(kind@ is Proper);
                    assert(edge_hit);
                    assert(segment_hits_polygon_edge_spec(seg_start@, seg_end@, polygon@, idx));
                }
                SegmentIntersection2dKind::EndpointTouch => {
                    assert(kind@ is EndpointTouch);
                    assert(edge_hit);
                    assert(segment_hits_polygon_edge_spec(seg_start@, seg_end@, polygon@, idx));
                }
                SegmentIntersection2dKind::CollinearOverlap => {
                    assert(kind@ is CollinearOverlap);
                    assert(edge_hit);
                    assert(segment_hits_polygon_edge_spec(seg_start@, seg_end@, polygon@, idx));
                }
            }

            lemma_segment_prefix_hits_polygon_edge_step(seg_start@, seg_end@, polygon@, idx);
            assert(new_saw
                == (
                segment_prefix_hits_polygon_edge_spec(seg_start@, seg_end@, polygon@, idx)
                    || segment_hits_polygon_edge_spec(seg_start@, seg_end@, polygon@, idx)
            ));
            assert(new_saw == segment_prefix_hits_polygon_edge_spec(seg_start@, seg_end@, polygon@, idx + 1));
        }
        saw_edge_hit = new_saw;
        i = prev_i + 1;
    }

    proof {
        assert(i == n);
        assert(saw_edge_hit == segment_prefix_hits_polygon_edge_spec(seg_start@, seg_end@, polygon@, n as int));
        assert(n as int == polygon@.len());
        assert(saw_edge_hit == segment_hits_some_polygon_edge_spec(seg_start@, seg_end@, polygon@));
        assert(!start_inside);
        assert(!end_inside);
        assert(!convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(seg_start@, polygon@));
        assert(!convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(seg_end@, polygon@));
        assert(segment_overlaps_convex_polygon_composed_spec(seg_start@, seg_end@, polygon@)
            == (
            polygon@.len() >= 3
                && (
                convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(seg_start@, polygon@)
                    || convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(seg_end@, polygon@)
                    || segment_hits_some_polygon_edge_spec(seg_start@, seg_end@, polygon@)
            )
        ));
        assert(saw_edge_hit == segment_overlaps_convex_polygon_composed_spec(seg_start@, seg_end@, polygon@));
    }
    saw_edge_hit
}
} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    fn unit_square() -> Vec<RuntimePoint2> {
        vec![
            RuntimePoint2::from_ints(0, 0),
            RuntimePoint2::from_ints(4, 0),
            RuntimePoint2::from_ints(4, 4),
            RuntimePoint2::from_ints(0, 4),
        ]
    }

    #[test]
    fn segment_overlap_short_polygon_false() {
        let seg_start = RuntimePoint2::from_ints(0, 0);
        let seg_end = RuntimePoint2::from_ints(1, 1);
        let poly = vec![RuntimePoint2::from_ints(0, 0), RuntimePoint2::from_ints(1, 0)];
        assert!(!segment_overlaps_convex_polygon_2d(&seg_start, &seg_end, &poly));
    }

    #[test]
    fn segment_overlap_endpoint_inside_polygon() {
        let seg_start = RuntimePoint2::from_ints(2, 2);
        let seg_end = RuntimePoint2::from_ints(6, 2);
        let poly = unit_square();
        assert!(segment_overlaps_convex_polygon_2d(&seg_start, &seg_end, &poly));
    }

    #[test]
    fn segment_overlap_proper_edge_crossing() {
        let seg_start = RuntimePoint2::from_ints(-1, 2);
        let seg_end = RuntimePoint2::from_ints(5, 2);
        let poly = unit_square();
        assert!(segment_overlaps_convex_polygon_2d(&seg_start, &seg_end, &poly));
    }

    #[test]
    fn segment_overlap_endpoint_touching_polygon_vertex() {
        let seg_start = RuntimePoint2::from_ints(-2, 0);
        let seg_end = RuntimePoint2::from_ints(0, 0);
        let poly = unit_square();
        assert!(segment_overlaps_convex_polygon_2d(&seg_start, &seg_end, &poly));
    }

    #[test]
    fn segment_overlap_collinear_with_polygon_edge() {
        let seg_start = RuntimePoint2::from_ints(1, 0);
        let seg_end = RuntimePoint2::from_ints(6, 0);
        let poly = unit_square();
        assert!(segment_overlaps_convex_polygon_2d(&seg_start, &seg_end, &poly));
    }

    #[test]
    fn segment_overlap_disjoint_from_polygon() {
        let seg_start = RuntimePoint2::from_ints(5, 5);
        let seg_end = RuntimePoint2::from_ints(7, 7);
        let poly = unit_square();
        assert!(!segment_overlaps_convex_polygon_2d(&seg_start, &seg_end, &poly));
    }
}
