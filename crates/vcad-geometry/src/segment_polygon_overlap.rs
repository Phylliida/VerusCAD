use crate::convex_polygon::point_in_convex_polygon_2d;
use crate::segment_intersection::{segment_intersection_kind_2d, SegmentIntersection2dKind};
use vcad_math::runtime_point2::RuntimePoint2;

/// Returns whether a closed segment intersects a closed convex polygon in 2D.
///
/// This is the composed predicate used by coplanar segment-vs-face checks after
/// 3D points are projected onto a dominant axis plane.
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
