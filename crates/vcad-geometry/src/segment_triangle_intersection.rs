use crate::convex_polygon::point_in_convex_polygon_2d;
use crate::sidedness::segment_plane_intersection_point_strict;
use vcad_math::runtime_point2::RuntimePoint2;
use vcad_math::runtime_point3::RuntimePoint3;
#[cfg(verus_keep_ghost)]
use vcad_math::runtime_scalar::RuntimeSign;
use vcad_math::runtime_vec3::RuntimeVec3;

#[derive(Clone, Copy)]
enum ProjectionAxis {
    DropX,
    DropY,
    DropZ,
}

#[cfg(not(verus_keep_ghost))]
fn projection_axis_from_normal(normal: &RuntimeVec3) -> Option<ProjectionAxis> {
    if normal.x().signum_i8() != 0 {
        Some(ProjectionAxis::DropX)
    } else if normal.y().signum_i8() != 0 {
        Some(ProjectionAxis::DropY)
    } else if normal.z().signum_i8() != 0 {
        Some(ProjectionAxis::DropZ)
    } else {
        None
    }
}

#[cfg(verus_keep_ghost)]
fn projection_axis_from_normal(normal: &RuntimeVec3) -> Option<ProjectionAxis> {
    if normal.x().sign_witness != RuntimeSign::Zero {
        Some(ProjectionAxis::DropX)
    } else if normal.y().sign_witness != RuntimeSign::Zero {
        Some(ProjectionAxis::DropY)
    } else if normal.z().sign_witness != RuntimeSign::Zero {
        Some(ProjectionAxis::DropZ)
    } else {
        None
    }
}

fn project_point3_to_2d(point: &RuntimePoint3, axis: ProjectionAxis) -> RuntimePoint2 {
    match axis {
        ProjectionAxis::DropX => RuntimePoint2::new(point.y.clone(), point.z.clone()),
        ProjectionAxis::DropY => RuntimePoint2::new(point.x.clone(), point.z.clone()),
        ProjectionAxis::DropZ => RuntimePoint2::new(point.x.clone(), point.y.clone()),
    }
}

fn point_in_triangle_boundary_on_supporting_plane(
    point: &RuntimePoint3,
    tri_a: &RuntimePoint3,
    tri_b: &RuntimePoint3,
    tri_c: &RuntimePoint3,
) -> bool {
    let ab = tri_b.sub(tri_a);
    let ac = tri_c.sub(tri_a);
    let normal = ab.cross(&ac);
    let axis = match projection_axis_from_normal(&normal) {
        Some(axis) => axis,
        None => return false,
    };

    let tri_2d = vec![
        project_point3_to_2d(tri_a, axis),
        project_point3_to_2d(tri_b, axis),
        project_point3_to_2d(tri_c, axis),
    ];
    let point_2d = project_point3_to_2d(point, axis);

    point_in_convex_polygon_2d(&point_2d, &tri_2d)
}

/// Strict segment-triangle intersection witness.
///
/// Returns `Some(p)` exactly when the segment `[seg_start, seg_end]` crosses
/// triangle `(tri_a, tri_b, tri_c)`'s supporting plane strictly and the
/// crossing point lies in the triangle boundary-inclusive region.
pub fn segment_triangle_intersection_point_strict(
    seg_start: &RuntimePoint3,
    seg_end: &RuntimePoint3,
    tri_a: &RuntimePoint3,
    tri_b: &RuntimePoint3,
    tri_c: &RuntimePoint3,
) -> Option<RuntimePoint3> {
    let p = segment_plane_intersection_point_strict(seg_start, seg_end, tri_a, tri_b, tri_c)?;
    if point_in_triangle_boundary_on_supporting_plane(&p, tri_a, tri_b, tri_c) {
        Some(p)
    } else {
        None
    }
}

/// Boolean wrapper for strict segment-triangle intersection.
pub fn segment_triangle_intersects_strict(
    seg_start: &RuntimePoint3,
    seg_end: &RuntimePoint3,
    tri_a: &RuntimePoint3,
    tri_b: &RuntimePoint3,
    tri_c: &RuntimePoint3,
) -> bool {
    segment_triangle_intersection_point_strict(seg_start, seg_end, tri_a, tri_b, tri_c).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn segment_triangle_strict_crossing_inside_returns_witness() {
        let a = RuntimePoint3::from_ints(0, 0, 0);
        let b = RuntimePoint3::from_ints(4, 0, 0);
        let c = RuntimePoint3::from_ints(0, 4, 0);
        let s0 = RuntimePoint3::from_ints(1, 1, 2);
        let s1 = RuntimePoint3::from_ints(1, 1, -2);

        let p = segment_triangle_intersection_point_strict(&s0, &s1, &a, &b, &c)
            .expect("strict segment-triangle crossing should yield a witness");
        assert_eq!(p, RuntimePoint3::from_ints(1, 1, 0));
        assert!(segment_triangle_intersects_strict(&s0, &s1, &a, &b, &c));
    }

    #[test]
    fn segment_triangle_strict_crossing_inside_reversed_winding_returns_witness() {
        let a = RuntimePoint3::from_ints(0, 0, 0);
        let b = RuntimePoint3::from_ints(0, 4, 0);
        let c = RuntimePoint3::from_ints(4, 0, 0);
        let s0 = RuntimePoint3::from_ints(1, 1, 2);
        let s1 = RuntimePoint3::from_ints(1, 1, -2);

        let p = segment_triangle_intersection_point_strict(&s0, &s1, &a, &b, &c)
            .expect("strict segment-triangle crossing should be winding-invariant");
        assert_eq!(p, RuntimePoint3::from_ints(1, 1, 0));
        assert!(segment_triangle_intersects_strict(&s0, &s1, &a, &b, &c));
    }

    #[test]
    fn segment_triangle_strict_crossing_outside_triangle_returns_none() {
        let a = RuntimePoint3::from_ints(0, 0, 0);
        let b = RuntimePoint3::from_ints(4, 0, 0);
        let c = RuntimePoint3::from_ints(0, 4, 0);
        let s0 = RuntimePoint3::from_ints(3, 3, 1);
        let s1 = RuntimePoint3::from_ints(3, 3, -1);

        assert!(segment_triangle_intersection_point_strict(&s0, &s1, &a, &b, &c).is_none());
        assert!(!segment_triangle_intersects_strict(&s0, &s1, &a, &b, &c));
    }

    #[test]
    fn segment_triangle_endpoint_on_plane_is_not_strict_intersection() {
        let a = RuntimePoint3::from_ints(0, 0, 0);
        let b = RuntimePoint3::from_ints(4, 0, 0);
        let c = RuntimePoint3::from_ints(0, 4, 0);
        let s0 = RuntimePoint3::from_ints(1, 1, 0);
        let s1 = RuntimePoint3::from_ints(1, 1, 2);

        assert!(segment_triangle_intersection_point_strict(&s0, &s1, &a, &b, &c).is_none());
        assert!(!segment_triangle_intersects_strict(&s0, &s1, &a, &b, &c));
    }

    #[test]
    fn segment_triangle_coplanar_segment_is_not_strict_intersection() {
        let a = RuntimePoint3::from_ints(0, 0, 0);
        let b = RuntimePoint3::from_ints(4, 0, 0);
        let c = RuntimePoint3::from_ints(0, 4, 0);
        let s0 = RuntimePoint3::from_ints(1, 1, 0);
        let s1 = RuntimePoint3::from_ints(2, 1, 0);

        assert!(segment_triangle_intersection_point_strict(&s0, &s1, &a, &b, &c).is_none());
        assert!(!segment_triangle_intersects_strict(&s0, &s1, &a, &b, &c));
    }

    #[test]
    fn segment_triangle_degenerate_triangle_returns_none() {
        let a = RuntimePoint3::from_ints(0, 0, 0);
        let b = RuntimePoint3::from_ints(1, 1, 0);
        let c = RuntimePoint3::from_ints(2, 2, 0);
        let s0 = RuntimePoint3::from_ints(1, 0, 1);
        let s1 = RuntimePoint3::from_ints(1, 0, -1);

        assert!(segment_triangle_intersection_point_strict(&s0, &s1, &a, &b, &c).is_none());
        assert!(!segment_triangle_intersects_strict(&s0, &s1, &a, &b, &c));
    }
}
