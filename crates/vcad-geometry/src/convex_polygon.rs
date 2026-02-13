use crate::orientation_predicates::orient2d_sign;
use vcad_math::runtime_point2::RuntimePoint2;

/// Returns true when `p` is inside or on the boundary of a convex polygon.
///
/// Precondition (not enforced): `polygon` is convex and vertices are ordered
/// consistently (all clockwise or all counter-clockwise).
pub fn point_in_convex_polygon_2d(p: &RuntimePoint2, polygon: &[RuntimePoint2]) -> bool {
    if polygon.len() < 3 {
        return false;
    }

    let mut saw_pos = false;
    let mut saw_neg = false;

    for i in 0..polygon.len() {
        let a = &polygon[i];
        let b = &polygon[(i + 1) % polygon.len()];
        let s = orient2d_sign(a, b, p);
        if s > 0 {
            saw_pos = true;
        } else if s < 0 {
            saw_neg = true;
        }
        if saw_pos && saw_neg {
            return false;
        }
    }

    true
}

/// Returns true when `p` is strictly inside a convex polygon.
///
/// Points on polygon edges/vertices are excluded.
///
/// Precondition (not enforced): `polygon` is convex and vertices are ordered
/// consistently (all clockwise or all counter-clockwise).
pub fn point_strictly_in_convex_polygon_2d(p: &RuntimePoint2, polygon: &[RuntimePoint2]) -> bool {
    if polygon.len() < 3 {
        return false;
    }

    let mut saw_pos = false;
    let mut saw_neg = false;

    for i in 0..polygon.len() {
        let a = &polygon[i];
        let b = &polygon[(i + 1) % polygon.len()];
        let s = orient2d_sign(a, b, p);
        if s == 0 {
            return false;
        } else if s > 0 {
            saw_pos = true;
        } else {
            saw_neg = true;
        }
        if saw_pos && saw_neg {
            return false;
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn point_inside_triangle() {
        let poly = vec![
            RuntimePoint2::from_ints(0, 0),
            RuntimePoint2::from_ints(2, 0),
            RuntimePoint2::from_ints(0, 2),
        ];
        let p = RuntimePoint2::from_ints(1, 1);
        assert!(point_in_convex_polygon_2d(&p, &poly));
    }

    #[test]
    fn point_outside_triangle() {
        let poly = vec![
            RuntimePoint2::from_ints(0, 0),
            RuntimePoint2::from_ints(2, 0),
            RuntimePoint2::from_ints(0, 2),
        ];
        let p = RuntimePoint2::from_ints(2, 2);
        assert!(!point_in_convex_polygon_2d(&p, &poly));
    }

    #[test]
    fn point_strictly_inside_triangle() {
        let poly = vec![
            RuntimePoint2::from_ints(0, 0),
            RuntimePoint2::from_ints(3, 0),
            RuntimePoint2::from_ints(0, 3),
        ];
        let p = RuntimePoint2::from_ints(1, 1);
        assert!(point_strictly_in_convex_polygon_2d(&p, &poly));
    }

    #[test]
    fn point_on_triangle_edge_not_strict() {
        let poly = vec![
            RuntimePoint2::from_ints(0, 0),
            RuntimePoint2::from_ints(2, 0),
            RuntimePoint2::from_ints(0, 2),
        ];
        let p = RuntimePoint2::from_ints(1, 0);
        assert!(point_in_convex_polygon_2d(&p, &poly));
        assert!(!point_strictly_in_convex_polygon_2d(&p, &poly));
    }

    #[test]
    fn point_outside_triangle_not_strict() {
        let poly = vec![
            RuntimePoint2::from_ints(0, 0),
            RuntimePoint2::from_ints(2, 0),
            RuntimePoint2::from_ints(0, 2),
        ];
        let p = RuntimePoint2::from_ints(2, 2);
        assert!(!point_strictly_in_convex_polygon_2d(&p, &poly));
    }
}
