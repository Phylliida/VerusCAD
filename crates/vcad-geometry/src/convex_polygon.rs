use crate::orientation_predicates::orient2d_sign;
use vcad_math::runtime_point2::RuntimePoint2;
#[cfg(verus_keep_ghost)]
use vcad_math::orientation::orient2d_spec;
#[cfg(verus_keep_ghost)]
use vcad_math::point2::Point2;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::View;

#[cfg(verus_keep_ghost)]
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

pub open spec fn polygon_prefix_has_positive_edge_sign_spec(p: Point2, polygon: Seq<RuntimePoint2>, upto: int) -> bool
    recommends
        polygon.len() >= 3,
        0 <= upto <= polygon.len() as int,
{
    exists|i: int| 0 <= i < upto && polygon_edge_orient_sign_spec(p, polygon, i) == 1
}

pub open spec fn polygon_prefix_has_negative_edge_sign_spec(p: Point2, polygon: Seq<RuntimePoint2>, upto: int) -> bool
    recommends
        polygon.len() >= 3,
        0 <= upto <= polygon.len() as int,
{
    exists|i: int| 0 <= i < upto && polygon_edge_orient_sign_spec(p, polygon, i) == -1
}

pub open spec fn polygon_prefix_has_zero_edge_sign_spec(p: Point2, polygon: Seq<RuntimePoint2>, upto: int) -> bool
    recommends
        polygon.len() >= 3,
        0 <= upto <= polygon.len() as int,
{
    exists|i: int| 0 <= i < upto && polygon_edge_orient_sign_spec(p, polygon, i) == 0
}

pub open spec fn polygon_has_positive_edge_sign_spec(p: Point2, polygon: Seq<RuntimePoint2>) -> bool
    recommends
        polygon.len() >= 3,
{
    polygon_prefix_has_positive_edge_sign_spec(p, polygon, polygon.len() as int)
}

pub open spec fn polygon_has_negative_edge_sign_spec(p: Point2, polygon: Seq<RuntimePoint2>) -> bool
    recommends
        polygon.len() >= 3,
{
    polygon_prefix_has_negative_edge_sign_spec(p, polygon, polygon.len() as int)
}

pub open spec fn polygon_has_zero_edge_sign_spec(p: Point2, polygon: Seq<RuntimePoint2>) -> bool
    recommends
        polygon.len() >= 3,
{
    polygon_prefix_has_zero_edge_sign_spec(p, polygon, polygon.len() as int)
}

pub open spec fn point_in_convex_polygon_boundary_inclusive_spec(p: Point2, polygon: Seq<RuntimePoint2>) -> bool {
    &&& polygon.len() >= 3
    &&& !(polygon_has_positive_edge_sign_spec(p, polygon) && polygon_has_negative_edge_sign_spec(p, polygon))
}

pub open spec fn point_strictly_in_convex_polygon_edge_sign_consistent_spec(
    p: Point2,
    polygon: Seq<RuntimePoint2>,
) -> bool {
    &&& polygon.len() >= 3
    &&& !(polygon_has_positive_edge_sign_spec(p, polygon) && polygon_has_negative_edge_sign_spec(p, polygon))
    &&& !polygon_has_zero_edge_sign_spec(p, polygon)
}

proof fn lemma_prefix_positive_step(p: Point2, polygon: Seq<RuntimePoint2>, i: int)
    requires
        polygon.len() >= 3,
        0 <= i < polygon.len() as int,
    ensures
        polygon_prefix_has_positive_edge_sign_spec(p, polygon, i + 1)
            == (polygon_prefix_has_positive_edge_sign_spec(p, polygon, i)
                || polygon_edge_orient_sign_spec(p, polygon, i) == 1),
{
    if polygon_prefix_has_positive_edge_sign_spec(p, polygon, i + 1) {
        let j = choose|j: int| 0 <= j < i + 1 && polygon_edge_orient_sign_spec(p, polygon, j) == 1;
        if j < i {
            assert(polygon_prefix_has_positive_edge_sign_spec(p, polygon, i));
        } else {
            assert(j == i);
            assert(polygon_edge_orient_sign_spec(p, polygon, i) == 1);
        }
    }
    if polygon_prefix_has_positive_edge_sign_spec(p, polygon, i) || polygon_edge_orient_sign_spec(p, polygon, i) == 1 {
        if polygon_prefix_has_positive_edge_sign_spec(p, polygon, i) {
            let j = choose|j: int| 0 <= j < i && polygon_edge_orient_sign_spec(p, polygon, j) == 1;
            assert(0 <= j < i + 1);
            assert(polygon_prefix_has_positive_edge_sign_spec(p, polygon, i + 1));
        } else {
            assert(0 <= i < i + 1);
            assert(polygon_prefix_has_positive_edge_sign_spec(p, polygon, i + 1));
        }
    }
}

proof fn lemma_prefix_negative_step(p: Point2, polygon: Seq<RuntimePoint2>, i: int)
    requires
        polygon.len() >= 3,
        0 <= i < polygon.len() as int,
    ensures
        polygon_prefix_has_negative_edge_sign_spec(p, polygon, i + 1)
            == (polygon_prefix_has_negative_edge_sign_spec(p, polygon, i)
                || polygon_edge_orient_sign_spec(p, polygon, i) == -1),
{
    if polygon_prefix_has_negative_edge_sign_spec(p, polygon, i + 1) {
        let j = choose|j: int| 0 <= j < i + 1 && polygon_edge_orient_sign_spec(p, polygon, j) == -1;
        if j < i {
            assert(polygon_prefix_has_negative_edge_sign_spec(p, polygon, i));
        } else {
            assert(j == i);
            assert(polygon_edge_orient_sign_spec(p, polygon, i) == -1);
        }
    }
    if polygon_prefix_has_negative_edge_sign_spec(p, polygon, i) || polygon_edge_orient_sign_spec(p, polygon, i) == -1 {
        if polygon_prefix_has_negative_edge_sign_spec(p, polygon, i) {
            let j = choose|j: int| 0 <= j < i && polygon_edge_orient_sign_spec(p, polygon, j) == -1;
            assert(0 <= j < i + 1);
            assert(polygon_prefix_has_negative_edge_sign_spec(p, polygon, i + 1));
        } else {
            assert(0 <= i < i + 1);
            assert(polygon_prefix_has_negative_edge_sign_spec(p, polygon, i + 1));
        }
    }
}

proof fn lemma_prefix_zero_step(p: Point2, polygon: Seq<RuntimePoint2>, i: int)
    requires
        polygon.len() >= 3,
        0 <= i < polygon.len() as int,
    ensures
        polygon_prefix_has_zero_edge_sign_spec(p, polygon, i + 1)
            == (polygon_prefix_has_zero_edge_sign_spec(p, polygon, i)
                || polygon_edge_orient_sign_spec(p, polygon, i) == 0),
{
    if polygon_prefix_has_zero_edge_sign_spec(p, polygon, i + 1) {
        let j = choose|j: int| 0 <= j < i + 1 && polygon_edge_orient_sign_spec(p, polygon, j) == 0;
        if j < i {
            assert(polygon_prefix_has_zero_edge_sign_spec(p, polygon, i));
        } else {
            assert(j == i);
            assert(polygon_edge_orient_sign_spec(p, polygon, i) == 0);
        }
    }
    if polygon_prefix_has_zero_edge_sign_spec(p, polygon, i) || polygon_edge_orient_sign_spec(p, polygon, i) == 0 {
        if polygon_prefix_has_zero_edge_sign_spec(p, polygon, i) {
            let j = choose|j: int| 0 <= j < i && polygon_edge_orient_sign_spec(p, polygon, j) == 0;
            assert(0 <= j < i + 1);
            assert(polygon_prefix_has_zero_edge_sign_spec(p, polygon, i + 1));
        } else {
            assert(0 <= i < i + 1);
            assert(polygon_prefix_has_zero_edge_sign_spec(p, polygon, i + 1));
        }
    }
}
}

/// Returns true when `p` is inside or on the boundary of a convex polygon.
///
/// Precondition (not enforced): `polygon` is convex and vertices are ordered
/// consistently (all clockwise or all counter-clockwise).
#[cfg(not(verus_keep_ghost))]
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

#[cfg(verus_keep_ghost)]
verus! {
pub fn point_in_convex_polygon_2d(p: &RuntimePoint2, polygon: &[RuntimePoint2]) -> (out: bool)
    ensures
        out == point_in_convex_polygon_boundary_inclusive_spec(p@, polygon@),
{
    if polygon.len() < 3 {
        return false;
    }

    let n = polygon.len();
    let mut saw_pos = false;
    let mut saw_neg = false;
    let mut i: usize = 0;

    while i < n
        invariant
            n == polygon.len(),
            n >= 3,
            0 <= i <= n,
            saw_pos == polygon_prefix_has_positive_edge_sign_spec(p@, polygon@, i as int),
            saw_neg == polygon_prefix_has_negative_edge_sign_spec(p@, polygon@, i as int),
        decreases n as int - i as int,
    {
        let a = &polygon[i];
        let next = if i + 1 < n { i + 1 } else { 0 };
        let b = &polygon[next];
        let s = orient2d_sign(a, b, p);
        let prev_i = i;
        let pos_now = s == 1;
        let neg_now = s == -1;
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
            assert((s == 1) == (orient2d_spec(a@, b@, p@).signum() == 1));
            assert((s == -1) == (orient2d_spec(a@, b@, p@).signum() == -1));
            assert(pos_now == (polygon_edge_orient_sign_spec(p@, polygon@, idx) == 1));
            assert(neg_now == (polygon_edge_orient_sign_spec(p@, polygon@, idx) == -1));
        }

        let new_saw_pos = saw_pos || pos_now;
        let new_saw_neg = saw_neg || neg_now;
        proof {
            let idx = prev_i as int;
            lemma_prefix_positive_step(p@, polygon@, idx);
            lemma_prefix_negative_step(p@, polygon@, idx);
            assert(new_saw_pos
                == (polygon_prefix_has_positive_edge_sign_spec(p@, polygon@, idx)
                    || polygon_edge_orient_sign_spec(p@, polygon@, idx) == 1));
            assert(new_saw_neg
                == (polygon_prefix_has_negative_edge_sign_spec(p@, polygon@, idx)
                    || polygon_edge_orient_sign_spec(p@, polygon@, idx) == -1));
            assert(new_saw_pos == polygon_prefix_has_positive_edge_sign_spec(p@, polygon@, idx + 1));
            assert(new_saw_neg == polygon_prefix_has_negative_edge_sign_spec(p@, polygon@, idx + 1));
        }
        saw_pos = new_saw_pos;
        saw_neg = new_saw_neg;
        i = prev_i + 1;
    }

    proof {
        assert(i == n);
        assert(saw_pos == polygon_has_positive_edge_sign_spec(p@, polygon@));
        assert(saw_neg == polygon_has_negative_edge_sign_spec(p@, polygon@));
        assert(point_in_convex_polygon_boundary_inclusive_spec(p@, polygon@)
            == !(polygon_has_positive_edge_sign_spec(p@, polygon@) && polygon_has_negative_edge_sign_spec(p@, polygon@)));
        assert(!(saw_pos && saw_neg)
            == !(polygon_has_positive_edge_sign_spec(p@, polygon@) && polygon_has_negative_edge_sign_spec(p@, polygon@)));
    }
    !(saw_pos && saw_neg)
}
}

/// Returns true when `p` is strictly inside a convex polygon.
///
/// Points on polygon edges/vertices are excluded.
///
/// Precondition (not enforced): `polygon` is convex and vertices are ordered
/// consistently (all clockwise or all counter-clockwise).
#[cfg(not(verus_keep_ghost))]
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

#[cfg(verus_keep_ghost)]
verus! {
pub fn point_strictly_in_convex_polygon_2d(p: &RuntimePoint2, polygon: &[RuntimePoint2]) -> (out: bool)
    ensures
        out == point_strictly_in_convex_polygon_edge_sign_consistent_spec(p@, polygon@),
{
    if polygon.len() < 3 {
        return false;
    }

    let n = polygon.len();
    let mut saw_pos = false;
    let mut saw_neg = false;
    let mut saw_zero = false;
    let mut i: usize = 0;

    while i < n
        invariant
            n == polygon.len(),
            n >= 3,
            0 <= i <= n,
            saw_pos == polygon_prefix_has_positive_edge_sign_spec(p@, polygon@, i as int),
            saw_neg == polygon_prefix_has_negative_edge_sign_spec(p@, polygon@, i as int),
            saw_zero == polygon_prefix_has_zero_edge_sign_spec(p@, polygon@, i as int),
        decreases n as int - i as int,
    {
        let a = &polygon[i];
        let next = if i + 1 < n { i + 1 } else { 0 };
        let b = &polygon[next];
        let s = orient2d_sign(a, b, p);
        let prev_i = i;
        let pos_now = s == 1;
        let neg_now = s == -1;
        let zero_now = s == 0;
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
            assert((s == 1) == (orient2d_spec(a@, b@, p@).signum() == 1));
            assert((s == -1) == (orient2d_spec(a@, b@, p@).signum() == -1));
            assert((s == 0) == (orient2d_spec(a@, b@, p@).signum() == 0));
            assert(pos_now == (polygon_edge_orient_sign_spec(p@, polygon@, idx) == 1));
            assert(neg_now == (polygon_edge_orient_sign_spec(p@, polygon@, idx) == -1));
            assert(zero_now == (polygon_edge_orient_sign_spec(p@, polygon@, idx) == 0));
        }

        let new_saw_pos = saw_pos || pos_now;
        let new_saw_neg = saw_neg || neg_now;
        let new_saw_zero = saw_zero || zero_now;
        proof {
            let idx = prev_i as int;
            lemma_prefix_positive_step(p@, polygon@, idx);
            lemma_prefix_negative_step(p@, polygon@, idx);
            lemma_prefix_zero_step(p@, polygon@, idx);
            assert(new_saw_pos
                == (polygon_prefix_has_positive_edge_sign_spec(p@, polygon@, idx)
                    || polygon_edge_orient_sign_spec(p@, polygon@, idx) == 1));
            assert(new_saw_neg
                == (polygon_prefix_has_negative_edge_sign_spec(p@, polygon@, idx)
                    || polygon_edge_orient_sign_spec(p@, polygon@, idx) == -1));
            assert(new_saw_zero
                == (polygon_prefix_has_zero_edge_sign_spec(p@, polygon@, idx)
                    || polygon_edge_orient_sign_spec(p@, polygon@, idx) == 0));
            assert(new_saw_pos == polygon_prefix_has_positive_edge_sign_spec(p@, polygon@, idx + 1));
            assert(new_saw_neg == polygon_prefix_has_negative_edge_sign_spec(p@, polygon@, idx + 1));
            assert(new_saw_zero == polygon_prefix_has_zero_edge_sign_spec(p@, polygon@, idx + 1));
        }
        saw_pos = new_saw_pos;
        saw_neg = new_saw_neg;
        saw_zero = new_saw_zero;
        i = prev_i + 1;
    }

    proof {
        assert(i == n);
        assert(saw_pos == polygon_has_positive_edge_sign_spec(p@, polygon@));
        assert(saw_neg == polygon_has_negative_edge_sign_spec(p@, polygon@));
        assert(saw_zero == polygon_has_zero_edge_sign_spec(p@, polygon@));
        assert(point_strictly_in_convex_polygon_edge_sign_consistent_spec(p@, polygon@)
            == (
            !(polygon_has_positive_edge_sign_spec(p@, polygon@) && polygon_has_negative_edge_sign_spec(p@, polygon@))
                && !polygon_has_zero_edge_sign_spec(p@, polygon@)
        ));
        assert((!(saw_pos && saw_neg) && !saw_zero)
            == (
            !(polygon_has_positive_edge_sign_spec(p@, polygon@) && polygon_has_negative_edge_sign_spec(p@, polygon@))
                && !polygon_has_zero_edge_sign_spec(p@, polygon@)
        ));
    }
    !(saw_pos && saw_neg) && !saw_zero
}
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
