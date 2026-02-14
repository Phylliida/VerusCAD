use crate::orientation_predicates::orient2d_sign;
use vcad_math::runtime_point2::RuntimePoint2;
use vcad_math::runtime_scalar::RuntimeScalar;
#[cfg(verus_keep_ghost)]
use vcad_math::orientation::orient2d_spec;
#[cfg(verus_keep_ghost)]
use vcad_math::point2::Point2;
#[cfg(verus_keep_ghost)]
use vcad_math::scalar::Scalar;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Coarse intersection relation for two closed 2D segments `[ab]` and `[cd]`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SegmentIntersection2dKind {
    Disjoint,
    Proper,
    EndpointTouch,
    CollinearOverlap,
}

#[cfg(not(verus_keep_ghost))]
fn scalar_sign(a: &RuntimeScalar, b: &RuntimeScalar) -> i8 {
    a.sub(b).signum_i8()
}

#[cfg(not(verus_keep_ghost))]
fn scalar_eq(a: &RuntimeScalar, b: &RuntimeScalar) -> bool {
    scalar_sign(a, b) == 0
}

#[cfg(not(verus_keep_ghost))]
fn scalar_le(a: &RuntimeScalar, b: &RuntimeScalar) -> bool {
    scalar_sign(a, b) <= 0
}

#[cfg(not(verus_keep_ghost))]
fn scalar_lt(a: &RuntimeScalar, b: &RuntimeScalar) -> bool {
    scalar_sign(a, b) < 0
}

#[cfg(not(verus_keep_ghost))]
fn scalar_min<'a>(a: &'a RuntimeScalar, b: &'a RuntimeScalar) -> &'a RuntimeScalar {
    if scalar_le(a, b) { a } else { b }
}

#[cfg(not(verus_keep_ghost))]
fn scalar_max<'a>(a: &'a RuntimeScalar, b: &'a RuntimeScalar) -> &'a RuntimeScalar {
    if scalar_le(a, b) { b } else { a }
}

#[cfg(not(verus_keep_ghost))]
fn point_on_segment_inclusive_runtime(
    p: &RuntimePoint2,
    a: &RuntimePoint2,
    b: &RuntimePoint2,
) -> bool {
    if orient2d_sign(a, b, p) != 0 {
        return false;
    }

    let x_lo = scalar_min(a.x(), b.x());
    let x_hi = scalar_max(a.x(), b.x());
    let y_lo = scalar_min(a.y(), b.y());
    let y_hi = scalar_max(a.y(), b.y());

    scalar_le(x_lo, p.x())
        && scalar_le(p.x(), x_hi)
        && scalar_le(y_lo, p.y())
        && scalar_le(p.y(), y_hi)
}

// Returns:
// -1 => disjoint intervals
//  0 => overlap at exactly one coordinate
//  1 => overlap on a non-zero interval
#[cfg(not(verus_keep_ghost))]
fn collinear_overlap_dimension_kind(
    a1: &RuntimeScalar,
    a2: &RuntimeScalar,
    b1: &RuntimeScalar,
    b2: &RuntimeScalar,
) -> i8 {
    let a_lo = scalar_min(a1, a2);
    let a_hi = scalar_max(a1, a2);
    let b_lo = scalar_min(b1, b2);
    let b_hi = scalar_max(b1, b2);
    let lo = scalar_max(a_lo, b_lo);
    let hi = scalar_min(a_hi, b_hi);
    if scalar_lt(hi, lo) {
        -1
    } else if scalar_eq(lo, hi) {
        0
    } else {
        1
    }
}

#[cfg(not(verus_keep_ghost))]
fn endpoint_touch_point_runtime(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
    d: &RuntimePoint2,
) -> Option<RuntimePoint2> {
    if point_on_segment_inclusive_runtime(c, a, b) {
        return Some(c.clone());
    }
    if point_on_segment_inclusive_runtime(d, a, b) {
        return Some(d.clone());
    }
    if point_on_segment_inclusive_runtime(a, c, d) {
        return Some(a.clone());
    }
    if point_on_segment_inclusive_runtime(b, c, d) {
        return Some(b.clone());
    }
    None
}

#[cfg(not(verus_keep_ghost))]
fn proper_intersection_point_runtime(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
    d: &RuntimePoint2,
) -> Option<RuntimePoint2> {
    // Line-line intersection parameterization:
    // a + t (b-a), where t = cross(c-a, d-c) / cross(b-a, d-c).
    let r = b.sub(a);
    let s = d.sub(c);
    let den = r.cross(&s);
    let inv = den.recip()?;
    let cma = c.sub(a);
    let t = cma.cross(&s).mul(&inv);
    let step = r.scale(&t);
    Some(a.add_vec(&step))
}

/// Classifies the intersection relation between two closed 2D segments.
#[cfg(not(verus_keep_ghost))]
pub fn segment_intersection_kind_2d(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
    d: &RuntimePoint2,
) -> SegmentIntersection2dKind {
    let o1 = orient2d_sign(a, b, c);
    let o2 = orient2d_sign(a, b, d);
    let o3 = orient2d_sign(c, d, a);
    let o4 = orient2d_sign(c, d, b);
    let touch1 = o1 == 0 && point_on_segment_inclusive_runtime(c, a, b);
    let touch2 = o2 == 0 && point_on_segment_inclusive_runtime(d, a, b);
    let touch3 = o3 == 0 && point_on_segment_inclusive_runtime(a, c, d);
    let touch4 = o4 == 0 && point_on_segment_inclusive_runtime(b, c, d);

    if o1 == 0 && o2 == 0 && o3 == 0 && o4 == 0 {
        let use_x = scalar_sign(a.x(), b.x()) != 0 || scalar_sign(c.x(), d.x()) != 0;
        let overlap_kind = if use_x {
            collinear_overlap_dimension_kind(a.x(), b.x(), c.x(), d.x())
        } else {
            collinear_overlap_dimension_kind(a.y(), b.y(), c.y(), d.y())
        };
        if overlap_kind < 0 {
            SegmentIntersection2dKind::Disjoint
        } else if overlap_kind == 0 {
            SegmentIntersection2dKind::EndpointTouch
        } else {
            SegmentIntersection2dKind::CollinearOverlap
        }
    } else if o1 != 0 && o2 != 0 && o3 != 0 && o4 != 0 && o1 != o2 && o3 != o4 {
        SegmentIntersection2dKind::Proper
    } else if touch1 || touch2 || touch3 || touch4
    {
        SegmentIntersection2dKind::EndpointTouch
    } else {
        SegmentIntersection2dKind::Disjoint
    }
}

/// Returns a concrete witness point when the relation has a unique point.
///
/// For `Proper` and `EndpointTouch` this returns `Some(point)`.
/// For `Disjoint` and `CollinearOverlap` this returns `None`.
#[cfg(not(verus_keep_ghost))]
pub fn segment_intersection_point_2d(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
    d: &RuntimePoint2,
) -> Option<RuntimePoint2> {
    match segment_intersection_kind_2d(a, b, c, d) {
        SegmentIntersection2dKind::Proper => proper_intersection_point_runtime(a, b, c, d),
        SegmentIntersection2dKind::EndpointTouch => endpoint_touch_point_runtime(a, b, c, d),
        SegmentIntersection2dKind::Disjoint => None,
        SegmentIntersection2dKind::CollinearOverlap => None,
    }
}

#[cfg(verus_keep_ghost)]
verus! {
#[derive(Structural, Copy, Clone, PartialEq, Eq)]
pub enum SegmentIntersection2dKindSpec {
    Disjoint,
    Proper,
    EndpointTouch,
    CollinearOverlap,
}

pub open spec fn scalar_sign_spec(a: Scalar, b: Scalar) -> int {
    a.sub_spec(b).signum()
}

pub open spec fn scalar_eq_sign_spec(a: Scalar, b: Scalar) -> bool {
    scalar_sign_spec(a, b) == 0
}

pub open spec fn scalar_le_sign_spec(a: Scalar, b: Scalar) -> bool {
    scalar_sign_spec(a, b) <= 0
}

pub open spec fn scalar_lt_sign_spec(a: Scalar, b: Scalar) -> bool {
    scalar_sign_spec(a, b) < 0
}

pub open spec fn scalar_min_spec(a: Scalar, b: Scalar) -> Scalar {
    if scalar_le_sign_spec(a, b) { a } else { b }
}

pub open spec fn scalar_max_spec(a: Scalar, b: Scalar) -> Scalar {
    if scalar_le_sign_spec(a, b) { b } else { a }
}

pub open spec fn point_on_segment_inclusive_spec(p: Point2, a: Point2, b: Point2) -> bool {
    &&& orient2d_spec(a, b, p).signum() == 0
    &&& scalar_le_sign_spec(scalar_min_spec(a.x, b.x), p.x)
    &&& scalar_le_sign_spec(p.x, scalar_max_spec(a.x, b.x))
    &&& scalar_le_sign_spec(scalar_min_spec(a.y, b.y), p.y)
    &&& scalar_le_sign_spec(p.y, scalar_max_spec(a.y, b.y))
}

pub open spec fn collinear_overlap_dimension_kind_spec(
    a1: Scalar,
    a2: Scalar,
    b1: Scalar,
    b2: Scalar,
) -> int {
    let a_lo = scalar_min_spec(a1, a2);
    let a_hi = scalar_max_spec(a1, a2);
    let b_lo = scalar_min_spec(b1, b2);
    let b_hi = scalar_max_spec(b1, b2);
    let lo = scalar_max_spec(a_lo, b_lo);
    let hi = scalar_min_spec(a_hi, b_hi);
    if scalar_lt_sign_spec(hi, lo) {
        -1
    } else if scalar_eq_sign_spec(lo, hi) {
        0
    } else {
        1
    }
}

pub open spec fn segment_intersection_kind_spec(
    a: Point2,
    b: Point2,
    c: Point2,
    d: Point2,
) -> SegmentIntersection2dKindSpec {
    let o1 = orient2d_spec(a, b, c).signum();
    let o2 = orient2d_spec(a, b, d).signum();
    let o3 = orient2d_spec(c, d, a).signum();
    let o4 = orient2d_spec(c, d, b).signum();
    if o1 == 0 && o2 == 0 && o3 == 0 && o4 == 0 {
        let use_x = scalar_sign_spec(a.x, b.x) != 0 || scalar_sign_spec(c.x, d.x) != 0;
        let overlap_kind = if use_x {
            collinear_overlap_dimension_kind_spec(a.x, b.x, c.x, d.x)
        } else {
            collinear_overlap_dimension_kind_spec(a.y, b.y, c.y, d.y)
        };
        if overlap_kind < 0 {
            SegmentIntersection2dKindSpec::Disjoint
        } else if overlap_kind == 0 {
            SegmentIntersection2dKindSpec::EndpointTouch
        } else {
            SegmentIntersection2dKindSpec::CollinearOverlap
        }
    } else if o1 != 0 && o2 != 0 && o3 != 0 && o4 != 0 && o1 != o2 && o3 != o4 {
        SegmentIntersection2dKindSpec::Proper
    } else if (o1 == 0 && point_on_segment_inclusive_spec(c, a, b))
        || (o2 == 0 && point_on_segment_inclusive_spec(d, a, b))
        || (o3 == 0 && point_on_segment_inclusive_spec(a, c, d))
        || (o4 == 0 && point_on_segment_inclusive_spec(b, c, d))
    {
        SegmentIntersection2dKindSpec::EndpointTouch
    } else {
        SegmentIntersection2dKindSpec::Disjoint
    }
}

pub open spec fn point_on_both_segments_spec(
    p: Point2,
    a: Point2,
    b: Point2,
    c: Point2,
    d: Point2,
) -> bool {
    point_on_segment_inclusive_spec(p, a, b) && point_on_segment_inclusive_spec(p, c, d)
}

fn scalar_sign(a: &RuntimeScalar, b: &RuntimeScalar) -> (out: i8)
    ensures
        out as int == scalar_sign_spec(a@, b@),
        out == 1 || out == -1 || out == 0,
        (out == 0) == (scalar_sign_spec(a@, b@) == 0),
        (out < 0) == (scalar_sign_spec(a@, b@) < 0),
        (out <= 0) == (scalar_sign_spec(a@, b@) <= 0),
{
    let diff = a.sub(b);
    let out = diff.signum_i8();
    proof {
        let sp = diff.signum_i8_proof();
        assert((sp == 1) == (diff@.signum() == 1));
        assert((sp == -1) == (diff@.signum() == -1));
        assert((sp == 0) == (diff@.signum() == 0));
        assert((out == 1) == (diff@.signum() == 1));
        assert((out == -1) == (diff@.signum() == -1));
        assert((out == 0) == (diff@.signum() == 0));
        assert(diff@ == a@.sub_spec(b@));
        vcad_math::scalar::Scalar::lemma_signum_cases(diff@);
        if diff@.signum() == 1 {
            assert(out == 1);
            assert(sp == 1);
        } else if diff@.signum() == -1 {
            assert(out == -1);
            assert(sp == -1);
        } else {
            assert(diff@.signum() == 0);
            assert(out == 0);
            assert(sp == 0);
        }
        assert(out == sp);
        if out == 1 {
            assert(diff@.signum() == 1);
            assert(out as int == 1);
        } else if out == -1 {
            assert(diff@.signum() == -1);
            assert(out as int == -1);
        } else {
            assert(out == 0);
            assert(diff@.signum() == 0);
            assert(out as int == 0);
        }
        assert(out == 1 || out == -1 || out == 0);
        assert(out as int == diff@.signum());
        assert(out as int == scalar_sign_spec(a@, b@));
        assert((out == 0) == (out as int == 0));
        assert((out < 0) == ((out as int) < 0));
        assert((out <= 0) == ((out as int) <= 0));
        assert((out as int == 0) == (scalar_sign_spec(a@, b@) == 0));
        assert(((out as int) < 0) == (scalar_sign_spec(a@, b@) < 0));
        assert(((out as int) <= 0) == (scalar_sign_spec(a@, b@) <= 0));
    }
    out
}

fn scalar_eq(a: &RuntimeScalar, b: &RuntimeScalar) -> (out: bool)
    ensures
        out == scalar_eq_sign_spec(a@, b@),
{
    let s = scalar_sign(a, b);
    let out = s == 0;
    proof {
        assert((s == 0) == (scalar_sign_spec(a@, b@) == 0));
        assert(out == scalar_eq_sign_spec(a@, b@));
    }
    out
}

fn scalar_le(a: &RuntimeScalar, b: &RuntimeScalar) -> (out: bool)
    ensures
        out == scalar_le_sign_spec(a@, b@),
{
    let s = scalar_sign(a, b);
    let out = s <= 0;
    proof {
        assert((s <= 0) == (scalar_sign_spec(a@, b@) <= 0));
        assert(out == scalar_le_sign_spec(a@, b@));
    }
    out
}

fn scalar_lt(a: &RuntimeScalar, b: &RuntimeScalar) -> (out: bool)
    ensures
        out == scalar_lt_sign_spec(a@, b@),
{
    let s = scalar_sign(a, b);
    let out = s < 0;
    proof {
        assert((s < 0) == (scalar_sign_spec(a@, b@) < 0));
        assert(out == scalar_lt_sign_spec(a@, b@));
    }
    out
}

fn scalar_min<'a>(a: &'a RuntimeScalar, b: &'a RuntimeScalar) -> (out: &'a RuntimeScalar)
    ensures
        out@ == scalar_min_spec(a@, b@),
{
    let le = scalar_le(a, b);
    if le {
        proof {
            assert(scalar_le_sign_spec(a@, b@));
            assert(scalar_min_spec(a@, b@) == a@);
        }
        a
    } else {
        proof {
            assert(!scalar_le_sign_spec(a@, b@));
            assert(scalar_min_spec(a@, b@) == b@);
        }
        b
    }
}

fn scalar_max<'a>(a: &'a RuntimeScalar, b: &'a RuntimeScalar) -> (out: &'a RuntimeScalar)
    ensures
        out@ == scalar_max_spec(a@, b@),
{
    let le = scalar_le(a, b);
    if le {
        proof {
            assert(scalar_le_sign_spec(a@, b@));
            assert(scalar_max_spec(a@, b@) == b@);
        }
        b
    } else {
        proof {
            assert(!scalar_le_sign_spec(a@, b@));
            assert(scalar_max_spec(a@, b@) == a@);
        }
        a
    }
}

fn point_on_segment_inclusive_runtime(
    p: &RuntimePoint2,
    a: &RuntimePoint2,
    b: &RuntimePoint2,
) -> (out: bool)
    ensures
        out == point_on_segment_inclusive_spec(p@, a@, b@),
{
    let o = orient2d_sign(a, b, p);
    if o != 0 {
        proof {
            assert((o == 0) == (orient2d_spec(a@, b@, p@).signum() == 0));
            assert(orient2d_spec(a@, b@, p@).signum() != 0);
            assert(!point_on_segment_inclusive_spec(p@, a@, b@));
        }
        return false;
    }

    let x_lo = scalar_min(&a.x, &b.x);
    let x_hi = scalar_max(&a.x, &b.x);
    let y_lo = scalar_min(&a.y, &b.y);
    let y_hi = scalar_max(&a.y, &b.y);

    let c1 = scalar_le(x_lo, &p.x);
    let c2 = scalar_le(&p.x, x_hi);
    let c3 = scalar_le(y_lo, &p.y);
    let c4 = scalar_le(&p.y, y_hi);
    let out = c1 && c2 && c3 && c4;
    proof {
        assert((o == 0) == (orient2d_spec(a@, b@, p@).signum() == 0));
        assert(orient2d_spec(a@, b@, p@).signum() == 0);
        assert(c1 == scalar_le_sign_spec(x_lo@, p@.x));
        assert(c2 == scalar_le_sign_spec(p@.x, x_hi@));
        assert(c3 == scalar_le_sign_spec(y_lo@, p@.y));
        assert(c4 == scalar_le_sign_spec(p@.y, y_hi@));
        assert(x_lo@ == scalar_min_spec(a@.x, b@.x));
        assert(x_hi@ == scalar_max_spec(a@.x, b@.x));
        assert(y_lo@ == scalar_min_spec(a@.y, b@.y));
        assert(y_hi@ == scalar_max_spec(a@.y, b@.y));
        assert(out == point_on_segment_inclusive_spec(p@, a@, b@));
    }
    out
}

fn collinear_overlap_dimension_kind(
    a1: &RuntimeScalar,
    a2: &RuntimeScalar,
    b1: &RuntimeScalar,
    b2: &RuntimeScalar,
) -> (out: i8)
    ensures
        out as int == collinear_overlap_dimension_kind_spec(a1@, a2@, b1@, b2@),
{
    let a_lo = scalar_min(a1, a2);
    let a_hi = scalar_max(a1, a2);
    let b_lo = scalar_min(b1, b2);
    let b_hi = scalar_max(b1, b2);
    let lo = scalar_max(a_lo, b_lo);
    let hi = scalar_min(a_hi, b_hi);
    let less = scalar_lt(hi, lo);
    let equal = scalar_eq(lo, hi);
    if less {
        proof {
            assert(less == scalar_lt_sign_spec(hi@, lo@));
            assert(scalar_lt_sign_spec(hi@, lo@));
            assert(collinear_overlap_dimension_kind_spec(a1@, a2@, b1@, b2@) == -1);
        }
        -1
    } else if equal {
        proof {
            assert(!less);
            assert(equal == scalar_eq_sign_spec(lo@, hi@));
            assert(scalar_eq_sign_spec(lo@, hi@));
            assert(collinear_overlap_dimension_kind_spec(a1@, a2@, b1@, b2@) == 0);
        }
        0
    } else {
        proof {
            assert(!less);
            assert(!equal);
            assert(collinear_overlap_dimension_kind_spec(a1@, a2@, b1@, b2@) == 1);
        }
        1
    }
}

pub fn segment_intersection_kind_2d(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
    d: &RuntimePoint2,
) -> (out: SegmentIntersection2dKind)
    ensures
        out@ == segment_intersection_kind_spec(a@, b@, c@, d@),
{
    let o1 = orient2d_sign(a, b, c);
    let o2 = orient2d_sign(a, b, d);
    let o3 = orient2d_sign(c, d, a);
    let o4 = orient2d_sign(c, d, b);
    let touch1 = o1 == 0 && point_on_segment_inclusive_runtime(c, a, b);
    let touch2 = o2 == 0 && point_on_segment_inclusive_runtime(d, a, b);
    let touch3 = o3 == 0 && point_on_segment_inclusive_runtime(a, c, d);
    let touch4 = o4 == 0 && point_on_segment_inclusive_runtime(b, c, d);

    if o1 == 0 && o2 == 0 && o3 == 0 && o4 == 0 {
        let sx1 = scalar_sign(&a.x, &b.x);
        let sx2 = scalar_sign(&c.x, &d.x);
        let use_x = sx1 != 0 || sx2 != 0;
        let overlap_kind = if use_x {
            collinear_overlap_dimension_kind(&a.x, &b.x, &c.x, &d.x)
        } else {
            collinear_overlap_dimension_kind(&a.y, &b.y, &c.y, &d.y)
        };
        if overlap_kind < 0 {
            let out = SegmentIntersection2dKind::Disjoint;
            proof {
                assert((o1 == 0) == (orient2d_spec(a@, b@, c@).signum() == 0));
                assert((o2 == 0) == (orient2d_spec(a@, b@, d@).signum() == 0));
                assert((o3 == 0) == (orient2d_spec(c@, d@, a@).signum() == 0));
                assert((o4 == 0) == (orient2d_spec(c@, d@, b@).signum() == 0));
                assert(orient2d_spec(a@, b@, c@).signum() == 0);
                assert(orient2d_spec(a@, b@, d@).signum() == 0);
                assert(orient2d_spec(c@, d@, a@).signum() == 0);
                assert(orient2d_spec(c@, d@, b@).signum() == 0);
                assert((sx1 != 0) == (scalar_sign_spec(a@.x, b@.x) != 0));
                assert((sx2 != 0) == (scalar_sign_spec(c@.x, d@.x) != 0));
                assert(use_x == (scalar_sign_spec(a@.x, b@.x) != 0 || scalar_sign_spec(c@.x, d@.x) != 0));
                if use_x {
                    assert(overlap_kind as int == collinear_overlap_dimension_kind_spec(a@.x, b@.x, c@.x, d@.x));
                } else {
                    assert(overlap_kind as int == collinear_overlap_dimension_kind_spec(a@.y, b@.y, c@.y, d@.y));
                }
                assert((overlap_kind as int) < 0);
                assert(segment_intersection_kind_spec(a@, b@, c@, d@) is Disjoint);
                assert(out@ is Disjoint);
            }
            out
        } else if overlap_kind == 0 {
            let out = SegmentIntersection2dKind::EndpointTouch;
            proof {
                assert((o1 == 0) == (orient2d_spec(a@, b@, c@).signum() == 0));
                assert((o2 == 0) == (orient2d_spec(a@, b@, d@).signum() == 0));
                assert((o3 == 0) == (orient2d_spec(c@, d@, a@).signum() == 0));
                assert((o4 == 0) == (orient2d_spec(c@, d@, b@).signum() == 0));
                assert(orient2d_spec(a@, b@, c@).signum() == 0);
                assert(orient2d_spec(a@, b@, d@).signum() == 0);
                assert(orient2d_spec(c@, d@, a@).signum() == 0);
                assert(orient2d_spec(c@, d@, b@).signum() == 0);
                assert((sx1 != 0) == (scalar_sign_spec(a@.x, b@.x) != 0));
                assert((sx2 != 0) == (scalar_sign_spec(c@.x, d@.x) != 0));
                assert(use_x == (scalar_sign_spec(a@.x, b@.x) != 0 || scalar_sign_spec(c@.x, d@.x) != 0));
                if use_x {
                    assert(overlap_kind as int == collinear_overlap_dimension_kind_spec(a@.x, b@.x, c@.x, d@.x));
                } else {
                    assert(overlap_kind as int == collinear_overlap_dimension_kind_spec(a@.y, b@.y, c@.y, d@.y));
                }
                assert(overlap_kind as int == 0);
                assert(segment_intersection_kind_spec(a@, b@, c@, d@) is EndpointTouch);
                assert(out@ is EndpointTouch);
            }
            out
        } else {
            let out = SegmentIntersection2dKind::CollinearOverlap;
            proof {
                assert((o1 == 0) == (orient2d_spec(a@, b@, c@).signum() == 0));
                assert((o2 == 0) == (orient2d_spec(a@, b@, d@).signum() == 0));
                assert((o3 == 0) == (orient2d_spec(c@, d@, a@).signum() == 0));
                assert((o4 == 0) == (orient2d_spec(c@, d@, b@).signum() == 0));
                assert(orient2d_spec(a@, b@, c@).signum() == 0);
                assert(orient2d_spec(a@, b@, d@).signum() == 0);
                assert(orient2d_spec(c@, d@, a@).signum() == 0);
                assert(orient2d_spec(c@, d@, b@).signum() == 0);
                assert((sx1 != 0) == (scalar_sign_spec(a@.x, b@.x) != 0));
                assert((sx2 != 0) == (scalar_sign_spec(c@.x, d@.x) != 0));
                assert(use_x == (scalar_sign_spec(a@.x, b@.x) != 0 || scalar_sign_spec(c@.x, d@.x) != 0));
                if use_x {
                    assert(overlap_kind as int == collinear_overlap_dimension_kind_spec(a@.x, b@.x, c@.x, d@.x));
                } else {
                    assert(overlap_kind as int == collinear_overlap_dimension_kind_spec(a@.y, b@.y, c@.y, d@.y));
                }
                assert(overlap_kind as int != 0);
                assert(overlap_kind as int >= 0);
                assert(segment_intersection_kind_spec(a@, b@, c@, d@) is CollinearOverlap);
                assert(out@ is CollinearOverlap);
            }
            out
        }
    } else if o1 != 0 && o2 != 0 && o3 != 0 && o4 != 0 && o1 != o2 && o3 != o4 {
        let out = SegmentIntersection2dKind::Proper;
        proof {
            assert((o1 == 0) == (orient2d_spec(a@, b@, c@).signum() == 0));
            assert((o2 == 0) == (orient2d_spec(a@, b@, d@).signum() == 0));
            assert((o3 == 0) == (orient2d_spec(c@, d@, a@).signum() == 0));
            assert((o4 == 0) == (orient2d_spec(c@, d@, b@).signum() == 0));
            assert(orient2d_spec(a@, b@, c@).signum() != 0);
            assert(orient2d_spec(a@, b@, d@).signum() != 0);
            assert(orient2d_spec(c@, d@, a@).signum() != 0);
            assert(orient2d_spec(c@, d@, b@).signum() != 0);
            assert(segment_intersection_kind_spec(a@, b@, c@, d@) is Proper);
            assert(out@ is Proper);
        }
        out
    } else if touch1 || touch2 || touch3 || touch4 {
        let out = SegmentIntersection2dKind::EndpointTouch;
        proof {
            assert((o1 == 0) == (orient2d_spec(a@, b@, c@).signum() == 0));
            assert((o2 == 0) == (orient2d_spec(a@, b@, d@).signum() == 0));
            assert((o3 == 0) == (orient2d_spec(c@, d@, a@).signum() == 0));
            assert((o4 == 0) == (orient2d_spec(c@, d@, b@).signum() == 0));
            assert(touch1 == ((orient2d_spec(a@, b@, c@).signum() == 0) && point_on_segment_inclusive_spec(c@, a@, b@)));
            assert(touch2 == ((orient2d_spec(a@, b@, d@).signum() == 0) && point_on_segment_inclusive_spec(d@, a@, b@)));
            assert(touch3 == ((orient2d_spec(c@, d@, a@).signum() == 0) && point_on_segment_inclusive_spec(a@, c@, d@)));
            assert(touch4 == ((orient2d_spec(c@, d@, b@).signum() == 0) && point_on_segment_inclusive_spec(b@, c@, d@)));
            assert(segment_intersection_kind_spec(a@, b@, c@, d@) is EndpointTouch);
            assert(out@ is EndpointTouch);
        }
        out
    } else {
        let out = SegmentIntersection2dKind::Disjoint;
        proof {
            assert(segment_intersection_kind_spec(a@, b@, c@, d@) is Disjoint);
            assert(out@ is Disjoint);
        }
        out
    }
}

pub proof fn lemma_segment_intersection_kind_spec_exhaustive(
    a: Point2,
    b: Point2,
    c: Point2,
    d: Point2,
)
    ensures
        (segment_intersection_kind_spec(a, b, c, d) is Disjoint)
            || (segment_intersection_kind_spec(a, b, c, d) is Proper)
            || (segment_intersection_kind_spec(a, b, c, d) is EndpointTouch)
            || (segment_intersection_kind_spec(a, b, c, d) is CollinearOverlap),
{
    let k = segment_intersection_kind_spec(a, b, c, d);
    match k {
        SegmentIntersection2dKindSpec::Disjoint => {
            assert(k is Disjoint);
        }
        SegmentIntersection2dKindSpec::Proper => {
            assert(k is Proper);
        }
        SegmentIntersection2dKindSpec::EndpointTouch => {
            assert(k is EndpointTouch);
        }
        SegmentIntersection2dKindSpec::CollinearOverlap => {
            assert(k is CollinearOverlap);
        }
    }
}

pub proof fn lemma_segment_intersection_kind_spec_pairwise_disjoint(
    a: Point2,
    b: Point2,
    c: Point2,
    d: Point2,
)
    ensures
        !((segment_intersection_kind_spec(a, b, c, d) is Disjoint)
            && (segment_intersection_kind_spec(a, b, c, d) is Proper)),
        !((segment_intersection_kind_spec(a, b, c, d) is Disjoint)
            && (segment_intersection_kind_spec(a, b, c, d) is EndpointTouch)),
        !((segment_intersection_kind_spec(a, b, c, d) is Disjoint)
            && (segment_intersection_kind_spec(a, b, c, d) is CollinearOverlap)),
        !((segment_intersection_kind_spec(a, b, c, d) is Proper)
            && (segment_intersection_kind_spec(a, b, c, d) is EndpointTouch)),
        !((segment_intersection_kind_spec(a, b, c, d) is Proper)
            && (segment_intersection_kind_spec(a, b, c, d) is CollinearOverlap)),
        !((segment_intersection_kind_spec(a, b, c, d) is EndpointTouch)
            && (segment_intersection_kind_spec(a, b, c, d) is CollinearOverlap)),
{
    let k = segment_intersection_kind_spec(a, b, c, d);
    match k {
        SegmentIntersection2dKindSpec::Disjoint => {
            assert(!(k is Proper));
            assert(!(k is EndpointTouch));
            assert(!(k is CollinearOverlap));
        }
        SegmentIntersection2dKindSpec::Proper => {
            assert(!(k is Disjoint));
            assert(!(k is EndpointTouch));
            assert(!(k is CollinearOverlap));
        }
        SegmentIntersection2dKindSpec::EndpointTouch => {
            assert(!(k is Disjoint));
            assert(!(k is Proper));
            assert(!(k is CollinearOverlap));
        }
        SegmentIntersection2dKindSpec::CollinearOverlap => {
            assert(!(k is Disjoint));
            assert(!(k is Proper));
            assert(!(k is EndpointTouch));
        }
    }
}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn segment_intersection_proper_crossing() {
        let a = RuntimePoint2::from_ints(0, 0);
        let b = RuntimePoint2::from_ints(4, 4);
        let c = RuntimePoint2::from_ints(0, 4);
        let d = RuntimePoint2::from_ints(4, 0);

        assert_eq!(
            segment_intersection_kind_2d(&a, &b, &c, &d),
            SegmentIntersection2dKind::Proper
        );

        let p = segment_intersection_point_2d(&a, &b, &c, &d).expect("proper intersection point");
        assert_eq!(p, RuntimePoint2::from_ints(2, 2));
    }

    #[test]
    fn segment_intersection_endpoint_touch() {
        let a = RuntimePoint2::from_ints(0, 0);
        let b = RuntimePoint2::from_ints(2, 0);
        let c = RuntimePoint2::from_ints(2, 0);
        let d = RuntimePoint2::from_ints(3, 1);

        assert_eq!(
            segment_intersection_kind_2d(&a, &b, &c, &d),
            SegmentIntersection2dKind::EndpointTouch
        );

        let p = segment_intersection_point_2d(&a, &b, &c, &d).expect("endpoint witness");
        assert_eq!(p, RuntimePoint2::from_ints(2, 0));
    }

    #[test]
    fn segment_intersection_parallel_disjoint() {
        let a = RuntimePoint2::from_ints(0, 0);
        let b = RuntimePoint2::from_ints(2, 0);
        let c = RuntimePoint2::from_ints(0, 1);
        let d = RuntimePoint2::from_ints(2, 1);

        assert_eq!(
            segment_intersection_kind_2d(&a, &b, &c, &d),
            SegmentIntersection2dKind::Disjoint
        );
        assert!(segment_intersection_point_2d(&a, &b, &c, &d).is_none());
    }

    #[test]
    fn segment_intersection_collinear_overlap() {
        let a = RuntimePoint2::from_ints(0, 0);
        let b = RuntimePoint2::from_ints(4, 0);
        let c = RuntimePoint2::from_ints(2, 0);
        let d = RuntimePoint2::from_ints(6, 0);

        assert_eq!(
            segment_intersection_kind_2d(&a, &b, &c, &d),
            SegmentIntersection2dKind::CollinearOverlap
        );
        assert!(segment_intersection_point_2d(&a, &b, &c, &d).is_none());
    }
}
