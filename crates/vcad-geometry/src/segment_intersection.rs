use crate::orientation_predicates::orient2d_sign;
use vcad_math::runtime_point2::RuntimePoint2;
use vcad_math::runtime_scalar::{RuntimeScalar, RuntimeSign};
#[cfg(verus_keep_ghost)]
use vcad_math::orientation::orient2d_spec;
#[cfg(verus_keep_ghost)]
use vcad_math::point2::Point2;
#[cfg(verus_keep_ghost)]
use vcad_math::runtime_wf as wf;
#[cfg(verus_keep_ghost)]
use vcad_math::scalar::Scalar;
#[cfg(verus_keep_ghost)]
use vcad_math::vec2::Vec2;
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
    match a.sub(b).sign() {
        RuntimeSign::Positive => 1,
        RuntimeSign::Negative => -1,
        RuntimeSign::Zero => 0,
    }
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
    let c_on_ab = point_on_segment_inclusive_runtime(c, a, b);
    let c_on_cd = point_on_segment_inclusive_runtime(c, c, d);
    if c_on_ab && c_on_cd {
        return Some(c.clone());
    }
    let d_on_ab = point_on_segment_inclusive_runtime(d, a, b);
    let d_on_cd = point_on_segment_inclusive_runtime(d, c, d);
    if d_on_ab && d_on_cd {
        return Some(d.clone());
    }
    let a_on_ab = point_on_segment_inclusive_runtime(a, a, b);
    let a_on_cd = point_on_segment_inclusive_runtime(a, c, d);
    if a_on_ab && a_on_cd {
        return Some(a.clone());
    }
    let b_on_ab = point_on_segment_inclusive_runtime(b, a, b);
    let b_on_cd = point_on_segment_inclusive_runtime(b, c, d);
    if b_on_ab && b_on_cd {
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
    let p = a.add_vec(&step);
    debug_assert!(point_on_segment_inclusive_runtime(&p, a, b));
    debug_assert!(point_on_segment_inclusive_runtime(&p, c, d));
    Some(p)
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
    let touch1 = point_on_segment_inclusive_runtime(c, a, b)
        && point_on_segment_inclusive_runtime(c, c, d);
    let touch2 = point_on_segment_inclusive_runtime(d, a, b)
        && point_on_segment_inclusive_runtime(d, c, d);
    let touch3 = point_on_segment_inclusive_runtime(a, a, b)
        && point_on_segment_inclusive_runtime(a, c, d);
    let touch4 = point_on_segment_inclusive_runtime(b, a, b)
        && point_on_segment_inclusive_runtime(b, c, d);

    if o1 == 0 && o2 == 0 && o3 == 0 && o4 == 0 {
        let use_x = scalar_sign(a.x(), b.x()) != 0 || scalar_sign(c.x(), d.x()) != 0;
        let overlap_kind = if use_x {
            collinear_overlap_dimension_kind(a.x(), b.x(), c.x(), d.x())
        } else {
            collinear_overlap_dimension_kind(a.y(), b.y(), c.y(), d.y())
        };
        if overlap_kind < 0 {
            SegmentIntersection2dKind::Disjoint
        } else if overlap_kind == 0 && (touch1 || touch2 || touch3 || touch4) {
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
    let touch1 = point_on_both_segments_spec(c, a, b, c, d);
    let touch2 = point_on_both_segments_spec(d, a, b, c, d);
    let touch3 = point_on_both_segments_spec(a, a, b, c, d);
    let touch4 = point_on_both_segments_spec(b, a, b, c, d);
    if o1 == 0 && o2 == 0 && o3 == 0 && o4 == 0 {
        let use_x = scalar_sign_spec(a.x, b.x) != 0 || scalar_sign_spec(c.x, d.x) != 0;
        let overlap_kind = if use_x {
            collinear_overlap_dimension_kind_spec(a.x, b.x, c.x, d.x)
        } else {
            collinear_overlap_dimension_kind_spec(a.y, b.y, c.y, d.y)
        };
        if overlap_kind < 0 {
            SegmentIntersection2dKindSpec::Disjoint
        } else if overlap_kind == 0 && (touch1 || touch2 || touch3 || touch4) {
            SegmentIntersection2dKindSpec::EndpointTouch
        } else {
            SegmentIntersection2dKindSpec::CollinearOverlap
        }
    } else if o1 != 0 && o2 != 0 && o3 != 0 && o4 != 0 && o1 != o2 && o3 != o4 {
        SegmentIntersection2dKindSpec::Proper
    } else if touch1 || touch2 || touch3 || touch4
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

pub open spec fn point_on_segment_supporting_line_spec(
    p: Point2,
    a: Point2,
    b: Point2,
) -> bool {
    orient2d_spec(a, b, p).signum() == 0
}

proof fn lemma_segment_intersection_kind_spec_proper_implies_straddling_signs(
    a: Point2,
    b: Point2,
    c: Point2,
    d: Point2,
)
    requires
        segment_intersection_kind_spec(a, b, c, d) is Proper,
    ensures
        orient2d_spec(a, b, c).signum() != 0,
        orient2d_spec(a, b, d).signum() != 0,
        orient2d_spec(c, d, a).signum() != 0,
        orient2d_spec(c, d, b).signum() != 0,
        orient2d_spec(a, b, c).signum() != orient2d_spec(a, b, d).signum(),
        orient2d_spec(c, d, a).signum() != orient2d_spec(c, d, b).signum(),
{
    let o1 = orient2d_spec(a, b, c).signum();
    let o2 = orient2d_spec(a, b, d).signum();
    let o3 = orient2d_spec(c, d, a).signum();
    let o4 = orient2d_spec(c, d, b).signum();
    let touch1 = point_on_both_segments_spec(c, a, b, c, d);
    let touch2 = point_on_both_segments_spec(d, a, b, c, d);
    let touch3 = point_on_both_segments_spec(a, a, b, c, d);
    let touch4 = point_on_both_segments_spec(b, a, b, c, d);
    let use_x = scalar_sign_spec(a.x, b.x) != 0 || scalar_sign_spec(c.x, d.x) != 0;
    let overlap_kind = if use_x {
        collinear_overlap_dimension_kind_spec(a.x, b.x, c.x, d.x)
    } else {
        collinear_overlap_dimension_kind_spec(a.y, b.y, c.y, d.y)
    };
    let k = segment_intersection_kind_spec(a, b, c, d);
    assert(k is Proper);

    if o1 == 0 && o2 == 0 && o3 == 0 && o4 == 0 {
        if overlap_kind < 0 {
            assert(k is Disjoint);
        } else if overlap_kind == 0 && (touch1 || touch2 || touch3 || touch4) {
            assert(k is EndpointTouch);
        } else {
            assert(k is CollinearOverlap);
        }
        lemma_segment_intersection_kind_spec_pairwise_disjoint(a, b, c, d);
        assert(false);
    } else if o1 != 0 && o2 != 0 && o3 != 0 && o4 != 0 && o1 != o2 && o3 != o4 {
        assert(orient2d_spec(a, b, c).signum() != 0);
        assert(orient2d_spec(a, b, d).signum() != 0);
        assert(orient2d_spec(c, d, a).signum() != 0);
        assert(orient2d_spec(c, d, b).signum() != 0);
        assert(orient2d_spec(a, b, c).signum() != orient2d_spec(a, b, d).signum());
        assert(orient2d_spec(c, d, a).signum() != orient2d_spec(c, d, b).signum());
    } else if touch1 || touch2 || touch3 || touch4 {
        assert(k is EndpointTouch);
        lemma_segment_intersection_kind_spec_pairwise_disjoint(a, b, c, d);
        assert(false);
    } else {
        assert(k is Disjoint);
        lemma_segment_intersection_kind_spec_pairwise_disjoint(a, b, c, d);
        assert(false);
    }
}

proof fn lemma_proper_straddling_implies_nonzero_direction_cross(
    a: Point2,
    b: Point2,
    c: Point2,
    d: Point2,
)
    requires
        orient2d_spec(a, b, c).signum() != 0,
        orient2d_spec(a, b, d).signum() != 0,
        orient2d_spec(a, b, c).signum() != orient2d_spec(a, b, d).signum(),
    ensures
        !b.sub_spec(a).cross_spec(d.sub_spec(c)).eqv_spec(Scalar::from_int_spec(0)),
{
    let ba = b.sub_spec(a);
    let ca = c.sub_spec(a);
    let da = d.sub_spec(a);
    let dc = d.sub_spec(c);
    let ac = a.sub_spec(c);
    let den = ba.cross_spec(dc);
    let o1 = orient2d_spec(a, b, c);
    let o2 = orient2d_spec(a, b, d);
    let z = Scalar::from_int_spec(0);

    assert(o1 == ba.cross_spec(ca));
    assert(o2 == ba.cross_spec(da));
    Point2::lemma_sub_chain_eqv(d, a, c);
    Point2::lemma_sub_antisymmetric(a, c);
    assert(ac == ca.neg_spec());
    Vec2::lemma_cross_eqv_congruence(ba, ba, dc, da.add_spec(ac));
    assert(den.eqv_spec(ba.cross_spec(da.add_spec(ac))));
    Vec2::lemma_cross_linear_right(ba, da, ac);
    assert(ba.cross_spec(da.add_spec(ac)).eqv_spec(ba.cross_spec(da).add_spec(ba.cross_spec(ac))));
    Scalar::lemma_eqv_transitive(
        den,
        ba.cross_spec(da.add_spec(ac)),
        ba.cross_spec(da).add_spec(ba.cross_spec(ac)),
    );
    assert(den.eqv_spec(ba.cross_spec(da).add_spec(ba.cross_spec(ac))));
    Vec2::lemma_cross_neg_right(ba, ca);
    assert(ba.cross_spec(ac) == ba.cross_spec(ca).neg_spec());
    assert(ba.cross_spec(da).add_spec(ba.cross_spec(ac)) == o2.add_spec(o1.neg_spec()));
    Scalar::lemma_sub_is_add_neg(o2, o1);
    assert(o2.sub_spec(o1) == o2.add_spec(o1.neg_spec()));
    assert(den.eqv_spec(o2.sub_spec(o1)));

    if den.eqv_spec(z) {
        Scalar::lemma_eqv_symmetric(den, o2.sub_spec(o1));
        assert(o2.sub_spec(o1).eqv_spec(den));
        Scalar::lemma_eqv_transitive(o2.sub_spec(o1), den, z);
        assert(o2.sub_spec(o1).eqv_spec(z));
        Scalar::lemma_sub_eqv_zero_iff_eqv(o2, o1);
        assert(o2.eqv_spec(o1));
        Scalar::lemma_eqv_signum(o2, o1);
        assert(o2.signum() == o1.signum());
        assert(o1.signum() != o2.signum());
        assert(false);
    }
}

fn scalar_sign(a: &RuntimeScalar, b: &RuntimeScalar) -> (out: i8)
    requires
        wf::scalar_wf2_spec(a, b),
    ensures
        out as int == scalar_sign_spec(a@, b@),
        out == 1 || out == -1 || out == 0,
        (out == 0) == (scalar_sign_spec(a@, b@) == 0),
        (out < 0) == (scalar_sign_spec(a@, b@) < 0),
        (out <= 0) == (scalar_sign_spec(a@, b@) <= 0),
{
    let diff = a.sub_wf(b);
    let sign = diff.sign_from_witness();
    let out = match sign {
        RuntimeSign::Positive => 1,
        RuntimeSign::Negative => -1,
        RuntimeSign::Zero => 0,
    };
    proof {
        assert((sign is Positive) == (diff@.signum() == 1));
        assert((sign is Negative) == (diff@.signum() == -1));
        assert((sign is Zero) == (diff@.signum() == 0));
        assert((out == 1) == (diff@.signum() == 1));
        assert((out == -1) == (diff@.signum() == -1));
        assert((out == 0) == (diff@.signum() == 0));
        assert(diff@ == a@.sub_spec(b@));
        vcad_math::scalar::Scalar::lemma_signum_cases(diff@);
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
    requires
        wf::scalar_wf2_spec(a, b),
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
    requires
        wf::scalar_wf2_spec(a, b),
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
    requires
        wf::scalar_wf2_spec(a, b),
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
    requires
        wf::scalar_wf2_spec(a, b),
    ensures
        out@ == scalar_min_spec(a@, b@),
        out.witness_wf_spec(),
{
    let le = scalar_le(a, b);
    if le {
        proof {
            assert(scalar_le_sign_spec(a@, b@));
            assert(scalar_min_spec(a@, b@) == a@);
            assert(a.witness_wf_spec());
        }
        a
    } else {
        proof {
            assert(!scalar_le_sign_spec(a@, b@));
            assert(scalar_min_spec(a@, b@) == b@);
            assert(b.witness_wf_spec());
        }
        b
    }
}

fn scalar_max<'a>(a: &'a RuntimeScalar, b: &'a RuntimeScalar) -> (out: &'a RuntimeScalar)
    requires
        wf::scalar_wf2_spec(a, b),
    ensures
        out@ == scalar_max_spec(a@, b@),
        out.witness_wf_spec(),
{
    let le = scalar_le(a, b);
    if le {
        proof {
            assert(scalar_le_sign_spec(a@, b@));
            assert(scalar_max_spec(a@, b@) == b@);
            assert(b.witness_wf_spec());
        }
        b
    } else {
        proof {
            assert(!scalar_le_sign_spec(a@, b@));
            assert(scalar_max_spec(a@, b@) == a@);
            assert(a.witness_wf_spec());
        }
        a
    }
}

fn point_on_segment_inclusive_runtime(
    p: &RuntimePoint2,
    a: &RuntimePoint2,
    b: &RuntimePoint2,
) -> (out: bool)
    requires
        wf::point2_wf3_spec(p, a, b),
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
    requires
        wf::scalar_wf4_spec(a1, a2, b1, b2),
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

fn endpoint_touch_point_runtime(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
    d: &RuntimePoint2,
) -> (out: Option<RuntimePoint2>)
    requires
        wf::point2_wf4_spec(a, b, c, d),
    ensures
        match out {
            Option::None => true,
            Option::Some(p) => point_on_both_segments_spec(p@, a@, b@, c@, d@),
        },
        (
            point_on_both_segments_spec(c@, a@, b@, c@, d@)
                || point_on_both_segments_spec(d@, a@, b@, c@, d@)
                || point_on_both_segments_spec(a@, a@, b@, c@, d@)
                || point_on_both_segments_spec(b@, a@, b@, c@, d@)
        ) ==> out.is_some(),
{
    let c_on_ab = point_on_segment_inclusive_runtime(c, a, b);
    let c_on_cd = point_on_segment_inclusive_runtime(c, c, d);
    let touch1 = c_on_ab && c_on_cd;
    if touch1 {
        proof {
            assert(c_on_ab == point_on_segment_inclusive_spec(c@, a@, b@));
            assert(c_on_cd == point_on_segment_inclusive_spec(c@, c@, d@));
            assert(point_on_both_segments_spec(c@, a@, b@, c@, d@));
        }
        return Option::Some(c.clone());
    }

    let d_on_ab = point_on_segment_inclusive_runtime(d, a, b);
    let d_on_cd = point_on_segment_inclusive_runtime(d, c, d);
    let touch2 = d_on_ab && d_on_cd;
    if touch2 {
        proof {
            assert(d_on_ab == point_on_segment_inclusive_spec(d@, a@, b@));
            assert(d_on_cd == point_on_segment_inclusive_spec(d@, c@, d@));
            assert(point_on_both_segments_spec(d@, a@, b@, c@, d@));
        }
        return Option::Some(d.clone());
    }

    let a_on_ab = point_on_segment_inclusive_runtime(a, a, b);
    let a_on_cd = point_on_segment_inclusive_runtime(a, c, d);
    let touch3 = a_on_ab && a_on_cd;
    if touch3 {
        proof {
            assert(a_on_ab == point_on_segment_inclusive_spec(a@, a@, b@));
            assert(a_on_cd == point_on_segment_inclusive_spec(a@, c@, d@));
            assert(point_on_both_segments_spec(a@, a@, b@, c@, d@));
        }
        return Option::Some(a.clone());
    }

    let b_on_ab = point_on_segment_inclusive_runtime(b, a, b);
    let b_on_cd = point_on_segment_inclusive_runtime(b, c, d);
    let touch4 = b_on_ab && b_on_cd;
    if touch4 {
        proof {
            assert(b_on_ab == point_on_segment_inclusive_spec(b@, a@, b@));
            assert(b_on_cd == point_on_segment_inclusive_spec(b@, c@, d@));
            assert(point_on_both_segments_spec(b@, a@, b@, c@, d@));
        }
        return Option::Some(b.clone());
    }

    proof {
        assert(!touch1);
        assert(!touch2);
        assert(!touch3);
        assert(!touch4);
        assert(c_on_ab == point_on_segment_inclusive_spec(c@, a@, b@));
        assert(c_on_cd == point_on_segment_inclusive_spec(c@, c@, d@));
        assert(d_on_ab == point_on_segment_inclusive_spec(d@, a@, b@));
        assert(d_on_cd == point_on_segment_inclusive_spec(d@, c@, d@));
        assert(a_on_ab == point_on_segment_inclusive_spec(a@, a@, b@));
        assert(a_on_cd == point_on_segment_inclusive_spec(a@, c@, d@));
        assert(b_on_ab == point_on_segment_inclusive_spec(b@, a@, b@));
        assert(b_on_cd == point_on_segment_inclusive_spec(b@, c@, d@));
        assert(!point_on_both_segments_spec(c@, a@, b@, c@, d@));
        assert(!point_on_both_segments_spec(d@, a@, b@, c@, d@));
        assert(!point_on_both_segments_spec(a@, a@, b@, c@, d@));
        assert(!point_on_both_segments_spec(b@, a@, b@, c@, d@));
    }
    Option::None
}

fn proper_intersection_point_runtime(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
    d: &RuntimePoint2,
) -> (out: Option<RuntimePoint2>)
    requires
        wf::point2_wf4_spec(a, b, c, d),
        !b@.sub_spec(a@).cross_spec(d@.sub_spec(c@)).eqv_spec(Scalar::from_int_spec(0)),
    ensures
        out.is_some(),
        match out {
            Option::None => true,
            Option::Some(p) => {
                &&& point_on_segment_supporting_line_spec(p@, a@, b@)
                &&& point_on_segment_supporting_line_spec(p@, c@, d@)
            },
        },
{
    // Line-line intersection parameterization:
    // a + t (b-a), where t = cross(c-a, d-c) / cross(b-a, d-c).
    let r = b.sub(a);
    let s = d.sub(c);
    let den = r.cross(&s);
    let inv_opt = den.recip();
    proof {
        assert(r@ == b@.sub_spec(a@));
        assert(s@ == d@.sub_spec(c@));
        assert(den@ == r@.cross_spec(s@));
        assert(den@ == b@.sub_spec(a@).cross_spec(d@.sub_spec(c@)));
        assert(inv_opt.is_none() == den@.eqv_spec(Scalar::from_int_spec(0)));
        assert(!den@.eqv_spec(Scalar::from_int_spec(0)));
        assert(!inv_opt.is_none());
    }
    let inv = match inv_opt {
        Option::None => {
            proof {
                assert(false);
            }
            return Option::None;
        }
        Option::Some(inv) => inv,
    };
    let cma = c.sub(a);
    let t = cma.cross(&s).mul(&inv);
    let step = r.scale(&t);
    let p = a.add_vec(&step);
    proof {
        let one = Scalar::from_int_spec(1);
        let z = Scalar::from_int_spec(0);
        let pa = p@.sub_spec(a@);

        assert(cma@ == c@.sub_spec(a@));
        assert(t@ == cma@.cross_spec(s@).mul_spec(inv@));
        assert(step@ == r@.scale_spec(t@));

        Point2::lemma_add_then_sub_cancel(a@, step@);
        assert(pa.eqv_spec(step@));

        Vec2::lemma_cross_eqv_congruence(r@, r@, pa, step@);
        assert(r@.cross_spec(pa).eqv_spec(r@.cross_spec(step@)));

        Vec2::lemma_cross_scale_extract_right(r@, r@, t@);
        assert(r@.cross_spec(step@).eqv_spec(t@.mul_spec(r@.cross_spec(r@))));

        Vec2::lemma_cross_self_zero(r@);
        Scalar::lemma_eqv_mul_congruence_right(t@, t@, r@.cross_spec(r@), z);
        assert(t@.mul_spec(r@.cross_spec(r@)).eqv_spec(t@.mul_spec(z)));
        Scalar::lemma_mul_zero(t@);
        assert(t@.mul_spec(z).eqv_spec(z));

        Scalar::lemma_eqv_transitive(
            r@.cross_spec(step@),
            t@.mul_spec(r@.cross_spec(r@)),
            t@.mul_spec(z),
        );
        assert(r@.cross_spec(step@).eqv_spec(t@.mul_spec(z)));
        Scalar::lemma_eqv_transitive(r@.cross_spec(step@), t@.mul_spec(z), z);
        assert(r@.cross_spec(step@).eqv_spec(z));
        Scalar::lemma_eqv_transitive(r@.cross_spec(pa), r@.cross_spec(step@), z);
        assert(r@.cross_spec(pa).eqv_spec(z));

        assert(orient2d_spec(a@, b@, p@) == b@.sub_spec(a@).cross_spec(p@.sub_spec(a@)));
        assert(b@.sub_spec(a@).cross_spec(p@.sub_spec(a@)).eqv_spec(z));
        assert(orient2d_spec(a@, b@, p@).eqv_spec(z));
        Scalar::lemma_eqv_signum(orient2d_spec(a@, b@, p@), z);
        assert(orient2d_spec(a@, b@, p@).signum() == z.signum());
        assert(z.signum() == 0);
        assert(point_on_segment_supporting_line_spec(p@, a@, b@));

        assert(inv_opt == Option::Some(inv));
        assert(match Option::Some(inv) {
            Option::None => true,
            Option::Some(rinv) => {
                &&& den@.mul_spec(rinv@).eqv_spec(one)
                &&& rinv@.mul_spec(den@).eqv_spec(one)
            }
        });
        assert(den@.mul_spec(inv@).eqv_spec(one));
        assert(inv@.mul_spec(den@).eqv_spec(one));

        let cma_cross_s = cma@.cross_spec(s@);
        assert(cma_cross_s.mul_spec(inv@).mul_spec(den@).eqv_spec(cma_cross_s.mul_spec(inv@.mul_spec(den@))))
            by {
                Scalar::lemma_mul_associative(cma_cross_s, inv@, den@);
            };
        assert(t@.mul_spec(den@) == cma_cross_s.mul_spec(inv@).mul_spec(den@));
        assert(t@.mul_spec(den@).eqv_spec(cma_cross_s.mul_spec(inv@.mul_spec(den@))));
        Scalar::lemma_eqv_mul_congruence_right(cma_cross_s, inv@.mul_spec(den@), one);
        assert(cma_cross_s.mul_spec(inv@.mul_spec(den@)).eqv_spec(cma_cross_s.mul_spec(one)));
        Scalar::lemma_mul_one_identity(cma_cross_s);
        assert(cma_cross_s.mul_spec(one) == cma_cross_s);
        Scalar::lemma_eqv_transitive(
            t@.mul_spec(den@),
            cma_cross_s.mul_spec(inv@.mul_spec(den@)),
            cma_cross_s.mul_spec(one),
        );
        assert(t@.mul_spec(den@).eqv_spec(cma_cross_s));

        let pc = p@.sub_spec(c@);
        let ac = a@.sub_spec(c@);
        let pc_rhs = step@.add_spec(cma@.neg_spec());

        Point2::lemma_sub_chain_eqv(p@, a@, c@);
        assert(pc.x.eqv_spec(pa.x.add_spec(ac.x)));
        assert(pc.y.eqv_spec(pa.y.add_spec(ac.y)));
        Point2::lemma_sub_antisymmetric(c@, a@);
        assert(cma@ == ac.neg_spec());
        assert(cma@.neg_spec() == ac.neg_spec().neg_spec());
        Vec2::lemma_neg_involution(ac);
        assert(ac.neg_spec().neg_spec() == ac);
        assert(cma@.neg_spec() == ac);
        assert(pa.eqv_spec(step@));
        Scalar::lemma_eqv_add_congruence(pa.x, step@.x, ac.x, cma@.neg_spec().x);
        Scalar::lemma_eqv_add_congruence(pa.y, step@.y, ac.y, cma@.neg_spec().y);
        assert(pc.x.eqv_spec(step@.x.add_spec(cma@.neg_spec().x)));
        assert(pc.y.eqv_spec(step@.y.add_spec(cma@.neg_spec().y)));
        Vec2::lemma_eqv_from_components(pc, pc_rhs);
        assert(pc.eqv_spec(pc_rhs));

        let s_cross_pc = s@.cross_spec(pc);
        let s_cross_pc_rhs = s@.cross_spec(pc_rhs);
        Vec2::lemma_cross_eqv_congruence(s@, s@, pc, pc_rhs);
        assert(s_cross_pc.eqv_spec(s_cross_pc_rhs));

        Vec2::lemma_cross_linear_right(s@, step@, cma@.neg_spec());
        assert(s_cross_pc_rhs.eqv_spec(s@.cross_spec(step@).add_spec(s@.cross_spec(cma@.neg_spec()))));
        Vec2::lemma_cross_scale_extract_right(s@, r@, t@);
        assert(s@.cross_spec(step@).eqv_spec(t@.mul_spec(s@.cross_spec(r@))));
        Vec2::lemma_cross_antisymmetric(s@, r@);
        assert(s@.cross_spec(r@) == r@.cross_spec(s@).neg_spec());
        assert(s@.cross_spec(r@) == den@.neg_spec());
        Scalar::lemma_eqv_mul_congruence_right(t@, s@.cross_spec(r@), den@.neg_spec());
        assert(t@.mul_spec(s@.cross_spec(r@)).eqv_spec(t@.mul_spec(den@.neg_spec())));
        Scalar::lemma_mul_neg_right(t@, den@);
        assert(t@.mul_spec(den@.neg_spec()) == t@.mul_spec(den@).neg_spec());

        Vec2::lemma_cross_neg_right(s@, cma@);
        assert(s@.cross_spec(cma@.neg_spec()) == s@.cross_spec(cma@).neg_spec());
        Vec2::lemma_cross_antisymmetric(cma@, s@);
        assert(cma@.cross_spec(s@) == s@.cross_spec(cma@).neg_spec());
        assert(s@.cross_spec(cma@.neg_spec()) == cma_cross_s);

        Scalar::lemma_eqv_neg_congruence(t@.mul_spec(den@), cma_cross_s);
        assert(t@.mul_spec(den@).neg_spec().eqv_spec(cma_cross_s.neg_spec()));
        Scalar::lemma_eqv_add_congruence(
            t@.mul_spec(den@).neg_spec(),
            cma_cross_s.neg_spec(),
            s@.cross_spec(cma@.neg_spec()),
            cma_cross_s,
        );
        assert(
            t@.mul_spec(den@).neg_spec().add_spec(s@.cross_spec(cma@.neg_spec()))
                .eqv_spec(cma_cross_s.neg_spec().add_spec(cma_cross_s)),
        );
        Scalar::lemma_add_inverse(cma_cross_s);
        assert(cma_cross_s.neg_spec().add_spec(cma_cross_s).eqv_spec(z));
        Scalar::lemma_eqv_transitive(
            t@.mul_spec(den@).neg_spec().add_spec(s@.cross_spec(cma@.neg_spec())),
            cma_cross_s.neg_spec().add_spec(cma_cross_s),
            z,
        );
        assert(t@.mul_spec(den@).neg_spec().add_spec(s@.cross_spec(cma@.neg_spec())).eqv_spec(z));
        Scalar::lemma_eqv_add_congruence(
            s@.cross_spec(step@),
            t@.mul_spec(den@).neg_spec(),
            s@.cross_spec(cma@.neg_spec()),
            s@.cross_spec(cma@.neg_spec()),
        );
        assert(
            s@.cross_spec(step@).add_spec(s@.cross_spec(cma@.neg_spec()))
                .eqv_spec(t@.mul_spec(den@).neg_spec().add_spec(s@.cross_spec(cma@.neg_spec()))),
        );
        Scalar::lemma_eqv_transitive(
            s@.cross_spec(step@).add_spec(s@.cross_spec(cma@.neg_spec())),
            t@.mul_spec(den@).neg_spec().add_spec(s@.cross_spec(cma@.neg_spec())),
            z,
        );
        assert(s@.cross_spec(step@).add_spec(s@.cross_spec(cma@.neg_spec())).eqv_spec(z));
        Scalar::lemma_eqv_transitive(
            s_cross_pc,
            s_cross_pc_rhs,
            s@.cross_spec(step@).add_spec(s@.cross_spec(cma@.neg_spec())),
        );
        Scalar::lemma_eqv_transitive(
            s_cross_pc,
            s@.cross_spec(step@).add_spec(s@.cross_spec(cma@.neg_spec())),
            z,
        );
        assert(s_cross_pc.eqv_spec(z));

        assert(orient2d_spec(c@, d@, p@) == d@.sub_spec(c@).cross_spec(p@.sub_spec(c@)));
        assert(d@.sub_spec(c@) == s@);
        assert(p@.sub_spec(c@) == pc);
        assert(orient2d_spec(c@, d@, p@) == s_cross_pc);
        assert(orient2d_spec(c@, d@, p@).eqv_spec(z));
        Scalar::lemma_eqv_signum(orient2d_spec(c@, d@, p@), z);
        assert(orient2d_spec(c@, d@, p@).signum() == z.signum());
        assert(point_on_segment_supporting_line_spec(p@, c@, d@));
    }
    Option::Some(p)
}

pub fn segment_intersection_kind_2d(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
    d: &RuntimePoint2,
) -> (out: SegmentIntersection2dKind)
    requires
        wf::point2_wf4_spec(a, b, c, d),
    ensures
        out@ == segment_intersection_kind_spec(a@, b@, c@, d@),
{
    let o1 = orient2d_sign(a, b, c);
    let o2 = orient2d_sign(a, b, d);
    let o3 = orient2d_sign(c, d, a);
    let o4 = orient2d_sign(c, d, b);
    let touch1 = point_on_segment_inclusive_runtime(c, a, b)
        && point_on_segment_inclusive_runtime(c, c, d);
    let touch2 = point_on_segment_inclusive_runtime(d, a, b)
        && point_on_segment_inclusive_runtime(d, c, d);
    let touch3 = point_on_segment_inclusive_runtime(a, a, b)
        && point_on_segment_inclusive_runtime(a, c, d);
    let touch4 = point_on_segment_inclusive_runtime(b, a, b)
        && point_on_segment_inclusive_runtime(b, c, d);

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
        } else if overlap_kind == 0 && (touch1 || touch2 || touch3 || touch4) {
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
                assert(touch1 == point_on_both_segments_spec(c@, a@, b@, c@, d@));
                assert(touch2 == point_on_both_segments_spec(d@, a@, b@, c@, d@));
                assert(touch3 == point_on_both_segments_spec(a@, a@, b@, c@, d@));
                assert(touch4 == point_on_both_segments_spec(b@, a@, b@, c@, d@));
                assert(touch1 || touch2 || touch3 || touch4);
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
                assert(touch1 == point_on_both_segments_spec(c@, a@, b@, c@, d@));
                assert(touch2 == point_on_both_segments_spec(d@, a@, b@, c@, d@));
                assert(touch3 == point_on_both_segments_spec(a@, a@, b@, c@, d@));
                assert(touch4 == point_on_both_segments_spec(b@, a@, b@, c@, d@));
                assert(!(overlap_kind as int < 0));
                assert(!((overlap_kind as int == 0) && (touch1 || touch2 || touch3 || touch4)));
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
            assert(touch1 == point_on_both_segments_spec(c@, a@, b@, c@, d@));
            assert(touch2 == point_on_both_segments_spec(d@, a@, b@, c@, d@));
            assert(touch3 == point_on_both_segments_spec(a@, a@, b@, c@, d@));
            assert(touch4 == point_on_both_segments_spec(b@, a@, b@, c@, d@));
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

pub fn segment_intersection_point_2d(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
    d: &RuntimePoint2,
) -> (out: Option<RuntimePoint2>)
    requires
        wf::point2_wf4_spec(a, b, c, d),
    ensures
        (segment_intersection_kind_spec(a@, b@, c@, d@) is Disjoint) ==> out.is_none(),
        (segment_intersection_kind_spec(a@, b@, c@, d@) is CollinearOverlap) ==> out.is_none(),
        (segment_intersection_kind_spec(a@, b@, c@, d@) is Proper) ==> out.is_some(),
        (segment_intersection_kind_spec(a@, b@, c@, d@) is EndpointTouch) ==> out.is_some(),
        (segment_intersection_kind_spec(a@, b@, c@, d@) is Proper) ==> match out {
            Option::None => true,
            Option::Some(p) => point_on_segment_supporting_line_spec(p@, a@, b@),
        },
        (segment_intersection_kind_spec(a@, b@, c@, d@) is Proper) ==> match out {
            Option::None => true,
            Option::Some(p) => point_on_segment_supporting_line_spec(p@, c@, d@),
        },
        (segment_intersection_kind_spec(a@, b@, c@, d@) is EndpointTouch) ==> match out {
            Option::None => true,
            Option::Some(p) => point_on_both_segments_spec(p@, a@, b@, c@, d@),
        },
{
    let kind = segment_intersection_kind_2d(a, b, c, d);
    match kind {
        SegmentIntersection2dKind::Proper => {
            proof {
                assert(kind@ is Proper);
                assert(segment_intersection_kind_spec(a@, b@, c@, d@) is Proper);
                lemma_segment_intersection_kind_spec_proper_implies_straddling_signs(a@, b@, c@, d@);
                lemma_proper_straddling_implies_nonzero_direction_cross(a@, b@, c@, d@);
                assert(!b@.sub_spec(a@).cross_spec(d@.sub_spec(c@)).eqv_spec(Scalar::from_int_spec(0)));
            }
            let out = proper_intersection_point_runtime(a, b, c, d);
            proof {
                assert(out.is_some());
                match &out {
                    Option::None => {}
                    Option::Some(p) => {
                        assert(point_on_segment_supporting_line_spec(p@, a@, b@));
                        assert(point_on_segment_supporting_line_spec(p@, c@, d@));
                    }
                }
            }
            out
        }
        SegmentIntersection2dKind::EndpointTouch => {
            let out = endpoint_touch_point_runtime(a, b, c, d);
            proof {
                assert(kind@ is EndpointTouch);
                assert(segment_intersection_kind_spec(a@, b@, c@, d@) is EndpointTouch);
                assert(
                    point_on_both_segments_spec(c@, a@, b@, c@, d@)
                        || point_on_both_segments_spec(d@, a@, b@, c@, d@)
                        || point_on_both_segments_spec(a@, a@, b@, c@, d@)
                        || point_on_both_segments_spec(b@, a@, b@, c@, d@),
                );
                assert(out.is_some());
                match &out {
                    Option::None => {}
                    Option::Some(p) => {
                        assert(point_on_both_segments_spec(p@, a@, b@, c@, d@));
                    }
                }
            }
            out
        }
        SegmentIntersection2dKind::Disjoint => {
            proof {
                assert(kind@ is Disjoint);
                assert(segment_intersection_kind_spec(a@, b@, c@, d@) is Disjoint);
            }
            Option::None
        }
        SegmentIntersection2dKind::CollinearOverlap => {
            proof {
                assert(kind@ is CollinearOverlap);
                assert(segment_intersection_kind_spec(a@, b@, c@, d@) is CollinearOverlap);
            }
            Option::None
        }
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
    fn segment_intersection_proper_witness_lies_on_both_segments_non_integer() {
        let a = RuntimePoint2::from_ints(0, 0);
        let b = RuntimePoint2::from_ints(4, 4);
        let c = RuntimePoint2::from_ints(1, 4);
        let d = RuntimePoint2::from_ints(5, 0);

        assert_eq!(
            segment_intersection_kind_2d(&a, &b, &c, &d),
            SegmentIntersection2dKind::Proper
        );

        let p = segment_intersection_point_2d(&a, &b, &c, &d).expect("proper intersection point");
        assert!(point_on_segment_inclusive_runtime(&p, &a, &b));
        assert!(point_on_segment_inclusive_runtime(&p, &c, &d));
    }

    #[test]
    fn segment_intersection_proper_witness_lies_on_both_segments_axis_mixed() {
        let a = RuntimePoint2::from_ints(-3, 1);
        let b = RuntimePoint2::from_ints(3, 1);
        let c = RuntimePoint2::from_ints(-1, -2);
        let d = RuntimePoint2::from_ints(2, 4);

        assert_eq!(
            segment_intersection_kind_2d(&a, &b, &c, &d),
            SegmentIntersection2dKind::Proper
        );

        let p = segment_intersection_point_2d(&a, &b, &c, &d).expect("proper intersection point");
        assert!(point_on_segment_inclusive_runtime(&p, &a, &b));
        assert!(point_on_segment_inclusive_runtime(&p, &c, &d));
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
    fn segment_intersection_collinear_endpoint_touch_has_witness() {
        let a = RuntimePoint2::from_ints(0, 0);
        let b = RuntimePoint2::from_ints(2, 0);
        let c = RuntimePoint2::from_ints(2, 0);
        let d = RuntimePoint2::from_ints(5, 0);

        assert_eq!(
            segment_intersection_kind_2d(&a, &b, &c, &d),
            SegmentIntersection2dKind::EndpointTouch
        );

        let p = segment_intersection_point_2d(&a, &b, &c, &d).expect("collinear endpoint witness");
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
