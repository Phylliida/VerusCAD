#![cfg(feature = "verus-proofs")]

use crate::sidedness;
use vcad_math::orientation3::{orientation3_spec, Orientation3};
use vcad_math::point3::Point3;
use vcad_math::runtime_point3::RuntimePoint3;
use vcad_math::runtime_scalar::RuntimeScalar;
use vcad_math::scalar::Scalar;
use vstd::prelude::*;

verus! {

pub open spec fn strict_opposite_sides_spec(a: Point3, b: Point3, c: Point3, d: Point3, e: Point3) -> bool {
    ((orientation3_spec(a, b, c, d) is Positive) && (orientation3_spec(a, b, c, e) is Negative))
        || ((orientation3_spec(a, b, c, d) is Negative) && (orientation3_spec(a, b, c, e) is Positive))
}

pub open spec fn base_plane_noncollinear3_spec(a: Point3, b: Point3, c: Point3) -> bool {
    let n = b.sub_spec(a).cross_spec(c.sub_spec(a));
    !(n.x.signum() == 0 && n.y.signum() == 0 && n.z.signum() == 0)
}

/// Signed side value of `d` with respect to oriented plane `(a,b,c)`,
/// using the plane normal `n = (b-a) x (c-a)`.
pub open spec fn signed_plane_side_value_spec(a: Point3, b: Point3, c: Point3, d: Point3) -> Scalar {
    d.sub_spec(a).dot_spec(b.sub_spec(a).cross_spec(c.sub_spec(a)))
}

/// Geometric "positive side of plane (a,b,c)" meaning, under non-collinear base.
pub open spec fn point_on_positive_side_of_plane_spec(a: Point3, b: Point3, c: Point3, d: Point3) -> bool {
    Scalar::from_int_spec(0).lt_spec(signed_plane_side_value_spec(a, b, c, d))
}

proof fn lemma_orient3d_matches_signed_plane_side_value(a: Point3, b: Point3, c: Point3, d: Point3)
    ensures
        vcad_math::orientation3::orient3d_spec(a, b, c, d).eqv_spec(signed_plane_side_value_spec(a, b, c, d)),
{
    let ba = b.sub_spec(a);
    let ca = c.sub_spec(a);
    let da = d.sub_spec(a);
    let det = vcad_math::orientation3::orient3d_spec(a, b, c, d);
    let side = signed_plane_side_value_spec(a, b, c, d);

    assert(det == ba.dot_spec(ca.cross_spec(da)));
    assert(side == da.dot_spec(ba.cross_spec(ca)));
    vcad_math::vec3::Vec3::lemma_dot_cross_cyclic(da, ba, ca);
    assert(da.dot_spec(ba.cross_spec(ca)).eqv_spec(ba.dot_spec(ca.cross_spec(da))));
    assert(side.eqv_spec(det));
}

proof fn lemma_scalar_gt_zero_iff_signum_one(s: Scalar)
    ensures
        Scalar::from_int_spec(0).lt_spec(s) == (s.signum() == 1),
{
    let z = Scalar::from_int_spec(0);
    assert(z.lt_spec(s) == (z.num * s.denom() < s.num * z.denom()));
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(z.lt_spec(s) == (0 * s.denom() < s.num * 1));
    assert(0 * s.denom() == 0) by (nonlinear_arith);
    assert(s.num * 1 == s.num) by (nonlinear_arith);
    assert(z.lt_spec(s) == (0 < s.num));
    if s.num > 0 {
        assert(s.signum() == 1);
    } else if s.num < 0 {
        assert(s.signum() == -1);
    } else {
        assert(s.num == 0);
        assert(s.signum() == 0);
    }
    assert((s.signum() == 1) == (s.num > 0));
    assert((0 < s.num) == (s.num > 0));
    assert(z.lt_spec(s) == (s.signum() == 1));
}

proof fn lemma_orient3d_positive_iff_positive_side_noncollinear(a: Point3, b: Point3, c: Point3, d: Point3)
    requires
        base_plane_noncollinear3_spec(a, b, c),
    ensures
        Scalar::from_int_spec(0).lt_spec(vcad_math::orientation3::orient3d_spec(a, b, c, d))
            == point_on_positive_side_of_plane_spec(a, b, c, d),
{
    let det = vcad_math::orientation3::orient3d_spec(a, b, c, d);
    let side = signed_plane_side_value_spec(a, b, c, d);
    vcad_math::orientation3::lemma_orientation3_spec_matches_predicates(a, b, c, d);
    lemma_orient3d_matches_signed_plane_side_value(a, b, c, d);
    Scalar::lemma_eqv_signum(det, side);
    lemma_scalar_gt_zero_iff_signum_one(det);
    lemma_scalar_gt_zero_iff_signum_one(side);
    assert((orientation3_spec(a, b, c, d) is Positive) == (det.signum() == 1));
    assert(Scalar::from_int_spec(0).lt_spec(det) == (det.signum() == 1));
    assert((det.signum() == 1) == (side.signum() == 1));
    assert(Scalar::from_int_spec(0).lt_spec(side) == (side.signum() == 1));
    assert(Scalar::from_int_spec(0).lt_spec(det) == Scalar::from_int_spec(0).lt_spec(side));
    assert(base_plane_noncollinear3_spec(a, b, c));
    assert(point_on_positive_side_of_plane_spec(a, b, c, d) == Scalar::from_int_spec(0).lt_spec(side));
    assert(Scalar::from_int_spec(0).lt_spec(det) == point_on_positive_side_of_plane_spec(a, b, c, d));
}

pub open spec fn segment_plane_orient_d_spec(a: Point3, b: Point3, c: Point3, d: Point3) -> Scalar {
    vcad_math::orientation3::orient3d_spec(a, b, c, d)
}

pub open spec fn segment_plane_orient_e_spec(a: Point3, b: Point3, c: Point3, e: Point3) -> Scalar {
    vcad_math::orientation3::orient3d_spec(a, b, c, e)
}

pub open spec fn segment_plane_denom_spec(a: Point3, b: Point3, c: Point3, d: Point3, e: Point3) -> Scalar {
    segment_plane_orient_d_spec(a, b, c, d).sub_spec(segment_plane_orient_e_spec(a, b, c, e))
}

pub open spec fn segment_plane_t_valid_spec(t: Scalar, a: Point3, b: Point3, c: Point3, d: Point3, e: Point3) -> bool {
    let od = segment_plane_orient_d_spec(a, b, c, d);
    let oe = segment_plane_orient_e_spec(a, b, c, e);
    let den = segment_plane_denom_spec(a, b, c, d, e);
    let one = Scalar::from_int_spec(1);
    &&& t.mul_spec(den).eqv_spec(od)
    &&& one.sub_spec(t).mul_spec(den).eqv_spec(oe.neg_spec())
    &&& den.signum() == od.signum()
}

pub open spec fn segment_plane_point_at_parameter_spec(p: Point3, t: Scalar, d: Point3, e: Point3) -> bool {
    p.eqv_spec(d.add_vec_spec(e.sub_spec(d).scale_spec(t)))
}

pub assume_specification[ sidedness::point_above_plane ](
    p: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: bool)
    ensures
        out == (orientation3_spec(a@, b@, c@, p@) is Positive),
;

pub assume_specification[ sidedness::point_below_plane ](
    p: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: bool)
    ensures
        out == (orientation3_spec(a@, b@, c@, p@) is Negative),
;

pub assume_specification[ sidedness::point_on_plane ](
    p: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: bool)
    ensures
        out == (orientation3_spec(a@, b@, c@, p@) is Coplanar),
;

pub assume_specification[ sidedness::segment_crosses_plane_strict ](
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: bool)
    ensures
        out == strict_opposite_sides_spec(a@, b@, c@, d@, e@),
;

pub assume_specification[ sidedness::segment_plane_intersection_parameter_strict ](
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: Option<RuntimeScalar>)
    ensures
        out.is_some() == strict_opposite_sides_spec(a@, b@, c@, d@, e@),
        match out {
            Option::None => true,
            Option::Some(t) => segment_plane_t_valid_spec(t@, a@, b@, c@, d@, e@),
        },
;

pub assume_specification[ sidedness::segment_plane_intersection_point_strict ](
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: Option<RuntimePoint3>)
    ensures
        out.is_some() == strict_opposite_sides_spec(a@, b@, c@, d@, e@),
        match out {
            Option::None => true,
            Option::Some(p) => exists|t: Scalar| {
                &&& segment_plane_t_valid_spec(t, a@, b@, c@, d@, e@)
                &&& segment_plane_point_at_parameter_spec(p@, t, d@, e@)
            },
        },
;

proof fn lemma_signum_one_implies_num_positive(s: Scalar)
    requires
        s.signum() == 1,
    ensures
        s.num > 0,
{
    if s.num > 0 {
    } else if s.num < 0 {
        assert(s.signum() == -1);
        assert(false);
    } else {
        assert(s.num == 0);
        assert(s.signum() == 0);
        assert(false);
    }
}

proof fn lemma_signum_minus_one_implies_num_negative(s: Scalar)
    requires
        s.signum() == -1,
    ensures
        s.num < 0,
{
    if s.num < 0 {
    } else if s.num > 0 {
        assert(s.signum() == 1);
        assert(false);
    } else {
        assert(s.num == 0);
        assert(s.signum() == 0);
        assert(false);
    }
}

proof fn lemma_num_positive_implies_signum_one(s: Scalar)
    requires
        s.num > 0,
    ensures
        s.signum() == 1,
{
    assert(s.signum() == 1);
}

proof fn lemma_num_negative_implies_signum_minus_one(s: Scalar)
    requires
        s.num < 0,
    ensures
        s.signum() == -1,
{
    assert(s.signum() == -1);
}

proof fn lemma_strict_crossing_parameter_open_unit_interval(a: Point3, b: Point3, c: Point3, d: Point3, e: Point3, t: Scalar)
    requires
        strict_opposite_sides_spec(a, b, c, d, e),
        segment_plane_t_valid_spec(t, a, b, c, d, e),
    ensures
        Scalar::from_int_spec(0).lt_spec(t),
        t.lt_spec(Scalar::from_int_spec(1)),
{
    let z = Scalar::from_int_spec(0);
    let one = Scalar::from_int_spec(1);
    let od = segment_plane_orient_d_spec(a, b, c, d);
    let oe = segment_plane_orient_e_spec(a, b, c, e);
    let den = segment_plane_denom_spec(a, b, c, d, e);
    let one_minus_t = one.sub_spec(t);

    vcad_math::orientation3::lemma_orientation3_spec_matches_predicates(a, b, c, d);
    vcad_math::orientation3::lemma_orientation3_spec_matches_predicates(a, b, c, e);
    Scalar::lemma_signum_mul(t, den);
    Scalar::lemma_signum_mul(one_minus_t, den);
    Scalar::lemma_signum_negate(oe);
    Scalar::lemma_eqv_signum(t.mul_spec(den), od);
    Scalar::lemma_eqv_signum(one_minus_t.mul_spec(den), oe.neg_spec());
    assert((orientation3_spec(a, b, c, d) is Positive) == (od.signum() == 1));
    assert((orientation3_spec(a, b, c, d) is Negative) == (od.signum() == -1));
    assert((orientation3_spec(a, b, c, e) is Positive) == (oe.signum() == 1));
    assert((orientation3_spec(a, b, c, e) is Negative) == (oe.signum() == -1));
    assert(den.signum() == od.signum());

    if (orientation3_spec(a, b, c, d) is Positive) && (orientation3_spec(a, b, c, e) is Negative) {
        assert(od.signum() == 1);
        assert(oe.signum() == -1);
        lemma_signum_one_implies_num_positive(od);
        lemma_signum_minus_one_implies_num_negative(oe);
        assert(den.signum() == 1);

        assert(t.mul_spec(den).signum() == od.signum());
        assert(t.mul_spec(den).signum() == t.signum() * den.signum());
        assert(t.signum() * den.signum() == od.signum());
        assert(t.signum() * 1 == 1);
        Scalar::lemma_signum_cases(t);
        if t.signum() == 1 {
        } else if t.signum() == -1 {
            assert(t.signum() * 1 == -1);
            assert(false);
        } else {
            assert(t.signum() == 0);
            assert(t.signum() * 1 == 0);
            assert(false);
        }
        lemma_signum_one_implies_num_positive(t);

        assert(oe.neg_spec().signum() == -oe.signum());
        assert(oe.neg_spec().signum() == 1);
        assert(one_minus_t.mul_spec(den).signum() == oe.neg_spec().signum());
        assert(one_minus_t.mul_spec(den).signum() == one_minus_t.signum() * den.signum());
        assert(one_minus_t.signum() * den.signum() == oe.neg_spec().signum());
        assert(one_minus_t.signum() * 1 == 1);
        Scalar::lemma_signum_cases(one_minus_t);
        if one_minus_t.signum() == 1 {
        } else if one_minus_t.signum() == -1 {
            assert(one_minus_t.signum() * 1 == -1);
            assert(false);
        } else {
            assert(one_minus_t.signum() == 0);
            assert(one_minus_t.signum() * 1 == 0);
            assert(false);
        }
        lemma_signum_one_implies_num_positive(one_minus_t);
    } else {
        assert((orientation3_spec(a, b, c, d) is Negative) && (orientation3_spec(a, b, c, e) is Positive));
        assert(od.signum() == -1);
        assert(oe.signum() == 1);
        lemma_signum_minus_one_implies_num_negative(od);
        lemma_signum_one_implies_num_positive(oe);
        assert(den.signum() == -1);

        assert(t.mul_spec(den).signum() == od.signum());
        assert(t.mul_spec(den).signum() == t.signum() * den.signum());
        assert(t.signum() * den.signum() == od.signum());
        assert(t.signum() * (-1) == -1);
        Scalar::lemma_signum_cases(t);
        if t.signum() == 1 {
        } else if t.signum() == -1 {
            assert(t.signum() * (-1) == 1);
            assert(false);
        } else {
            assert(t.signum() == 0);
            assert(t.signum() * (-1) == 0);
            assert(false);
        }
        lemma_signum_one_implies_num_positive(t);

        assert(oe.neg_spec().signum() == -oe.signum());
        assert(oe.neg_spec().signum() == -1);
        assert(one_minus_t.mul_spec(den).signum() == oe.neg_spec().signum());
        assert(one_minus_t.mul_spec(den).signum() == one_minus_t.signum() * den.signum());
        assert(one_minus_t.signum() * den.signum() == oe.neg_spec().signum());
        assert(one_minus_t.signum() * (-1) == -1);
        Scalar::lemma_signum_cases(one_minus_t);
        if one_minus_t.signum() == 1 {
        } else if one_minus_t.signum() == -1 {
            assert(one_minus_t.signum() * (-1) == 1);
            assert(false);
        } else {
            assert(one_minus_t.signum() == 0);
            assert(one_minus_t.signum() * (-1) == 0);
            assert(false);
        }
        lemma_signum_one_implies_num_positive(one_minus_t);
    }

    assert(t.signum() == 1);
    assert(one_minus_t.signum() == 1);
    lemma_signum_one_implies_num_positive(t);
    lemma_signum_one_implies_num_positive(one_minus_t);

    assert(z.lt_spec(t) == (z.num * t.denom() < t.num * z.denom()));
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(z.num * t.denom() == 0 * t.denom());
    assert(t.num * z.denom() == t.num * 1);
    assert(0 * t.denom() == 0) by (nonlinear_arith);
    assert(t.num > 0);
    assert((t.num > 0) ==> (0 * t.denom() < t.num * 1)) by (nonlinear_arith);
    assert(0 * t.denom() < t.num * 1);
    assert(z.lt_spec(t));

    assert(one_minus_t == one.sub_spec(t));
    assert(one_minus_t == one.add_spec(t.neg_spec()));
    assert(one_minus_t.num == one.num * t.neg_spec().denom() + t.neg_spec().num * one.denom());
    assert(t.neg_spec().denom() == t.denom());
    assert(t.neg_spec().num == -t.num);
    assert(one.num == 1);
    assert(one.denom() == 1);
    assert(one_minus_t.num == 1 * t.denom() + (-t.num) * 1);
    assert(1 * t.denom() + (-t.num) * 1 == t.denom() - t.num) by (nonlinear_arith);
    assert(one_minus_t.num == t.denom() - t.num);
    assert(one_minus_t.num > 0);
    assert((one_minus_t.num > 0 && one_minus_t.num == t.denom() - t.num) ==> (t.num < t.denom())) by (nonlinear_arith);
    assert(t.num < t.denom());
    assert(t.lt_spec(one) == (t.num * one.denom() < one.num * t.denom()));
    assert(t.num * one.denom() == t.num * 1);
    assert(one.num * t.denom() == 1 * t.denom());
    assert((t.num < t.denom()) ==> (t.num * 1 < 1 * t.denom())) by (nonlinear_arith);
    assert(t.num * 1 < 1 * t.denom());
    assert(t.lt_spec(one));
}

#[allow(dead_code)]
pub fn runtime_plane_side_partition(
    p: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (triple: (bool, bool, bool))
    ensures
        triple.0 == (orientation3_spec(a@, b@, c@, p@) is Positive),
        triple.1 == (orientation3_spec(a@, b@, c@, p@) is Negative),
        triple.2 == (orientation3_spec(a@, b@, c@, p@) is Coplanar),
        triple.0 || triple.1 || triple.2,
        !(triple.0 && triple.1),
        !(triple.0 && triple.2),
        !(triple.1 && triple.2),
{
    let above = sidedness::point_above_plane(p, a, b, c);
    let below = sidedness::point_below_plane(p, a, b, c);
    let on = sidedness::point_on_plane(p, a, b, c);
    proof {
        vcad_math::orientation3::lemma_orientation3_spec_exclusive(a@, b@, c@, p@);
    }
    (above, below, on)
}

#[allow(dead_code)]
pub fn runtime_orient3d_positive_iff_point_above_noncollinear(
    d: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: bool)
    requires
        base_plane_noncollinear3_spec(a@, b@, c@),
    ensures
        out == point_on_positive_side_of_plane_spec(a@, b@, c@, d@),
        Scalar::from_int_spec(0).lt_spec(vcad_math::orientation3::orient3d_spec(a@, b@, c@, d@))
            == point_on_positive_side_of_plane_spec(a@, b@, c@, d@),
{
    let out = sidedness::point_above_plane(d, a, b, c);
    proof {
        lemma_orient3d_positive_iff_positive_side_noncollinear(a@, b@, c@, d@);
        assert(out == (orientation3_spec(a@, b@, c@, d@) is Positive));
        lemma_scalar_gt_zero_iff_signum_one(vcad_math::orientation3::orient3d_spec(a@, b@, c@, d@));
        assert(
            Scalar::from_int_spec(0).lt_spec(vcad_math::orientation3::orient3d_spec(a@, b@, c@, d@))
                == (orientation3_spec(a@, b@, c@, d@) is Positive)
        );
        assert(base_plane_noncollinear3_spec(a@, b@, c@));
        assert(
            point_on_positive_side_of_plane_spec(a@, b@, c@, d@)
                == Scalar::from_int_spec(0).lt_spec(vcad_math::orientation3::orient3d_spec(a@, b@, c@, d@))
        );
        assert(out == point_on_positive_side_of_plane_spec(a@, b@, c@, d@));
    }
    out
}

#[allow(dead_code)]
pub fn runtime_segment_crosses_plane_from_opposite_sides(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: bool)
    requires
        (orientation3_spec(a@, b@, c@, d@) is Positive),
        (orientation3_spec(a@, b@, c@, e@) is Negative),
    ensures
        out,
{
    let out = sidedness::segment_crosses_plane_strict(d, e, a, b, c);
    proof {
        assert(strict_opposite_sides_spec(a@, b@, c@, d@, e@));
    }
    out
}

#[allow(dead_code)]
pub fn runtime_segment_crosses_plane_from_opposite_sides_swapped(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: bool)
    requires
        (orientation3_spec(a@, b@, c@, d@) is Negative),
        (orientation3_spec(a@, b@, c@, e@) is Positive),
    ensures
        out,
{
    let out = sidedness::segment_crosses_plane_strict(d, e, a, b, c);
    proof {
        assert(strict_opposite_sides_spec(a@, b@, c@, d@, e@));
    }
    out
}

#[allow(dead_code)]
pub fn runtime_segment_crossing_implies_not_on_plane_endpoints(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (triple: (bool, bool, bool))
    ensures
        triple.0 == strict_opposite_sides_spec(a@, b@, c@, d@, e@),
        triple.1 == (orientation3_spec(a@, b@, c@, d@) is Coplanar),
        triple.2 == (orientation3_spec(a@, b@, c@, e@) is Coplanar),
        triple.0 ==> !triple.1,
        triple.0 ==> !triple.2,
{
    let crosses = sidedness::segment_crosses_plane_strict(d, e, a, b, c);
    let d_on = sidedness::point_on_plane(d, a, b, c);
    let e_on = sidedness::point_on_plane(e, a, b, c);
    proof {
        if crosses {
            assert((orientation3_spec(a@, b@, c@, d@) is Positive) || (orientation3_spec(a@, b@, c@, d@) is Negative));
            assert((orientation3_spec(a@, b@, c@, e@) is Positive) || (orientation3_spec(a@, b@, c@, e@) is Negative));
            assert(!(orientation3_spec(a@, b@, c@, d@) is Coplanar));
            assert(!(orientation3_spec(a@, b@, c@, e@) is Coplanar));
        }
    }
    (crosses, d_on, e_on)
}

#[allow(dead_code)]
pub fn runtime_crossing_implies_intersection_parameter_exists(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: Option<RuntimeScalar>)
    requires
        strict_opposite_sides_spec(a@, b@, c@, d@, e@),
    ensures
        out.is_some(),
{
    let out = sidedness::segment_plane_intersection_parameter_strict(d, e, a, b, c);
    out
}

#[allow(dead_code)]
pub fn runtime_crossing_parameter_open_unit_interval(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: Option<RuntimeScalar>)
    requires
        strict_opposite_sides_spec(a@, b@, c@, d@, e@),
    ensures
        out.is_some(),
        match out {
            Option::None => true,
            Option::Some(t) => {
                &&& Scalar::from_int_spec(0).lt_spec(t@)
                &&& t@.lt_spec(Scalar::from_int_spec(1))
            },
        },
{
    let out = sidedness::segment_plane_intersection_parameter_strict(d, e, a, b, c);
    proof {
        assert(out.is_some());
        match out {
            Option::None => {
                assert(false);
            }
            Option::Some(ref t) => {
                lemma_strict_crossing_parameter_open_unit_interval(a@, b@, c@, d@, e@, t@);
            }
        }
    }
    out
}

#[allow(dead_code)]
pub fn runtime_crossing_implies_intersection_point_has_parameter(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: Option<RuntimePoint3>)
    requires
        strict_opposite_sides_spec(a@, b@, c@, d@, e@),
    ensures
        out.is_some(),
        match out {
            Option::None => true,
            Option::Some(p) => exists|t: Scalar| {
                &&& segment_plane_t_valid_spec(t, a@, b@, c@, d@, e@)
                &&& segment_plane_point_at_parameter_spec(p@, t, d@, e@)
            },
        },
{
    let out = sidedness::segment_plane_intersection_point_strict(d, e, a, b, c);
    out
}

#[allow(dead_code)]
pub fn runtime_no_crossing_implies_no_intersection_parameter(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: Option<RuntimeScalar>)
    requires
        !strict_opposite_sides_spec(a@, b@, c@, d@, e@),
    ensures
        out.is_none(),
{
    let out = sidedness::segment_plane_intersection_parameter_strict(d, e, a, b, c);
    out
}

} // verus!
