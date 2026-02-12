use vstd::prelude::*;
use crate::scalar::Scalar;
use crate::point2::Point2;

verus! {

#[derive(Structural, PartialEq, Eq)]
pub enum Orientation {
    Cw,
    Collinear,
    Ccw,
}

pub open spec fn orient2d_spec(a: Point2, b: Point2, c: Point2) -> Scalar {
    b.sub_spec(a).cross_spec(c.sub_spec(a))
}

pub open spec fn is_ccw(a: Point2, b: Point2, c: Point2) -> bool {
    orient2d_spec(a, b, c).signum() == 1
}

pub open spec fn is_cw(a: Point2, b: Point2, c: Point2) -> bool {
    orient2d_spec(a, b, c).signum() == -1
}

pub open spec fn is_collinear(a: Point2, b: Point2, c: Point2) -> bool {
    orient2d_spec(a, b, c).signum() == 0
}

pub open spec fn orientation_spec(a: Point2, b: Point2, c: Point2) -> Orientation {
    let s = orient2d_spec(a, b, c).signum();
    if s == 1 {
        Orientation::Ccw
    } else if s == -1 {
        Orientation::Cw
    } else {
        Orientation::Collinear
    }
}

pub proof fn orient2d(a: Point2, b: Point2, c: Point2) -> (out: Scalar)
    ensures
        out == orient2d_spec(a, b, c),
{
    let ba = b.sub(a);
    let ca = c.sub(a);
    ba.cross(ca)
}

pub proof fn orientation(a: Point2, b: Point2, c: Point2) -> (o: Orientation)
    ensures
        o == orientation_spec(a, b, c),
{
    let s = orient2d_spec(a, b, c).signum();
    if s == 1 {
        Orientation::Ccw
    } else if s == -1 {
        Orientation::Cw
    } else {
        Orientation::Collinear
    }
}

pub proof fn lemma_is_ccw_iff_positive(a: Point2, b: Point2, c: Point2)
    ensures
        is_ccw(a, b, c) == (orient2d_spec(a, b, c).num > 0),
{
    let det = orient2d_spec(a, b, c);
    Scalar::lemma_signum_positive_iff(det);
    assert(is_ccw(a, b, c) == (det.signum() == 1));
    assert((det.signum() == 1) == (det.num > 0));
}

pub proof fn lemma_is_cw_iff_negative(a: Point2, b: Point2, c: Point2)
    ensures
        is_cw(a, b, c) == (orient2d_spec(a, b, c).num < 0),
{
    let det = orient2d_spec(a, b, c);
    Scalar::lemma_signum_negative_iff(det);
    assert(is_cw(a, b, c) == (det.signum() == -1));
    assert((det.signum() == -1) == (det.num < 0));
}

pub proof fn lemma_is_collinear_iff_zero(a: Point2, b: Point2, c: Point2)
    ensures
        is_collinear(a, b, c) == (orient2d_spec(a, b, c).num == 0),
{
    let det = orient2d_spec(a, b, c);
    Scalar::lemma_signum_zero_iff(det);
    assert(is_collinear(a, b, c) == (det.signum() == 0));
    assert((det.signum() == 0) == (det.num == 0));
}

pub proof fn lemma_orientation_classes_exhaustive(a: Point2, b: Point2, c: Point2)
    ensures
        is_ccw(a, b, c) || is_cw(a, b, c) || is_collinear(a, b, c),
{
    let det = orient2d_spec(a, b, c);
    Scalar::lemma_signum_cases(det);
    assert(det.signum() == 1 || det.signum() == -1 || det.signum() == 0);
}

pub proof fn lemma_orientation_classes_pairwise_disjoint(a: Point2, b: Point2, c: Point2)
    ensures
        !(is_ccw(a, b, c) && is_cw(a, b, c)),
        !(is_ccw(a, b, c) && is_collinear(a, b, c)),
        !(is_cw(a, b, c) && is_collinear(a, b, c)),
{
    let s = orient2d_spec(a, b, c).signum();
    assert(!(s == 1 && s == -1)) by (nonlinear_arith);
    assert(!(s == 1 && s == 0)) by (nonlinear_arith);
    assert(!(s == -1 && s == 0)) by (nonlinear_arith);
}

pub proof fn lemma_orientation_spec_matches_predicates(a: Point2, b: Point2, c: Point2)
    ensures
        (orientation_spec(a, b, c) is Ccw) == is_ccw(a, b, c),
        (orientation_spec(a, b, c) is Cw) == is_cw(a, b, c),
        (orientation_spec(a, b, c) is Collinear) == is_collinear(a, b, c),
{
    let det = orient2d_spec(a, b, c);
    let s = det.signum();
    Scalar::lemma_signum_cases(det);

    if s == 1 {
        assert(orientation_spec(a, b, c) is Ccw);
        assert(!(orientation_spec(a, b, c) is Cw));
        assert(!(orientation_spec(a, b, c) is Collinear));
        assert(is_ccw(a, b, c));
        assert(!is_cw(a, b, c));
        assert(!is_collinear(a, b, c));
    } else if s == -1 {
        assert(!(orientation_spec(a, b, c) is Ccw));
        assert(orientation_spec(a, b, c) is Cw);
        assert(!(orientation_spec(a, b, c) is Collinear));
        assert(!is_ccw(a, b, c));
        assert(is_cw(a, b, c));
        assert(!is_collinear(a, b, c));
    } else {
        assert(s == 0);
        assert(!(orientation_spec(a, b, c) is Ccw));
        assert(!(orientation_spec(a, b, c) is Cw));
        assert(orientation_spec(a, b, c) is Collinear);
        assert(!is_ccw(a, b, c));
        assert(!is_cw(a, b, c));
        assert(is_collinear(a, b, c));
    }
}

} // verus!
