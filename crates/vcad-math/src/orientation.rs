use vstd::prelude::*;
use vstd::arithmetic::mul::{
    lemma_mul_cancels_negatives,
    lemma_mul_strict_inequality,
    lemma_mul_strictly_positive,
};
use crate::scalar::Scalar;
use crate::vec2::Vec2;
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

pub open spec fn scale_point_from_origin_spec(p: Point2, k: Scalar) -> Point2 {
    Point2 { x: p.x.mul_spec(k), y: p.y.mul_spec(k) }
}

pub proof fn orient2d(a: Point2, b: Point2, c: Point2) -> (out: Scalar)
    ensures
        out == orient2d_spec(a, b, c),
{
    Scalar {
        value:
            (b.x.value - a.x.value) * (c.y.value - a.y.value)
            - (b.y.value - a.y.value) * (c.x.value - a.x.value),
    }
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
        is_ccw(a, b, c) == (orient2d_spec(a, b, c).as_int() > 0),
{
    let det = orient2d_spec(a, b, c);
    Scalar::lemma_signum_positive_iff(det);
    assert(is_ccw(a, b, c) == (det.signum() == 1));
    assert((det.signum() == 1) == (det.as_int() > 0));
}

pub proof fn lemma_is_cw_iff_negative(a: Point2, b: Point2, c: Point2)
    ensures
        is_cw(a, b, c) == (orient2d_spec(a, b, c).as_int() < 0),
{
    let det = orient2d_spec(a, b, c);
    Scalar::lemma_signum_negative_iff(det);
    assert(is_cw(a, b, c) == (det.signum() == -1));
    assert((det.signum() == -1) == (det.as_int() < 0));
}

pub proof fn lemma_is_collinear_iff_zero(a: Point2, b: Point2, c: Point2)
    ensures
        is_collinear(a, b, c) == (orient2d_spec(a, b, c).as_int() == 0),
{
    let det = orient2d_spec(a, b, c);
    Scalar::lemma_signum_zero_iff(det);
    assert(is_collinear(a, b, c) == (det.signum() == 0));
    assert((det.signum() == 0) == (det.as_int() == 0));
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

pub proof fn lemma_ccw_swap_to_cw(a: Point2, b: Point2, c: Point2)
    ensures
        is_ccw(a, b, c) == is_cw(a, c, b),
{
    lemma_orient2d_swap_antisymmetric(a, b, c);
    let o = orient2d_spec(a, b, c).as_int();
    assert(orient2d_spec(a, c, b).as_int() == -o);
    assert((o > 0) == ((-o) < 0)) by (nonlinear_arith);
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
        lemma_orientation_classes_pairwise_disjoint(a, b, c);
        assert(!(is_ccw(a, b, c) && is_cw(a, b, c)));
        assert(!(is_ccw(a, b, c) && is_collinear(a, b, c)));
        assert(!is_cw(a, b, c));
        assert(!is_collinear(a, b, c));
    } else if s == -1 {
        assert(!(orientation_spec(a, b, c) is Ccw));
        assert(orientation_spec(a, b, c) is Cw);
        assert(!(orientation_spec(a, b, c) is Collinear));
        lemma_orientation_classes_pairwise_disjoint(a, b, c);
        assert(is_cw(a, b, c));
        assert(!(is_ccw(a, b, c) && is_cw(a, b, c)));
        assert(!(is_cw(a, b, c) && is_collinear(a, b, c)));
        assert(!is_ccw(a, b, c));
        assert(!is_collinear(a, b, c));
    } else {
        assert(s == 1 || s == -1 || s == 0);
        if s == 1 {
            assert(false);
        } else if s == -1 {
            assert(false);
        } else {
            assert(s == 0);
        }
        assert(!(orientation_spec(a, b, c) is Ccw));
        assert(!(orientation_spec(a, b, c) is Cw));
        assert(orientation_spec(a, b, c) is Collinear);
        lemma_orientation_classes_pairwise_disjoint(a, b, c);
        assert(is_collinear(a, b, c));
        assert(!(is_ccw(a, b, c) && is_collinear(a, b, c)));
        assert(!(is_cw(a, b, c) && is_collinear(a, b, c)));
        assert(!is_ccw(a, b, c));
        assert(!is_cw(a, b, c));
    }
}

pub proof fn lemma_orientation_spec_swap(a: Point2, b: Point2, c: Point2)
    ensures
        (orientation_spec(a, b, c) is Ccw) == (orientation_spec(a, c, b) is Cw),
        (orientation_spec(a, b, c) is Cw) == (orientation_spec(a, c, b) is Ccw),
        (orientation_spec(a, b, c) is Collinear) == (orientation_spec(a, c, b) is Collinear),
{
    lemma_orientation_spec_matches_predicates(a, b, c);
    lemma_orientation_spec_matches_predicates(a, c, b);
    lemma_orient2d_swap_antisymmetric(a, b, c);
    let o = orient2d_spec(a, b, c).as_int();
    assert(orient2d_spec(a, c, b).as_int() == -o);
    assert((o > 0) == ((-o) < 0)) by (nonlinear_arith);
    assert((o < 0) == ((-o) > 0)) by (nonlinear_arith);
    assert((o == 0) == ((-o) == 0)) by (nonlinear_arith);
}

pub proof fn lemma_orient2d_unit_ccw()
    ensures
        orient2d_spec(
            Point2::from_ints_spec(0, 0),
            Point2::from_ints_spec(1, 0),
            Point2::from_ints_spec(0, 1),
        ).as_int() == 1,
{
    assert(orient2d_spec(
        Point2::from_ints_spec(0, 0),
        Point2::from_ints_spec(1, 0),
        Point2::from_ints_spec(0, 1),
    ).as_int() == 1) by (nonlinear_arith);
}

pub proof fn lemma_orient2d_collinear()
    ensures
        orient2d_spec(
            Point2::from_ints_spec(0, 0),
            Point2::from_ints_spec(1, 1),
            Point2::from_ints_spec(2, 2),
        ).as_int() == 0,
{
    assert(orient2d_spec(
        Point2::from_ints_spec(0, 0),
        Point2::from_ints_spec(1, 1),
        Point2::from_ints_spec(2, 2),
    ).as_int() == 0) by (nonlinear_arith);
}

pub proof fn lemma_orient2d_swap_antisymmetric(a: Point2, b: Point2, c: Point2)
    ensures
        orient2d_spec(a, b, c) == orient2d_spec(a, c, b).neg_spec(),
{
    let lhs = orient2d_spec(a, b, c);
    let rhs = orient2d_spec(a, c, b).neg_spec();
    assert(lhs.as_int()
        == (b.x.as_int() - a.x.as_int()) * (c.y.as_int() - a.y.as_int())
        - (b.y.as_int() - a.y.as_int()) * (c.x.as_int() - a.x.as_int()));
    assert(orient2d_spec(a, c, b).as_int()
        == (c.x.as_int() - a.x.as_int()) * (b.y.as_int() - a.y.as_int())
        - (c.y.as_int() - a.y.as_int()) * (b.x.as_int() - a.x.as_int()));
    assert(rhs.as_int()
        == -(
            (c.x.as_int() - a.x.as_int()) * (b.y.as_int() - a.y.as_int())
            - (c.y.as_int() - a.y.as_int()) * (b.x.as_int() - a.x.as_int())
        ));
    assert(
        (b.x.as_int() - a.x.as_int()) * (c.y.as_int() - a.y.as_int())
        - (b.y.as_int() - a.y.as_int()) * (c.x.as_int() - a.x.as_int())
        == -(
            (c.x.as_int() - a.x.as_int()) * (b.y.as_int() - a.y.as_int())
            - (c.y.as_int() - a.y.as_int()) * (b.x.as_int() - a.x.as_int())
        )
    ) by (nonlinear_arith);
    assert(lhs.as_int() == rhs.as_int());
    Scalar::lemma_eq_from_as_int_internal(lhs, rhs);
}

pub proof fn lemma_orient2d_cyclic_invariant(a: Point2, b: Point2, c: Point2)
    ensures
        orient2d_spec(a, b, c) == orient2d_spec(b, c, a),
{
    let lhs = orient2d_spec(a, b, c);
    let rhs = orient2d_spec(b, c, a);
    assert(lhs.as_int()
        == (b.x.as_int() - a.x.as_int()) * (c.y.as_int() - a.y.as_int())
        - (b.y.as_int() - a.y.as_int()) * (c.x.as_int() - a.x.as_int()));
    assert(rhs.as_int()
        == (c.x.as_int() - b.x.as_int()) * (a.y.as_int() - b.y.as_int())
        - (c.y.as_int() - b.y.as_int()) * (a.x.as_int() - b.x.as_int()));
    assert(
        (b.x.as_int() - a.x.as_int()) * (c.y.as_int() - a.y.as_int())
        - (b.y.as_int() - a.y.as_int()) * (c.x.as_int() - a.x.as_int())
        == (c.x.as_int() - b.x.as_int()) * (a.y.as_int() - b.y.as_int())
        - (c.y.as_int() - b.y.as_int()) * (a.x.as_int() - b.x.as_int())
    ) by (nonlinear_arith);
    assert(lhs.as_int() == rhs.as_int());
    Scalar::lemma_eq_from_as_int_internal(lhs, rhs);
}

pub proof fn lemma_orient2d_translation_invariant(a: Point2, b: Point2, c: Point2, t: Vec2)
    ensures
        orient2d_spec(a.add_vec_spec(t), b.add_vec_spec(t), c.add_vec_spec(t))
            == orient2d_spec(a, b, c),
{
    let lhs = orient2d_spec(a.add_vec_spec(t), b.add_vec_spec(t), c.add_vec_spec(t));
    let rhs = orient2d_spec(a, b, c);
    assert(lhs.as_int()
        == ((b.x.as_int() + t.x.as_int()) - (a.x.as_int() + t.x.as_int()))
            * ((c.y.as_int() + t.y.as_int()) - (a.y.as_int() + t.y.as_int()))
        - ((b.y.as_int() + t.y.as_int()) - (a.y.as_int() + t.y.as_int()))
            * ((c.x.as_int() + t.x.as_int()) - (a.x.as_int() + t.x.as_int())));
    assert(rhs.as_int()
        == (b.x.as_int() - a.x.as_int()) * (c.y.as_int() - a.y.as_int())
        - (b.y.as_int() - a.y.as_int()) * (c.x.as_int() - a.x.as_int()));
    assert(
        ((b.x.as_int() + t.x.as_int()) - (a.x.as_int() + t.x.as_int()))
            * ((c.y.as_int() + t.y.as_int()) - (a.y.as_int() + t.y.as_int()))
        - ((b.y.as_int() + t.y.as_int()) - (a.y.as_int() + t.y.as_int()))
            * ((c.x.as_int() + t.x.as_int()) - (a.x.as_int() + t.x.as_int()))
        == (b.x.as_int() - a.x.as_int()) * (c.y.as_int() - a.y.as_int())
            - (b.y.as_int() - a.y.as_int()) * (c.x.as_int() - a.x.as_int())
    ) by (nonlinear_arith);
    assert(lhs.as_int() == rhs.as_int());
    Scalar::lemma_eq_from_as_int_internal(lhs, rhs);
}

pub proof fn lemma_orient2d_degenerate_repeated_points(a: Point2, b: Point2)
    ensures
        orient2d_spec(a, a, b).as_int() == 0,
        orient2d_spec(a, b, a).as_int() == 0,
        orient2d_spec(b, a, a).as_int() == 0,
{
    assert(orient2d_spec(a, a, b).as_int() == 0) by (nonlinear_arith);
    assert(orient2d_spec(a, b, a).as_int() == 0) by (nonlinear_arith);
    assert(orient2d_spec(b, a, a).as_int() == 0) by (nonlinear_arith);
}

pub proof fn lemma_orient2d_permutation_table(a: Point2, b: Point2, c: Point2)
    ensures
        orient2d_spec(a, b, c) == orient2d_spec(b, c, a),
        orient2d_spec(a, b, c) == orient2d_spec(c, a, b),
        orient2d_spec(a, b, c) == orient2d_spec(a, c, b).neg_spec(),
        orient2d_spec(a, b, c) == orient2d_spec(b, a, c).neg_spec(),
        orient2d_spec(a, b, c) == orient2d_spec(c, b, a).neg_spec(),
{
    lemma_orient2d_cyclic_invariant(a, b, c);
    lemma_orient2d_cyclic_invariant(c, a, b);
    lemma_orient2d_swap_antisymmetric(a, b, c);

    lemma_orient2d_cyclic_invariant(b, a, c);
    assert(orient2d_spec(b, a, c) == orient2d_spec(a, c, b));
    assert(orient2d_spec(a, b, c) == orient2d_spec(a, c, b).neg_spec());
    assert(orient2d_spec(a, c, b).neg_spec() == orient2d_spec(b, a, c).neg_spec());
    assert(orient2d_spec(a, b, c) == orient2d_spec(b, a, c).neg_spec());

    lemma_orient2d_cyclic_invariant(c, b, a);
    assert(orient2d_spec(c, b, a) == orient2d_spec(b, a, c));
    assert(orient2d_spec(b, a, c).neg_spec() == orient2d_spec(c, b, a).neg_spec());
    assert(orient2d_spec(a, b, c) == orient2d_spec(c, b, a).neg_spec());
}

pub proof fn lemma_orientation_spec_exclusive(a: Point2, b: Point2, c: Point2)
    ensures
        (orientation_spec(a, b, c) is Ccw) || (orientation_spec(a, b, c) is Cw)
            || (orientation_spec(a, b, c) is Collinear),
        !((orientation_spec(a, b, c) is Ccw) && (orientation_spec(a, b, c) is Cw)),
        !((orientation_spec(a, b, c) is Ccw) && (orientation_spec(a, b, c) is Collinear)),
        !((orientation_spec(a, b, c) is Cw) && (orientation_spec(a, b, c) is Collinear)),
{
    let o = orientation_spec(a, b, c);
    if o is Ccw {
        assert(!(o is Cw));
        assert(!(o is Collinear));
    } else if o is Cw {
        assert(!(o is Ccw));
        assert(!(o is Collinear));
    } else {
        assert(o is Collinear);
        assert(!(o is Ccw));
        assert(!(o is Cw));
    }
}

pub proof fn lemma_orientation_spec_translation_invariant(a: Point2, b: Point2, c: Point2, t: Vec2)
    ensures
        orientation_spec(a.add_vec_spec(t), b.add_vec_spec(t), c.add_vec_spec(t))
            == orientation_spec(a, b, c),
{
    lemma_orient2d_translation_invariant(a, b, c, t);
    let d0 = orient2d_spec(a, b, c);
    let d1 = orient2d_spec(a.add_vec_spec(t), b.add_vec_spec(t), c.add_vec_spec(t));
    assert(d1.as_int() == d0.as_int());
    Scalar::lemma_eq_from_as_int_internal(d1, d0);
    assert(d1.signum() == d0.signum());
}

pub proof fn lemma_orient2d_scale_from_origin(a: Point2, b: Point2, c: Point2, k: Scalar)
    ensures
        orient2d_spec(
            scale_point_from_origin_spec(a, k),
            scale_point_from_origin_spec(b, k),
            scale_point_from_origin_spec(c, k),
        ).as_int() == k.mul_spec(k).mul_spec(orient2d_spec(a, b, c)).as_int(),
{
    let sa = scale_point_from_origin_spec(a, k);
    let sb = scale_point_from_origin_spec(b, k);
    let sc = scale_point_from_origin_spec(c, k);
    let ba = b.sub_spec(a);
    let ca = c.sub_spec(a);
    let sba = sb.sub_spec(sa);
    let sca = sc.sub_spec(sa);

    assert(sba.x.as_int() == (b.x.as_int() * k.as_int()) - (a.x.as_int() * k.as_int()));
    assert(sba.y.as_int() == (b.y.as_int() * k.as_int()) - (a.y.as_int() * k.as_int()));
    assert(sca.x.as_int() == (c.x.as_int() * k.as_int()) - (a.x.as_int() * k.as_int()));
    assert(sca.y.as_int() == (c.y.as_int() * k.as_int()) - (a.y.as_int() * k.as_int()));
    assert(ba.scale_spec(k).x.as_int() == (b.x.as_int() - a.x.as_int()) * k.as_int());
    assert(ba.scale_spec(k).y.as_int() == (b.y.as_int() - a.y.as_int()) * k.as_int());
    assert(ca.scale_spec(k).x.as_int() == (c.x.as_int() - a.x.as_int()) * k.as_int());
    assert(ca.scale_spec(k).y.as_int() == (c.y.as_int() - a.y.as_int()) * k.as_int());
    assert(((b.x.as_int() * k.as_int()) - (a.x.as_int() * k.as_int()))
        == (b.x.as_int() - a.x.as_int()) * k.as_int()) by (nonlinear_arith);
    assert(((b.y.as_int() * k.as_int()) - (a.y.as_int() * k.as_int()))
        == (b.y.as_int() - a.y.as_int()) * k.as_int()) by (nonlinear_arith);
    assert(((c.x.as_int() * k.as_int()) - (a.x.as_int() * k.as_int()))
        == (c.x.as_int() - a.x.as_int()) * k.as_int()) by (nonlinear_arith);
    assert(((c.y.as_int() * k.as_int()) - (a.y.as_int() * k.as_int()))
        == (c.y.as_int() - a.y.as_int()) * k.as_int()) by (nonlinear_arith);
    assert(sba.x.as_int() == ba.scale_spec(k).x.as_int());
    assert(sba.y.as_int() == ba.scale_spec(k).y.as_int());
    assert(sca.x.as_int() == ca.scale_spec(k).x.as_int());
    assert(sca.y.as_int() == ca.scale_spec(k).y.as_int());
    Vec2::lemma_eq_from_component_ints(sba, ba.scale_spec(k));
    Vec2::lemma_eq_from_component_ints(sca, ca.scale_spec(k));

    Vec2::lemma_cross_scale_extract_left(ba, ca.scale_spec(k), k);
    Vec2::lemma_cross_scale_extract_right(ba, ca, k);
    Scalar::lemma_mul_associative(k, k, ba.cross_spec(ca));

    assert(orient2d_spec(sa, sb, sc).as_int() == sba.cross_spec(sca).as_int());
    assert(orient2d_spec(a, b, c).as_int() == ba.cross_spec(ca).as_int());
    assert(sba.cross_spec(sca).as_int() == ba.scale_spec(k).cross_spec(ca.scale_spec(k)).as_int());
    assert(ba.scale_spec(k).cross_spec(ca.scale_spec(k)).as_int()
        == k.mul_spec(ba.cross_spec(ca.scale_spec(k))).as_int());
    assert(ba.cross_spec(ca.scale_spec(k)).as_int()
        == k.mul_spec(ba.cross_spec(ca)).as_int());
    assert(k.mul_spec(ba.cross_spec(ca.scale_spec(k))).as_int()
        == k.mul_spec(k.mul_spec(ba.cross_spec(ca))).as_int());
    assert(k.mul_spec(k.mul_spec(ba.cross_spec(ca))).as_int()
        == k.mul_spec(k).mul_spec(ba.cross_spec(ca)).as_int());
}

pub proof fn lemma_orientation_spec_scale_nonzero_preserves(a: Point2, b: Point2, c: Point2, k: Scalar)
    ensures
        k.as_int() != 0 ==> orientation_spec(
            scale_point_from_origin_spec(a, k),
            scale_point_from_origin_spec(b, k),
            scale_point_from_origin_spec(c, k),
        ) == orientation_spec(a, b, c),
{
    if k.as_int() != 0 {
        lemma_orientation_spec_scale_nonzero_preserves_strong(a, b, c, k);
    }
}

pub proof fn lemma_orientation_spec_scale_nonzero_preserves_strong(a: Point2, b: Point2, c: Point2, k: Scalar)
    requires
        k.as_int() != 0,
    ensures
        orientation_spec(
            scale_point_from_origin_spec(a, k),
            scale_point_from_origin_spec(b, k),
            scale_point_from_origin_spec(c, k),
        ) == orientation_spec(a, b, c),
{
    let sa = scale_point_from_origin_spec(a, k);
    let sb = scale_point_from_origin_spec(b, k);
    let sc = scale_point_from_origin_spec(c, k);

    lemma_orient2d_scale_from_origin(a, b, c, k);
    let o = orient2d_spec(a, b, c).as_int();
    let os = orient2d_spec(sa, sb, sc).as_int();
    let k2 = k.as_int() * k.as_int();
    assert(os == k2 * o);
    assert(o * k2 == k2 * o) by (nonlinear_arith);

    if k.as_int() > 0 {
        lemma_mul_strictly_positive(k.as_int(), k.as_int());
        assert(k2 > 0);
    } else {
        assert(k.as_int() < 0);
        assert(-k.as_int() > 0);
        lemma_mul_strictly_positive(-k.as_int(), -k.as_int());
        assert((-k.as_int()) * (-k.as_int()) > 0);
        lemma_mul_cancels_negatives(k.as_int(), k.as_int());
        assert(k2 == (-k.as_int()) * (-k.as_int()));
        assert(k2 > 0);
    }

    if o > 0 {
        lemma_mul_strictly_positive(k2, o);
        assert(os > 0);
        lemma_is_ccw_iff_positive(sa, sb, sc);
        lemma_is_ccw_iff_positive(a, b, c);
        lemma_orientation_spec_matches_predicates(sa, sb, sc);
        lemma_orientation_spec_matches_predicates(a, b, c);
        assert(orientation_spec(sa, sb, sc) is Ccw);
        assert(orientation_spec(a, b, c) is Ccw);
        assert(orientation_spec(sa, sb, sc) == orientation_spec(a, b, c));
    } else if o < 0 {
        lemma_mul_strict_inequality(o, 0, k2);
        assert(o * k2 < 0 * k2);
        assert(0 * k2 == 0);
        assert(os == o * k2);
        assert(os < 0);
        lemma_is_cw_iff_negative(sa, sb, sc);
        lemma_is_cw_iff_negative(a, b, c);
        lemma_orientation_spec_matches_predicates(sa, sb, sc);
        lemma_orientation_spec_matches_predicates(a, b, c);
        assert(orientation_spec(sa, sb, sc) is Cw);
        assert(orientation_spec(a, b, c) is Cw);
        assert(orientation_spec(sa, sb, sc) == orientation_spec(a, b, c));
    } else {
        assert(o == 0);
        assert(k2 * o == k2 * 0);
        assert(k2 * 0 == 0);
        assert(os == 0);
        lemma_is_collinear_iff_zero(sa, sb, sc);
        lemma_is_collinear_iff_zero(a, b, c);
        lemma_orientation_spec_matches_predicates(sa, sb, sc);
        lemma_orientation_spec_matches_predicates(a, b, c);
        assert(orientation_spec(sa, sb, sc) is Collinear);
        assert(orientation_spec(a, b, c) is Collinear);
        assert(orientation_spec(sa, sb, sc) == orientation_spec(a, b, c));
    }
}

pub proof fn lemma_orientation_spec_scale_zero_collinear(a: Point2, b: Point2, c: Point2, k: Scalar)
    ensures
        k.as_int() == 0 ==> (orientation_spec(
            scale_point_from_origin_spec(a, k),
            scale_point_from_origin_spec(b, k),
            scale_point_from_origin_spec(c, k),
        ) is Collinear),
{
    if k.as_int() == 0 {
        lemma_orientation_spec_scale_zero_collinear_strong(a, b, c, k);
    }
}

pub proof fn lemma_orientation_spec_scale_zero_collinear_strong(a: Point2, b: Point2, c: Point2, k: Scalar)
    requires
        k.as_int() == 0,
    ensures
        orientation_spec(
            scale_point_from_origin_spec(a, k),
            scale_point_from_origin_spec(b, k),
            scale_point_from_origin_spec(c, k),
        ) is Collinear,
{
    let sa = scale_point_from_origin_spec(a, k);
    let sb = scale_point_from_origin_spec(b, k);
    let sc = scale_point_from_origin_spec(c, k);
    lemma_orient2d_scale_from_origin(a, b, c, k);
    assert(k.as_int() * k.as_int() == 0);
    assert(orient2d_spec(sa, sb, sc).as_int() == 0);
    lemma_is_collinear_iff_zero(sa, sb, sc);
    lemma_orientation_spec_matches_predicates(sa, sb, sc);
    assert(orientation_spec(sa, sb, sc) is Collinear);
}

} // verus!
