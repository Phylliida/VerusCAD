use vstd::prelude::*;
use vstd::arithmetic::mul::lemma_mul_by_zero_is_zero;
use crate::scalar::Scalar;
use crate::point2::Point2;
use crate::vec2::Vec2;

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

pub proof fn lemma_orientation_spec_exclusive(a: Point2, b: Point2, c: Point2)
    ensures
        (orientation_spec(a, b, c) is Ccw)
            || (orientation_spec(a, b, c) is Cw)
            || (orientation_spec(a, b, c) is Collinear),
        !((orientation_spec(a, b, c) is Ccw) && (orientation_spec(a, b, c) is Cw)),
        !((orientation_spec(a, b, c) is Ccw) && (orientation_spec(a, b, c) is Collinear)),
        !((orientation_spec(a, b, c) is Cw) && (orientation_spec(a, b, c) is Collinear)),
{
    lemma_orientation_spec_matches_predicates(a, b, c);
    lemma_orientation_classes_exhaustive(a, b, c);
    lemma_orientation_classes_pairwise_disjoint(a, b, c);
    assert((orientation_spec(a, b, c) is Ccw) == is_ccw(a, b, c));
    assert((orientation_spec(a, b, c) is Cw) == is_cw(a, b, c));
    assert((orientation_spec(a, b, c) is Collinear) == is_collinear(a, b, c));
}

pub proof fn lemma_orient2d_degenerate_repeated_points(a: Point2, b: Point2)
    ensures
        orient2d_spec(a, a, b).signum() == 0,
        orient2d_spec(a, b, a).signum() == 0,
        orient2d_spec(b, a, a).signum() == 0,
{
    let aa = a.sub_spec(a);
    let ba = b.sub_spec(a);
    Point2::lemma_sub_self_zero_num(a);
    assert(aa.x.num == 0);
    assert(aa.y.num == 0);
    Vec2::lemma_cross_left_zero_signum(aa, ba);
    assert(orient2d_spec(a, a, b) == aa.cross_spec(ba));
    assert(orient2d_spec(a, a, b).signum() == 0);

    let ba2 = b.sub_spec(a);
    let aa2 = a.sub_spec(a);
    assert(aa2.x.num == 0);
    assert(aa2.y.num == 0);
    Vec2::lemma_cross_right_zero_signum(ba2, aa2);
    assert(orient2d_spec(a, b, a) == ba2.cross_spec(aa2));
    assert(orient2d_spec(a, b, a).signum() == 0);

    let ab2 = a.sub_spec(b);
    Vec2::lemma_cross_self_zero_signum(ab2);
    assert(orient2d_spec(b, a, a) == ab2.cross_spec(ab2));
    assert(orient2d_spec(b, a, a).signum() == 0);
}

pub proof fn lemma_orient2d_collinear(a: Point2, b: Point2, c: Point2)
    ensures
        is_collinear(a, b, c) ==> orient2d_spec(a, b, c).eqv_spec(Scalar::from_int_spec(0)),
{
    let z = Scalar::from_int_spec(0);
    if is_collinear(a, b, c) {
        let det = orient2d_spec(a, b, c);
        lemma_is_collinear_iff_zero(a, b, c);
        assert(is_collinear(a, b, c) == (det.num == 0));
        assert(det.num == 0);
        assert(z.num == 0);
        assert(det.eqv_spec(z) == (det.num * z.denom() == z.num * det.denom()));
        assert(det.num * z.denom() == 0 * z.denom());
        assert(z.num * det.denom() == 0 * det.denom());
        lemma_mul_by_zero_is_zero(z.denom());
        lemma_mul_by_zero_is_zero(det.denom());
        assert(0 * z.denom() == 0);
        assert(0 * det.denom() == 0);
        assert(det.eqv_spec(z));
    }
}

pub proof fn lemma_orient2d_unit_ccw()
    ensures
        orient2d_spec(
            Point2::from_ints_spec(0, 0),
            Point2::from_ints_spec(1, 0),
            Point2::from_ints_spec(0, 1),
        ).eqv_spec(Scalar::from_int_spec(1)),
        is_ccw(
            Point2::from_ints_spec(0, 0),
            Point2::from_ints_spec(1, 0),
            Point2::from_ints_spec(0, 1),
        ),
{
    let a = Point2::from_ints_spec(0, 0);
    let b = Point2::from_ints_spec(1, 0);
    let c = Point2::from_ints_spec(0, 1);
    let det = orient2d_spec(a, b, c);
    let one = Scalar::from_int_spec(1);
    let ba = b.sub_spec(a);
    let ca = c.sub_spec(a);

    assert(ba.x == Scalar::from_int_spec(1));
    assert(ba.y == Scalar::from_int_spec(0));
    assert(ca.x == Scalar::from_int_spec(0));
    assert(ca.y == Scalar::from_int_spec(1));
    assert(det == ba.cross_spec(ca));
    assert(det == ba.x.mul_spec(ca.y).sub_spec(ba.y.mul_spec(ca.x)));
    assert(ba.x.mul_spec(ca.y) == Scalar::from_int_spec(1).mul_spec(Scalar::from_int_spec(1)));
    assert(ba.y.mul_spec(ca.x) == Scalar::from_int_spec(0).mul_spec(Scalar::from_int_spec(0)));
    assert(Scalar::from_int_spec(1).mul_spec(Scalar::from_int_spec(1)) == Scalar::from_int_spec(1));
    assert(Scalar::from_int_spec(0).mul_spec(Scalar::from_int_spec(0)) == Scalar::from_int_spec(0));
    assert(det == Scalar::from_int_spec(1).sub_spec(Scalar::from_int_spec(0)));
    Scalar::lemma_add_zero_identity(Scalar::from_int_spec(1));
    assert(Scalar::from_int_spec(1).sub_spec(Scalar::from_int_spec(0))
        == Scalar::from_int_spec(1).add_spec(Scalar::from_int_spec(0).neg_spec()));
    assert(Scalar::from_int_spec(0).neg_spec() == Scalar::from_int_spec(0));
    assert(Scalar::from_int_spec(1).add_spec(Scalar::from_int_spec(0)) == Scalar::from_int_spec(1));
    assert(det == one);
    Scalar::lemma_eqv_reflexive(one);
    assert(det.eqv_spec(one));

    lemma_is_ccw_iff_positive(a, b, c);
    assert(det.num == 1);
    assert(is_ccw(a, b, c) == (det.num > 0));
    assert(det.num > 0);
    assert(is_ccw(a, b, c));
}

pub proof fn lemma_orient2d_translation_invariant(a: Point2, b: Point2, c: Point2, t: Vec2)
    ensures
        orient2d_spec(a.add_vec_spec(t), b.add_vec_spec(t), c.add_vec_spec(t)).eqv_spec(orient2d_spec(a, b, c)),
{
    let at = a.add_vec_spec(t);
    let bt = b.add_vec_spec(t);
    let ct = c.add_vec_spec(t);

    let u1 = bt.sub_spec(at);
    let u2 = b.sub_spec(a);
    let v1 = ct.sub_spec(at);
    let v2 = c.sub_spec(a);
    let lhs = orient2d_spec(at, bt, ct);
    let rhs = orient2d_spec(a, b, c);

    crate::point2::lemma_sub_translation_invariant(b, a, t);
    crate::point2::lemma_sub_translation_invariant(c, a, t);
    assert(u1.eqv_spec(u2));
    assert(v1.eqv_spec(v2));
    assert(u1.x.eqv_spec(u2.x));
    assert(u1.y.eqv_spec(u2.y));
    assert(v1.x.eqv_spec(v2.x));
    assert(v1.y.eqv_spec(v2.y));

    Vec2::lemma_cross_eqv_congruence(u1, u2, v1, v2);
    assert(u1.cross_spec(v1).eqv_spec(u2.cross_spec(v2)));
    assert(lhs == u1.cross_spec(v1));
    assert(rhs == u2.cross_spec(v2));
    assert(lhs.eqv_spec(rhs));
}

pub proof fn lemma_orientation_spec_translation_invariant(a: Point2, b: Point2, c: Point2, t: Vec2)
    ensures
        orientation_spec(a.add_vec_spec(t), b.add_vec_spec(t), c.add_vec_spec(t)) == orientation_spec(a, b, c),
{
    let at = a.add_vec_spec(t);
    let bt = b.add_vec_spec(t);
    let ct = c.add_vec_spec(t);
    let dt = orient2d_spec(at, bt, ct);
    let d = orient2d_spec(a, b, c);
    let st = dt.signum();
    let s = d.signum();

    lemma_orient2d_translation_invariant(a, b, c, t);
    assert(dt.eqv_spec(d));
    Scalar::lemma_eqv_signum(dt, d);
    assert(st == s);

    if s == 1 {
        assert(orientation_spec(at, bt, ct) == Orientation::Ccw);
        assert(orientation_spec(a, b, c) == Orientation::Ccw);
    } else if s == -1 {
        assert(orientation_spec(at, bt, ct) == Orientation::Cw);
        assert(orientation_spec(a, b, c) == Orientation::Cw);
    } else {
        assert(s != 1 && s != -1);
        assert(orientation_spec(at, bt, ct) == Orientation::Collinear);
        assert(orientation_spec(a, b, c) == Orientation::Collinear);
    }
    assert(orientation_spec(at, bt, ct) == orientation_spec(a, b, c));
}

proof fn lemma_scale_point_sub_eqv(p: Point2, q: Point2, k: Scalar)
    ensures
        scale_point_from_origin_spec(p, k).sub_spec(scale_point_from_origin_spec(q, k)).eqv_spec(p.sub_spec(q).scale_spec(k)),
{
    let lhs = scale_point_from_origin_spec(p, k).sub_spec(scale_point_from_origin_spec(q, k));
    let rhs = p.sub_spec(q).scale_spec(k);
    Scalar::lemma_sub_mul_right(p.x, q.x, k);
    Scalar::lemma_sub_mul_right(p.y, q.y, k);
    assert(lhs.x == p.x.mul_spec(k).sub_spec(q.x.mul_spec(k)));
    assert(lhs.y == p.y.mul_spec(k).sub_spec(q.y.mul_spec(k)));
    assert(rhs.x == p.x.sub_spec(q.x).mul_spec(k));
    assert(rhs.y == p.y.sub_spec(q.y).mul_spec(k));
    Scalar::lemma_eqv_symmetric(rhs.x, lhs.x);
    Scalar::lemma_eqv_symmetric(rhs.y, lhs.y);
    assert(lhs.x.eqv_spec(rhs.x));
    assert(lhs.y.eqv_spec(rhs.y));
    assert(lhs.eqv_spec(rhs));
}

pub proof fn lemma_orient2d_scale_from_origin(a: Point2, b: Point2, c: Point2, k: Scalar)
    ensures
        orient2d_spec(
            scale_point_from_origin_spec(a, k),
            scale_point_from_origin_spec(b, k),
            scale_point_from_origin_spec(c, k),
        ).eqv_spec(k.mul_spec(k).mul_spec(orient2d_spec(a, b, c))),
{
    let sa = scale_point_from_origin_spec(a, k);
    let sb = scale_point_from_origin_spec(b, k);
    let sc = scale_point_from_origin_spec(c, k);
    let ba = b.sub_spec(a);
    let ca = c.sub_spec(a);
    let ba_s = sb.sub_spec(sa);
    let ca_s = sc.sub_spec(sa);
    let ba_k = ba.scale_spec(k);
    let ca_k = ca.scale_spec(k);
    let lhs = orient2d_spec(sa, sb, sc);
    let rhs = k.mul_spec(k).mul_spec(orient2d_spec(a, b, c));
    let mid1 = ba_k.cross_spec(ca_k);
    let mid2 = k.mul_spec(ba.cross_spec(ca_k));
    let mid3 = k.mul_spec(k.mul_spec(ba.cross_spec(ca)));

    lemma_scale_point_sub_eqv(b, a, k);
    lemma_scale_point_sub_eqv(c, a, k);
    assert(ba_s.eqv_spec(ba_k));
    assert(ca_s.eqv_spec(ca_k));
    assert(ba_s.x.eqv_spec(ba_k.x));
    assert(ba_s.y.eqv_spec(ba_k.y));
    assert(ca_s.x.eqv_spec(ca_k.x));
    assert(ca_s.y.eqv_spec(ca_k.y));
    Vec2::lemma_cross_eqv_congruence(ba_s, ba_k, ca_s, ca_k);
    assert(ba_s.cross_spec(ca_s).eqv_spec(mid1));
    assert(lhs == ba_s.cross_spec(ca_s));
    assert(lhs.eqv_spec(mid1));

    Vec2::lemma_cross_scale_extract_left(ba, ca_k, k);
    assert(mid1.eqv_spec(mid2));
    Vec2::lemma_cross_scale_extract_right(ba, ca, k);
    assert(ba.cross_spec(ca_k).eqv_spec(k.mul_spec(ba.cross_spec(ca))));
    Scalar::lemma_eqv_mul_congruence_right(k, ba.cross_spec(ca_k), k.mul_spec(ba.cross_spec(ca)));
    assert(mid2.eqv_spec(mid3));

    Scalar::lemma_mul_associative(k, k, ba.cross_spec(ca));
    assert(rhs.eqv_spec(mid3));
    Scalar::lemma_eqv_symmetric(rhs, mid3);
    assert(mid3.eqv_spec(rhs));

    Scalar::lemma_eqv_transitive(lhs, mid1, mid2);
    Scalar::lemma_eqv_transitive(lhs, mid2, mid3);
    Scalar::lemma_eqv_transitive(lhs, mid3, rhs);
    assert(lhs.eqv_spec(rhs));
}

pub proof fn lemma_orientation_spec_scale_nonzero_preserves(a: Point2, b: Point2, c: Point2, k: Scalar)
    ensures
        (k.num != 0) ==> (
            orientation_spec(
                scale_point_from_origin_spec(a, k),
                scale_point_from_origin_spec(b, k),
                scale_point_from_origin_spec(c, k),
            ) == orientation_spec(a, b, c)
        ),
{
    if k.num != 0 {
        lemma_orientation_spec_scale_nonzero_preserves_strong(a, b, c, k);
        assert(
            orientation_spec(
                scale_point_from_origin_spec(a, k),
                scale_point_from_origin_spec(b, k),
                scale_point_from_origin_spec(c, k),
            ) == orientation_spec(a, b, c)
        );
    }
}

pub proof fn lemma_orientation_spec_scale_nonzero_preserves_strong(a: Point2, b: Point2, c: Point2, k: Scalar)
    requires
        k.num != 0,
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
    let ds = orient2d_spec(sa, sb, sc);
    let d = orient2d_spec(a, b, c);
    let kk = k.mul_spec(k);
    let prod = kk.mul_spec(d);

    lemma_orient2d_scale_from_origin(a, b, c, k);
    assert(ds.eqv_spec(prod));
    Scalar::lemma_eqv_signum(ds, prod);
    Scalar::lemma_signum_mul(k, k);
    assert(kk.signum() == k.signum() * k.signum());
    Scalar::lemma_signum_cases(k);
    Scalar::lemma_signum_zero_iff(k);
    assert((k.signum() == 0) == (k.num == 0));
    assert(k.signum() != 0);
    if k.signum() == 1 {
        assert(kk.signum() == 1 * 1);
        assert(kk.signum() == 1);
    } else {
        assert(k.signum() == -1);
        assert(kk.signum() == (-1) * (-1));
        assert(kk.signum() == 1);
    }
    Scalar::lemma_signum_mul(kk, d);
    assert(prod.signum() == kk.signum() * d.signum());
    assert(prod.signum() == 1 * d.signum());
    assert(prod.signum() == d.signum());
    assert(ds.signum() == prod.signum());
    assert(ds.signum() == d.signum());

    if d.signum() == 1 {
        assert(orientation_spec(sa, sb, sc) == Orientation::Ccw);
        assert(orientation_spec(a, b, c) == Orientation::Ccw);
    } else if d.signum() == -1 {
        assert(orientation_spec(sa, sb, sc) == Orientation::Cw);
        assert(orientation_spec(a, b, c) == Orientation::Cw);
    } else {
        assert(orientation_spec(sa, sb, sc) == Orientation::Collinear);
        assert(orientation_spec(a, b, c) == Orientation::Collinear);
    }
    assert(orientation_spec(sa, sb, sc) == orientation_spec(a, b, c));
}

pub proof fn lemma_orientation_spec_scale_zero_collinear(a: Point2, b: Point2, c: Point2, k: Scalar)
    ensures
        (k.num == 0) ==> (
            orientation_spec(
                scale_point_from_origin_spec(a, k),
                scale_point_from_origin_spec(b, k),
                scale_point_from_origin_spec(c, k),
            ) is Collinear
        ),
{
    if k.num == 0 {
        lemma_orientation_spec_scale_zero_collinear_strong(a, b, c, k);
        assert(orientation_spec(
            scale_point_from_origin_spec(a, k),
            scale_point_from_origin_spec(b, k),
            scale_point_from_origin_spec(c, k),
        ) is Collinear);
    }
}

pub proof fn lemma_orientation_spec_scale_zero_collinear_strong(a: Point2, b: Point2, c: Point2, k: Scalar)
    requires
        k.num == 0,
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
    let ds = orient2d_spec(sa, sb, sc);
    let d = orient2d_spec(a, b, c);
    let kk = k.mul_spec(k);
    let prod = kk.mul_spec(d);

    lemma_orient2d_scale_from_origin(a, b, c, k);
    assert(ds.eqv_spec(prod));
    Scalar::lemma_mul_left_zero_num(k, k);
    assert(kk.num == 0);
    Scalar::lemma_mul_left_zero_num(kk, d);
    assert(prod.num == 0);
    Scalar::lemma_signum_zero_iff(prod);
    assert((prod.signum() == 0) == (prod.num == 0));
    assert(prod.signum() == 0);
    Scalar::lemma_eqv_signum(ds, prod);
    assert(ds.signum() == prod.signum());
    assert(ds.signum() == 0);
    assert(orientation_spec(sa, sb, sc) is Collinear);
}

pub proof fn lemma_orientation_spec_degenerate_repeated_points(a: Point2, b: Point2)
    ensures
        orientation_spec(a, a, b) is Collinear,
        orientation_spec(a, b, a) is Collinear,
        orientation_spec(b, a, a) is Collinear,
{
    lemma_orient2d_degenerate_repeated_points(a, b);
    lemma_orientation_spec_matches_predicates(a, a, b);
    lemma_orientation_spec_matches_predicates(a, b, a);
    lemma_orientation_spec_matches_predicates(b, a, a);
    assert(is_collinear(a, a, b));
    assert(is_collinear(a, b, a));
    assert(is_collinear(b, a, a));
    assert(orientation_spec(a, a, b) is Collinear);
    assert(orientation_spec(a, b, a) is Collinear);
    assert(orientation_spec(b, a, a) is Collinear);
}

pub proof fn lemma_orient2d_swap_antisymmetric(a: Point2, b: Point2, c: Point2)
    ensures
        orient2d_spec(a, b, c) == orient2d_spec(a, c, b).neg_spec(),
{
    let ba = b.sub_spec(a);
    let ca = c.sub_spec(a);
    Vec2::lemma_cross_antisymmetric(ba, ca);
    assert(orient2d_spec(a, b, c) == ba.cross_spec(ca));
    assert(orient2d_spec(a, c, b) == ca.cross_spec(ba));
    assert(orient2d_spec(a, b, c) == orient2d_spec(a, c, b).neg_spec());
}

pub proof fn lemma_orient2d_swap_antisymmetric_num(a: Point2, b: Point2, c: Point2)
    ensures
        orient2d_spec(a, b, c).num == -orient2d_spec(a, c, b).num,
{
    lemma_orient2d_swap_antisymmetric(a, b, c);
    Scalar::lemma_signum_neg(orient2d_spec(a, c, b));
    assert(orient2d_spec(a, b, c) == orient2d_spec(a, c, b).neg_spec());
    assert(orient2d_spec(a, b, c).num == orient2d_spec(a, c, b).neg_spec().num);
    assert(orient2d_spec(a, b, c).num == -orient2d_spec(a, c, b).num);
}

pub proof fn lemma_is_collinear_swap(a: Point2, b: Point2, c: Point2)
    ensures
        is_collinear(a, b, c) == is_collinear(a, c, b),
{
    lemma_orient2d_swap_antisymmetric_num(a, b, c);
    lemma_is_collinear_iff_zero(a, b, c);
    lemma_is_collinear_iff_zero(a, c, b);

    let l = orient2d_spec(a, b, c).num;
    let r = orient2d_spec(a, c, b).num;
    assert(l == -r);
    if l == 0 {
        assert(-r == l);
        assert(-r == 0);
        assert((-r == 0) ==> (r == 0)) by (nonlinear_arith);
        assert(r == 0);
    }
    if r == 0 {
        lemma_mul_by_zero_is_zero(-1);
        assert((-1) * r == 0);
        assert((-1) * r == -r) by (nonlinear_arith);
        assert(-r == 0);
        assert(l == -r);
        assert(l == 0);
    }
    assert((l == 0) == (r == 0));

    assert(is_collinear(a, b, c) == (l == 0));
    assert(is_collinear(a, c, b) == (r == 0));
    assert(is_collinear(a, b, c) == is_collinear(a, c, b));
}

pub proof fn lemma_ccw_swap_to_cw(a: Point2, b: Point2, c: Point2)
    ensures
        is_ccw(a, b, c) == is_cw(a, c, b),
{
    lemma_is_ccw_swap_to_cw(a, b, c);
    assert(is_ccw(a, b, c) == is_cw(a, c, b));
}

pub proof fn lemma_is_ccw_swap_to_cw(a: Point2, b: Point2, c: Point2)
    ensures
        is_ccw(a, b, c) == is_cw(a, c, b),
{
    lemma_is_ccw_iff_positive(a, b, c);
    lemma_is_cw_iff_negative(a, c, b);
    lemma_orient2d_swap_antisymmetric_num(a, b, c);

    let l = orient2d_spec(a, b, c).num;
    let r = orient2d_spec(a, c, b).num;
    assert(l == -r);
    assert(l + r == (-r) + r);
    assert((-r) + r == 0) by (nonlinear_arith);
    assert(l + r == 0);
    assert((l + r == 0) ==> ((l > 0) == (r < 0))) by (nonlinear_arith);
    assert((l > 0) == (r < 0));

    assert(is_ccw(a, b, c) == (l > 0));
    assert(is_cw(a, c, b) == (r < 0));
    assert(is_ccw(a, b, c) == is_cw(a, c, b));
}

pub proof fn lemma_is_cw_swap_to_ccw(a: Point2, b: Point2, c: Point2)
    ensures
        is_cw(a, b, c) == is_ccw(a, c, b),
{
    lemma_is_cw_iff_negative(a, b, c);
    lemma_is_ccw_iff_positive(a, c, b);
    lemma_orient2d_swap_antisymmetric_num(a, b, c);

    let l = orient2d_spec(a, b, c).num;
    let r = orient2d_spec(a, c, b).num;
    assert(l == -r);
    assert(l + r == (-r) + r);
    assert((-r) + r == 0) by (nonlinear_arith);
    assert(l + r == 0);
    assert((l + r == 0) ==> ((l < 0) == (r > 0))) by (nonlinear_arith);
    assert((l < 0) == (r > 0));

    assert(is_cw(a, b, c) == (l < 0));
    assert(is_ccw(a, c, b) == (r > 0));
    assert(is_cw(a, b, c) == is_ccw(a, c, b));
}

pub proof fn lemma_orientation_spec_swap_collinear(a: Point2, b: Point2, c: Point2)
    ensures
        (orientation_spec(a, b, c) is Collinear) == (orientation_spec(a, c, b) is Collinear),
{
    lemma_orientation_spec_matches_predicates(a, b, c);
    lemma_orientation_spec_matches_predicates(a, c, b);
    lemma_is_collinear_swap(a, b, c);
    assert((orientation_spec(a, b, c) is Collinear) == is_collinear(a, b, c));
    assert((orientation_spec(a, c, b) is Collinear) == is_collinear(a, c, b));
    assert((orientation_spec(a, b, c) is Collinear) == (orientation_spec(a, c, b) is Collinear));
}

pub proof fn lemma_orientation_spec_swap(a: Point2, b: Point2, c: Point2)
    ensures
        (orientation_spec(a, b, c) is Ccw) == (orientation_spec(a, c, b) is Cw),
        (orientation_spec(a, b, c) is Cw) == (orientation_spec(a, c, b) is Ccw),
        (orientation_spec(a, b, c) is Collinear) == (orientation_spec(a, c, b) is Collinear),
{
    lemma_orientation_spec_matches_predicates(a, b, c);
    lemma_orientation_spec_matches_predicates(a, c, b);
    lemma_is_ccw_swap_to_cw(a, b, c);
    lemma_is_cw_swap_to_ccw(a, b, c);
    lemma_orientation_spec_swap_collinear(a, b, c);

    assert((orientation_spec(a, b, c) is Ccw) == is_ccw(a, b, c));
    assert((orientation_spec(a, c, b) is Cw) == is_cw(a, c, b));
    assert((orientation_spec(a, b, c) is Cw) == is_cw(a, b, c));
    assert((orientation_spec(a, c, b) is Ccw) == is_ccw(a, c, b));
    assert((orientation_spec(a, b, c) is Collinear) == is_collinear(a, b, c));
    assert((orientation_spec(a, c, b) is Collinear) == is_collinear(a, c, b));
}

pub proof fn lemma_orient2d_cyclic_eqv(a: Point2, b: Point2, c: Point2)
    ensures
        orient2d_spec(a, b, c).eqv_spec(orient2d_spec(b, c, a)),
{
    let ba = b.sub_spec(a);
    let ca = c.sub_spec(a);
    let cb = c.sub_spec(b);
    let ab = a.sub_spec(b);

    let o1 = orient2d_spec(a, b, c);
    let o2 = orient2d_spec(b, c, a);

    let ca_split = cb.add_spec(ba);
    Point2::lemma_sub_chain_eqv(c, b, a);
    assert(ca.x.eqv_spec(ca_split.x));
    assert(ca.y.eqv_spec(ca_split.y));
    Scalar::lemma_eqv_reflexive(ba.x);
    Scalar::lemma_eqv_reflexive(ba.y);
    Vec2::lemma_cross_eqv_congruence(ba, ba, ca, ca_split);
    assert(o1 == ba.cross_spec(ca));
    let o_mid1 = ba.cross_spec(ca_split);
    assert(o1.eqv_spec(o_mid1));

    Vec2::lemma_cross_add_self_right_eqv(ba, cb);
    let o_mid2 = ba.cross_spec(cb);
    assert(o_mid1 == ba.cross_spec(cb.add_spec(ba)));
    assert(o_mid1.eqv_spec(o_mid2));

    Point2::lemma_sub_antisymmetric(a, b);
    assert(ab == ba.neg_spec());
    Vec2::lemma_cross_neg_right(cb, ba);
    Vec2::lemma_cross_antisymmetric(ba, cb);
    assert(o2 == cb.cross_spec(ab));
    assert(cb.cross_spec(ab) == cb.cross_spec(ba.neg_spec()));
    assert(cb.cross_spec(ba.neg_spec()) == cb.cross_spec(ba).neg_spec());
    assert(o2 == cb.cross_spec(ba).neg_spec());
    assert(o_mid2 == ba.cross_spec(cb));
    assert(ba.cross_spec(cb) == cb.cross_spec(ba).neg_spec());
    assert(o_mid2 == o2);
    Scalar::lemma_eqv_reflexive(o2);
    assert(o_mid2.eqv_spec(o2));

    Scalar::lemma_eqv_transitive(o1, o_mid1, o_mid2);
    Scalar::lemma_eqv_transitive(o1, o_mid2, o2);
    assert(o1.eqv_spec(o2));
}

pub proof fn lemma_orient2d_permutation_table_eqv(a: Point2, b: Point2, c: Point2)
    ensures
        orient2d_spec(a, b, c).eqv_spec(orient2d_spec(b, c, a)),
        orient2d_spec(a, b, c).eqv_spec(orient2d_spec(c, a, b)),
        orient2d_spec(a, c, b).eqv_spec(orient2d_spec(a, b, c).neg_spec()),
        orient2d_spec(b, a, c).eqv_spec(orient2d_spec(a, b, c).neg_spec()),
        orient2d_spec(c, b, a).eqv_spec(orient2d_spec(a, b, c).neg_spec()),
{
    let oabc = orient2d_spec(a, b, c);
    let obca = orient2d_spec(b, c, a);
    let ocab = orient2d_spec(c, a, b);
    let oacb = orient2d_spec(a, c, b);
    let obac = orient2d_spec(b, a, c);
    let ocba = orient2d_spec(c, b, a);

    lemma_orient2d_cyclic_eqv(a, b, c);
    assert(oabc.eqv_spec(obca));

    lemma_orient2d_cyclic_eqv(c, a, b);
    assert(ocab.eqv_spec(oabc));
    Scalar::lemma_eqv_symmetric(ocab, oabc);
    assert(oabc.eqv_spec(ocab));

    lemma_orient2d_swap_antisymmetric(a, c, b);
    assert(oacb == oabc.neg_spec());
    Scalar::lemma_eqv_reflexive(oacb);
    assert(oacb.eqv_spec(oabc.neg_spec()));

    lemma_orient2d_cyclic_eqv(b, a, c);
    assert(obac.eqv_spec(oacb));
    Scalar::lemma_eqv_transitive(obac, oacb, oabc.neg_spec());
    assert(obac.eqv_spec(oabc.neg_spec()));

    lemma_orient2d_cyclic_eqv(c, b, a);
    assert(ocba.eqv_spec(obac));
    Scalar::lemma_eqv_transitive(ocba, obac, oabc.neg_spec());
    assert(ocba.eqv_spec(oabc.neg_spec()));
}

pub proof fn lemma_orient2d_cyclic_invariant(a: Point2, b: Point2, c: Point2)
    ensures
        orient2d_spec(a, b, c).eqv_spec(orient2d_spec(b, c, a)),
{
    lemma_orient2d_cyclic_eqv(a, b, c);
    assert(orient2d_spec(a, b, c).eqv_spec(orient2d_spec(b, c, a)));
}

pub proof fn lemma_orient2d_permutation_table(a: Point2, b: Point2, c: Point2)
    ensures
        orient2d_spec(a, b, c).eqv_spec(orient2d_spec(b, c, a)),
        orient2d_spec(a, b, c).eqv_spec(orient2d_spec(c, a, b)),
        orient2d_spec(a, c, b).eqv_spec(orient2d_spec(a, b, c).neg_spec()),
        orient2d_spec(b, a, c).eqv_spec(orient2d_spec(a, b, c).neg_spec()),
        orient2d_spec(c, b, a).eqv_spec(orient2d_spec(a, b, c).neg_spec()),
{
    lemma_orient2d_permutation_table_eqv(a, b, c);
    assert(orient2d_spec(a, b, c).eqv_spec(orient2d_spec(b, c, a)));
    assert(orient2d_spec(a, b, c).eqv_spec(orient2d_spec(c, a, b)));
    assert(orient2d_spec(a, c, b).eqv_spec(orient2d_spec(a, b, c).neg_spec()));
    assert(orient2d_spec(b, a, c).eqv_spec(orient2d_spec(a, b, c).neg_spec()));
    assert(orient2d_spec(c, b, a).eqv_spec(orient2d_spec(a, b, c).neg_spec()));
}

} // verus!
