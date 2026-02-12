use vstd::prelude::*;
use vstd::arithmetic::mul::{lemma_mul_by_zero_is_zero, lemma_mul_nonzero};
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
        assert((-1) * r == -r) by (nonlinear_arith);
        assert((-1) * r == 0);
        if r != 0 {
            lemma_mul_nonzero(-1, r);
            assert(-1 != 0);
            assert(-1 != 0 && r != 0);
            assert((-1) * r != 0);
            assert(false);
        }
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
