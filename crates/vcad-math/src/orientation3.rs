use crate::point3::Point3;
use crate::scalar::Scalar;
use crate::vec3::Vec3;
use vstd::calc;
use vstd::prelude::*;

verus! {

#[derive(Structural, PartialEq, Eq)]
pub enum Orientation3 {
    Negative,
    Coplanar,
    Positive,
}

pub open spec fn orient3d_spec(a: Point3, b: Point3, c: Point3, d: Point3) -> Scalar {
    b.sub_spec(a).dot_spec(c.sub_spec(a).cross_spec(d.sub_spec(a)))
}

pub open spec fn is_positive(a: Point3, b: Point3, c: Point3, d: Point3) -> bool {
    orient3d_spec(a, b, c, d).signum() == 1
}

pub open spec fn is_negative(a: Point3, b: Point3, c: Point3, d: Point3) -> bool {
    orient3d_spec(a, b, c, d).signum() == -1
}

pub open spec fn is_coplanar(a: Point3, b: Point3, c: Point3, d: Point3) -> bool {
    orient3d_spec(a, b, c, d).signum() == 0
}

pub open spec fn orientation3_spec(a: Point3, b: Point3, c: Point3, d: Point3) -> Orientation3 {
    let s = orient3d_spec(a, b, c, d).signum();
    if s == 1 {
        Orientation3::Positive
    } else if s == -1 {
        Orientation3::Negative
    } else {
        Orientation3::Coplanar
    }
}

pub open spec fn scale_point_from_origin3_spec(p: Point3, k: Scalar) -> Point3 {
    Point3 {
        x: p.x.mul_spec(k),
        y: p.y.mul_spec(k),
        z: p.z.mul_spec(k),
    }
}

pub proof fn orient3d(a: Point3, b: Point3, c: Point3, d: Point3) -> (out: Scalar)
    ensures
        out == orient3d_spec(a, b, c, d),
{
    let ba = b.sub(a);
    let ca = c.sub(a);
    let da = d.sub(a);
    let cad = ca.cross(da);
    ba.dot(cad)
}

pub proof fn orientation3(a: Point3, b: Point3, c: Point3, d: Point3) -> (o: Orientation3)
    ensures
        o == orientation3_spec(a, b, c, d),
{
    let s = orient3d_spec(a, b, c, d).signum();
    if s == 1 {
        Orientation3::Positive
    } else if s == -1 {
        Orientation3::Negative
    } else {
        Orientation3::Coplanar
    }
}

pub proof fn lemma_orientation3_classes_exhaustive(a: Point3, b: Point3, c: Point3, d: Point3)
    ensures
        is_positive(a, b, c, d) || is_negative(a, b, c, d) || is_coplanar(a, b, c, d),
{
    let det = orient3d_spec(a, b, c, d);
    Scalar::lemma_signum_cases(det);
    assert(det.signum() == 1 || det.signum() == -1 || det.signum() == 0);
}

pub proof fn lemma_orientation3_classes_pairwise_disjoint(a: Point3, b: Point3, c: Point3, d: Point3)
    ensures
        !(is_positive(a, b, c, d) && is_negative(a, b, c, d)),
        !(is_positive(a, b, c, d) && is_coplanar(a, b, c, d)),
        !(is_negative(a, b, c, d) && is_coplanar(a, b, c, d)),
{
    let s = orient3d_spec(a, b, c, d).signum();
    assert(!(s == 1 && s == -1)) by (nonlinear_arith);
    assert(!(s == 1 && s == 0)) by (nonlinear_arith);
    assert(!(s == -1 && s == 0)) by (nonlinear_arith);
}

pub proof fn lemma_orientation3_spec_matches_predicates(a: Point3, b: Point3, c: Point3, d: Point3)
    ensures
        (orientation3_spec(a, b, c, d) is Positive) == is_positive(a, b, c, d),
        (orientation3_spec(a, b, c, d) is Negative) == is_negative(a, b, c, d),
        (orientation3_spec(a, b, c, d) is Coplanar) == is_coplanar(a, b, c, d),
{
    let det = orient3d_spec(a, b, c, d);
    let s = det.signum();
    Scalar::lemma_signum_cases(det);

    if s == 1 {
        assert(orientation3_spec(a, b, c, d) is Positive);
        assert(!(orientation3_spec(a, b, c, d) is Negative));
        assert(!(orientation3_spec(a, b, c, d) is Coplanar));
        assert(is_positive(a, b, c, d));
        assert(!is_negative(a, b, c, d));
        assert(!is_coplanar(a, b, c, d));
    } else if s == -1 {
        assert(!(orientation3_spec(a, b, c, d) is Positive));
        assert(orientation3_spec(a, b, c, d) is Negative);
        assert(!(orientation3_spec(a, b, c, d) is Coplanar));
        assert(!is_positive(a, b, c, d));
        assert(is_negative(a, b, c, d));
        assert(!is_coplanar(a, b, c, d));
    } else {
        assert(s == 0);
        assert(!(orientation3_spec(a, b, c, d) is Positive));
        assert(!(orientation3_spec(a, b, c, d) is Negative));
        assert(orientation3_spec(a, b, c, d) is Coplanar);
        assert(!is_positive(a, b, c, d));
        assert(!is_negative(a, b, c, d));
        assert(is_coplanar(a, b, c, d));
    }
}

pub proof fn lemma_orientation3_spec_exclusive(a: Point3, b: Point3, c: Point3, d: Point3)
    ensures
        (orientation3_spec(a, b, c, d) is Positive)
            || (orientation3_spec(a, b, c, d) is Negative)
            || (orientation3_spec(a, b, c, d) is Coplanar),
        !((orientation3_spec(a, b, c, d) is Positive) && (orientation3_spec(a, b, c, d) is Negative)),
        !((orientation3_spec(a, b, c, d) is Positive) && (orientation3_spec(a, b, c, d) is Coplanar)),
        !((orientation3_spec(a, b, c, d) is Negative) && (orientation3_spec(a, b, c, d) is Coplanar)),
{
    lemma_orientation3_spec_matches_predicates(a, b, c, d);
    lemma_orientation3_classes_exhaustive(a, b, c, d);
    lemma_orientation3_classes_pairwise_disjoint(a, b, c, d);
}

pub proof fn lemma_orient3d_translation_invariant(a: Point3, b: Point3, c: Point3, d: Point3, t: Vec3)
    ensures
        orient3d_spec(a.add_vec_spec(t), b.add_vec_spec(t), c.add_vec_spec(t), d.add_vec_spec(t))
            .eqv_spec(orient3d_spec(a, b, c, d)),
{
    let at = a.add_vec_spec(t);
    let bt = b.add_vec_spec(t);
    let ct = c.add_vec_spec(t);
    let dt = d.add_vec_spec(t);

    let ub1 = bt.sub_spec(at);
    let uc1 = ct.sub_spec(at);
    let ud1 = dt.sub_spec(at);

    let ub2 = b.sub_spec(a);
    let uc2 = c.sub_spec(a);
    let ud2 = d.sub_spec(a);

    crate::point3::lemma_sub_translation_invariant(b, a, t);
    crate::point3::lemma_sub_translation_invariant(c, a, t);
    crate::point3::lemma_sub_translation_invariant(d, a, t);
    assert(ub1.eqv_spec(ub2));
    assert(uc1.eqv_spec(uc2));
    assert(ud1.eqv_spec(ud2));

    Vec3::lemma_cross_eqv_congruence(uc1, uc2, ud1, ud2);
    assert(uc1.cross_spec(ud1).eqv_spec(uc2.cross_spec(ud2)));

    Vec3::lemma_dot_eqv_congruence(ub1, ub2, uc1.cross_spec(ud1), uc2.cross_spec(ud2));
    assert(ub1.dot_spec(uc1.cross_spec(ud1)).eqv_spec(ub2.dot_spec(uc2.cross_spec(ud2))));

    assert(orient3d_spec(at, bt, ct, dt).eqv_spec(orient3d_spec(a, b, c, d)));
}

pub proof fn lemma_orientation3_spec_translation_invariant(a: Point3, b: Point3, c: Point3, d: Point3, t: Vec3)
    ensures
        orientation3_spec(a.add_vec_spec(t), b.add_vec_spec(t), c.add_vec_spec(t), d.add_vec_spec(t))
            == orientation3_spec(a, b, c, d),
{
    let at = a.add_vec_spec(t);
    let bt = b.add_vec_spec(t);
    let ct = c.add_vec_spec(t);
    let dt = d.add_vec_spec(t);
    let ot = orient3d_spec(at, bt, ct, dt);
    let o = orient3d_spec(a, b, c, d);
    lemma_orient3d_translation_invariant(a, b, c, d, t);
    assert(ot.eqv_spec(o));
    Scalar::lemma_eqv_signum(ot, o);
    assert(ot.signum() == o.signum());
    assert(orientation3_spec(at, bt, ct, dt) == orientation3_spec(a, b, c, d));
}

proof fn lemma_signum_negated(a: Scalar)
    ensures
        a.neg_spec().signum() == -a.signum(),
{
    let one = Scalar::from_int_spec(1);
    let neg_one = one.neg_spec();
    let n = a.neg_spec();
    let m = neg_one.mul_spec(a);

    Scalar::lemma_mul_neg_right(a, one);
    Scalar::lemma_mul_one_identity(a);
    assert(a.mul_spec(one) == a);
    assert(a.mul_spec(one.neg_spec()) == a.mul_spec(one).neg_spec());
    assert(a.mul_spec(neg_one) == n);
    Scalar::lemma_mul_commutative(a, neg_one);
    assert(m == a.mul_spec(neg_one));
    assert(m == n);

    Scalar::lemma_signum_mul(neg_one, a);
    Scalar::lemma_signum_negative_iff(neg_one);
    assert((neg_one.signum() == -1) == (neg_one.num < 0));
    assert(neg_one.num == -1);
    assert(neg_one.num < 0);
    assert(neg_one.signum() == -1);
    assert(m.signum() == neg_one.signum() * a.signum());
    assert(m.signum() == (-1) * a.signum());
    assert(n.signum() == m.signum());
    assert(n.signum() == -a.signum());
}

proof fn lemma_scale_point_sub_eqv(p: Point3, q: Point3, k: Scalar)
    ensures
        scale_point_from_origin3_spec(p, k).sub_spec(scale_point_from_origin3_spec(q, k)).eqv_spec(p.sub_spec(q).scale_spec(k)),
{
    let lhs = scale_point_from_origin3_spec(p, k).sub_spec(scale_point_from_origin3_spec(q, k));
    let rhs = p.sub_spec(q).scale_spec(k);
    Scalar::lemma_sub_mul_right(p.x, q.x, k);
    Scalar::lemma_sub_mul_right(p.y, q.y, k);
    Scalar::lemma_sub_mul_right(p.z, q.z, k);
    assert(lhs.x == p.x.mul_spec(k).sub_spec(q.x.mul_spec(k)));
    assert(lhs.y == p.y.mul_spec(k).sub_spec(q.y.mul_spec(k)));
    assert(lhs.z == p.z.mul_spec(k).sub_spec(q.z.mul_spec(k)));
    assert(rhs.x == p.x.sub_spec(q.x).mul_spec(k));
    assert(rhs.y == p.y.sub_spec(q.y).mul_spec(k));
    assert(rhs.z == p.z.sub_spec(q.z).mul_spec(k));
    Scalar::lemma_eqv_symmetric(rhs.x, lhs.x);
    Scalar::lemma_eqv_symmetric(rhs.y, lhs.y);
    Scalar::lemma_eqv_symmetric(rhs.z, lhs.z);
    assert(lhs.x.eqv_spec(rhs.x));
    assert(lhs.y.eqv_spec(rhs.y));
    assert(lhs.z.eqv_spec(rhs.z));
    assert(lhs.eqv_spec(rhs));
}

pub proof fn lemma_orient3d_swap_cd_eqv_neg(a: Point3, b: Point3, c: Point3, d: Point3)
    ensures
        orient3d_spec(a, b, d, c).eqv_spec(orient3d_spec(a, b, c, d).neg_spec()),
{
    let ba = b.sub_spec(a);
    let ca = c.sub_spec(a);
    let da = d.sub_spec(a);
    let o = orient3d_spec(a, b, c, d);
    let os = orient3d_spec(a, b, d, c);

    Vec3::lemma_cross_antisymmetric(da, ca);
    assert(da.cross_spec(ca) == ca.cross_spec(da).neg_spec());
    Vec3::lemma_dot_neg_right(ba, ca.cross_spec(da));
    assert(ba.dot_spec(ca.cross_spec(da).neg_spec()).eqv_spec(ba.dot_spec(ca.cross_spec(da)).neg_spec()));
    assert(os == ba.dot_spec(da.cross_spec(ca)));
    assert(o == ba.dot_spec(ca.cross_spec(da)));
    assert(os == ba.dot_spec(ca.cross_spec(da).neg_spec()));
    assert(os.eqv_spec(o.neg_spec()));
}

pub proof fn lemma_orientation3_spec_swap_cd(a: Point3, b: Point3, c: Point3, d: Point3)
    ensures
        (orientation3_spec(a, b, c, d) is Positive) == (orientation3_spec(a, b, d, c) is Negative),
        (orientation3_spec(a, b, c, d) is Negative) == (orientation3_spec(a, b, d, c) is Positive),
        (orientation3_spec(a, b, c, d) is Coplanar) == (orientation3_spec(a, b, d, c) is Coplanar),
{
    let o = orient3d_spec(a, b, c, d);
    let os = orient3d_spec(a, b, d, c);
    let s = o.signum();
    let ss = os.signum();
    lemma_orient3d_swap_cd_eqv_neg(a, b, c, d);
    Scalar::lemma_eqv_signum(os, o.neg_spec());
    lemma_signum_negated(o);
    assert(ss == o.neg_spec().signum());
    assert(ss == -s);
    lemma_orientation3_spec_matches_predicates(a, b, c, d);
    lemma_orientation3_spec_matches_predicates(a, b, d, c);
    Scalar::lemma_signum_cases(o);
    if s == 1 {
        assert(ss == -s);
        calc! {
            (==)
            -s;
            { assert(s == 1); }
            -1;
        }
        assert(ss == -1);
        assert(orientation3_spec(a, b, c, d) is Positive);
        assert(!(orientation3_spec(a, b, c, d) is Negative));
        assert(!(orientation3_spec(a, b, c, d) is Coplanar));
        assert(!(orientation3_spec(a, b, d, c) is Positive));
        assert(orientation3_spec(a, b, d, c) is Negative);
        assert(!(orientation3_spec(a, b, d, c) is Coplanar));
        assert((orientation3_spec(a, b, c, d) is Positive) == (orientation3_spec(a, b, d, c) is Negative));
        assert((orientation3_spec(a, b, c, d) is Negative) == (orientation3_spec(a, b, d, c) is Positive));
        assert((orientation3_spec(a, b, c, d) is Coplanar) == (orientation3_spec(a, b, d, c) is Coplanar));
    } else if s == -1 {
        assert(ss == -s);
        calc! {
            (==)
            -s;
            { assert(s == -1); }
            1;
        }
        assert(ss == 1);
        assert(!(orientation3_spec(a, b, c, d) is Positive));
        assert(orientation3_spec(a, b, c, d) is Negative);
        assert(!(orientation3_spec(a, b, c, d) is Coplanar));
        assert(orientation3_spec(a, b, d, c) is Positive);
        assert(!(orientation3_spec(a, b, d, c) is Negative));
        assert(!(orientation3_spec(a, b, d, c) is Coplanar));
        assert((orientation3_spec(a, b, c, d) is Positive) == (orientation3_spec(a, b, d, c) is Negative));
        assert((orientation3_spec(a, b, c, d) is Negative) == (orientation3_spec(a, b, d, c) is Positive));
        assert((orientation3_spec(a, b, c, d) is Coplanar) == (orientation3_spec(a, b, d, c) is Coplanar));
    } else {
        assert(s == 0);
        assert(ss == -s);
        calc! {
            (==)
            -s;
            { assert(s == 0); }
            0;
        }
        assert(ss == 0);
        assert(!(orientation3_spec(a, b, c, d) is Positive));
        assert(!(orientation3_spec(a, b, c, d) is Negative));
        assert(orientation3_spec(a, b, c, d) is Coplanar);
        assert(!(orientation3_spec(a, b, d, c) is Positive));
        assert(!(orientation3_spec(a, b, d, c) is Negative));
        assert(orientation3_spec(a, b, d, c) is Coplanar);
        assert((orientation3_spec(a, b, c, d) is Positive) == (orientation3_spec(a, b, d, c) is Negative));
        assert((orientation3_spec(a, b, c, d) is Negative) == (orientation3_spec(a, b, d, c) is Positive));
        assert((orientation3_spec(a, b, c, d) is Coplanar) == (orientation3_spec(a, b, d, c) is Coplanar));
    }
}

pub proof fn lemma_orient3d_degenerate_repeated_points(a: Point3, b: Point3, c: Point3)
    ensures
        orient3d_spec(a, a, b, c).signum() == 0,
        orient3d_spec(a, b, c, c).signum() == 0,
{
    let z = Scalar::from_int_spec(0);
    let zv = Vec3::zero_spec();

    let aa = a.sub_spec(a);
    let ba = b.sub_spec(a);
    let ca = c.sub_spec(a);
    let o1 = orient3d_spec(a, a, b, c);
    Point3::lemma_sub_self_zero_num(a);
    Scalar::lemma_eqv_zero_iff_num_zero(aa.x);
    Scalar::lemma_eqv_zero_iff_num_zero(aa.y);
    Scalar::lemma_eqv_zero_iff_num_zero(aa.z);
    assert(aa.x.eqv_spec(z) == (aa.x.num == 0));
    assert(aa.y.eqv_spec(z) == (aa.y.num == 0));
    assert(aa.z.eqv_spec(z) == (aa.z.num == 0));
    assert(aa.x.eqv_spec(z));
    assert(aa.y.eqv_spec(z));
    assert(aa.z.eqv_spec(z));
    Vec3::lemma_eqv_from_components(aa, zv);
    assert(aa.eqv_spec(zv));
    let cw = ba.cross_spec(ca);
    Scalar::lemma_eqv_reflexive(cw.x);
    Scalar::lemma_eqv_reflexive(cw.y);
    Scalar::lemma_eqv_reflexive(cw.z);
    Vec3::lemma_dot_eqv_congruence(aa, zv, cw, cw);
    assert(o1 == aa.dot_spec(cw));
    assert(o1.eqv_spec(zv.dot_spec(cw)));
    Vec3::lemma_dot_left_zero(cw);
    assert(zv.dot_spec(cw).eqv_spec(z));
    Scalar::lemma_eqv_transitive(o1, zv.dot_spec(cw), z);
    assert(o1.eqv_spec(z));
    Scalar::lemma_eqv_signum(o1, z);
    Scalar::lemma_signum_zero_iff(z);
    assert((z.signum() == 0) == (z.num == 0));
    assert(z.num == 0);
    assert(z.signum() == 0);
    assert(o1.signum() == 0);

    let cc = c.sub_spec(a);
    let o2 = orient3d_spec(a, b, c, c);
    let cross_cc = cc.cross_spec(cc);
    Vec3::lemma_cross_self_zero(cc);
    assert(cross_cc.eqv_spec(zv));
    Scalar::lemma_eqv_reflexive(ba.x);
    Scalar::lemma_eqv_reflexive(ba.y);
    Scalar::lemma_eqv_reflexive(ba.z);
    Vec3::lemma_dot_eqv_congruence(ba, ba, cross_cc, zv);
    assert(o2 == ba.dot_spec(cross_cc));
    assert(o2.eqv_spec(ba.dot_spec(zv)));
    Vec3::lemma_dot_right_zero(ba);
    assert(ba.dot_spec(zv).eqv_spec(z));
    Scalar::lemma_eqv_transitive(o2, ba.dot_spec(zv), z);
    assert(o2.eqv_spec(z));
    Scalar::lemma_eqv_signum(o2, z);
    assert(o2.signum() == z.signum());
    assert(o2.signum() == 0);
}

pub proof fn lemma_orientation3_spec_degenerate_repeated_points(a: Point3, b: Point3, c: Point3)
    ensures
        orientation3_spec(a, a, b, c) is Coplanar,
        orientation3_spec(a, b, c, c) is Coplanar,
{
    lemma_orient3d_degenerate_repeated_points(a, b, c);
    lemma_orientation3_spec_matches_predicates(a, a, b, c);
    lemma_orientation3_spec_matches_predicates(a, b, c, c);
    assert(is_coplanar(a, a, b, c));
    assert(is_coplanar(a, b, c, c));
    assert(orientation3_spec(a, a, b, c) is Coplanar);
    assert(orientation3_spec(a, b, c, c) is Coplanar);
}

pub proof fn lemma_orientation3_spec_scale_zero_coplanar(a: Point3, b: Point3, c: Point3, d: Point3, k: Scalar)
    ensures
        (k.num == 0) ==> (
            orientation3_spec(
                scale_point_from_origin3_spec(a, k),
                scale_point_from_origin3_spec(b, k),
                scale_point_from_origin3_spec(c, k),
                scale_point_from_origin3_spec(d, k),
            ) is Coplanar
        ),
{
    if k.num == 0 {
        lemma_orientation3_spec_scale_zero_coplanar_strong(a, b, c, d, k);
        assert(
            orientation3_spec(
                scale_point_from_origin3_spec(a, k),
                scale_point_from_origin3_spec(b, k),
                scale_point_from_origin3_spec(c, k),
                scale_point_from_origin3_spec(d, k),
            ) is Coplanar
        );
    }
}

pub proof fn lemma_orientation3_spec_scale_zero_coplanar_strong(a: Point3, b: Point3, c: Point3, d: Point3, k: Scalar)
    requires
        k.num == 0,
    ensures
        orientation3_spec(
            scale_point_from_origin3_spec(a, k),
            scale_point_from_origin3_spec(b, k),
            scale_point_from_origin3_spec(c, k),
            scale_point_from_origin3_spec(d, k),
        ) is Coplanar,
{
    let sa = scale_point_from_origin3_spec(a, k);
    let sb = scale_point_from_origin3_spec(b, k);
    let sc = scale_point_from_origin3_spec(c, k);
    let sd = scale_point_from_origin3_spec(d, k);
    let ba_s = sb.sub_spec(sa);
    let ba = b.sub_spec(a);
    let z = Scalar::from_int_spec(0);
    let zv = Vec3::zero_spec();
    let o = orient3d_spec(sa, sb, sc, sd);

    lemma_scale_point_sub_eqv(b, a, k);
    assert(ba_s.eqv_spec(ba.scale_spec(k)));
    let bak = ba.scale_spec(k);
    Scalar::lemma_mul_right_zero_num(ba.x, k);
    Scalar::lemma_mul_right_zero_num(ba.y, k);
    Scalar::lemma_mul_right_zero_num(ba.z, k);
    assert(bak.x.num == 0);
    assert(bak.y.num == 0);
    assert(bak.z.num == 0);
    Scalar::lemma_eqv_zero_iff_num_zero(bak.x);
    Scalar::lemma_eqv_zero_iff_num_zero(bak.y);
    Scalar::lemma_eqv_zero_iff_num_zero(bak.z);
    assert(bak.x.eqv_spec(z) == (bak.x.num == 0));
    assert(bak.y.eqv_spec(z) == (bak.y.num == 0));
    assert(bak.z.eqv_spec(z) == (bak.z.num == 0));
    assert(bak.x.eqv_spec(z));
    assert(bak.y.eqv_spec(z));
    assert(bak.z.eqv_spec(z));
    Vec3::lemma_eqv_from_components(bak, zv);
    assert(bak.eqv_spec(zv));
    assert(ba_s.x.eqv_spec(bak.x));
    assert(ba_s.y.eqv_spec(bak.y));
    assert(ba_s.z.eqv_spec(bak.z));
    Scalar::lemma_eqv_transitive(ba_s.x, bak.x, zv.x);
    Scalar::lemma_eqv_transitive(ba_s.y, bak.y, zv.y);
    Scalar::lemma_eqv_transitive(ba_s.z, bak.z, zv.z);
    assert(ba_s.eqv_spec(zv));

    let cd = sc.sub_spec(sa).cross_spec(sd.sub_spec(sa));
    Scalar::lemma_eqv_reflexive(cd.x);
    Scalar::lemma_eqv_reflexive(cd.y);
    Scalar::lemma_eqv_reflexive(cd.z);
    Vec3::lemma_dot_eqv_congruence(ba_s, zv, cd, cd);
    assert(o == ba_s.dot_spec(cd));
    assert(o.eqv_spec(zv.dot_spec(cd)));
    Vec3::lemma_dot_left_zero(cd);
    assert(zv.dot_spec(cd).eqv_spec(z));
    Scalar::lemma_eqv_transitive(o, zv.dot_spec(cd), z);
    assert(o.eqv_spec(z));
    Scalar::lemma_eqv_signum(o, z);
    Scalar::lemma_signum_zero_iff(z);
    assert((z.signum() == 0) == (z.num == 0));
    assert(z.num == 0);
    assert(z.signum() == 0);
    assert(o.signum() == 0);
    assert(orientation3_spec(sa, sb, sc, sd) is Coplanar);
}

} // verus!
