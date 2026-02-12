use crate::point3::Point3;
use crate::scalar::Scalar;
use crate::vec3::Vec3;
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

} // verus!
