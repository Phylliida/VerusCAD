use crate::point3::{dist2_spec, Point3};
use crate::runtime_point3::RuntimePoint3;
use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec3::RuntimeVec3;
use crate::scalar::Scalar;
use vstd::prelude::*;
use vstd::view::View;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRuntimePoint3(RuntimePoint3);

impl View for RuntimePoint3 {
    type V = Point3;

    uninterp spec fn view(&self) -> Point3;
}

pub assume_specification[ RuntimePoint3::new ](
    x: RuntimeScalar,
    y: RuntimeScalar,
    z: RuntimeScalar,
) -> (out: RuntimePoint3)
    ensures
        out@ == (Point3 { x: x@, y: y@, z: z@ }),
;

pub assume_specification[ RuntimePoint3::from_ints ](x: i64, y: i64, z: i64) -> (out: RuntimePoint3)
    ensures
        out@ == Point3::from_ints_spec(x as int, y as int, z as int),
;

pub assume_specification[ RuntimePoint3::add_vec ](
    this: &RuntimePoint3,
    v: &RuntimeVec3,
) -> (out: RuntimePoint3)
    ensures
        out@ == this@.add_vec_spec(v@),
;

pub assume_specification[ RuntimePoint3::sub ](
    this: &RuntimePoint3,
    rhs: &RuntimePoint3,
) -> (out: RuntimeVec3)
    ensures
        out@ == this@.sub_spec(rhs@),
;

pub assume_specification[ RuntimePoint3::dist2 ](
    this: &RuntimePoint3,
    rhs: &RuntimePoint3,
) -> (out: RuntimeScalar)
    ensures
        out@ == dist2_spec(this@, rhs@),
;

#[allow(dead_code)]
pub fn runtime_point3_sub_then_add_cancel(p: &RuntimePoint3, q: &RuntimePoint3) -> (out: RuntimePoint3)
    ensures
        out@ == q@.add_vec_spec(p@.sub_spec(q@)),
        out@.eqv_spec(p@),
{
    let d = p.sub(q);
    let out = q.add_vec(&d);
    proof {
        Point3::lemma_sub_then_add_cancel(p@, q@);
        assert(q@.add_vec_spec(p@.sub_spec(q@)).eqv_spec(p@));
        assert(out@.eqv_spec(p@));
    }
    out
}

#[allow(dead_code)]
pub fn runtime_point3_dist2_translation_invariant(
    p: &RuntimePoint3,
    q: &RuntimePoint3,
    t: &RuntimeVec3,
) -> (pair: (RuntimeScalar, RuntimeScalar))
    ensures
        pair.0@ == dist2_spec(p@.add_vec_spec(t@), q@.add_vec_spec(t@)),
        pair.1@ == dist2_spec(p@, q@),
        pair.0@.eqv_spec(pair.1@),
{
    let pt = p.add_vec(t);
    let qt = q.add_vec(t);
    let lhs = pt.dist2(&qt);
    let rhs = p.dist2(q);
    proof {
        crate::point3::lemma_dist2_translation_invariant(p@, q@, t@);
        assert(dist2_spec(p@.add_vec_spec(t@), q@.add_vec_spec(t@)).eqv_spec(dist2_spec(p@, q@)));
        assert(lhs@.eqv_spec(rhs@));
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_point3_dist2_is_sub_norm2(p: &RuntimePoint3, q: &RuntimePoint3) -> (pair: (
    RuntimeScalar,
    RuntimeScalar,
))
    ensures
        pair.0@ == dist2_spec(p@, q@),
        pair.1@ == p@.sub_spec(q@).norm2_spec(),
        pair.0@ == pair.1@,
{
    let d = p.dist2(q);
    let sub = p.sub(q);
    let n = sub.norm2();
    proof {
        crate::point3::lemma_dist2_is_sub_norm2(p@, q@);
        assert(dist2_spec(p@, q@) == p@.sub_spec(q@).norm2_spec());
        assert(d@ == n@);
    }
    (d, n)
}

#[allow(dead_code)]
pub fn runtime_point3_dist2_nonnegative(p: &RuntimePoint3, q: &RuntimePoint3) -> (out: RuntimeScalar)
    ensures
        out@ == dist2_spec(p@, q@),
        Scalar::from_int_spec(0).le_spec(out@),
{
    let out = p.dist2(q);
    proof {
        crate::point3::lemma_dist2_nonnegative(p@, q@);
        assert(Scalar::from_int_spec(0).le_spec(dist2_spec(p@, q@)));
        assert(Scalar::from_int_spec(0).le_spec(out@));
    }
    out
}

#[allow(dead_code)]
pub fn runtime_point3_dist2_zero_iff_equal_points(p: &RuntimePoint3, q: &RuntimePoint3) -> (out: RuntimeScalar)
    ensures
        out@ == dist2_spec(p@, q@),
        out@.eqv_spec(Scalar::from_int_spec(0)) == p@.eqv_spec(q@),
{
    let out = p.dist2(q);
    proof {
        crate::point3::lemma_dist2_zero_iff_equal_points(p@, q@);
        assert(dist2_spec(p@, q@).eqv_spec(Scalar::from_int_spec(0)) == p@.eqv_spec(q@));
        assert(out@.eqv_spec(Scalar::from_int_spec(0)) == p@.eqv_spec(q@));
    }
    out
}

#[allow(dead_code)]
pub fn runtime_point3_dist2_self_zero(p: &RuntimePoint3) -> (out: RuntimeScalar)
    ensures
        out@ == dist2_spec(p@, p@),
        out@.eqv_spec(Scalar::from_int_spec(0)),
{
    let out = p.dist2(p);
    proof {
        crate::point3::lemma_dist2_self_zero(p@);
        assert(dist2_spec(p@, p@).eqv_spec(Scalar::from_int_spec(0)));
        assert(out@.eqv_spec(Scalar::from_int_spec(0)));
    }
    out
}

} // verus!
