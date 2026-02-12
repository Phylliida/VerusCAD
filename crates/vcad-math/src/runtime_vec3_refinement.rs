use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec3::RuntimeVec3;
use crate::scalar::Scalar;
use crate::vec3::Vec3;
use vstd::prelude::*;
use vstd::view::View;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRuntimeVec3(RuntimeVec3);

impl View for RuntimeVec3 {
    type V = Vec3;

    uninterp spec fn view(&self) -> Vec3;
}

pub assume_specification[ RuntimeVec3::new ](
    x: RuntimeScalar,
    y: RuntimeScalar,
    z: RuntimeScalar,
) -> (out: RuntimeVec3)
    ensures
        out@ == (Vec3 { x: x@, y: y@, z: z@ }),
;

pub assume_specification[ RuntimeVec3::from_ints ](x: i64, y: i64, z: i64) -> (out: RuntimeVec3)
    ensures
        out@ == Vec3::from_ints_spec(x as int, y as int, z as int),
;

pub assume_specification[ RuntimeVec3::zero ]() -> (out: RuntimeVec3)
    ensures
        out@ == Vec3::zero_spec(),
;

pub assume_specification[ RuntimeVec3::add ](this: &RuntimeVec3, rhs: &RuntimeVec3) -> (out: RuntimeVec3)
    ensures
        out@ == this@.add_spec(rhs@),
;

pub assume_specification[ RuntimeVec3::sub ](this: &RuntimeVec3, rhs: &RuntimeVec3) -> (out: RuntimeVec3)
    ensures
        out@ == this@.sub_spec(rhs@),
;

pub assume_specification[ RuntimeVec3::neg ](this: &RuntimeVec3) -> (out: RuntimeVec3)
    ensures
        out@ == this@.neg_spec(),
;

pub assume_specification[ RuntimeVec3::scale ](this: &RuntimeVec3, k: &RuntimeScalar) -> (out: RuntimeVec3)
    ensures
        out@ == this@.scale_spec(k@),
;

pub assume_specification[ RuntimeVec3::dot ](this: &RuntimeVec3, rhs: &RuntimeVec3) -> (out: RuntimeScalar)
    ensures
        out@ == this@.dot_spec(rhs@),
;

pub assume_specification[ RuntimeVec3::cross ](this: &RuntimeVec3, rhs: &RuntimeVec3) -> (out: RuntimeVec3)
    ensures
        out@ == this@.cross_spec(rhs@),
;

pub assume_specification[ RuntimeVec3::norm2 ](this: &RuntimeVec3) -> (out: RuntimeScalar)
    ensures
        out@ == this@.norm2_spec(),
;

#[allow(dead_code)]
pub fn runtime_vec3_add_pair_commutative(a: &RuntimeVec3, b: &RuntimeVec3) -> (pair: (
    RuntimeVec3,
    RuntimeVec3,
))
    ensures
        pair.0@ == a@.add_spec(b@),
        pair.1@ == b@.add_spec(a@),
        pair.0@.eqv_spec(pair.1@),
{
    let ab = a.add(b);
    let ba = b.add(a);
    proof {
        Vec3::lemma_add_commutative(a@, b@);
        assert(a@.add_spec(b@).eqv_spec(b@.add_spec(a@)));
        assert(ab@.eqv_spec(ba@));
    }
    (ab, ba)
}

#[allow(dead_code)]
pub fn runtime_vec3_sub_matches_add_neg(a: &RuntimeVec3, b: &RuntimeVec3) -> (pair: (
    RuntimeVec3,
    RuntimeVec3,
))
    ensures
        pair.0@ == a@.sub_spec(b@),
        pair.1@ == a@.add_spec(b@.neg_spec()),
        pair.0@ == pair.1@,
{
    let sub = a.sub(b);
    let negb = b.neg();
    let add_neg = a.add(&negb);
    proof {
        Vec3::lemma_sub_is_add_neg(a@, b@);
        assert(a@.sub_spec(b@) == a@.add_spec(b@.neg_spec()));
        assert(sub@ == add_neg@);
    }
    (sub, add_neg)
}

#[allow(dead_code)]
pub fn runtime_vec3_dot_pair_symmetric(a: &RuntimeVec3, b: &RuntimeVec3) -> (pair: (
    RuntimeScalar,
    RuntimeScalar,
))
    ensures
        pair.0@ == a@.dot_spec(b@),
        pair.1@ == b@.dot_spec(a@),
        pair.0@.eqv_spec(pair.1@),
{
    let ab = a.dot(b);
    let ba = b.dot(a);
    proof {
        Vec3::lemma_dot_symmetric(a@, b@);
        assert(a@.dot_spec(b@).eqv_spec(b@.dot_spec(a@)));
        assert(ab@.eqv_spec(ba@));
    }
    (ab, ba)
}

#[allow(dead_code)]
pub fn runtime_vec3_cross_pair_antisymmetric(a: &RuntimeVec3, b: &RuntimeVec3) -> (pair: (
    RuntimeVec3,
    RuntimeVec3,
))
    ensures
        pair.0@ == a@.cross_spec(b@),
        pair.1@ == b@.cross_spec(a@).neg_spec(),
        pair.0@ == pair.1@,
{
    let ab = a.cross(b);
    let ba = b.cross(a);
    let neg_ba = ba.neg();
    proof {
        Vec3::lemma_cross_antisymmetric(a@, b@);
        assert(a@.cross_spec(b@) == b@.cross_spec(a@).neg_spec());
        assert(ab@ == neg_ba@);
    }
    (ab, neg_ba)
}

#[allow(dead_code)]
pub fn runtime_vec3_dot_linear_right(a: &RuntimeVec3, b: &RuntimeVec3, c: &RuntimeVec3) -> (pair: (
    RuntimeScalar,
    RuntimeScalar,
))
    ensures
        pair.0@ == a@.dot_spec(b@.add_spec(c@)),
        pair.1@ == a@.dot_spec(b@).add_spec(a@.dot_spec(c@)),
        pair.0@.eqv_spec(pair.1@),
{
    let bc = b.add(c);
    let lhs = a.dot(&bc);
    let ab = a.dot(b);
    let ac = a.dot(c);
    let rhs = ab.add(&ac);
    proof {
        Vec3::lemma_dot_linear_right(a@, b@, c@);
        assert(a@.dot_spec(b@.add_spec(c@)).eqv_spec(a@.dot_spec(b@).add_spec(a@.dot_spec(c@))));
        assert(lhs@.eqv_spec(rhs@));
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_vec3_cross_linear_right(a: &RuntimeVec3, b: &RuntimeVec3, c: &RuntimeVec3) -> (pair: (
    RuntimeVec3,
    RuntimeVec3,
))
    ensures
        pair.0@ == a@.cross_spec(b@.add_spec(c@)),
        pair.1@ == a@.cross_spec(b@).add_spec(a@.cross_spec(c@)),
        pair.0@.eqv_spec(pair.1@),
{
    let bc = b.add(c);
    let lhs = a.cross(&bc);
    let ab = a.cross(b);
    let ac = a.cross(c);
    let rhs = ab.add(&ac);
    proof {
        Vec3::lemma_cross_linear_right(a@, b@, c@);
        assert(a@.cross_spec(b@.add_spec(c@)).eqv_spec(a@.cross_spec(b@).add_spec(a@.cross_spec(c@))));
        assert(lhs@.eqv_spec(rhs@));
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_vec3_norm2_nonnegative(v: &RuntimeVec3) -> (out: RuntimeScalar)
    ensures
        out@ == v@.norm2_spec(),
        Scalar::from_int_spec(0).le_spec(out@),
{
    let out = v.norm2();
    proof {
        Vec3::lemma_norm2_nonnegative(v@);
        assert(Scalar::from_int_spec(0).le_spec(v@.norm2_spec()));
        assert(Scalar::from_int_spec(0).le_spec(out@));
    }
    out
}

#[allow(dead_code)]
pub fn runtime_vec3_norm2_zero_iff_zero(v: &RuntimeVec3) -> (out: RuntimeScalar)
    ensures
        out@ == v@.norm2_spec(),
        out@.eqv_spec(Scalar::from_int_spec(0)) == v@.eqv_spec(Vec3::zero_spec()),
{
    let out = v.norm2();
    proof {
        Vec3::lemma_norm2_zero_iff_zero(v@);
        assert(v@.norm2_spec().eqv_spec(Scalar::from_int_spec(0)) == v@.eqv_spec(Vec3::zero_spec()));
        assert(out@.eqv_spec(Scalar::from_int_spec(0)) == v@.eqv_spec(Vec3::zero_spec()));
    }
    out
}

} // verus!
