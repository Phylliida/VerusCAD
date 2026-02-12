use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec4::RuntimeVec4;
use crate::scalar::Scalar;
use crate::vec4::Vec4;
use vstd::prelude::*;
use vstd::view::View;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRuntimeVec4(RuntimeVec4);

impl View for RuntimeVec4 {
    type V = Vec4;

    uninterp spec fn view(&self) -> Vec4;
}

pub assume_specification[ RuntimeVec4::new ](
    x: RuntimeScalar,
    y: RuntimeScalar,
    z: RuntimeScalar,
    w: RuntimeScalar,
) -> (out: RuntimeVec4)
    ensures
        out@ == (Vec4 { x: x@, y: y@, z: z@, w: w@ }),
;

pub assume_specification[ RuntimeVec4::from_ints ](x: i64, y: i64, z: i64, w: i64) -> (out: RuntimeVec4)
    ensures
        out@ == Vec4::from_ints_spec(x as int, y as int, z as int, w as int),
;

pub assume_specification[ RuntimeVec4::zero ]() -> (out: RuntimeVec4)
    ensures
        out@ == Vec4::zero_spec(),
;

pub assume_specification[ RuntimeVec4::add ](this: &RuntimeVec4, rhs: &RuntimeVec4) -> (out: RuntimeVec4)
    ensures
        out@ == this@.add_spec(rhs@),
;

pub assume_specification[ RuntimeVec4::sub ](this: &RuntimeVec4, rhs: &RuntimeVec4) -> (out: RuntimeVec4)
    ensures
        out@ == this@.sub_spec(rhs@),
;

pub assume_specification[ RuntimeVec4::neg ](this: &RuntimeVec4) -> (out: RuntimeVec4)
    ensures
        out@ == this@.neg_spec(),
;

pub assume_specification[ RuntimeVec4::scale ](this: &RuntimeVec4, k: &RuntimeScalar) -> (out: RuntimeVec4)
    ensures
        out@ == this@.scale_spec(k@),
;

pub assume_specification[ RuntimeVec4::dot ](this: &RuntimeVec4, rhs: &RuntimeVec4) -> (out: RuntimeScalar)
    ensures
        out@ == this@.dot_spec(rhs@),
;

pub assume_specification[ RuntimeVec4::norm2 ](this: &RuntimeVec4) -> (out: RuntimeScalar)
    ensures
        out@ == this@.norm2_spec(),
;

#[allow(dead_code)]
pub fn runtime_vec4_add_pair_commutative(a: &RuntimeVec4, b: &RuntimeVec4) -> (pair: (
    RuntimeVec4,
    RuntimeVec4,
))
    ensures
        pair.0@ == a@.add_spec(b@),
        pair.1@ == b@.add_spec(a@),
        pair.0@.eqv_spec(pair.1@),
{
    let ab = a.add(b);
    let ba = b.add(a);
    proof {
        Vec4::lemma_add_commutative(a@, b@);
        assert(a@.add_spec(b@).eqv_spec(b@.add_spec(a@)));
        assert(ab@.eqv_spec(ba@));
    }
    (ab, ba)
}

#[allow(dead_code)]
pub fn runtime_vec4_dot_pair_symmetric(a: &RuntimeVec4, b: &RuntimeVec4) -> (pair: (
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
        Vec4::lemma_dot_symmetric(a@, b@);
        assert(a@.dot_spec(b@).eqv_spec(b@.dot_spec(a@)));
        assert(ab@.eqv_spec(ba@));
    }
    (ab, ba)
}

#[allow(dead_code)]
pub fn runtime_vec4_sub_matches_add_neg(a: &RuntimeVec4, b: &RuntimeVec4) -> (pair: (
    RuntimeVec4,
    RuntimeVec4,
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
        Vec4::lemma_sub_is_add_neg(a@, b@);
        assert(a@.sub_spec(b@) == a@.add_spec(b@.neg_spec()));
        assert(sub@ == add_neg@);
    }
    (sub, add_neg)
}

#[allow(dead_code)]
pub fn runtime_vec4_dot_linear_right(a: &RuntimeVec4, b: &RuntimeVec4, c: &RuntimeVec4) -> (pair: (
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
        Vec4::lemma_dot_linear_right(a@, b@, c@);
        assert(a@.dot_spec(b@.add_spec(c@)).eqv_spec(a@.dot_spec(b@).add_spec(a@.dot_spec(c@))));
        assert(lhs@.eqv_spec(rhs@));
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_vec4_norm2_nonnegative(v: &RuntimeVec4) -> (out: RuntimeScalar)
    ensures
        out@ == v@.norm2_spec(),
        Scalar::from_int_spec(0).le_spec(out@),
{
    let out = v.norm2();
    proof {
        Vec4::lemma_norm2_nonnegative(v@);
        assert(Scalar::from_int_spec(0).le_spec(v@.norm2_spec()));
        assert(Scalar::from_int_spec(0).le_spec(out@));
    }
    out
}

#[allow(dead_code)]
pub fn runtime_vec4_norm2_zero_iff_zero(v: &RuntimeVec4) -> (out: RuntimeScalar)
    ensures
        out@ == v@.norm2_spec(),
        out@.eqv_spec(Scalar::from_int_spec(0)) == v@.eqv_spec(Vec4::zero_spec()),
{
    let out = v.norm2();
    proof {
        Vec4::lemma_norm2_zero_iff_zero(v@);
        assert(v@.norm2_spec().eqv_spec(Scalar::from_int_spec(0)) == v@.eqv_spec(Vec4::zero_spec()));
        assert(out@.eqv_spec(Scalar::from_int_spec(0)) == v@.eqv_spec(Vec4::zero_spec()));
    }
    out
}

} // verus!
