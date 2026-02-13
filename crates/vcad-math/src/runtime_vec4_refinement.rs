use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec4::RuntimeVec4;
use crate::scalar::Scalar;
use crate::vec4::Vec4;
use vstd::prelude::*;
use vstd::view::View;

verus! {

#[verifier::external_type_specification]
pub struct ExRuntimeVec4(RuntimeVec4);

impl View for RuntimeVec4 {
    type V = Vec4;

    open spec fn view(&self) -> Vec4 {
        Vec4 { x: self.x@, y: self.y@, z: self.z@, w: self.w@ }
    }
}

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
