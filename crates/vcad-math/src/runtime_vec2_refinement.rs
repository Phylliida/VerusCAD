use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec2::RuntimeVec2;
use crate::vec2::Vec2;
use vstd::prelude::*;
use vstd::view::View;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRuntimeVec2(RuntimeVec2);

impl View for RuntimeVec2 {
    type V = Vec2;

    uninterp spec fn view(&self) -> Vec2;
}

pub assume_specification[ RuntimeVec2::new ](x: RuntimeScalar, y: RuntimeScalar) -> (out: RuntimeVec2)
    ensures
        out@ == (Vec2 { x: x@, y: y@ }),
;

pub assume_specification[ RuntimeVec2::from_ints ](x: i64, y: i64) -> (out: RuntimeVec2)
    ensures
        out@ == Vec2::from_ints_spec(x as int, y as int),
;

pub assume_specification[ RuntimeVec2::zero ]() -> (out: RuntimeVec2)
    ensures
        out@ == Vec2::zero_spec(),
;

pub assume_specification[ RuntimeVec2::add ](this: &RuntimeVec2, rhs: &RuntimeVec2) -> (out: RuntimeVec2)
    ensures
        out@ == this@.add_spec(rhs@),
;

pub assume_specification[ RuntimeVec2::sub ](this: &RuntimeVec2, rhs: &RuntimeVec2) -> (out: RuntimeVec2)
    ensures
        out@ == this@.sub_spec(rhs@),
;

pub assume_specification[ RuntimeVec2::neg ](this: &RuntimeVec2) -> (out: RuntimeVec2)
    ensures
        out@ == this@.neg_spec(),
;

pub assume_specification[ RuntimeVec2::scale ](this: &RuntimeVec2, k: &RuntimeScalar) -> (out: RuntimeVec2)
    ensures
        out@ == this@.scale_spec(k@),
;

pub assume_specification[ RuntimeVec2::dot ](this: &RuntimeVec2, rhs: &RuntimeVec2) -> (out: RuntimeScalar)
    ensures
        out@ == this@.dot_spec(rhs@),
;

pub assume_specification[ RuntimeVec2::cross ](this: &RuntimeVec2, rhs: &RuntimeVec2) -> (out: RuntimeScalar)
    ensures
        out@ == this@.cross_spec(rhs@),
;

pub assume_specification[ RuntimeVec2::norm2 ](this: &RuntimeVec2) -> (out: RuntimeScalar)
    ensures
        out@ == this@.norm2_spec(),
;

#[allow(dead_code)]
pub fn runtime_vec2_add_pair_commutative(a: &RuntimeVec2, b: &RuntimeVec2) -> (pair: (
    RuntimeVec2,
    RuntimeVec2,
))
    ensures
        pair.0@ == a@.add_spec(b@),
        pair.1@ == b@.add_spec(a@),
        pair.0@.eqv_spec(pair.1@),
{
    let ab = a.add(b);
    let ba = b.add(a);
    proof {
        Vec2::lemma_add_commutative(a@, b@);
        assert(a@.add_spec(b@).eqv_spec(b@.add_spec(a@)));
        assert(ab@.eqv_spec(ba@));
    }
    (ab, ba)
}

#[allow(dead_code)]
pub fn runtime_vec2_add_pair_associative(a: &RuntimeVec2, b: &RuntimeVec2, c: &RuntimeVec2) -> (pair: (
    RuntimeVec2,
    RuntimeVec2,
))
    ensures
        pair.0@ == a@.add_spec(b@).add_spec(c@),
        pair.1@ == a@.add_spec(b@.add_spec(c@)),
        pair.0@.eqv_spec(pair.1@),
{
    let ab = a.add(b);
    let lhs = ab.add(c);
    let bc = b.add(c);
    let rhs = a.add(&bc);
    proof {
        Vec2::lemma_add_associative(a@, b@, c@);
        assert(a@.add_spec(b@).add_spec(c@).eqv_spec(a@.add_spec(b@.add_spec(c@))));
        assert(lhs@.eqv_spec(rhs@));
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_vec2_sub_matches_add_neg(a: &RuntimeVec2, b: &RuntimeVec2) -> (pair: (
    RuntimeVec2,
    RuntimeVec2,
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
        Vec2::lemma_sub_is_add_neg(a@, b@);
        assert(a@.sub_spec(b@) == a@.add_spec(b@.neg_spec()));
        assert(sub@ == add_neg@);
    }
    (sub, add_neg)
}

#[allow(dead_code)]
pub fn runtime_vec2_dot_pair_symmetric(a: &RuntimeVec2, b: &RuntimeVec2) -> (pair: (
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
        Vec2::lemma_dot_symmetric(a@, b@);
        assert(a@.dot_spec(b@).eqv_spec(b@.dot_spec(a@)));
        assert(ab@.eqv_spec(ba@));
    }
    (ab, ba)
}

#[allow(dead_code)]
pub fn runtime_vec2_cross_pair_antisymmetric(a: &RuntimeVec2, b: &RuntimeVec2) -> (pair: (
    RuntimeScalar,
    RuntimeScalar,
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
        Vec2::lemma_cross_antisymmetric(a@, b@);
        assert(a@.cross_spec(b@) == b@.cross_spec(a@).neg_spec());
        assert(ab@ == neg_ba@);
    }
    (ab, neg_ba)
}

} // verus!
