use crate::quaternion::Quaternion;
use crate::runtime_quaternion::RuntimeQuaternion;
use crate::runtime_scalar::RuntimeScalar;
use vstd::prelude::*;
use vstd::view::View;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRuntimeQuaternion(RuntimeQuaternion);

impl View for RuntimeQuaternion {
    type V = Quaternion;

    uninterp spec fn view(&self) -> Quaternion;
}

pub assume_specification[ RuntimeQuaternion::new ](
    w: RuntimeScalar,
    x: RuntimeScalar,
    y: RuntimeScalar,
    z: RuntimeScalar,
) -> (out: RuntimeQuaternion)
    ensures
        out@ == (Quaternion { w: w@, x: x@, y: y@, z: z@ }),
;

pub assume_specification[ RuntimeQuaternion::from_ints ](
    w: i64,
    x: i64,
    y: i64,
    z: i64,
) -> (out: RuntimeQuaternion)
    ensures
        out@ == Quaternion::from_ints_spec(w as int, x as int, y as int, z as int),
;

pub assume_specification[ RuntimeQuaternion::zero ]() -> (out: RuntimeQuaternion)
    ensures
        out@ == Quaternion::zero_spec(),
;

pub assume_specification[ RuntimeQuaternion::one ]() -> (out: RuntimeQuaternion)
    ensures
        out@ == Quaternion::one_spec(),
;

pub assume_specification[ RuntimeQuaternion::add ](
    this: &RuntimeQuaternion,
    rhs: &RuntimeQuaternion,
) -> (out: RuntimeQuaternion)
    ensures
        out@ == this@.add_spec(rhs@),
;

pub assume_specification[ RuntimeQuaternion::sub ](
    this: &RuntimeQuaternion,
    rhs: &RuntimeQuaternion,
) -> (out: RuntimeQuaternion)
    ensures
        out@ == this@.sub_spec(rhs@),
;

pub assume_specification[ RuntimeQuaternion::neg ](this: &RuntimeQuaternion) -> (out: RuntimeQuaternion)
    ensures
        out@ == this@.neg_spec(),
;

pub assume_specification[ RuntimeQuaternion::scale ](
    this: &RuntimeQuaternion,
    k: &RuntimeScalar,
) -> (out: RuntimeQuaternion)
    ensures
        out@ == this@.scale_spec(k@),
;

pub assume_specification[ RuntimeQuaternion::mul ](
    this: &RuntimeQuaternion,
    rhs: &RuntimeQuaternion,
) -> (out: RuntimeQuaternion)
    ensures
        out@ == this@.mul_spec(rhs@),
;

pub assume_specification[ RuntimeQuaternion::conjugate ](this: &RuntimeQuaternion) -> (out: RuntimeQuaternion)
    ensures
        out@ == this@.conjugate_spec(),
;

pub assume_specification[ RuntimeQuaternion::norm2 ](this: &RuntimeQuaternion) -> (out: RuntimeScalar)
    ensures
        out@ == this@.norm2_spec(),
;

#[allow(dead_code)]
pub fn runtime_quaternion_add_pair_commutative(a: &RuntimeQuaternion, b: &RuntimeQuaternion) -> (pair: (
    RuntimeQuaternion,
    RuntimeQuaternion,
))
    ensures
        pair.0@ == a@.add_spec(b@),
        pair.1@ == b@.add_spec(a@),
        pair.0@.eqv_spec(pair.1@),
{
    let ab = a.add(b);
    let ba = b.add(a);
    proof {
        Quaternion::lemma_add_commutative(a@, b@);
        assert(a@.add_spec(b@).eqv_spec(b@.add_spec(a@)));
        assert(ab@.eqv_spec(ba@));
    }
    (ab, ba)
}

#[allow(dead_code)]
pub fn runtime_quaternion_conjugate_involution(q: &RuntimeQuaternion) -> (out: RuntimeQuaternion)
    ensures
        out@ == q@,
{
    let c = q.conjugate();
    let out = c.conjugate();
    proof {
        Quaternion::lemma_conjugate_involution(q@);
        assert(q@.conjugate_spec().conjugate_spec() == q@);
        assert(out@ == q@);
    }
    out
}

} // verus!
