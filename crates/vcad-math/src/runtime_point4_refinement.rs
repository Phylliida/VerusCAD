use crate::point4::{dist2_spec, Point4};
use crate::runtime_point4::RuntimePoint4;
use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec4::RuntimeVec4;
use vstd::prelude::*;
use vstd::view::View;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRuntimePoint4(RuntimePoint4);

impl View for RuntimePoint4 {
    type V = Point4;

    uninterp spec fn view(&self) -> Point4;
}

pub assume_specification[ RuntimePoint4::new ](
    x: RuntimeScalar,
    y: RuntimeScalar,
    z: RuntimeScalar,
    w: RuntimeScalar,
) -> (out: RuntimePoint4)
    ensures
        out@ == (Point4 { x: x@, y: y@, z: z@, w: w@ }),
;

pub assume_specification[ RuntimePoint4::from_ints ](x: i64, y: i64, z: i64, w: i64) -> (out: RuntimePoint4)
    ensures
        out@ == Point4::from_ints_spec(x as int, y as int, z as int, w as int),
;

pub assume_specification[ RuntimePoint4::add_vec ](
    this: &RuntimePoint4,
    v: &RuntimeVec4,
) -> (out: RuntimePoint4)
    ensures
        out@ == this@.add_vec_spec(v@),
;

pub assume_specification[ RuntimePoint4::sub ](
    this: &RuntimePoint4,
    rhs: &RuntimePoint4,
) -> (out: RuntimeVec4)
    ensures
        out@ == this@.sub_spec(rhs@),
;

pub assume_specification[ RuntimePoint4::dist2 ](
    this: &RuntimePoint4,
    rhs: &RuntimePoint4,
) -> (out: RuntimeScalar)
    ensures
        out@ == dist2_spec(this@, rhs@),
;

#[allow(dead_code)]
pub fn runtime_point4_dist2_is_sub_norm2(p: &RuntimePoint4, q: &RuntimePoint4) -> (pair: (
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
        crate::point4::lemma_dist2_is_sub_norm2(p@, q@);
        assert(dist2_spec(p@, q@) == p@.sub_spec(q@).norm2_spec());
        assert(d@ == n@);
    }
    (d, n)
}

} // verus!
