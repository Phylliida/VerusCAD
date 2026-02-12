use crate::point2::{dist2_spec, Point2};
use crate::runtime_point2::RuntimePoint2;
use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec2::RuntimeVec2;
use vstd::prelude::*;
use vstd::view::View;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRuntimePoint2(RuntimePoint2);

impl View for RuntimePoint2 {
    type V = Point2;

    uninterp spec fn view(&self) -> Point2;
}

pub assume_specification[ RuntimePoint2::new ](x: RuntimeScalar, y: RuntimeScalar) -> (out: RuntimePoint2)
    ensures
        out@ == (Point2 { x: x@, y: y@ }),
;

pub assume_specification[ RuntimePoint2::from_ints ](x: i64, y: i64) -> (out: RuntimePoint2)
    ensures
        out@ == Point2::from_ints_spec(x as int, y as int),
;

pub assume_specification[ RuntimePoint2::add_vec ](
    this: &RuntimePoint2,
    v: &RuntimeVec2,
) -> (out: RuntimePoint2)
    ensures
        out@ == this@.add_vec_spec(v@),
;

pub assume_specification[ RuntimePoint2::sub ](
    this: &RuntimePoint2,
    rhs: &RuntimePoint2,
) -> (out: RuntimeVec2)
    ensures
        out@ == this@.sub_spec(rhs@),
;

pub assume_specification[ RuntimePoint2::dist2 ](
    this: &RuntimePoint2,
    rhs: &RuntimePoint2,
) -> (out: RuntimeScalar)
    ensures
        out@ == dist2_spec(this@, rhs@),
;

#[allow(dead_code)]
pub fn runtime_point2_sub_then_add_cancel(p: &RuntimePoint2, q: &RuntimePoint2) -> (out: RuntimePoint2)
    ensures
        out@ == q@.add_vec_spec(p@.sub_spec(q@)),
        out@.eqv_spec(p@),
{
    let d = p.sub(q);
    let out = q.add_vec(&d);
    proof {
        Point2::lemma_sub_then_add_cancel(p@, q@);
        assert(q@.add_vec_spec(p@.sub_spec(q@)).eqv_spec(p@));
        assert(out@.eqv_spec(p@));
    }
    out
}

#[allow(dead_code)]
pub fn runtime_point2_dist2_translation_invariant(
    p: &RuntimePoint2,
    q: &RuntimePoint2,
    t: &RuntimeVec2,
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
        crate::point2::lemma_dist2_translation_invariant(p@, q@, t@);
        assert(dist2_spec(p@.add_vec_spec(t@), q@.add_vec_spec(t@)).eqv_spec(dist2_spec(p@, q@)));
        assert(lhs@.eqv_spec(rhs@));
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_point2_dist2_is_sub_norm2(p: &RuntimePoint2, q: &RuntimePoint2) -> (pair: (
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
        crate::point2::lemma_dist2_is_sub_norm2(p@, q@);
        assert(dist2_spec(p@, q@) == p@.sub_spec(q@).norm2_spec());
        assert(d@ == n@);
    }
    (d, n)
}

} // verus!
