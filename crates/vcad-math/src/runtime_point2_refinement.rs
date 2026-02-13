use crate::point2::{dist2_spec, Point2};
use crate::runtime_point2::RuntimePoint2;
use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec2::RuntimeVec2;
use vstd::prelude::*;
use vstd::view::View;

verus! {

#[verifier::external_type_specification]
pub struct ExRuntimePoint2(RuntimePoint2);

impl View for RuntimePoint2 {
    type V = Point2;

    open spec fn view(&self) -> Point2 {
        Point2 { x: self.x@, y: self.y@ }
    }
}

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
