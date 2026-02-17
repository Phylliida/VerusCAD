use crate::runtime_point2::RuntimePoint2;
use crate::runtime_scalar::{RuntimeScalar, RuntimeSign};
#[cfg(verus_keep_ghost)]
use crate::orientation::{orient2d_spec, orientation_spec, Orientation};
#[cfg(verus_keep_ghost)]
use crate::point2::Point2;
#[cfg(verus_keep_ghost)]
use crate::scalar::Scalar;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::View;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuntimeOrientation {
    Cw,
    Collinear,
    Ccw,
}

#[cfg(not(verus_keep_ghost))]
pub fn orient2d(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> RuntimeScalar {
    let ba = b.sub(a);
    let ca = c.sub(a);
    ba.cross(&ca)
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn orient2d(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> (out: RuntimeScalar)
    ensures
        out@ == orient2d_spec(a@, b@, c@),
{
    let ba = b.sub(a);
    let ca = c.sub(a);
    let out = ba.cross(&ca);
    proof {
        assert(ba@ == b@.sub_spec(a@));
        assert(ca@ == c@.sub_spec(a@));
        assert(out@ == ba@.cross_spec(ca@));
        assert(out@ == orient2d_spec(a@, b@, c@));
    }
    out
}
}

#[cfg(not(verus_keep_ghost))]
pub fn scale_point_from_origin(p: &RuntimePoint2, k: &RuntimeScalar) -> RuntimePoint2 {
    RuntimePoint2::new(p.x().mul(k), p.y().mul(k))
}

#[cfg(verus_keep_ghost)]
verus! {
fn orient2d_wf(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> (out: RuntimeScalar)
    requires
        a.witness_wf_spec(),
        b.witness_wf_spec(),
        c.witness_wf_spec(),
    ensures
        out@ == orient2d_spec(a@, b@, c@),
        out.witness_wf_spec(),
{
    let bax = b.x.sub_wf(&a.x);
    let bay = b.y.sub_wf(&a.y);
    let cax = c.x.sub_wf(&a.x);
    let cay = c.y.sub_wf(&a.y);
    let left = bax.mul_wf(&cay);
    let right = bay.mul_wf(&cax);
    let out = left.sub_wf(&right);
    proof {
        assert(bax@ == b@.x.sub_spec(a@.x));
        assert(bay@ == b@.y.sub_spec(a@.y));
        assert(cax@ == c@.x.sub_spec(a@.x));
        assert(cay@ == c@.y.sub_spec(a@.y));
        assert(left@ == bax@.mul_spec(cay@));
        assert(right@ == bay@.mul_spec(cax@));
        assert(out@ == left@.sub_spec(right@));
        assert(out@ == orient2d_spec(a@, b@, c@));
    }
    out
}

pub fn scale_point_from_origin(p: &RuntimePoint2, k: &RuntimeScalar) -> (out: RuntimePoint2)
    ensures
        out@ == crate::orientation::scale_point_from_origin_spec(p@, k@),
{
    let origin = RuntimePoint2::from_ints(0, 0);
    let v = p.sub(&origin);
    let vs = v.scale(k);
    let out = origin.add_vec(&vs);
    proof {
        let z = Scalar::from_int_spec(0);

        assert(origin@ == Point2::from_ints_spec(0, 0));
        assert(origin@.x == z);
        assert(origin@.y == z);

        assert(v@ == p@.sub_spec(origin@));
        assert(v@.x == p@.x.sub_spec(z));
        assert(v@.y == p@.y.sub_spec(z));

        assert(vs@ == v@.scale_spec(k@));
        assert(vs@.x == v@.x.mul_spec(k@));
        assert(vs@.y == v@.y.mul_spec(k@));

        Scalar::lemma_add_zero_identity(p@.x);
        Scalar::lemma_add_zero_identity(p@.y);
        assert(z.num == 0);
        assert(z.neg_spec().num == -z.num);
        assert(z.neg_spec().num == 0);
        assert(z.neg_spec().den == z.den);
        assert(z.neg_spec() == z);
        assert(p@.x.sub_spec(z) == p@.x.add_spec(z.neg_spec()));
        assert(p@.y.sub_spec(z) == p@.y.add_spec(z.neg_spec()));
        assert(p@.x.sub_spec(z) == p@.x);
        assert(p@.y.sub_spec(z) == p@.y);

        assert(vs@.x == p@.x.mul_spec(k@));
        assert(vs@.y == p@.y.mul_spec(k@));

        assert(out@ == origin@.add_vec_spec(vs@));
        assert(out@.x == z.add_spec(vs@.x));
        assert(out@.y == z.add_spec(vs@.y));
        Scalar::lemma_add_zero_identity(vs@.x);
        Scalar::lemma_add_zero_identity(vs@.y);
        assert(out@.x == vs@.x);
        assert(out@.y == vs@.y);
        assert(out@ == Point2 { x: p@.x.mul_spec(k@), y: p@.y.mul_spec(k@) });
        assert(out@ == crate::orientation::scale_point_from_origin_spec(p@, k@));
    }
    out
}

pub fn scale_point_from_origin_wf(p: &RuntimePoint2, k: &RuntimeScalar) -> (out: RuntimePoint2)
    requires
        p.witness_wf_spec(),
        k.witness_wf_spec(),
    ensures
        out@ == crate::orientation::scale_point_from_origin_spec(p@, k@),
        out.witness_wf_spec(),
{
    let x = p.x.mul_wf(k);
    let y = p.y.mul_wf(k);
    let out = RuntimePoint2 { x, y };
    proof {
        assert(out@ == Point2 { x: p@.x.mul_spec(k@), y: p@.y.mul_spec(k@) });
        assert(out@ == crate::orientation::scale_point_from_origin_spec(p@, k@));
        assert(out.witness_wf_spec());
    }
    out
}
}

#[cfg(not(verus_keep_ghost))]
pub fn orientation(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> RuntimeOrientation {
    match orient2d(a, b, c).sign() {
        RuntimeSign::Positive => RuntimeOrientation::Ccw,
        RuntimeSign::Negative => RuntimeOrientation::Cw,
        RuntimeSign::Zero => RuntimeOrientation::Collinear,
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn orientation(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> (out: RuntimeOrientation)
    requires
        a.witness_wf_spec(),
        b.witness_wf_spec(),
        c.witness_wf_spec(),
    ensures
        out@ == orientation_spec(a@, b@, c@),
{
    let det = orient2d_wf(a, b, c);
    let sign = det.sign_from_witness();
    match sign {
        RuntimeSign::Positive => {
            proof {
                assert((sign is Positive) == (det@.signum() == 1));
                assert(det@.signum() == 1);
                assert(orientation_spec(a@, b@, c@) == Orientation::Ccw);
            }
            RuntimeOrientation::Ccw
        }
        RuntimeSign::Negative => {
            proof {
                assert((sign is Negative) == (det@.signum() == -1));
                assert(det@.signum() == -1);
                assert(orientation_spec(a@, b@, c@) == Orientation::Cw);
            }
            RuntimeOrientation::Cw
        }
        RuntimeSign::Zero => {
            proof {
                assert((sign is Positive) == (det@.signum() == 1));
                assert((sign is Negative) == (det@.signum() == -1));
                assert(!(sign is Positive));
                assert(!(sign is Negative));
                assert(det@.signum() != 1);
                assert(det@.signum() != -1);
                assert(orientation_spec(a@, b@, c@) == Orientation::Collinear);
            }
            RuntimeOrientation::Collinear
        }
    }
}
}
