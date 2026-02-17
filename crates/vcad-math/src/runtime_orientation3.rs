use crate::runtime_point3::RuntimePoint3;
use crate::runtime_scalar::{RuntimeScalar, RuntimeSign};
#[cfg(verus_keep_ghost)]
use crate::orientation3::{orient3d_spec, orientation3_spec, Orientation3};
#[cfg(verus_keep_ghost)]
use crate::point3::Point3;
#[cfg(verus_keep_ghost)]
use crate::scalar::Scalar;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::View;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuntimeOrientation3 {
    Negative,
    Coplanar,
    Positive,
}

#[cfg(not(verus_keep_ghost))]
pub fn orient3d(a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3, d: &RuntimePoint3) -> RuntimeScalar {
    let ba = b.sub(a);
    let ca = c.sub(a);
    let da = d.sub(a);
    let cad = ca.cross(&da);
    ba.dot(&cad)
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn orient3d(a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3, d: &RuntimePoint3) -> (out: RuntimeScalar)
    ensures
        out@ == orient3d_spec(a@, b@, c@, d@),
{
    let ba = b.sub(a);
    let ca = c.sub(a);
    let da = d.sub(a);
    let cad = ca.cross(&da);
    let out = ba.dot(&cad);
    proof {
        assert(ba@ == b@.sub_spec(a@));
        assert(ca@ == c@.sub_spec(a@));
        assert(da@ == d@.sub_spec(a@));
        assert(cad@ == ca@.cross_spec(da@));
        assert(out@ == ba@.dot_spec(cad@));
        assert(out@ == orient3d_spec(a@, b@, c@, d@));
    }
    out
}
}

#[cfg(not(verus_keep_ghost))]
pub fn scale_point_from_origin3(p: &RuntimePoint3, k: &RuntimeScalar) -> RuntimePoint3 {
    RuntimePoint3::new(p.x().mul(k), p.y().mul(k), p.z().mul(k))
}

#[cfg(verus_keep_ghost)]
verus! {
fn orient3d_wf(a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3, d: &RuntimePoint3) -> (out: RuntimeScalar)
    requires
        a.witness_wf_spec(),
        b.witness_wf_spec(),
        c.witness_wf_spec(),
        d.witness_wf_spec(),
    ensures
        out@ == orient3d_spec(a@, b@, c@, d@),
        out.witness_wf_spec(),
{
    let bax = b.x.sub_wf(&a.x);
    let bay = b.y.sub_wf(&a.y);
    let baz = b.z.sub_wf(&a.z);
    let cax = c.x.sub_wf(&a.x);
    let cay = c.y.sub_wf(&a.y);
    let caz = c.z.sub_wf(&a.z);
    let dax = d.x.sub_wf(&a.x);
    let day = d.y.sub_wf(&a.y);
    let daz = d.z.sub_wf(&a.z);

    let cad_x_l = cay.mul_wf(&daz);
    let cad_x_r = caz.mul_wf(&day);
    let cad_x = cad_x_l.sub_wf(&cad_x_r);
    let cad_y_l = caz.mul_wf(&dax);
    let cad_y_r = cax.mul_wf(&daz);
    let cad_y = cad_y_l.sub_wf(&cad_y_r);
    let cad_z_l = cax.mul_wf(&day);
    let cad_z_r = cay.mul_wf(&dax);
    let cad_z = cad_z_l.sub_wf(&cad_z_r);

    let term_x = bax.mul_wf(&cad_x);
    let term_y = bay.mul_wf(&cad_y);
    let term_z = baz.mul_wf(&cad_z);
    let sum_xy = term_x.add_wf(&term_y);
    let out = sum_xy.add_wf(&term_z);

    proof {
        assert(bax@ == b@.x.sub_spec(a@.x));
        assert(bay@ == b@.y.sub_spec(a@.y));
        assert(baz@ == b@.z.sub_spec(a@.z));
        assert(cax@ == c@.x.sub_spec(a@.x));
        assert(cay@ == c@.y.sub_spec(a@.y));
        assert(caz@ == c@.z.sub_spec(a@.z));
        assert(dax@ == d@.x.sub_spec(a@.x));
        assert(day@ == d@.y.sub_spec(a@.y));
        assert(daz@ == d@.z.sub_spec(a@.z));

        assert(cad_x_l@ == cay@.mul_spec(daz@));
        assert(cad_x_r@ == caz@.mul_spec(day@));
        assert(cad_x@ == cad_x_l@.sub_spec(cad_x_r@));
        assert(cad_y_l@ == caz@.mul_spec(dax@));
        assert(cad_y_r@ == cax@.mul_spec(daz@));
        assert(cad_y@ == cad_y_l@.sub_spec(cad_y_r@));
        assert(cad_z_l@ == cax@.mul_spec(day@));
        assert(cad_z_r@ == cay@.mul_spec(dax@));
        assert(cad_z@ == cad_z_l@.sub_spec(cad_z_r@));

        assert(term_x@ == bax@.mul_spec(cad_x@));
        assert(term_y@ == bay@.mul_spec(cad_y@));
        assert(term_z@ == baz@.mul_spec(cad_z@));
        assert(sum_xy@ == term_x@.add_spec(term_y@));
        assert(out@ == sum_xy@.add_spec(term_z@));
        assert(out@ == orient3d_spec(a@, b@, c@, d@));
    }
    out
}

pub fn scale_point_from_origin3(p: &RuntimePoint3, k: &RuntimeScalar) -> (out: RuntimePoint3)
    ensures
        out@ == crate::orientation3::scale_point_from_origin3_spec(p@, k@),
{
    let origin = RuntimePoint3::from_ints(0, 0, 0);
    let v = p.sub(&origin);
    let vs = v.scale(k);
    let out = origin.add_vec(&vs);
    proof {
        let z = Scalar::from_int_spec(0);

        assert(origin@ == Point3::from_ints_spec(0, 0, 0));
        assert(origin@.x == z);
        assert(origin@.y == z);
        assert(origin@.z == z);

        assert(v@ == p@.sub_spec(origin@));
        assert(v@.x == p@.x.sub_spec(z));
        assert(v@.y == p@.y.sub_spec(z));
        assert(v@.z == p@.z.sub_spec(z));

        assert(vs@ == v@.scale_spec(k@));
        assert(vs@.x == v@.x.mul_spec(k@));
        assert(vs@.y == v@.y.mul_spec(k@));
        assert(vs@.z == v@.z.mul_spec(k@));

        Scalar::lemma_add_zero_identity(p@.x);
        Scalar::lemma_add_zero_identity(p@.y);
        Scalar::lemma_add_zero_identity(p@.z);
        assert(z.num == 0);
        assert(z.neg_spec().num == -z.num);
        assert(z.neg_spec().num == 0);
        assert(z.neg_spec().den == z.den);
        assert(z.neg_spec() == z);
        assert(p@.x.sub_spec(z) == p@.x.add_spec(z.neg_spec()));
        assert(p@.y.sub_spec(z) == p@.y.add_spec(z.neg_spec()));
        assert(p@.z.sub_spec(z) == p@.z.add_spec(z.neg_spec()));
        assert(p@.x.sub_spec(z) == p@.x);
        assert(p@.y.sub_spec(z) == p@.y);
        assert(p@.z.sub_spec(z) == p@.z);

        assert(vs@.x == p@.x.mul_spec(k@));
        assert(vs@.y == p@.y.mul_spec(k@));
        assert(vs@.z == p@.z.mul_spec(k@));

        assert(out@ == origin@.add_vec_spec(vs@));
        assert(out@.x == z.add_spec(vs@.x));
        assert(out@.y == z.add_spec(vs@.y));
        assert(out@.z == z.add_spec(vs@.z));
        Scalar::lemma_add_zero_identity(vs@.x);
        Scalar::lemma_add_zero_identity(vs@.y);
        Scalar::lemma_add_zero_identity(vs@.z);
        assert(out@.x == vs@.x);
        assert(out@.y == vs@.y);
        assert(out@.z == vs@.z);
        assert(out@ == Point3 { x: p@.x.mul_spec(k@), y: p@.y.mul_spec(k@), z: p@.z.mul_spec(k@) });
        assert(out@ == crate::orientation3::scale_point_from_origin3_spec(p@, k@));
    }
    out
}
}

#[cfg(not(verus_keep_ghost))]
pub fn orientation3(a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3, d: &RuntimePoint3) -> RuntimeOrientation3 {
    match orient3d(a, b, c, d).sign() {
        RuntimeSign::Positive => RuntimeOrientation3::Positive,
        RuntimeSign::Negative => RuntimeOrientation3::Negative,
        RuntimeSign::Zero => RuntimeOrientation3::Coplanar,
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn orientation3(a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3, d: &RuntimePoint3) -> (out: RuntimeOrientation3)
    requires
        a.witness_wf_spec(),
        b.witness_wf_spec(),
        c.witness_wf_spec(),
        d.witness_wf_spec(),
    ensures
        out@ == orientation3_spec(a@, b@, c@, d@),
{
    let det = orient3d_wf(a, b, c, d);
    let sign = det.sign_from_witness();
    match sign {
        RuntimeSign::Positive => {
            proof {
                assert((sign is Positive) == (det@.signum() == 1));
                assert(det@.signum() == 1);
                assert(orientation3_spec(a@, b@, c@, d@) == Orientation3::Positive);
            }
            RuntimeOrientation3::Positive
        }
        RuntimeSign::Negative => {
            proof {
                assert((sign is Negative) == (det@.signum() == -1));
                assert(det@.signum() == -1);
                assert(orientation3_spec(a@, b@, c@, d@) == Orientation3::Negative);
            }
            RuntimeOrientation3::Negative
        }
        RuntimeSign::Zero => {
            proof {
                assert((sign is Positive) == (det@.signum() == 1));
                assert((sign is Negative) == (det@.signum() == -1));
                assert(!(sign is Positive));
                assert(!(sign is Negative));
                assert(det@.signum() != 1);
                assert(det@.signum() != -1);
                assert(orientation3_spec(a@, b@, c@, d@) == Orientation3::Coplanar);
            }
            RuntimeOrientation3::Coplanar
        }
    }
}
}
