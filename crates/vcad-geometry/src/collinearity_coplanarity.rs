use crate::orientation_predicates::{orient2d_sign, orient2d_value, orient3d_sign, orient3d_value};
use vcad_math::runtime_point2::RuntimePoint2;
use vcad_math::runtime_point3::RuntimePoint3;
use vcad_math::runtime_scalar::RuntimeSign;
#[cfg(verus_keep_ghost)]
use vcad_math::orientation::is_collinear;
#[cfg(verus_keep_ghost)]
use vcad_math::orientation3::is_coplanar;
#[cfg(verus_keep_ghost)]
use vcad_math::runtime_wf as wf;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::View;

#[cfg(not(verus_keep_ghost))]
pub fn collinear2d(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> bool {
    orient2d_sign(a, b, c) == 0
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn collinear2d(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> (out: bool)
    requires
        wf::point2_wf3_spec(a, b, c),
    ensures
        out == is_collinear(a@, b@, c@),
{
    let out = orient2d_sign(a, b, c) == 0;
    proof {
        vcad_math::orientation::lemma_is_collinear_iff_zero(a@, b@, c@);
    }
    out
}
}

#[cfg(not(verus_keep_ghost))]
pub fn collinear3d(a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3) -> bool {
    let ba = b.sub(a);
    let ca = c.sub(a);
    let cross = ba.cross(&ca);
    cross.norm2().sign() == RuntimeSign::Zero
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn collinear3d(a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3) -> (out: bool)
    requires
        wf::point3_wf3_spec(a, b, c),
    ensures
        out == (b@.sub_spec(a@).cross_spec(c@.sub_spec(a@)).norm2_spec().signum() == 0),
{
    let bax = b.x.sub_wf(&a.x);
    let bay = b.y.sub_wf(&a.y);
    let baz = b.z.sub_wf(&a.z);
    let cax = c.x.sub_wf(&a.x);
    let cay = c.y.sub_wf(&a.y);
    let caz = c.z.sub_wf(&a.z);

    let cx_l = bay.mul_wf(&caz);
    let cx_r = baz.mul_wf(&cay);
    let cx = cx_l.sub_wf(&cx_r);
    let cy_l = baz.mul_wf(&cax);
    let cy_r = bax.mul_wf(&caz);
    let cy = cy_l.sub_wf(&cy_r);
    let cz_l = bax.mul_wf(&cay);
    let cz_r = bay.mul_wf(&cax);
    let cz = cz_l.sub_wf(&cz_r);

    let n2x = cx.mul_wf(&cx);
    let n2y = cy.mul_wf(&cy);
    let n2z = cz.mul_wf(&cz);
    let n2xy = n2x.add_wf(&n2y);
    let n2 = n2xy.add_wf(&n2z);
    let sign = n2.sign_from_witness();
    let out = match sign {
        RuntimeSign::Zero => true,
        RuntimeSign::Negative | RuntimeSign::Positive => false,
    };
    proof {
        assert((sign is Zero) == (n2@.signum() == 0));
        assert(bax@ == b@.x.sub_spec(a@.x));
        assert(bay@ == b@.y.sub_spec(a@.y));
        assert(baz@ == b@.z.sub_spec(a@.z));
        assert(cax@ == c@.x.sub_spec(a@.x));
        assert(cay@ == c@.y.sub_spec(a@.y));
        assert(caz@ == c@.z.sub_spec(a@.z));
        assert(cx_l@ == bay@.mul_spec(caz@));
        assert(cx_r@ == baz@.mul_spec(cay@));
        assert(cx@ == cx_l@.sub_spec(cx_r@));
        assert(cy_l@ == baz@.mul_spec(cax@));
        assert(cy_r@ == bax@.mul_spec(caz@));
        assert(cy@ == cy_l@.sub_spec(cy_r@));
        assert(cz_l@ == bax@.mul_spec(cay@));
        assert(cz_r@ == bay@.mul_spec(cax@));
        assert(cz@ == cz_l@.sub_spec(cz_r@));
        assert(n2x@ == cx@.mul_spec(cx@));
        assert(n2y@ == cy@.mul_spec(cy@));
        assert(n2z@ == cz@.mul_spec(cz@));
        assert(n2xy@ == n2x@.add_spec(n2y@));
        assert(n2@ == n2xy@.add_spec(n2z@));
        assert(n2@ == b@.sub_spec(a@).cross_spec(c@.sub_spec(a@)).norm2_spec());
    }
    out
}
}

#[cfg(not(verus_keep_ghost))]
pub fn coplanar(a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3, d: &RuntimePoint3) -> bool {
    orient3d_sign(a, b, c, d) == 0
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn coplanar(a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3, d: &RuntimePoint3) -> (out: bool)
    requires
        wf::point3_wf4_spec(a, b, c, d),
    ensures
        out == is_coplanar(a@, b@, c@, d@),
{
    let out = orient3d_sign(a, b, c, d) == 0;
    proof {
        assert(is_coplanar(a@, b@, c@, d@) == (vcad_math::orientation3::orient3d_spec(a@, b@, c@, d@).signum() == 0));
    }
    out
}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collinear2d_basic() {
        let a = RuntimePoint2::from_ints(0, 0);
        let b = RuntimePoint2::from_ints(1, 1);
        let c = RuntimePoint2::from_ints(2, 2);
        assert!(collinear2d(&a, &b, &c));
    }

    #[test]
    fn coplanar_basic() {
        let a = RuntimePoint3::from_ints(0, 0, 0);
        let b = RuntimePoint3::from_ints(1, 0, 0);
        let c = RuntimePoint3::from_ints(0, 1, 0);
        let d = RuntimePoint3::from_ints(2, 3, 0);
        assert!(coplanar(&a, &b, &c, &d));
    }
}
