use crate::orientation_predicates::{orient2d_sign, orient2d_value, orient3d_sign, orient3d_value};
use vcad_math::runtime_point2::RuntimePoint2;
use vcad_math::runtime_point3::RuntimePoint3;
use vcad_math::runtime_scalar::RuntimeSign;
#[cfg(verus_keep_ghost)]
use vcad_math::orientation::is_collinear;
#[cfg(verus_keep_ghost)]
use vcad_math::orientation3::is_coplanar;
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
    ensures
        out == (b@.sub_spec(a@).cross_spec(c@.sub_spec(a@)).norm2_spec().signum() == 0),
{
    let ba = b.sub(a);
    let ca = c.sub(a);
    let cross = ba.cross(&ca);
    let n2 = cross.norm2();
    let sign = n2.sign();
    let out = match sign {
        RuntimeSign::Zero => true,
        RuntimeSign::Negative | RuntimeSign::Positive => false,
    };
    proof {
        assert((sign is Zero) == (n2@.signum() == 0));
        assert(ba@ == b@.sub_spec(a@));
        assert(ca@ == c@.sub_spec(a@));
        assert(cross@ == ba@.cross_spec(ca@));
        assert(n2@ == cross@.norm2_spec());
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
