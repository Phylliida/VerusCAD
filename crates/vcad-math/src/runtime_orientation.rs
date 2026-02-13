use crate::runtime_point2::RuntimePoint2;
use crate::runtime_scalar::RuntimeScalar;
#[cfg(verus_keep_ghost)]
use crate::orientation::orient2d_spec;
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

pub fn scale_point_from_origin(p: &RuntimePoint2, k: &RuntimeScalar) -> RuntimePoint2 {
    RuntimePoint2::new(p.x().mul(k), p.y().mul(k))
}

pub fn orientation(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> RuntimeOrientation {
    match orient2d(a, b, c).signum_i8() {
        1 => RuntimeOrientation::Ccw,
        -1 => RuntimeOrientation::Cw,
        _ => RuntimeOrientation::Collinear,
    }
}
