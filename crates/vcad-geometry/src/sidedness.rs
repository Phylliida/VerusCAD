use crate::orientation_predicates::{orient3d_sign, orient3d_value};
use vcad_math::runtime_point3::RuntimePoint3;
use vcad_math::runtime_scalar::RuntimeScalar;
#[cfg(verus_keep_ghost)]
use vcad_math::orientation3::orient3d_spec;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::View;

#[cfg(not(verus_keep_ghost))]
pub fn point_above_plane(p: &RuntimePoint3, a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3) -> bool {
    orient3d_value(a, b, c, p).signum_i8() > 0
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn point_above_plane(p: &RuntimePoint3, a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3) -> (out: bool)
    ensures
        out == (orient3d_spec(a@, b@, c@, p@).signum() == 1),
{
    orient3d_sign(a, b, c, p) == 1
}
}

#[cfg(not(verus_keep_ghost))]
pub fn point_below_plane(p: &RuntimePoint3, a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3) -> bool {
    orient3d_value(a, b, c, p).signum_i8() < 0
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn point_below_plane(p: &RuntimePoint3, a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3) -> (out: bool)
    ensures
        out == (orient3d_spec(a@, b@, c@, p@).signum() == -1),
{
    orient3d_sign(a, b, c, p) == -1
}
}

#[cfg(not(verus_keep_ghost))]
pub fn point_on_plane(p: &RuntimePoint3, a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3) -> bool {
    orient3d_value(a, b, c, p).signum_i8() == 0
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn point_on_plane(p: &RuntimePoint3, a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3) -> (out: bool)
    ensures
        out == (orient3d_spec(a@, b@, c@, p@).signum() == 0),
{
    orient3d_sign(a, b, c, p) == 0
}
}

pub fn segment_crosses_plane_strict(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> bool {
    let od = orient3d_value(a, b, c, d).signum_i8();
    let oe = orient3d_value(a, b, c, e).signum_i8();
    (od > 0 && oe < 0) || (od < 0 && oe > 0)
}

pub fn segment_plane_intersection_parameter_strict(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> Option<RuntimeScalar> {
    if !segment_crosses_plane_strict(d, e, a, b, c) {
        return None;
    }
    let od = orient3d_value(a, b, c, d);
    let oe = orient3d_value(a, b, c, e);
    let denom = od.sub(&oe); // od - oe
    let inv = denom.recip()?;
    Some(od.mul(&inv))
}

pub fn segment_plane_intersection_point_strict(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> Option<RuntimePoint3> {
    let t = segment_plane_intersection_parameter_strict(d, e, a, b, c)?;
    let dir = e.sub(d);
    let step = dir.scale(&t);
    Some(d.add_vec(&step))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strict_crossing_and_t_on_simple_plane() {
        let a = RuntimePoint3::from_ints(0, 0, 0);
        let b = RuntimePoint3::from_ints(1, 0, 0);
        let c = RuntimePoint3::from_ints(0, 1, 0);
        let d = RuntimePoint3::from_ints(0, 0, 1);
        let e = RuntimePoint3::from_ints(0, 0, -1);

        assert!(segment_crosses_plane_strict(&d, &e, &a, &b, &c));
        let t = segment_plane_intersection_parameter_strict(&d, &e, &a, &b, &c).unwrap();
        assert_eq!(t.signum_i8(), 1);

        let p = segment_plane_intersection_point_strict(&d, &e, &a, &b, &c).unwrap();
        assert_eq!(point_on_plane(&p, &a, &b, &c), true);
    }

    #[test]
    fn no_crossing_when_same_side() {
        let a = RuntimePoint3::from_ints(0, 0, 0);
        let b = RuntimePoint3::from_ints(1, 0, 0);
        let c = RuntimePoint3::from_ints(0, 1, 0);
        let d = RuntimePoint3::from_ints(0, 0, 1);
        let e = RuntimePoint3::from_ints(0, 0, 2);

        assert!(!segment_crosses_plane_strict(&d, &e, &a, &b, &c));
        assert!(segment_plane_intersection_parameter_strict(&d, &e, &a, &b, &c).is_none());
    }
}
