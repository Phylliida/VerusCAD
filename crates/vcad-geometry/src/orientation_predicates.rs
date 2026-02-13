use vcad_math::runtime_orientation::{self, RuntimeOrientation};
use vcad_math::runtime_orientation3::{self, RuntimeOrientation3};
use vcad_math::runtime_point2::RuntimePoint2;
use vcad_math::runtime_point3::RuntimePoint3;
use vcad_math::runtime_scalar::RuntimeScalar;
#[cfg(verus_keep_ghost)]
use vcad_math::orientation::{orient2d_spec, orientation_spec};
#[cfg(verus_keep_ghost)]
use vcad_math::orientation3::{orient3d_spec, orientation3_spec};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::View;

#[cfg(not(verus_keep_ghost))]
pub fn orient2d_value(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> RuntimeScalar {
    runtime_orientation::orient2d(a, b, c)
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn orient2d_value(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> (out: RuntimeScalar)
    ensures
        out@ == orient2d_spec(a@, b@, c@),
{
    runtime_orientation::orient2d(a, b, c)
}
}

#[cfg(not(verus_keep_ghost))]
pub fn orient3d_value(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
) -> RuntimeScalar {
    runtime_orientation3::orient3d(a, b, c, d)
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn orient3d_value(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
) -> (out: RuntimeScalar)
    ensures
        out@ == orient3d_spec(a@, b@, c@, d@),
{
    runtime_orientation3::orient3d(a, b, c, d)
}
}

#[cfg(not(verus_keep_ghost))]
pub fn orient2d_sign(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> i8 {
    orient2d_value(a, b, c).signum_i8()
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn orient2d_sign(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> (out: i8)
    ensures
        (out == 1) == (orient2d_spec(a@, b@, c@).signum() == 1),
        (out == -1) == (orient2d_spec(a@, b@, c@).signum() == -1),
        (out == 0) == (orient2d_spec(a@, b@, c@).signum() == 0),
{
    orient2d_value(a, b, c).signum_i8()
}
}

#[cfg(not(verus_keep_ghost))]
pub fn orient3d_sign(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
) -> i8 {
    orient3d_value(a, b, c, d).signum_i8()
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn orient3d_sign(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
) -> (out: i8)
    ensures
        (out == 1) == (orient3d_spec(a@, b@, c@, d@).signum() == 1),
        (out == -1) == (orient3d_spec(a@, b@, c@, d@).signum() == -1),
        (out == 0) == (orient3d_spec(a@, b@, c@, d@).signum() == 0),
{
    orient3d_value(a, b, c, d).signum_i8()
}
}

#[cfg(not(verus_keep_ghost))]
pub fn orient2d_class(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> RuntimeOrientation {
    runtime_orientation::orientation(a, b, c)
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn orient2d_class(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> (out: RuntimeOrientation)
    ensures
        out@ == orientation_spec(a@, b@, c@),
{
    runtime_orientation::orientation(a, b, c)
}
}

#[cfg(not(verus_keep_ghost))]
pub fn orient3d_class(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
) -> RuntimeOrientation3 {
    runtime_orientation3::orientation3(a, b, c, d)
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn orient3d_class(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
) -> (out: RuntimeOrientation3)
    ensures
        out@ == orientation3_spec(a@, b@, c@, d@),
{
    runtime_orientation3::orientation3(a, b, c, d)
}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn orient2d_sign_basic_ccw() {
        let a = RuntimePoint2::from_ints(0, 0);
        let b = RuntimePoint2::from_ints(1, 0);
        let c = RuntimePoint2::from_ints(0, 1);
        assert_eq!(orient2d_sign(&a, &b, &c), 1);
    }

    #[test]
    fn orient3d_sign_basic_positive() {
        let a = RuntimePoint3::from_ints(0, 0, 0);
        let b = RuntimePoint3::from_ints(1, 0, 0);
        let c = RuntimePoint3::from_ints(0, 1, 0);
        let d = RuntimePoint3::from_ints(0, 0, 1);
        assert_eq!(orient3d_sign(&a, &b, &c, &d), 1);
    }
}
