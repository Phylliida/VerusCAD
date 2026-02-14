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
    match runtime_orientation::orientation(a, b, c) {
        RuntimeOrientation::Ccw => 1,
        RuntimeOrientation::Cw => -1,
        RuntimeOrientation::Collinear => 0,
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn orient2d_sign(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> (out: i8)
    ensures
        (out == 1) == (orient2d_spec(a@, b@, c@).signum() == 1),
        (out == -1) == (orient2d_spec(a@, b@, c@).signum() == -1),
        (out == 0) == (orient2d_spec(a@, b@, c@).signum() == 0),
{
    let cls = runtime_orientation::orientation(a, b, c);
    match cls {
        ccls @ RuntimeOrientation::Ccw => {
            proof {
                vcad_math::orientation::lemma_orientation_spec_matches_predicates(a@, b@, c@);
                assert(ccls@ == orientation_spec(a@, b@, c@));
                assert(orientation_spec(a@, b@, c@) is Ccw);
                assert((orientation_spec(a@, b@, c@) is Ccw) == (orient2d_spec(a@, b@, c@).signum() == 1));
                assert((orientation_spec(a@, b@, c@) is Cw) == (orient2d_spec(a@, b@, c@).signum() == -1));
                assert((orientation_spec(a@, b@, c@) is Collinear) == (orient2d_spec(a@, b@, c@).signum() == 0));
            }
            1
        }
        ccls @ RuntimeOrientation::Cw => {
            proof {
                vcad_math::orientation::lemma_orientation_spec_matches_predicates(a@, b@, c@);
                assert(ccls@ == orientation_spec(a@, b@, c@));
                assert(orientation_spec(a@, b@, c@) is Cw);
                assert((orientation_spec(a@, b@, c@) is Ccw) == (orient2d_spec(a@, b@, c@).signum() == 1));
                assert((orientation_spec(a@, b@, c@) is Cw) == (orient2d_spec(a@, b@, c@).signum() == -1));
                assert((orientation_spec(a@, b@, c@) is Collinear) == (orient2d_spec(a@, b@, c@).signum() == 0));
            }
            -1
        }
        ccls @ RuntimeOrientation::Collinear => {
            proof {
                vcad_math::orientation::lemma_orientation_spec_matches_predicates(a@, b@, c@);
                assert(ccls@ == orientation_spec(a@, b@, c@));
                assert(orientation_spec(a@, b@, c@) is Collinear);
                assert((orientation_spec(a@, b@, c@) is Ccw) == (orient2d_spec(a@, b@, c@).signum() == 1));
                assert((orientation_spec(a@, b@, c@) is Cw) == (orient2d_spec(a@, b@, c@).signum() == -1));
                assert((orientation_spec(a@, b@, c@) is Collinear) == (orient2d_spec(a@, b@, c@).signum() == 0));
            }
            0
        }
    }
}
}

#[cfg(not(verus_keep_ghost))]
pub fn orient3d_sign(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
) -> i8 {
    match runtime_orientation3::orientation3(a, b, c, d) {
        RuntimeOrientation3::Positive => 1,
        RuntimeOrientation3::Negative => -1,
        RuntimeOrientation3::Coplanar => 0,
    }
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
    let cls = runtime_orientation3::orientation3(a, b, c, d);
    match cls {
        ccls @ RuntimeOrientation3::Positive => {
            proof {
                vcad_math::orientation3::lemma_orientation3_spec_matches_predicates(a@, b@, c@, d@);
                assert(ccls@ == orientation3_spec(a@, b@, c@, d@));
                assert(orientation3_spec(a@, b@, c@, d@) is Positive);
                assert((orientation3_spec(a@, b@, c@, d@) is Positive) == (orient3d_spec(a@, b@, c@, d@).signum() == 1));
                assert((orientation3_spec(a@, b@, c@, d@) is Negative) == (orient3d_spec(a@, b@, c@, d@).signum() == -1));
                assert((orientation3_spec(a@, b@, c@, d@) is Coplanar) == (orient3d_spec(a@, b@, c@, d@).signum() == 0));
            }
            1
        }
        ccls @ RuntimeOrientation3::Negative => {
            proof {
                vcad_math::orientation3::lemma_orientation3_spec_matches_predicates(a@, b@, c@, d@);
                assert(ccls@ == orientation3_spec(a@, b@, c@, d@));
                assert(orientation3_spec(a@, b@, c@, d@) is Negative);
                assert((orientation3_spec(a@, b@, c@, d@) is Positive) == (orient3d_spec(a@, b@, c@, d@).signum() == 1));
                assert((orientation3_spec(a@, b@, c@, d@) is Negative) == (orient3d_spec(a@, b@, c@, d@).signum() == -1));
                assert((orientation3_spec(a@, b@, c@, d@) is Coplanar) == (orient3d_spec(a@, b@, c@, d@).signum() == 0));
            }
            -1
        }
        ccls @ RuntimeOrientation3::Coplanar => {
            proof {
                vcad_math::orientation3::lemma_orientation3_spec_matches_predicates(a@, b@, c@, d@);
                assert(ccls@ == orientation3_spec(a@, b@, c@, d@));
                assert(orientation3_spec(a@, b@, c@, d@) is Coplanar);
                assert((orientation3_spec(a@, b@, c@, d@) is Positive) == (orient3d_spec(a@, b@, c@, d@).signum() == 1));
                assert((orientation3_spec(a@, b@, c@, d@) is Negative) == (orient3d_spec(a@, b@, c@, d@).signum() == -1));
                assert((orientation3_spec(a@, b@, c@, d@) is Coplanar) == (orient3d_spec(a@, b@, c@, d@).signum() == 0));
            }
            0
        }
    }
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
