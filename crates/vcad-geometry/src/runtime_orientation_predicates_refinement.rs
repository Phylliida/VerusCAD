#![cfg(feature = "verus-proofs")]

use crate::orientation_predicates;
use vcad_math::orientation::{orient2d_spec, orientation_spec, signed_area2_poly_spec, Orientation};
use vcad_math::orientation3::{orient3d_spec, orientation3_spec, signed_volume3_poly_spec, Orientation3};
use vcad_math::runtime_orientation::RuntimeOrientation;
use vcad_math::runtime_orientation3::RuntimeOrientation3;
use vcad_math::runtime_point2::RuntimePoint2;
use vcad_math::runtime_point3::RuntimePoint3;
use vcad_math::runtime_scalar::RuntimeScalar;
use vstd::prelude::*;
use vstd::view::View;

verus! {

#[allow(dead_code)]
pub fn runtime_orient2d_value_matches_signed_area2_poly(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
) -> (out: RuntimeScalar)
    ensures
        out@ == orient2d_spec(a@, b@, c@),
        out@ == signed_area2_poly_spec(a@, b@, c@),
{
    let out = orientation_predicates::orient2d_value(a, b, c);
    proof {
        vcad_math::orientation::lemma_signed_area2_poly_matches_orient2d(a@, b@, c@);
        assert(signed_area2_poly_spec(a@, b@, c@) == orient2d_spec(a@, b@, c@));
        assert(out@ == signed_area2_poly_spec(a@, b@, c@));
    }
    out
}

#[allow(dead_code)]
pub fn runtime_orient3d_value_matches_signed_volume3_poly(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
) -> (out: RuntimeScalar)
    ensures
        out@ == orient3d_spec(a@, b@, c@, d@),
        out@ == signed_volume3_poly_spec(a@, b@, c@, d@),
{
    let out = orientation_predicates::orient3d_value(a, b, c, d);
    proof {
        vcad_math::orientation3::lemma_signed_volume3_poly_matches_orient3d(a@, b@, c@, d@);
        assert(signed_volume3_poly_spec(a@, b@, c@, d@) == orient3d_spec(a@, b@, c@, d@));
        assert(out@ == signed_volume3_poly_spec(a@, b@, c@, d@));
    }
    out
}

#[allow(dead_code)]
pub fn runtime_orient2d_class_matches_sign(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
) -> (pair: (RuntimeOrientation, RuntimeScalar))
    requires
        a.witness_wf_spec(),
        b.witness_wf_spec(),
        c.witness_wf_spec(),
    ensures
        pair.0@ == orientation_spec(a@, b@, c@),
        pair.1@ == orient2d_spec(a@, b@, c@),
        (pair.0@ is Ccw) == (pair.1@.signum() == 1),
        (pair.0@ is Cw) == (pair.1@.signum() == -1),
        (pair.0@ is Collinear) == (pair.1@.signum() == 0),
{
    let class = orientation_predicates::orient2d_class(a, b, c);
    let value = orientation_predicates::orient2d_value(a, b, c);
    proof {
        vcad_math::orientation::lemma_orientation_spec_matches_predicates(a@, b@, c@);
        vcad_math::orientation::lemma_is_ccw_iff_positive(a@, b@, c@);
        vcad_math::orientation::lemma_is_cw_iff_negative(a@, b@, c@);
        vcad_math::orientation::lemma_is_collinear_iff_zero(a@, b@, c@);
        assert((orientation_spec(a@, b@, c@) is Ccw) == (orient2d_spec(a@, b@, c@).signum() == 1));
        assert((orientation_spec(a@, b@, c@) is Cw) == (orient2d_spec(a@, b@, c@).signum() == -1));
        assert((orientation_spec(a@, b@, c@) is Collinear) == (orient2d_spec(a@, b@, c@).signum() == 0));
        assert((class@ is Ccw) == (value@.signum() == 1));
        assert((class@ is Cw) == (value@.signum() == -1));
        assert((class@ is Collinear) == (value@.signum() == 0));
    }
    (class, value)
}

#[allow(dead_code)]
pub fn runtime_orient3d_class_matches_sign(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
) -> (pair: (RuntimeOrientation3, RuntimeScalar))
    requires
        a.witness_wf_spec(),
        b.witness_wf_spec(),
        c.witness_wf_spec(),
        d.witness_wf_spec(),
    ensures
        pair.0@ == orientation3_spec(a@, b@, c@, d@),
        pair.1@ == orient3d_spec(a@, b@, c@, d@),
        (pair.0@ is Positive) == (pair.1@.signum() == 1),
        (pair.0@ is Negative) == (pair.1@.signum() == -1),
        (pair.0@ is Coplanar) == (pair.1@.signum() == 0),
{
    let class = orientation_predicates::orient3d_class(a, b, c, d);
    let value = orientation_predicates::orient3d_value(a, b, c, d);
    proof {
        vcad_math::orientation3::lemma_orientation3_spec_matches_predicates(a@, b@, c@, d@);
        assert((orientation3_spec(a@, b@, c@, d@) is Positive) == (orient3d_spec(a@, b@, c@, d@).signum() == 1));
        assert((orientation3_spec(a@, b@, c@, d@) is Negative) == (orient3d_spec(a@, b@, c@, d@).signum() == -1));
        assert((orientation3_spec(a@, b@, c@, d@) is Coplanar) == (orient3d_spec(a@, b@, c@, d@).signum() == 0));
        assert((class@ is Positive) == (value@.signum() == 1));
        assert((class@ is Negative) == (value@.signum() == -1));
        assert((class@ is Coplanar) == (value@.signum() == 0));
    }
    (class, value)
}

} // verus!
