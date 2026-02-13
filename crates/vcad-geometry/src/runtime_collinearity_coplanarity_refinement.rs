#![cfg(feature = "verus-proofs")]

use crate::collinearity_coplanarity;
use vcad_math::orientation::{
    edge_vectors2_linear_dependent_spec, is_collinear, orient2d_spec,
};
use vcad_math::orientation3::{
    edge_vectors3_linear_dependent_spec, is_coplanar, orient3d_spec,
};
use vcad_math::point3::Point3;
use vcad_math::runtime_point2::RuntimePoint2;
use vcad_math::runtime_point3::RuntimePoint3;
use vstd::prelude::*;

verus! {

pub open spec fn base_plane_noncollinear3_spec(a: Point3, b: Point3, c: Point3) -> bool {
    let n = b.sub_spec(a).cross_spec(c.sub_spec(a));
    !(n.x.signum() == 0 && n.y.signum() == 0 && n.z.signum() == 0)
}

pub open spec fn coplanar5_wrt_base_spec(a: Point3, b: Point3, c: Point3, d: Point3, e: Point3) -> bool {
    is_coplanar(a, b, c, d) && is_coplanar(a, b, c, e)
}

pub open spec fn coplanar5_from_base_spec(a: Point3, b: Point3, c: Point3, d: Point3, e: Point3) -> bool {
    &&& base_plane_noncollinear3_spec(a, b, c)
    &&& is_coplanar(a, b, c, d)
    &&& is_coplanar(a, b, c, e)
}

/// Set-level 5-point coplanarity:
/// at least one non-collinear triple from the set serves as a valid base plane
/// for the remaining two points.
pub open spec fn coplanar5_set_spec(a: Point3, b: Point3, c: Point3, d: Point3, e: Point3) -> bool {
    coplanar5_from_base_spec(a, b, c, d, e)
        || coplanar5_from_base_spec(a, b, d, c, e)
        || coplanar5_from_base_spec(a, b, e, c, d)
        || coplanar5_from_base_spec(a, c, d, b, e)
        || coplanar5_from_base_spec(a, c, e, b, d)
        || coplanar5_from_base_spec(a, d, e, b, c)
        || coplanar5_from_base_spec(b, c, d, a, e)
        || coplanar5_from_base_spec(b, c, e, a, d)
        || coplanar5_from_base_spec(b, d, e, a, c)
        || coplanar5_from_base_spec(c, d, e, a, b)
}

#[allow(dead_code)]
pub fn runtime_collinear2d_matches_orient_zero(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
) -> (out: bool)
    ensures
        out == (orient2d_spec(a@, b@, c@).signum() == 0),
{
    let out = collinearity_coplanarity::collinear2d(a, b, c);
    proof {
        vcad_math::orientation::lemma_is_collinear_iff_zero(a@, b@, c@);
    }
    out
}

#[allow(dead_code)]
pub fn runtime_collinear2d_iff_linear_dependent(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
) -> (out: bool)
    ensures
        out == edge_vectors2_linear_dependent_spec(a@, b@, c@),
{
    let out = collinearity_coplanarity::collinear2d(a, b, c);
    proof {
        vcad_math::orientation::lemma_is_collinear_iff_edge_vectors_linear_dependent(a@, b@, c@);
    }
    out
}

#[allow(dead_code)]
pub fn runtime_coplanar_matches_orient_zero(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
) -> (out: bool)
    ensures
        out == (orient3d_spec(a@, b@, c@, d@).signum() == 0),
{
    let out = collinearity_coplanarity::coplanar(a, b, c, d);
    out
}

#[allow(dead_code)]
pub fn runtime_coplanar_iff_linear_dependent(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
) -> (out: bool)
    ensures
        out == edge_vectors3_linear_dependent_spec(a@, b@, c@, d@),
{
    let out = collinearity_coplanarity::coplanar(a, b, c, d);
    proof {
        vcad_math::orientation3::lemma_is_coplanar_iff_edge_vectors_linear_dependent(a@, b@, c@, d@);
    }
    out
}

#[allow(dead_code)]
pub fn runtime_coplanarity_extension_wrt_base(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
    e: &RuntimePoint3,
) -> (pair: (bool, bool))
    requires
        is_coplanar(a@, b@, c@, d@),
        is_coplanar(a@, b@, c@, e@),
        base_plane_noncollinear3_spec(a@, b@, c@),
    ensures
        pair.0 == is_coplanar(a@, b@, c@, d@),
        pair.1 == is_coplanar(a@, b@, c@, e@),
        pair.0,
        pair.1,
        coplanar5_wrt_base_spec(a@, b@, c@, d@, e@),
{
    let d_ok = collinearity_coplanarity::coplanar(a, b, c, d);
    let e_ok = collinearity_coplanarity::coplanar(a, b, c, e);
    proof {
        assert(coplanar5_wrt_base_spec(a@, b@, c@, d@, e@));
    }
    (d_ok, e_ok)
}

#[allow(dead_code)]
pub fn runtime_coplanarity_extension_set_level(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
    e: &RuntimePoint3,
) -> (out: bool)
    requires
        is_coplanar(a@, b@, c@, d@),
        is_coplanar(a@, b@, c@, e@),
        base_plane_noncollinear3_spec(a@, b@, c@),
    ensures
        out,
        coplanar5_set_spec(a@, b@, c@, d@, e@),
{
    let d_ok = collinearity_coplanarity::coplanar(a, b, c, d);
    let e_ok = collinearity_coplanarity::coplanar(a, b, c, e);
    let out = d_ok && e_ok;
    proof {
        assert(coplanar5_from_base_spec(a@, b@, c@, d@, e@));
        assert(coplanar5_set_spec(a@, b@, c@, d@, e@));
    }
    out
}

} // verus!
