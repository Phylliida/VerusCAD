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

pub open spec fn collinear3d_cross_zero_spec(a: Point3, b: Point3, c: Point3) -> bool {
    let cross = b.sub_spec(a).cross_spec(c.sub_spec(a));
    (cross.x.signum() == 0) && (cross.y.signum() == 0) && (cross.z.signum() == 0)
}

pub assume_specification[ collinearity_coplanarity::collinear2d ](
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
) -> (out: bool)
    ensures
        out == is_collinear(a@, b@, c@),
;

pub assume_specification[ collinearity_coplanarity::collinear3d ](
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: bool)
    ensures
        out == collinear3d_cross_zero_spec(a@, b@, c@),
;

pub assume_specification[ collinearity_coplanarity::coplanar ](
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
) -> (out: bool)
    ensures
        out == is_coplanar(a@, b@, c@, d@),
;

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

} // verus!
