use crate::sidedness;
use vcad_math::orientation3::{orientation3_spec, Orientation3};
use vcad_math::point3::Point3;
use vcad_math::runtime_point3::RuntimePoint3;
use vcad_math::runtime_scalar::RuntimeScalar;
use vstd::prelude::*;

verus! {

pub open spec fn strict_opposite_sides_spec(a: Point3, b: Point3, c: Point3, d: Point3, e: Point3) -> bool {
    ((orientation3_spec(a, b, c, d) is Positive) && (orientation3_spec(a, b, c, e) is Negative))
        || ((orientation3_spec(a, b, c, d) is Negative) && (orientation3_spec(a, b, c, e) is Positive))
}

pub assume_specification[ sidedness::point_above_plane ](
    p: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: bool)
    ensures
        out == (orientation3_spec(a@, b@, c@, p@) is Positive),
;

pub assume_specification[ sidedness::point_below_plane ](
    p: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: bool)
    ensures
        out == (orientation3_spec(a@, b@, c@, p@) is Negative),
;

pub assume_specification[ sidedness::point_on_plane ](
    p: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: bool)
    ensures
        out == (orientation3_spec(a@, b@, c@, p@) is Coplanar),
;

pub assume_specification[ sidedness::segment_crosses_plane_strict ](
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: bool)
    ensures
        out == strict_opposite_sides_spec(a@, b@, c@, d@, e@),
;

pub assume_specification[ sidedness::segment_plane_intersection_parameter_strict ](
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: Option<RuntimeScalar>)
    ensures
        out.is_some() == strict_opposite_sides_spec(a@, b@, c@, d@, e@),
;

pub assume_specification[ sidedness::segment_plane_intersection_point_strict ](
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: Option<RuntimePoint3>)
    ensures
        out.is_some() == strict_opposite_sides_spec(a@, b@, c@, d@, e@),
;

#[allow(dead_code)]
pub fn runtime_plane_side_partition(
    p: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (triple: (bool, bool, bool))
    ensures
        triple.0 == (orientation3_spec(a@, b@, c@, p@) is Positive),
        triple.1 == (orientation3_spec(a@, b@, c@, p@) is Negative),
        triple.2 == (orientation3_spec(a@, b@, c@, p@) is Coplanar),
        triple.0 || triple.1 || triple.2,
        !(triple.0 && triple.1),
        !(triple.0 && triple.2),
        !(triple.1 && triple.2),
{
    let above = sidedness::point_above_plane(p, a, b, c);
    let below = sidedness::point_below_plane(p, a, b, c);
    let on = sidedness::point_on_plane(p, a, b, c);
    proof {
        vcad_math::orientation3::lemma_orientation3_spec_exclusive(a@, b@, c@, p@);
    }
    (above, below, on)
}

#[allow(dead_code)]
pub fn runtime_segment_crosses_plane_from_opposite_sides(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: bool)
    requires
        (orientation3_spec(a@, b@, c@, d@) is Positive),
        (orientation3_spec(a@, b@, c@, e@) is Negative),
    ensures
        out,
{
    let out = sidedness::segment_crosses_plane_strict(d, e, a, b, c);
    proof {
        assert(strict_opposite_sides_spec(a@, b@, c@, d@, e@));
    }
    out
}

#[allow(dead_code)]
pub fn runtime_segment_crosses_plane_from_opposite_sides_swapped(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: bool)
    requires
        (orientation3_spec(a@, b@, c@, d@) is Negative),
        (orientation3_spec(a@, b@, c@, e@) is Positive),
    ensures
        out,
{
    let out = sidedness::segment_crosses_plane_strict(d, e, a, b, c);
    proof {
        assert(strict_opposite_sides_spec(a@, b@, c@, d@, e@));
    }
    out
}

#[allow(dead_code)]
pub fn runtime_segment_crossing_implies_not_on_plane_endpoints(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (triple: (bool, bool, bool))
    ensures
        triple.0 == strict_opposite_sides_spec(a@, b@, c@, d@, e@),
        triple.1 == (orientation3_spec(a@, b@, c@, d@) is Coplanar),
        triple.2 == (orientation3_spec(a@, b@, c@, e@) is Coplanar),
        triple.0 ==> !triple.1,
        triple.0 ==> !triple.2,
{
    let crosses = sidedness::segment_crosses_plane_strict(d, e, a, b, c);
    let d_on = sidedness::point_on_plane(d, a, b, c);
    let e_on = sidedness::point_on_plane(e, a, b, c);
    proof {
        if crosses {
            assert((orientation3_spec(a@, b@, c@, d@) is Positive) || (orientation3_spec(a@, b@, c@, d@) is Negative));
            assert((orientation3_spec(a@, b@, c@, e@) is Positive) || (orientation3_spec(a@, b@, c@, e@) is Negative));
            assert(!(orientation3_spec(a@, b@, c@, d@) is Coplanar));
            assert(!(orientation3_spec(a@, b@, c@, e@) is Coplanar));
        }
    }
    (crosses, d_on, e_on)
}

#[allow(dead_code)]
pub fn runtime_crossing_implies_intersection_parameter_exists(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: Option<RuntimeScalar>)
    requires
        strict_opposite_sides_spec(a@, b@, c@, d@, e@),
    ensures
        out.is_some(),
{
    let out = sidedness::segment_plane_intersection_parameter_strict(d, e, a, b, c);
    out
}

#[allow(dead_code)]
pub fn runtime_no_crossing_implies_no_intersection_parameter(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: Option<RuntimeScalar>)
    requires
        !strict_opposite_sides_spec(a@, b@, c@, d@, e@),
    ensures
        out.is_none(),
{
    let out = sidedness::segment_plane_intersection_parameter_strict(d, e, a, b, c);
    out
}

} // verus!
