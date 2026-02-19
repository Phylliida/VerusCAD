#![cfg(feature = "verus-proofs")]

use crate::segment_intersection::{self, SegmentIntersection2dKind, SegmentIntersection2dKindSpec};
use vcad_math::runtime_point2::RuntimePoint2;
use vcad_math::runtime_wf as wf;
use vstd::prelude::*;
use vstd::view::View;

verus! {

#[verifier::external_type_specification]
pub struct ExSegmentIntersection2dKind(SegmentIntersection2dKind);

impl View for SegmentIntersection2dKind {
    type V = SegmentIntersection2dKindSpec;

    open spec fn view(&self) -> SegmentIntersection2dKindSpec {
        match self {
            SegmentIntersection2dKind::Disjoint => SegmentIntersection2dKindSpec::Disjoint,
            SegmentIntersection2dKind::Proper => SegmentIntersection2dKindSpec::Proper,
            SegmentIntersection2dKind::EndpointTouch => SegmentIntersection2dKindSpec::EndpointTouch,
            SegmentIntersection2dKind::CollinearOverlap => SegmentIntersection2dKindSpec::CollinearOverlap,
        }
    }
}

#[allow(dead_code)]
pub proof fn segment_intersection_runtime_kind_exhaustive(k: SegmentIntersection2dKind)
    ensures
        (k@ is Disjoint) || (k@ is Proper) || (k@ is EndpointTouch) || (k@ is CollinearOverlap),
{
    match k {
        SegmentIntersection2dKind::Disjoint => {
            assert(k@ is Disjoint);
        }
        SegmentIntersection2dKind::Proper => {
            assert(k@ is Proper);
        }
        SegmentIntersection2dKind::EndpointTouch => {
            assert(k@ is EndpointTouch);
        }
        SegmentIntersection2dKind::CollinearOverlap => {
            assert(k@ is CollinearOverlap);
        }
    }
}

#[allow(dead_code)]
pub proof fn segment_intersection_runtime_kind_pairwise_disjoint(k: SegmentIntersection2dKind)
    ensures
        !((k@ is Disjoint) && (k@ is Proper)),
        !((k@ is Disjoint) && (k@ is EndpointTouch)),
        !((k@ is Disjoint) && (k@ is CollinearOverlap)),
        !((k@ is Proper) && (k@ is EndpointTouch)),
        !((k@ is Proper) && (k@ is CollinearOverlap)),
        !((k@ is EndpointTouch) && (k@ is CollinearOverlap)),
{
    match k {
        SegmentIntersection2dKind::Disjoint => {
            assert(!(k@ is Proper));
            assert(!(k@ is EndpointTouch));
            assert(!(k@ is CollinearOverlap));
        }
        SegmentIntersection2dKind::Proper => {
            assert(!(k@ is Disjoint));
            assert(!(k@ is EndpointTouch));
            assert(!(k@ is CollinearOverlap));
        }
        SegmentIntersection2dKind::EndpointTouch => {
            assert(!(k@ is Disjoint));
            assert(!(k@ is Proper));
            assert(!(k@ is CollinearOverlap));
        }
        SegmentIntersection2dKind::CollinearOverlap => {
            assert(!(k@ is Disjoint));
            assert(!(k@ is Proper));
            assert(!(k@ is EndpointTouch));
        }
    }
}

#[allow(dead_code)]
pub proof fn segment_intersection_kind_spec_total_for_runtime_points(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
    d: &RuntimePoint2,
)
    ensures
        (segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is Disjoint)
            || (segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is Proper)
            || (segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is EndpointTouch)
            || (segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is CollinearOverlap),
{
    segment_intersection::lemma_segment_intersection_kind_spec_exhaustive(a@, b@, c@, d@);
}

#[allow(dead_code)]
pub proof fn segment_intersection_kind_spec_pairwise_disjoint_for_runtime_points(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
    d: &RuntimePoint2,
)
    ensures
        !((segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is Disjoint)
            && (segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is Proper)),
        !((segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is Disjoint)
            && (segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is EndpointTouch)),
        !((segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is Disjoint)
            && (segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is CollinearOverlap)),
        !((segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is Proper)
            && (segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is EndpointTouch)),
        !((segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is Proper)
            && (segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is CollinearOverlap)),
        !((segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is EndpointTouch)
            && (segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is CollinearOverlap)),
{
    segment_intersection::lemma_segment_intersection_kind_spec_pairwise_disjoint(a@, b@, c@, d@);
}

#[allow(dead_code)]
pub fn runtime_segment_intersection_kind_refines_spec(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
    d: &RuntimePoint2,
) -> (out: SegmentIntersection2dKind)
    requires
        wf::point2_wf4_spec(a, b, c, d),
    ensures
        out@ == segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@),
{
    segment_intersection::segment_intersection_kind_2d(a, b, c, d)
}

#[allow(dead_code)]
pub fn runtime_segment_intersection_kind_total_from_classifier(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
    d: &RuntimePoint2,
) -> (out: SegmentIntersection2dKind)
    requires
        wf::point2_wf4_spec(a, b, c, d),
    ensures
        (out@ is Disjoint) || (out@ is Proper) || (out@ is EndpointTouch) || (out@ is CollinearOverlap),
{
    let out = runtime_segment_intersection_kind_refines_spec(a, b, c, d);
    proof {
        segment_intersection_runtime_kind_exhaustive(out);
    }
    out
}

#[allow(dead_code)]
pub fn runtime_segment_intersection_kind_disjointness_from_classifier(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
    d: &RuntimePoint2,
) -> (out: SegmentIntersection2dKind)
    requires
        wf::point2_wf4_spec(a, b, c, d),
    ensures
        !((out@ is Disjoint) && (out@ is Proper)),
        !((out@ is Disjoint) && (out@ is EndpointTouch)),
        !((out@ is Disjoint) && (out@ is CollinearOverlap)),
        !((out@ is Proper) && (out@ is EndpointTouch)),
        !((out@ is Proper) && (out@ is CollinearOverlap)),
        !((out@ is EndpointTouch) && (out@ is CollinearOverlap)),
{
    let out = runtime_segment_intersection_kind_refines_spec(a, b, c, d);
    proof {
        segment_intersection_runtime_kind_pairwise_disjoint(out);
    }
    out
}

#[allow(dead_code)]
pub fn runtime_segment_intersection_point_refines_spec(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
    d: &RuntimePoint2,
) -> (out: Option<RuntimePoint2>)
    requires
        wf::point2_wf4_spec(a, b, c, d),
    ensures
        (segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is Disjoint) ==> out.is_none(),
        (segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is CollinearOverlap) ==> out.is_none(),
        (segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is EndpointTouch) ==> out.is_some(),
        (segment_intersection::segment_intersection_kind_spec(a@, b@, c@, d@) is EndpointTouch) ==> match out {
            Option::None => true,
            Option::Some(p) => segment_intersection::point_on_both_segments_spec(p@, a@, b@, c@, d@),
        },
{
    segment_intersection::segment_intersection_point_2d(a, b, c, d)
}

} // verus!
