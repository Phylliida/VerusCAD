#![cfg(feature = "verus-proofs")]

use crate::convex_polygon;
use crate::segment_polygon_overlap;
use vcad_math::runtime_point2::RuntimePoint2;
use vcad_math::runtime_wf as wf;
use vstd::prelude::*;

verus! {

#[allow(dead_code)]
pub fn runtime_segment_overlaps_convex_polygon_refines_spec(
    seg_start: &RuntimePoint2,
    seg_end: &RuntimePoint2,
    polygon: &[RuntimePoint2],
) -> (out: bool)
    requires
        wf::point2_wf2_spec(seg_start, seg_end),
        convex_polygon::point2_seq_wf_spec(polygon@),
    ensures
        out == segment_polygon_overlap::segment_overlaps_convex_polygon_composed_spec(seg_start@, seg_end@, polygon@),
{
    segment_polygon_overlap::segment_overlaps_convex_polygon_2d(seg_start, seg_end, polygon)
}

#[allow(dead_code)]
pub fn runtime_segment_overlaps_convex_polygon_true_implies_structured_witness(
    seg_start: &RuntimePoint2,
    seg_end: &RuntimePoint2,
    polygon: &[RuntimePoint2],
) -> (out: bool)
    requires
        wf::point2_wf2_spec(seg_start, seg_end),
        convex_polygon::point2_seq_wf_spec(polygon@),
    ensures
        out == segment_polygon_overlap::segment_overlaps_convex_polygon_composed_spec(seg_start@, seg_end@, polygon@),
        out ==> (
            convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(seg_start@, polygon@)
                || convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(seg_end@, polygon@)
                || segment_polygon_overlap::segment_hits_some_polygon_edge_spec(seg_start@, seg_end@, polygon@)
        ),
{
    let out = segment_polygon_overlap::segment_overlaps_convex_polygon_2d(seg_start, seg_end, polygon);
    proof {
        assert(out == segment_polygon_overlap::segment_overlaps_convex_polygon_composed_spec(seg_start@, seg_end@, polygon@));
        if out {
            assert(segment_polygon_overlap::segment_overlaps_convex_polygon_composed_spec(seg_start@, seg_end@, polygon@)
                == (
                polygon@.len() >= 3
                    && (
                    convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(seg_start@, polygon@)
                        || convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(seg_end@, polygon@)
                        || segment_polygon_overlap::segment_hits_some_polygon_edge_spec(seg_start@, seg_end@, polygon@)
                )
            ));
            assert(polygon@.len() >= 3);
            assert(
                convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(seg_start@, polygon@)
                    || convex_polygon::point_in_convex_polygon_boundary_inclusive_spec(seg_end@, polygon@)
                    || segment_polygon_overlap::segment_hits_some_polygon_edge_spec(seg_start@, seg_end@, polygon@)
            );
        }
    }
    out
}

} // verus!
