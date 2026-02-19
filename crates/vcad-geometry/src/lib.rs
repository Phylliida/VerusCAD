pub mod collinearity_coplanarity;
pub mod convex_polygon;
pub mod orientation_predicates;
pub mod phase5_upstream_lemmas;
pub mod segment_intersection;
pub mod segment_polygon_overlap;
pub mod segment_triangle_intersection;
pub mod sidedness;

#[cfg(all(feature = "verus-proofs", verus_keep_ghost))]
mod runtime_collinearity_coplanarity_refinement;
#[cfg(all(feature = "verus-proofs", verus_keep_ghost))]
mod runtime_convex_polygon_refinement;
#[cfg(all(feature = "verus-proofs", verus_keep_ghost))]
mod runtime_orientation_predicates_refinement;
#[cfg(all(feature = "verus-proofs", verus_keep_ghost))]
mod runtime_segment_intersection_refinement;
#[cfg(all(feature = "verus-proofs", verus_keep_ghost))]
mod runtime_segment_polygon_overlap_refinement;
#[cfg(all(feature = "verus-proofs", verus_keep_ghost))]
mod runtime_sidedness_refinement;
