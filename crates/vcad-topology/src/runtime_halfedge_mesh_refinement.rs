#![cfg(feature = "verus-proofs")]

use crate::halfedge_mesh::{Edge, Face, HalfEdge, Mesh, MeshBuildError, Vertex};
use crate::verified_checker_kernels as kernels;
use vcad_math::runtime_point3::RuntimePoint3;
#[cfg(verus_keep_ghost)]
use vcad_math::scalar::Scalar;
use vstd::prelude::*;
use vstd::view::View;

verus! {
#[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
#[verifier::external_type_specification]
pub struct ExMesh(Mesh);

#[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
#[verifier::external_type_specification]
pub struct ExMeshBuildError(MeshBuildError);

#[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
#[verifier::external_type_specification]
pub struct ExHalfEdge(HalfEdge);

#[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
#[verifier::external_type_specification]
pub struct ExVertex(Vertex);

#[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
#[verifier::external_type_specification]
pub struct ExEdge(Edge);

#[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
#[verifier::external_type_specification]
pub struct ExFace(Face);

pub(crate) fn mesh_build_error_empty_face_set() -> MeshBuildError {
    MeshBuildError::EmptyFaceSet
}

#[verifier::exec_allows_no_decreases_clause]
pub(crate) fn ex_from_face_cycles_constructive_abort() -> ! {
    loop {}
}
} // verus!

include!("runtime_halfedge_mesh_refinement/model_and_bridge_specs.rs");
include!("runtime_halfedge_mesh_refinement/kernel_bridge_lemmas.rs");
include!("runtime_halfedge_mesh_refinement/components_and_validity_specs.rs");
include!("runtime_halfedge_mesh_refinement/from_face_cycles_specs_and_lemmas.rs");
include!("runtime_halfedge_mesh_refinement/from_face_cycles_runtime_checks.rs");
include!("runtime_halfedge_mesh_refinement/core_runtime_checks_and_bridges.rs");
include!("runtime_halfedge_mesh_refinement/kernel_component_runtime_checks.rs");
include!("runtime_halfedge_mesh_refinement/constructive_gates_and_examples.rs");
