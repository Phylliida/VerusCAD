use super::{Mesh, MeshBuildError};
use std::fs;
use std::path::{Path, PathBuf};
#[cfg(feature = "verus-proofs")]
use std::collections::BTreeSet;
#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
use crate::runtime_halfedge_mesh_refinement::{
    check_geometric_topological_consistency_constructive,
    is_valid_with_geometry_constructive,
    runtime_check_face_coplanarity_seed0_fixed_witness_bridge,
    runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_and_quad_face_preconditions,
    runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_and_triangle_or_quad_face_preconditions,
    runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_and_triangle_face_preconditions,
    runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_preconditions,
    runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_phase5_runtime_bundle_sound_bridge,
    runtime_check_face_coplanarity_seed0_fixed_witness_sound_bridge,
    runtime_check_face_coplanarity_seed0_fixed_witness_triangle_or_quad_sound_complete_bridge,
    runtime_check_face_coplanarity_seed0_fixed_witness_triangle_or_quad_sound_bridge,
    runtime_check_face_convexity_triangle_projected_turn_sound_bridge,
    runtime_check_geometric_topological_consistency_sound_bridge,
    runtime_check_phase4_valid_and_shared_edge_local_orientation_imply_geometric_topological_consistency_spec,
};
#[cfg(feature = "geometry-checks")]
use super::GeometricTopologicalConsistencyFailure;
#[cfg(feature = "geometry-checks")]
use vcad_geometry::collinearity_coplanarity::{collinear3d, coplanar};
#[cfg(feature = "geometry-checks")]
use vcad_geometry::orientation_predicates::{orient2d_sign, orient3d_sign, orient3d_value};
#[cfg(feature = "geometry-checks")]
use vcad_math::runtime_point2::RuntimePoint2;
use vcad_math::runtime_point3::RuntimePoint3;
#[cfg(feature = "geometry-checks")]
use vcad_math::runtime_scalar::RuntimeScalar;
#[cfg(feature = "geometry-checks")]
use vcad_math::runtime_vec3::RuntimeVec3;

fn is_rust_identifier_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

fn has_identifier_token(contents: &str, token: &str) -> bool {
    contents
        .split(|c: char| !is_rust_identifier_char(c))
        .any(|piece| piece == token)
}

fn collect_rs_files_recursively(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = fs::read_dir(dir).expect("source directory should be readable");
    for entry_result in entries {
        let entry = entry_result.expect("directory entry should be readable");
        let path = entry.path();
        if path.is_dir() {
            collect_rs_files_recursively(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
            out.push(path);
        }
    }
}

#[cfg(feature = "geometry-checks")]
fn append_translated_tetrahedron(
    vertices: &mut Vec<RuntimePoint3>,
    faces: &mut Vec<Vec<usize>>,
    tx: i64,
    ty: i64,
    tz: i64,
) {
    let base = vertices.len();
    vertices.push(RuntimePoint3::from_ints(tx, ty, tz));
    vertices.push(RuntimePoint3::from_ints(tx + 1, ty, tz));
    vertices.push(RuntimePoint3::from_ints(tx, ty + 1, tz));
    vertices.push(RuntimePoint3::from_ints(tx, ty, tz + 1));

    faces.push(vec![base, base + 1, base + 2]);
    faces.push(vec![base, base + 3, base + 1]);
    faces.push(vec![base + 1, base + 3, base + 2]);
    faces.push(vec![base + 2, base + 3, base]);
}

#[cfg(feature = "geometry-checks")]
fn build_disconnected_translated_tetrahedra_mesh(component_origins: &[(i64, i64, i64)]) -> Mesh {
    let mut vertices = Vec::with_capacity(component_origins.len() * 4);
    let mut faces = Vec::with_capacity(component_origins.len() * 4);
    for &(tx, ty, tz) in component_origins {
        append_translated_tetrahedron(&mut vertices, &mut faces, tx, ty, tz);
    }
    Mesh::from_face_cycles(vertices, &faces)
        .expect("disconnected translated tetrahedra stress fixture should build")
}

#[cfg(feature = "geometry-checks")]
fn phase5_checker_signature(mesh: &Mesh) -> [bool; 10] {
    [
        mesh.check_no_zero_length_geometric_edges(),
        mesh.check_face_corner_non_collinearity(),
        mesh.check_face_coplanarity(),
        mesh.check_face_convexity(),
        mesh.check_face_plane_consistency(),
        mesh.check_shared_edge_local_orientation_consistency(),
        mesh.check_no_forbidden_face_face_intersections(),
        mesh.check_outward_face_normals(),
        mesh.check_geometric_topological_consistency(),
        mesh.is_valid_with_geometry(),
    ]
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn assert_face_coplanarity_runtime_seed0_bridge_parity(mesh: &Mesh, label: &str) {
    let runtime_coplanarity_ok = mesh.check_face_coplanarity();
    let seed0_bridge_ok = runtime_check_face_coplanarity_seed0_fixed_witness_bridge(mesh);
    assert_eq!(
        seed0_bridge_ok, runtime_coplanarity_ok,
        "seed0 coplanarity bridge parity failed for {label}"
    );
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn assert_face_coplanarity_runtime_seed0_sound_bridge_parity(mesh: &Mesh, label: &str) {
    let runtime_coplanarity_ok = mesh.check_face_coplanarity();
    let seed0_sound_bridge_ok = runtime_check_face_coplanarity_seed0_fixed_witness_sound_bridge(mesh);
    assert_eq!(
        seed0_sound_bridge_ok, runtime_coplanarity_ok,
        "seed0 coplanarity sound bridge parity failed for {label}"
    );
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn assert_face_coplanarity_runtime_seed0_triangle_or_quad_sound_bridge_parity(
    mesh: &Mesh,
    label: &str,
) {
    assert!(
        mesh_all_faces_are_triangles_or_quads(mesh),
        "triangle/quad seed0 coplanarity sound bridge parity requires triangle/quad faces in {label}"
    );
    let runtime_coplanarity_ok = mesh.check_face_coplanarity();
    let seed0_triangle_or_quad_sound_bridge_ok =
        runtime_check_face_coplanarity_seed0_fixed_witness_triangle_or_quad_sound_bridge(mesh);
    assert_eq!(
        seed0_triangle_or_quad_sound_bridge_ok, runtime_coplanarity_ok,
        "triangle/quad seed0 coplanarity sound bridge parity failed for {label}"
    );
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn assert_face_coplanarity_seed0_triangle_or_quad_sound_complete_bridge_parity(
    mesh: &Mesh,
    label: &str,
) {
    assert!(
        mesh_all_faces_are_triangles_or_quads(mesh),
        "triangle/quad seed0 coplanarity sound+complete bridge parity requires triangle/quad faces in {label}"
    );
    let runtime_coplanarity_ok = mesh.check_face_coplanarity();
    let seed0_triangle_or_quad_sound_complete_bridge_ok =
        runtime_check_face_coplanarity_seed0_fixed_witness_triangle_or_quad_sound_complete_bridge(
            mesh,
        );
    assert_eq!(
        seed0_triangle_or_quad_sound_complete_bridge_ok, runtime_coplanarity_ok,
        "triangle/quad seed0 coplanarity sound+complete bridge parity failed for {label}"
    );
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn assert_face_convexity_triangle_projected_turn_sound_bridge_parity(mesh: &Mesh, label: &str) {
    assert!(
        mesh_all_faces_are_triangles(mesh),
        "triangle convexity projected-turn sound bridge parity requires triangle faces in {label}"
    );
    let runtime_convexity_ok = mesh.check_face_convexity();
    let triangle_projected_turn_sound_bridge_ok =
        runtime_check_face_convexity_triangle_projected_turn_sound_bridge(mesh);
    assert_eq!(
        triangle_projected_turn_sound_bridge_ok, runtime_convexity_ok,
        "triangle convexity projected-turn sound bridge parity failed for {label}"
    );
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn assert_face_coplanarity_seed0_phase5_runtime_bundle_completeness_bridge_parity(
    mesh: &Mesh,
    label: &str,
) {
    let geometric_sound_bridge_ok = runtime_check_geometric_topological_consistency_sound_bridge(mesh);
    let coplanarity_bundle_complete_ok =
        runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_phase5_runtime_bundle_sound_bridge(
            mesh,
        );
    assert_eq!(
        coplanarity_bundle_complete_ok, geometric_sound_bridge_ok,
        "seed0 coplanarity phase5-bundle completeness parity failed for {label}"
    );
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn assert_face_coplanarity_seed0_oriented_plane_completeness_bridge_parity(
    mesh: &Mesh,
    label: &str,
) {
    let geometric_sound_bridge_ok = runtime_check_geometric_topological_consistency_sound_bridge(mesh);
    let oriented_plane_complete_ok = if geometric_sound_bridge_ok {
        runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_preconditions(
            mesh,
        )
    } else {
        false
    };
    assert_eq!(
        oriented_plane_complete_ok, geometric_sound_bridge_ok,
        "seed0 coplanarity oriented-plane completeness parity failed for {label}"
    );
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn assert_face_coplanarity_seed0_oriented_plane_triangle_completeness_bridge_parity(
    mesh: &Mesh,
    label: &str,
) {
    assert!(
        mesh_all_faces_are_triangles(mesh),
        "triangle-only oriented-plane completeness parity requires triangle faces in {label}"
    );
    let geometric_sound_bridge_ok = runtime_check_geometric_topological_consistency_sound_bridge(mesh);
    let oriented_plane_triangle_complete_ok = if geometric_sound_bridge_ok {
        runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_and_triangle_face_preconditions(
            mesh,
        )
    } else {
        false
    };
    assert_eq!(
        oriented_plane_triangle_complete_ok, geometric_sound_bridge_ok,
        "seed0 coplanarity oriented-plane triangle completeness parity failed for {label}"
    );
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn assert_face_coplanarity_seed0_oriented_plane_quad_completeness_bridge_parity(
    mesh: &Mesh,
    label: &str,
) {
    assert!(
        mesh_all_faces_are_quads(mesh),
        "quad-only oriented-plane completeness parity requires quad faces in {label}"
    );
    let geometric_sound_bridge_ok = runtime_check_geometric_topological_consistency_sound_bridge(mesh);
    let oriented_plane_quad_complete_ok = if geometric_sound_bridge_ok {
        runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_and_quad_face_preconditions(
            mesh,
        )
    } else {
        false
    };
    assert_eq!(
        oriented_plane_quad_complete_ok, geometric_sound_bridge_ok,
        "seed0 coplanarity oriented-plane quad completeness parity failed for {label}"
    );
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn assert_face_coplanarity_seed0_oriented_plane_triangle_or_quad_completeness_bridge_parity(
    mesh: &Mesh,
    label: &str,
) {
    assert!(
        mesh_all_faces_are_triangles_or_quads(mesh),
        "triangle/quad-only oriented-plane completeness parity requires triangle/quad faces in {label}"
    );
    let geometric_sound_bridge_ok = runtime_check_geometric_topological_consistency_sound_bridge(mesh);
    let oriented_plane_triangle_or_quad_complete_ok = if geometric_sound_bridge_ok {
        runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_and_triangle_or_quad_face_preconditions(
            mesh,
        )
    } else {
        false
    };
    assert_eq!(
        oriented_plane_triangle_or_quad_complete_ok, geometric_sound_bridge_ok,
        "seed0 coplanarity oriented-plane triangle/quad completeness parity failed for {label}"
    );
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn assert_constructive_phase5_gate_parity(mesh: &Mesh, label: &str) {
    assert_face_coplanarity_runtime_seed0_bridge_parity(mesh, label);
    assert_face_coplanarity_runtime_seed0_sound_bridge_parity(mesh, label);
    if mesh_all_faces_are_triangles(mesh) {
        assert_face_convexity_triangle_projected_turn_sound_bridge_parity(mesh, label);
    }
    if mesh_all_faces_are_triangles_or_quads(mesh) {
        assert_face_coplanarity_runtime_seed0_triangle_or_quad_sound_bridge_parity(mesh, label);
        assert_face_coplanarity_seed0_triangle_or_quad_sound_complete_bridge_parity(mesh, label);
    }
    assert_face_coplanarity_seed0_oriented_plane_completeness_bridge_parity(mesh, label);
    assert_face_coplanarity_seed0_phase5_runtime_bundle_completeness_bridge_parity(mesh, label);

    let geometric_runtime = mesh.check_geometric_topological_consistency();
    let geometric_sound_bridge = runtime_check_geometric_topological_consistency_sound_bridge(mesh);
    assert_eq!(
        geometric_sound_bridge, geometric_runtime,
        "constructive geometric sound bridge parity failed for {label}"
    );

    let geometric_constructive = check_geometric_topological_consistency_constructive(mesh)
        .expect("constructive geometric gate should produce a witness");
    assert_eq!(
        geometric_constructive.api_ok, geometric_runtime,
        "constructive geometric gate parity failed for {label}"
    );
    assert_eq!(
        geometric_constructive.phase4_valid_ok,
        mesh.is_valid(),
        "constructive phase4 witness mismatch for {label}"
    );
    assert_eq!(
        geometric_constructive.no_zero_length_geometric_edges_ok,
        mesh.check_no_zero_length_geometric_edges(),
        "constructive zero-length-edge witness mismatch for {label}"
    );
    assert_eq!(
        geometric_constructive.face_corner_non_collinearity_ok,
        mesh.check_face_corner_non_collinearity(),
        "constructive face-corner non-collinearity witness mismatch for {label}"
    );
    assert_eq!(
        geometric_constructive.face_coplanarity_ok,
        mesh.check_face_coplanarity(),
        "constructive coplanarity witness mismatch for {label}"
    );
    assert_eq!(
        geometric_constructive.face_convexity_ok,
        mesh.check_face_convexity(),
        "constructive convexity witness mismatch for {label}"
    );
    assert_eq!(
        geometric_constructive.face_plane_consistency_ok,
        mesh.check_face_plane_consistency(),
        "constructive face-plane-consistency witness mismatch for {label}"
    );
    assert_eq!(
        geometric_constructive.shared_edge_local_orientation_ok,
        mesh.check_shared_edge_local_orientation_consistency(),
        "constructive shared-edge-orientation witness mismatch for {label}"
    );
    assert_eq!(
        geometric_constructive.no_forbidden_face_face_intersections_ok,
        mesh.check_no_forbidden_face_face_intersections(),
        "constructive forbidden-face-intersection witness mismatch for {label}"
    );
    assert_eq!(
        geometric_constructive.outward_face_normals_ok,
        mesh.check_outward_face_normals(),
        "constructive outward-face-normal witness mismatch for {label}"
    );

    let with_geometry_runtime = mesh.is_valid_with_geometry();
    let with_geometry_constructive = is_valid_with_geometry_constructive(mesh)
        .expect("constructive valid-with-geometry gate should produce a witness");
    assert_eq!(
        with_geometry_constructive.api_ok, with_geometry_runtime,
        "constructive valid-with-geometry gate parity failed for {label}"
    );
    assert_eq!(
        with_geometry_constructive.phase4_validity_ok,
        mesh.is_valid(),
        "constructive valid-with-geometry phase4 witness mismatch for {label}"
    );
    assert_eq!(
        with_geometry_constructive.geometric_topological_consistency_ok, geometric_runtime,
        "constructive valid-with-geometry geometric witness mismatch for {label}"
    );
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn build_noncoplanar_single_quad_double_face_mesh_with_lift(lift_z: i64) -> Mesh {
    let noncoplanar_vertices = vec![
        RuntimePoint3::from_ints(0, 0, 0),
        RuntimePoint3::from_ints(1, 0, 0),
        RuntimePoint3::from_ints(1, 1, lift_z),
        RuntimePoint3::from_ints(0, 1, 0),
    ];
    let noncoplanar_faces = vec![vec![0, 1, 2, 3], vec![0, 3, 2, 1]];
    Mesh::from_face_cycles(noncoplanar_vertices, &noncoplanar_faces)
        .expect("noncoplanar quad fixture should build")
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn build_concave_single_face_pair_mesh() -> Mesh {
    let vertices = vec![
        RuntimePoint3::from_ints(0, 0, 0),
        RuntimePoint3::from_ints(2, 0, 0),
        RuntimePoint3::from_ints(2, 2, 0),
        RuntimePoint3::from_ints(1, 1, 0),
        RuntimePoint3::from_ints(0, 2, 0),
    ];
    let faces = vec![vec![0, 1, 2, 3, 4], vec![0, 4, 3, 2, 1]];
    Mesh::from_face_cycles(vertices, &faces).expect("concave face-pair fixture should build")
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn build_reflected_cube_outward_failure_mesh() -> Mesh {
    let cube = Mesh::cube();
    transform_mesh_positions(&cube, |point| {
        let mirrored = reflect_point3_across_yz_plane(point);
        translate_point3(&mirrored, 11, 3, -5)
    })
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn build_collinear_single_triangle_pair_mesh() -> Mesh {
    let vertices = vec![
        RuntimePoint3::from_ints(0, 0, 0),
        RuntimePoint3::from_ints(1, 0, 0),
        RuntimePoint3::from_ints(2, 0, 0),
    ];
    let faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
    Mesh::from_face_cycles(vertices, &faces)
        .expect("collinear-corner fixture should build")
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
#[derive(Clone, Copy)]
enum Phase4SharedEdgeSpecGapFailure {
    CollinearCorner,
    NonCoplanar,
    NonConvex,
    ForbiddenIntersection,
    InwardOrDegenerate,
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn assert_phase4_shared_edge_spec_characterization_gap(
    mesh: &Mesh,
    label: &str,
    expected_failure: Phase4SharedEdgeSpecGapFailure,
) {
    assert!(mesh.is_valid(), "{label}: fixture should satisfy Phase 4 validity");
    assert!(
        mesh.check_shared_edge_local_orientation_consistency(),
        "{label}: fixture should satisfy shared-edge local orientation consistency"
    );
    assert!(
        runtime_check_phase4_valid_and_shared_edge_local_orientation_imply_geometric_topological_consistency_spec(mesh),
        "{label}: aggregate model spec still characterizes phase4 + shared-edge-local-orientation"
    );
    assert!(
        !mesh.check_geometric_topological_consistency(),
        "{label}: runtime aggregate checker should reject this geometric-failure fixture"
    );
    let diagnostic_failure = mesh
        .check_geometric_topological_consistency_diagnostic()
        .expect_err("diagnostic checker should reject fixture");
    assert!(
        !runtime_check_geometric_topological_consistency_sound_bridge(mesh),
        "{label}: aggregate sound bridge should reject this geometric-failure fixture"
    );

    let constructive = check_geometric_topological_consistency_constructive(mesh)
        .expect("constructive geometric gate should produce a witness");
    assert!(
        constructive.phase4_valid_ok,
        "{label}: constructive witness should retain phase4 validity"
    );
    assert!(
        constructive.shared_edge_local_orientation_ok,
        "{label}: constructive witness should retain shared-edge local orientation consistency"
    );
    assert!(
        !constructive.api_ok,
        "{label}: constructive aggregate witness should remain false"
    );

    match expected_failure {
        Phase4SharedEdgeSpecGapFailure::CollinearCorner => {
            assert!(
                mesh.check_no_zero_length_geometric_edges(),
                "{label}: fixture should keep zero-length geometric-edge check passing"
            );
            assert!(
                !mesh.check_face_corner_non_collinearity(),
                "{label}: fixture should fail face-corner non-collinearity"
            );
            assert!(
                matches!(
                    diagnostic_failure,
                    GeometricTopologicalConsistencyFailure::FaceCornerCollinear { .. }
                ),
                "{label}: first aggregate diagnostic failure should be face-corner collinearity"
            );
            assert!(
                constructive.no_zero_length_geometric_edges_ok,
                "{label}: constructive witness should retain zero-length geometric-edge pass"
            );
            assert!(
                !constructive.face_corner_non_collinearity_ok,
                "{label}: constructive witness should reject induced corner collinearity"
            );
            assert!(
                !constructive.face_coplanarity_ok,
                "{label}: constructive witness should reject induced coplanarity precondition failure"
            );
        },
        Phase4SharedEdgeSpecGapFailure::NonCoplanar => {
            assert!(
                !mesh.check_face_coplanarity(),
                "{label}: fixture should fail face coplanarity"
            );
            assert!(
                matches!(
                    diagnostic_failure,
                    GeometricTopologicalConsistencyFailure::FaceNonCoplanar { .. }
                ),
                "{label}: first aggregate diagnostic failure should be face non-coplanarity"
            );
            assert!(
                !runtime_check_face_coplanarity_seed0_fixed_witness_sound_bridge(mesh),
                "{label}: coplanarity sound bridge should reject non-coplanar fixture"
            );
            assert!(
                !constructive.face_coplanarity_ok,
                "{label}: constructive witness should reject non-coplanar faces"
            );
        },
        Phase4SharedEdgeSpecGapFailure::NonConvex => {
            assert!(
                mesh.check_face_coplanarity(),
                "{label}: fixture should pass coplanarity"
            );
            assert!(
                !mesh.check_face_convexity(),
                "{label}: fixture should fail face convexity"
            );
            assert!(
                matches!(
                    diagnostic_failure,
                    GeometricTopologicalConsistencyFailure::FaceNonConvex { .. }
                ),
                "{label}: first aggregate diagnostic failure should be face non-convexity"
            );
            assert!(
                runtime_check_face_coplanarity_seed0_fixed_witness_sound_bridge(mesh),
                "{label}: coplanarity sound bridge should pass convexity-only failure fixture"
            );
            assert!(
                constructive.face_coplanarity_ok,
                "{label}: constructive witness should retain coplanarity"
            );
            assert!(
                !constructive.face_convexity_ok,
                "{label}: constructive witness should reject non-convex faces"
            );
        },
        Phase4SharedEdgeSpecGapFailure::ForbiddenIntersection => {
            assert!(
                mesh.check_face_coplanarity(),
                "{label}: fixture should pass coplanarity"
            );
            assert!(
                mesh.check_face_convexity(),
                "{label}: fixture should pass convexity"
            );
            assert!(
                !mesh.check_no_forbidden_face_face_intersections(),
                "{label}: fixture should fail forbidden face-face intersection check"
            );
            assert!(
                matches!(
                    diagnostic_failure,
                    GeometricTopologicalConsistencyFailure::ForbiddenFaceFaceIntersection { .. }
                ),
                "{label}: first aggregate diagnostic failure should be forbidden face-face intersection"
            );
            assert!(
                runtime_check_face_coplanarity_seed0_fixed_witness_sound_bridge(mesh),
                "{label}: coplanarity sound bridge should pass intersection-only failure fixture"
            );
            assert!(
                constructive.face_coplanarity_ok,
                "{label}: constructive witness should retain coplanarity"
            );
            assert!(
                constructive.face_convexity_ok,
                "{label}: constructive witness should retain convexity"
            );
            assert!(
                !constructive.no_forbidden_face_face_intersections_ok,
                "{label}: constructive witness should reject forbidden face-face intersections"
            );
        },
        Phase4SharedEdgeSpecGapFailure::InwardOrDegenerate => {
            assert!(
                mesh.check_face_coplanarity(),
                "{label}: fixture should pass coplanarity"
            );
            assert!(
                mesh.check_face_convexity(),
                "{label}: fixture should pass convexity"
            );
            assert!(
                mesh.check_no_forbidden_face_face_intersections(),
                "{label}: fixture should pass forbidden face-face intersection check"
            );
            assert!(
                !mesh.check_outward_face_normals(),
                "{label}: fixture should fail outward-face-normal check"
            );
            assert!(
                matches!(
                    diagnostic_failure,
                    GeometricTopologicalConsistencyFailure::InwardOrDegenerateComponent { .. }
                ),
                "{label}: first aggregate diagnostic failure should be inward/degenerate component"
            );
            assert!(
                runtime_check_face_coplanarity_seed0_fixed_witness_sound_bridge(mesh),
                "{label}: coplanarity sound bridge should pass outward-only failure fixture"
            );
            assert!(
                constructive.face_coplanarity_ok,
                "{label}: constructive witness should retain coplanarity"
            );
            assert!(
                constructive.face_convexity_ok,
                "{label}: constructive witness should retain convexity"
            );
            assert!(
                constructive.no_forbidden_face_face_intersections_ok,
                "{label}: constructive witness should retain forbidden-intersection pass"
            );
            assert!(
                !constructive.outward_face_normals_ok,
                "{label}: constructive witness should reject outward orientation"
            );
        },
    }
}

#[cfg(feature = "geometry-checks")]
fn no_forbidden_face_face_intersections_pairwise_oracle(
    mesh: &Mesh,
    use_broad_phase: bool,
) -> Option<bool> {
    if !mesh.is_valid() {
        return Some(false);
    }
    if !mesh.check_face_convexity() {
        return Some(false);
    }

    for face_a in 0..mesh.faces.len() {
        for face_b in (face_a + 1)..mesh.faces.len() {
            let pair_forbidden = mesh.face_pair_has_forbidden_intersection_for_testing(
                face_a,
                face_b,
                use_broad_phase,
            )?;
            if pair_forbidden {
                return Some(false);
            }
        }
    }

    Some(true)
}

#[cfg(feature = "geometry-checks")]
fn assert_forbidden_face_face_checker_broad_phase_sound(mesh: &Mesh) {
    let broad_phase_result = mesh.check_no_forbidden_face_face_intersections();
    let no_cull_result =
        mesh.check_no_forbidden_face_face_intersections_without_broad_phase_for_testing();
    let broad_phase_pairwise_oracle =
        no_forbidden_face_face_intersections_pairwise_oracle(mesh, true)
            .expect("pairwise broad-phase oracle should produce an output");
    let no_cull_pairwise_oracle =
        no_forbidden_face_face_intersections_pairwise_oracle(mesh, false)
            .expect("pairwise no-cull oracle should produce an output");
    assert_eq!(
        broad_phase_result, broad_phase_pairwise_oracle,
        "broad-phase aggregate result diverged from explicit pairwise oracle"
    );
    assert_eq!(
        no_cull_result, no_cull_pairwise_oracle,
        "no-cull aggregate result diverged from explicit pairwise oracle"
    );
    assert_eq!(
        broad_phase_result, no_cull_result,
        "broad-phase culling changed the forbidden face-face intersection outcome"
    );
}

#[cfg(feature = "geometry-checks")]
fn ordered_face_vertex_cycle_indices(mesh: &Mesh, face_id: usize) -> Option<Vec<usize>> {
    if face_id >= mesh.faces.len() {
        return None;
    }
    let hcnt = mesh.half_edges.len();
    if hcnt == 0 {
        return None;
    }

    let start = mesh.faces[face_id].half_edge;
    if start >= hcnt {
        return None;
    }
    let mut h = start;
    let mut steps = 0usize;
    let mut out = Vec::new();
    loop {
        let he = mesh.half_edges.get(h)?;
        if he.vertex >= mesh.vertices.len() {
            return None;
        }
        out.push(he.vertex);
        h = he.next;
        steps += 1;
        if h == start {
            break;
        }
        if steps > hcnt {
            return None;
        }
    }
    if out.len() < 3 {
        return None;
    }
    Some(out)
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn mesh_all_faces_are_triangles(mesh: &Mesh) -> bool {
    for face_id in 0..mesh.faces.len() {
        let Some(cycle) = ordered_face_vertex_cycle_indices(mesh, face_id) else {
            return false;
        };
        if cycle.len() != 3 {
            return false;
        }
    }
    true
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn mesh_all_faces_are_quads(mesh: &Mesh) -> bool {
    for face_id in 0..mesh.faces.len() {
        let Some(cycle) = ordered_face_vertex_cycle_indices(mesh, face_id) else {
            return false;
        };
        if cycle.len() != 4 {
            return false;
        }
    }
    true
}

#[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
fn mesh_all_faces_are_triangles_or_quads(mesh: &Mesh) -> bool {
    for face_id in 0..mesh.faces.len() {
        let Some(cycle) = ordered_face_vertex_cycle_indices(mesh, face_id) else {
            return false;
        };
        if cycle.len() != 3 && cycle.len() != 4 {
            return false;
        }
    }
    true
}

#[cfg(feature = "geometry-checks")]
fn mesh_vertices_and_face_cycles_for_relabeling(
    mesh: &Mesh,
) -> Option<(Vec<RuntimePoint3>, Vec<Vec<usize>>)> {
    let vertices = mesh
        .vertices
        .iter()
        .map(|v| v.position.clone())
        .collect::<Vec<_>>();
    let mut faces = Vec::with_capacity(mesh.faces.len());
    for face_id in 0..mesh.faces.len() {
        faces.push(ordered_face_vertex_cycle_indices(mesh, face_id)?);
    }
    Some((vertices, faces))
}

#[cfg(feature = "geometry-checks")]
fn relabel_mesh_vertices_for_testing(mesh: &Mesh, old_to_new: &[usize]) -> Option<Mesh> {
    let (vertices, faces) = mesh_vertices_and_face_cycles_for_relabeling(mesh)?;
    let (relabeled_vertices, relabeled_faces) =
        relabel_vertices_in_face_cycles(&vertices, &faces, old_to_new);
    Mesh::from_face_cycles(relabeled_vertices, &relabeled_faces).ok()
}

#[cfg(feature = "geometry-checks")]
fn ordered_face_boundary_vertices_and_edge_indices(
    mesh: &Mesh,
    face_id: usize,
) -> Option<(Vec<usize>, Vec<usize>)> {
    if face_id >= mesh.faces.len() {
        return None;
    }
    let hcnt = mesh.half_edges.len();
    if hcnt == 0 {
        return None;
    }

    let start = mesh.faces[face_id].half_edge;
    if start >= hcnt {
        return None;
    }
    let mut h = start;
    let mut steps = 0usize;
    let mut vertices = Vec::new();
    let mut edges = Vec::new();
    loop {
        let he = mesh.half_edges.get(h)?;
        if he.face != face_id || he.vertex >= mesh.vertices.len() || he.edge >= mesh.edges.len() {
            return None;
        }
        vertices.push(he.vertex);
        if !edges.contains(&he.edge) {
            edges.push(he.edge);
        }

        h = he.next;
        steps += 1;
        if h == start {
            break;
        }
        if steps > hcnt {
            return None;
        }
    }

    if vertices.len() < 3 {
        return None;
    }
    Some((vertices, edges))
}

#[cfg(feature = "geometry-checks")]
fn face_pair_shared_boundary_counts_edge_index_oracle(
    mesh: &Mesh,
    face_a: usize,
    face_b: usize,
) -> Option<(usize, usize)> {
    if face_a >= mesh.faces.len() || face_b >= mesh.faces.len() || face_a == face_b {
        return None;
    }

    let (face_a_vertices, face_a_edges) =
        ordered_face_boundary_vertices_and_edge_indices(mesh, face_a)?;
    let (face_b_vertices, face_b_edges) =
        ordered_face_boundary_vertices_and_edge_indices(mesh, face_b)?;

    let mut shared_vertices = Vec::new();
    for vertex in face_a_vertices {
        if face_b_vertices.contains(&vertex) && !shared_vertices.contains(&vertex) {
            shared_vertices.push(vertex);
        }
    }

    let mut shared_edges = Vec::new();
    for edge in face_a_edges {
        if face_b_edges.contains(&edge) && !shared_edges.contains(&edge) {
            shared_edges.push(edge);
        }
    }

    Some((shared_vertices.len(), shared_edges.len()))
}

#[cfg(feature = "geometry-checks")]
fn face_pair_allowed_contact_topology_edge_index_oracle(
    mesh: &Mesh,
    face_a: usize,
    face_b: usize,
) -> Option<bool> {
    let (shared_vertices, shared_edges) =
        face_pair_shared_boundary_counts_edge_index_oracle(mesh, face_a, face_b)?;
    Some(if shared_edges == 0 {
        shared_vertices <= 1
    } else {
        shared_edges == 1 && shared_vertices == 2
    })
}

#[cfg(feature = "geometry-checks")]
fn assert_allowed_contact_topology_classifier_matches_edge_index_oracle(mesh: &Mesh) {
    for face_a in 0..mesh.faces.len() {
        for face_b in (face_a + 1)..mesh.faces.len() {
            let runtime = mesh
                .face_pair_has_allowed_contact_topology_for_testing(face_a, face_b)
                .expect("pair classifier should produce an output for valid face ids");
            let oracle = face_pair_allowed_contact_topology_edge_index_oracle(
                mesh, face_a, face_b,
            )
            .expect("oracle should produce an output for valid face ids");
            assert_eq!(
                runtime, oracle,
                "allowed-contact topology classifier mismatch on face pair ({face_a}, {face_b})"
            );
        }
    }
}

#[cfg(feature = "geometry-checks")]
fn assert_shared_edge_contacts_not_misclassified_as_forbidden_intersections(
    mesh: &Mesh,
    label: &str,
) {
    let mut saw_shared_edge_pair = false;
    for face_a in 0..mesh.faces.len() {
        for face_b in (face_a + 1)..mesh.faces.len() {
            let (shared_vertices, shared_edges) =
                face_pair_shared_boundary_counts_edge_index_oracle(mesh, face_a, face_b)
                    .expect("shared-boundary oracle should produce an output for valid face ids");
            if shared_edges != 1 || shared_vertices != 2 {
                continue;
            }
            saw_shared_edge_pair = true;

            let topology_allowed = mesh
                .face_pair_has_allowed_contact_topology_for_testing(face_a, face_b)
                .expect("pair classifier should produce an output for valid face ids");
            assert!(
                topology_allowed,
                "shared-edge pair ({face_a}, {face_b}) should satisfy allowed-contact topology for {label}"
            );

            let forbidden_no_cull = mesh
                .face_pair_has_forbidden_intersection_for_testing(face_a, face_b, false)
                .expect("pair forbidden-intersection hook should produce an output for valid face ids");
            let forbidden_with_cull = mesh
                .face_pair_has_forbidden_intersection_for_testing(face_a, face_b, true)
                .expect("pair forbidden-intersection hook should produce an output for valid face ids");
            assert_eq!(
                forbidden_no_cull, forbidden_with_cull,
                "broad-phase culling changed pair classification for shared-edge pair ({face_a}, {face_b}) in {label}"
            );
            assert!(
                !forbidden_no_cull,
                "shared-edge pair ({face_a}, {face_b}) was misclassified as forbidden in {label}"
            );
        }
    }
    assert!(
        saw_shared_edge_pair,
        "fixture {label} should include at least one shared-edge face pair"
    );
}

#[cfg(feature = "geometry-checks")]
fn assert_shared_vertex_only_contacts_not_misclassified_as_forbidden_intersections(
    mesh: &Mesh,
    label: &str,
) {
    let mut saw_shared_vertex_only_pair = false;
    for face_a in 0..mesh.faces.len() {
        for face_b in (face_a + 1)..mesh.faces.len() {
            let (shared_vertices, shared_edges) =
                face_pair_shared_boundary_counts_edge_index_oracle(mesh, face_a, face_b)
                    .expect("shared-boundary oracle should produce an output for valid face ids");
            if shared_edges != 0 || shared_vertices != 1 {
                continue;
            }
            saw_shared_vertex_only_pair = true;

            let topology_allowed = mesh
                .face_pair_has_allowed_contact_topology_for_testing(face_a, face_b)
                .expect("pair classifier should produce an output for valid face ids");
            assert!(
                topology_allowed,
                "shared-vertex-only pair ({face_a}, {face_b}) should satisfy allowed-contact topology for {label}"
            );

            let forbidden_no_cull = mesh
                .face_pair_has_forbidden_intersection_for_testing(face_a, face_b, false)
                .expect("pair forbidden-intersection hook should produce an output for valid face ids");
            let forbidden_with_cull = mesh
                .face_pair_has_forbidden_intersection_for_testing(face_a, face_b, true)
                .expect("pair forbidden-intersection hook should produce an output for valid face ids");
            assert_eq!(
                forbidden_no_cull, forbidden_with_cull,
                "broad-phase culling changed pair classification for shared-vertex-only pair ({face_a}, {face_b}) in {label}"
            );
            assert!(
                !forbidden_no_cull,
                "shared-vertex-only pair ({face_a}, {face_b}) was misclassified as forbidden in {label}"
            );
        }
    }
    assert!(
        saw_shared_vertex_only_pair,
        "fixture {label} should include at least one shared-vertex-only face pair"
    );
}

#[cfg(feature = "geometry-checks")]
fn assert_non_allowed_contact_topology_pairs_are_forbidden(mesh: &Mesh, label: &str) {
    let mut saw_non_allowed_pair = false;
    for face_a in 0..mesh.faces.len() {
        for face_b in (face_a + 1)..mesh.faces.len() {
            let topology_allowed = mesh
                .face_pair_has_allowed_contact_topology_for_testing(face_a, face_b)
                .expect("pair classifier should produce an output for valid face ids");
            if topology_allowed {
                continue;
            }

            saw_non_allowed_pair = true;
            let forbidden_no_cull = mesh
                .face_pair_has_forbidden_intersection_for_testing(face_a, face_b, false)
                .expect("pair forbidden-intersection hook should produce an output for valid face ids");
            let forbidden_with_cull = mesh
                .face_pair_has_forbidden_intersection_for_testing(face_a, face_b, true)
                .expect("pair forbidden-intersection hook should produce an output for valid face ids");

            assert_eq!(
                forbidden_no_cull, forbidden_with_cull,
                "broad-phase culling changed pair classification for non-allowed-topology pair ({face_a}, {face_b}) in {label}"
            );
            assert!(
                forbidden_no_cull,
                "non-allowed-topology pair ({face_a}, {face_b}) should be classified as forbidden in {label}"
            );
        }
    }

    assert!(
        saw_non_allowed_pair,
        "fixture {label} should include at least one non-allowed-topology face pair"
    );
}

#[cfg(feature = "geometry-checks")]
fn check_face_coplanarity_exhaustive_face_quadruple_oracle(mesh: &Mesh) -> bool {
    if !mesh.is_valid() {
        return false;
    }
    if !mesh.check_face_corner_non_collinearity() {
        return false;
    }

    for face_id in 0..mesh.faces.len() {
        let cycle = match ordered_face_vertex_cycle_indices(mesh, face_id) {
            Some(cycle) => cycle,
            None => return false,
        };
        let k = cycle.len();
        for i in 0..k {
            let a = &mesh.vertices[cycle[i]].position;
            for j in 0..k {
                let b = &mesh.vertices[cycle[j]].position;
                for l in 0..k {
                    let c = &mesh.vertices[cycle[l]].position;
                    for d in 0..k {
                        let p = &mesh.vertices[cycle[d]].position;
                        if !coplanar(a, b, c, p) {
                            return false;
                        }
                    }
                }
            }
        }
    }
    true
}

#[cfg(feature = "geometry-checks")]
fn assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(mesh: &Mesh, label: &str) {
    let checker_result = mesh.check_face_coplanarity();
    let oracle_result = check_face_coplanarity_exhaustive_face_quadruple_oracle(mesh);
    assert_eq!(
        checker_result, oracle_result,
        "face coplanarity checker diverged from exhaustive face-quadruple oracle for {label}"
    );

    #[cfg(feature = "verus-proofs")]
    {
        assert_face_coplanarity_runtime_seed0_bridge_parity(mesh, label);
        assert_face_coplanarity_runtime_seed0_sound_bridge_parity(mesh, label);
        assert_face_coplanarity_seed0_phase5_runtime_bundle_completeness_bridge_parity(mesh, label);
    }
}

#[cfg(feature = "geometry-checks")]
fn face_projection_axis_from_reference_normal(normal: &RuntimeVec3) -> Option<usize> {
    if normal.x().signum_i8() != 0 {
        Some(0)
    } else if normal.y().signum_i8() != 0 {
        Some(1)
    } else if normal.z().signum_i8() != 0 {
        Some(2)
    } else {
        None
    }
}

#[cfg(feature = "geometry-checks")]
fn project_point3_to_2d_for_face_axis(point: &RuntimePoint3, axis: usize) -> RuntimePoint2 {
    if axis == 0 {
        RuntimePoint2::new(point.y().clone(), point.z().clone())
    } else if axis == 1 {
        RuntimePoint2::new(point.x().clone(), point.z().clone())
    } else {
        RuntimePoint2::new(point.x().clone(), point.y().clone())
    }
}

#[cfg(feature = "geometry-checks")]
fn check_face_convexity_projected_orient2d_oracle(mesh: &Mesh) -> bool {
    if !mesh.is_valid() {
        return false;
    }
    if !mesh.check_face_coplanarity() || !mesh.check_face_corner_non_collinearity() {
        return false;
    }

    for face_id in 0..mesh.faces.len() {
        let cycle = match ordered_face_vertex_cycle_indices(mesh, face_id) {
            Some(cycle) => cycle,
            None => return false,
        };
        let k = cycle.len();
        if k < 3 {
            return false;
        }

        let p0 = &mesh.vertices[cycle[0]].position;
        let p1 = &mesh.vertices[cycle[1]].position;
        let p2 = &mesh.vertices[cycle[2]].position;
        let e01 = p1.sub(p0);
        let e12 = p2.sub(p1);
        let reference_normal = e01.cross(&e12);
        let axis = match face_projection_axis_from_reference_normal(&reference_normal) {
            Some(axis) => axis,
            None => return false,
        };

        let mut expected_turn_sign = 0i8;
        for i in 0..k {
            let prev_i = if i == 0 { k - 1 } else { i - 1 };
            let next_i = if i + 1 < k { i + 1 } else { 0 };

            let prev = &mesh.vertices[cycle[prev_i]].position;
            let curr = &mesh.vertices[cycle[i]].position;
            let next = &mesh.vertices[cycle[next_i]].position;

            let prev_2d = project_point3_to_2d_for_face_axis(prev, axis);
            let curr_2d = project_point3_to_2d_for_face_axis(curr, axis);
            let next_2d = project_point3_to_2d_for_face_axis(next, axis);
            let turn_sign = orient2d_sign(&prev_2d, &curr_2d, &next_2d);
            if turn_sign == 0 {
                return false;
            }
            if expected_turn_sign == 0 {
                expected_turn_sign = turn_sign;
            } else if turn_sign != expected_turn_sign {
                return false;
            }
        }
    }
    true
}

#[cfg(feature = "geometry-checks")]
fn assert_face_convexity_checker_matches_projected_orient2d_oracle(mesh: &Mesh, label: &str) {
    let checker_result = mesh.check_face_convexity();
    let oracle_result = check_face_convexity_projected_orient2d_oracle(mesh);
    assert_eq!(
        checker_result, oracle_result,
        "face convexity checker diverged from projected orient2d-sign oracle for {label}"
    );
}

#[cfg(feature = "geometry-checks")]
fn build_overlapping_tetrahedra_mesh() -> Mesh {
    let vertices = vec![
        RuntimePoint3::from_ints(0, 0, 0),
        RuntimePoint3::from_ints(4, 0, 0),
        RuntimePoint3::from_ints(0, 4, 0),
        RuntimePoint3::from_ints(0, 0, 4),
        RuntimePoint3::from_ints(1, 1, 1),
        RuntimePoint3::from_ints(5, 1, 1),
        RuntimePoint3::from_ints(1, 5, 1),
        RuntimePoint3::from_ints(1, 1, 5),
    ];
    let faces = vec![
        vec![0, 1, 2],
        vec![0, 3, 1],
        vec![1, 3, 2],
        vec![2, 3, 0],
        vec![4, 5, 6],
        vec![4, 7, 5],
        vec![5, 7, 6],
        vec![6, 7, 4],
    ];
    Mesh::from_face_cycles(vertices, &faces).expect("overlapping tetrahedra fixture should build")
}

#[cfg(feature = "geometry-checks")]
fn build_octahedron_mesh() -> Mesh {
    let vertices = vec![
        RuntimePoint3::from_ints(0, 0, 1),
        RuntimePoint3::from_ints(0, 0, -1),
        RuntimePoint3::from_ints(1, 0, 0),
        RuntimePoint3::from_ints(0, 1, 0),
        RuntimePoint3::from_ints(-1, 0, 0),
        RuntimePoint3::from_ints(0, -1, 0),
    ];
    let faces = vec![
        vec![0, 3, 2],
        vec![0, 4, 3],
        vec![0, 5, 4],
        vec![0, 2, 5],
        vec![1, 2, 3],
        vec![1, 3, 4],
        vec![1, 4, 5],
        vec![1, 5, 2],
    ];
    Mesh::from_face_cycles(vertices, &faces).expect("octahedron fixture should build")
}

#[cfg(feature = "geometry-checks")]
fn transform_mesh_positions<F>(mesh: &Mesh, transform: F) -> Mesh
where
    F: Fn(&RuntimePoint3) -> RuntimePoint3,
{
    let mut out = mesh.clone();
    for vertex in &mut out.vertices {
        vertex.position = transform(&vertex.position);
    }
    out
}

#[cfg(feature = "geometry-checks")]
fn translate_point3(point: &RuntimePoint3, tx: i64, ty: i64, tz: i64) -> RuntimePoint3 {
    point.add_vec(&RuntimeVec3::from_ints(tx, ty, tz))
}

#[cfg(feature = "geometry-checks")]
fn rotate_point3_z_90(point: &RuntimePoint3) -> RuntimePoint3 {
    RuntimePoint3::new(point.y().neg(), point.x().clone(), point.z().clone())
}

#[cfg(feature = "geometry-checks")]
fn rigid_rotate_z_90_then_translate(point: &RuntimePoint3, tx: i64, ty: i64, tz: i64) -> RuntimePoint3 {
    let rotated = rotate_point3_z_90(point);
    translate_point3(&rotated, tx, ty, tz)
}

#[cfg(feature = "geometry-checks")]
fn reflect_point3_across_yz_plane(point: &RuntimePoint3) -> RuntimePoint3 {
    RuntimePoint3::new(point.x().neg(), point.y().clone(), point.z().clone())
}

#[cfg(feature = "geometry-checks")]
#[derive(Clone, Copy)]
struct DeterministicRng {
    state: u64,
}

#[cfg(feature = "geometry-checks")]
impl DeterministicRng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn next_usize_inclusive(&mut self, min: usize, max: usize) -> usize {
        assert!(min <= max, "min must be <= max");
        let span = (max - min + 1) as u64;
        min + (self.next_u64() % span) as usize
    }

    fn next_i64_inclusive(&mut self, min: i64, max: i64) -> i64 {
        assert!(min <= max, "min must be <= max");
        let span = (max - min + 1) as u64;
        min + (self.next_u64() % span) as i64
    }
}

#[cfg(feature = "geometry-checks")]
fn rotate_point3_z_quarter_turns(point: &RuntimePoint3, quarter_turns: u64) -> RuntimePoint3 {
    let mut out = point.clone();
    for _ in 0..(quarter_turns % 4) {
        out = rotate_point3_z_90(&out);
    }
    out
}

#[cfg(feature = "geometry-checks")]
fn rigid_rotate_z_quarter_turns_then_translate(
    point: &RuntimePoint3,
    quarter_turns: u64,
    tx: i64,
    ty: i64,
    tz: i64,
) -> RuntimePoint3 {
    let rotated = rotate_point3_z_quarter_turns(point, quarter_turns);
    translate_point3(&rotated, tx, ty, tz)
}

#[cfg(feature = "geometry-checks")]
fn random_well_separated_component_origins(
    rng: &mut DeterministicRng,
    components: usize,
) -> Vec<(i64, i64, i64)> {
    let mut origins = Vec::with_capacity(components);
    while origins.len() < components {
        let candidate = (
            rng.next_i64_inclusive(-20, 20) * 6,
            rng.next_i64_inclusive(-20, 20) * 6,
            rng.next_i64_inclusive(-20, 20) * 6,
        );
        if !origins.contains(&candidate) {
            origins.push(candidate);
        }
    }
    origins
}

#[cfg(feature = "geometry-checks")]
fn pick_distinct_indices(rng: &mut DeterministicRng, len: usize) -> (usize, usize) {
    assert!(len >= 2, "need at least two indices");
    let first = rng.next_usize_inclusive(0, len - 1);
    let mut second = rng.next_usize_inclusive(0, len - 2);
    if second >= first {
        second += 1;
    }
    (first, second)
}

#[cfg(feature = "geometry-checks")]
fn random_permutation(rng: &mut DeterministicRng, len: usize) -> Vec<usize> {
    let mut out: Vec<usize> = (0..len).collect();
    if len < 2 {
        return out;
    }
    let mut i = len - 1;
    while i > 0 {
        let j = rng.next_usize_inclusive(0, i);
        out.swap(i, j);
        i -= 1;
    }
    out
}

#[cfg(feature = "geometry-checks")]
fn relabel_vertices_in_face_cycles(
    vertices: &[RuntimePoint3],
    faces: &[Vec<usize>],
    old_to_new: &[usize],
) -> (Vec<RuntimePoint3>, Vec<Vec<usize>>) {
    assert_eq!(
        vertices.len(),
        old_to_new.len(),
        "old_to_new must map every old vertex index exactly once"
    );

    let mut seen = vec![false; vertices.len()];
    for &new_idx in old_to_new {
        assert!(
            new_idx < vertices.len(),
            "old_to_new contains out-of-bounds new vertex index"
        );
        assert!(!seen[new_idx], "old_to_new must be a bijection");
        seen[new_idx] = true;
    }
    assert!(
        seen.into_iter().all(|visited| visited),
        "old_to_new must assign each new index exactly once"
    );

    let mut relabeled_vertices = vertices.to_vec();
    for (old_idx, &new_idx) in old_to_new.iter().enumerate() {
        relabeled_vertices[new_idx] = vertices[old_idx].clone();
    }

    let relabeled_faces = faces
        .iter()
        .map(|cycle| cycle.iter().map(|&v| old_to_new[v]).collect())
        .collect();
    (relabeled_vertices, relabeled_faces)
}

#[cfg(feature = "geometry-checks")]
fn face_cycle_contains_half_edge(mesh: &Mesh, face: usize, target_half_edge: usize) -> bool {
    if face >= mesh.faces.len() || target_half_edge >= mesh.half_edges.len() {
        return false;
    }

    let start = mesh.faces[face].half_edge;
    let hcnt = mesh.half_edges.len();
    let mut h = start;
    let mut steps = 0usize;
    loop {
        if h == target_half_edge {
            return true;
        }

        h = mesh.half_edges[h].next;
        steps += 1;
        if h == start {
            break;
        }
        if steps > hcnt {
            return false;
        }
    }

    false
}

#[cfg(feature = "geometry-checks")]
fn component_signed_volume_six_from_start_half_edge_relative_to_reference(
    mesh: &Mesh,
    start_half_edge: usize,
    reference: &RuntimePoint3,
) -> RuntimeScalar {
    if start_half_edge >= mesh.half_edges.len() {
        return RuntimeScalar::from_int(0);
    }

    fn face_signed_volume_six_relative_to_reference(
        mesh: &Mesh,
        face_id: usize,
        reference: &RuntimePoint3,
    ) -> RuntimeScalar {
        if face_id >= mesh.faces.len() {
            return RuntimeScalar::from_int(0);
        }
        let hcnt = mesh.half_edges.len();
        if hcnt == 0 {
            return RuntimeScalar::from_int(0);
        }

        let h0 = mesh.faces[face_id].half_edge;
        if h0 >= hcnt {
            return RuntimeScalar::from_int(0);
        }
        let h0_next = mesh.half_edges[h0].next;
        if h0_next >= hcnt {
            return RuntimeScalar::from_int(0);
        }
        let hi0 = h0_next;
        let hj0 = mesh.half_edges[hi0].next;
        if hj0 >= hcnt {
            return RuntimeScalar::from_int(0);
        }

        let p0_vid = mesh.half_edges[h0].vertex;
        if p0_vid >= mesh.vertices.len() {
            return RuntimeScalar::from_int(0);
        }
        let p0 = &mesh.vertices[p0_vid].position;

        let mut hi = hi0;
        let mut hj = hj0;
        let mut steps = 0usize;
        let mut sum = RuntimeScalar::from_int(0);
        while hj != h0 {
            if hi >= hcnt || hj >= hcnt {
                return RuntimeScalar::from_int(0);
            }
            let pi_vid = mesh.half_edges[hi].vertex;
            let pj_vid = mesh.half_edges[hj].vertex;
            if pi_vid >= mesh.vertices.len() || pj_vid >= mesh.vertices.len() {
                return RuntimeScalar::from_int(0);
            }
            let pi = &mesh.vertices[pi_vid].position;
            let pj = &mesh.vertices[pj_vid].position;
            let det = orient3d_value(reference, p0, pi, pj);
            sum = sum.add(&det);

            hi = hj;
            hj = mesh.half_edges[hj].next;
            steps += 1;
            if steps > hcnt {
                return RuntimeScalar::from_int(0);
            }
        }
        sum
    }

    let mut visited = vec![false; mesh.half_edges.len()];
    let mut queue = std::collections::VecDeque::new();
    let mut seen_faces = std::collections::HashSet::new();
    let mut signed_volume6 = RuntimeScalar::from_int(0);

    queue.push_back(start_half_edge);
    visited[start_half_edge] = true;

    while let Some(h) = queue.pop_front() {
        let he = &mesh.half_edges[h];
        if seen_faces.insert(he.face) {
            let face_volume6 = face_signed_volume_six_relative_to_reference(mesh, he.face, reference);
            signed_volume6 = signed_volume6.add(&face_volume6);
        }
        for n in [he.twin, he.next, he.prev] {
            if !visited[n] {
                visited[n] = true;
                queue.push_back(n);
            }
        }
    }

    signed_volume6
}

#[cfg(feature = "geometry-checks")]
fn component_signed_volume_six_from_start_half_edge(mesh: &Mesh, start_half_edge: usize) -> RuntimeScalar {
    let origin = RuntimePoint3::from_ints(0, 0, 0);
    component_signed_volume_six_from_start_half_edge_relative_to_reference(
        mesh,
        start_half_edge,
        &origin,
    )
}

#[cfg(feature = "geometry-checks")]
fn component_start_half_edges(mesh: &Mesh) -> Vec<usize> {
    let hcnt = mesh.half_edges.len();
    let mut starts = Vec::new();
    if hcnt == 0 {
        return starts;
    }

    let mut visited = vec![false; hcnt];
    for start in 0..hcnt {
        if visited[start] {
            continue;
        }

        starts.push(start);
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(start);
        visited[start] = true;

        while let Some(h) = queue.pop_front() {
            let he = &mesh.half_edges[h];
            for n in [he.twin, he.next, he.prev] {
                if !visited[n] {
                    visited[n] = true;
                    queue.push_back(n);
                }
            }
        }
    }

    starts
}

#[cfg(feature = "geometry-checks")]
fn component_faces_and_vertices_from_start_half_edge(
    mesh: &Mesh,
    start_half_edge: usize,
) -> Option<(Vec<usize>, Vec<usize>)> {
    if start_half_edge >= mesh.half_edges.len() {
        return None;
    }

    let mut queue = std::collections::VecDeque::new();
    let mut visited = vec![false; mesh.half_edges.len()];
    let mut face_seen = vec![false; mesh.faces.len()];
    let mut vertex_seen = vec![false; mesh.vertices.len()];
    let mut faces = Vec::new();
    let mut vertices = Vec::new();

    queue.push_back(start_half_edge);
    visited[start_half_edge] = true;

    while let Some(h) = queue.pop_front() {
        let he = mesh.half_edges.get(h)?;
        if he.face >= mesh.faces.len() || he.vertex >= mesh.vertices.len() {
            return None;
        }

        if !face_seen[he.face] {
            face_seen[he.face] = true;
            faces.push(he.face);
        }
        if !vertex_seen[he.vertex] {
            vertex_seen[he.vertex] = true;
            vertices.push(he.vertex);
        }

        for n in [he.twin, he.next, he.prev] {
            if n >= mesh.half_edges.len() {
                return None;
            }
            if !visited[n] {
                visited[n] = true;
                queue.push_back(n);
            }
        }
    }

    Some((faces, vertices))
}

#[cfg(feature = "geometry-checks")]
fn sum_mesh_vertex_positions(mesh: &Mesh, vertex_indices: &[usize]) -> Option<RuntimePoint3> {
    let mut sum_x = RuntimeScalar::from_int(0);
    let mut sum_y = RuntimeScalar::from_int(0);
    let mut sum_z = RuntimeScalar::from_int(0);

    for &v in vertex_indices {
        let point = &mesh.vertices.get(v)?.position;
        sum_x = sum_x.add(point.x());
        sum_y = sum_y.add(point.y());
        sum_z = sum_z.add(point.z());
    }

    Some(RuntimePoint3::new(sum_x, sum_y, sum_z))
}

#[cfg(feature = "geometry-checks")]
fn scale_point3_by_usize(point: &RuntimePoint3, factor: usize) -> RuntimePoint3 {
    let factor_i64 = i64::try_from(factor).expect("point scaling factor should fit in i64");
    let factor_scalar = RuntimeScalar::from_int(factor_i64);
    RuntimePoint3::new(
        point.x().mul(&factor_scalar),
        point.y().mul(&factor_scalar),
        point.z().mul(&factor_scalar),
    )
}

#[cfg(feature = "geometry-checks")]
fn assert_signed_volume_component_sign_matches_per_face_normal_alignment(
    mesh: &Mesh,
    references: &[RuntimePoint3],
    label: &str,
) {
    assert!(!references.is_empty(), "at least one reference point is required");

    let component_starts = component_start_half_edges(mesh);
    assert!(
        !component_starts.is_empty(),
        "fixture {label} should expose at least one connected component"
    );

    for start_half_edge in component_starts {
        let (component_faces, component_vertices) =
            component_faces_and_vertices_from_start_half_edge(mesh, start_half_edge).expect(
                "component face/vertex extraction should succeed for valid geometric fixtures",
            );
        assert!(
            !component_faces.is_empty() && !component_vertices.is_empty(),
            "component extraction produced an empty face/vertex set in {label}"
        );

        let component_vertex_sum = sum_mesh_vertex_positions(mesh, &component_vertices)
            .expect("component vertex-index sums should be in bounds");
        let mut component_signed_volume_sign = None;
        for reference in references {
            let sign = component_signed_volume_six_from_start_half_edge_relative_to_reference(
                mesh,
                start_half_edge,
                reference,
            )
            .signum_i8();
            assert_ne!(
                sign, 0,
                "component signed volume should be non-zero in {label} (start half-edge {start_half_edge})"
            );
            if let Some(expected) = component_signed_volume_sign {
                assert_eq!(
                    sign, expected,
                    "component signed-volume sign changed under reference shift in {label} (start half-edge {start_half_edge})"
                );
            } else {
                component_signed_volume_sign = Some(sign);
            }
        }
        let component_sign = component_signed_volume_sign.expect(
            "component signed-volume sign should be established from at least one reference point",
        );

        for face_id in component_faces {
            let face_cycle = ordered_face_vertex_cycle_indices(mesh, face_id)
                .expect("component face cycle should be available for valid geometric fixtures");
            let face_vertex_sum = sum_mesh_vertex_positions(mesh, &face_cycle)
                .expect("face vertex-index sums should be in bounds");
            let scaled_face_sum = scale_point3_by_usize(&face_vertex_sum, component_vertices.len());
            let scaled_component_sum =
                scale_point3_by_usize(&component_vertex_sum, face_cycle.len());
            let centroid_direction = scaled_face_sum.sub(&scaled_component_sum);

            let (normal, _) = mesh.compute_face_plane(face_id).expect(
                "face-plane computation should succeed for valid geometric fixtures in this oracle",
            );
            let alignment_sign = normal.dot(&centroid_direction).signum_i8();
            assert_ne!(
                alignment_sign, 0,
                "per-face normal alignment should be non-zero in {label} (component start {start_half_edge}, face {face_id})"
            );
            assert_eq!(
                alignment_sign, component_sign,
                "per-face normal alignment diverged from component signed-volume sign in {label} (component start {start_half_edge}, face {face_id})"
            );
        }
    }
}

#[cfg(feature = "geometry-checks")]
fn assert_component_signed_volume_reference_invariance(
    mesh: &Mesh,
    references: &[RuntimePoint3],
) {
    assert!(
        !references.is_empty(),
        "at least one reference point is required for invariance checks"
    );
    let component_starts = component_start_half_edges(mesh);
    assert!(
        !component_starts.is_empty(),
        "mesh should expose at least one connected component"
    );

    for start in component_starts {
        let baseline = component_signed_volume_six_from_start_half_edge_relative_to_reference(
            mesh,
            start,
            &references[0],
        );
        for reference in references.iter().skip(1) {
            let candidate = component_signed_volume_six_from_start_half_edge_relative_to_reference(
                mesh,
                start,
                reference,
            );
            assert_eq!(
                candidate.sub(&baseline).signum_i8(),
                0,
                "component signed volume changed under reference-point shift"
            );
        }
    }
}

#[cfg(feature = "geometry-checks")]
fn assert_component_signed_volume_reference_invariance_with_expected_sign(
    mesh: &Mesh,
    references: &[RuntimePoint3],
    expected_sign: i8,
    label: &str,
) {
    assert!(
        expected_sign == -1 || expected_sign == 1,
        "expected sign must be -1 or +1"
    );
    assert_component_signed_volume_reference_invariance(mesh, references);

    let component_starts = component_start_half_edges(mesh);
    assert!(
        !component_starts.is_empty(),
        "fixture {label} should expose at least one connected component"
    );
    for start in component_starts {
        let baseline = component_signed_volume_six_from_start_half_edge_relative_to_reference(
            mesh,
            start,
            &references[0],
        );
        assert_eq!(
            baseline.signum_i8(),
            expected_sign,
            "unexpected signed-volume orientation sign for {label}"
        );
    }
}

#[cfg(feature = "geometry-checks")]
fn assert_outward_face_normals_checker_reference_invariance(
    mesh: &Mesh,
    references: &[RuntimePoint3],
) {
    assert!(
        !references.is_empty(),
        "at least one reference point is required for checker invariance checks"
    );
    let baseline = mesh.check_outward_face_normals();
    for reference in references {
        let candidate = mesh.check_outward_face_normals_relative_to_reference_for_testing(reference);
        assert_eq!(
            candidate, baseline,
            "outward-face-normal checker changed under reference-point shift"
        );
    }
}

#[cfg(feature = "geometry-checks")]
fn diagnostic_witness_is_real_counterexample(
    mesh: &Mesh,
    failure: &GeometricTopologicalConsistencyFailure,
) -> bool {
    fn point_plane_value_relative_to_origin(
        normal: &RuntimeVec3,
        offset: &RuntimeScalar,
        point: &RuntimePoint3,
    ) -> RuntimeScalar {
        let origin = RuntimePoint3::from_ints(0, 0, 0);
        normal.dot(&point.sub(&origin)).sub(offset)
    }

    fn ordered_face_vertex_cycle(mesh: &Mesh, face_id: usize) -> Option<Vec<usize>> {
        if face_id >= mesh.faces.len() {
            return None;
        }
        let hcnt = mesh.half_edges.len();
        if hcnt == 0 {
            return None;
        }

        let start = mesh.faces[face_id].half_edge;
        if start >= hcnt {
            return None;
        }
        let mut h = start;
        let mut steps = 0usize;
        let mut out = Vec::new();
        loop {
            let he = mesh.half_edges.get(h)?;
            if he.vertex >= mesh.vertices.len() {
                return None;
            }
            out.push(he.vertex);
            h = he.next;
            steps += 1;
            if h == start {
                break;
            }
            if steps > hcnt {
                return None;
            }
        }
        if out.len() < 3 {
            return None;
        }
        Some(out)
    }

    match failure {
        GeometricTopologicalConsistencyFailure::Phase4Validity => !mesh.is_valid(),
        GeometricTopologicalConsistencyFailure::InternalInconsistency => false,
        GeometricTopologicalConsistencyFailure::ZeroLengthGeometricEdge {
            half_edge,
            from_vertex,
            to_vertex,
        } => {
            if *half_edge >= mesh.half_edges.len()
                || *from_vertex >= mesh.vertices.len()
                || *to_vertex >= mesh.vertices.len()
            {
                return false;
            }
            let he = &mesh.half_edges[*half_edge];
            if he.vertex != *from_vertex {
                return false;
            }
            let to = mesh.half_edges[he.next].vertex;
            to == *to_vertex && mesh.vertices[*from_vertex].position == mesh.vertices[*to_vertex].position
        }
        GeometricTopologicalConsistencyFailure::FaceCornerCollinear { face, half_edge } => {
            if !face_cycle_contains_half_edge(mesh, *face, *half_edge) {
                return false;
            }
            let he = &mesh.half_edges[*half_edge];
            if he.face != *face {
                return false;
            }
            let prev = &mesh.half_edges[he.prev];
            let next = &mesh.half_edges[he.next];
            let a = &mesh.vertices[prev.vertex].position;
            let b = &mesh.vertices[he.vertex].position;
            let c = &mesh.vertices[next.vertex].position;
            collinear3d(a, b, c)
        }
        GeometricTopologicalConsistencyFailure::FaceNonCoplanar { face, half_edge } => {
            if !face_cycle_contains_half_edge(mesh, *face, *half_edge) {
                return false;
            }
            let h0 = mesh.faces[*face].half_edge;
            let h1 = mesh.half_edges[h0].next;
            let h2 = mesh.half_edges[h1].next;
            let a = &mesh.vertices[mesh.half_edges[h0].vertex].position;
            let b = &mesh.vertices[mesh.half_edges[h1].vertex].position;
            let c = &mesh.vertices[mesh.half_edges[h2].vertex].position;
            let d = &mesh.vertices[mesh.half_edges[*half_edge].vertex].position;
            !coplanar(a, b, c, d)
        }
        GeometricTopologicalConsistencyFailure::FaceNonConvex { face, half_edge } => {
            if !face_cycle_contains_half_edge(mesh, *face, *half_edge) {
                return false;
            }

            let hcnt = mesh.half_edges.len();
            let h0 = mesh.faces[*face].half_edge;
            let h1 = mesh.half_edges[h0].next;
            let h2 = mesh.half_edges[h1].next;
            let p0 = &mesh.vertices[mesh.half_edges[h0].vertex].position;
            let p1 = &mesh.vertices[mesh.half_edges[h1].vertex].position;
            let p2 = &mesh.vertices[mesh.half_edges[h2].vertex].position;
            let e01 = p1.sub(p0);
            let e12 = p2.sub(p1);
            let reference_normal = e01.cross(&e12);
            let witness = p0.add_vec(&reference_normal);

            let mut expected_turn_sign = 0i8;
            let mut h = h0;
            let mut steps = 0usize;
            loop {
                let he = &mesh.half_edges[h];
                let prev = &mesh.half_edges[he.prev];
                let next = &mesh.half_edges[he.next];
                let a = &mesh.vertices[prev.vertex].position;
                let b = &mesh.vertices[he.vertex].position;
                let c = &mesh.vertices[next.vertex].position;
                let turn_sign = orient3d_sign(a, b, c, &witness);

                if h == *half_edge {
                    if turn_sign == 0 {
                        return true;
                    }
                    return expected_turn_sign != 0 && turn_sign != expected_turn_sign;
                }

                if turn_sign == 0 {
                    return false;
                }
                if expected_turn_sign == 0 {
                    expected_turn_sign = turn_sign;
                } else if turn_sign != expected_turn_sign {
                    return false;
                }

                h = he.next;
                steps += 1;
                if h == h0 {
                    break;
                }
                if steps > hcnt {
                    return false;
                }
            }

            false
        }
        GeometricTopologicalConsistencyFailure::FacePlaneInconsistent { face, half_edge } => {
            if !face_cycle_contains_half_edge(mesh, *face, *half_edge) {
                return false;
            }

            match mesh.compute_face_plane(*face) {
                None => *half_edge == mesh.faces[*face].half_edge,
                Some((normal, offset)) => {
                    let p = &mesh.vertices[mesh.half_edges[*half_edge].vertex].position;
                    point_plane_value_relative_to_origin(&normal, &offset, p).signum_i8() != 0
                }
            }
        }
        GeometricTopologicalConsistencyFailure::SharedEdgeOrientationInconsistent {
            half_edge,
            twin_half_edge,
        } => {
            if *half_edge >= mesh.half_edges.len() || *twin_half_edge >= mesh.half_edges.len() {
                return false;
            }
            let he = &mesh.half_edges[*half_edge];
            if he.twin != *twin_half_edge {
                return false;
            }
            let twin = &mesh.half_edges[*twin_half_edge];
            if he.face == twin.face {
                return true;
            }

            let he_start = he.vertex;
            let he_end = mesh.half_edges[he.next].vertex;
            let twin_start = twin.vertex;
            let twin_end = mesh.half_edges[twin.next].vertex;
            he_start != twin_end || he_end != twin_start
        }
        GeometricTopologicalConsistencyFailure::ForbiddenFaceFaceIntersection { face_a, face_b } => {
            if *face_a >= mesh.faces.len() || *face_b >= mesh.faces.len() || face_a == face_b {
                return false;
            }

            if ordered_face_vertex_cycle(mesh, *face_a).is_none()
                || ordered_face_vertex_cycle(mesh, *face_b).is_none()
            {
                return false;
            }

            if mesh.check_no_forbidden_face_face_intersections() {
                return false;
            }

            matches!(
                mesh.check_geometric_topological_consistency_diagnostic(),
                Err(
                    GeometricTopologicalConsistencyFailure::ForbiddenFaceFaceIntersection {
                        face_a: observed_a,
                        face_b: observed_b,
                    }
                ) if *face_a == observed_a && *face_b == observed_b
            )
        }
        GeometricTopologicalConsistencyFailure::InwardOrDegenerateComponent { start_half_edge } => {
            if *start_half_edge >= mesh.half_edges.len() {
                return false;
            }
            component_signed_volume_six_from_start_half_edge(mesh, *start_half_edge).signum_i8() >= 0
        }
    }
}

    #[test]
    fn tetrahedron_is_valid() {
        let mesh = Mesh::tetrahedron();
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        #[cfg(feature = "geometry-checks")]
        {
            assert!(mesh.check_no_zero_length_geometric_edges());
            assert!(mesh.check_face_corner_non_collinearity());
            assert!(mesh.check_face_coplanarity());
            assert!(mesh.check_face_convexity());
            assert!(mesh.check_face_plane_consistency());
            assert!(mesh.check_shared_edge_local_orientation_consistency());
            assert!(mesh.check_no_forbidden_face_face_intersections());
            assert!(mesh.check_outward_face_normals());
            assert!(mesh.check_geometric_topological_consistency());
            assert!(mesh.is_valid_with_geometry());
        }
        assert_eq!(mesh.vertices.len(), 4);
        assert_eq!(mesh.edges.len(), 6);
        assert_eq!(mesh.faces.len(), 4);
        assert_eq!(mesh.half_edges.len(), 12);
        assert_eq!(mesh.component_count(), 1);
        assert_eq!(mesh.euler_characteristics_per_component(), vec![2]);
    }

    #[test]
    fn cube_is_valid() {
        let mesh = Mesh::cube();
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        #[cfg(feature = "geometry-checks")]
        {
            assert!(mesh.check_no_zero_length_geometric_edges());
            assert!(mesh.check_face_corner_non_collinearity());
            assert!(mesh.check_face_coplanarity());
            assert!(mesh.check_face_convexity());
            assert!(mesh.check_face_plane_consistency());
            assert!(mesh.check_shared_edge_local_orientation_consistency());
            assert!(mesh.check_no_forbidden_face_face_intersections());
            assert!(mesh.check_outward_face_normals());
            assert!(mesh.check_geometric_topological_consistency());
            assert!(mesh.is_valid_with_geometry());
        }
        assert_eq!(mesh.vertices.len(), 8);
        assert_eq!(mesh.edges.len(), 12);
        assert_eq!(mesh.faces.len(), 6);
        assert_eq!(mesh.half_edges.len(), 24);
        assert_eq!(mesh.component_count(), 1);
        assert_eq!(mesh.euler_characteristics_per_component(), vec![2]);
    }

    #[test]
    fn triangular_prism_is_valid() {
        let mesh = Mesh::triangular_prism();
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        #[cfg(feature = "geometry-checks")]
        {
            assert!(mesh.check_no_zero_length_geometric_edges());
            assert!(mesh.check_face_corner_non_collinearity());
            assert!(mesh.check_face_coplanarity());
            assert!(mesh.check_face_convexity());
            assert!(mesh.check_face_plane_consistency());
            assert!(mesh.check_shared_edge_local_orientation_consistency());
            assert!(mesh.check_no_forbidden_face_face_intersections());
            assert!(mesh.check_outward_face_normals());
            assert!(mesh.check_geometric_topological_consistency());
            assert!(mesh.is_valid_with_geometry());
        }
        assert_eq!(mesh.vertices.len(), 6);
        assert_eq!(mesh.edges.len(), 9);
        assert_eq!(mesh.faces.len(), 5);
        assert_eq!(mesh.half_edges.len(), 18);
        assert_eq!(mesh.component_count(), 1);
        assert_eq!(mesh.euler_characteristics_per_component(), vec![2]);
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn phase5_checks_are_invariant_under_face_cycle_start_rotation() {
        let vertices = vec![
            RuntimePoint3::from_ints(-1, -1, -1),
            RuntimePoint3::from_ints(1, -1, -1),
            RuntimePoint3::from_ints(1, 1, -1),
            RuntimePoint3::from_ints(-1, 1, -1),
            RuntimePoint3::from_ints(-1, -1, 1),
            RuntimePoint3::from_ints(1, -1, 1),
            RuntimePoint3::from_ints(1, 1, 1),
            RuntimePoint3::from_ints(-1, 1, 1),
        ];
        let faces = vec![
            vec![0, 1, 2, 3],
            vec![4, 7, 6, 5],
            vec![0, 4, 5, 1],
            vec![3, 2, 6, 7],
            vec![0, 3, 7, 4],
            vec![1, 5, 6, 2],
        ];
        let rotated_faces: Vec<Vec<usize>> = faces
            .iter()
            .map(|cycle| {
                let mut rotated = cycle.clone();
                rotated.rotate_left(1);
                rotated
            })
            .collect();

        let original = Mesh::from_face_cycles(vertices.clone(), &faces)
            .expect("original cube cycle starts should build");
        let rotated = Mesh::from_face_cycles(vertices, &rotated_faces)
            .expect("rotated cube cycle starts should build");

        assert!(original.is_valid());
        assert!(rotated.is_valid());

        assert_eq!(
            original.check_no_zero_length_geometric_edges(),
            rotated.check_no_zero_length_geometric_edges()
        );
        assert_eq!(
            original.check_face_corner_non_collinearity(),
            rotated.check_face_corner_non_collinearity()
        );
        assert_eq!(original.check_face_coplanarity(), rotated.check_face_coplanarity());
        assert_eq!(original.check_face_convexity(), rotated.check_face_convexity());
        assert_eq!(
            original.check_face_plane_consistency(),
            rotated.check_face_plane_consistency()
        );
        for f in 0..original.faces.len() {
            assert_eq!(
                original.compute_face_plane_canonical(f),
                rotated.compute_face_plane_canonical(f)
            );
        }
        assert_eq!(
            original.check_shared_edge_local_orientation_consistency(),
            rotated.check_shared_edge_local_orientation_consistency()
        );
        assert_eq!(
            original.check_no_forbidden_face_face_intersections(),
            rotated.check_no_forbidden_face_face_intersections()
        );
        assert_eq!(
            original.check_outward_face_normals(),
            rotated.check_outward_face_normals()
        );
        assert_eq!(
            original.check_geometric_topological_consistency(),
            rotated.check_geometric_topological_consistency()
        );
        assert!(original.check_geometric_topological_consistency());
        assert!(rotated.check_geometric_topological_consistency());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn phase5_checks_are_invariant_under_face_iteration_order() {
        let vertices = vec![
            RuntimePoint3::from_ints(-1, -1, -1),
            RuntimePoint3::from_ints(1, -1, -1),
            RuntimePoint3::from_ints(1, 1, -1),
            RuntimePoint3::from_ints(-1, 1, -1),
            RuntimePoint3::from_ints(-1, -1, 1),
            RuntimePoint3::from_ints(1, -1, 1),
            RuntimePoint3::from_ints(1, 1, 1),
            RuntimePoint3::from_ints(-1, 1, 1),
        ];
        let faces = vec![
            vec![0, 1, 2, 3],
            vec![4, 7, 6, 5],
            vec![0, 4, 5, 1],
            vec![3, 2, 6, 7],
            vec![0, 3, 7, 4],
            vec![1, 5, 6, 2],
        ];
        let reordered_faces = vec![
            faces[3].clone(),
            faces[5].clone(),
            faces[0].clone(),
            faces[2].clone(),
            faces[4].clone(),
            faces[1].clone(),
        ];

        let original = Mesh::from_face_cycles(vertices.clone(), &faces)
            .expect("original face ordering should build");
        let reordered = Mesh::from_face_cycles(vertices, &reordered_faces)
            .expect("reordered face ordering should build");

        assert!(original.is_valid());
        assert!(reordered.is_valid());
        assert_eq!(
            phase5_checker_signature(&original),
            phase5_checker_signature(&reordered)
        );
        assert!(original.check_geometric_topological_consistency());
        assert!(reordered.check_geometric_topological_consistency());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn phase5_checks_are_invariant_under_consistent_vertex_index_relabeling() {
        let cube_vertices = vec![
            RuntimePoint3::from_ints(-1, -1, -1),
            RuntimePoint3::from_ints(1, -1, -1),
            RuntimePoint3::from_ints(1, 1, -1),
            RuntimePoint3::from_ints(-1, 1, -1),
            RuntimePoint3::from_ints(-1, -1, 1),
            RuntimePoint3::from_ints(1, -1, 1),
            RuntimePoint3::from_ints(1, 1, 1),
            RuntimePoint3::from_ints(-1, 1, 1),
        ];
        let cube_faces = vec![
            vec![0, 1, 2, 3],
            vec![4, 7, 6, 5],
            vec![0, 4, 5, 1],
            vec![3, 2, 6, 7],
            vec![0, 3, 7, 4],
            vec![1, 5, 6, 2],
        ];
        let cube_permutation = vec![7, 2, 5, 1, 6, 0, 3, 4];
        let (cube_relabeled_vertices, cube_relabeled_faces) =
            relabel_vertices_in_face_cycles(&cube_vertices, &cube_faces, &cube_permutation);

        let cube_original =
            Mesh::from_face_cycles(cube_vertices, &cube_faces).expect("original cube should build");
        let cube_relabeled = Mesh::from_face_cycles(cube_relabeled_vertices, &cube_relabeled_faces)
            .expect("vertex-relabeled cube should build");
        assert_eq!(
            phase5_checker_signature(&cube_original),
            phase5_checker_signature(&cube_relabeled)
        );
        assert!(cube_original.check_geometric_topological_consistency());
        assert!(cube_relabeled.check_geometric_topological_consistency());

        let intersecting_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(4, 0, 0),
            RuntimePoint3::from_ints(0, 4, 0),
            RuntimePoint3::from_ints(0, 0, 4),
            RuntimePoint3::from_ints(1, 1, 1),
            RuntimePoint3::from_ints(5, 1, 1),
            RuntimePoint3::from_ints(1, 5, 1),
            RuntimePoint3::from_ints(1, 1, 5),
        ];
        let intersecting_faces = vec![
            vec![0, 1, 2],
            vec![0, 3, 1],
            vec![1, 3, 2],
            vec![2, 3, 0],
            vec![4, 5, 6],
            vec![4, 7, 5],
            vec![5, 7, 6],
            vec![6, 7, 4],
        ];
        let intersecting_permutation = vec![3, 5, 7, 1, 0, 4, 2, 6];
        let (intersecting_relabeled_vertices, intersecting_relabeled_faces) =
            relabel_vertices_in_face_cycles(
                &intersecting_vertices,
                &intersecting_faces,
                &intersecting_permutation,
            );

        let intersecting_original = Mesh::from_face_cycles(intersecting_vertices, &intersecting_faces)
            .expect("original intersecting fixture should build");
        let intersecting_relabeled = Mesh::from_face_cycles(
            intersecting_relabeled_vertices,
            &intersecting_relabeled_faces,
        )
        .expect("vertex-relabeled intersecting fixture should build");
        assert_eq!(
            phase5_checker_signature(&intersecting_original),
            phase5_checker_signature(&intersecting_relabeled)
        );
        assert!(!intersecting_original.check_geometric_topological_consistency());
        assert!(!intersecting_relabeled.check_geometric_topological_consistency());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn phase5_checks_are_invariant_under_rigid_translation_and_rotation() {
        let cube_original = Mesh::cube();
        let cube_transformed = transform_mesh_positions(&cube_original, |point| {
            rigid_rotate_z_90_then_translate(point, 13, -7, 5)
        });

        assert!(cube_original.is_valid());
        assert!(cube_transformed.is_valid());
        assert_eq!(
            phase5_checker_signature(&cube_original),
            phase5_checker_signature(&cube_transformed)
        );
        assert!(cube_original.check_geometric_topological_consistency());
        assert!(cube_transformed.check_geometric_topological_consistency());

        let intersecting_original = build_overlapping_tetrahedra_mesh();
        let intersecting_transformed = transform_mesh_positions(&intersecting_original, |point| {
            rigid_rotate_z_90_then_translate(point, 13, -7, 5)
        });

        assert!(intersecting_original.is_valid());
        assert!(intersecting_transformed.is_valid());
        assert_eq!(
            phase5_checker_signature(&intersecting_original),
            phase5_checker_signature(&intersecting_transformed)
        );
        assert!(!intersecting_original.check_geometric_topological_consistency());
        assert!(!intersecting_transformed.check_geometric_topological_consistency());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn outward_face_normals_checker_is_reference_origin_invariant() {
        let references = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(11, -7, 5),
            RuntimePoint3::from_ints(-19, 13, -4),
        ];

        let passing_meshes = vec![
            Mesh::tetrahedron(),
            Mesh::cube(),
            Mesh::triangular_prism(),
            build_disconnected_translated_tetrahedra_mesh(&[(0, 0, 0), (20, 0, 0), (-15, 7, 3)]),
        ];
        for mesh in &passing_meshes {
            assert!(mesh.is_valid());
            assert!(mesh.check_outward_face_normals());
            assert_outward_face_normals_checker_reference_invariance(mesh, &references);

            let relabel_permutation: Vec<usize> = (0..mesh.vertices.len()).rev().collect();
            let relabeled_mesh = relabel_mesh_vertices_for_testing(mesh, &relabel_permutation)
                .expect("vertex-relabeled outwardness reference-invariance fixture should build");
            assert!(relabeled_mesh.is_valid());
            assert!(relabeled_mesh.check_outward_face_normals());
            assert_outward_face_normals_checker_reference_invariance(&relabeled_mesh, &references);
        }

        let reflected_cube = transform_mesh_positions(&Mesh::cube(), |point| {
            let mirrored = reflect_point3_across_yz_plane(point);
            translate_point3(&mirrored, 11, 3, -5)
        });
        assert!(reflected_cube.is_valid());
        assert!(!reflected_cube.check_outward_face_normals());
        assert_outward_face_normals_checker_reference_invariance(&reflected_cube, &references);

        let reflected_relabel_permutation: Vec<usize> =
            (0..reflected_cube.vertices.len()).rev().collect();
        let relabeled_reflected_cube =
            relabel_mesh_vertices_for_testing(&reflected_cube, &reflected_relabel_permutation)
                .expect(
                    "vertex-relabeled reflected outwardness reference-invariance fixture should build",
                );
        assert!(relabeled_reflected_cube.is_valid());
        assert!(!relabeled_reflected_cube.check_outward_face_normals());
        assert_outward_face_normals_checker_reference_invariance(
            &relabeled_reflected_cube,
            &references,
        );
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn differential_randomized_outward_checker_reference_origin_invariance_harness() {
        const CASES: usize = 40;
        let mut rng = DeterministicRng::new(0x0D15_EA5F);

        for case_id in 0..CASES {
            let component_count = rng.next_usize_inclusive(2, 7);
            let disjoint_origins = random_well_separated_component_origins(&mut rng, component_count);
            let disjoint_mesh = build_disconnected_translated_tetrahedra_mesh(&disjoint_origins);
            assert!(disjoint_mesh.is_valid());
            assert!(disjoint_mesh.check_outward_face_normals());

            let references = vec![
                RuntimePoint3::from_ints(0, 0, 0),
                RuntimePoint3::from_ints(
                    rng.next_i64_inclusive(-31, 31),
                    rng.next_i64_inclusive(-31, 31),
                    rng.next_i64_inclusive(-31, 31),
                ),
                RuntimePoint3::from_ints(
                    rng.next_i64_inclusive(-31, 31),
                    rng.next_i64_inclusive(-31, 31),
                    rng.next_i64_inclusive(-31, 31),
                ),
                RuntimePoint3::from_ints(
                    rng.next_i64_inclusive(-31, 31),
                    rng.next_i64_inclusive(-31, 31),
                    rng.next_i64_inclusive(-31, 31),
                ),
            ];
            assert_outward_face_normals_checker_reference_invariance(&disjoint_mesh, &references);
            let disjoint_permutation = random_permutation(&mut rng, disjoint_mesh.vertices.len());
            let relabeled_disjoint =
                relabel_mesh_vertices_for_testing(&disjoint_mesh, &disjoint_permutation)
                    .expect("vertex-relabeled disjoint outwardness fixture should build");
            assert!(
                relabeled_disjoint.is_valid(),
                "vertex-relabeled disjoint outwardness fixture should preserve validity in case {case_id}"
            );
            assert!(
                relabeled_disjoint.check_outward_face_normals(),
                "vertex-relabeled disjoint outwardness fixture should preserve orientation in case {case_id}"
            );
            assert_outward_face_normals_checker_reference_invariance(
                &relabeled_disjoint,
                &references,
            );

            let quarter_turns = rng.next_u64() % 4;
            let tx = rng.next_i64_inclusive(-25, 25);
            let ty = rng.next_i64_inclusive(-25, 25);
            let tz = rng.next_i64_inclusive(-25, 25);
            let rigid_disjoint = transform_mesh_positions(&disjoint_mesh, |point| {
                rigid_rotate_z_quarter_turns_then_translate(point, quarter_turns, tx, ty, tz)
            });
            assert!(rigid_disjoint.is_valid());
            assert!(rigid_disjoint.check_outward_face_normals());
            assert_outward_face_normals_checker_reference_invariance(&rigid_disjoint, &references);
            let rigid_permutation = random_permutation(&mut rng, rigid_disjoint.vertices.len());
            let relabeled_rigid_disjoint =
                relabel_mesh_vertices_for_testing(&rigid_disjoint, &rigid_permutation)
                    .expect("vertex-relabeled rigid outwardness fixture should build");
            assert!(
                relabeled_rigid_disjoint.is_valid(),
                "vertex-relabeled rigid outwardness fixture should preserve validity in case {case_id}"
            );
            assert!(
                relabeled_rigid_disjoint.check_outward_face_normals(),
                "vertex-relabeled rigid outwardness fixture should preserve orientation in case {case_id}"
            );
            assert_outward_face_normals_checker_reference_invariance(
                &relabeled_rigid_disjoint,
                &references,
            );

            let reflected_disjoint = transform_mesh_positions(&disjoint_mesh, |point| {
                let mirrored = reflect_point3_across_yz_plane(point);
                translate_point3(&mirrored, tx, ty, tz)
            });
            assert!(reflected_disjoint.is_valid());
            assert!(!reflected_disjoint.check_outward_face_normals());
            assert_outward_face_normals_checker_reference_invariance(
                &reflected_disjoint,
                &references,
            );
            let reflected_permutation = random_permutation(&mut rng, reflected_disjoint.vertices.len());
            let relabeled_reflected_disjoint =
                relabel_mesh_vertices_for_testing(&reflected_disjoint, &reflected_permutation)
                    .expect("vertex-relabeled reflected outwardness fixture should build");
            assert!(
                relabeled_reflected_disjoint.is_valid(),
                "vertex-relabeled reflected outwardness fixture should preserve validity in case {case_id}"
            );
            assert!(
                !relabeled_reflected_disjoint.check_outward_face_normals(),
                "vertex-relabeled reflected outwardness fixture should remain inward in case {case_id}"
            );
            assert_outward_face_normals_checker_reference_invariance(
                &relabeled_reflected_disjoint,
                &references,
            );
        }
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn outward_signed_volume_is_reference_origin_invariant_per_component() {
        let origins = vec![(0, 0, 0), (20, 0, 0), (-15, 7, 3)];
        let mesh = build_disconnected_translated_tetrahedra_mesh(&origins);
        assert!(mesh.is_valid());
        assert!(mesh.check_outward_face_normals());
        let component_starts = component_start_half_edges(&mesh);
        assert_eq!(component_starts.len(), origins.len());

        let references = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(11, -7, 5),
            RuntimePoint3::from_ints(-19, 13, -4),
        ];
        assert_component_signed_volume_reference_invariance_with_expected_sign(
            &mesh,
            &references,
            -1,
            "deterministic_disjoint_outward",
        );

        let relabel_permutation: Vec<usize> = (0..mesh.vertices.len()).rev().collect();
        let relabeled_mesh = relabel_mesh_vertices_for_testing(&mesh, &relabel_permutation)
            .expect("vertex-relabeled deterministic disjoint mesh should build");
        assert!(relabeled_mesh.is_valid());
        assert!(relabeled_mesh.check_outward_face_normals());
        assert_component_signed_volume_reference_invariance_with_expected_sign(
            &relabeled_mesh,
            &references,
            -1,
            "deterministic_disjoint_outward_relabeled",
        );

        let reflected_mesh = transform_mesh_positions(&mesh, |point| {
            let mirrored = reflect_point3_across_yz_plane(point);
            translate_point3(&mirrored, 11, 3, -5)
        });
        assert!(reflected_mesh.is_valid());
        assert!(!reflected_mesh.check_outward_face_normals());
        assert_component_signed_volume_reference_invariance_with_expected_sign(
            &reflected_mesh,
            &references,
            1,
            "deterministic_disjoint_reflected",
        );

        let relabeled_reflected_mesh =
            relabel_mesh_vertices_for_testing(&reflected_mesh, &relabel_permutation)
                .expect("vertex-relabeled deterministic reflected mesh should build");
        assert!(relabeled_reflected_mesh.is_valid());
        assert!(!relabeled_reflected_mesh.check_outward_face_normals());
        assert_component_signed_volume_reference_invariance_with_expected_sign(
            &relabeled_reflected_mesh,
            &references,
            1,
            "deterministic_disjoint_reflected_relabeled",
        );
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn differential_randomized_outward_signed_volume_reference_origin_invariance_harness() {
        const CASES: usize = 40;
        let mut rng = DeterministicRng::new(0x0D15_EA5E);

        for case_id in 0..CASES {
            let component_count = rng.next_usize_inclusive(2, 7);
            let disjoint_origins = random_well_separated_component_origins(&mut rng, component_count);
            let disjoint_mesh = build_disconnected_translated_tetrahedra_mesh(&disjoint_origins);
            assert!(disjoint_mesh.is_valid());
            assert!(disjoint_mesh.check_outward_face_normals());

            let references = vec![
                RuntimePoint3::from_ints(0, 0, 0),
                RuntimePoint3::from_ints(
                    rng.next_i64_inclusive(-31, 31),
                    rng.next_i64_inclusive(-31, 31),
                    rng.next_i64_inclusive(-31, 31),
                ),
                RuntimePoint3::from_ints(
                    rng.next_i64_inclusive(-31, 31),
                    rng.next_i64_inclusive(-31, 31),
                    rng.next_i64_inclusive(-31, 31),
                ),
                RuntimePoint3::from_ints(
                    rng.next_i64_inclusive(-31, 31),
                    rng.next_i64_inclusive(-31, 31),
                    rng.next_i64_inclusive(-31, 31),
                ),
            ];
            assert_component_signed_volume_reference_invariance_with_expected_sign(
                &disjoint_mesh,
                &references,
                -1,
                &format!("random_disjoint_signed_volume_case_{case_id}"),
            );
            let disjoint_permutation = random_permutation(&mut rng, disjoint_mesh.vertices.len());
            let relabeled_disjoint =
                relabel_mesh_vertices_for_testing(&disjoint_mesh, &disjoint_permutation)
                    .expect("vertex-relabeled disjoint signed-volume fixture should build");
            assert!(
                relabeled_disjoint.is_valid(),
                "vertex-relabeled disjoint signed-volume fixture should preserve validity in case {case_id}"
            );
            assert!(
                relabeled_disjoint.check_outward_face_normals(),
                "vertex-relabeled disjoint signed-volume fixture should preserve outwardness in case {case_id}"
            );
            assert_component_signed_volume_reference_invariance_with_expected_sign(
                &relabeled_disjoint,
                &references,
                -1,
                &format!("random_disjoint_signed_volume_relabeled_case_{case_id}"),
            );

            let quarter_turns = rng.next_u64() % 4;
            let tx = rng.next_i64_inclusive(-25, 25);
            let ty = rng.next_i64_inclusive(-25, 25);
            let tz = rng.next_i64_inclusive(-25, 25);
            let rigid_disjoint = transform_mesh_positions(&disjoint_mesh, |point| {
                rigid_rotate_z_quarter_turns_then_translate(point, quarter_turns, tx, ty, tz)
            });
            assert!(rigid_disjoint.is_valid());
            assert!(rigid_disjoint.check_outward_face_normals());
            assert_component_signed_volume_reference_invariance_with_expected_sign(
                &rigid_disjoint,
                &references,
                -1,
                &format!("random_rigid_signed_volume_case_{case_id}"),
            );
            let rigid_permutation = random_permutation(&mut rng, rigid_disjoint.vertices.len());
            let relabeled_rigid_disjoint =
                relabel_mesh_vertices_for_testing(&rigid_disjoint, &rigid_permutation)
                    .expect("vertex-relabeled rigid signed-volume fixture should build");
            assert!(
                relabeled_rigid_disjoint.is_valid(),
                "vertex-relabeled rigid signed-volume fixture should preserve validity in case {case_id}"
            );
            assert!(
                relabeled_rigid_disjoint.check_outward_face_normals(),
                "vertex-relabeled rigid signed-volume fixture should preserve outwardness in case {case_id}"
            );
            assert_component_signed_volume_reference_invariance_with_expected_sign(
                &relabeled_rigid_disjoint,
                &references,
                -1,
                &format!("random_rigid_signed_volume_relabeled_case_{case_id}"),
            );

            let reflected_disjoint = transform_mesh_positions(&disjoint_mesh, |point| {
                let mirrored = reflect_point3_across_yz_plane(point);
                translate_point3(&mirrored, tx, ty, tz)
            });
            assert!(reflected_disjoint.is_valid());
            assert!(!reflected_disjoint.check_outward_face_normals());
            assert_component_signed_volume_reference_invariance_with_expected_sign(
                &reflected_disjoint,
                &references,
                1,
                &format!("random_reflected_signed_volume_case_{case_id}"),
            );
            let reflected_permutation = random_permutation(&mut rng, reflected_disjoint.vertices.len());
            let relabeled_reflected_disjoint =
                relabel_mesh_vertices_for_testing(&reflected_disjoint, &reflected_permutation)
                    .expect("vertex-relabeled reflected signed-volume fixture should build");
            assert!(
                relabeled_reflected_disjoint.is_valid(),
                "vertex-relabeled reflected signed-volume fixture should preserve validity in case {case_id}"
            );
            assert!(
                !relabeled_reflected_disjoint.check_outward_face_normals(),
                "vertex-relabeled reflected signed-volume fixture should remain inward in case {case_id}"
            );
            assert_component_signed_volume_reference_invariance_with_expected_sign(
                &relabeled_reflected_disjoint,
                &references,
                1,
                &format!("random_reflected_signed_volume_relabeled_case_{case_id}"),
            );
        }
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn outward_signed_volume_sign_matches_per_face_normal_alignment_for_convex_components() {
        let references = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(11, -7, 5),
            RuntimePoint3::from_ints(-19, 13, -4),
        ];

        let passing_meshes = vec![
            ("tetrahedron", Mesh::tetrahedron()),
            ("cube", Mesh::cube()),
            ("triangular_prism", Mesh::triangular_prism()),
            (
                "disconnected_tetrahedra",
                build_disconnected_translated_tetrahedra_mesh(&[(0, 0, 0), (20, 0, 0), (-15, 7, 3)]),
            ),
        ];
        for (label, mesh) in passing_meshes {
            assert!(mesh.is_valid(), "{label}: fixture should remain Phase-4 valid");
            assert!(
                mesh.check_outward_face_normals(),
                "{label}: fixture should satisfy outward-normal checker"
            );
            assert_signed_volume_component_sign_matches_per_face_normal_alignment(
                &mesh,
                &references,
                label,
            );

            let relabel_permutation: Vec<usize> = (0..mesh.vertices.len()).rev().collect();
            let relabeled_mesh = relabel_mesh_vertices_for_testing(&mesh, &relabel_permutation)
                .expect("vertex-relabeled convex-component outwardness fixture should build");
            assert!(
                relabeled_mesh.is_valid(),
                "{label}: relabeled fixture should remain Phase-4 valid"
            );
            assert!(
                relabeled_mesh.check_outward_face_normals(),
                "{label}: relabeled fixture should satisfy outward-normal checker"
            );
            assert_signed_volume_component_sign_matches_per_face_normal_alignment(
                &relabeled_mesh,
                &references,
                &format!("{label}_relabeled"),
            );
        }

        let reflected_meshes = vec![
            (
                "reflected_cube",
                transform_mesh_positions(&Mesh::cube(), |point| {
                    let mirrored = reflect_point3_across_yz_plane(point);
                    translate_point3(&mirrored, 11, 3, -5)
                }),
            ),
            (
                "reflected_disconnected_tetrahedra",
                transform_mesh_positions(
                    &build_disconnected_translated_tetrahedra_mesh(&[(0, 0, 0), (20, 0, 0), (-15, 7, 3)]),
                    |point| {
                        let mirrored = reflect_point3_across_yz_plane(point);
                        translate_point3(&mirrored, 11, 3, -5)
                    },
                ),
            ),
        ];
        for (label, mesh) in reflected_meshes {
            assert!(mesh.is_valid(), "{label}: reflected fixture should remain Phase-4 valid");
            assert!(
                !mesh.check_outward_face_normals(),
                "{label}: reflected fixture should fail outward-normal checker"
            );
            assert_signed_volume_component_sign_matches_per_face_normal_alignment(
                &mesh,
                &references,
                label,
            );

            let relabel_permutation: Vec<usize> = (0..mesh.vertices.len()).rev().collect();
            let relabeled_mesh = relabel_mesh_vertices_for_testing(&mesh, &relabel_permutation)
                .expect("vertex-relabeled reflected convex-component fixture should build");
            assert!(
                relabeled_mesh.is_valid(),
                "{label}: relabeled reflected fixture should remain Phase-4 valid"
            );
            assert!(
                !relabeled_mesh.check_outward_face_normals(),
                "{label}: relabeled reflected fixture should fail outward-normal checker"
            );
            assert_signed_volume_component_sign_matches_per_face_normal_alignment(
                &relabeled_mesh,
                &references,
                &format!("{label}_relabeled"),
            );
        }
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn differential_randomized_outward_signed_volume_per_face_alignment_harness() {
        const CASES: usize = 40;
        let mut rng = DeterministicRng::new(0x0D15_EA61);

        for case_id in 0..CASES {
            let component_count = rng.next_usize_inclusive(2, 7);
            let disjoint_origins = random_well_separated_component_origins(&mut rng, component_count);
            let disjoint_mesh = build_disconnected_translated_tetrahedra_mesh(&disjoint_origins);
            assert!(
                disjoint_mesh.is_valid(),
                "random disjoint fixture should be Phase-4 valid in case {case_id}"
            );
            assert!(
                disjoint_mesh.check_outward_face_normals(),
                "random disjoint fixture should satisfy outward-normal checker in case {case_id}"
            );

            let references = vec![
                RuntimePoint3::from_ints(0, 0, 0),
                RuntimePoint3::from_ints(
                    rng.next_i64_inclusive(-31, 31),
                    rng.next_i64_inclusive(-31, 31),
                    rng.next_i64_inclusive(-31, 31),
                ),
                RuntimePoint3::from_ints(
                    rng.next_i64_inclusive(-31, 31),
                    rng.next_i64_inclusive(-31, 31),
                    rng.next_i64_inclusive(-31, 31),
                ),
                RuntimePoint3::from_ints(
                    rng.next_i64_inclusive(-31, 31),
                    rng.next_i64_inclusive(-31, 31),
                    rng.next_i64_inclusive(-31, 31),
                ),
            ];

            assert_signed_volume_component_sign_matches_per_face_normal_alignment(
                &disjoint_mesh,
                &references,
                &format!("random_disjoint_per_face_alignment_case_{case_id}"),
            );
            let disjoint_permutation = random_permutation(&mut rng, disjoint_mesh.vertices.len());
            let relabeled_disjoint =
                relabel_mesh_vertices_for_testing(&disjoint_mesh, &disjoint_permutation)
                    .expect("vertex-relabeled disjoint per-face-alignment fixture should build");
            assert!(
                relabeled_disjoint.is_valid(),
                "vertex-relabeled disjoint fixture should remain valid in case {case_id}"
            );
            assert!(
                relabeled_disjoint.check_outward_face_normals(),
                "vertex-relabeled disjoint fixture should remain outward in case {case_id}"
            );
            assert_signed_volume_component_sign_matches_per_face_normal_alignment(
                &relabeled_disjoint,
                &references,
                &format!("random_disjoint_per_face_alignment_relabeled_case_{case_id}"),
            );

            let quarter_turns = rng.next_u64() % 4;
            let tx = rng.next_i64_inclusive(-25, 25);
            let ty = rng.next_i64_inclusive(-25, 25);
            let tz = rng.next_i64_inclusive(-25, 25);
            let rigid_disjoint = transform_mesh_positions(&disjoint_mesh, |point| {
                rigid_rotate_z_quarter_turns_then_translate(point, quarter_turns, tx, ty, tz)
            });
            assert!(
                rigid_disjoint.is_valid(),
                "rigid disjoint fixture should remain valid in case {case_id}"
            );
            assert!(
                rigid_disjoint.check_outward_face_normals(),
                "rigid disjoint fixture should remain outward in case {case_id}"
            );
            assert_signed_volume_component_sign_matches_per_face_normal_alignment(
                &rigid_disjoint,
                &references,
                &format!("random_rigid_per_face_alignment_case_{case_id}"),
            );
            let rigid_permutation = random_permutation(&mut rng, rigid_disjoint.vertices.len());
            let relabeled_rigid_disjoint =
                relabel_mesh_vertices_for_testing(&rigid_disjoint, &rigid_permutation)
                    .expect("vertex-relabeled rigid per-face-alignment fixture should build");
            assert!(
                relabeled_rigid_disjoint.is_valid(),
                "vertex-relabeled rigid fixture should remain valid in case {case_id}"
            );
            assert!(
                relabeled_rigid_disjoint.check_outward_face_normals(),
                "vertex-relabeled rigid fixture should remain outward in case {case_id}"
            );
            assert_signed_volume_component_sign_matches_per_face_normal_alignment(
                &relabeled_rigid_disjoint,
                &references,
                &format!("random_rigid_per_face_alignment_relabeled_case_{case_id}"),
            );

            let reflected_disjoint = transform_mesh_positions(&disjoint_mesh, |point| {
                let mirrored = reflect_point3_across_yz_plane(point);
                translate_point3(&mirrored, tx, ty, tz)
            });
            assert!(
                reflected_disjoint.is_valid(),
                "reflected disjoint fixture should remain valid in case {case_id}"
            );
            assert!(
                !reflected_disjoint.check_outward_face_normals(),
                "reflected disjoint fixture should fail outward checker in case {case_id}"
            );
            assert_signed_volume_component_sign_matches_per_face_normal_alignment(
                &reflected_disjoint,
                &references,
                &format!("random_reflected_per_face_alignment_case_{case_id}"),
            );
            let reflected_permutation = random_permutation(&mut rng, reflected_disjoint.vertices.len());
            let relabeled_reflected_disjoint =
                relabel_mesh_vertices_for_testing(&reflected_disjoint, &reflected_permutation)
                    .expect("vertex-relabeled reflected per-face-alignment fixture should build");
            assert!(
                relabeled_reflected_disjoint.is_valid(),
                "vertex-relabeled reflected fixture should remain valid in case {case_id}"
            );
            assert!(
                !relabeled_reflected_disjoint.check_outward_face_normals(),
                "vertex-relabeled reflected fixture should fail outward checker in case {case_id}"
            );
            assert_signed_volume_component_sign_matches_per_face_normal_alignment(
                &relabeled_reflected_disjoint,
                &references,
                &format!("random_reflected_per_face_alignment_relabeled_case_{case_id}"),
            );
        }
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn reflection_flips_outward_orientation_sensitive_phase5_checks() {
        let cube = Mesh::cube();
        let reflected = transform_mesh_positions(&cube, |point| {
            let mirrored = reflect_point3_across_yz_plane(point);
            translate_point3(&mirrored, 11, 3, -5)
        });

        assert!(cube.is_valid());
        assert!(reflected.is_valid());
        assert_eq!(
            cube.check_no_zero_length_geometric_edges(),
            reflected.check_no_zero_length_geometric_edges()
        );
        assert_eq!(
            cube.check_face_corner_non_collinearity(),
            reflected.check_face_corner_non_collinearity()
        );
        assert_eq!(cube.check_face_coplanarity(), reflected.check_face_coplanarity());
        assert_eq!(cube.check_face_convexity(), reflected.check_face_convexity());
        assert_eq!(
            cube.check_face_plane_consistency(),
            reflected.check_face_plane_consistency()
        );
        assert_eq!(
            cube.check_shared_edge_local_orientation_consistency(),
            reflected.check_shared_edge_local_orientation_consistency()
        );
        assert_eq!(
            cube.check_no_forbidden_face_face_intersections(),
            reflected.check_no_forbidden_face_face_intersections()
        );
        assert!(cube.check_outward_face_normals());
        assert!(!reflected.check_outward_face_normals());
        assert!(cube.check_geometric_topological_consistency());
        assert!(!reflected.check_geometric_topological_consistency());
        assert!(cube.is_valid_with_geometry());
        assert!(!reflected.is_valid_with_geometry());

        let reflected_failure = reflected
            .check_geometric_topological_consistency_diagnostic()
            .expect_err("reflected cube should fail by orientation-sensitive outwardness");
        assert!(matches!(
            reflected_failure,
            GeometricTopologicalConsistencyFailure::InwardOrDegenerateComponent { .. }
        ));
    }

    #[test]
    fn disconnected_closed_components_have_expected_component_and_euler_counts() {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(0, 1, 0),
            RuntimePoint3::from_ints(0, 0, 1),
            RuntimePoint3::from_ints(10, 0, 0),
            RuntimePoint3::from_ints(11, 0, 0),
            RuntimePoint3::from_ints(10, 1, 0),
            RuntimePoint3::from_ints(10, 0, 1),
        ];
        let faces = vec![
            vec![0, 1, 2],
            vec![0, 3, 1],
            vec![1, 3, 2],
            vec![2, 3, 0],
            vec![4, 5, 6],
            vec![4, 7, 5],
            vec![5, 7, 6],
            vec![6, 7, 4],
        ];

        let mesh = Mesh::from_face_cycles(vertices, &faces)
            .expect("two disconnected tetrahedra should build as a closed mesh");
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        assert_eq!(mesh.component_count(), 2);

        let chis = mesh.euler_characteristics_per_component();
        assert_eq!(chis.len(), 2);
        assert!(chis.into_iter().all(|chi| chi == 2));
        assert!(mesh.check_euler_formula_closed_components());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn stress_many_disconnected_components_geometric_consistency_passes() {
        const COMPONENTS: usize = 24;
        let mut origins = Vec::with_capacity(COMPONENTS);
        for i in 0..COMPONENTS {
            origins.push((i as i64 * 10, 0, 0));
        }

        let mesh = build_disconnected_translated_tetrahedra_mesh(&origins);
        assert_eq!(mesh.faces.len(), COMPONENTS * 4);
        assert!(mesh.is_valid());
        assert_eq!(mesh.component_count(), COMPONENTS);
        assert!(mesh.check_no_forbidden_face_face_intersections());
        assert!(mesh.check_geometric_topological_consistency());
        assert_eq!(
            mesh.check_geometric_topological_consistency(),
            mesh.check_geometric_topological_consistency_diagnostic().is_ok()
        );
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn stress_many_components_with_one_overlap_fails_intersection_checker() {
        const COMPONENTS: usize = 24;
        let mut origins = Vec::with_capacity(COMPONENTS);
        for i in 0..(COMPONENTS - 1) {
            origins.push((i as i64 * 10, 0, 0));
        }
        origins.push((0, 0, 0));

        let mesh = build_disconnected_translated_tetrahedra_mesh(&origins);
        assert_eq!(mesh.faces.len(), COMPONENTS * 4);
        assert!(mesh.is_valid());
        assert!(!mesh.check_no_forbidden_face_face_intersections());
        assert!(!mesh.check_geometric_topological_consistency());
        let failure = mesh
            .check_geometric_topological_consistency_diagnostic()
            .expect_err("overlapping stress fixture should fail");
        assert!(matches!(
            failure,
            GeometricTopologicalConsistencyFailure::ForbiddenFaceFaceIntersection { .. }
        ));
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn broad_phase_face_pair_culling_matches_no_cull_oracle() {
        let mut disjoint_origins = Vec::new();
        for i in 0..12 {
            disjoint_origins.push((i * 10, 0, 0));
        }
        let disjoint_stress = build_disconnected_translated_tetrahedra_mesh(&disjoint_origins);

        let mut overlapping_origins = disjoint_origins.clone();
        overlapping_origins.push((0, 0, 0));
        let overlapping_stress = build_disconnected_translated_tetrahedra_mesh(&overlapping_origins);

        let cube = Mesh::cube();
        let cube_rigid = transform_mesh_positions(&cube, |point| {
            rigid_rotate_z_90_then_translate(point, 7, -5, 3)
        });
        let overlapping_rigid = transform_mesh_positions(&build_overlapping_tetrahedra_mesh(), |point| {
            rigid_rotate_z_90_then_translate(point, -11, 4, 9)
        });

        let fixtures = vec![
            Mesh::tetrahedron(),
            cube,
            Mesh::triangular_prism(),
            build_overlapping_tetrahedra_mesh(),
            disjoint_stress,
            overlapping_stress,
            cube_rigid,
            overlapping_rigid,
        ];

        for mesh in fixtures {
            assert!(mesh.is_valid(), "fixture must satisfy Phase 4 validity");
            assert_forbidden_face_face_checker_broad_phase_sound(&mesh);
        }
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn allowed_contact_topology_classifier_matches_edge_index_oracle() {
        let coincident_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 1),
            RuntimePoint3::from_ints(1, 0, 1),
            RuntimePoint3::from_ints(0, 1, 1),
        ];
        let coincident_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let coincident_double_face_mesh = Mesh::from_face_cycles(coincident_vertices, &coincident_faces)
            .expect("coincident double-face fixture should build");

        let mut disjoint_origins = Vec::new();
        for i in 0..8 {
            disjoint_origins.push((i * 10, 0, 0));
        }
        let disjoint_stress = build_disconnected_translated_tetrahedra_mesh(&disjoint_origins);

        let fixtures = vec![
            Mesh::tetrahedron(),
            Mesh::cube(),
            Mesh::triangular_prism(),
            build_overlapping_tetrahedra_mesh(),
            coincident_double_face_mesh,
            disjoint_stress,
        ];

        for mesh in fixtures {
            assert!(mesh.is_valid(), "fixture must satisfy Phase 4 validity");
            assert_allowed_contact_topology_classifier_matches_edge_index_oracle(&mesh);
        }
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn differential_randomized_allowed_contact_topology_classifier_harness() {
        const CASES: usize = 40;
        let mut rng = DeterministicRng::new(0xA110_C0DE);

        for case_idx in 0..CASES {
            let component_count = rng.next_usize_inclusive(2, 7);
            let disjoint_origins =
                random_well_separated_component_origins(&mut rng, component_count);
            let disjoint_mesh =
                build_disconnected_translated_tetrahedra_mesh(&disjoint_origins);
            assert!(
                disjoint_mesh.is_valid(),
                "generated disjoint fixture should satisfy Phase 4 validity"
            );
            assert_allowed_contact_topology_classifier_matches_edge_index_oracle(&disjoint_mesh);
            let disjoint_permutation = random_permutation(&mut rng, disjoint_mesh.vertices.len());
            let relabeled_disjoint =
                relabel_mesh_vertices_for_testing(&disjoint_mesh, &disjoint_permutation)
                    .expect("vertex-relabeled disjoint mesh should build");
            assert!(
                relabeled_disjoint.is_valid(),
                "vertex-relabeled disjoint fixture should satisfy Phase 4 validity in case {case_idx}"
            );
            assert_allowed_contact_topology_classifier_matches_edge_index_oracle(
                &relabeled_disjoint,
            );

            let quarter_turns = rng.next_u64() % 4;
            let tx = rng.next_i64_inclusive(-25, 25);
            let ty = rng.next_i64_inclusive(-25, 25);
            let tz = rng.next_i64_inclusive(-25, 25);
            let rigid_disjoint = transform_mesh_positions(&disjoint_mesh, |point| {
                rigid_rotate_z_quarter_turns_then_translate(point, quarter_turns, tx, ty, tz)
            });
            assert!(
                rigid_disjoint.is_valid(),
                "rigidly transformed fixture should preserve Phase 4 validity"
            );
            assert_allowed_contact_topology_classifier_matches_edge_index_oracle(&rigid_disjoint);
            let rigid_permutation = random_permutation(&mut rng, rigid_disjoint.vertices.len());
            let relabeled_rigid_disjoint =
                relabel_mesh_vertices_for_testing(&rigid_disjoint, &rigid_permutation)
                    .expect("vertex-relabeled rigid disjoint mesh should build");
            assert!(
                relabeled_rigid_disjoint.is_valid(),
                "vertex-relabeled rigid fixture should satisfy Phase 4 validity in case {case_idx}"
            );
            assert_allowed_contact_topology_classifier_matches_edge_index_oracle(
                &relabeled_rigid_disjoint,
            );

            let (source_component, perturbed_component) =
                pick_distinct_indices(&mut rng, component_count);
            let mut perturbed_origins = disjoint_origins.clone();
            let perturbation = match rng.next_u64() % 4 {
                0 => (0, 0, 0),
                1 => (1, 0, 0),
                2 => (0, 1, 0),
                _ => (0, 0, 1),
            };
            let (ox, oy, oz) = perturbed_origins[source_component];
            perturbed_origins[perturbed_component] =
                (ox + perturbation.0, oy + perturbation.1, oz + perturbation.2);

            let perturbed_mesh =
                build_disconnected_translated_tetrahedra_mesh(&perturbed_origins);
            assert!(
                perturbed_mesh.is_valid(),
                "topology should remain valid under coordinate perturbations"
            );
            assert_allowed_contact_topology_classifier_matches_edge_index_oracle(&perturbed_mesh);
            let perturbed_permutation = random_permutation(&mut rng, perturbed_mesh.vertices.len());
            let relabeled_perturbed =
                relabel_mesh_vertices_for_testing(&perturbed_mesh, &perturbed_permutation)
                    .expect("vertex-relabeled perturbed mesh should build");
            assert!(
                relabeled_perturbed.is_valid(),
                "vertex-relabeled perturbed fixture should satisfy Phase 4 validity in case {case_idx}"
            );
            assert_allowed_contact_topology_classifier_matches_edge_index_oracle(
                &relabeled_perturbed,
            );
        }
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn shared_edge_contacts_are_not_misclassified_as_forbidden_intersections() {
        let tetrahedron = Mesh::tetrahedron();
        let cube = Mesh::cube();
        let prism = Mesh::triangular_prism();
        let reflected_tetrahedron = transform_mesh_positions(&tetrahedron, reflect_point3_across_yz_plane);
        let reflected_cube = transform_mesh_positions(&cube, reflect_point3_across_yz_plane);
        let reflected_prism = transform_mesh_positions(&prism, reflect_point3_across_yz_plane);

        let fixtures = vec![
            ("tetrahedron", tetrahedron),
            ("cube", cube),
            ("triangular_prism", prism),
            ("reflected_tetrahedron", reflected_tetrahedron),
            ("reflected_cube", reflected_cube),
            ("reflected_triangular_prism", reflected_prism),
        ];

        for (label, mesh) in fixtures {
            assert!(mesh.is_valid(), "fixture must satisfy Phase 4 validity");
            assert_allowed_contact_topology_classifier_matches_edge_index_oracle(&mesh);
            assert!(mesh.check_no_forbidden_face_face_intersections());
            assert_shared_edge_contacts_not_misclassified_as_forbidden_intersections(&mesh, label);
        }
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn shared_vertex_only_contacts_are_not_misclassified_as_forbidden_intersections() {
        let octahedron = build_octahedron_mesh();
        let rigid_octahedron = transform_mesh_positions(&octahedron, |point| {
            rigid_rotate_z_90_then_translate(point, 9, -6, 4)
        });
        let reflected_octahedron = transform_mesh_positions(&octahedron, reflect_point3_across_yz_plane);
        let reflected_rigid_octahedron =
            transform_mesh_positions(&rigid_octahedron, reflect_point3_across_yz_plane);

        let fixtures = vec![
            ("octahedron", octahedron),
            ("rigid_octahedron", rigid_octahedron),
            ("reflected_octahedron", reflected_octahedron),
            ("reflected_rigid_octahedron", reflected_rigid_octahedron),
        ];

        for (label, mesh) in fixtures {
            assert!(mesh.is_valid(), "fixture must satisfy Phase 4 validity");
            assert_allowed_contact_topology_classifier_matches_edge_index_oracle(&mesh);
            assert!(mesh.check_no_forbidden_face_face_intersections());
            assert_shared_vertex_only_contacts_not_misclassified_as_forbidden_intersections(
                &mesh,
                label,
            );
        }
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn non_allowed_contact_topology_pairs_are_classified_as_forbidden() {
        let coincident_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 1),
            RuntimePoint3::from_ints(1, 0, 1),
            RuntimePoint3::from_ints(0, 1, 1),
        ];
        let coincident_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let coincident_double_face_mesh = Mesh::from_face_cycles(coincident_vertices, &coincident_faces)
            .expect("coincident double-face fixture should build");
        let rigid = transform_mesh_positions(&coincident_double_face_mesh, |point| {
            rigid_rotate_z_90_then_translate(point, 11, -7, 5)
        });
        let reflected =
            transform_mesh_positions(&coincident_double_face_mesh, reflect_point3_across_yz_plane);
        let relabeled = relabel_mesh_vertices_for_testing(&coincident_double_face_mesh, &[2, 0, 1])
            .expect("vertex-relabeled coincident fixture should build");

        let fixtures = vec![
            ("coincident_double_face", coincident_double_face_mesh),
            ("coincident_double_face_rigid", rigid),
            ("coincident_double_face_reflected", reflected),
            ("coincident_double_face_relabeled", relabeled),
        ];

        for (label, mesh) in fixtures {
            assert!(mesh.is_valid(), "fixture {label} should satisfy Phase 4 validity");
            assert_allowed_contact_topology_classifier_matches_edge_index_oracle(&mesh);
            assert_non_allowed_contact_topology_pairs_are_forbidden(&mesh, label);
            assert!(
                !mesh.check_no_forbidden_face_face_intersections(),
                "fixture {label} should fail the forbidden face-face checker"
            );
        }
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn differential_randomized_shared_boundary_contact_non_misclassification_harness() {
        const CASES: usize = 40;
        let mut rng = DeterministicRng::new(0x5EED_B00A_DA7A);

        let shared_edge_bases = vec![
            ("tetrahedron", Mesh::tetrahedron()),
            ("cube", Mesh::cube()),
            ("triangular_prism", Mesh::triangular_prism()),
        ];
        let shared_vertex_bases = vec![("octahedron", build_octahedron_mesh())];

        for case_idx in 0..CASES {
            let edge_quarter_turns = rng.next_u64() % 4;
            let edge_tx = rng.next_i64_inclusive(-30, 30);
            let edge_ty = rng.next_i64_inclusive(-30, 30);
            let edge_tz = rng.next_i64_inclusive(-30, 30);

            for (label, base_mesh) in &shared_edge_bases {
                let transformed = transform_mesh_positions(base_mesh, |point| {
                    rigid_rotate_z_quarter_turns_then_translate(
                        point,
                        edge_quarter_turns,
                        edge_tx,
                        edge_ty,
                        edge_tz,
                    )
                });
                assert!(
                    transformed.is_valid(),
                    "rigidly transformed shared-edge fixture should satisfy Phase 4 validity"
                );
                assert_allowed_contact_topology_classifier_matches_edge_index_oracle(&transformed);
                assert!(
                    transformed.check_no_forbidden_face_face_intersections(),
                    "shared-edge fixture should remain intersection-free in randomized case {case_idx}"
                );

                let case_label = format!("{label}_random_case_{case_idx}");
                assert_shared_edge_contacts_not_misclassified_as_forbidden_intersections(
                    &transformed,
                    &case_label,
                );
                let relabel_permutation = random_permutation(&mut rng, transformed.vertices.len());
                let relabeled =
                    relabel_mesh_vertices_for_testing(&transformed, &relabel_permutation)
                        .expect("vertex-relabeled shared-edge fixture should build");
                assert!(
                    relabeled.is_valid(),
                    "vertex-relabeled shared-edge fixture should satisfy Phase 4 validity in randomized case {case_idx}"
                );
                assert_allowed_contact_topology_classifier_matches_edge_index_oracle(&relabeled);
                assert!(
                    relabeled.check_no_forbidden_face_face_intersections(),
                    "vertex-relabeled shared-edge fixture should remain intersection-free in randomized case {case_idx}"
                );
                let relabeled_case_label = format!("{label}_random_case_{case_idx}_relabeled");
                assert_shared_edge_contacts_not_misclassified_as_forbidden_intersections(
                    &relabeled,
                    &relabeled_case_label,
                );

                let reflected = transform_mesh_positions(&transformed, reflect_point3_across_yz_plane);
                assert!(
                    reflected.is_valid(),
                    "reflected shared-edge fixture should satisfy Phase 4 validity"
                );
                assert_allowed_contact_topology_classifier_matches_edge_index_oracle(&reflected);
                assert!(
                    reflected.check_no_forbidden_face_face_intersections(),
                    "reflected shared-edge fixture should remain intersection-free in randomized case {case_idx}"
                );
                let reflected_case_label = format!("{label}_random_case_{case_idx}_reflected");
                assert_shared_edge_contacts_not_misclassified_as_forbidden_intersections(
                    &reflected,
                    &reflected_case_label,
                );
                let reflected_relabel_permutation =
                    random_permutation(&mut rng, reflected.vertices.len());
                let reflected_relabeled = relabel_mesh_vertices_for_testing(
                    &reflected,
                    &reflected_relabel_permutation,
                )
                .expect("vertex-relabeled reflected shared-edge fixture should build");
                assert!(
                    reflected_relabeled.is_valid(),
                    "vertex-relabeled reflected shared-edge fixture should satisfy Phase 4 validity in randomized case {case_idx}"
                );
                assert_allowed_contact_topology_classifier_matches_edge_index_oracle(
                    &reflected_relabeled,
                );
                assert!(
                    reflected_relabeled.check_no_forbidden_face_face_intersections(),
                    "vertex-relabeled reflected shared-edge fixture should remain intersection-free in randomized case {case_idx}"
                );
                let reflected_relabeled_case_label =
                    format!("{label}_random_case_{case_idx}_reflected_relabeled");
                assert_shared_edge_contacts_not_misclassified_as_forbidden_intersections(
                    &reflected_relabeled,
                    &reflected_relabeled_case_label,
                );
            }

            let vertex_quarter_turns = rng.next_u64() % 4;
            let vertex_tx = rng.next_i64_inclusive(-30, 30);
            let vertex_ty = rng.next_i64_inclusive(-30, 30);
            let vertex_tz = rng.next_i64_inclusive(-30, 30);

            for (label, base_mesh) in &shared_vertex_bases {
                let transformed = transform_mesh_positions(base_mesh, |point| {
                    rigid_rotate_z_quarter_turns_then_translate(
                        point,
                        vertex_quarter_turns,
                        vertex_tx,
                        vertex_ty,
                        vertex_tz,
                    )
                });
                assert!(
                    transformed.is_valid(),
                    "rigidly transformed shared-vertex fixture should satisfy Phase 4 validity"
                );
                assert_allowed_contact_topology_classifier_matches_edge_index_oracle(&transformed);
                assert!(
                    transformed.check_no_forbidden_face_face_intersections(),
                    "shared-vertex fixture should remain intersection-free in randomized case {case_idx}"
                );

                let case_label = format!("{label}_random_case_{case_idx}");
                assert_shared_vertex_only_contacts_not_misclassified_as_forbidden_intersections(
                    &transformed,
                    &case_label,
                );
                let relabel_permutation = random_permutation(&mut rng, transformed.vertices.len());
                let relabeled =
                    relabel_mesh_vertices_for_testing(&transformed, &relabel_permutation)
                        .expect("vertex-relabeled shared-vertex fixture should build");
                assert!(
                    relabeled.is_valid(),
                    "vertex-relabeled shared-vertex fixture should satisfy Phase 4 validity in randomized case {case_idx}"
                );
                assert_allowed_contact_topology_classifier_matches_edge_index_oracle(&relabeled);
                assert!(
                    relabeled.check_no_forbidden_face_face_intersections(),
                    "vertex-relabeled shared-vertex fixture should remain intersection-free in randomized case {case_idx}"
                );
                let relabeled_case_label = format!("{label}_random_case_{case_idx}_relabeled");
                assert_shared_vertex_only_contacts_not_misclassified_as_forbidden_intersections(
                    &relabeled,
                    &relabeled_case_label,
                );

                let reflected = transform_mesh_positions(&transformed, reflect_point3_across_yz_plane);
                assert!(
                    reflected.is_valid(),
                    "reflected shared-vertex fixture should satisfy Phase 4 validity"
                );
                assert_allowed_contact_topology_classifier_matches_edge_index_oracle(&reflected);
                assert!(
                    reflected.check_no_forbidden_face_face_intersections(),
                    "reflected shared-vertex fixture should remain intersection-free in randomized case {case_idx}"
                );
                let reflected_case_label = format!("{label}_random_case_{case_idx}_reflected");
                assert_shared_vertex_only_contacts_not_misclassified_as_forbidden_intersections(
                    &reflected,
                    &reflected_case_label,
                );
                let reflected_relabel_permutation =
                    random_permutation(&mut rng, reflected.vertices.len());
                let reflected_relabeled = relabel_mesh_vertices_for_testing(
                    &reflected,
                    &reflected_relabel_permutation,
                )
                .expect("vertex-relabeled reflected shared-vertex fixture should build");
                assert!(
                    reflected_relabeled.is_valid(),
                    "vertex-relabeled reflected shared-vertex fixture should satisfy Phase 4 validity in randomized case {case_idx}"
                );
                assert_allowed_contact_topology_classifier_matches_edge_index_oracle(
                    &reflected_relabeled,
                );
                assert!(
                    reflected_relabeled.check_no_forbidden_face_face_intersections(),
                    "vertex-relabeled reflected shared-vertex fixture should remain intersection-free in randomized case {case_idx}"
                );
                let reflected_relabeled_case_label =
                    format!("{label}_random_case_{case_idx}_reflected_relabeled");
                assert_shared_vertex_only_contacts_not_misclassified_as_forbidden_intersections(
                    &reflected_relabeled,
                    &reflected_relabeled_case_label,
                );
            }
        }
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle() {
        let noncoplanar_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(0, 1, 0),
            RuntimePoint3::from_ints(0, 0, 1),
        ];
        let noncoplanar_faces = vec![vec![0, 1, 2, 3], vec![0, 3, 2, 1]];
        let noncoplanar_mesh = Mesh::from_face_cycles(noncoplanar_vertices, &noncoplanar_faces)
            .expect("noncoplanar face fixture should build");

        let collinear_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(2, 0, 0),
        ];
        let collinear_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let collinear_mesh =
            Mesh::from_face_cycles(collinear_vertices, &collinear_faces)
                .expect("collinear face fixture should build");

        let zero_length_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
        ];
        let zero_length_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let zero_length_mesh =
            Mesh::from_face_cycles(zero_length_vertices, &zero_length_faces)
                .expect("zero-length edge fixture should build");

        let mut disjoint_origins = Vec::new();
        for i in 0..8 {
            disjoint_origins.push((i * 10, 0, 0));
        }
        let disjoint_stress = build_disconnected_translated_tetrahedra_mesh(&disjoint_origins);

        let fixtures = vec![
            ("tetrahedron", Mesh::tetrahedron()),
            ("cube", Mesh::cube()),
            ("triangular_prism", Mesh::triangular_prism()),
            (
                "overlapping_disconnected_tetrahedra",
                build_overlapping_tetrahedra_mesh(),
            ),
            ("disconnected_stress", disjoint_stress),
            ("noncoplanar_face", noncoplanar_mesh),
            ("collinear_face", collinear_mesh),
            ("zero_length_edge", zero_length_mesh),
        ];

        for (label, mesh) in fixtures {
            assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(&mesh, label);
            let permutation: Vec<usize> = (0..mesh.vertices.len()).rev().collect();
            let relabeled = relabel_mesh_vertices_for_testing(&mesh, &permutation)
                .expect("vertex-relabeled coplanarity fixture should build");
            assert!(
                relabeled.is_valid(),
                "vertex-relabeled coplanarity fixture should preserve Phase 4 validity for {label}"
            );
            assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(
                &relabeled,
                &format!("{label}_relabeled"),
            );

            let reflected = transform_mesh_positions(&mesh, reflect_point3_across_yz_plane);
            assert!(
                reflected.is_valid(),
                "reflected coplanarity fixture should preserve Phase 4 validity for {label}"
            );
            assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(
                &reflected,
                &format!("{label}_reflected"),
            );
            let relabeled_reflected = relabel_mesh_vertices_for_testing(&reflected, &permutation)
                .expect("vertex-relabeled reflected coplanarity fixture should build");
            assert!(
                relabeled_reflected.is_valid(),
                "vertex-relabeled reflected coplanarity fixture should preserve Phase 4 validity for {label}"
            );
            assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(
                &relabeled_reflected,
                &format!("{label}_reflected_relabeled"),
            );
        }
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn seed0_fixed_witness_without_noncollinear_seed_is_insufficient_for_k_ge_5() {
        let p0 = RuntimePoint3::from_ints(0, 0, 0);
        let p1 = RuntimePoint3::from_ints(1, 0, 0);
        let p2 = RuntimePoint3::from_ints(2, 0, 0);
        let p3 = RuntimePoint3::from_ints(0, 1, 0);
        let p4 = RuntimePoint3::from_ints(0, 0, 1);

        // Seed witness (0,1,2) is vacuously true when the seed triple is collinear.
        assert!(coplanar(&p0, &p1, &p2, &p0));
        assert!(coplanar(&p0, &p1, &p2, &p1));
        assert!(coplanar(&p0, &p1, &p2, &p2));
        assert!(coplanar(&p0, &p1, &p2, &p3));
        assert!(coplanar(&p0, &p1, &p2, &p4));

        // But full all-quadruple coplanarity for five points fails.
        assert!(!coplanar(&p0, &p1, &p3, &p4));
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn differential_randomized_face_coplanarity_checker_exhaustive_quadruple_oracle_harness() {
        const CASES: usize = 40;
        let mut rng = DeterministicRng::new(0x4F21_BD68_90AE_13C7);

        let noncoplanar_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(0, 1, 0),
            RuntimePoint3::from_ints(0, 0, 1),
        ];
        let noncoplanar_faces = vec![vec![0, 1, 2, 3], vec![0, 3, 2, 1]];
        let noncoplanar_mesh = Mesh::from_face_cycles(noncoplanar_vertices, &noncoplanar_faces)
            .expect("noncoplanar face fixture should build");

        let collinear_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(2, 0, 0),
        ];
        let collinear_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let collinear_mesh = Mesh::from_face_cycles(collinear_vertices, &collinear_faces)
            .expect("collinear face fixture should build");

        let zero_length_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
        ];
        let zero_length_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let zero_length_mesh = Mesh::from_face_cycles(zero_length_vertices, &zero_length_faces)
            .expect("zero-length edge fixture should build");

        let failing_fixtures = vec![
            ("noncoplanar_face", noncoplanar_mesh),
            ("collinear_face", collinear_mesh),
            ("zero_length_edge", zero_length_mesh),
        ];
        for (label, mesh) in &failing_fixtures {
            assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(mesh, label);
        }

        for case_id in 0..CASES {
            let component_count = rng.next_usize_inclusive(2, 7);
            let disjoint_origins = random_well_separated_component_origins(&mut rng, component_count);
            let disjoint_mesh = build_disconnected_translated_tetrahedra_mesh(&disjoint_origins);
            assert!(
                disjoint_mesh.is_valid(),
                "generated disjoint fixture should satisfy Phase 4 validity"
            );
            assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(
                &disjoint_mesh,
                &format!("disjoint_case_{case_id}"),
            );
            let disjoint_permutation = random_permutation(&mut rng, disjoint_mesh.vertices.len());
            let relabeled_disjoint =
                relabel_mesh_vertices_for_testing(&disjoint_mesh, &disjoint_permutation)
                    .expect("vertex-relabeled disjoint coplanarity fixture should build");
            assert!(
                relabeled_disjoint.is_valid(),
                "vertex-relabeled disjoint coplanarity fixture should satisfy Phase 4 validity in case {case_id}"
            );
            assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(
                &relabeled_disjoint,
                &format!("disjoint_relabeled_case_{case_id}"),
            );

            let quarter_turns = rng.next_u64() % 4;
            let tx = rng.next_i64_inclusive(-25, 25);
            let ty = rng.next_i64_inclusive(-25, 25);
            let tz = rng.next_i64_inclusive(-25, 25);
            let rigid_disjoint = transform_mesh_positions(&disjoint_mesh, |point| {
                rigid_rotate_z_quarter_turns_then_translate(point, quarter_turns, tx, ty, tz)
            });
            assert!(
                rigid_disjoint.is_valid(),
                "rigidly transformed disjoint fixture should preserve Phase 4 validity"
            );
            assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(
                &rigid_disjoint,
                &format!("disjoint_rigid_case_{case_id}"),
            );
            let rigid_permutation = random_permutation(&mut rng, rigid_disjoint.vertices.len());
            let relabeled_rigid_disjoint =
                relabel_mesh_vertices_for_testing(&rigid_disjoint, &rigid_permutation)
                    .expect("vertex-relabeled rigid coplanarity fixture should build");
            assert!(
                relabeled_rigid_disjoint.is_valid(),
                "vertex-relabeled rigid coplanarity fixture should satisfy Phase 4 validity in case {case_id}"
            );
            assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(
                &relabeled_rigid_disjoint,
                &format!("disjoint_rigid_relabeled_case_{case_id}"),
            );

            let reflected_disjoint = transform_mesh_positions(&disjoint_mesh, |point| {
                let mirrored = reflect_point3_across_yz_plane(point);
                translate_point3(&mirrored, tx, ty, tz)
            });
            assert!(
                reflected_disjoint.is_valid(),
                "reflected disjoint coplanarity fixture should satisfy Phase 4 validity in case {case_id}"
            );
            assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(
                &reflected_disjoint,
                &format!("disjoint_reflected_case_{case_id}"),
            );
            let reflected_disjoint_permutation =
                random_permutation(&mut rng, reflected_disjoint.vertices.len());
            let relabeled_reflected_disjoint = relabel_mesh_vertices_for_testing(
                &reflected_disjoint,
                &reflected_disjoint_permutation,
            )
            .expect("vertex-relabeled reflected disjoint coplanarity fixture should build");
            assert!(
                relabeled_reflected_disjoint.is_valid(),
                "vertex-relabeled reflected disjoint coplanarity fixture should satisfy Phase 4 validity in case {case_id}"
            );
            assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(
                &relabeled_reflected_disjoint,
                &format!("disjoint_reflected_relabeled_case_{case_id}"),
            );

            let (source_component, perturbed_component) =
                pick_distinct_indices(&mut rng, component_count);
            let mut perturbed_origins = disjoint_origins.clone();
            let perturbation = match rng.next_u64() % 3 {
                0 => (0, 0, 0),
                1 => (1, 0, 0),
                _ => (0, 1, 0),
            };
            let (ox, oy, oz) = perturbed_origins[source_component];
            perturbed_origins[perturbed_component] = (
                ox + perturbation.0,
                oy + perturbation.1,
                oz + perturbation.2,
            );
            let perturbed_mesh = build_disconnected_translated_tetrahedra_mesh(&perturbed_origins);
            assert!(
                perturbed_mesh.is_valid(),
                "topology should remain valid under coordinate perturbations"
            );
            assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(
                &perturbed_mesh,
                &format!("perturbed_case_{case_id}"),
            );
            let perturbed_permutation = random_permutation(&mut rng, perturbed_mesh.vertices.len());
            let relabeled_perturbed =
                relabel_mesh_vertices_for_testing(&perturbed_mesh, &perturbed_permutation)
                    .expect("vertex-relabeled perturbed coplanarity fixture should build");
            assert!(
                relabeled_perturbed.is_valid(),
                "vertex-relabeled perturbed coplanarity fixture should satisfy Phase 4 validity in case {case_id}"
            );
            assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(
                &relabeled_perturbed,
                &format!("perturbed_relabeled_case_{case_id}"),
            );

            let reflected_perturbed = transform_mesh_positions(&perturbed_mesh, |point| {
                let mirrored = reflect_point3_across_yz_plane(point);
                translate_point3(&mirrored, tx, ty, tz)
            });
            assert!(
                reflected_perturbed.is_valid(),
                "reflected perturbed coplanarity fixture should satisfy Phase 4 validity in case {case_id}"
            );
            assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(
                &reflected_perturbed,
                &format!("perturbed_reflected_case_{case_id}"),
            );
            let reflected_perturbed_permutation =
                random_permutation(&mut rng, reflected_perturbed.vertices.len());
            let relabeled_reflected_perturbed = relabel_mesh_vertices_for_testing(
                &reflected_perturbed,
                &reflected_perturbed_permutation,
            )
            .expect("vertex-relabeled reflected perturbed coplanarity fixture should build");
            assert!(
                relabeled_reflected_perturbed.is_valid(),
                "vertex-relabeled reflected perturbed coplanarity fixture should satisfy Phase 4 validity in case {case_id}"
            );
            assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(
                &relabeled_reflected_perturbed,
                &format!("perturbed_reflected_relabeled_case_{case_id}"),
            );

            for (label, mesh) in &failing_fixtures {
                let fail_turns = rng.next_u64() % 4;
                let fail_tx = rng.next_i64_inclusive(-30, 30);
                let fail_ty = rng.next_i64_inclusive(-30, 30);
                let fail_tz = rng.next_i64_inclusive(-30, 30);
                let transformed = transform_mesh_positions(mesh, |point| {
                    rigid_rotate_z_quarter_turns_then_translate(
                        point,
                        fail_turns,
                        fail_tx,
                        fail_ty,
                        fail_tz,
                    )
                });
                assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(
                    &transformed,
                    &format!("{label}_rigid_case_{case_id}"),
                );
                let transformed_permutation =
                    random_permutation(&mut rng, transformed.vertices.len());
                let relabeled_transformed =
                    relabel_mesh_vertices_for_testing(&transformed, &transformed_permutation)
                        .expect("vertex-relabeled transformed failing coplanarity fixture should build");
                assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(
                    &relabeled_transformed,
                    &format!("{label}_rigid_relabeled_case_{case_id}"),
                );

                let reflected_transformed = transform_mesh_positions(&transformed, |point| {
                    let mirrored = reflect_point3_across_yz_plane(point);
                    translate_point3(&mirrored, fail_tx, fail_ty, fail_tz)
                });
                assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(
                    &reflected_transformed,
                    &format!("{label}_rigid_reflected_case_{case_id}"),
                );
                let reflected_transformed_permutation =
                    random_permutation(&mut rng, reflected_transformed.vertices.len());
                let relabeled_reflected_transformed = relabel_mesh_vertices_for_testing(
                    &reflected_transformed,
                    &reflected_transformed_permutation,
                )
                .expect(
                    "vertex-relabeled reflected transformed failing coplanarity fixture should build",
                );
                assert_face_coplanarity_checker_matches_exhaustive_face_quadruple_oracle(
                    &relabeled_reflected_transformed,
                    &format!("{label}_rigid_reflected_relabeled_case_{case_id}"),
                );
            }
        }
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn face_convexity_checker_matches_projected_orient2d_sign_oracle() {
        let noncoplanar_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(0, 1, 0),
            RuntimePoint3::from_ints(0, 0, 1),
        ];
        let noncoplanar_faces = vec![vec![0, 1, 2, 3], vec![0, 3, 2, 1]];
        let noncoplanar_mesh = Mesh::from_face_cycles(noncoplanar_vertices, &noncoplanar_faces)
            .expect("noncoplanar face fixture should build");

        let concave_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(2, 0, 0),
            RuntimePoint3::from_ints(2, 2, 0),
            RuntimePoint3::from_ints(1, 1, 0),
            RuntimePoint3::from_ints(0, 2, 0),
        ];
        let concave_faces = vec![vec![0, 1, 2, 3, 4], vec![0, 4, 3, 2, 1]];
        let concave_mesh = Mesh::from_face_cycles(concave_vertices, &concave_faces)
            .expect("concave face fixture should build");

        let collinear_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(2, 0, 0),
        ];
        let collinear_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let collinear_mesh =
            Mesh::from_face_cycles(collinear_vertices, &collinear_faces)
                .expect("collinear face fixture should build");

        let zero_length_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
        ];
        let zero_length_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let zero_length_mesh =
            Mesh::from_face_cycles(zero_length_vertices, &zero_length_faces)
                .expect("zero-length edge fixture should build");

        let tetrahedron = Mesh::tetrahedron();
        let cube = Mesh::cube();
        let triangular_prism = Mesh::triangular_prism();
        let overlapping_disconnected_tetrahedra = build_overlapping_tetrahedra_mesh();

        let reflected_tetrahedron =
            transform_mesh_positions(&tetrahedron, reflect_point3_across_yz_plane);
        let reflected_cube = transform_mesh_positions(&cube, reflect_point3_across_yz_plane);
        let reflected_triangular_prism =
            transform_mesh_positions(&triangular_prism, reflect_point3_across_yz_plane);
        let reflected_overlapping_disconnected_tetrahedra = transform_mesh_positions(
            &overlapping_disconnected_tetrahedra,
            reflect_point3_across_yz_plane,
        );
        let reflected_concave_mesh =
            transform_mesh_positions(&concave_mesh, reflect_point3_across_yz_plane);
        let reflected_noncoplanar_mesh =
            transform_mesh_positions(&noncoplanar_mesh, reflect_point3_across_yz_plane);
        let reflected_collinear_mesh =
            transform_mesh_positions(&collinear_mesh, reflect_point3_across_yz_plane);
        let reflected_zero_length_mesh =
            transform_mesh_positions(&zero_length_mesh, reflect_point3_across_yz_plane);

        let mut disjoint_origins = Vec::new();
        for i in 0..8 {
            disjoint_origins.push((i * 10, 0, 0));
        }
        let disjoint_stress = build_disconnected_translated_tetrahedra_mesh(&disjoint_origins);
        let reflected_disjoint_stress =
            transform_mesh_positions(&disjoint_stress, reflect_point3_across_yz_plane);

        let fixtures = vec![
            ("tetrahedron", tetrahedron),
            ("reflected_tetrahedron", reflected_tetrahedron),
            ("cube", cube),
            ("reflected_cube", reflected_cube),
            ("triangular_prism", triangular_prism),
            ("reflected_triangular_prism", reflected_triangular_prism),
            (
                "overlapping_disconnected_tetrahedra",
                overlapping_disconnected_tetrahedra,
            ),
            (
                "reflected_overlapping_disconnected_tetrahedra",
                reflected_overlapping_disconnected_tetrahedra,
            ),
            ("disconnected_stress", disjoint_stress),
            ("reflected_disconnected_stress", reflected_disjoint_stress),
            ("concave_face", concave_mesh),
            ("reflected_concave_face", reflected_concave_mesh),
            ("noncoplanar_face", noncoplanar_mesh),
            ("reflected_noncoplanar_face", reflected_noncoplanar_mesh),
            ("collinear_face", collinear_mesh),
            ("reflected_collinear_face", reflected_collinear_mesh),
            ("zero_length_edge", zero_length_mesh),
            ("reflected_zero_length_edge", reflected_zero_length_mesh),
        ];

        for (label, mesh) in fixtures {
            assert_face_convexity_checker_matches_projected_orient2d_oracle(&mesh, label);

            let reverse_permutation: Vec<usize> = (0..mesh.vertices.len()).rev().collect();
            let relabeled = relabel_mesh_vertices_for_testing(&mesh, &reverse_permutation)
                .expect("deterministic reverse-relabeled convexity fixture should build");
            assert!(
                relabeled.is_valid(),
                "deterministic reverse-relabeled convexity fixture should satisfy Phase 4 validity for {label}"
            );
            assert_face_convexity_checker_matches_projected_orient2d_oracle(
                &relabeled,
                &format!("{label}_deterministic_reverse_relabeled"),
            );
        }
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn differential_randomized_face_convexity_checker_projected_orient2d_oracle_harness() {
        const CASES: usize = 40;
        let mut rng = DeterministicRng::new(0xC0A2_3F57_9B1D_6E42);

        let noncoplanar_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(0, 1, 0),
            RuntimePoint3::from_ints(0, 0, 1),
        ];
        let noncoplanar_faces = vec![vec![0, 1, 2, 3], vec![0, 3, 2, 1]];
        let noncoplanar_mesh = Mesh::from_face_cycles(noncoplanar_vertices, &noncoplanar_faces)
            .expect("noncoplanar face fixture should build");

        let concave_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(2, 0, 0),
            RuntimePoint3::from_ints(2, 2, 0),
            RuntimePoint3::from_ints(1, 1, 0),
            RuntimePoint3::from_ints(0, 2, 0),
        ];
        let concave_faces = vec![vec![0, 1, 2, 3, 4], vec![0, 4, 3, 2, 1]];
        let concave_mesh = Mesh::from_face_cycles(concave_vertices, &concave_faces)
            .expect("concave face fixture should build");

        let collinear_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(2, 0, 0),
        ];
        let collinear_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let collinear_mesh = Mesh::from_face_cycles(collinear_vertices, &collinear_faces)
            .expect("collinear face fixture should build");

        let zero_length_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
        ];
        let zero_length_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let zero_length_mesh = Mesh::from_face_cycles(zero_length_vertices, &zero_length_faces)
            .expect("zero-length edge fixture should build");

        let failing_fixtures = vec![
            ("concave_face", concave_mesh),
            ("noncoplanar_face", noncoplanar_mesh),
            ("collinear_face", collinear_mesh),
            ("zero_length_edge", zero_length_mesh),
        ];
        for (label, mesh) in &failing_fixtures {
            assert_face_convexity_checker_matches_projected_orient2d_oracle(mesh, label);
        }

        for case_id in 0..CASES {
            let component_count = rng.next_usize_inclusive(2, 7);
            let disjoint_origins = random_well_separated_component_origins(&mut rng, component_count);
            let disjoint_mesh = build_disconnected_translated_tetrahedra_mesh(&disjoint_origins);
            assert!(
                disjoint_mesh.is_valid(),
                "generated disjoint fixture should satisfy Phase 4 validity"
            );
            assert_face_convexity_checker_matches_projected_orient2d_oracle(
                &disjoint_mesh,
                &format!("disjoint_case_{case_id}"),
            );
            let disjoint_permutation = random_permutation(&mut rng, disjoint_mesh.vertices.len());
            let relabeled_disjoint =
                relabel_mesh_vertices_for_testing(&disjoint_mesh, &disjoint_permutation)
                    .expect("vertex-relabeled disjoint convexity fixture should build");
            assert!(
                relabeled_disjoint.is_valid(),
                "vertex-relabeled disjoint convexity fixture should satisfy Phase 4 validity in case {case_id}"
            );
            assert_face_convexity_checker_matches_projected_orient2d_oracle(
                &relabeled_disjoint,
                &format!("disjoint_relabeled_case_{case_id}"),
            );
            let reflected_disjoint =
                transform_mesh_positions(&disjoint_mesh, reflect_point3_across_yz_plane);
            assert!(
                reflected_disjoint.is_valid(),
                "reflected disjoint convexity fixture should satisfy Phase 4 validity in case {case_id}"
            );
            assert_face_convexity_checker_matches_projected_orient2d_oracle(
                &reflected_disjoint,
                &format!("disjoint_reflected_case_{case_id}"),
            );
            let reflected_disjoint_permutation =
                random_permutation(&mut rng, reflected_disjoint.vertices.len());
            let relabeled_reflected_disjoint =
                relabel_mesh_vertices_for_testing(&reflected_disjoint, &reflected_disjoint_permutation)
                    .expect("vertex-relabeled reflected disjoint convexity fixture should build");
            assert!(
                relabeled_reflected_disjoint.is_valid(),
                "vertex-relabeled reflected disjoint convexity fixture should satisfy Phase 4 validity in case {case_id}"
            );
            assert_face_convexity_checker_matches_projected_orient2d_oracle(
                &relabeled_reflected_disjoint,
                &format!("disjoint_reflected_relabeled_case_{case_id}"),
            );

            let quarter_turns = rng.next_u64() % 4;
            let tx = rng.next_i64_inclusive(-25, 25);
            let ty = rng.next_i64_inclusive(-25, 25);
            let tz = rng.next_i64_inclusive(-25, 25);
            let rigid_disjoint = transform_mesh_positions(&disjoint_mesh, |point| {
                rigid_rotate_z_quarter_turns_then_translate(point, quarter_turns, tx, ty, tz)
            });
            assert!(
                rigid_disjoint.is_valid(),
                "rigidly transformed disjoint fixture should preserve Phase 4 validity"
            );
            assert_face_convexity_checker_matches_projected_orient2d_oracle(
                &rigid_disjoint,
                &format!("disjoint_rigid_case_{case_id}"),
            );
            let rigid_permutation = random_permutation(&mut rng, rigid_disjoint.vertices.len());
            let relabeled_rigid_disjoint =
                relabel_mesh_vertices_for_testing(&rigid_disjoint, &rigid_permutation)
                    .expect("vertex-relabeled rigid convexity fixture should build");
            assert!(
                relabeled_rigid_disjoint.is_valid(),
                "vertex-relabeled rigid convexity fixture should satisfy Phase 4 validity in case {case_id}"
            );
            assert_face_convexity_checker_matches_projected_orient2d_oracle(
                &relabeled_rigid_disjoint,
                &format!("disjoint_rigid_relabeled_case_{case_id}"),
            );
            let reflected_rigid_disjoint =
                transform_mesh_positions(&rigid_disjoint, reflect_point3_across_yz_plane);
            assert!(
                reflected_rigid_disjoint.is_valid(),
                "reflected rigid convexity fixture should satisfy Phase 4 validity in case {case_id}"
            );
            assert_face_convexity_checker_matches_projected_orient2d_oracle(
                &reflected_rigid_disjoint,
                &format!("disjoint_rigid_reflected_case_{case_id}"),
            );
            let reflected_rigid_permutation =
                random_permutation(&mut rng, reflected_rigid_disjoint.vertices.len());
            let relabeled_reflected_rigid_disjoint = relabel_mesh_vertices_for_testing(
                &reflected_rigid_disjoint,
                &reflected_rigid_permutation,
            )
            .expect("vertex-relabeled reflected rigid convexity fixture should build");
            assert!(
                relabeled_reflected_rigid_disjoint.is_valid(),
                "vertex-relabeled reflected rigid convexity fixture should satisfy Phase 4 validity in case {case_id}"
            );
            assert_face_convexity_checker_matches_projected_orient2d_oracle(
                &relabeled_reflected_rigid_disjoint,
                &format!("disjoint_rigid_reflected_relabeled_case_{case_id}"),
            );

            let (source_component, perturbed_component) =
                pick_distinct_indices(&mut rng, component_count);
            let mut perturbed_origins = disjoint_origins.clone();
            let perturbation = match rng.next_u64() % 3 {
                0 => (0, 0, 0),
                1 => (1, 0, 0),
                _ => (0, 1, 0),
            };
            let (ox, oy, oz) = perturbed_origins[source_component];
            perturbed_origins[perturbed_component] = (
                ox + perturbation.0,
                oy + perturbation.1,
                oz + perturbation.2,
            );
            let perturbed_mesh = build_disconnected_translated_tetrahedra_mesh(&perturbed_origins);
            assert!(
                perturbed_mesh.is_valid(),
                "topology should remain valid under coordinate perturbations"
            );
            assert_face_convexity_checker_matches_projected_orient2d_oracle(
                &perturbed_mesh,
                &format!("perturbed_case_{case_id}"),
            );
            let perturbed_permutation = random_permutation(&mut rng, perturbed_mesh.vertices.len());
            let relabeled_perturbed =
                relabel_mesh_vertices_for_testing(&perturbed_mesh, &perturbed_permutation)
                    .expect("vertex-relabeled perturbed convexity fixture should build");
            assert!(
                relabeled_perturbed.is_valid(),
                "vertex-relabeled perturbed convexity fixture should satisfy Phase 4 validity in case {case_id}"
            );
            assert_face_convexity_checker_matches_projected_orient2d_oracle(
                &relabeled_perturbed,
                &format!("perturbed_relabeled_case_{case_id}"),
            );
            let reflected_perturbed =
                transform_mesh_positions(&perturbed_mesh, reflect_point3_across_yz_plane);
            assert!(
                reflected_perturbed.is_valid(),
                "reflected perturbed convexity fixture should satisfy Phase 4 validity in case {case_id}"
            );
            assert_face_convexity_checker_matches_projected_orient2d_oracle(
                &reflected_perturbed,
                &format!("perturbed_reflected_case_{case_id}"),
            );
            let reflected_perturbed_permutation =
                random_permutation(&mut rng, reflected_perturbed.vertices.len());
            let relabeled_reflected_perturbed =
                relabel_mesh_vertices_for_testing(&reflected_perturbed, &reflected_perturbed_permutation)
                    .expect("vertex-relabeled reflected perturbed convexity fixture should build");
            assert!(
                relabeled_reflected_perturbed.is_valid(),
                "vertex-relabeled reflected perturbed convexity fixture should satisfy Phase 4 validity in case {case_id}"
            );
            assert_face_convexity_checker_matches_projected_orient2d_oracle(
                &relabeled_reflected_perturbed,
                &format!("perturbed_reflected_relabeled_case_{case_id}"),
            );

            for (label, mesh) in &failing_fixtures {
                let fail_turns = rng.next_u64() % 4;
                let fail_tx = rng.next_i64_inclusive(-30, 30);
                let fail_ty = rng.next_i64_inclusive(-30, 30);
                let fail_tz = rng.next_i64_inclusive(-30, 30);
                let transformed = transform_mesh_positions(mesh, |point| {
                    rigid_rotate_z_quarter_turns_then_translate(
                        point,
                        fail_turns,
                        fail_tx,
                        fail_ty,
                        fail_tz,
                    )
                });
                assert_face_convexity_checker_matches_projected_orient2d_oracle(
                    &transformed,
                    &format!("{label}_rigid_case_{case_id}"),
                );
                let transformed_permutation =
                    random_permutation(&mut rng, transformed.vertices.len());
                let relabeled_transformed =
                    relabel_mesh_vertices_for_testing(&transformed, &transformed_permutation)
                        .expect("vertex-relabeled transformed failing convexity fixture should build");
                assert_face_convexity_checker_matches_projected_orient2d_oracle(
                    &relabeled_transformed,
                    &format!("{label}_rigid_relabeled_case_{case_id}"),
                );
                let reflected_transformed =
                    transform_mesh_positions(&transformed, reflect_point3_across_yz_plane);
                assert_face_convexity_checker_matches_projected_orient2d_oracle(
                    &reflected_transformed,
                    &format!("{label}_rigid_reflected_case_{case_id}"),
                );
                let reflected_transformed_permutation =
                    random_permutation(&mut rng, reflected_transformed.vertices.len());
                let relabeled_reflected_transformed = relabel_mesh_vertices_for_testing(
                    &reflected_transformed,
                    &reflected_transformed_permutation,
                )
                .expect(
                    "vertex-relabeled reflected transformed failing convexity fixture should build",
                );
                assert_face_convexity_checker_matches_projected_orient2d_oracle(
                    &relabeled_reflected_transformed,
                    &format!("{label}_rigid_reflected_relabeled_case_{case_id}"),
                );
            }
        }
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn differential_randomized_forbidden_intersection_checker_harness() {
        const CASES: usize = 40;
        let mut rng = DeterministicRng::new(0xD1FFEA5E);

        for _ in 0..CASES {
            let component_count = rng.next_usize_inclusive(2, 7);
            let disjoint_origins =
                random_well_separated_component_origins(&mut rng, component_count);

            let disjoint_mesh =
                build_disconnected_translated_tetrahedra_mesh(&disjoint_origins);
            assert!(
                disjoint_mesh.is_valid(),
                "generated disjoint fixture should satisfy Phase 4 validity"
            );
            assert_forbidden_face_face_checker_broad_phase_sound(&disjoint_mesh);
            assert_eq!(
                disjoint_mesh.check_geometric_topological_consistency(),
                disjoint_mesh
                    .check_geometric_topological_consistency_diagnostic()
                    .is_ok()
            );

            let quarter_turns = rng.next_u64() % 4;
            let tx = rng.next_i64_inclusive(-25, 25);
            let ty = rng.next_i64_inclusive(-25, 25);
            let tz = rng.next_i64_inclusive(-25, 25);
            let rigid_disjoint = transform_mesh_positions(&disjoint_mesh, |point| {
                rigid_rotate_z_quarter_turns_then_translate(point, quarter_turns, tx, ty, tz)
            });
            assert!(
                rigid_disjoint.is_valid(),
                "rigidly transformed fixture should preserve Phase 4 validity"
            );
            assert_forbidden_face_face_checker_broad_phase_sound(&rigid_disjoint);
            assert_eq!(
                rigid_disjoint.check_geometric_topological_consistency(),
                rigid_disjoint
                    .check_geometric_topological_consistency_diagnostic()
                    .is_ok()
            );

            let (source_component, perturbed_component) =
                pick_distinct_indices(&mut rng, component_count);
            let mut perturbed_origins = disjoint_origins.clone();
            let perturbation = match rng.next_u64() % 3 {
                0 => (0, 0, 0),
                1 => (1, 0, 0),
                _ => (0, 1, 0),
            };
            let (ox, oy, oz) = perturbed_origins[source_component];
            perturbed_origins[perturbed_component] =
                (ox + perturbation.0, oy + perturbation.1, oz + perturbation.2);

            let perturbed_mesh =
                build_disconnected_translated_tetrahedra_mesh(&perturbed_origins);
            assert!(
                perturbed_mesh.is_valid(),
                "topology should remain valid under coordinate perturbations"
            );
            assert_forbidden_face_face_checker_broad_phase_sound(&perturbed_mesh);
            assert_eq!(
                perturbed_mesh.check_geometric_topological_consistency(),
                perturbed_mesh
                    .check_geometric_topological_consistency_diagnostic()
                    .is_ok()
            );

            if perturbation == (0, 0, 0) {
                assert!(
                    !perturbed_mesh.check_no_forbidden_face_face_intersections(),
                    "exactly overlapping disconnected components must be rejected"
                );
            }
        }
    }

    #[test]
    fn empty_mesh_fails_euler_gate() {
        let mesh = Mesh {
            vertices: vec![],
            edges: vec![],
            faces: vec![],
            half_edges: vec![],
        };
        assert!(!mesh.is_structurally_valid());
        assert_eq!(mesh.component_count(), 0);
        assert_eq!(mesh.euler_characteristics_per_component(), Vec::<isize>::new());
        assert!(!mesh.check_euler_formula_closed_components());
        assert!(!mesh.is_valid());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn phase5_geometry_checks_require_phase4_validity() {
        let mesh = Mesh {
            vertices: vec![super::Vertex {
                position: RuntimePoint3::from_ints(0, 0, 0),
                half_edge: 0,
            }],
            edges: vec![super::Edge { half_edge: 0 }],
            faces: vec![super::Face { half_edge: 0 }],
            half_edges: vec![
                super::HalfEdge {
                    vertex: 0,
                    twin: 1,
                    next: 0,
                    prev: 0,
                    edge: 0,
                    face: 0,
                },
                super::HalfEdge {
                    vertex: 0,
                    twin: 1,
                    next: 1,
                    prev: 1,
                    edge: 0,
                    face: 0,
                },
            ],
        };

        assert!(!mesh.is_valid());
        assert!(!mesh.check_no_zero_length_geometric_edges());
        assert!(!mesh.check_face_corner_non_collinearity());
        assert!(!mesh.check_face_coplanarity());
        assert!(!mesh.check_face_convexity());
        assert!(!mesh.check_face_plane_consistency());
        assert!(!mesh.check_shared_edge_local_orientation_consistency());
        assert!(!mesh.check_no_forbidden_face_face_intersections());
        assert!(!mesh.check_outward_face_normals());
        assert!(!mesh.check_geometric_topological_consistency());
        assert!(!mesh.is_valid_with_geometry());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn geometric_consistency_diagnostic_agrees_with_boolean_gate() {
        let passing_meshes = [Mesh::tetrahedron(), Mesh::cube(), Mesh::triangular_prism()];
        for mesh in &passing_meshes {
            assert!(mesh.check_geometric_topological_consistency());
            assert_eq!(
                mesh.check_geometric_topological_consistency(),
                mesh.check_geometric_topological_consistency_diagnostic().is_ok()
            );
        }

        let zero_length_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
        ];
        let zero_length_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let zero_length_mesh = Mesh::from_face_cycles(zero_length_vertices, &zero_length_faces)
            .expect("zero-length-edge fixture should build");
        assert!(!zero_length_mesh.check_geometric_topological_consistency());
        assert_eq!(
            zero_length_mesh.check_geometric_topological_consistency(),
            zero_length_mesh
                .check_geometric_topological_consistency_diagnostic()
                .is_ok()
        );
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn geometric_consistency_constructive_gate_matches_runtime_boolean_gate() {
        let passing_meshes = [Mesh::tetrahedron(), Mesh::cube(), Mesh::triangular_prism()];
        for (idx, mesh) in passing_meshes.iter().enumerate() {
            let label = format!("passing_fixture_{idx}");
            assert_constructive_phase5_gate_parity(mesh, &label);
        }

        let intersecting_mesh = build_overlapping_tetrahedra_mesh();
        assert_constructive_phase5_gate_parity(
            &intersecting_mesh,
            "overlapping_disconnected_tetrahedra",
        );

        let disconnected_stress =
            build_disconnected_translated_tetrahedra_mesh(&[(0, 0, 0), (12, 0, 0), (0, 12, 0)]);
        assert_constructive_phase5_gate_parity(
            &disconnected_stress,
            "disconnected_stress_fixture",
        );

        let noncoplanar_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(1, 1, 1),
            RuntimePoint3::from_ints(0, 1, 0),
        ];
        let noncoplanar_faces = vec![
            vec![0, 1, 2, 3],
            vec![0, 3, 2, 1],
        ];
        let noncoplanar_mesh = Mesh::from_face_cycles(noncoplanar_vertices, &noncoplanar_faces)
            .expect("noncoplanar quad fixture should build");
        assert_constructive_phase5_gate_parity(&noncoplanar_mesh, "noncoplanar_quad_fixture");
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn face_coplanarity_seed0_bridge_matches_runtime_checker() {
        let noncoplanar_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(1, 1, 1),
            RuntimePoint3::from_ints(0, 1, 0),
        ];
        let noncoplanar_faces = vec![vec![0, 1, 2, 3], vec![0, 3, 2, 1]];
        let noncoplanar_mesh = Mesh::from_face_cycles(noncoplanar_vertices, &noncoplanar_faces)
            .expect("noncoplanar face fixture should build");

        let collinear_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(2, 0, 0),
        ];
        let collinear_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let collinear_mesh = Mesh::from_face_cycles(collinear_vertices, &collinear_faces)
            .expect("collinear face fixture should build");

        let zero_length_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
        ];
        let zero_length_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let zero_length_mesh = Mesh::from_face_cycles(zero_length_vertices, &zero_length_faces)
            .expect("zero-length edge fixture should build");

        let fixtures = vec![
            ("tetrahedron", Mesh::tetrahedron()),
            ("cube", Mesh::cube()),
            ("triangular_prism", Mesh::triangular_prism()),
            ("overlapping_disconnected_tetrahedra", build_overlapping_tetrahedra_mesh()),
            ("noncoplanar_face", noncoplanar_mesh),
            ("collinear_face", collinear_mesh),
            ("zero_length_edge", zero_length_mesh),
        ];

        for (label, mesh) in fixtures {
            assert_face_coplanarity_runtime_seed0_bridge_parity(&mesh, label);
        }
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn face_coplanarity_seed0_sound_bridge_matches_runtime_checker() {
        let noncoplanar_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(1, 1, 1),
            RuntimePoint3::from_ints(0, 1, 0),
        ];
        let noncoplanar_faces = vec![vec![0, 1, 2, 3], vec![0, 3, 2, 1]];
        let noncoplanar_mesh = Mesh::from_face_cycles(noncoplanar_vertices, &noncoplanar_faces)
            .expect("noncoplanar face fixture should build");

        let collinear_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(2, 0, 0),
        ];
        let collinear_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let collinear_mesh = Mesh::from_face_cycles(collinear_vertices, &collinear_faces)
            .expect("collinear face fixture should build");

        let zero_length_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
        ];
        let zero_length_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let zero_length_mesh = Mesh::from_face_cycles(zero_length_vertices, &zero_length_faces)
            .expect("zero-length edge fixture should build");

        let fixtures = vec![
            ("tetrahedron", Mesh::tetrahedron()),
            ("cube", Mesh::cube()),
            ("triangular_prism", Mesh::triangular_prism()),
            ("overlapping_disconnected_tetrahedra", build_overlapping_tetrahedra_mesh()),
            ("noncoplanar_face", noncoplanar_mesh),
            ("collinear_face", collinear_mesh),
            ("zero_length_edge", zero_length_mesh),
        ];

        for (label, mesh) in fixtures {
            assert_face_coplanarity_runtime_seed0_sound_bridge_parity(&mesh, label);
        }
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn face_coplanarity_seed0_triangle_or_quad_sound_bridge_matches_runtime_checker() {
        let noncoplanar_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(1, 1, 1),
            RuntimePoint3::from_ints(0, 1, 0),
        ];
        let noncoplanar_faces = vec![vec![0, 1, 2, 3], vec![0, 3, 2, 1]];
        let noncoplanar_mesh = Mesh::from_face_cycles(noncoplanar_vertices, &noncoplanar_faces)
            .expect("noncoplanar face fixture should build");

        let collinear_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(2, 0, 0),
        ];
        let collinear_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let collinear_mesh = Mesh::from_face_cycles(collinear_vertices, &collinear_faces)
            .expect("collinear face fixture should build");

        let zero_length_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
        ];
        let zero_length_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let zero_length_mesh = Mesh::from_face_cycles(zero_length_vertices, &zero_length_faces)
            .expect("zero-length edge fixture should build");

        let fixtures = vec![
            ("tetrahedron", Mesh::tetrahedron()),
            ("cube", Mesh::cube()),
            ("triangular_prism", Mesh::triangular_prism()),
            ("overlapping_disconnected_tetrahedra", build_overlapping_tetrahedra_mesh()),
            (
                "reflected_cube_outward_failure",
                build_reflected_cube_outward_failure_mesh(),
            ),
            ("noncoplanar_face", noncoplanar_mesh),
            ("collinear_face", collinear_mesh),
            ("zero_length_edge", zero_length_mesh),
        ];

        for (label, mesh) in fixtures {
            assert!(mesh_all_faces_are_triangles_or_quads(&mesh));
            assert_face_coplanarity_runtime_seed0_triangle_or_quad_sound_bridge_parity(
                &mesh, label,
            );
        }
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn face_coplanarity_seed0_triangle_or_quad_sound_complete_bridge_matches_runtime_checker() {
        let noncoplanar_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(1, 1, 1),
            RuntimePoint3::from_ints(0, 1, 0),
        ];
        let noncoplanar_faces = vec![vec![0, 1, 2, 3], vec![0, 3, 2, 1]];
        let noncoplanar_mesh = Mesh::from_face_cycles(noncoplanar_vertices, &noncoplanar_faces)
            .expect("noncoplanar face fixture should build");

        let collinear_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(2, 0, 0),
        ];
        let collinear_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let collinear_mesh = Mesh::from_face_cycles(collinear_vertices, &collinear_faces)
            .expect("collinear face fixture should build");

        let zero_length_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
        ];
        let zero_length_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let zero_length_mesh = Mesh::from_face_cycles(zero_length_vertices, &zero_length_faces)
            .expect("zero-length edge fixture should build");

        let fixtures = vec![
            ("tetrahedron", Mesh::tetrahedron()),
            ("cube", Mesh::cube()),
            ("triangular_prism", Mesh::triangular_prism()),
            ("overlapping_disconnected_tetrahedra", build_overlapping_tetrahedra_mesh()),
            (
                "reflected_cube_outward_failure",
                build_reflected_cube_outward_failure_mesh(),
            ),
            ("noncoplanar_face", noncoplanar_mesh),
            ("collinear_face", collinear_mesh),
            ("zero_length_edge", zero_length_mesh),
        ];

        for (label, mesh) in fixtures {
            assert!(mesh_all_faces_are_triangles_or_quads(&mesh));
            assert_face_coplanarity_seed0_triangle_or_quad_sound_complete_bridge_parity(
                &mesh, label,
            );
        }
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn face_convexity_triangle_projected_turn_sound_bridge_matches_runtime_checker() {
        let collinear_mesh = build_collinear_single_triangle_pair_mesh();

        let zero_length_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
        ];
        let zero_length_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let zero_length_mesh = Mesh::from_face_cycles(zero_length_vertices, &zero_length_faces)
            .expect("zero-length triangle fixture should build");

        let fixtures = vec![
            ("tetrahedron", Mesh::tetrahedron()),
            ("overlapping_disconnected_tetrahedra", build_overlapping_tetrahedra_mesh()),
            ("collinear_face", collinear_mesh),
            ("zero_length_edge", zero_length_mesh),
        ];

        for (label, mesh) in fixtures {
            assert!(mesh_all_faces_are_triangles(&mesh));
            assert_face_convexity_triangle_projected_turn_sound_bridge_parity(&mesh, label);
        }
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn face_coplanarity_seed0_phase5_runtime_bundle_completeness_bridge_matches_geometric_sound_bridge(
    ) {
        let noncoplanar_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(1, 1, 1),
            RuntimePoint3::from_ints(0, 1, 0),
        ];
        let noncoplanar_faces = vec![vec![0, 1, 2, 3], vec![0, 3, 2, 1]];
        let noncoplanar_mesh = Mesh::from_face_cycles(noncoplanar_vertices, &noncoplanar_faces)
            .expect("noncoplanar face fixture should build");

        let fixtures = vec![
            ("tetrahedron", Mesh::tetrahedron()),
            ("cube", Mesh::cube()),
            ("triangular_prism", Mesh::triangular_prism()),
            ("overlapping_disconnected_tetrahedra", build_overlapping_tetrahedra_mesh()),
            ("noncoplanar_face", noncoplanar_mesh),
        ];

        for (label, mesh) in fixtures {
            assert_face_coplanarity_seed0_phase5_runtime_bundle_completeness_bridge_parity(
                &mesh, label,
            );
        }
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn face_coplanarity_seed0_oriented_plane_completeness_bridge_matches_geometric_sound_bridge() {
        let noncoplanar_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(1, 1, 1),
            RuntimePoint3::from_ints(0, 1, 0),
        ];
        let noncoplanar_faces = vec![vec![0, 1, 2, 3], vec![0, 3, 2, 1]];
        let noncoplanar_mesh = Mesh::from_face_cycles(noncoplanar_vertices, &noncoplanar_faces)
            .expect("noncoplanar face fixture should build");

        let fixtures = vec![
            ("tetrahedron", Mesh::tetrahedron()),
            ("cube", Mesh::cube()),
            ("triangular_prism", Mesh::triangular_prism()),
            ("overlapping_disconnected_tetrahedra", build_overlapping_tetrahedra_mesh()),
            ("noncoplanar_face", noncoplanar_mesh),
        ];

        for (label, mesh) in fixtures {
            assert_face_coplanarity_seed0_oriented_plane_completeness_bridge_parity(&mesh, label);
        }
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn face_coplanarity_seed0_oriented_plane_triangle_completeness_bridge_matches_geometric_sound_bridge(
    ) {
        let reflected_tetrahedron = transform_mesh_positions(&Mesh::tetrahedron(), |point| {
            let mirrored = reflect_point3_across_yz_plane(point);
            translate_point3(&mirrored, 5, -2, 7)
        });

        let fixtures = vec![
            ("tetrahedron", Mesh::tetrahedron()),
            (
                "overlapping_disconnected_tetrahedra",
                build_overlapping_tetrahedra_mesh(),
            ),
            ("reflected_tetrahedron", reflected_tetrahedron),
        ];

        for (label, mesh) in fixtures {
            assert!(mesh_all_faces_are_triangles(&mesh));
            assert_face_coplanarity_seed0_oriented_plane_triangle_completeness_bridge_parity(
                &mesh, label,
            );
        }
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn face_coplanarity_seed0_oriented_plane_quad_completeness_bridge_matches_geometric_sound_bridge(
    ) {
        let fixtures = vec![
            ("cube", Mesh::cube()),
            (
                "reflected_cube_outward_failure",
                build_reflected_cube_outward_failure_mesh(),
            ),
            (
                "noncoplanar_single_quad_double_face_lift1",
                build_noncoplanar_single_quad_double_face_mesh_with_lift(1),
            ),
        ];

        for (label, mesh) in fixtures {
            assert!(mesh_all_faces_are_quads(&mesh));
            assert_face_coplanarity_seed0_oriented_plane_quad_completeness_bridge_parity(
                &mesh, label,
            );
        }
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn face_coplanarity_seed0_oriented_plane_triangle_or_quad_completeness_bridge_matches_geometric_sound_bridge(
    ) {
        let fixtures = vec![
            ("tetrahedron", Mesh::tetrahedron()),
            ("cube", Mesh::cube()),
            ("triangular_prism", Mesh::triangular_prism()),
            (
                "overlapping_disconnected_tetrahedra",
                build_overlapping_tetrahedra_mesh(),
            ),
            (
                "reflected_cube_outward_failure",
                build_reflected_cube_outward_failure_mesh(),
            ),
            (
                "noncoplanar_single_quad_double_face_lift1",
                build_noncoplanar_single_quad_double_face_mesh_with_lift(1),
            ),
        ];

        for (label, mesh) in fixtures {
            assert!(mesh_all_faces_are_triangles_or_quads(&mesh));
            assert_face_coplanarity_seed0_oriented_plane_triangle_or_quad_completeness_bridge_parity(
                &mesh, label,
            );
        }
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn noncoplanar_fixture_keeps_phase4_and_shared_edge_orientation_but_fails_aggregate_gate() {
        let mesh = build_noncoplanar_single_quad_double_face_mesh_with_lift(1);
        assert_phase4_shared_edge_spec_characterization_gap(
            &mesh,
            "noncoplanar_quad_lift1",
            Phase4SharedEdgeSpecGapFailure::NonCoplanar,
        );
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn collinear_fixture_keeps_phase4_and_shared_edge_orientation_but_fails_aggregate_gate() {
        let mesh = build_collinear_single_triangle_pair_mesh();
        assert_phase4_shared_edge_spec_characterization_gap(
            &mesh,
            "collinear_triangle_pair",
            Phase4SharedEdgeSpecGapFailure::CollinearCorner,
        );
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn concave_fixture_keeps_phase4_and_shared_edge_orientation_but_fails_aggregate_gate() {
        let mesh = build_concave_single_face_pair_mesh();
        assert_phase4_shared_edge_spec_characterization_gap(
            &mesh,
            "concave_face_pair",
            Phase4SharedEdgeSpecGapFailure::NonConvex,
        );
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn overlapping_fixture_keeps_phase4_and_shared_edge_orientation_but_fails_aggregate_gate() {
        let mesh = build_overlapping_tetrahedra_mesh();
        assert_phase4_shared_edge_spec_characterization_gap(
            &mesh,
            "overlapping_disconnected_tetrahedra",
            Phase4SharedEdgeSpecGapFailure::ForbiddenIntersection,
        );
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn reflected_fixture_keeps_phase4_and_shared_edge_orientation_but_fails_aggregate_gate() {
        let mesh = build_reflected_cube_outward_failure_mesh();
        assert_phase4_shared_edge_spec_characterization_gap(
            &mesh,
            "reflected_cube_outward_failure",
            Phase4SharedEdgeSpecGapFailure::InwardOrDegenerate,
        );
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn differential_randomized_noncoplanar_phase4_shared_edge_spec_gap_harness() {
        const CASES: usize = 40;
        let mut rng = DeterministicRng::new(0x9A73_2CD1_4E80_B5F2);

        for case_id in 0..CASES {
            let lift_z = rng.next_i64_inclusive(1, 9);
            let base_mesh = build_noncoplanar_single_quad_double_face_mesh_with_lift(lift_z);
            assert_phase4_shared_edge_spec_characterization_gap(
                &base_mesh,
                &format!("noncoplanar_lift_case_{case_id}_z{lift_z}"),
                Phase4SharedEdgeSpecGapFailure::NonCoplanar,
            );

            let quarter_turns = rng.next_u64() % 4;
            let tx = rng.next_i64_inclusive(-30, 30);
            let ty = rng.next_i64_inclusive(-30, 30);
            let tz = rng.next_i64_inclusive(-30, 30);
            let rigid_mesh = transform_mesh_positions(&base_mesh, |point| {
                rigid_rotate_z_quarter_turns_then_translate(
                    point,
                    quarter_turns,
                    tx,
                    ty,
                    tz,
                )
            });
            assert_phase4_shared_edge_spec_characterization_gap(
                &rigid_mesh,
                &format!("noncoplanar_lift_case_{case_id}_rigid"),
                Phase4SharedEdgeSpecGapFailure::NonCoplanar,
            );

            let reflected_mesh = transform_mesh_positions(&base_mesh, |point| {
                let mirrored = reflect_point3_across_yz_plane(point);
                rigid_rotate_z_quarter_turns_then_translate(
                    &mirrored,
                    quarter_turns,
                    tx,
                    ty,
                    tz,
                )
            });
            assert_phase4_shared_edge_spec_characterization_gap(
                &reflected_mesh,
                &format!("noncoplanar_lift_case_{case_id}_reflected"),
                Phase4SharedEdgeSpecGapFailure::NonCoplanar,
            );
        }
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn differential_randomized_multiclass_phase4_shared_edge_spec_gap_harness() {
        const CASES: usize = 40;
        let mut rng = DeterministicRng::new(0x74A1_B50C_9D2F_3E68);

        for case_id in 0..CASES {
            let lift_z = rng.next_i64_inclusive(1, 9);
            let base_fixtures = vec![
                (
                    "collinear",
                    build_collinear_single_triangle_pair_mesh(),
                    Phase4SharedEdgeSpecGapFailure::CollinearCorner,
                ),
                (
                    "noncoplanar",
                    build_noncoplanar_single_quad_double_face_mesh_with_lift(lift_z),
                    Phase4SharedEdgeSpecGapFailure::NonCoplanar,
                ),
                (
                    "concave",
                    build_concave_single_face_pair_mesh(),
                    Phase4SharedEdgeSpecGapFailure::NonConvex,
                ),
                (
                    "overlapping",
                    build_overlapping_tetrahedra_mesh(),
                    Phase4SharedEdgeSpecGapFailure::ForbiddenIntersection,
                ),
                (
                    "reflected",
                    build_reflected_cube_outward_failure_mesh(),
                    Phase4SharedEdgeSpecGapFailure::InwardOrDegenerate,
                ),
            ];

            for (fixture_label, base_mesh, expected_failure) in base_fixtures {
                assert_phase4_shared_edge_spec_characterization_gap(
                    &base_mesh,
                    &format!("{fixture_label}_gap_case_{case_id}_base"),
                    expected_failure,
                );

                let quarter_turns = rng.next_u64() % 4;
                let tx = rng.next_i64_inclusive(-30, 30);
                let ty = rng.next_i64_inclusive(-30, 30);
                let tz = rng.next_i64_inclusive(-30, 30);
                let rigid_mesh = transform_mesh_positions(&base_mesh, |point| {
                    rigid_rotate_z_quarter_turns_then_translate(
                        point,
                        quarter_turns,
                        tx,
                        ty,
                        tz,
                    )
                });
                assert_phase4_shared_edge_spec_characterization_gap(
                    &rigid_mesh,
                    &format!("{fixture_label}_gap_case_{case_id}_rigid"),
                    expected_failure,
                );
            }
        }
    }

    #[cfg(all(feature = "geometry-checks", feature = "verus-proofs"))]
    #[test]
    fn differential_randomized_constructive_geometric_gate_parity_harness() {
        const CASES: usize = 40;
        let mut rng = DeterministicRng::new(0x8C95_DA41_2B7E_4F11);

        for case_id in 0..CASES {
            let component_count = rng.next_usize_inclusive(2, 5);
            let disjoint_origins =
                random_well_separated_component_origins(&mut rng, component_count);
            let disjoint_mesh = build_disconnected_translated_tetrahedra_mesh(&disjoint_origins);
            assert!(
                disjoint_mesh.is_valid(),
                "generated disjoint fixture should preserve Phase 4 validity"
            );
            assert_constructive_phase5_gate_parity(
                &disjoint_mesh,
                &format!("random_disjoint_case_{case_id}"),
            );

            let quarter_turns = rng.next_u64() % 4;
            let tx = rng.next_i64_inclusive(-15, 15);
            let ty = rng.next_i64_inclusive(-15, 15);
            let tz = rng.next_i64_inclusive(-15, 15);
            let rigid_disjoint = transform_mesh_positions(&disjoint_mesh, |point| {
                rigid_rotate_z_quarter_turns_then_translate(point, quarter_turns, tx, ty, tz)
            });
            assert!(
                rigid_disjoint.is_valid(),
                "rigidly transformed disjoint fixture should preserve Phase 4 validity"
            );
            assert_constructive_phase5_gate_parity(
                &rigid_disjoint,
                &format!("random_disjoint_rigid_case_{case_id}"),
            );

            let (source_component, perturbed_component) =
                pick_distinct_indices(&mut rng, component_count);
            let mut perturbed_origins = disjoint_origins.clone();
            let touch_mode = rng.next_usize_inclusive(0, 2);
            let (ox, oy, oz) = perturbed_origins[source_component];
            perturbed_origins[perturbed_component] = match touch_mode {
                0 => (ox, oy, oz),
                1 => (ox + 1, oy, oz),
                _ => (ox, oy, oz + 1),
            };
            let perturbed_mesh = build_disconnected_translated_tetrahedra_mesh(&perturbed_origins);
            assert!(
                perturbed_mesh.is_valid(),
                "perturbed fixture should preserve Phase 4 validity"
            );
            assert_constructive_phase5_gate_parity(
                &perturbed_mesh,
                &format!("random_perturbed_case_{case_id}"),
            );
        }
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn geometric_consistency_diagnostic_returns_first_failure_witness() {
        let invalid_mesh = Mesh {
            vertices: vec![super::Vertex {
                position: RuntimePoint3::from_ints(0, 0, 0),
                half_edge: 0,
            }],
            edges: vec![super::Edge { half_edge: 0 }],
            faces: vec![super::Face { half_edge: 0 }],
            half_edges: vec![
                super::HalfEdge {
                    vertex: 0,
                    twin: 1,
                    next: 0,
                    prev: 0,
                    edge: 0,
                    face: 0,
                },
                super::HalfEdge {
                    vertex: 0,
                    twin: 1,
                    next: 1,
                    prev: 1,
                    edge: 0,
                    face: 0,
                },
            ],
        };
        let invalid_failure = invalid_mesh
            .check_geometric_topological_consistency_diagnostic()
            .expect_err("invalid mesh should fail phase-4 gate");
        assert!(matches!(
            invalid_failure,
            GeometricTopologicalConsistencyFailure::Phase4Validity
        ));
        assert!(diagnostic_witness_is_real_counterexample(
            &invalid_mesh,
            &invalid_failure
        ));

        let zero_length_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
        ];
        let zero_length_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let zero_length_mesh = Mesh::from_face_cycles(zero_length_vertices, &zero_length_faces)
            .expect("zero-length-edge fixture should build");
        let zero_length_failure = zero_length_mesh
            .check_geometric_topological_consistency_diagnostic()
            .expect_err("zero-length fixture should fail");
        assert!(matches!(
            zero_length_failure,
            GeometricTopologicalConsistencyFailure::ZeroLengthGeometricEdge { .. }
        ));
        assert!(diagnostic_witness_is_real_counterexample(
            &zero_length_mesh,
            &zero_length_failure
        ));

        let collinear_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(2, 0, 0),
        ];
        let collinear_faces = vec![vec![0, 1, 2], vec![0, 2, 1]];
        let collinear_mesh = Mesh::from_face_cycles(collinear_vertices, &collinear_faces)
            .expect("collinear fixture should build");
        let collinear_failure = collinear_mesh
            .check_geometric_topological_consistency_diagnostic()
            .expect_err("collinear fixture should fail");
        assert!(matches!(
            collinear_failure,
            GeometricTopologicalConsistencyFailure::FaceCornerCollinear { .. }
        ));
        assert!(diagnostic_witness_is_real_counterexample(
            &collinear_mesh,
            &collinear_failure
        ));

        let noncoplanar_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(0, 1, 0),
            RuntimePoint3::from_ints(0, 0, 1),
        ];
        let noncoplanar_faces = vec![vec![0, 1, 2, 3], vec![0, 3, 2, 1]];
        let noncoplanar_mesh = Mesh::from_face_cycles(noncoplanar_vertices, &noncoplanar_faces)
            .expect("noncoplanar fixture should build");
        let noncoplanar_failure = noncoplanar_mesh
            .check_geometric_topological_consistency_diagnostic()
            .expect_err("noncoplanar fixture should fail");
        assert!(matches!(
            noncoplanar_failure,
            GeometricTopologicalConsistencyFailure::FaceNonCoplanar { .. }
        ));
        assert!(diagnostic_witness_is_real_counterexample(
            &noncoplanar_mesh,
            &noncoplanar_failure
        ));

        let concave_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(2, 0, 0),
            RuntimePoint3::from_ints(2, 2, 0),
            RuntimePoint3::from_ints(1, 1, 0),
            RuntimePoint3::from_ints(0, 2, 0),
        ];
        let concave_faces = vec![vec![0, 1, 2, 3, 4], vec![0, 4, 3, 2, 1]];
        let concave_mesh = Mesh::from_face_cycles(concave_vertices, &concave_faces)
            .expect("concave fixture should build");
        let concave_failure = concave_mesh
            .check_geometric_topological_consistency_diagnostic()
            .expect_err("concave fixture should fail");
        assert!(matches!(
            concave_failure,
            GeometricTopologicalConsistencyFailure::FaceNonConvex { .. }
        ));
        assert!(diagnostic_witness_is_real_counterexample(
            &concave_mesh,
            &concave_failure
        ));

        let intersecting_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(4, 0, 0),
            RuntimePoint3::from_ints(0, 4, 0),
            RuntimePoint3::from_ints(0, 0, 4),
            RuntimePoint3::from_ints(1, 1, 1),
            RuntimePoint3::from_ints(5, 1, 1),
            RuntimePoint3::from_ints(1, 5, 1),
            RuntimePoint3::from_ints(1, 1, 5),
        ];
        let intersecting_faces = vec![
            vec![0, 1, 2],
            vec![0, 3, 1],
            vec![1, 3, 2],
            vec![2, 3, 0],
            vec![4, 5, 6],
            vec![4, 7, 5],
            vec![5, 7, 6],
            vec![6, 7, 4],
        ];
        let intersecting_mesh = Mesh::from_face_cycles(intersecting_vertices, &intersecting_faces)
            .expect("intersecting fixture should build");
        let intersecting_failure = intersecting_mesh
            .check_geometric_topological_consistency_diagnostic()
            .expect_err("intersecting fixture should fail");
        assert!(matches!(
            intersecting_failure,
            GeometricTopologicalConsistencyFailure::ForbiddenFaceFaceIntersection { .. }
        ));
        assert!(diagnostic_witness_is_real_counterexample(
            &intersecting_mesh,
            &intersecting_failure
        ));

        let flipped_vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(0, 1, 0),
            RuntimePoint3::from_ints(0, 0, 1),
        ];
        let flipped_faces = vec![vec![0, 2, 1], vec![0, 1, 3], vec![1, 2, 3], vec![2, 0, 3]];
        let flipped_mesh = Mesh::from_face_cycles(flipped_vertices, &flipped_faces)
            .expect("inward-winding tetrahedron should build");
        let flipped_failure = flipped_mesh
            .check_geometric_topological_consistency_diagnostic()
            .expect_err("inward-winding tetrahedron should fail");
        assert!(matches!(
            flipped_failure,
            GeometricTopologicalConsistencyFailure::InwardOrDegenerateComponent { .. }
        ));
        assert!(diagnostic_witness_is_real_counterexample(
            &flipped_mesh,
            &flipped_failure
        ));
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn geometric_consistency_diagnostic_rejects_fabricated_witnesses() {
        let mesh = Mesh::tetrahedron();
        assert!(mesh.check_geometric_topological_consistency());

        let fake_plane = GeometricTopologicalConsistencyFailure::FacePlaneInconsistent {
            face: 0,
            half_edge: mesh.faces[0].half_edge,
        };
        assert!(!diagnostic_witness_is_real_counterexample(&mesh, &fake_plane));

        let fake_shared_edge =
            GeometricTopologicalConsistencyFailure::SharedEdgeOrientationInconsistent {
                half_edge: 0,
                twin_half_edge: mesh.half_edges[0].twin,
            };
        assert!(!diagnostic_witness_is_real_counterexample(
            &mesh,
            &fake_shared_edge
        ));

        let fake_internal = GeometricTopologicalConsistencyFailure::InternalInconsistency;
        assert!(!diagnostic_witness_is_real_counterexample(&mesh, &fake_internal));
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn collinear_triangle_faces_fail_geometric_nondegeneracy() {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(2, 0, 0),
        ];
        let faces = vec![vec![0, 1, 2], vec![0, 2, 1]];

        let mesh = Mesh::from_face_cycles(vertices, &faces)
            .expect("closed opposite-orientation collinear triangles should build");
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        assert!(mesh.check_no_zero_length_geometric_edges());
        assert!(!mesh.check_face_corner_non_collinearity());
        assert!(!mesh.check_face_coplanarity());
        assert!(mesh.compute_face_plane(0).is_none());
        assert!(mesh.compute_face_plane(1).is_none());
        assert!(!mesh.check_face_convexity());
        assert!(!mesh.check_face_plane_consistency());
        assert!(!mesh.check_geometric_topological_consistency());
        assert!(!mesh.is_valid_with_geometry());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn coincident_edge_endpoints_fail_zero_length_geometric_edge_check() {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
        ];
        let faces = vec![vec![0, 1, 2], vec![0, 2, 1]];

        let mesh = Mesh::from_face_cycles(vertices, &faces)
            .expect("closed opposite-orientation triangle pair should build");
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        assert!(!mesh.check_no_zero_length_geometric_edges());
        assert!(!mesh.check_face_corner_non_collinearity());
        assert!(!mesh.check_face_coplanarity());
        assert!(!mesh.check_face_convexity());
        assert!(!mesh.check_face_plane_consistency());
        assert!(!mesh.check_geometric_topological_consistency());
        assert!(!mesh.is_valid_with_geometry());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn noncoplanar_quad_faces_fail_face_coplanarity() {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(0, 1, 0),
            RuntimePoint3::from_ints(0, 0, 1),
        ];
        let faces = vec![vec![0, 1, 2, 3], vec![0, 3, 2, 1]];

        let mesh = Mesh::from_face_cycles(vertices, &faces)
            .expect("closed opposite-orientation noncoplanar quad faces should build");
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        assert!(mesh.check_no_zero_length_geometric_edges());
        assert!(mesh.check_face_corner_non_collinearity());
        assert!(!mesh.check_face_coplanarity());
        assert!(!mesh.check_face_convexity());
        assert!(!mesh.check_face_plane_consistency());
        assert!(!mesh.check_geometric_topological_consistency());
        assert!(!mesh.is_valid_with_geometry());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn concave_polygon_faces_fail_face_convexity() {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(2, 0, 0),
            RuntimePoint3::from_ints(2, 2, 0),
            RuntimePoint3::from_ints(1, 1, 0),
            RuntimePoint3::from_ints(0, 2, 0),
        ];
        let faces = vec![vec![0, 1, 2, 3, 4], vec![0, 4, 3, 2, 1]];

        let mesh = Mesh::from_face_cycles(vertices, &faces)
            .expect("closed opposite-orientation concave polygon faces should build");
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        assert!(mesh.check_no_zero_length_geometric_edges());
        assert!(mesh.check_face_corner_non_collinearity());
        assert!(mesh.check_face_coplanarity());
        assert!(!mesh.check_face_convexity());
        assert!(mesh.check_face_plane_consistency());
        assert!(!mesh.check_geometric_topological_consistency());
        assert!(!mesh.is_valid_with_geometry());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn compute_face_plane_returns_expected_values_for_cube_bottom_face() {
        let mesh = Mesh::cube();
        assert!(mesh.is_valid());

        let (normal, offset) = mesh.compute_face_plane(0).expect("cube bottom face should yield a plane");
        assert_eq!(*normal.x(), RuntimeScalar::from_int(0));
        assert_eq!(*normal.y(), RuntimeScalar::from_int(0));
        assert_eq!(*normal.z(), RuntimeScalar::from_int(4));
        assert_eq!(offset, RuntimeScalar::from_int(-4));
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn canonicalize_plane_normalizes_sign_and_scale() {
        let normal = RuntimeVec3::from_ints(0, 0, 4);
        let offset = RuntimeScalar::from_int(-4);
        let scale = RuntimeScalar::from_int(-3);
        let scaled_normal = normal.scale(&scale);
        let scaled_offset = offset.mul(&scale);

        let canonical = Mesh::canonicalize_plane(&normal, &offset)
            .expect("non-zero normal should canonicalize");
        let scaled_canonical = Mesh::canonicalize_plane(&scaled_normal, &scaled_offset)
            .expect("scaled non-zero normal should canonicalize");

        assert_eq!(canonical, scaled_canonical);
        assert_eq!(*canonical.0.x(), RuntimeScalar::from_int(0));
        assert_eq!(*canonical.0.y(), RuntimeScalar::from_int(0));
        assert_eq!(*canonical.0.z(), RuntimeScalar::from_int(1));
        assert_eq!(canonical.1, RuntimeScalar::from_int(-1));
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn compute_face_plane_canonical_returns_expected_values_for_cube_bottom_face() {
        let mesh = Mesh::cube();
        assert!(mesh.is_valid());

        let (normal, offset) = mesh.compute_face_plane_canonical(0)
            .expect("cube bottom face should yield a canonical plane");
        assert_eq!(*normal.x(), RuntimeScalar::from_int(0));
        assert_eq!(*normal.y(), RuntimeScalar::from_int(0));
        assert_eq!(*normal.z(), RuntimeScalar::from_int(1));
        assert_eq!(offset, RuntimeScalar::from_int(-1));
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn canonical_face_plane_is_stable_under_cycle_rotation_with_collinear_seed_prefix() {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(2, 0, 0),
            RuntimePoint3::from_ints(2, 1, 0),
            RuntimePoint3::from_ints(0, 1, 0),
            RuntimePoint3::from_ints(0, 0, 1),
            RuntimePoint3::from_ints(1, 0, 1),
            RuntimePoint3::from_ints(2, 0, 1),
            RuntimePoint3::from_ints(2, 1, 1),
            RuntimePoint3::from_ints(0, 1, 1),
        ];
        let faces = vec![
            vec![0, 1, 2, 3, 4],
            vec![5, 9, 8, 7, 6],
            vec![0, 5, 6, 1],
            vec![1, 6, 7, 2],
            vec![2, 7, 8, 3],
            vec![3, 8, 9, 4],
            vec![4, 9, 5, 0],
        ];
        assert!(collinear3d(
            &vertices[faces[0][0]],
            &vertices[faces[0][1]],
            &vertices[faces[0][2]]
        ));

        let mut faces_rotated_by_one = faces.clone();
        faces_rotated_by_one[0].rotate_left(1);
        let mut faces_rotated_by_two = faces.clone();
        faces_rotated_by_two[0].rotate_left(2);
        assert!(!collinear3d(
            &vertices[faces_rotated_by_one[0][0]],
            &vertices[faces_rotated_by_one[0][1]],
            &vertices[faces_rotated_by_one[0][2]]
        ));
        assert!(!collinear3d(
            &vertices[faces_rotated_by_two[0][0]],
            &vertices[faces_rotated_by_two[0][1]],
            &vertices[faces_rotated_by_two[0][2]]
        ));

        let base = Mesh::from_face_cycles(vertices.clone(), &faces)
            .expect("baseline prism with collinear face prefix should build");
        let rotated_by_one = Mesh::from_face_cycles(vertices.clone(), &faces_rotated_by_one)
            .expect("cycle-rotated-by-one prism should build");
        let rotated_by_two = Mesh::from_face_cycles(vertices, &faces_rotated_by_two)
            .expect("cycle-rotated-by-two prism should build");
        assert!(base.is_valid());
        assert!(rotated_by_one.is_valid());
        assert!(rotated_by_two.is_valid());

        let base_plane = base
            .compute_face_plane(0)
            .expect("baseline face plane should exist");
        let rotated_by_one_plane = rotated_by_one
            .compute_face_plane(0)
            .expect("rotated-by-one face plane should exist");
        let rotated_by_two_plane = rotated_by_two
            .compute_face_plane(0)
            .expect("rotated-by-two face plane should exist");

        assert_eq!(base_plane, rotated_by_one_plane);
        assert_ne!(base_plane, rotated_by_two_plane);

        let base_canonical = base
            .compute_face_plane_canonical(0)
            .expect("baseline canonical face plane should exist");
        assert_eq!(
            base_canonical,
            rotated_by_one
                .compute_face_plane_canonical(0)
                .expect("rotated-by-one canonical face plane should exist")
        );
        assert_eq!(
            base_canonical,
            rotated_by_two
                .compute_face_plane_canonical(0)
                .expect("rotated-by-two canonical face plane should exist")
        );
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn flipped_face_winding_fails_outward_normal_check() {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(0, 1, 0),
            RuntimePoint3::from_ints(0, 0, 1),
        ];
        let faces = vec![vec![0, 2, 1], vec![0, 1, 3], vec![1, 2, 3], vec![2, 0, 3]];

        let mesh = Mesh::from_face_cycles(vertices, &faces)
            .expect("closed tetrahedron with inward winding should build");
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        assert!(mesh.check_no_zero_length_geometric_edges());
        assert!(mesh.check_face_corner_non_collinearity());
        assert!(mesh.check_face_coplanarity());
        assert!(mesh.check_face_convexity());
        assert!(mesh.check_face_plane_consistency());
        assert!(mesh.check_shared_edge_local_orientation_consistency());
        assert!(!mesh.check_outward_face_normals());
        assert!(!mesh.check_geometric_topological_consistency());
        assert!(!mesh.is_valid_with_geometry());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn nonadjacent_face_intersection_fails_self_intersection_checker() {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(4, 0, 0),
            RuntimePoint3::from_ints(0, 4, 0),
            RuntimePoint3::from_ints(0, 0, 4),
            RuntimePoint3::from_ints(1, 1, 1),
            RuntimePoint3::from_ints(5, 1, 1),
            RuntimePoint3::from_ints(1, 5, 1),
            RuntimePoint3::from_ints(1, 1, 5),
        ];
        let faces = vec![
            vec![0, 1, 2],
            vec![0, 3, 1],
            vec![1, 3, 2],
            vec![2, 3, 0],
            vec![4, 5, 6],
            vec![4, 7, 5],
            vec![5, 7, 6],
            vec![6, 7, 4],
        ];

        let mesh = Mesh::from_face_cycles(vertices, &faces)
            .expect("two overlapping tetrahedra should still build topologically");
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        assert!(mesh.check_no_zero_length_geometric_edges());
        assert!(mesh.check_face_corner_non_collinearity());
        assert!(mesh.check_face_coplanarity());
        assert!(mesh.check_face_convexity());
        assert!(mesh.check_face_plane_consistency());
        assert!(mesh.check_shared_edge_local_orientation_consistency());
        assert!(mesh.check_outward_face_normals());
        assert!(!mesh.check_no_forbidden_face_face_intersections());
        assert!(!mesh.check_geometric_topological_consistency());
        assert!(!mesh.is_valid_with_geometry());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn coplanar_neighboring_faces_policy_split_prism_side_is_accepted() {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(2, 0, 0),
            RuntimePoint3::from_ints(1, 2, 0),
            RuntimePoint3::from_ints(0, 0, 1),
            RuntimePoint3::from_ints(2, 0, 1),
            RuntimePoint3::from_ints(1, 2, 1),
        ];
        let faces = vec![
            vec![0, 1, 2],
            vec![3, 5, 4],
            vec![0, 3, 4],
            vec![0, 4, 1],
            vec![1, 4, 5, 2],
            vec![2, 5, 3, 0],
        ];

        let mesh = Mesh::from_face_cycles(vertices, &faces)
            .expect("split-side triangular prism should build");
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        assert!(mesh.check_no_zero_length_geometric_edges());
        assert!(mesh.check_face_corner_non_collinearity());
        assert!(mesh.check_face_coplanarity());
        assert!(mesh.check_face_convexity());
        assert!(mesh.check_face_plane_consistency());
        assert!(mesh.check_shared_edge_local_orientation_consistency());
        assert!(mesh.check_no_forbidden_face_face_intersections());
        assert!(mesh.check_outward_face_normals());
        assert!(mesh.check_geometric_topological_consistency());
        assert!(mesh.is_valid_with_geometry());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn shared_vertex_only_face_contact_is_allowed_when_geometrically_limited_to_that_vertex() {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 1),
            RuntimePoint3::from_ints(0, 0, -1),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(0, 1, 0),
            RuntimePoint3::from_ints(-1, 0, 0),
            RuntimePoint3::from_ints(0, -1, 0),
        ];
        let faces = vec![
            vec![0, 3, 2],
            vec![0, 4, 3],
            vec![0, 5, 4],
            vec![0, 2, 5],
            vec![1, 2, 3],
            vec![1, 3, 4],
            vec![1, 4, 5],
            vec![1, 5, 2],
        ];

        let mesh = Mesh::from_face_cycles(vertices, &faces)
            .expect("octahedron fixture should build");
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        assert!(mesh.check_no_zero_length_geometric_edges());
        assert!(mesh.check_face_corner_non_collinearity());
        assert!(mesh.check_face_coplanarity());
        assert!(mesh.check_face_convexity());
        assert!(mesh.check_face_plane_consistency());
        assert!(mesh.check_shared_edge_local_orientation_consistency());
        assert!(mesh.check_no_forbidden_face_face_intersections());
        assert!(mesh.check_outward_face_normals());
        assert!(mesh.check_geometric_topological_consistency());
        assert!(mesh.is_valid_with_geometry());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn coplanar_neighboring_faces_policy_coincident_double_face_is_rejected() {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 1),
            RuntimePoint3::from_ints(1, 0, 1),
            RuntimePoint3::from_ints(0, 1, 1),
        ];
        let faces = vec![vec![0, 1, 2], vec![0, 2, 1]];

        let mesh = Mesh::from_face_cycles(vertices, &faces)
            .expect("coincident opposite-orientation triangles should build");
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        assert!(mesh.check_no_zero_length_geometric_edges());
        assert!(mesh.check_face_corner_non_collinearity());
        assert!(mesh.check_face_coplanarity());
        assert!(mesh.check_face_convexity());
        assert!(mesh.check_face_plane_consistency());
        assert!(mesh.check_shared_edge_local_orientation_consistency());
        assert!(!mesh.check_no_forbidden_face_face_intersections());
        assert!(matches!(
            mesh.check_geometric_topological_consistency_diagnostic(),
            Err(GeometricTopologicalConsistencyFailure::ForbiddenFaceFaceIntersection { .. })
        ));
        assert!(!mesh.check_outward_face_normals());
        assert!(!mesh.check_geometric_topological_consistency());
        assert!(!mesh.is_valid_with_geometry());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn vertex_touch_only_components_policy_separated_components_are_accepted() {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(0, 1, 0),
            RuntimePoint3::from_ints(0, 0, 1),
            RuntimePoint3::from_ints(10, 0, 0),
            RuntimePoint3::from_ints(11, 0, 0),
            RuntimePoint3::from_ints(10, 1, 0),
            RuntimePoint3::from_ints(10, 0, 1),
        ];
        let faces = vec![
            vec![0, 1, 2],
            vec![0, 3, 1],
            vec![1, 3, 2],
            vec![2, 3, 0],
            vec![4, 5, 6],
            vec![4, 7, 5],
            vec![5, 7, 6],
            vec![6, 7, 4],
        ];

        let mesh = Mesh::from_face_cycles(vertices, &faces)
            .expect("separated tetrahedra should build");
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        assert!(mesh.check_no_zero_length_geometric_edges());
        assert!(mesh.check_face_corner_non_collinearity());
        assert!(mesh.check_face_coplanarity());
        assert!(mesh.check_face_convexity());
        assert!(mesh.check_face_plane_consistency());
        assert!(mesh.check_shared_edge_local_orientation_consistency());
        assert!(mesh.check_no_forbidden_face_face_intersections());
        assert!(mesh.check_outward_face_normals());
        assert!(mesh.check_geometric_topological_consistency());
        assert!(mesh.is_valid_with_geometry());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn vertex_touch_only_components_policy_position_touch_is_rejected() {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(0, 1, 0),
            RuntimePoint3::from_ints(0, 0, 1),
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(-1, 0, 0),
            RuntimePoint3::from_ints(0, -1, 0),
            RuntimePoint3::from_ints(0, 0, -1),
        ];
        let faces = vec![
            vec![0, 1, 2],
            vec![0, 3, 1],
            vec![1, 3, 2],
            vec![2, 3, 0],
            vec![4, 5, 6],
            vec![4, 7, 5],
            vec![5, 7, 6],
            vec![6, 7, 4],
        ];

        let mesh = Mesh::from_face_cycles(vertices, &faces)
            .expect("vertex-touch-only tetrahedra should still build topologically");
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        assert!(mesh.check_no_zero_length_geometric_edges());
        assert!(mesh.check_face_corner_non_collinearity());
        assert!(mesh.check_face_coplanarity());
        assert!(mesh.check_face_convexity());
        assert!(mesh.check_face_plane_consistency());
        assert!(mesh.check_shared_edge_local_orientation_consistency());
        assert!(!mesh.check_no_forbidden_face_face_intersections());
        assert!(!mesh.check_geometric_topological_consistency());
        assert!(!mesh.is_valid_with_geometry());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn edge_touch_only_components_policy_is_rejected() {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(0, 1, 0),
            RuntimePoint3::from_ints(0, 0, 1),
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(0, -1, 0),
            RuntimePoint3::from_ints(0, 0, -1),
        ];
        let faces = vec![
            vec![0, 1, 2],
            vec![0, 3, 1],
            vec![1, 3, 2],
            vec![2, 3, 0],
            vec![4, 5, 6],
            vec![4, 7, 5],
            vec![5, 7, 6],
            vec![6, 7, 4],
        ];

        let mesh = Mesh::from_face_cycles(vertices, &faces)
            .expect("edge-touch-only tetrahedra should still build topologically");
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        assert!(mesh.check_no_zero_length_geometric_edges());
        assert!(mesh.check_face_corner_non_collinearity());
        assert!(mesh.check_face_coplanarity());
        assert!(mesh.check_face_convexity());
        assert!(mesh.check_face_plane_consistency());
        assert!(mesh.check_shared_edge_local_orientation_consistency());
        assert!(!mesh.check_no_forbidden_face_face_intersections());
        let failure = mesh
            .check_geometric_topological_consistency_diagnostic()
            .expect_err("edge-touch-only components should fail geometric consistency");
        assert!(matches!(
            failure,
            GeometricTopologicalConsistencyFailure::ForbiddenFaceFaceIntersection { .. }
        ));
        assert!(!mesh.check_geometric_topological_consistency());
        assert!(!mesh.is_valid_with_geometry());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn face_touch_only_components_policy_is_rejected() {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(0, 1, 0),
            RuntimePoint3::from_ints(0, 0, 1),
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(0, 1, 0),
            RuntimePoint3::from_ints(0, 0, -1),
        ];
        let faces = vec![
            vec![0, 1, 2],
            vec![0, 3, 1],
            vec![1, 3, 2],
            vec![2, 3, 0],
            vec![4, 5, 6],
            vec![4, 7, 5],
            vec![5, 7, 6],
            vec![6, 7, 4],
        ];

        let mesh = Mesh::from_face_cycles(vertices, &faces)
            .expect("face-touch-only tetrahedra should still build topologically");
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        assert!(mesh.check_no_zero_length_geometric_edges());
        assert!(mesh.check_face_corner_non_collinearity());
        assert!(mesh.check_face_coplanarity());
        assert!(mesh.check_face_convexity());
        assert!(mesh.check_face_plane_consistency());
        assert!(mesh.check_shared_edge_local_orientation_consistency());
        assert!(!mesh.check_no_forbidden_face_face_intersections());
        let failure = mesh
            .check_geometric_topological_consistency_diagnostic()
            .expect_err("face-touch-only components should fail geometric consistency");
        assert!(matches!(
            failure,
            GeometricTopologicalConsistencyFailure::ForbiddenFaceFaceIntersection { .. }
        ));
        assert!(!mesh.check_geometric_topological_consistency());
        assert!(!mesh.is_valid_with_geometry());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn zero_volume_policy_nonzero_tetrahedron_is_accepted() {
        let mesh = Mesh::tetrahedron();
        assert!(mesh.is_valid());
        assert!(mesh.check_outward_face_normals());
        assert!(mesh.check_geometric_topological_consistency());
    }

    #[cfg(feature = "geometry-checks")]
    #[test]
    fn zero_volume_policy_planar_closed_component_is_rejected() {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 1),
            RuntimePoint3::from_ints(1, 0, 1),
            RuntimePoint3::from_ints(0, 1, 1),
        ];
        let faces = vec![vec![0, 1, 2], vec![0, 2, 1]];

        let mesh = Mesh::from_face_cycles(vertices, &faces)
            .expect("planar closed two-face component should build");
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        assert!(mesh.check_no_zero_length_geometric_edges());
        assert!(mesh.check_face_corner_non_collinearity());
        assert!(mesh.check_face_coplanarity());
        assert!(mesh.check_face_convexity());
        assert!(mesh.check_face_plane_consistency());
        assert!(mesh.check_shared_edge_local_orientation_consistency());
        assert!(!mesh.check_no_forbidden_face_face_intersections());
        assert!(matches!(
            mesh.check_geometric_topological_consistency_diagnostic(),
            Err(GeometricTopologicalConsistencyFailure::ForbiddenFaceFaceIntersection { .. })
        ));
        assert!(!mesh.check_outward_face_normals());
        assert!(!mesh.check_geometric_topological_consistency());
        assert!(!mesh.is_valid_with_geometry());
    }

    #[test]
    fn self_loop_face_cycle_can_build_but_is_not_structurally_valid() {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
        ];
        let faces = vec![vec![0, 0, 1]];
        let out = Mesh::from_face_cycles(vertices, &faces);
        assert_eq!(
            out,
            Err(MeshBuildError::DegenerateOrientedEdge {
                face: 0,
                index: 0,
                vertex: 0,
            })
        );
    }

    #[test]
    fn broken_twin_involution_fails_twin_check() {
        let mesh = Mesh {
            vertices: vec![super::Vertex {
                position: RuntimePoint3::from_ints(0, 0, 0),
                half_edge: 0,
            }],
            edges: vec![super::Edge { half_edge: 0 }],
            faces: vec![super::Face { half_edge: 0 }],
            half_edges: vec![
                super::HalfEdge {
                    vertex: 0,
                    twin: 1,
                    next: 0,
                    prev: 0,
                    edge: 0,
                    face: 0,
                },
                super::HalfEdge {
                    vertex: 0,
                    twin: 1,
                    next: 1,
                    prev: 1,
                    edge: 0,
                    face: 0,
                },
            ],
        };

        assert!(!mesh.check_twin_involution());
        #[cfg(feature = "verus-proofs")]
        assert!(!mesh.check_twin_involution_via_kernel());
    }

    #[test]
    fn broken_prev_next_inverse_fails_prev_inverse_check() {
        let mesh = Mesh {
            vertices: vec![super::Vertex {
                position: RuntimePoint3::from_ints(0, 0, 0),
                half_edge: 0,
            }],
            edges: vec![super::Edge { half_edge: 0 }],
            faces: vec![super::Face { half_edge: 0 }],
            half_edges: vec![
                super::HalfEdge {
                    vertex: 0,
                    twin: 0,
                    next: 1,
                    prev: 0,
                    edge: 0,
                    face: 0,
                },
                super::HalfEdge {
                    vertex: 0,
                    twin: 1,
                    next: 0,
                    prev: 1,
                    edge: 0,
                    face: 0,
                },
            ],
        };

        assert!(!mesh.check_prev_inverse_of_next());
        #[cfg(feature = "verus-proofs")]
        assert!(!mesh.check_prev_inverse_of_next_via_kernel());
    }

    #[test]
    fn edge_with_three_incident_half_edges_fails_edge_cardinality_check() {
        let mesh = Mesh {
            vertices: vec![super::Vertex {
                position: RuntimePoint3::from_ints(0, 0, 0),
                half_edge: 0,
            }],
            edges: vec![super::Edge { half_edge: 0 }],
            faces: vec![super::Face { half_edge: 0 }],
            half_edges: vec![
                super::HalfEdge {
                    vertex: 0,
                    twin: 0,
                    next: 0,
                    prev: 0,
                    edge: 0,
                    face: 0,
                },
                super::HalfEdge {
                    vertex: 0,
                    twin: 1,
                    next: 1,
                    prev: 1,
                    edge: 0,
                    face: 0,
                },
                super::HalfEdge {
                    vertex: 0,
                    twin: 2,
                    next: 2,
                    prev: 2,
                    edge: 0,
                    face: 0,
                },
            ],
        };

        assert!(!mesh.check_edge_has_exactly_two_half_edges());
        #[cfg(feature = "verus-proofs")]
        assert!(!mesh.check_edge_has_exactly_two_half_edges_via_kernel());
    }

    #[test]
    fn overlapping_face_representatives_fail_face_cycle_check() {
        let mesh = Mesh {
            vertices: vec![
                super::Vertex {
                    position: RuntimePoint3::from_ints(0, 0, 0),
                    half_edge: 0,
                },
                super::Vertex {
                    position: RuntimePoint3::from_ints(1, 0, 0),
                    half_edge: 1,
                },
                super::Vertex {
                    position: RuntimePoint3::from_ints(0, 1, 0),
                    half_edge: 2,
                },
            ],
            edges: vec![
                super::Edge { half_edge: 0 },
                super::Edge { half_edge: 1 },
                super::Edge { half_edge: 2 },
            ],
            faces: vec![super::Face { half_edge: 0 }, super::Face { half_edge: 0 }],
            half_edges: vec![
                super::HalfEdge {
                    vertex: 0,
                    twin: 0,
                    next: 1,
                    prev: 2,
                    edge: 0,
                    face: 0,
                },
                super::HalfEdge {
                    vertex: 1,
                    twin: 1,
                    next: 2,
                    prev: 0,
                    edge: 1,
                    face: 0,
                },
                super::HalfEdge {
                    vertex: 2,
                    twin: 2,
                    next: 0,
                    prev: 1,
                    edge: 2,
                    face: 0,
                },
            ],
        };

        assert!(!mesh.check_face_cycles());
        #[cfg(feature = "verus-proofs")]
        assert!(!mesh.check_face_cycles_via_kernel());
    }

    #[test]
    fn split_vertex_ring_fails_vertex_manifold_single_cycle_check() {
        let mesh = Mesh {
            vertices: vec![super::Vertex {
                position: RuntimePoint3::from_ints(0, 0, 0),
                half_edge: 0,
            }],
            edges: vec![super::Edge { half_edge: 0 }, super::Edge { half_edge: 1 }],
            faces: vec![super::Face { half_edge: 0 }],
            half_edges: vec![
                super::HalfEdge {
                    vertex: 0,
                    twin: 0,
                    next: 0,
                    prev: 0,
                    edge: 0,
                    face: 0,
                },
                super::HalfEdge {
                    vertex: 0,
                    twin: 1,
                    next: 1,
                    prev: 1,
                    edge: 1,
                    face: 0,
                },
            ],
        };

        assert!(!mesh.check_vertex_manifold_single_cycle());
        #[cfg(feature = "verus-proofs")]
        assert!(!mesh.check_vertex_manifold_single_cycle_via_kernel());
    }

    #[cfg(feature = "verus-proofs")]
    #[test]
    fn bridge_core_checks_agree_on_reference_meshes() {
        let t = Mesh::tetrahedron();
        assert!(t.bridge_index_and_twin_checks_agree());
        assert_eq!(t.check_prev_inverse_of_next(), t.check_prev_inverse_of_next_via_kernel());
        assert_eq!(t.check_no_degenerate_edges(), t.check_no_degenerate_edges_via_kernel());
        assert_eq!(t.check_face_cycles(), t.check_face_cycles_via_kernel());
        assert_eq!(
            t.check_vertex_manifold_single_cycle(),
            t.check_vertex_manifold_single_cycle_via_kernel()
        );
        assert_eq!(
            t.check_edge_has_exactly_two_half_edges(),
            t.check_edge_has_exactly_two_half_edges_via_kernel()
        );
        assert_eq!(
            t.euler_characteristics_per_component(),
            t.euler_characteristics_per_component_raw()
        );
        assert_eq!(
            t.check_euler_formula_closed_components(),
            t.check_euler_formula_closed_components_raw()
        );

        let c = Mesh::cube();
        assert!(c.bridge_index_and_twin_checks_agree());
        assert_eq!(c.check_prev_inverse_of_next(), c.check_prev_inverse_of_next_via_kernel());
        assert_eq!(c.check_no_degenerate_edges(), c.check_no_degenerate_edges_via_kernel());
        assert_eq!(c.check_face_cycles(), c.check_face_cycles_via_kernel());
        assert_eq!(
            c.check_vertex_manifold_single_cycle(),
            c.check_vertex_manifold_single_cycle_via_kernel()
        );
        assert_eq!(
            c.check_edge_has_exactly_two_half_edges(),
            c.check_edge_has_exactly_two_half_edges_via_kernel()
        );
        assert_eq!(
            c.euler_characteristics_per_component(),
            c.euler_characteristics_per_component_raw()
        );
        assert_eq!(
            c.check_euler_formula_closed_components(),
            c.check_euler_formula_closed_components_raw()
        );

        let p = Mesh::triangular_prism();
        assert!(p.bridge_index_and_twin_checks_agree());
        assert_eq!(p.check_prev_inverse_of_next(), p.check_prev_inverse_of_next_via_kernel());
        assert_eq!(p.check_no_degenerate_edges(), p.check_no_degenerate_edges_via_kernel());
        assert_eq!(p.check_face_cycles(), p.check_face_cycles_via_kernel());
        assert_eq!(
            p.check_vertex_manifold_single_cycle(),
            p.check_vertex_manifold_single_cycle_via_kernel()
        );
        assert_eq!(
            p.check_edge_has_exactly_two_half_edges(),
            p.check_edge_has_exactly_two_half_edges_via_kernel()
        );
        assert_eq!(
            p.euler_characteristics_per_component(),
            p.euler_characteristics_per_component_raw()
        );
        assert_eq!(
            p.check_euler_formula_closed_components(),
            p.check_euler_formula_closed_components_raw()
        );
    }

    #[cfg(feature = "verus-proofs")]
    #[test]
    fn runtime_refinement_include_list_covers_all_refinement_modules() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let refinement_root = manifest_dir.join("src/runtime_halfedge_mesh_refinement");
        let refinement_include_root =
            manifest_dir.join("src/runtime_halfedge_mesh_refinement.rs");

        let include_contents = fs::read_to_string(&refinement_include_root)
            .expect("runtime refinement include file should be readable");
        let include_prefix = "include!(\"runtime_halfedge_mesh_refinement/";
        let mut included_files = BTreeSet::new();
        for line in include_contents.lines() {
            let trimmed = line.trim();
            if let Some(rest) = trimmed.strip_prefix(include_prefix) {
                if let Some(file) = rest.strip_suffix("\");") {
                    included_files.insert(file.to_string());
                }
            }
        }

        let mut module_files = BTreeSet::new();
        let entries = fs::read_dir(&refinement_root)
            .expect("runtime refinement module directory should be readable");
        for entry_result in entries {
            let entry = entry_result.expect("directory entry should be readable");
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) == Some("rs") {
                module_files.insert(
                    path.file_name()
                        .expect("module file should have file name")
                        .to_str()
                        .expect("module file name should be UTF-8")
                        .to_string(),
                );
            }
        }

        assert_eq!(
            included_files, module_files,
            "runtime_halfedge_mesh_refinement.rs include! list must match src/runtime_halfedge_mesh_refinement/*.rs exactly"
        );
    }

    #[test]
    fn topology_sources_remain_exact_arithmetic_only() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let source_root = manifest_dir.join("src");

        let mut source_files = Vec::new();
        collect_rs_files_recursively(&source_root, &mut source_files);
        source_files.sort();

        let mut offenders = Vec::new();
        for source_file in source_files {
            let source_name = source_file
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or_default();
            if source_name == "tests.rs" {
                continue;
            }

            let contents = fs::read_to_string(&source_file)
                .expect("Rust source file should be readable");
            if has_identifier_token(&contents, "f32") || has_identifier_token(&contents, "f64") {
                offenders.push(
                    source_file
                        .strip_prefix(&manifest_dir)
                        .expect("source file should be inside crate manifest dir")
                        .display()
                        .to_string(),
                );
            }
        }

        assert!(
            offenders.is_empty(),
            "floating-point type tokens found in vcad-topology source: {:?}",
            offenders
        );
    }

    #[test]
    fn topology_sources_contain_no_trusted_verification_boundaries() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let source_root = manifest_dir.join("src");
        let assume_spec_token = ["assume", "_specification"].concat();
        let external_fn_spec_token = ["external_fn", "_specification"].concat();
        let verifier_external_marker = ["[verifier::external", "]"].concat();
        let verifier_external_body_marker = ["[verifier::external", "_body]"].concat();
        let verus_trusted_marker = ["verus::", "trusted"].concat();

        let mut source_files = Vec::new();
        collect_rs_files_recursively(&source_root, &mut source_files);
        source_files.sort();

        let mut offenders = Vec::new();
        for source_file in source_files {
            let source_name = source_file
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or_default();
            if source_name == "tests.rs" {
                continue;
            }

            let contents = fs::read_to_string(&source_file)
                .expect("Rust source file should be readable");

            let mut violation_tokens = Vec::new();
            if has_identifier_token(&contents, &assume_spec_token) {
                violation_tokens.push(assume_spec_token.clone());
            }
            if has_identifier_token(&contents, &external_fn_spec_token) {
                violation_tokens.push(external_fn_spec_token.clone());
            }
            if has_identifier_token(&contents, "admit") {
                violation_tokens.push("admit".to_string());
            }
            if contents.contains(&verifier_external_marker) {
                violation_tokens.push(verifier_external_marker.clone());
            }
            if contents.contains(&verifier_external_body_marker) {
                violation_tokens.push(verifier_external_body_marker.clone());
            }
            if contents.contains(&verus_trusted_marker) {
                violation_tokens.push(verus_trusted_marker.clone());
            }

            if !violation_tokens.is_empty() {
                offenders.push((
                    source_file
                        .strip_prefix(&manifest_dir)
                        .expect("source file should be inside crate manifest dir")
                        .display()
                        .to_string(),
                    violation_tokens,
                ));
            }
        }

        assert!(
            offenders.is_empty(),
            "trusted verification boundary tokens found in vcad-topology source: {:?}",
            offenders
        );
    }
