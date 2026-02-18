use super::{Mesh, MeshBuildError};
#[cfg(feature = "geometry-checks")]
use super::GeometricTopologicalConsistencyFailure;
use vcad_math::runtime_point3::RuntimePoint3;
#[cfg(feature = "geometry-checks")]
use vcad_math::runtime_scalar::RuntimeScalar;
#[cfg(feature = "geometry-checks")]
use vcad_math::runtime_vec3::RuntimeVec3;

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
        assert_eq!(
            invalid_mesh.check_geometric_topological_consistency_diagnostic(),
            Err(GeometricTopologicalConsistencyFailure::Phase4Validity)
        );

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
        assert!(mesh.check_no_forbidden_face_face_intersections());
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
        assert!(mesh.check_no_forbidden_face_face_intersections());
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
