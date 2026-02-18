use super::{Mesh, MeshBuildError};
use vcad_math::runtime_point3::RuntimePoint3;

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
        assert!(mesh.check_face_coplanarity());
        assert!(!mesh.check_face_convexity());
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
        assert!(mesh.check_face_coplanarity());
        assert!(!mesh.check_face_convexity());
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
