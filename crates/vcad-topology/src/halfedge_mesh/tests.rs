use super::{Mesh, MeshBuildError};
use std::fs;
use std::path::{Path, PathBuf};
#[cfg(feature = "verus-proofs")]
use std::collections::BTreeSet;
#[cfg(feature = "geometry-checks")]
use super::GeometricTopologicalConsistencyFailure;
#[cfg(feature = "geometry-checks")]
use vcad_geometry::collinearity_coplanarity::{collinear3d, coplanar};
#[cfg(feature = "geometry-checks")]
use vcad_geometry::orientation_predicates::{orient3d_sign, orient3d_value};
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
fn component_signed_volume_six_from_start_half_edge(mesh: &Mesh, start_half_edge: usize) -> RuntimeScalar {
    if start_half_edge >= mesh.half_edges.len() {
        return RuntimeScalar::from_int(0);
    }

    fn face_signed_volume_six_relative_to_origin(mesh: &Mesh, face_id: usize) -> RuntimeScalar {
        if face_id >= mesh.faces.len() {
            return RuntimeScalar::from_int(0);
        }
        let hcnt = mesh.half_edges.len();
        if hcnt == 0 {
            return RuntimeScalar::from_int(0);
        }

        let origin = RuntimePoint3::from_ints(0, 0, 0);
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
            let det = orient3d_value(&origin, p0, pi, pj);
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
            let face_volume6 = face_signed_volume_six_relative_to_origin(mesh, he.face);
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
