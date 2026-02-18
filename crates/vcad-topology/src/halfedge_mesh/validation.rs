#[cfg(not(feature = "verus-proofs"))]
use std::collections::HashSet;

#[cfg(feature = "geometry-checks")]
use vcad_geometry::convex_polygon::point_in_convex_polygon_2d;
#[cfg(feature = "geometry-checks")]
use vcad_geometry::collinearity_coplanarity::{collinear3d, coplanar};
#[cfg(feature = "geometry-checks")]
use vcad_geometry::orientation_predicates::{orient3d_sign, orient3d_value};
#[cfg(feature = "geometry-checks")]
use vcad_geometry::segment_intersection::{segment_intersection_kind_2d, SegmentIntersection2dKind};
#[cfg(feature = "geometry-checks")]
use vcad_geometry::sidedness::segment_plane_intersection_point_strict;
#[cfg(feature = "geometry-checks")]
use vcad_math::runtime_point2::RuntimePoint2;
#[cfg(feature = "geometry-checks")]
use vcad_math::runtime_point3::RuntimePoint3;
#[cfg(feature = "geometry-checks")]
use vcad_math::runtime_scalar::RuntimeScalar;
#[cfg(feature = "geometry-checks")]
use vcad_math::runtime_vec3::RuntimeVec3;
#[cfg(feature = "verus-proofs")]
use crate::verified_checker_kernels::{
    kernel_check_edge_has_exactly_two_half_edges, kernel_check_face_cycles, kernel_check_index_bounds,
    kernel_check_no_degenerate_edges, kernel_check_prev_inverse_of_next, kernel_check_twin_involution,
    kernel_check_vertex_manifold_single_cycle, KernelHalfEdge, KernelMesh,
};

use super::Mesh;
#[cfg(feature = "geometry-checks")]
use super::GeometricTopologicalConsistencyFailure;

#[cfg(feature = "geometry-checks")]
#[derive(Clone, Copy)]
enum ProjectionAxis {
    DropX,
    DropY,
    DropZ,
}

impl Mesh {
    pub fn is_structurally_valid(&self) -> bool {
        !self.vertices.is_empty()
            && !self.edges.is_empty()
            && !self.faces.is_empty()
            && !self.half_edges.is_empty()
            && self.check_index_bounds()
            && self.check_twin_involution()
            && self.check_prev_inverse_of_next()
            && self.check_face_cycles()
            && self.check_no_degenerate_edges()
            && self.check_vertex_manifold_single_cycle()
            && self.check_edge_has_exactly_two_half_edges()
    }

    /// Full phase-4 validity gate.
    ///
    /// Currently this enforces structural invariants plus the requested
    /// per-component Euler check `V - E + F = 2` (sphere-like closed components).
    pub fn is_valid(&self) -> bool {
        self.is_structurally_valid() && self.check_euler_formula_closed_components()
    }

    #[cfg(feature = "geometry-checks")]
    /// Optional geometric extension: every face corner must have non-collinear
    /// `(prev, current, next)` vertex positions.
    ///
    /// This intentionally stays outside `is_structurally_valid`/`is_valid` so
    /// the core topology gate remains purely combinatorial.
    pub fn check_face_corner_non_collinearity(&self) -> bool {
        if !self.is_valid() {
            return false;
        }
        if !self.check_index_bounds() || !self.check_face_cycles() {
            return false;
        }

        let hcnt = self.half_edges.len();
        for face in &self.faces {
            let start = face.half_edge;
            let mut h = start;
            let mut steps = 0usize;

            loop {
                let he = &self.half_edges[h];
                let prev = &self.half_edges[he.prev];
                let next = &self.half_edges[he.next];

                let a = &self.vertices[prev.vertex].position;
                let b = &self.vertices[he.vertex].position;
                let c = &self.vertices[next.vertex].position;
                if collinear3d(a, b, c) {
                    return false;
                }

                h = he.next;
                steps += 1;
                if h == start {
                    break;
                }
                if steps > hcnt {
                    return false;
                }
            }
        }

        true
    }

    #[cfg(feature = "geometry-checks")]
    /// Optional geometric extension: each oriented half-edge must span a
    /// non-zero geometric segment between its endpoint vertices.
    pub fn check_no_zero_length_geometric_edges(&self) -> bool {
        if !self.is_valid() {
            return false;
        }
        if !self.check_index_bounds() || !self.check_face_cycles() {
            return false;
        }

        for he in &self.half_edges {
            let a = &self.vertices[he.vertex].position;
            let b = &self.vertices[self.half_edges[he.next].vertex].position;
            if a == b {
                return false;
            }
        }

        true
    }

    #[cfg(feature = "geometry-checks")]
    /// Optional geometric extension: each face cycle's vertices are coplanar.
    pub fn check_face_coplanarity(&self) -> bool {
        if !self.is_valid() {
            return false;
        }
        if !self.check_index_bounds() || !self.check_face_cycles() {
            return false;
        }
        if !self.check_face_corner_non_collinearity() {
            return false;
        }

        let hcnt = self.half_edges.len();
        for face in &self.faces {
            let h0 = face.half_edge;
            let h1 = self.half_edges[h0].next;
            let h2 = self.half_edges[h1].next;

            let a = &self.vertices[self.half_edges[h0].vertex].position;
            let b = &self.vertices[self.half_edges[h1].vertex].position;
            let c = &self.vertices[self.half_edges[h2].vertex].position;

            let mut h = self.half_edges[h2].next;
            let mut steps = 0usize;
            while h != h0 {
                let d = &self.vertices[self.half_edges[h].vertex].position;
                if !coplanar(a, b, c, d) {
                    return false;
                }

                h = self.half_edges[h].next;
                steps += 1;
                if steps > hcnt {
                    return false;
                }
            }
        }

        true
    }

    #[cfg(feature = "geometry-checks")]
    /// Optional geometric extension: each face cycle is strictly convex under
    /// its own winding order.
    ///
    /// This uses exact arithmetic only:
    /// - choose a deterministic reference normal from the first face corner;
    /// - compare every corner turn orientation sign against that reference.
    pub fn check_face_convexity(&self) -> bool {
        if !self.is_valid() {
            return false;
        }
        if !self.check_index_bounds() || !self.check_face_cycles() {
            return false;
        }
        if !self.check_face_coplanarity() || !self.check_face_corner_non_collinearity() {
            return false;
        }

        let hcnt = self.half_edges.len();
        for face in &self.faces {
            let h0 = face.half_edge;
            let h1 = self.half_edges[h0].next;
            let h2 = self.half_edges[h1].next;

            let p0 = &self.vertices[self.half_edges[h0].vertex].position;
            let p1 = &self.vertices[self.half_edges[h1].vertex].position;
            let p2 = &self.vertices[self.half_edges[h2].vertex].position;

            let e01 = p1.sub(p0);
            let e12 = p2.sub(p1);
            let reference_normal = e01.cross(&e12);
            let witness = p0.add_vec(&reference_normal);

            let mut expected_turn_sign = 0i8;
            let mut h = h0;
            let mut steps = 0usize;
            loop {
                let he = &self.half_edges[h];
                let prev = &self.half_edges[he.prev];
                let next = &self.half_edges[he.next];

                let a = &self.vertices[prev.vertex].position;
                let b = &self.vertices[he.vertex].position;
                let c = &self.vertices[next.vertex].position;
                let turn_sign = orient3d_sign(a, b, c, &witness);
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
        }

        true
    }

    #[cfg(feature = "geometry-checks")]
    fn plane_offset_relative_to_origin(normal: &RuntimeVec3, point: &RuntimePoint3) -> RuntimeScalar {
        let origin = RuntimePoint3::from_ints(0, 0, 0);
        normal.dot(&point.sub(&origin))
    }

    #[cfg(feature = "geometry-checks")]
    fn point_plane_value_relative_to_origin(
        normal: &RuntimeVec3,
        offset: &RuntimeScalar,
        point: &RuntimePoint3,
    ) -> RuntimeScalar {
        let origin = RuntimePoint3::from_ints(0, 0, 0);
        normal.dot(&point.sub(&origin)).sub(offset)
    }

    #[cfg(feature = "geometry-checks")]
    /// Canonicalize plane representation `(normal, offset)` for comparison.
    ///
    /// Policy:
    /// - pick the first non-zero normal component in `(x, y, z)` order;
    /// - scale both `normal` and `offset` so that pivot component becomes `1`.
    ///
    /// This removes sign/scale ambiguity for equivalent planes.
    pub fn canonicalize_plane(
        normal: &RuntimeVec3,
        offset: &RuntimeScalar,
    ) -> Option<(RuntimeVec3, RuntimeScalar)> {
        let pivot = if normal.x().signum_i8() != 0 {
            normal.x()
        } else if normal.y().signum_i8() != 0 {
            normal.y()
        } else if normal.z().signum_i8() != 0 {
            normal.z()
        } else {
            return None;
        };

        let pivot_recip = pivot.recip()?;
        let normalized_normal = normal.scale(&pivot_recip);
        let normalized_offset = offset.mul(&pivot_recip);
        Some((normalized_normal, normalized_offset))
    }

    #[cfg(feature = "geometry-checks")]
    /// Optional geometric extension: compute a face plane `(normal, offset)`
    /// in the equation `normal . p = offset`, using exact arithmetic.
    ///
    /// Plane seed selection is robust: this scans the face cycle and picks the
    /// first non-collinear consecutive triple.
    pub fn compute_face_plane(&self, face_id: usize) -> Option<(RuntimeVec3, RuntimeScalar)> {
        if !self.is_valid() {
            return None;
        }
        if face_id >= self.faces.len() {
            return None;
        }
        if !self.check_index_bounds() || !self.check_face_cycles() {
            return None;
        }

        let hcnt = self.half_edges.len();
        let start = self.faces[face_id].half_edge;
        let mut h = start;
        let mut steps = 0usize;
        loop {
            let h1 = self.half_edges[h].next;
            let h2 = self.half_edges[h1].next;

            let p0 = &self.vertices[self.half_edges[h].vertex].position;
            let p1 = &self.vertices[self.half_edges[h1].vertex].position;
            let p2 = &self.vertices[self.half_edges[h2].vertex].position;

            let e01 = p1.sub(p0);
            let e12 = p2.sub(p1);
            let normal = e01.cross(&e12);
            if normal.norm2().signum_i8() != 0 {
                let offset = Self::plane_offset_relative_to_origin(&normal, p0);
                return Some((normal, offset));
            }

            h = self.half_edges[h].next;
            steps += 1;
            if h == start {
                break;
            }
            if steps > hcnt {
                return None;
            }
        }

        None
    }

    #[cfg(feature = "geometry-checks")]
    /// Optional geometric extension: compute a canonicalized face plane.
    ///
    /// See `canonicalize_plane` for the normalization policy.
    pub fn compute_face_plane_canonical(&self, face_id: usize) -> Option<(RuntimeVec3, RuntimeScalar)> {
        let (normal, offset) = self.compute_face_plane(face_id)?;
        Self::canonicalize_plane(&normal, &offset)
    }

    #[cfg(feature = "geometry-checks")]
    /// Optional geometric extension: each computed face plane must contain all
    /// vertices in that face cycle.
    pub fn check_face_plane_consistency(&self) -> bool {
        if !self.is_valid() {
            return false;
        }
        if !self.check_index_bounds() || !self.check_face_cycles() {
            return false;
        }
        if !self.check_face_coplanarity() || !self.check_face_corner_non_collinearity() {
            return false;
        }

        let hcnt = self.half_edges.len();
        for face_id in 0..self.faces.len() {
            let (normal, offset) = match self.compute_face_plane(face_id) {
                Some(plane) => plane,
                None => return false,
            };

            let start = self.faces[face_id].half_edge;
            let mut h = start;
            let mut steps = 0usize;
            loop {
                let p = &self.vertices[self.half_edges[h].vertex].position;
                let side = Self::point_plane_value_relative_to_origin(&normal, &offset, p);
                if side.signum_i8() != 0 {
                    return false;
                }

                h = self.half_edges[h].next;
                steps += 1;
                if h == start {
                    break;
                }
                if steps > hcnt {
                    return false;
                }
            }
        }

        true
    }

    #[cfg(feature = "geometry-checks")]
    fn face_signed_volume_six_relative_to_origin(&self, face_id: usize) -> RuntimeScalar {
        let origin = RuntimePoint3::from_ints(0, 0, 0);
        let hcnt = self.half_edges.len();

        let h0 = self.faces[face_id].half_edge;
        let p0 = &self.vertices[self.half_edges[h0].vertex].position;
        let mut hi = self.half_edges[h0].next;
        let mut hj = self.half_edges[hi].next;

        let mut sum = RuntimeScalar::from_int(0);
        let mut steps = 0usize;
        while hj != h0 {
            let pi = &self.vertices[self.half_edges[hi].vertex].position;
            let pj = &self.vertices[self.half_edges[hj].vertex].position;
            let det = orient3d_value(&origin, p0, pi, pj);
            sum = sum.add(&det);

            hi = hj;
            hj = self.half_edges[hj].next;
            steps += 1;
            if steps > hcnt {
                return RuntimeScalar::from_int(0);
            }
        }

        sum
    }

    #[cfg(feature = "geometry-checks")]
    /// Optional geometric extension: each connected component must have
    /// strictly negative signed volume under face winding.
    ///
    /// This treats negative signed volume as the outward-orientation
    /// convention for closed components.
    ///
    /// Degeneracy policy:
    /// - zero signed-volume components are rejected;
    /// - exact arithmetic is used throughout (no epsilon tolerance path).
    pub fn check_outward_face_normals(&self) -> bool {
        if !self.is_valid() {
            return false;
        }
        if self.faces.is_empty() || self.half_edges.is_empty() {
            return false;
        }
        if !self.check_index_bounds() || !self.check_face_cycles() {
            return false;
        }
        if !self.check_face_coplanarity() || !self.check_face_corner_non_collinearity() {
            return false;
        }

        let mut visited = vec![false; self.half_edges.len()];
        for start in 0..self.half_edges.len() {
            if visited[start] {
                continue;
            }

            let mut queue = std::collections::VecDeque::new();
            let mut seen_faces = std::collections::HashSet::new();
            let mut signed_volume6 = RuntimeScalar::from_int(0);

            queue.push_back(start);
            visited[start] = true;

            while let Some(h) = queue.pop_front() {
                let he = &self.half_edges[h];

                if seen_faces.insert(he.face) {
                    let face_volume6 = self.face_signed_volume_six_relative_to_origin(he.face);
                    signed_volume6 = signed_volume6.add(&face_volume6);
                }

                for n in [he.twin, he.next, he.prev] {
                    if !visited[n] {
                        visited[n] = true;
                        queue.push_back(n);
                    }
                }
            }

            if signed_volume6.signum_i8() >= 0 {
                return false;
            }
        }

        true
    }

    #[cfg(feature = "geometry-checks")]
    fn scalar_abs(value: &RuntimeScalar) -> RuntimeScalar {
        if value.signum_i8() < 0 {
            value.neg()
        } else {
            value.clone()
        }
    }

    #[cfg(feature = "geometry-checks")]
    fn scalar_ge(lhs: &RuntimeScalar, rhs: &RuntimeScalar) -> bool {
        lhs.sub(rhs).signum_i8() >= 0
    }

    #[cfg(feature = "geometry-checks")]
    fn dominant_projection_axis(normal: &RuntimeVec3) -> ProjectionAxis {
        let ax = Self::scalar_abs(normal.x());
        let ay = Self::scalar_abs(normal.y());
        let az = Self::scalar_abs(normal.z());

        if Self::scalar_ge(&ax, &ay) && Self::scalar_ge(&ax, &az) {
            ProjectionAxis::DropX
        } else if Self::scalar_ge(&ay, &az) {
            ProjectionAxis::DropY
        } else {
            ProjectionAxis::DropZ
        }
    }

    #[cfg(feature = "geometry-checks")]
    fn project_point3_to_2d(point: &RuntimePoint3, axis: ProjectionAxis) -> RuntimePoint2 {
        match axis {
            ProjectionAxis::DropX => RuntimePoint2::new(point.y().clone(), point.z().clone()),
            ProjectionAxis::DropY => RuntimePoint2::new(point.x().clone(), point.z().clone()),
            ProjectionAxis::DropZ => RuntimePoint2::new(point.x().clone(), point.y().clone()),
        }
    }

    #[cfg(feature = "geometry-checks")]
    fn ordered_face_vertex_cycle(&self, face_id: usize) -> Option<Vec<usize>> {
        if face_id >= self.faces.len() {
            return None;
        }

        let hcnt = self.half_edges.len();
        let start = self.faces[face_id].half_edge;
        let mut h = start;
        let mut steps = 0usize;
        let mut out = Vec::new();

        loop {
            out.push(self.half_edges[h].vertex);
            h = self.half_edges[h].next;
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

    #[cfg(feature = "geometry-checks")]
    fn faces_share_vertex(face_a_vertices: &[usize], face_b_vertices: &[usize]) -> bool {
        for &va in face_a_vertices {
            if face_b_vertices.contains(&va) {
                return true;
            }
        }
        false
    }

    #[cfg(feature = "geometry-checks")]
    /// Optional geometric extension: each shared edge between adjacent faces
    /// must induce opposite endpoint-vertex order on twin half-edges.
    pub fn check_shared_edge_local_orientation_consistency(&self) -> bool {
        if !self.is_valid() {
            return false;
        }
        if !self.check_index_bounds() || !self.check_face_cycles() {
            return false;
        }
        if !self.check_no_zero_length_geometric_edges() {
            return false;
        }

        for he in &self.half_edges {
            let twin = &self.half_edges[he.twin];
            if he.face == twin.face {
                return false;
            }

            let he_start = he.vertex;
            let he_end = self.half_edges[he.next].vertex;
            let twin_start = twin.vertex;
            let twin_end = self.half_edges[twin.next].vertex;
            if he_start != twin_end || he_end != twin_start {
                return false;
            }
        }

        true
    }

    #[cfg(feature = "geometry-checks")]
    fn point_in_convex_face_boundary(
        &self,
        point: &RuntimePoint3,
        face_vertices: &[usize],
        face_normal: &RuntimeVec3,
    ) -> bool {
        if face_vertices.len() < 3 {
            return false;
        }

        let mut expected_sign = 0i8;
        for i in 0..face_vertices.len() {
            let a = &self.vertices[face_vertices[i]].position;
            let b = &self.vertices[face_vertices[(i + 1) % face_vertices.len()]].position;
            let edge = b.sub(a);
            let to_point = point.sub(a);
            let side = edge.cross(&to_point).dot(face_normal).signum_i8();
            if side == 0 {
                continue;
            }
            if expected_sign == 0 {
                expected_sign = side;
            } else if side != expected_sign {
                return false;
            }
        }

        true
    }

    #[cfg(feature = "geometry-checks")]
    fn coplanar_segment_intersects_face_boundary_or_interior(
        &self,
        seg_start: &RuntimePoint3,
        seg_end: &RuntimePoint3,
        face_vertices: &[usize],
        face_normal: &RuntimeVec3,
    ) -> bool {
        if face_vertices.len() < 3 {
            return false;
        }

        let axis = Self::dominant_projection_axis(face_normal);
        let seg_start_2d = Self::project_point3_to_2d(seg_start, axis);
        let seg_end_2d = Self::project_point3_to_2d(seg_end, axis);
        let face_polygon_2d: Vec<RuntimePoint2> = face_vertices
            .iter()
            .map(|&vid| Self::project_point3_to_2d(&self.vertices[vid].position, axis))
            .collect();

        if point_in_convex_polygon_2d(&seg_start_2d, &face_polygon_2d)
            || point_in_convex_polygon_2d(&seg_end_2d, &face_polygon_2d)
        {
            return true;
        }

        for i in 0..face_polygon_2d.len() {
            let a = &face_polygon_2d[i];
            let b = &face_polygon_2d[(i + 1) % face_polygon_2d.len()];
            let kind = segment_intersection_kind_2d(&seg_start_2d, &seg_end_2d, a, b);
            if kind != SegmentIntersection2dKind::Disjoint {
                return true;
            }
        }

        false
    }

    #[cfg(feature = "geometry-checks")]
    fn segment_intersects_convex_face(
        &self,
        seg_start: &RuntimePoint3,
        seg_end: &RuntimePoint3,
        face_vertices: &[usize],
        face_plane_a: &RuntimePoint3,
        face_plane_b: &RuntimePoint3,
        face_plane_c: &RuntimePoint3,
        face_normal: &RuntimeVec3,
    ) -> bool {
        let start_side = orient3d_sign(face_plane_a, face_plane_b, face_plane_c, seg_start);
        let end_side = orient3d_sign(face_plane_a, face_plane_b, face_plane_c, seg_end);

        if start_side == 0 && end_side == 0 {
            return self.coplanar_segment_intersects_face_boundary_or_interior(
                seg_start,
                seg_end,
                face_vertices,
                face_normal,
            );
        }
        if start_side == 0 {
            return self.point_in_convex_face_boundary(seg_start, face_vertices, face_normal);
        }
        if end_side == 0 {
            return self.point_in_convex_face_boundary(seg_end, face_vertices, face_normal);
        }
        if start_side == end_side {
            return false;
        }

        let intersection = match segment_plane_intersection_point_strict(
            seg_start,
            seg_end,
            face_plane_a,
            face_plane_b,
            face_plane_c,
        ) {
            Some(p) => p,
            None => return false,
        };
        self.point_in_convex_face_boundary(&intersection, face_vertices, face_normal)
    }

    #[cfg(feature = "geometry-checks")]
    fn face_pair_has_forbidden_intersection(
        &self,
        face_a_vertices: &[usize],
        face_a_normal: &RuntimeVec3,
        face_b_vertices: &[usize],
        face_b_normal: &RuntimeVec3,
    ) -> bool {
        if face_a_vertices.len() < 3 || face_b_vertices.len() < 3 {
            return true;
        }

        let face_a_plane_a = &self.vertices[face_a_vertices[0]].position;
        let face_a_plane_b = &self.vertices[face_a_vertices[1]].position;
        let face_a_plane_c = &self.vertices[face_a_vertices[2]].position;
        let face_b_plane_a = &self.vertices[face_b_vertices[0]].position;
        let face_b_plane_b = &self.vertices[face_b_vertices[1]].position;
        let face_b_plane_c = &self.vertices[face_b_vertices[2]].position;

        for i in 0..face_a_vertices.len() {
            let seg_start = &self.vertices[face_a_vertices[i]].position;
            let seg_end = &self.vertices[face_a_vertices[(i + 1) % face_a_vertices.len()]].position;
            if self.segment_intersects_convex_face(
                seg_start,
                seg_end,
                face_b_vertices,
                face_b_plane_a,
                face_b_plane_b,
                face_b_plane_c,
                face_b_normal,
            ) {
                return true;
            }
        }

        for i in 0..face_b_vertices.len() {
            let seg_start = &self.vertices[face_b_vertices[i]].position;
            let seg_end = &self.vertices[face_b_vertices[(i + 1) % face_b_vertices.len()]].position;
            if self.segment_intersects_convex_face(
                seg_start,
                seg_end,
                face_a_vertices,
                face_a_plane_a,
                face_a_plane_b,
                face_a_plane_c,
                face_a_normal,
            ) {
                return true;
            }
        }

        false
    }

    #[cfg(feature = "geometry-checks")]
    /// Optional geometric extension: non-adjacent face pairs must not
    /// intersect.
    ///
    /// Degeneracy policy:
    /// - adjacency exemptions are index-based: if two face cycles share any
    ///   vertex index, this checker skips that pair;
    /// - geometric position coincidence with different vertex indices is not
    ///   exempt (for example, disconnected components touching at a vertex,
    ///   along an edge, or across an entire face);
    /// - exact arithmetic is used throughout (no epsilon tolerance path).
    pub fn check_no_forbidden_face_face_intersections(&self) -> bool {
        if !self.is_valid() {
            return false;
        }
        if !self.check_index_bounds() || !self.check_face_cycles() {
            return false;
        }
        if !self.check_no_zero_length_geometric_edges() {
            return false;
        }
        if !self.check_face_coplanarity() || !self.check_face_corner_non_collinearity() {
            return false;
        }
        if !self.check_face_convexity() {
            return false;
        }

        let mut face_vertices = Vec::with_capacity(self.faces.len());
        let mut face_normals = Vec::with_capacity(self.faces.len());
        for face_id in 0..self.faces.len() {
            let vertices = match self.ordered_face_vertex_cycle(face_id) {
                Some(vs) => vs,
                None => return false,
            };
            let (normal, _) = match self.compute_face_plane(face_id) {
                Some(plane) => plane,
                None => return false,
            };
            face_vertices.push(vertices);
            face_normals.push(normal);
        }

        for fa in 0..self.faces.len() {
            for fb in (fa + 1)..self.faces.len() {
                if Self::faces_share_vertex(&face_vertices[fa], &face_vertices[fb]) {
                    continue;
                }
                if self.face_pair_has_forbidden_intersection(
                    &face_vertices[fa],
                    &face_normals[fa],
                    &face_vertices[fb],
                    &face_normals[fb],
                ) {
                    return false;
                }
            }
        }

        true
    }

    #[cfg(feature = "geometry-checks")]
    fn first_zero_length_geometric_edge_failure(
        &self,
    ) -> Option<GeometricTopologicalConsistencyFailure> {
        for (half_edge, he) in self.half_edges.iter().enumerate() {
            let from_vertex = he.vertex;
            let to_vertex = self.half_edges[he.next].vertex;
            let a = &self.vertices[from_vertex].position;
            let b = &self.vertices[to_vertex].position;
            if a == b {
                return Some(GeometricTopologicalConsistencyFailure::ZeroLengthGeometricEdge {
                    half_edge,
                    from_vertex,
                    to_vertex,
                });
            }
        }
        None
    }

    #[cfg(feature = "geometry-checks")]
    fn first_face_corner_collinear_failure(
        &self,
    ) -> Option<GeometricTopologicalConsistencyFailure> {
        let hcnt = self.half_edges.len();
        for (face_id, face) in self.faces.iter().enumerate() {
            let start = face.half_edge;
            let mut h = start;
            let mut steps = 0usize;

            loop {
                let he = &self.half_edges[h];
                let prev = &self.half_edges[he.prev];
                let next = &self.half_edges[he.next];

                let a = &self.vertices[prev.vertex].position;
                let b = &self.vertices[he.vertex].position;
                let c = &self.vertices[next.vertex].position;
                if collinear3d(a, b, c) {
                    return Some(GeometricTopologicalConsistencyFailure::FaceCornerCollinear {
                        face: face_id,
                        half_edge: h,
                    });
                }

                h = he.next;
                steps += 1;
                if h == start {
                    break;
                }
                if steps > hcnt {
                    return Some(GeometricTopologicalConsistencyFailure::InternalInconsistency);
                }
            }
        }
        None
    }

    #[cfg(feature = "geometry-checks")]
    fn first_face_non_coplanar_failure(&self) -> Option<GeometricTopologicalConsistencyFailure> {
        let hcnt = self.half_edges.len();
        for (face_id, face) in self.faces.iter().enumerate() {
            let h0 = face.half_edge;
            let h1 = self.half_edges[h0].next;
            let h2 = self.half_edges[h1].next;

            let a = &self.vertices[self.half_edges[h0].vertex].position;
            let b = &self.vertices[self.half_edges[h1].vertex].position;
            let c = &self.vertices[self.half_edges[h2].vertex].position;

            let mut h = self.half_edges[h2].next;
            let mut steps = 0usize;
            while h != h0 {
                let d = &self.vertices[self.half_edges[h].vertex].position;
                if !coplanar(a, b, c, d) {
                    return Some(GeometricTopologicalConsistencyFailure::FaceNonCoplanar {
                        face: face_id,
                        half_edge: h,
                    });
                }

                h = self.half_edges[h].next;
                steps += 1;
                if steps > hcnt {
                    return Some(GeometricTopologicalConsistencyFailure::InternalInconsistency);
                }
            }
        }
        None
    }

    #[cfg(feature = "geometry-checks")]
    fn first_face_non_convex_failure(&self) -> Option<GeometricTopologicalConsistencyFailure> {
        let hcnt = self.half_edges.len();
        for (face_id, face) in self.faces.iter().enumerate() {
            let h0 = face.half_edge;
            let h1 = self.half_edges[h0].next;
            let h2 = self.half_edges[h1].next;

            let p0 = &self.vertices[self.half_edges[h0].vertex].position;
            let p1 = &self.vertices[self.half_edges[h1].vertex].position;
            let p2 = &self.vertices[self.half_edges[h2].vertex].position;

            let e01 = p1.sub(p0);
            let e12 = p2.sub(p1);
            let reference_normal = e01.cross(&e12);
            let witness = p0.add_vec(&reference_normal);

            let mut expected_turn_sign = 0i8;
            let mut h = h0;
            let mut steps = 0usize;
            loop {
                let he = &self.half_edges[h];
                let prev = &self.half_edges[he.prev];
                let next = &self.half_edges[he.next];

                let a = &self.vertices[prev.vertex].position;
                let b = &self.vertices[he.vertex].position;
                let c = &self.vertices[next.vertex].position;
                let turn_sign = orient3d_sign(a, b, c, &witness);
                if turn_sign == 0 {
                    return Some(GeometricTopologicalConsistencyFailure::FaceNonConvex {
                        face: face_id,
                        half_edge: h,
                    });
                }
                if expected_turn_sign == 0 {
                    expected_turn_sign = turn_sign;
                } else if turn_sign != expected_turn_sign {
                    return Some(GeometricTopologicalConsistencyFailure::FaceNonConvex {
                        face: face_id,
                        half_edge: h,
                    });
                }

                h = he.next;
                steps += 1;
                if h == h0 {
                    break;
                }
                if steps > hcnt {
                    return Some(GeometricTopologicalConsistencyFailure::InternalInconsistency);
                }
            }
        }
        None
    }

    #[cfg(feature = "geometry-checks")]
    fn first_face_plane_inconsistent_failure(
        &self,
    ) -> Option<GeometricTopologicalConsistencyFailure> {
        let hcnt = self.half_edges.len();
        for face_id in 0..self.faces.len() {
            let (normal, offset) = match self.compute_face_plane(face_id) {
                Some(plane) => plane,
                None => {
                    return Some(GeometricTopologicalConsistencyFailure::FacePlaneInconsistent {
                        face: face_id,
                        half_edge: self.faces[face_id].half_edge,
                    })
                }
            };

            let start = self.faces[face_id].half_edge;
            let mut h = start;
            let mut steps = 0usize;
            loop {
                let p = &self.vertices[self.half_edges[h].vertex].position;
                let side = Self::point_plane_value_relative_to_origin(&normal, &offset, p);
                if side.signum_i8() != 0 {
                    return Some(GeometricTopologicalConsistencyFailure::FacePlaneInconsistent {
                        face: face_id,
                        half_edge: h,
                    });
                }

                h = self.half_edges[h].next;
                steps += 1;
                if h == start {
                    break;
                }
                if steps > hcnt {
                    return Some(GeometricTopologicalConsistencyFailure::InternalInconsistency);
                }
            }
        }
        None
    }

    #[cfg(feature = "geometry-checks")]
    fn first_shared_edge_orientation_inconsistent_failure(
        &self,
    ) -> Option<GeometricTopologicalConsistencyFailure> {
        for (half_edge, he) in self.half_edges.iter().enumerate() {
            let twin_half_edge = he.twin;
            let twin = &self.half_edges[twin_half_edge];
            if he.face == twin.face {
                return Some(
                    GeometricTopologicalConsistencyFailure::SharedEdgeOrientationInconsistent {
                        half_edge,
                        twin_half_edge,
                    },
                );
            }

            let he_start = he.vertex;
            let he_end = self.half_edges[he.next].vertex;
            let twin_start = twin.vertex;
            let twin_end = self.half_edges[twin.next].vertex;
            if he_start != twin_end || he_end != twin_start {
                return Some(
                    GeometricTopologicalConsistencyFailure::SharedEdgeOrientationInconsistent {
                        half_edge,
                        twin_half_edge,
                    },
                );
            }
        }
        None
    }

    #[cfg(feature = "geometry-checks")]
    fn first_forbidden_face_face_intersection_failure(
        &self,
    ) -> Option<GeometricTopologicalConsistencyFailure> {
        let mut face_vertices = Vec::with_capacity(self.faces.len());
        let mut face_normals = Vec::with_capacity(self.faces.len());
        for face_id in 0..self.faces.len() {
            let vertices = match self.ordered_face_vertex_cycle(face_id) {
                Some(vs) => vs,
                None => return Some(GeometricTopologicalConsistencyFailure::InternalInconsistency),
            };
            let (normal, _) = match self.compute_face_plane(face_id) {
                Some(plane) => plane,
                None => return Some(GeometricTopologicalConsistencyFailure::InternalInconsistency),
            };
            face_vertices.push(vertices);
            face_normals.push(normal);
        }

        for fa in 0..self.faces.len() {
            for fb in (fa + 1)..self.faces.len() {
                if Self::faces_share_vertex(&face_vertices[fa], &face_vertices[fb]) {
                    continue;
                }
                if self.face_pair_has_forbidden_intersection(
                    &face_vertices[fa],
                    &face_normals[fa],
                    &face_vertices[fb],
                    &face_normals[fb],
                ) {
                    return Some(
                        GeometricTopologicalConsistencyFailure::ForbiddenFaceFaceIntersection {
                            face_a: fa,
                            face_b: fb,
                        },
                    );
                }
            }
        }

        None
    }

    #[cfg(feature = "geometry-checks")]
    fn first_inward_or_degenerate_component_failure(
        &self,
    ) -> Option<GeometricTopologicalConsistencyFailure> {
        let mut visited = vec![false; self.half_edges.len()];
        for start in 0..self.half_edges.len() {
            if visited[start] {
                continue;
            }

            let mut queue = std::collections::VecDeque::new();
            let mut seen_faces = std::collections::HashSet::new();
            let mut signed_volume6 = RuntimeScalar::from_int(0);

            queue.push_back(start);
            visited[start] = true;

            while let Some(h) = queue.pop_front() {
                let he = &self.half_edges[h];
                if seen_faces.insert(he.face) {
                    let face_volume6 = self.face_signed_volume_six_relative_to_origin(he.face);
                    signed_volume6 = signed_volume6.add(&face_volume6);
                }

                for n in [he.twin, he.next, he.prev] {
                    if !visited[n] {
                        visited[n] = true;
                        queue.push_back(n);
                    }
                }
            }

            if signed_volume6.signum_i8() >= 0 {
                return Some(GeometricTopologicalConsistencyFailure::InwardOrDegenerateComponent {
                    start_half_edge: start,
                });
            }
        }

        None
    }

    #[cfg(feature = "geometry-checks")]
    pub fn check_geometric_topological_consistency_diagnostic(
        &self,
    ) -> Result<(), GeometricTopologicalConsistencyFailure> {
        if !self.is_valid() {
            return Err(GeometricTopologicalConsistencyFailure::Phase4Validity);
        }
        if !self.check_index_bounds() || !self.check_face_cycles() {
            return Err(GeometricTopologicalConsistencyFailure::InternalInconsistency);
        }

        if let Some(failure) = self.first_zero_length_geometric_edge_failure() {
            return Err(failure);
        }
        if let Some(failure) = self.first_face_corner_collinear_failure() {
            return Err(failure);
        }
        if let Some(failure) = self.first_face_non_coplanar_failure() {
            return Err(failure);
        }
        if let Some(failure) = self.first_face_non_convex_failure() {
            return Err(failure);
        }
        if let Some(failure) = self.first_face_plane_inconsistent_failure() {
            return Err(failure);
        }
        if let Some(failure) = self.first_shared_edge_orientation_inconsistent_failure() {
            return Err(failure);
        }
        if let Some(failure) = self.first_forbidden_face_face_intersection_failure() {
            return Err(failure);
        }
        if let Some(failure) = self.first_inward_or_degenerate_component_failure() {
            return Err(failure);
        }

        Ok(())
    }

    #[cfg(feature = "geometry-checks")]
    pub fn check_geometric_topological_consistency(&self) -> bool {
        self.check_geometric_topological_consistency_diagnostic().is_ok()
    }

    #[cfg(feature = "geometry-checks")]
    pub fn is_valid_with_geometry(&self) -> bool {
        self.is_valid() && self.check_geometric_topological_consistency()
    }
    #[cfg(feature = "verus-proofs")]
    pub(crate) fn to_kernel_mesh_for_verification(&self) -> KernelMesh {
        let vertex_half_edges = self.vertices.iter().map(|v| v.half_edge).collect();
        let edge_half_edges = self.edges.iter().map(|e| e.half_edge).collect();
        let face_half_edges = self.faces.iter().map(|f| f.half_edge).collect();
        let half_edges = self.half_edges.iter().map(|he| KernelHalfEdge {
            twin: he.twin,
            next: he.next,
            prev: he.prev,
            vertex: he.vertex,
            edge: he.edge,
            face: he.face,
        }).collect();
        KernelMesh {
            vertex_half_edges,
            edge_half_edges,
            face_half_edges,
            half_edges,
        }
    }

    #[cfg(feature = "verus-proofs")]
    pub(crate) fn check_index_bounds_via_kernel(&self) -> bool {
        let km = self.to_kernel_mesh_for_verification();
        kernel_check_index_bounds(&km)
    }

    #[cfg(feature = "verus-proofs")]
    pub(crate) fn check_twin_involution_via_kernel(&self) -> bool {
        let km = self.to_kernel_mesh_for_verification();
        kernel_check_twin_involution(&km)
    }

    #[cfg(feature = "verus-proofs")]
    pub(crate) fn check_prev_inverse_of_next_via_kernel(&self) -> bool {
        let km = self.to_kernel_mesh_for_verification();
        kernel_check_prev_inverse_of_next(&km)
    }

    #[cfg(feature = "verus-proofs")]
    pub(crate) fn check_no_degenerate_edges_via_kernel(&self) -> bool {
        let km = self.to_kernel_mesh_for_verification();
        kernel_check_no_degenerate_edges(&km)
    }

    #[cfg(feature = "verus-proofs")]
    pub(crate) fn check_edge_has_exactly_two_half_edges_via_kernel(&self) -> bool {
        let km = self.to_kernel_mesh_for_verification();
        kernel_check_edge_has_exactly_two_half_edges(&km)
    }

    #[cfg(feature = "verus-proofs")]
    pub(crate) fn check_face_cycles_via_kernel(&self) -> bool {
        let km = self.to_kernel_mesh_for_verification();
        kernel_check_face_cycles(&km)
    }

    #[cfg(feature = "verus-proofs")]
    pub(crate) fn check_vertex_manifold_single_cycle_via_kernel(&self) -> bool {
        let km = self.to_kernel_mesh_for_verification();
        kernel_check_vertex_manifold_single_cycle(&km)
    }

    #[cfg(all(test, feature = "verus-proofs"))]
    pub(crate) fn bridge_index_and_twin_checks_agree(&self) -> bool {
        let runtime_index_ok = self.check_index_bounds();
        let kernel_index_ok = self.check_index_bounds_via_kernel();
        if runtime_index_ok != kernel_index_ok {
            return false;
        }
        if !runtime_index_ok {
            return true;
        }

        let runtime_twin_ok = self.check_twin_involution();
        let kernel_twin_ok = self.check_twin_involution_via_kernel();
        runtime_twin_ok == kernel_twin_ok
    }

    fn check_index_bounds(&self) -> bool {
        #[cfg(feature = "verus-proofs")]
        {
            // In proof-enabled builds, delegate directly to the verified kernel checker.
            return self.check_index_bounds_via_kernel();
        }

        #[cfg(not(feature = "verus-proofs"))]
        {
            for v in &self.vertices {
                if v.half_edge >= self.half_edges.len() {
                    return false;
                }
            }
            for e in &self.edges {
                if e.half_edge >= self.half_edges.len() {
                    return false;
                }
            }
            for f in &self.faces {
                if f.half_edge >= self.half_edges.len() {
                    return false;
                }
            }
            for he in &self.half_edges {
                if he.twin >= self.half_edges.len() {
                    return false;
                }
                if he.next >= self.half_edges.len() {
                    return false;
                }
                if he.prev >= self.half_edges.len() {
                    return false;
                }
                if he.vertex >= self.vertices.len() {
                    return false;
                }
                if he.edge >= self.edges.len() {
                    return false;
                }
                if he.face >= self.faces.len() {
                    return false;
                }
            }
            true
        }
    }

    pub(super) fn check_twin_involution(&self) -> bool {
        #[cfg(feature = "verus-proofs")]
        {
            // In proof-enabled builds, delegate directly to the verified kernel checker.
            return self.check_twin_involution_via_kernel();
        }

        #[cfg(not(feature = "verus-proofs"))]
        {
            for (h, he) in self.half_edges.iter().enumerate() {
                let t = he.twin;
                if self.half_edges[t].twin != h {
                    return false;
                }
            }
            true
        }
    }

    pub(super) fn check_prev_inverse_of_next(&self) -> bool {
        #[cfg(feature = "verus-proofs")]
        {
            // In proof-enabled builds, delegate directly to the verified kernel checker.
            return self.check_prev_inverse_of_next_via_kernel();
        }

        #[cfg(not(feature = "verus-proofs"))]
        {
            for (h, he) in self.half_edges.iter().enumerate() {
                if self.half_edges[he.next].prev != h {
                    return false;
                }
                if self.half_edges[he.prev].next != h {
                    return false;
                }
            }
            true
        }
    }

    pub(super) fn check_face_cycles(&self) -> bool {
        #[cfg(feature = "verus-proofs")]
        {
            // In proof-enabled builds, delegate directly to the kernel checker.
            return self.check_face_cycles_via_kernel();
        }

        #[cfg(not(feature = "verus-proofs"))]
        {
        let mut globally_seen = vec![false; self.half_edges.len()];

        for (face_id, face) in self.faces.iter().enumerate() {
            let start = face.half_edge;
            let mut local_seen: HashSet<usize> = HashSet::new();
            let mut h = start;

            loop {
                if !local_seen.insert(h) {
                    return false;
                }
                if globally_seen[h] {
                    return false;
                }
                globally_seen[h] = true;

                let he = &self.half_edges[h];
                if he.face != face_id {
                    return false;
                }

                h = he.next;
                if h == start {
                    break;
                }
                if local_seen.len() > self.half_edges.len() {
                    return false;
                }
            }

            if local_seen.len() < 3 {
                return false;
            }
        }

        globally_seen.into_iter().all(|seen| seen)
        }
    }

    pub(super) fn check_no_degenerate_edges(&self) -> bool {
        #[cfg(feature = "verus-proofs")]
        {
            // In proof-enabled builds, delegate directly to the verified kernel checker.
            return self.check_no_degenerate_edges_via_kernel();
        }

        #[cfg(not(feature = "verus-proofs"))]
        {
            for he in &self.half_edges {
                let twin = &self.half_edges[he.twin];
                if he.vertex == twin.vertex {
                    return false;
                }

                let to = self.half_edges[he.next].vertex;
                if he.vertex == to {
                    return false;
                }
            }
            true
        }
    }

    pub(super) fn check_vertex_manifold_single_cycle(&self) -> bool {
        #[cfg(feature = "verus-proofs")]
        {
            // In proof-enabled builds, delegate directly to the kernel checker.
            return self.check_vertex_manifold_single_cycle_via_kernel();
        }

        #[cfg(not(feature = "verus-proofs"))]
        {
        let mut outgoing_by_vertex: Vec<Vec<usize>> = vec![Vec::new(); self.vertices.len()];
        for (h, he) in self.half_edges.iter().enumerate() {
            outgoing_by_vertex[he.vertex].push(h);
        }

        for (vertex_id, vertex) in self.vertices.iter().enumerate() {
            let expected = outgoing_by_vertex[vertex_id].len();
            if expected == 0 {
                return false;
            }

            let start = vertex.half_edge;
            if self.half_edges[start].vertex != vertex_id {
                return false;
            }

            let mut seen = HashSet::new();
            let mut h = start;
            loop {
                if self.half_edges[h].vertex != vertex_id {
                    return false;
                }
                if !seen.insert(h) {
                    return false;
                }

                // Vertex ring traversal via twin/next.
                h = self.half_edges[self.half_edges[h].twin].next;

                if h == start {
                    break;
                }
                if seen.len() > expected {
                    return false;
                }
            }

            if seen.len() != expected {
                return false;
            }
        }

        true
        }
    }

    pub(super) fn check_edge_has_exactly_two_half_edges(&self) -> bool {
        #[cfg(feature = "verus-proofs")]
        {
            // In proof-enabled builds, delegate directly to the verified kernel checker.
            return self.check_edge_has_exactly_two_half_edges_via_kernel();
        }

        #[cfg(not(feature = "verus-proofs"))]
        {
            let mut first: Vec<Option<usize>> = vec![None; self.edges.len()];
            let mut second: Vec<Option<usize>> = vec![None; self.edges.len()];

            for (h, he) in self.half_edges.iter().enumerate() {
                match first[he.edge] {
                    None => first[he.edge] = Some(h),
                    Some(_) => match second[he.edge] {
                        None => second[he.edge] = Some(h),
                        Some(_) => return false,
                    },
                }
            }

            for (edge_id, edge) in self.edges.iter().enumerate() {
                let a = match first[edge_id] {
                    Some(a) => a,
                    None => return false,
                };
                let b = match second[edge_id] {
                    Some(b) => b,
                    None => return false,
                };

                if self.half_edges[a].twin != b || self.half_edges[b].twin != a {
                    return false;
                }
                if edge.half_edge != a && edge.half_edge != b {
                    return false;
                }
            }

            true
        }
    }
}
