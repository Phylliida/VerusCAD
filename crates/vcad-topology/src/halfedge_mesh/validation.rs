#[cfg(not(feature = "verus-proofs"))]
use std::collections::HashSet;

#[cfg(feature = "geometry-checks")]
use vcad_geometry::collinearity_coplanarity::{collinear3d, coplanar};
#[cfg(feature = "geometry-checks")]
use vcad_geometry::orientation_predicates::{orient3d_sign, orient3d_value};
#[cfg(feature = "geometry-checks")]
use vcad_math::runtime_point3::RuntimePoint3;
#[cfg(feature = "geometry-checks")]
use vcad_math::runtime_scalar::RuntimeScalar;
#[cfg(feature = "verus-proofs")]
use crate::verified_checker_kernels::{
    kernel_check_edge_has_exactly_two_half_edges, kernel_check_face_cycles, kernel_check_index_bounds,
    kernel_check_no_degenerate_edges, kernel_check_prev_inverse_of_next, kernel_check_twin_involution,
    kernel_check_vertex_manifold_single_cycle, KernelHalfEdge, KernelMesh,
};

use super::Mesh;
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
    pub fn check_geometric_topological_consistency(&self) -> bool {
        self.is_valid()
            && self.check_no_zero_length_geometric_edges()
            && self.check_face_corner_non_collinearity()
            && self.check_face_coplanarity()
            && self.check_face_convexity()
            && self.check_outward_face_normals()
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
