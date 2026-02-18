use std::collections::{HashMap, HashSet, VecDeque};

#[cfg(feature = "geometry-checks")]
use vcad_geometry::collinearity_coplanarity::collinear3d;
use vcad_math::runtime_point3::RuntimePoint3;
#[cfg(feature = "verus-proofs")]
use crate::verified_checker_kernels::{
    kernel_check_face_cycles,
    kernel_check_edge_has_exactly_two_half_edges, kernel_check_index_bounds,
    kernel_check_no_degenerate_edges,
    kernel_check_prev_inverse_of_next, kernel_check_twin_involution,
    kernel_check_vertex_manifold_single_cycle,
    KernelHalfEdge, KernelMesh,
};

pub type VertexId = usize;
pub type EdgeId = usize;
pub type FaceId = usize;
pub type HalfEdgeId = usize;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HalfEdge {
    pub twin: HalfEdgeId,
    pub next: HalfEdgeId,
    pub prev: HalfEdgeId,
    pub vertex: VertexId,
    pub edge: EdgeId,
    pub face: FaceId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Vertex {
    pub position: RuntimePoint3,
    pub half_edge: HalfEdgeId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Edge {
    pub half_edge: HalfEdgeId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Face {
    pub half_edge: HalfEdgeId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Mesh {
    pub vertices: Vec<Vertex>,
    pub edges: Vec<Edge>,
    pub faces: Vec<Face>,
    pub half_edges: Vec<HalfEdge>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MeshBuildError {
    EmptyVertexSet,
    EmptyFaceSet,
    FaceTooSmall { face: usize, len: usize },
    VertexOutOfBounds { face: usize, vertex: usize, index: usize },
    DegenerateOrientedEdge { face: usize, index: usize, vertex: usize },
    DuplicateOrientedEdge { from: usize, to: usize },
    MissingTwinForHalfEdge { half_edge: usize, from: usize, to: usize },
    IsolatedVertex { vertex: usize },
}

impl Mesh {
    /// Build a closed half-edge mesh from explicit face cycles.
    ///
    /// Indexing strategy:
    /// arena indices (`usize`) into `Vec`s for `vertices/edges/faces/half_edges`.
    /// This keeps runtime structures compact and stable for proof-facing invariants.
    pub fn from_face_cycles(
        vertex_positions: Vec<RuntimePoint3>,
        face_cycles: &[Vec<usize>],
    ) -> Result<Self, MeshBuildError> {
        if vertex_positions.is_empty() {
            return Err(MeshBuildError::EmptyVertexSet);
        }
        if face_cycles.is_empty() {
            return Err(MeshBuildError::EmptyFaceSet);
        }

        let vertex_count = vertex_positions.len();
        for (face_id, cycle) in face_cycles.iter().enumerate() {
            if cycle.len() < 3 {
                return Err(MeshBuildError::FaceTooSmall {
                    face: face_id,
                    len: cycle.len(),
                });
            }
            for (i, &v) in cycle.iter().enumerate() {
                if v >= vertex_count {
                    return Err(MeshBuildError::VertexOutOfBounds {
                        face: face_id,
                        vertex: v,
                        index: i,
                    });
                }
            }
        }

        let mut half_edges: Vec<HalfEdge> = Vec::new();
        let mut faces: Vec<Face> = Vec::with_capacity(face_cycles.len());
        let mut oriented_to_half_edge: HashMap<(usize, usize), usize> = HashMap::new();

        for (face_id, cycle) in face_cycles.iter().enumerate() {
            let start = half_edges.len();
            let n = cycle.len();
            faces.push(Face { half_edge: start });

            for i in 0..n {
                let h = start + i;
                let next = start + ((i + 1) % n);
                let prev = start + ((i + n - 1) % n);
                half_edges.push(HalfEdge {
                    twin: usize::MAX,
                    next,
                    prev,
                    vertex: cycle[i],
                    edge: usize::MAX,
                    face: face_id,
                });

                let from = cycle[i];
                let to = cycle[(i + 1) % n];
                if from == to {
                    return Err(MeshBuildError::DegenerateOrientedEdge {
                        face: face_id,
                        index: i,
                        vertex: from,
                    });
                }
                if oriented_to_half_edge.insert((from, to), h).is_some() {
                    return Err(MeshBuildError::DuplicateOrientedEdge { from, to });
                }
            }
        }

        for h in 0..half_edges.len() {
            let from = half_edges[h].vertex;
            let to = half_edges[half_edges[h].next].vertex;
            let twin = match oriented_to_half_edge.get(&(to, from)).copied() {
                Some(twin) => twin,
                None => {
                    return Err(MeshBuildError::MissingTwinForHalfEdge {
                        half_edge: h,
                        from,
                        to,
                    });
                }
            };
            half_edges[h].twin = twin;
        }

        let mut edges: Vec<Edge> = Vec::new();
        let mut undirected_to_edge: HashMap<(usize, usize), usize> = HashMap::new();
        for h in 0..half_edges.len() {
            let from = half_edges[h].vertex;
            let to = half_edges[half_edges[h].next].vertex;
            let key = if from < to { (from, to) } else { (to, from) };
            let edge = match undirected_to_edge.get(&key).copied() {
                Some(edge) => edge,
                None => {
                    let edge = edges.len();
                    edges.push(Edge { half_edge: h });
                    undirected_to_edge.insert(key, edge);
                    edge
                }
            };
            half_edges[h].edge = edge;
        }

        let mut first_outgoing: Vec<Option<usize>> = vec![None; vertex_count];
        for (h, he) in half_edges.iter().enumerate() {
            if first_outgoing[he.vertex].is_none() {
                first_outgoing[he.vertex] = Some(h);
            }
        }

        let mut vertices: Vec<Vertex> = Vec::with_capacity(vertex_count);
        for (vertex_id, position) in vertex_positions.into_iter().enumerate() {
            let half_edge = match first_outgoing[vertex_id] {
                Some(half_edge) => half_edge,
                None => return Err(MeshBuildError::IsolatedVertex { vertex: vertex_id }),
            };
            vertices.push(Vertex {
                position,
                half_edge,
            });
        }

        Ok(Self {
            vertices,
            edges,
            faces,
            half_edges,
        })
    }

    pub fn tetrahedron() -> Self {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(1, 0, 0),
            RuntimePoint3::from_ints(0, 1, 0),
            RuntimePoint3::from_ints(0, 0, 1),
        ];
        let faces = vec![vec![0, 1, 2], vec![0, 3, 1], vec![1, 3, 2], vec![2, 3, 0]];
        Self::from_face_cycles(vertices, &faces).expect("tetrahedron face cycles should build")
    }

    pub fn cube() -> Self {
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
            vec![0, 3, 2, 1],
            vec![4, 5, 6, 7],
            vec![0, 1, 5, 4],
            vec![3, 7, 6, 2],
            vec![0, 4, 7, 3],
            vec![1, 2, 6, 5],
        ];
        Self::from_face_cycles(vertices, &faces).expect("cube face cycles should build")
    }

    pub fn triangular_prism() -> Self {
        let vertices = vec![
            RuntimePoint3::from_ints(0, 0, 0),
            RuntimePoint3::from_ints(2, 0, 0),
            RuntimePoint3::from_ints(1, 2, 0),
            RuntimePoint3::from_ints(0, 0, 1),
            RuntimePoint3::from_ints(2, 0, 1),
            RuntimePoint3::from_ints(1, 2, 1),
        ];
        let faces = vec![
            vec![0, 2, 1],
            vec![3, 4, 5],
            vec![0, 1, 4, 3],
            vec![1, 2, 5, 4],
            vec![2, 0, 3, 5],
        ];
        Self::from_face_cycles(vertices, &faces).expect("triangular prism face cycles should build")
    }

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
    pub fn is_valid_with_geometry(&self) -> bool {
        self.is_valid() && self.check_face_corner_non_collinearity()
    }

    pub fn component_count(&self) -> usize {
        self.half_edge_components().len()
    }

    pub fn euler_characteristics_per_component(&self) -> Vec<isize> {
        #[cfg(feature = "verus-proofs")]
        {
            if let Some(chis) =
                crate::runtime_halfedge_mesh_refinement::euler_characteristics_per_component_constructive(self)
            {
                return chis;
            }
        }

        self.euler_characteristics_per_component_raw()
    }

    fn euler_characteristics_per_component_raw(&self) -> Vec<isize> {
        let mut out = Vec::new();
        for component in self.half_edge_components() {
            let mut vertices = HashSet::new();
            let mut edges = HashSet::new();
            let mut faces = HashSet::new();
            for h in component {
                let he = &self.half_edges[h];
                vertices.insert(he.vertex);
                edges.insert(he.edge);
                faces.insert(he.face);
            }
            out.push(vertices.len() as isize - edges.len() as isize + faces.len() as isize);
        }
        out
    }

    pub fn check_euler_formula_closed_components(&self) -> bool {
        #[cfg(feature = "verus-proofs")]
        {
            if let Some(w) =
                crate::runtime_halfedge_mesh_refinement::check_euler_formula_closed_components_constructive(self)
            {
                return w.api_ok;
            }
        }

        self.check_euler_formula_closed_components_raw()
    }

    fn check_euler_formula_closed_components_raw(&self) -> bool {
        let chis = self.euler_characteristics_per_component_raw();
        !chis.is_empty() && chis.into_iter().all(|chi| chi == 2)
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

    fn check_twin_involution(&self) -> bool {
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

    fn check_prev_inverse_of_next(&self) -> bool {
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

    fn check_face_cycles(&self) -> bool {
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

    fn check_no_degenerate_edges(&self) -> bool {
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

    fn check_vertex_manifold_single_cycle(&self) -> bool {
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

    fn check_edge_has_exactly_two_half_edges(&self) -> bool {
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

    fn half_edge_components(&self) -> Vec<Vec<usize>> {
        let mut components = Vec::new();
        if self.half_edges.is_empty() {
            return components;
        }

        let mut visited = vec![false; self.half_edges.len()];
        for start in 0..self.half_edges.len() {
            if visited[start] {
                continue;
            }

            let mut queue = VecDeque::new();
            let mut component = Vec::new();
            queue.push_back(start);
            visited[start] = true;

            while let Some(h) = queue.pop_front() {
                component.push(h);
                let he = &self.half_edges[h];
                let neighbors = [he.twin, he.next, he.prev];
                for n in neighbors {
                    if !visited[n] {
                        visited[n] = true;
                        queue.push_back(n);
                    }
                }
            }

            components.push(component);
        }

        components
    }
}

#[cfg(test)]
mod tests {
    use super::{Mesh, MeshBuildError};
    use vcad_math::runtime_point3::RuntimePoint3;

    #[test]
    fn tetrahedron_is_valid() {
        let mesh = Mesh::tetrahedron();
        assert!(mesh.is_structurally_valid());
        assert!(mesh.is_valid());
        #[cfg(feature = "geometry-checks")]
        {
            assert!(mesh.check_face_corner_non_collinearity());
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
            assert!(mesh.check_face_corner_non_collinearity());
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
            assert!(mesh.check_face_corner_non_collinearity());
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
        assert!(!mesh.check_face_corner_non_collinearity());
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
}
