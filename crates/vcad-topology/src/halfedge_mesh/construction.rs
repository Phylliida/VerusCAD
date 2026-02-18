use std::collections::HashMap;

use vcad_math::runtime_point3::RuntimePoint3;

use super::{Edge, Face, HalfEdge, Mesh, MeshBuildError, Vertex};

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
            vec![0, 1, 2, 3],
            vec![4, 7, 6, 5],
            vec![0, 4, 5, 1],
            vec![3, 2, 6, 7],
            vec![0, 3, 7, 4],
            vec![1, 5, 6, 2],
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
            vec![0, 1, 2],
            vec![3, 5, 4],
            vec![0, 3, 4, 1],
            vec![1, 4, 5, 2],
            vec![2, 5, 3, 0],
        ];
        Self::from_face_cycles(vertices, &faces).expect("triangular prism face cycles should build")
    }
}
