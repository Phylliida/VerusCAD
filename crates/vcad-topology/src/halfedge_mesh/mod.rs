use vcad_math::runtime_point3::RuntimePoint3;

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

#[cfg(feature = "geometry-checks")]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GeometricTopologicalConsistencyFailure {
    Phase4Validity,
    ZeroLengthGeometricEdge {
        half_edge: usize,
        from_vertex: usize,
        to_vertex: usize,
    },
    FaceCornerCollinear {
        face: usize,
        half_edge: usize,
    },
    FaceNonCoplanar {
        face: usize,
        half_edge: usize,
    },
    FaceNonConvex {
        face: usize,
        half_edge: usize,
    },
    FacePlaneInconsistent {
        face: usize,
        half_edge: usize,
    },
    SharedEdgeOrientationInconsistent {
        half_edge: usize,
        twin_half_edge: usize,
    },
    ForbiddenFaceFaceIntersection {
        face_a: usize,
        face_b: usize,
    },
    InwardOrDegenerateComponent {
        start_half_edge: usize,
    },
    InternalInconsistency,
}

mod components;
mod construction;
mod validation;

#[cfg(test)]
mod tests;
