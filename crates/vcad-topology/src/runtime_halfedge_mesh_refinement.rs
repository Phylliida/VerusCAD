#![cfg(feature = "verus-proofs")]

use crate::halfedge_mesh::{Edge, Face, HalfEdge, Mesh, MeshBuildError, Vertex};
use vcad_math::runtime_point3::RuntimePoint3;
use vstd::prelude::*;
use vstd::view::View;

verus! {

#[verifier::external_type_specification]
pub struct ExMesh(Mesh);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExMeshBuildError(MeshBuildError);

#[verifier::external_type_specification]
pub struct ExHalfEdge(HalfEdge);

#[verifier::external_type_specification]
pub struct ExVertex(Vertex);

#[verifier::external_type_specification]
pub struct ExEdge(Edge);

#[verifier::external_type_specification]
pub struct ExFace(Face);

#[verifier::external_body]
fn mesh_build_error_empty_face_set() -> MeshBuildError {
    MeshBuildError::EmptyFaceSet
}

#[derive(Structural, Copy, Clone, PartialEq, Eq)]
pub struct HalfEdgeModel {
    pub twin: int,
    pub next: int,
    pub prev: int,
    pub vertex: int,
    pub edge: int,
    pub face: int,
}

#[derive(Structural, Copy, Clone, PartialEq, Eq)]
pub struct VertexModel {
    pub half_edge: int,
}

#[derive(Structural, Copy, Clone, PartialEq, Eq)]
pub struct EdgeModel {
    pub half_edge: int,
}

#[derive(Structural, Copy, Clone, PartialEq, Eq)]
pub struct FaceModel {
    pub half_edge: int,
}

pub struct MeshModel {
    pub vertex_half_edges: Seq<int>,
    pub edge_half_edges: Seq<int>,
    pub face_half_edges: Seq<int>,
    pub half_edges: Seq<HalfEdgeModel>,
}

impl View for HalfEdge {
    type V = HalfEdgeModel;

    open spec fn view(&self) -> HalfEdgeModel {
        HalfEdgeModel {
            twin: self.twin as int,
            next: self.next as int,
            prev: self.prev as int,
            vertex: self.vertex as int,
            edge: self.edge as int,
            face: self.face as int,
        }
    }
}

impl View for Vertex {
    type V = VertexModel;

    open spec fn view(&self) -> VertexModel {
        VertexModel { half_edge: self.half_edge as int }
    }
}

impl View for Edge {
    type V = EdgeModel;

    open spec fn view(&self) -> EdgeModel {
        EdgeModel { half_edge: self.half_edge as int }
    }
}

impl View for Face {
    type V = FaceModel;

    open spec fn view(&self) -> FaceModel {
        FaceModel { half_edge: self.half_edge as int }
    }
}

impl View for Mesh {
    type V = MeshModel;

    open spec fn view(&self) -> MeshModel {
        MeshModel {
            vertex_half_edges: Seq::new(self.vertices@.len(), |i: int| self.vertices@[i]@.half_edge),
            edge_half_edges: Seq::new(self.edges@.len(), |i: int| self.edges@[i]@.half_edge),
            face_half_edges: Seq::new(self.faces@.len(), |i: int| self.faces@[i]@.half_edge),
            half_edges: Seq::new(self.half_edges@.len(), |i: int| self.half_edges@[i]@),
        }
    }
}

pub open spec fn mesh_vertex_count_spec(m: MeshModel) -> int {
    m.vertex_half_edges.len() as int
}

pub open spec fn mesh_edge_count_spec(m: MeshModel) -> int {
    m.edge_half_edges.len() as int
}

pub open spec fn mesh_face_count_spec(m: MeshModel) -> int {
    m.face_half_edges.len() as int
}

pub open spec fn mesh_half_edge_count_spec(m: MeshModel) -> int {
    m.half_edges.len() as int
}

pub open spec fn mesh_index_bounds_spec(m: MeshModel) -> bool {
    &&& forall|v: int|
        0 <= v < mesh_vertex_count_spec(m)
            ==> 0 <= #[trigger] m.vertex_half_edges[v] < mesh_half_edge_count_spec(m)
    &&& forall|e: int|
        0 <= e < mesh_edge_count_spec(m)
            ==> 0 <= #[trigger] m.edge_half_edges[e] < mesh_half_edge_count_spec(m)
    &&& forall|f: int|
        0 <= f < mesh_face_count_spec(m)
            ==> 0 <= #[trigger] m.face_half_edges[f] < mesh_half_edge_count_spec(m)
    &&& forall|h: int| 0 <= h < mesh_half_edge_count_spec(m) ==> {
        let he = #[trigger] m.half_edges[h];
        &&& 0 <= he.twin < mesh_half_edge_count_spec(m)
        &&& 0 <= he.next < mesh_half_edge_count_spec(m)
        &&& 0 <= he.prev < mesh_half_edge_count_spec(m)
        &&& 0 <= he.vertex < mesh_vertex_count_spec(m)
        &&& 0 <= he.edge < mesh_edge_count_spec(m)
        &&& 0 <= he.face < mesh_face_count_spec(m)
    }
}

pub open spec fn mesh_twin_involution_spec(m: MeshModel) -> bool {
    forall|h: int|
        0 <= h < mesh_half_edge_count_spec(m)
            ==> #[trigger] m.half_edges[m.half_edges[h].twin].twin == h
}

pub open spec fn mesh_prev_next_inverse_spec(m: MeshModel) -> bool {
    forall|h: int| 0 <= h < mesh_half_edge_count_spec(m) ==> {
        &&& #[trigger] m.half_edges[m.half_edges[h].next].prev == h
        &&& #[trigger] m.half_edges[m.half_edges[h].prev].next == h
    }
}

pub open spec fn mesh_no_degenerate_edges_spec(m: MeshModel) -> bool {
    forall|h: int| 0 <= h < mesh_half_edge_count_spec(m) ==> {
        &&& #[trigger] m.half_edges[h].vertex != m.half_edges[m.half_edges[h].twin].vertex
        &&& #[trigger] m.half_edges[h].vertex != m.half_edges[m.half_edges[h].next].vertex
    }
}

pub open spec fn mesh_edge_exactly_two_half_edges_at_spec(m: MeshModel, e: int) -> bool {
    let h0 = #[trigger] m.edge_half_edges[e];
    let h1 = m.half_edges[h0].twin;
    &&& 0 <= h0 < mesh_half_edge_count_spec(m)
    &&& 0 <= h1 < mesh_half_edge_count_spec(m)
    &&& h0 != h1
    &&& m.half_edges[h0].edge == e
    &&& m.half_edges[h1].edge == e
    &&& m.half_edges[h1].twin == h0
    &&& forall|h: int|
        0 <= h < mesh_half_edge_count_spec(m)
            ==> (#[trigger] m.half_edges[h].edge == e ==> (h == h0 || h == h1))
}

pub open spec fn mesh_edge_exactly_two_half_edges_spec(m: MeshModel) -> bool {
    forall|e: int|
        0 <= e < mesh_edge_count_spec(m) ==> #[trigger] mesh_edge_exactly_two_half_edges_at_spec(m, e)
}

pub open spec fn mesh_next_or_self_spec(m: MeshModel, h: int) -> int {
    let hcnt = mesh_half_edge_count_spec(m);
    if 0 <= h < hcnt {
        let n = m.half_edges[h].next;
        if 0 <= n < hcnt {
            n
        } else {
            h
        }
    } else {
        h
    }
}

pub open spec fn mesh_vertex_ring_succ_or_self_spec(m: MeshModel, h: int) -> int {
    let hcnt = mesh_half_edge_count_spec(m);
    if 0 <= h < hcnt {
        let t = m.half_edges[h].twin;
        if 0 <= t < hcnt {
            let n = m.half_edges[t].next;
            if 0 <= n < hcnt {
                n
            } else {
                h
            }
        } else {
            h
        }
    } else {
        h
    }
}

pub open spec fn mesh_next_iter_spec(m: MeshModel, h: int, n: nat) -> int
    decreases n
{
    if n == 0 {
        h
    } else {
        mesh_next_or_self_spec(m, mesh_next_iter_spec(m, h, (n - 1) as nat))
    }
}

pub open spec fn mesh_vertex_ring_iter_spec(m: MeshModel, h: int, n: nat) -> int
    decreases n
{
    if n == 0 {
        h
    } else {
        mesh_vertex_ring_succ_or_self_spec(m, mesh_vertex_ring_iter_spec(m, h, (n - 1) as nat))
    }
}

pub open spec fn mesh_face_cycle_witness_spec(m: MeshModel, f: int, k: int) -> bool {
    let hcnt = mesh_half_edge_count_spec(m);
    let start = m.face_half_edges[f];
    &&& 3 <= k <= hcnt
    &&& mesh_next_iter_spec(m, start, k as nat) == start
    &&& forall|i: int|
        0 <= i < k ==> {
            let h = mesh_next_iter_spec(m, start, i as nat);
            &&& 0 <= h < hcnt
            &&& #[trigger] m.half_edges[mesh_next_iter_spec(m, start, i as nat)].face == f
        }
    &&& forall|i: int, j: int|
        #![trigger mesh_next_iter_spec(m, start, i as nat), mesh_next_iter_spec(m, start, j as nat)]
        0 <= i < j < k ==> mesh_next_iter_spec(m, start, i as nat) != mesh_next_iter_spec(
            m,
            start,
            j as nat,
        )
    &&& forall|h: int|
        0 <= h < hcnt && #[trigger] m.half_edges[h].face == f ==> exists|i: int|
            #![trigger mesh_next_iter_spec(m, start, i as nat)]
            0 <= i < k && mesh_next_iter_spec(m, start, i as nat) == h
}

pub open spec fn mesh_face_next_cycles_spec(m: MeshModel) -> bool {
    forall|f: int|
        #![trigger m.face_half_edges[f]]
        0 <= f < mesh_face_count_spec(m) ==> exists|k: int| mesh_face_cycle_witness_spec(m, f, k)
}

pub open spec fn mesh_vertex_ring_witness_spec(m: MeshModel, v: int, k: int) -> bool {
    let hcnt = mesh_half_edge_count_spec(m);
    let start = m.vertex_half_edges[v];
    &&& 1 <= k <= hcnt
    &&& mesh_vertex_ring_iter_spec(m, start, k as nat) == start
    &&& forall|i: int|
        0 <= i < k ==> {
            let h = mesh_vertex_ring_iter_spec(m, start, i as nat);
            &&& 0 <= h < hcnt
            &&& #[trigger] m.half_edges[mesh_vertex_ring_iter_spec(m, start, i as nat)].vertex == v
        }
    &&& forall|i: int, j: int|
        #![trigger mesh_vertex_ring_iter_spec(m, start, i as nat), mesh_vertex_ring_iter_spec(m, start, j as nat)]
        0 <= i < j < k
            ==> mesh_vertex_ring_iter_spec(m, start, i as nat) != mesh_vertex_ring_iter_spec(
                m,
                start,
                j as nat,
            )
    &&& forall|h: int|
        0 <= h < hcnt && #[trigger] m.half_edges[h].vertex == v ==> exists|i: int|
            #![trigger mesh_vertex_ring_iter_spec(m, start, i as nat)]
            0 <= i < k && mesh_vertex_ring_iter_spec(m, start, i as nat) == h
}

pub open spec fn mesh_vertex_manifold_single_cycle_spec(m: MeshModel) -> bool {
    forall|v: int|
        #![trigger m.vertex_half_edges[v]]
        0 <= v < mesh_vertex_count_spec(m) ==> exists|k: int| mesh_vertex_ring_witness_spec(m, v, k)
}

pub open spec fn mesh_half_edge_direct_step_spec(m: MeshModel, from: int, to: int) -> bool {
    let hcnt = mesh_half_edge_count_spec(m);
    &&& 0 <= from < hcnt
    &&& 0 <= to < hcnt
    &&& (to == m.half_edges[from].twin || to == m.half_edges[from].next || to == m.half_edges[from].prev)
}

pub open spec fn mesh_half_edge_adjacent_spec(m: MeshModel, a: int, b: int) -> bool {
    mesh_half_edge_direct_step_spec(m, a, b) || mesh_half_edge_direct_step_spec(m, b, a)
}

pub open spec fn mesh_half_edge_walk_spec(m: MeshModel, path: Seq<int>) -> bool {
    let hcnt = mesh_half_edge_count_spec(m);
    &&& path.len() > 0
    &&& forall|i: int| 0 <= i < path.len() as int ==> 0 <= #[trigger] path[i] < hcnt
    &&& forall|i: int|
        0 <= i < (path.len() as int) - 1
            ==> mesh_half_edge_adjacent_spec(m, path[i], #[trigger] path[i + 1])
}

pub open spec fn mesh_half_edge_connected_spec(m: MeshModel, from: int, to: int) -> bool {
    let hcnt = mesh_half_edge_count_spec(m);
    exists|path: Seq<int>| #![auto] {
        &&& 0 <= from < hcnt
        &&& 0 <= to < hcnt
        &&& 0 < path.len()
        &&& path.len() as int <= hcnt + 1
        &&& path[0] == from
        &&& path[(path.len() - 1) as int] == to
        &&& mesh_half_edge_walk_spec(m, path)
    }
}

pub open spec fn mesh_component_representative_spec(m: MeshModel, r: int) -> bool {
    let hcnt = mesh_half_edge_count_spec(m);
    &&& 0 <= r < hcnt
    &&& forall|h: int| 0 <= h < hcnt && mesh_half_edge_connected_spec(m, r, h) ==> r <= h
}

pub open spec fn mesh_component_count_spec(m: MeshModel) -> int {
    let hcnt = mesh_half_edge_count_spec(m);
    Set::new(|r: int| 0 <= r < hcnt && mesh_component_representative_spec(m, r)).len() as int
}

/// Euler relation under the current closed-component model:
/// each connected closed component contributes characteristic `2`,
/// so globally `V - E + F = 2 * component_count`.
pub open spec fn mesh_euler_closed_components_spec(m: MeshModel) -> bool {
    mesh_vertex_count_spec(m) - mesh_edge_count_spec(m) + mesh_face_count_spec(m)
        == 2 * mesh_component_count_spec(m)
}

pub open spec fn mesh_vertex_representative_valid_nonisolated_spec(m: MeshModel) -> bool {
    forall|v: int|
        #![trigger m.vertex_half_edges[v]]
        0 <= v < mesh_vertex_count_spec(m) ==> {
            &&& 0 <= m.vertex_half_edges[v] < mesh_half_edge_count_spec(m)
            &&& m.half_edges[m.vertex_half_edges[v]].vertex == v
        }
}

pub open spec fn mesh_structurally_valid_spec(m: MeshModel) -> bool {
    &&& mesh_vertex_count_spec(m) > 0
    &&& mesh_edge_count_spec(m) > 0
    &&& mesh_face_count_spec(m) > 0
    &&& mesh_half_edge_count_spec(m) > 0
    &&& mesh_index_bounds_spec(m)
    &&& mesh_twin_involution_spec(m)
    &&& mesh_prev_next_inverse_spec(m)
    &&& mesh_no_degenerate_edges_spec(m)
    &&& mesh_edge_exactly_two_half_edges_spec(m)
    &&& mesh_face_next_cycles_spec(m)
    &&& mesh_vertex_manifold_single_cycle_spec(m)
}

pub open spec fn mesh_valid_spec(m: MeshModel) -> bool {
    mesh_structurally_valid_spec(m) && mesh_euler_closed_components_spec(m)
}

pub open spec fn input_face_local_index_valid_spec(face_cycles: Seq<Seq<int>>, f: int, i: int) -> bool {
    0 <= f < face_cycles.len() as int && 0 <= i < face_cycles[f].len() as int
}

pub open spec fn input_face_cycle_start_spec(face_cycles: Seq<Seq<int>>, f: int) -> int
    decreases if f <= 0 { 0 } else { f }
{
    if f <= 0 {
        0
    } else {
        input_face_cycle_start_spec(face_cycles, f - 1) + face_cycles[(f - 1) as int].len() as int
    }
}

pub open spec fn input_half_edge_count_spec(face_cycles: Seq<Seq<int>>) -> int {
    input_face_cycle_start_spec(face_cycles, face_cycles.len() as int)
}

pub open spec fn input_face_half_edge_index_spec(face_cycles: Seq<Seq<int>>, f: int, i: int) -> int {
    input_face_cycle_start_spec(face_cycles, f) + i
}

pub open spec fn input_face_from_vertex_spec(face_cycles: Seq<Seq<int>>, f: int, i: int) -> int {
    let n = face_cycles[f].len() as int;
    if n > 0 {
        face_cycles[f][i]
    } else {
        0
    }
}

pub open spec fn input_face_next_local_index_spec(face_cycles: Seq<Seq<int>>, f: int, i: int) -> int {
    let n = face_cycles[f].len() as int;
    if n > 0 {
        if i + 1 < n {
            i + 1
        } else {
            0
        }
    } else {
        0
    }
}

pub open spec fn input_face_to_vertex_spec(face_cycles: Seq<Seq<int>>, f: int, i: int) -> int {
    let n = face_cycles[f].len() as int;
    if n > 0 {
        face_cycles[f][input_face_next_local_index_spec(face_cycles, f, i)]
    } else {
        0
    }
}

pub open spec fn input_face_prev_local_index_spec(face_cycles: Seq<Seq<int>>, f: int, i: int) -> int {
    let n = face_cycles[f].len() as int;
    if n > 0 {
        if i == 0 {
            n - 1
        } else {
            i - 1
        }
    } else {
        0
    }
}

pub open spec fn from_face_cycles_basic_input_spec(vertex_count: int, face_cycles: Seq<Seq<int>>) -> bool {
    &&& vertex_count > 0
    &&& face_cycles.len() > 0
    &&& forall|f: int|
        #![trigger face_cycles[f]]
        0 <= f < face_cycles.len() as int ==> {
            let n = face_cycles[f].len() as int;
            &&& n >= 3
            &&& forall|i: int|
                #![trigger face_cycles[f][i]]
                0 <= i < n ==> 0 <= face_cycles[f][i] < vertex_count
        }
}

pub open spec fn from_face_cycles_no_duplicate_oriented_edges_spec(face_cycles: Seq<Seq<int>>) -> bool {
    forall|f1: int, i1: int, f2: int, i2: int|
        #![trigger input_face_from_vertex_spec(face_cycles, f1, i1), input_face_to_vertex_spec(face_cycles, f1, i1), input_face_from_vertex_spec(face_cycles, f2, i2), input_face_to_vertex_spec(face_cycles, f2, i2)]
        input_face_local_index_valid_spec(face_cycles, f1, i1)
            && input_face_local_index_valid_spec(face_cycles, f2, i2)
            && input_face_from_vertex_spec(face_cycles, f1, i1) == input_face_from_vertex_spec(face_cycles, f2, i2)
            && input_face_to_vertex_spec(face_cycles, f1, i1) == input_face_to_vertex_spec(face_cycles, f2, i2)
            ==> f1 == f2 && i1 == i2
}

pub open spec fn from_face_cycles_all_oriented_edges_have_twin_spec(face_cycles: Seq<Seq<int>>) -> bool {
    forall|f: int, i: int|
        #![trigger input_face_from_vertex_spec(face_cycles, f, i), input_face_to_vertex_spec(face_cycles, f, i)]
        input_face_local_index_valid_spec(face_cycles, f, i) ==> exists|g: int, j: int| {
            &&& input_face_local_index_valid_spec(face_cycles, g, j)
            &&& #[trigger] input_face_from_vertex_spec(face_cycles, g, j)
                == input_face_to_vertex_spec(face_cycles, f, i)
            &&& #[trigger] input_face_to_vertex_spec(face_cycles, g, j)
                == input_face_from_vertex_spec(face_cycles, f, i)
        }
}

pub open spec fn from_face_cycles_no_isolated_vertices_spec(vertex_count: int, face_cycles: Seq<Seq<int>>) -> bool {
    forall|v: int|
        #![trigger v + 0]
        0 <= v < vertex_count ==> exists|f: int, i: int| {
        &&& input_face_local_index_valid_spec(face_cycles, f, i)
        &&& #[trigger] input_face_from_vertex_spec(face_cycles, f, i) == v
    }
}

pub open spec fn from_face_cycles_failure_spec(vertex_count: int, face_cycles: Seq<Seq<int>>) -> bool {
    !from_face_cycles_basic_input_spec(vertex_count, face_cycles)
        || !from_face_cycles_no_duplicate_oriented_edges_spec(face_cycles)
        || !from_face_cycles_all_oriented_edges_have_twin_spec(face_cycles)
        || !from_face_cycles_no_isolated_vertices_spec(vertex_count, face_cycles)
}

pub open spec fn face_cycles_exec_to_model_spec(face_cycles: Seq<Vec<usize>>) -> Seq<Seq<int>> {
    Seq::new(face_cycles.len(), |f: int| {
        Seq::new(face_cycles[f]@.len(), |i: int| face_cycles[f]@[i] as int)
    })
}

pub proof fn lemma_face_cycles_exec_to_model_face_len(face_cycles: Seq<Vec<usize>>, f: int)
    requires
        0 <= f < face_cycles.len() as int,
    ensures
        face_cycles_exec_to_model_spec(face_cycles)[f].len() == face_cycles[f]@.len() as int,
{
    assert(face_cycles_exec_to_model_spec(face_cycles)[f]
        == Seq::new(face_cycles[f]@.len(), |i: int| face_cycles[f]@[i] as int));
}

pub proof fn lemma_face_cycles_exec_to_model_face_len_exec(
    face_cycles: &[Vec<usize>],
    f: usize,
    face: &Vec<usize>,
    n: usize,
)
    requires
        f < face_cycles.len(),
        *face == face_cycles@.index(f as int),
        n == face.len(),
    ensures
        face_cycles_exec_to_model_spec(face_cycles@)[f as int].len() == n as int,
{
    lemma_face_cycles_exec_to_model_face_len(face_cycles@, f as int);
    assert(face@.len() == face.len());
    assert(face_cycles@.index(f as int) == face_cycles@[f as int]);
    assert(face_cycles@[f as int] == *face);
    assert(face_cycles@[f as int]@.len() == (*face)@.len());
    assert((*face)@.len() == n);
}

pub open spec fn mesh_half_edge_from_vertex_spec(m: MeshModel, h: int) -> int {
    m.half_edges[h].vertex
}

pub open spec fn mesh_half_edge_to_vertex_spec(m: MeshModel, h: int) -> int {
    m.half_edges[m.half_edges[h].next].vertex
}

pub open spec fn mesh_undirected_key_spec(a: int, b: int) -> (int, int) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

pub open spec fn from_face_cycles_incidence_model_spec(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
) -> bool {
    let fcnt = face_cycles.len() as int;
    let hcnt = input_half_edge_count_spec(face_cycles);
    &&& mesh_vertex_count_spec(m) == vertex_count
    &&& mesh_face_count_spec(m) == fcnt
    &&& mesh_half_edge_count_spec(m) == hcnt
    &&& mesh_index_bounds_spec(m)
    &&& forall|f: int|
        #![trigger m.face_half_edges[f]]
        0 <= f < fcnt ==> m.face_half_edges[f] == input_face_cycle_start_spec(face_cycles, f)
    &&& forall|f: int, i: int|
        #![trigger m.half_edges[input_face_half_edge_index_spec(face_cycles, f, i)]]
        input_face_local_index_valid_spec(face_cycles, f, i) ==> {
            let n = face_cycles[f].len() as int;
            let h = input_face_half_edge_index_spec(face_cycles, f, i);
            let next_i = input_face_next_local_index_spec(face_cycles, f, i);
            let prev_i = input_face_prev_local_index_spec(face_cycles, f, i);
            &&& m.half_edges[h].face == f
            &&& m.half_edges[h].vertex == input_face_from_vertex_spec(face_cycles, f, i)
            &&& m.half_edges[h].next == input_face_half_edge_index_spec(face_cycles, f, next_i)
            &&& m.half_edges[h].prev == input_face_half_edge_index_spec(face_cycles, f, prev_i)
        }
    &&& forall|h: int|
        #![trigger m.half_edges[h].twin]
        0 <= h < hcnt ==> {
            let t = m.half_edges[h].twin;
            &&& 0 <= t < hcnt
            &&& mesh_half_edge_from_vertex_spec(m, t) == mesh_half_edge_to_vertex_spec(m, h)
            &&& mesh_half_edge_to_vertex_spec(m, t) == mesh_half_edge_from_vertex_spec(m, h)
        }
    &&& forall|h1: int, h2: int|
        #![trigger m.half_edges[h1].edge, m.half_edges[h2].edge]
        0 <= h1 < hcnt && 0 <= h2 < hcnt ==> {
            (m.half_edges[h1].edge == m.half_edges[h2].edge) <==> (
                mesh_undirected_key_spec(
                    mesh_half_edge_from_vertex_spec(m, h1),
                    mesh_half_edge_to_vertex_spec(m, h1),
                ) == mesh_undirected_key_spec(
                    mesh_half_edge_from_vertex_spec(m, h2),
                    mesh_half_edge_to_vertex_spec(m, h2),
                )
            )
        }
    &&& forall|e: int|
        #![trigger m.edge_half_edges[e]]
        0 <= e < mesh_edge_count_spec(m) ==> {
            let h = m.edge_half_edges[e];
            &&& 0 <= h < hcnt
            &&& m.half_edges[h].edge == e
        }
    &&& forall|h: int| 0 <= h < hcnt ==> 0 <= #[trigger] m.half_edges[h].edge < mesh_edge_count_spec(m)
    &&& forall|v: int|
        #![trigger m.vertex_half_edges[v]]
        0 <= v < vertex_count ==> {
            let h = m.vertex_half_edges[v];
            &&& 0 <= h < hcnt
            &&& m.half_edges[h].vertex == v
        }
}

pub open spec fn from_face_cycles_next_prev_face_at_spec(
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
    f: int,
    i: int,
) -> bool {
    let n = face_cycles[f].len() as int;
    let h = input_face_half_edge_index_spec(face_cycles, f, i);
    let next_i = input_face_next_local_index_spec(face_cycles, f, i);
    let prev_i = input_face_prev_local_index_spec(face_cycles, f, i);
    &&& m.half_edges[h].face == f
    &&& m.half_edges[h].next == input_face_half_edge_index_spec(face_cycles, f, next_i)
    &&& m.half_edges[h].prev == input_face_half_edge_index_spec(face_cycles, f, prev_i)
}

pub open spec fn from_face_cycles_next_prev_face_coherent_spec(
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
) -> bool {
    forall|f: int, i: int|
        #![trigger m.half_edges[input_face_half_edge_index_spec(face_cycles, f, i)]]
        input_face_local_index_valid_spec(face_cycles, f, i)
            ==> from_face_cycles_next_prev_face_at_spec(face_cycles, m, f, i)
}

pub open spec fn from_face_cycles_vertex_representatives_spec(m: MeshModel) -> bool {
    mesh_vertex_representative_valid_nonisolated_spec(m)
}

pub open spec fn from_face_cycles_twin_assignment_total_involution_spec(m: MeshModel) -> bool {
    let hcnt = mesh_half_edge_count_spec(m);
    forall|h: int| 0 <= h < hcnt ==> {
        &&& 0 <= #[trigger] m.half_edges[h].twin < hcnt
        &&& #[trigger] m.half_edges[m.half_edges[h].twin].twin == h
    }
}

pub open spec fn from_face_cycles_success_spec(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
) -> bool {
    &&& from_face_cycles_basic_input_spec(vertex_count, face_cycles)
    &&& from_face_cycles_no_duplicate_oriented_edges_spec(face_cycles)
    &&& from_face_cycles_all_oriented_edges_have_twin_spec(face_cycles)
    &&& from_face_cycles_no_isolated_vertices_spec(vertex_count, face_cycles)
    &&& from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m)
}

pub proof fn lemma_from_face_cycles_incidence_implies_next_prev_face_coherent(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
)
    ensures
        from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m)
            ==> from_face_cycles_next_prev_face_coherent_spec(face_cycles, m),
{
    if from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m) {
        assert(from_face_cycles_next_prev_face_coherent_spec(face_cycles, m));
    }
}

pub proof fn lemma_from_face_cycles_success_implies_next_prev_face_coherent(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
)
    ensures
        from_face_cycles_success_spec(vertex_count, face_cycles, m)
            ==> from_face_cycles_next_prev_face_coherent_spec(face_cycles, m),
{
    if from_face_cycles_success_spec(vertex_count, face_cycles, m) {
        assert(from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m));
        lemma_from_face_cycles_incidence_implies_next_prev_face_coherent(vertex_count, face_cycles, m);
    }
}

pub proof fn lemma_from_face_cycles_incidence_implies_vertex_representatives(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
)
    ensures
        from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m)
            ==> from_face_cycles_vertex_representatives_spec(m),
{
    if from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m) {
        assert(from_face_cycles_vertex_representatives_spec(m));
    }
}

pub proof fn lemma_from_face_cycles_success_implies_vertex_representatives(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
)
    ensures
        from_face_cycles_success_spec(vertex_count, face_cycles, m)
            ==> from_face_cycles_vertex_representatives_spec(m),
{
    if from_face_cycles_success_spec(vertex_count, face_cycles, m) {
        assert(from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m));
        lemma_from_face_cycles_incidence_implies_vertex_representatives(vertex_count, face_cycles, m);
    }
}

#[verifier::external_body]
pub fn ex_mesh_from_face_cycles(
    vertex_positions: Vec<RuntimePoint3>,
    face_cycles: &[Vec<usize>],
) -> (out: Result<Mesh, MeshBuildError>)
{
    Mesh::from_face_cycles(vertex_positions, face_cycles)
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_from_face_cycles_next_prev_face_coherent(
    m: &Mesh,
    face_cycles: &[Vec<usize>],
) -> (out: bool)
    ensures
        out ==> from_face_cycles_next_prev_face_coherent_spec(face_cycles_exec_to_model_spec(face_cycles@), m@),
{
    let ghost model_cycles = face_cycles_exec_to_model_spec(face_cycles@);

    proof {
        assert(face_cycles_exec_to_model_spec(face_cycles@).len() == face_cycles.len());
        assert(model_cycles.len() == face_cycles.len() as int);
    }

    let mut start: usize = 0;
    let mut f: usize = 0;
    while f < face_cycles.len()
        invariant
            0 <= f <= face_cycles.len(),
            model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
            model_cycles.len() == face_cycles.len() as int,
            start as int == input_face_cycle_start_spec(model_cycles, f as int),
            forall|fp: int, ip: int|
                0 <= fp < f as int && input_face_local_index_valid_spec(model_cycles, fp, ip)
                    ==> from_face_cycles_next_prev_face_at_spec(model_cycles, m@, fp, ip),
    {
        let face = vstd::slice::slice_index_get(face_cycles, f);
        let n = face.len();
        if n == 0 {
            return false;
        }
        if n > usize::MAX - start {
            return false;
        }
        proof {
            lemma_face_cycles_exec_to_model_face_len_exec(face_cycles, f, face, n);
            assert(model_cycles[f as int].len() == n as int);
        }

        let mut i: usize = 0;
        while i < n
            invariant
                0 <= f < face_cycles.len(),
                0 <= i <= n,
                model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
                model_cycles.len() == face_cycles.len() as int,
                model_cycles[f as int].len() == n as int,
                start as int == input_face_cycle_start_spec(model_cycles, f as int),
                forall|fp: int, ip: int|
                    0 <= fp < f as int && input_face_local_index_valid_spec(model_cycles, fp, ip)
                        ==> from_face_cycles_next_prev_face_at_spec(model_cycles, m@, fp, ip),
                forall|ip: int|
                    0 <= ip < i as int && input_face_local_index_valid_spec(model_cycles, f as int, ip)
                        ==> from_face_cycles_next_prev_face_at_spec(model_cycles, m@, f as int, ip),
        {
            let next_i = if i + 1 < n { i + 1 } else { 0 };
            let prev_i = if i == 0 { n - 1 } else { i - 1 };

            let h = match start.checked_add(i) {
                Some(v) => v,
                None => return false,
            };
            let expected_next = match start.checked_add(next_i) {
                Some(v) => v,
                None => return false,
            };
            let expected_prev = match start.checked_add(prev_i) {
                Some(v) => v,
                None => return false,
            };

            if h >= m.half_edges.len() {
                return false;
            }

            let he = &m.half_edges[h];
            if he.face != f || he.next != expected_next || he.prev != expected_prev {
                return false;
            }

            proof {
                assert(0 <= i as int && (i as int) < (n as int));
                assert(input_face_local_index_valid_spec(model_cycles, f as int, i as int));
                assert(h as int == input_face_half_edge_index_spec(model_cycles, f as int, i as int));
                if i + 1 < n {
                    assert(next_i == i + 1);
                } else {
                    assert(next_i == 0);
                }
                assert(next_i as int == input_face_next_local_index_spec(model_cycles, f as int, i as int));
                if i == 0 {
                    assert(prev_i == n - 1);
                } else {
                    assert(prev_i == i - 1);
                }
                assert(prev_i as int == input_face_prev_local_index_spec(model_cycles, f as int, i as int));
                assert(expected_next as int == input_face_half_edge_index_spec(model_cycles, f as int, next_i as int));
                assert(expected_prev as int == input_face_half_edge_index_spec(model_cycles, f as int, prev_i as int));
                assert(m.half_edges@[h as int].face == he.face as int);
                assert(m.half_edges@[h as int].next == he.next as int);
                assert(m.half_edges@[h as int].prev == he.prev as int);
                assert(from_face_cycles_next_prev_face_at_spec(model_cycles, m@, f as int, i as int));
            }

            i += 1;
        }

        proof {
            assert(model_cycles[f as int].len() == n as int);
            assert(i == n);
            assert forall|fp: int, ip: int|
                0 <= fp < (f + 1) as int && input_face_local_index_valid_spec(model_cycles, fp, ip)
                    implies from_face_cycles_next_prev_face_at_spec(model_cycles, m@, fp, ip) by {
                if 0 <= fp < f as int {
                    assert(from_face_cycles_next_prev_face_at_spec(model_cycles, m@, fp, ip));
                } else {
                    assert(fp == f as int);
                    assert(0 <= ip < i as int);
                    assert(from_face_cycles_next_prev_face_at_spec(model_cycles, m@, f as int, ip));
                }
            };
            assert(input_face_cycle_start_spec(model_cycles, f as int + 1)
                == input_face_cycle_start_spec(model_cycles, f as int) + model_cycles[f as int].len() as int);
            assert((start + n) as int == start as int + n as int);
        }

        start += n;
        f += 1;
    }

    proof {
        assert(forall|fp: int, ip: int|
            0 <= fp < face_cycles.len() as int && input_face_local_index_valid_spec(model_cycles, fp, ip)
                ==> from_face_cycles_next_prev_face_at_spec(model_cycles, m@, fp, ip));
        assert(from_face_cycles_next_prev_face_coherent_spec(model_cycles, m@));
    }
    true
}

#[allow(dead_code)]
pub fn from_face_cycles_constructive_next_prev_face(
    vertex_positions: Vec<RuntimePoint3>,
    face_cycles: &[Vec<usize>],
) -> (out: Result<Mesh, MeshBuildError>)
    ensures
        match out {
            Result::Ok(m) => from_face_cycles_next_prev_face_coherent_spec(
                face_cycles_exec_to_model_spec(face_cycles@),
                m@,
            ),
            Result::Err(_) => true,
        },
{
    let out0 = ex_mesh_from_face_cycles(vertex_positions, face_cycles);
    match out0 {
        Result::Ok(m) => {
            let ok = runtime_check_from_face_cycles_next_prev_face_coherent(&m, face_cycles);
            if ok {
                Result::Ok(m)
            } else {
                Result::Err(mesh_build_error_empty_face_set())
            }
        }
        Result::Err(e) => Result::Err(e),
    }
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_twin_assignment_total_involution(m: &Mesh) -> (out: bool)
    ensures
        out ==> from_face_cycles_twin_assignment_total_involution_spec(m@),
{
    let hcnt = m.half_edges.len();
    let mut h: usize = 0;
    while h < hcnt
        invariant
            hcnt == m.half_edges.len(),
            0 <= h <= hcnt,
            forall|hp: int| 0 <= hp < h as int ==> 0 <= #[trigger] m@.half_edges[hp].twin < hcnt as int,
            forall|hp: int|
                0 <= hp < h as int ==> #[trigger] m@.half_edges[m@.half_edges[hp].twin].twin == hp,
    {
        let t = m.half_edges[h].twin;
        if t >= hcnt {
            return false;
        }
        let tt = m.half_edges[t].twin;
        if tt != h {
            return false;
        }

        proof {
            assert(mesh_half_edge_count_spec(m@) == hcnt as int);
            assert(m@.half_edges[h as int].twin == t as int);
            assert(m@.half_edges[t as int].twin == m.half_edges@[t as int].twin);
            assert(m.half_edges@[t as int].twin == tt as int);
            assert(tt == h);
            assert(m@.half_edges[t as int].twin == h as int);
            assert(0 <= #[trigger] m@.half_edges[h as int].twin < hcnt as int);
            assert(
                #[trigger] m@.half_edges[m@.half_edges[h as int].twin].twin
                    == m@.half_edges[t as int].twin
            );
            assert(#[trigger] m@.half_edges[m@.half_edges[h as int].twin].twin == h as int);
            assert(forall|hp: int|
                0 <= hp < (h + 1) as int ==> 0 <= #[trigger] m@.half_edges[hp].twin < hcnt as int) by {
                assert forall|hp: int|
                    0 <= hp < (h + 1) as int implies 0 <= #[trigger] m@.half_edges[hp].twin < hcnt as int by {
                    if hp < h as int {
                        assert(0 <= hp < h as int);
                    } else {
                        assert(hp == h as int);
                        assert(#[trigger] m@.half_edges[hp].twin == t as int);
                        assert(0 <= t as int);
                        assert((t as int) < hcnt as int);
                    }
                };
            }
            assert(forall|hp: int|
                0 <= hp < (h + 1) as int
                    ==> #[trigger] m@.half_edges[m@.half_edges[hp].twin].twin == hp) by {
                assert forall|hp: int|
                    0 <= hp < (h + 1) as int
                        implies #[trigger] m@.half_edges[m@.half_edges[hp].twin].twin == hp by {
                    if hp < h as int {
                        assert(0 <= hp < h as int);
                    } else {
                        assert(hp == h as int);
                        assert(#[trigger] m@.half_edges[m@.half_edges[hp].twin].twin == h as int);
                    }
                };
            }
        }

        h += 1;
    }

    proof {
        assert(h == hcnt);
        assert(mesh_half_edge_count_spec(m@) == hcnt as int);
        assert(forall|hp: int|
            0 <= hp < mesh_half_edge_count_spec(m@)
                ==> 0 <= #[trigger] m@.half_edges[hp].twin < mesh_half_edge_count_spec(m@)) by {
            assert forall|hp: int|
                0 <= hp < mesh_half_edge_count_spec(m@)
                    implies 0 <= #[trigger] m@.half_edges[hp].twin < mesh_half_edge_count_spec(m@) by {
                assert(mesh_half_edge_count_spec(m@) == h as int);
                assert(0 <= hp < h as int);
            };
        }
        assert(forall|hp: int|
            0 <= hp < mesh_half_edge_count_spec(m@)
                ==> #[trigger] m@.half_edges[m@.half_edges[hp].twin].twin == hp) by {
            assert forall|hp: int|
                0 <= hp < mesh_half_edge_count_spec(m@)
                    implies #[trigger] m@.half_edges[m@.half_edges[hp].twin].twin == hp by {
                assert(mesh_half_edge_count_spec(m@) == h as int);
                assert(0 <= hp < h as int);
            };
        }
        assert(from_face_cycles_twin_assignment_total_involution_spec(m@));
    }
    true
}

#[allow(dead_code)]
pub fn from_face_cycles_constructive_twin_assignment_total_involution(
    vertex_positions: Vec<RuntimePoint3>,
    face_cycles: &[Vec<usize>],
) -> (out: Result<Mesh, MeshBuildError>)
    ensures
        match out {
            Result::Ok(m) => from_face_cycles_twin_assignment_total_involution_spec(m@),
            Result::Err(_) => true,
        },
{
    let out0 = ex_mesh_from_face_cycles(vertex_positions, face_cycles);
    match out0 {
        Result::Ok(m) => {
            let ok = runtime_check_twin_assignment_total_involution(&m);
            if ok {
                Result::Ok(m)
            } else {
                Result::Err(mesh_build_error_empty_face_set())
            }
        }
        Result::Err(e) => Result::Err(e),
    }
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_edge_exactly_two_half_edges(m: &Mesh) -> (out: bool)
    ensures
        out ==> mesh_edge_exactly_two_half_edges_spec(m@),
{
    let hcnt = m.half_edges.len();
    let ecnt = m.edges.len();
    let mut e: usize = 0;
    while e < ecnt
        invariant
            hcnt == m.half_edges.len(),
            ecnt == m.edges.len(),
            0 <= e <= ecnt,
            forall|ep: int| 0 <= ep < e as int ==> mesh_edge_exactly_two_half_edges_at_spec(m@, ep),
    {
        let h0 = m.edges[e].half_edge;
        if h0 >= hcnt {
            return false;
        }
        let he0 = &m.half_edges[h0];
        if he0.edge != e {
            return false;
        }
        let h1 = he0.twin;
        if h1 >= hcnt || h1 == h0 {
            return false;
        }
        let he1 = &m.half_edges[h1];
        if he1.edge != e {
            return false;
        }
        if he1.twin != h0 {
            return false;
        }

        let mut h: usize = 0;
        while h < hcnt
            invariant
                hcnt == m.half_edges.len(),
                ecnt == m.edges.len(),
                0 <= e < ecnt,
                0 <= h <= hcnt,
                0 <= h0 < hcnt,
                0 <= h1 < hcnt,
                h0 != h1,
                m@.edge_half_edges[e as int] == h0 as int,
                m@.half_edges[h0 as int].edge == e as int,
                m@.half_edges[h0 as int].twin == h1 as int,
                m@.half_edges[h1 as int].edge == e as int,
                m@.half_edges[h1 as int].twin == h0 as int,
                forall|hp: int|
                    0 <= hp < h as int
                        ==> (#[trigger] m@.half_edges[hp].edge == e as int ==> (hp == h0 as int || hp == h1 as int)),
        {
            let edge_at_h = m.half_edges[h].edge;
            if edge_at_h == e {
                if h != h0 && h != h1 {
                    return false;
                }
            }

            proof {
                assert(m@.half_edges[h as int].edge == edge_at_h as int);
                assert(forall|hp: int|
                    0 <= hp < (h + 1) as int
                        ==> (#[trigger] m@.half_edges[hp].edge == e as int ==> (hp == h0 as int || hp == h1 as int))) by {
                    assert forall|hp: int|
                        0 <= hp < (h + 1) as int && #[trigger] m@.half_edges[hp].edge == e as int
                            implies (hp == h0 as int || hp == h1 as int) by {
                        if hp < h as int {
                            assert(0 <= hp < h as int);
                        } else {
                            assert(hp == h as int);
                            assert(edge_at_h as int == e as int);
                            if h != h0 {
                                assert(h == h1);
                            } else {
                                assert(h == h0);
                            }
                            assert(hp == h0 as int || hp == h1 as int);
                        }
                    };
                }
            }

            h += 1;
        }

        proof {
            assert(mesh_half_edge_count_spec(m@) == hcnt as int);
            assert(mesh_edge_count_spec(m@) == ecnt as int);
            assert(m@.edge_half_edges[e as int] == h0 as int);
            assert(m@.half_edges[h0 as int].twin == h1 as int);
            assert(m@.half_edges[h1 as int].twin == h0 as int);
            assert(m@.half_edges[h0 as int].edge == e as int);
            assert(m@.half_edges[h1 as int].edge == e as int);
            assert(forall|hp: int|
                0 <= hp < mesh_half_edge_count_spec(m@)
                    ==> (#[trigger] m@.half_edges[hp].edge == e as int ==> (hp == h0 as int || hp == h1 as int))) by {
                assert forall|hp: int|
                    0 <= hp < mesh_half_edge_count_spec(m@) && #[trigger] m@.half_edges[hp].edge == e as int
                        implies (hp == h0 as int || hp == h1 as int) by {
                    assert(mesh_half_edge_count_spec(m@) == h as int);
                    assert(0 <= hp < h as int);
                };
            }
            assert(mesh_edge_exactly_two_half_edges_at_spec(m@, e as int));
            assert(forall|ep: int|
                0 <= ep < (e + 1) as int ==> mesh_edge_exactly_two_half_edges_at_spec(m@, ep)) by {
                assert forall|ep: int|
                    0 <= ep < (e + 1) as int implies mesh_edge_exactly_two_half_edges_at_spec(m@, ep) by {
                    if ep < e as int {
                        assert(0 <= ep < e as int);
                    } else {
                        assert(ep == e as int);
                        assert(mesh_edge_exactly_two_half_edges_at_spec(m@, e as int));
                    }
                };
            }
        }

        e += 1;
    }

    proof {
        assert(mesh_edge_count_spec(m@) == ecnt as int);
        assert(forall|ep: int|
            0 <= ep < mesh_edge_count_spec(m@) ==> mesh_edge_exactly_two_half_edges_at_spec(m@, ep)) by {
            assert forall|ep: int|
                0 <= ep < mesh_edge_count_spec(m@) implies mesh_edge_exactly_two_half_edges_at_spec(m@, ep) by {
                assert(mesh_edge_count_spec(m@) == e as int);
                assert(0 <= ep < e as int);
            };
        }
        assert(mesh_edge_exactly_two_half_edges_spec(m@));
    }
    true
}

#[allow(dead_code)]
pub fn from_face_cycles_constructive_edge_exactly_two_half_edges(
    vertex_positions: Vec<RuntimePoint3>,
    face_cycles: &[Vec<usize>],
) -> (out: Result<Mesh, MeshBuildError>)
    ensures
        match out {
            Result::Ok(m) => mesh_edge_exactly_two_half_edges_spec(m@),
            Result::Err(_) => true,
        },
{
    let out0 = ex_mesh_from_face_cycles(vertex_positions, face_cycles);
    match out0 {
        Result::Ok(m) => {
            let ok = runtime_check_edge_exactly_two_half_edges(&m);
            if ok {
                Result::Ok(m)
            } else {
                Result::Err(mesh_build_error_empty_face_set())
            }
        }
        Result::Err(e) => Result::Err(e),
    }
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_vertex_representative_valid_nonisolated(m: &Mesh) -> (out: bool)
    ensures
        out ==> mesh_vertex_representative_valid_nonisolated_spec(m@),
{
    let hcnt = m.half_edges.len();
    let mut v: usize = 0;
    while v < m.vertices.len()
        invariant
            hcnt == m.half_edges.len(),
            0 <= v <= m.vertices.len(),
            forall|vp: int| 0 <= vp < v as int ==> {
                &&& 0 <= #[trigger] m@.vertex_half_edges[vp] < mesh_half_edge_count_spec(m@)
                &&& m@.half_edges[m@.vertex_half_edges[vp]].vertex == vp
            },
    {
        let h = m.vertices[v].half_edge;
        if h >= hcnt {
            return false;
        }
        let hv = m.half_edges[h].vertex;
        if hv != v {
            return false;
        }

        proof {
            assert(mesh_half_edge_count_spec(m@) == hcnt as int);
            assert(m@.vertex_half_edges[v as int] == h as int);
            assert(m@.half_edges[h as int].vertex == m.half_edges@[h as int].vertex);
            assert(m.half_edges@[h as int].vertex == hv as int);
            assert(m@.half_edges[h as int].vertex == v as int);
            assert(forall|vp: int| 0 <= vp < (v + 1) as int ==> {
                &&& 0 <= #[trigger] m@.vertex_half_edges[vp] < mesh_half_edge_count_spec(m@)
                &&& m@.half_edges[m@.vertex_half_edges[vp]].vertex == vp
            }) by {
                assert forall|vp: int|
                    0 <= vp < (v + 1) as int implies {
                        &&& 0 <= #[trigger] m@.vertex_half_edges[vp] < mesh_half_edge_count_spec(m@)
                        &&& m@.half_edges[m@.vertex_half_edges[vp]].vertex == vp
                    } by {
                    if vp < v as int {
                        assert(0 <= vp < v as int);
                    } else {
                        assert(vp == v as int);
                        assert(#[trigger] m@.vertex_half_edges[vp] == h as int);
                        assert(0 <= h as int);
                        assert((h as int) < mesh_half_edge_count_spec(m@));
                        assert(#[trigger] m@.half_edges[h as int].vertex == vp);
                    }
                };
            }
        }

        v += 1;
    }

    proof {
        assert(v == m.vertices.len());
        assert(mesh_vertex_count_spec(m@) == m.vertices.len() as int);
        assert(forall|vp: int| 0 <= vp < mesh_vertex_count_spec(m@) ==> {
            &&& 0 <= #[trigger] m@.vertex_half_edges[vp] < mesh_half_edge_count_spec(m@)
            &&& m@.half_edges[m@.vertex_half_edges[vp]].vertex == vp
        }) by {
            assert forall|vp: int|
                0 <= vp < mesh_vertex_count_spec(m@) implies {
                    &&& 0 <= #[trigger] m@.vertex_half_edges[vp] < mesh_half_edge_count_spec(m@)
                    &&& m@.half_edges[m@.vertex_half_edges[vp]].vertex == vp
                } by {
                assert(mesh_vertex_count_spec(m@) == v as int);
                assert(0 <= vp < v as int);
            };
        }
        assert(mesh_vertex_representative_valid_nonisolated_spec(m@));
    }
    true
}

#[allow(dead_code)]
pub fn from_face_cycles_constructive_vertex_representatives(
    vertex_positions: Vec<RuntimePoint3>,
    face_cycles: &[Vec<usize>],
) -> (out: Result<Mesh, MeshBuildError>)
    ensures
        match out {
            Result::Ok(m) => from_face_cycles_vertex_representatives_spec(m@),
            Result::Err(_) => true,
        },
{
    let out0 = ex_mesh_from_face_cycles(vertex_positions, face_cycles);
    match out0 {
        Result::Ok(m) => {
            let ok = runtime_check_vertex_representative_valid_nonisolated(&m);
            if ok {
                Result::Ok(m)
            } else {
                Result::Err(mesh_build_error_empty_face_set())
            }
        }
        Result::Err(e) => Result::Err(e),
    }
}

} // verus!
