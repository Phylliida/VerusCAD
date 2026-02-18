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

pub open spec fn mesh_half_edge_component_contains_spec(
    m: MeshModel,
    components: Seq<Vec<usize>>,
    c: int,
    h: int,
) -> bool {
    &&& 0 <= c < components.len() as int
    &&& 0 <= h < mesh_half_edge_count_spec(m)
    &&& exists|i: int|
        #![trigger mesh_half_edge_component_entry_spec(components, c, i)]
        0 <= i < components[c]@.len() as int
            && mesh_half_edge_component_entry_spec(components, c, i) == h
}

pub open spec fn mesh_half_edge_component_entry_spec(
    components: Seq<Vec<usize>>,
    c: int,
    i: int,
) -> int {
    components[c]@[i] as int
}

pub open spec fn mesh_half_edge_has_component_spec(
    m: MeshModel,
    components: Seq<Vec<usize>>,
    h: int,
) -> bool {
    exists|c: int| {
        &&& 0 <= c < components.len() as int
        &&& mesh_half_edge_component_contains_spec(m, components, c, h)
    }
}

pub open spec fn mesh_half_edge_components_cover_all_spec(
    m: MeshModel,
    components: Seq<Vec<usize>>,
) -> bool {
    let hcnt = mesh_half_edge_count_spec(m);
    forall|h: int|
        #![trigger mesh_half_edge_has_component_spec(m, components, h)]
        0 <= h < hcnt ==> mesh_half_edge_has_component_spec(m, components, h)
}

pub open spec fn mesh_half_edge_components_partition_spec(
    m: MeshModel,
    components: Seq<Vec<usize>>,
) -> bool {
    let hcnt = mesh_half_edge_count_spec(m);
    &&& forall|c: int|
        #![trigger components[c]@]
        0 <= c < components.len() as int ==> components[c]@.len() > 0
    &&& forall|c: int, i: int|
        #![trigger mesh_half_edge_component_entry_spec(components, c, i)]
        0 <= c < components.len() as int && 0 <= i < components[c]@.len() as int
            ==> 0 <= mesh_half_edge_component_entry_spec(components, c, i)
                && mesh_half_edge_component_entry_spec(components, c, i) < hcnt
    &&& forall|c: int, i: int, j: int|
        #![trigger mesh_half_edge_component_entry_spec(components, c, i), mesh_half_edge_component_entry_spec(components, c, j)]
        0 <= c < components.len() as int
            && 0 <= i
            && i < j
            && j < components[c]@.len() as int
            ==> mesh_half_edge_component_entry_spec(components, c, i)
                != mesh_half_edge_component_entry_spec(components, c, j)
    &&& mesh_half_edge_components_cover_all_spec(m, components)
    &&& forall|c1: int, c2: int, h: int|
        mesh_half_edge_component_contains_spec(m, components, c1, h)
            && mesh_half_edge_component_contains_spec(m, components, c2, h)
            ==> c1 == c2
}

pub open spec fn mesh_half_edge_component_neighbor_closed_at_spec(
    m: MeshModel,
    components: Seq<Vec<usize>>,
    c: int,
) -> bool {
    let hcnt = mesh_half_edge_count_spec(m);
    forall|h: int|
        #![trigger mesh_half_edge_component_contains_spec(m, components, c, h)]
        mesh_half_edge_component_contains_spec(m, components, c, h) ==> {
            let t = m.half_edges[h].twin;
            let n = m.half_edges[h].next;
            let p = m.half_edges[h].prev;
            &&& 0 <= t < hcnt
            &&& 0 <= n < hcnt
            &&& 0 <= p < hcnt
            &&& mesh_half_edge_component_contains_spec(m, components, c, t)
            &&& mesh_half_edge_component_contains_spec(m, components, c, n)
            &&& mesh_half_edge_component_contains_spec(m, components, c, p)
        }
}

pub open spec fn mesh_half_edge_components_neighbor_closed_spec(
    m: MeshModel,
    components: Seq<Vec<usize>>,
) -> bool {
    forall|c: int|
        #![trigger components[c]@]
        0 <= c < components.len() as int ==> mesh_half_edge_component_neighbor_closed_at_spec(m, components, c)
}

pub open spec fn mesh_half_edge_components_partition_neighbor_closed_spec(
    m: MeshModel,
    components: Seq<Vec<usize>>,
) -> bool {
    &&& mesh_half_edge_components_partition_spec(m, components)
    &&& mesh_half_edge_components_neighbor_closed_spec(m, components)
}

pub open spec fn mesh_component_count_partition_witness_spec(m: MeshModel, count: int) -> bool {
    exists|components: Seq<Vec<usize>>| {
        &&& mesh_half_edge_components_partition_neighbor_closed_spec(m, components)
        &&& count == components.len() as int
    }
}

pub open spec fn bool_true_count_prefix_spec(bits: Seq<bool>, n: int) -> int
    decreases if n <= 0 { 0 } else { n }
{
    if n <= 0 {
        0
    } else {
        bool_true_count_prefix_spec(bits, n - 1) + if bits[(n - 1) as int] { 1int } else { 0int }
    }
}

pub open spec fn bool_true_count_spec(bits: Seq<bool>) -> int {
    bool_true_count_prefix_spec(bits, bits.len() as int)
}

pub open spec fn mesh_component_has_vertex_spec(m: MeshModel, component: Seq<usize>, v: int) -> bool {
    &&& 0 <= v < mesh_vertex_count_spec(m)
    &&& exists|i: int| {
        &&& 0 <= i < component.len() as int
        &&& 0 <= (component[i] as int)
        &&& (component[i] as int) < mesh_half_edge_count_spec(m)
        &&& #[trigger] m.half_edges[(component[i] as int)].vertex == v
    }
}

pub open spec fn mesh_component_has_edge_spec(m: MeshModel, component: Seq<usize>, e: int) -> bool {
    &&& 0 <= e < mesh_edge_count_spec(m)
    &&& exists|i: int| {
        &&& 0 <= i < component.len() as int
        &&& 0 <= (component[i] as int)
        &&& (component[i] as int) < mesh_half_edge_count_spec(m)
        &&& #[trigger] m.half_edges[(component[i] as int)].edge == e
    }
}

pub open spec fn mesh_component_has_face_spec(m: MeshModel, component: Seq<usize>, f: int) -> bool {
    &&& 0 <= f < mesh_face_count_spec(m)
    &&& exists|i: int| {
        &&& 0 <= i < component.len() as int
        &&& 0 <= (component[i] as int)
        &&& (component[i] as int) < mesh_half_edge_count_spec(m)
        &&& #[trigger] m.half_edges[(component[i] as int)].face == f
    }
}

pub open spec fn mesh_component_euler_characteristic_witness_spec(
    m: MeshModel,
    component: Seq<usize>,
    chi: int,
    vertex_present: Seq<bool>,
    edge_present: Seq<bool>,
    face_present: Seq<bool>,
) -> bool {
    &&& vertex_present.len() == mesh_vertex_count_spec(m)
    &&& edge_present.len() == mesh_edge_count_spec(m)
    &&& face_present.len() == mesh_face_count_spec(m)
    &&& forall|v: int|
        #![trigger vertex_present[v]]
        0 <= v < mesh_vertex_count_spec(m)
            ==> (#[trigger] vertex_present[v] <==> mesh_component_has_vertex_spec(m, component, v))
    &&& forall|e: int|
        #![trigger edge_present[e]]
        0 <= e < mesh_edge_count_spec(m)
            ==> (#[trigger] edge_present[e] <==> mesh_component_has_edge_spec(m, component, e))
    &&& forall|f: int|
        #![trigger face_present[f]]
        0 <= f < mesh_face_count_spec(m)
            ==> (#[trigger] face_present[f] <==> mesh_component_has_face_spec(m, component, f))
    &&& chi
        == bool_true_count_spec(vertex_present) - bool_true_count_spec(edge_present)
            + bool_true_count_spec(face_present)
}

pub open spec fn mesh_component_euler_characteristic_spec(
    m: MeshModel,
    component: Seq<usize>,
    chi: int,
) -> bool {
    exists|vertex_present: Seq<bool>, edge_present: Seq<bool>, face_present: Seq<bool>| {
        &&& mesh_component_euler_characteristic_witness_spec(
            m,
            component,
            chi,
            vertex_present,
            edge_present,
            face_present,
        )
    }
}

pub open spec fn mesh_euler_characteristics_per_component_spec(
    m: MeshModel,
    components: Seq<Vec<usize>>,
    chis: Seq<isize>,
) -> bool {
    &&& chis.len() == components.len()
    &&& forall|c: int|
        #![trigger components[c]@]
        0 <= c < components.len() as int
            ==> mesh_component_euler_characteristic_spec(m, components[c]@, chis[c] as int)
}

pub open spec fn mesh_euler_characteristics_partition_witness_spec(
    m: MeshModel,
    chis: Seq<isize>,
) -> bool {
    exists|components: Seq<Vec<usize>>| {
        &&& mesh_half_edge_components_partition_neighbor_closed_spec(m, components)
        &&& mesh_euler_characteristics_per_component_spec(m, components, chis)
    }
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
pub fn runtime_check_from_face_cycles_basic_input(
    vertex_count: usize,
    face_cycles: &[Vec<usize>],
) -> (out: bool)
    ensures
        out ==> from_face_cycles_basic_input_spec(
            vertex_count as int,
            face_cycles_exec_to_model_spec(face_cycles@),
        ),
{
    if vertex_count == 0 {
        return false;
    }
    if face_cycles.len() == 0 {
        return false;
    }

    let ghost model_cycles = face_cycles_exec_to_model_spec(face_cycles@);
    proof {
        assert(model_cycles.len() == face_cycles.len() as int);
    }

    let mut f: usize = 0;
    while f < face_cycles.len()
        invariant
            vertex_count > 0,
            face_cycles.len() > 0,
            0 <= f <= face_cycles.len(),
            model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
            model_cycles.len() == face_cycles.len() as int,
            forall|fp: int|
                #![trigger model_cycles[fp]]
                0 <= fp < f as int ==> {
                    let n = model_cycles[fp].len() as int;
                    &&& n >= 3
                    &&& forall|ip: int|
                        #![trigger model_cycles[fp][ip]]
                        0 <= ip < n ==> 0 <= model_cycles[fp][ip] < vertex_count as int
                },
    {
        let face = vstd::slice::slice_index_get(face_cycles, f);
        let n = face.len();
        if n < 3 {
            return false;
        }

        proof {
            assert(*face == face_cycles@.index(f as int));
            lemma_face_cycles_exec_to_model_face_len_exec(face_cycles, f, face, n);
            assert(model_cycles[f as int].len() == n as int);
        }

        let mut i: usize = 0;
        while i < n
            invariant
                vertex_count > 0,
                face_cycles.len() > 0,
                0 <= f < face_cycles.len(),
                0 <= i <= n,
                n == face.len(),
                face@.len() == n as int,
                *face == face_cycles@.index(f as int),
                model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
                model_cycles.len() == face_cycles.len() as int,
                model_cycles[f as int].len() == n as int,
                n >= 3,
                forall|fp: int|
                    #![trigger model_cycles[fp]]
                    0 <= fp < f as int ==> {
                        let nfp = model_cycles[fp].len() as int;
                        &&& nfp >= 3
                        &&& forall|ip: int|
                            #![trigger model_cycles[fp][ip]]
                            0 <= ip < nfp ==> 0 <= model_cycles[fp][ip] < vertex_count as int
                    },
                forall|ip: int|
                    #![trigger model_cycles[f as int][ip]]
                    0 <= ip < i as int ==> 0 <= model_cycles[f as int][ip] < vertex_count as int,
        {
            proof {
                assert(i < n);
                assert(n == face.len());
            }
            let v = face[i];
            if v >= vertex_count {
                return false;
            }

            proof {
                assert(0 <= i as int);
                assert((i as int) < (n as int));
                assert(face@.len() == face.len());
                assert(face.len() == n);
                assert(face@.len() == n as int);
                assert(face@[i as int] == v);
                assert(face_cycles@.index(f as int) == face_cycles@[f as int]);
                assert(face_cycles@[f as int] == *face);
                assert(model_cycles[f as int]
                    == Seq::new(face_cycles@[f as int]@.len(), |j: int| face_cycles@[f as int]@[j] as int));
                assert(model_cycles[f as int][i as int] == face_cycles@[f as int]@[i as int] as int);
                assert(model_cycles[f as int][i as int] == v as int);
                assert(0 <= model_cycles[f as int][i as int] < vertex_count as int);
                assert(forall|ip: int|
                    #![trigger model_cycles[f as int][ip]]
                    0 <= ip < (i + 1) as int ==> 0 <= model_cycles[f as int][ip] < vertex_count as int) by {
                    assert forall|ip: int|
                        #![trigger model_cycles[f as int][ip]]
                        0 <= ip < (i + 1) as int
                            implies 0 <= model_cycles[f as int][ip] < vertex_count as int by {
                        if ip < i as int {
                            assert(0 <= ip < i as int);
                        } else {
                            assert(ip == i as int);
                            assert(model_cycles[f as int][ip] == v as int);
                        }
                    };
                }
            }

            i += 1;
        }

        proof {
            assert(i == n);
            assert(forall|fp: int|
                #![trigger model_cycles[fp]]
                0 <= fp < (f + 1) as int ==> {
                    let nfp = model_cycles[fp].len() as int;
                    &&& nfp >= 3
                    &&& forall|ip: int|
                        #![trigger model_cycles[fp][ip]]
                        0 <= ip < nfp ==> 0 <= model_cycles[fp][ip] < vertex_count as int
                }) by {
                assert forall|fp: int|
                    #![trigger model_cycles[fp]]
                    0 <= fp < (f + 1) as int implies {
                        let nfp = model_cycles[fp].len() as int;
                        &&& nfp >= 3
                        &&& forall|ip: int|
                            #![trigger model_cycles[fp][ip]]
                            0 <= ip < nfp ==> 0 <= model_cycles[fp][ip] < vertex_count as int
                    } by {
                    if fp < f as int {
                    } else {
                        assert(fp == f as int);
                        assert(model_cycles[fp].len() == n as int);
                        assert(n as int >= 3);
                        assert(forall|ip: int|
                            #![trigger model_cycles[f as int][ip]]
                            0 <= ip < i as int ==> 0 <= model_cycles[f as int][ip] < vertex_count as int);
                        assert(forall|ip: int|
                            #![trigger model_cycles[fp][ip]]
                            0 <= ip < model_cycles[fp].len() as int
                                ==> 0 <= model_cycles[fp][ip] < vertex_count as int);
                    }
                };
            };
        }

        f += 1;
    }

    proof {
        assert(f == face_cycles.len());
        assert(vertex_count as int > 0);
        assert(face_cycles.len() as int > 0);
        assert(forall|fp: int|
            #![trigger model_cycles[fp]]
            0 <= fp < face_cycles.len() as int ==> {
                let nfp = model_cycles[fp].len() as int;
                &&& nfp >= 3
                &&& forall|ip: int|
                    #![trigger model_cycles[fp][ip]]
                    0 <= ip < nfp ==> 0 <= model_cycles[fp][ip] < vertex_count as int
            }) by {
            assert forall|fp: int|
                #![trigger model_cycles[fp]]
                0 <= fp < face_cycles.len() as int implies {
                    let nfp = model_cycles[fp].len() as int;
                    &&& nfp >= 3
                    &&& forall|ip: int|
                        #![trigger model_cycles[fp][ip]]
                        0 <= ip < nfp ==> 0 <= model_cycles[fp][ip] < vertex_count as int
                } by {
                assert(face_cycles.len() as int == f as int);
                assert(0 <= fp < f as int);
            };
        };
        assert(from_face_cycles_basic_input_spec(vertex_count as int, model_cycles));
    }
    true
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
            Result::Ok(m) => {
                &&& from_face_cycles_basic_input_spec(
                    vertex_positions@.len() as int,
                    face_cycles_exec_to_model_spec(face_cycles@),
                )
                &&& from_face_cycles_next_prev_face_coherent_spec(
                    face_cycles_exec_to_model_spec(face_cycles@),
                    m@,
                )
            }
            Result::Err(_) => true,
        },
{
    let vertex_count = vertex_positions.len();
    let input_ok = runtime_check_from_face_cycles_basic_input(vertex_count, face_cycles);
    if !input_ok {
        return Result::Err(mesh_build_error_empty_face_set());
    }

    let out0 = ex_mesh_from_face_cycles(vertex_positions, face_cycles);
    match out0 {
        Result::Ok(m) => {
            let ok = runtime_check_from_face_cycles_next_prev_face_coherent(&m, face_cycles);
            if ok {
                proof {
                    assert(input_ok);
                    assert(from_face_cycles_basic_input_spec(
                        vertex_count as int,
                        face_cycles_exec_to_model_spec(face_cycles@),
                    ));
                }
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
            forall|hp: int| 0 <= hp < h as int ==> 0 <= #[trigger] m@.half_edges[hp].twin < (hcnt as int),
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
            assert(0 <= #[trigger] m@.half_edges[h as int].twin < (hcnt as int));
            assert(
                #[trigger] m@.half_edges[m@.half_edges[h as int].twin].twin
                    == m@.half_edges[t as int].twin
            );
            assert(#[trigger] m@.half_edges[m@.half_edges[h as int].twin].twin == h as int);
            assert(forall|hp: int|
                0 <= hp < (h + 1) as int ==> 0 <= #[trigger] m@.half_edges[hp].twin < (hcnt as int)) by {
                assert forall|hp: int|
                    0 <= hp < (h + 1) as int implies 0 <= #[trigger] m@.half_edges[hp].twin < (hcnt as int) by {
                    if hp < h as int {
                        assert(0 <= hp < h as int);
                    } else {
                        assert(hp == h as int);
                        assert(#[trigger] m@.half_edges[hp].twin == t as int);
                        assert(0 <= t as int);
                        assert((t as int) < (hcnt as int));
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

#[verifier::external_body]
pub fn ex_mesh_half_edge_components(m: &Mesh) -> (out: Vec<Vec<usize>>)
{
    m.half_edge_components_for_verification()
}

#[verifier::external_body]
pub fn ex_mesh_component_count(m: &Mesh) -> (out: usize)
{
    m.component_count()
}

#[verifier::external_body]
pub fn ex_mesh_euler_characteristics_per_component(m: &Mesh) -> (out: Vec<isize>)
{
    m.euler_characteristics_per_component()
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_count_true(bits: &[bool]) -> (out: usize)
    ensures
        out as int == bool_true_count_spec(bits@),
{
    let mut i: usize = 0;
    let mut count: usize = 0;

    while i < bits.len()
        invariant
            0 <= i <= bits.len(),
            0 <= count <= i,
            count as int == bool_true_count_prefix_spec(bits@, i as int),
    {
        let bit = bits[i];
        let ghost count_before = count as int;
        if bit {
            count += 1;
        }
        proof {
            assert(bit == bits@[i as int]);
            assert(count_before == bool_true_count_prefix_spec(bits@, i as int));
            assert(bool_true_count_prefix_spec(bits@, (i + 1) as int)
                == bool_true_count_prefix_spec(bits@, i as int) + if bits@[i as int] { 1int } else { 0int });
            if bit {
                assert(count as int == count_before + 1);
            } else {
                assert(count as int == count_before);
            }
            assert(count as int == bool_true_count_prefix_spec(bits@, (i + 1) as int));
            assert(0 <= count);
            assert(count <= i + 1);
        }
        i += 1;
    }

    proof {
        assert(i == bits.len());
        assert(bool_true_count_spec(bits@) == bool_true_count_prefix_spec(bits@, i as int));
    }

    count
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_component_euler_characteristic(
    m: &Mesh,
    component: &[usize],
    chi: isize,
) -> (out: bool)
    ensures
        out ==> mesh_component_euler_characteristic_spec(m@, component@, chi as int),
{
    let hcnt = m.half_edges.len();
    let vcnt = m.vertices.len();
    let ecnt = m.edges.len();
    let fcnt = m.faces.len();

    let mut vertex_present = vec![false; vcnt];
    let mut edge_present = vec![false; ecnt];
    let mut face_present = vec![false; fcnt];

    let mut i: usize = 0;
    while i < component.len()
        invariant
            hcnt == m.half_edges.len(),
            vcnt == m.vertices.len(),
            ecnt == m.edges.len(),
            fcnt == m.faces.len(),
            0 <= i <= component.len(),
            vertex_present@.len() == vcnt as int,
            edge_present@.len() == ecnt as int,
            face_present@.len() == fcnt as int,
            forall|ip: int|
                #![trigger component@[ip]]
                0 <= ip < i as int ==> 0 <= (component@[ip] as int) && (component@[ip] as int) < hcnt as int,
    {
        let h = component[i];
        if h >= hcnt {
            return false;
        }
        let he = &m.half_edges[h];
        let v = he.vertex;
        let e = he.edge;
        let f = he.face;
        if v >= vcnt || e >= ecnt || f >= fcnt {
            return false;
        }

        vertex_present[v] = true;
        edge_present[e] = true;
        face_present[f] = true;

        proof {
            assert(component@[i as int] == h);
            assert(forall|ip: int|
                #![trigger component@[ip]]
                0 <= ip < (i + 1) as int
                    ==> 0 <= (component@[ip] as int) && (component@[ip] as int) < hcnt as int) by {
                assert forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < (i + 1) as int
                        implies 0 <= (component@[ip] as int) && (component@[ip] as int) < hcnt as int by {
                    if ip < i as int {
                    } else {
                        assert(ip == i as int);
                        assert(component@[ip] as int == h as int);
                        assert(0 <= h as int);
                        assert((h as int) < (hcnt as int));
                    }
                };
            }
        }

        i += 1;
    }

    let mut j: usize = 0;
    while j < component.len()
        invariant
            hcnt == m.half_edges.len(),
            vcnt == m.vertices.len(),
            ecnt == m.edges.len(),
            fcnt == m.faces.len(),
            i == component.len(),
            0 <= j <= component.len(),
            vertex_present@.len() == vcnt as int,
            edge_present@.len() == ecnt as int,
            face_present@.len() == fcnt as int,
            forall|ip: int|
                #![trigger component@[ip]]
                0 <= ip < component@.len() as int
                    ==> 0 <= (component@[ip] as int) && (component@[ip] as int) < hcnt as int,
            forall|ip: int|
                #![trigger component@[ip]]
                0 <= ip < j as int ==> {
                    &&& #[trigger] vertex_present@[m@.half_edges[component@[ip] as int].vertex]
                    &&& #[trigger] edge_present@[m@.half_edges[component@[ip] as int].edge]
                    &&& #[trigger] face_present@[m@.half_edges[component@[ip] as int].face]
                },
    {
        let h = component[j];
        if h >= hcnt {
            return false;
        }
        let he = &m.half_edges[h];
        let hv = he.vertex;
        let hee = he.edge;
        let hf = he.face;
        if hv >= vcnt || hee >= ecnt || hf >= fcnt {
            return false;
        }
        if !vertex_present[hv] || !edge_present[hee] || !face_present[hf] {
            return false;
        }

        proof {
            assert(component@[j as int] == h);
            assert(forall|ip: int|
                #![trigger component@[ip]]
                0 <= ip < (j + 1) as int ==> {
                    &&& #[trigger] vertex_present@[m@.half_edges[component@[ip] as int].vertex]
                    &&& #[trigger] edge_present@[m@.half_edges[component@[ip] as int].edge]
                    &&& #[trigger] face_present@[m@.half_edges[component@[ip] as int].face]
                }) by {
                assert forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < (j + 1) as int implies {
                        &&& #[trigger] vertex_present@[m@.half_edges[component@[ip] as int].vertex]
                        &&& #[trigger] edge_present@[m@.half_edges[component@[ip] as int].edge]
                        &&& #[trigger] face_present@[m@.half_edges[component@[ip] as int].face]
                    } by {
                    if ip < j as int {
                    } else {
                        assert(ip == j as int);
                        assert(component@[ip] as int == h as int);
                        assert(vertex_present@[m@.half_edges[h as int].vertex]);
                        assert(edge_present@[m@.half_edges[h as int].edge]);
                        assert(face_present@[m@.half_edges[h as int].face]);
                    }
                };
            }
        }

        j += 1;
    }

    let mut v: usize = 0;
    while v < vcnt
        invariant
            hcnt == m.half_edges.len(),
            vcnt == m.vertices.len(),
            i == component.len(),
            j == component.len(),
            0 <= v <= vcnt,
            vertex_present@.len() == vcnt as int,
            forall|ip: int|
                #![trigger component@[ip]]
                0 <= ip < component@.len() as int ==> {
                    &&& 0 <= (component@[ip] as int)
                    &&& (component@[ip] as int) < hcnt as int
                    &&& #[trigger] vertex_present@[m@.half_edges[component@[ip] as int].vertex]
                },
            forall|ip: int|
                #![trigger component@[ip]]
                0 <= ip < component@.len() as int
                    ==> #[trigger] edge_present@[m@.half_edges[component@[ip] as int].edge],
            forall|ip: int|
                #![trigger component@[ip]]
                0 <= ip < component@.len() as int
                    ==> #[trigger] face_present@[m@.half_edges[component@[ip] as int].face],
            forall|vp: int|
                0 <= vp < v as int && #[trigger] vertex_present@[vp] ==> exists|ip: int| {
                    &&& 0 <= ip < component@.len() as int
                    &&& #[trigger] m@.half_edges[component@[ip] as int].vertex == vp
                },
    {
        if vertex_present[v] {
            let mut found = false;
            let mut ip: usize = 0;
            while ip < component.len()
                invariant
                    hcnt == m.half_edges.len(),
                    0 <= ip <= component.len(),
                    0 <= v < vcnt,
                    found <==> exists|jp: int| {
                        &&& 0 <= jp < ip as int
                        &&& #[trigger] m@.half_edges[component@[jp] as int].vertex == v as int
                    },
            {
                let h = component[ip];
                if h >= hcnt {
                    return false;
                }
                if m.half_edges[h].vertex == v {
                    found = true;
                }
                proof {
                    assert(component@[ip as int] == h);
                    if m@.half_edges[h as int].vertex == v as int {
                        assert(exists|jp: int| {
                            &&& 0 <= jp < (ip + 1) as int
                            &&& #[trigger] m@.half_edges[component@[jp] as int].vertex == v as int
                        });
                    } else {
                        assert((exists|jp: int| {
                            &&& 0 <= jp < (ip + 1) as int
                            &&& #[trigger] m@.half_edges[component@[jp] as int].vertex == v as int
                        }) <==> (exists|jp: int| {
                            &&& 0 <= jp < ip as int
                            &&& #[trigger] m@.half_edges[component@[jp] as int].vertex == v as int
                        }));
                    }
                    assert(found <==> exists|jp: int| {
                        &&& 0 <= jp < (ip + 1) as int
                        &&& #[trigger] m@.half_edges[component@[jp] as int].vertex == v as int
                    });
                }
                ip += 1;
            }
            if !found {
                return false;
            }
        }

        proof {
            assert(forall|vp: int|
                0 <= vp < (v + 1) as int && #[trigger] vertex_present@[vp] ==> exists|ip: int| {
                    &&& 0 <= ip < component@.len() as int
                    &&& #[trigger] m@.half_edges[component@[ip] as int].vertex == vp
                }) by {
                assert forall|vp: int|
                    0 <= vp < (v + 1) as int && #[trigger] vertex_present@[vp] implies exists|ip: int| {
                        &&& 0 <= ip < component@.len() as int
                        &&& #[trigger] m@.half_edges[component@[ip] as int].vertex == vp
                    } by {
                    if vp < v as int {
                    } else {
                        assert(vp == v as int);
                        assert(vertex_present@[vp]);
                        assert(v as int == vp);
                        assert(exists|ip: int| {
                            &&& 0 <= ip < component@.len() as int
                            &&& #[trigger] m@.half_edges[component@[ip] as int].vertex == vp
                        });
                    }
                };
            }
        }

        v += 1;
    }

    let mut e: usize = 0;
    while e < ecnt
        invariant
            hcnt == m.half_edges.len(),
            ecnt == m.edges.len(),
            i == component.len(),
            0 <= e <= ecnt,
            edge_present@.len() == ecnt as int,
            forall|ip: int|
                #![trigger component@[ip]]
                0 <= ip < component@.len() as int ==> {
                    &&& 0 <= (component@[ip] as int)
                    &&& (component@[ip] as int) < hcnt as int
                    &&& #[trigger] edge_present@[m@.half_edges[component@[ip] as int].edge]
                },
            forall|ip: int|
                #![trigger component@[ip]]
                0 <= ip < component@.len() as int
                    ==> #[trigger] vertex_present@[m@.half_edges[component@[ip] as int].vertex],
            forall|ip: int|
                #![trigger component@[ip]]
                0 <= ip < component@.len() as int
                    ==> #[trigger] face_present@[m@.half_edges[component@[ip] as int].face],
            forall|ep: int|
                0 <= ep < e as int && #[trigger] edge_present@[ep] ==> exists|ip: int| {
                    &&& 0 <= ip < component@.len() as int
                    &&& #[trigger] m@.half_edges[component@[ip] as int].edge == ep
                },
    {
        if edge_present[e] {
            let mut found = false;
            let mut ip: usize = 0;
            while ip < component.len()
                invariant
                    hcnt == m.half_edges.len(),
                    0 <= ip <= component.len(),
                    0 <= e < ecnt,
                    found <==> exists|jp: int| {
                        &&& 0 <= jp < ip as int
                        &&& #[trigger] m@.half_edges[component@[jp] as int].edge == e as int
                    },
            {
                let h = component[ip];
                if h >= hcnt {
                    return false;
                }
                if m.half_edges[h].edge == e {
                    found = true;
                }
                proof {
                    assert(component@[ip as int] == h);
                    if m@.half_edges[h as int].edge == e as int {
                        assert(exists|jp: int| {
                            &&& 0 <= jp < (ip + 1) as int
                            &&& #[trigger] m@.half_edges[component@[jp] as int].edge == e as int
                        });
                    } else {
                        assert((exists|jp: int| {
                            &&& 0 <= jp < (ip + 1) as int
                            &&& #[trigger] m@.half_edges[component@[jp] as int].edge == e as int
                        }) <==> (exists|jp: int| {
                            &&& 0 <= jp < ip as int
                            &&& #[trigger] m@.half_edges[component@[jp] as int].edge == e as int
                        }));
                    }
                    assert(found <==> exists|jp: int| {
                        &&& 0 <= jp < (ip + 1) as int
                        &&& #[trigger] m@.half_edges[component@[jp] as int].edge == e as int
                    });
                }
                ip += 1;
            }
            if !found {
                return false;
            }
        }

        proof {
            assert(forall|ep: int|
                0 <= ep < (e + 1) as int && #[trigger] edge_present@[ep] ==> exists|ip: int| {
                    &&& 0 <= ip < component@.len() as int
                    &&& #[trigger] m@.half_edges[component@[ip] as int].edge == ep
                }) by {
                assert forall|ep: int|
                    0 <= ep < (e + 1) as int && #[trigger] edge_present@[ep] implies exists|ip: int| {
                        &&& 0 <= ip < component@.len() as int
                        &&& #[trigger] m@.half_edges[component@[ip] as int].edge == ep
                    } by {
                    if ep < e as int {
                    } else {
                        assert(ep == e as int);
                        assert(edge_present@[ep]);
                        assert(exists|ip: int| {
                            &&& 0 <= ip < component@.len() as int
                            &&& #[trigger] m@.half_edges[component@[ip] as int].edge == ep
                        });
                    }
                };
            }
        }

        e += 1;
    }

    let mut f: usize = 0;
    while f < fcnt
        invariant
            hcnt == m.half_edges.len(),
            fcnt == m.faces.len(),
            i == component.len(),
            0 <= f <= fcnt,
            face_present@.len() == fcnt as int,
            forall|ip: int|
                #![trigger component@[ip]]
                0 <= ip < component@.len() as int ==> {
                    &&& 0 <= (component@[ip] as int)
                    &&& (component@[ip] as int) < hcnt as int
                    &&& #[trigger] face_present@[m@.half_edges[component@[ip] as int].face]
                },
            forall|ip: int|
                #![trigger component@[ip]]
                0 <= ip < component@.len() as int
                    ==> #[trigger] vertex_present@[m@.half_edges[component@[ip] as int].vertex],
            forall|ip: int|
                #![trigger component@[ip]]
                0 <= ip < component@.len() as int
                    ==> #[trigger] edge_present@[m@.half_edges[component@[ip] as int].edge],
            forall|fp: int|
                0 <= fp < f as int && #[trigger] face_present@[fp] ==> exists|ip: int| {
                    &&& 0 <= ip < component@.len() as int
                    &&& #[trigger] m@.half_edges[component@[ip] as int].face == fp
                },
    {
        if face_present[f] {
            let mut found = false;
            let mut ip: usize = 0;
            while ip < component.len()
                invariant
                    hcnt == m.half_edges.len(),
                    0 <= ip <= component.len(),
                    0 <= f < fcnt,
                    found <==> exists|jp: int| {
                        &&& 0 <= jp < ip as int
                        &&& #[trigger] m@.half_edges[component@[jp] as int].face == f as int
                    },
            {
                let h = component[ip];
                if h >= hcnt {
                    return false;
                }
                if m.half_edges[h].face == f {
                    found = true;
                }
                proof {
                    assert(component@[ip as int] == h);
                    if m@.half_edges[h as int].face == f as int {
                        assert(exists|jp: int| {
                            &&& 0 <= jp < (ip + 1) as int
                            &&& #[trigger] m@.half_edges[component@[jp] as int].face == f as int
                        });
                    } else {
                        assert((exists|jp: int| {
                            &&& 0 <= jp < (ip + 1) as int
                            &&& #[trigger] m@.half_edges[component@[jp] as int].face == f as int
                        }) <==> (exists|jp: int| {
                            &&& 0 <= jp < ip as int
                            &&& #[trigger] m@.half_edges[component@[jp] as int].face == f as int
                        }));
                    }
                    assert(found <==> exists|jp: int| {
                        &&& 0 <= jp < (ip + 1) as int
                        &&& #[trigger] m@.half_edges[component@[jp] as int].face == f as int
                    });
                }
                ip += 1;
            }
            if !found {
                return false;
            }
        }

        proof {
            assert(forall|fp: int|
                0 <= fp < (f + 1) as int && #[trigger] face_present@[fp] ==> exists|ip: int| {
                    &&& 0 <= ip < component@.len() as int
                    &&& #[trigger] m@.half_edges[component@[ip] as int].face == fp
                }) by {
                assert forall|fp: int|
                    0 <= fp < (f + 1) as int && #[trigger] face_present@[fp] implies exists|ip: int| {
                        &&& 0 <= ip < component@.len() as int
                        &&& #[trigger] m@.half_edges[component@[ip] as int].face == fp
                    } by {
                    if fp < f as int {
                    } else {
                        assert(fp == f as int);
                        assert(face_present@[fp]);
                        assert(exists|ip: int| {
                            &&& 0 <= ip < component@.len() as int
                            &&& #[trigger] m@.half_edges[component@[ip] as int].face == fp
                        });
                    }
                };
            }
        }

        f += 1;
    }

    let vcount = runtime_count_true(&vertex_present);
    let ecount = runtime_count_true(&edge_present);
    let fcount = runtime_count_true(&face_present);
    let expected = vcount as i128 - ecount as i128 + fcount as i128;
    if chi as i128 != expected {
        return false;
    }

    proof {
        assert(i == component.len());
        assert(v == vcnt);
        assert(e == ecnt);
        assert(f == fcnt);
        assert(forall|vp: int|
            0 <= vp < mesh_vertex_count_spec(m@)
                ==> (#[trigger] vertex_present@[vp] <==> mesh_component_has_vertex_spec(
                    m@,
                    component@,
                    vp,
                ))) by {
            assert forall|vp: int|
                0 <= vp < mesh_vertex_count_spec(m@) implies (#[trigger] vertex_present@[vp]
                    <==> mesh_component_has_vertex_spec(m@, component@, vp)) by {
                if vertex_present@[vp] {
                    assert(exists|ip: int| {
                        &&& 0 <= ip < component@.len() as int
                        &&& #[trigger] m@.half_edges[component@[ip] as int].vertex == vp
                    });
                    assert(mesh_component_has_vertex_spec(m@, component@, vp));
                } else if mesh_component_has_vertex_spec(m@, component@, vp) {
                    let ip = choose|ip: int| {
                        &&& 0 <= ip < component@.len() as int
                        &&& 0 <= (component@[ip] as int)
                        &&& (component@[ip] as int) < mesh_half_edge_count_spec(m@)
                        &&& #[trigger] m@.half_edges[(component@[ip] as int)].vertex == vp
                    };
                    assert(0 <= ip < component@.len() as int);
                    let h = component@[ip] as int;
                    assert(0 <= h < hcnt as int);
                    assert(#[trigger] vertex_present@[m@.half_edges[h].vertex]);
                    assert(m@.half_edges[h].vertex == vp);
                    assert(vertex_present@[vp]);
                }
            };
        }
        assert(forall|ep: int|
            0 <= ep < mesh_edge_count_spec(m@)
                ==> (#[trigger] edge_present@[ep] <==> mesh_component_has_edge_spec(
                    m@,
                    component@,
                    ep,
                ))) by {
            assert forall|ep: int|
                0 <= ep < mesh_edge_count_spec(m@) implies (#[trigger] edge_present@[ep]
                    <==> mesh_component_has_edge_spec(m@, component@, ep)) by {
                if edge_present@[ep] {
                    assert(exists|ip: int| {
                        &&& 0 <= ip < component@.len() as int
                        &&& #[trigger] m@.half_edges[component@[ip] as int].edge == ep
                    });
                    assert(mesh_component_has_edge_spec(m@, component@, ep));
                } else if mesh_component_has_edge_spec(m@, component@, ep) {
                    let ip = choose|ip: int| {
                        &&& 0 <= ip < component@.len() as int
                        &&& 0 <= (component@[ip] as int)
                        &&& (component@[ip] as int) < mesh_half_edge_count_spec(m@)
                        &&& #[trigger] m@.half_edges[(component@[ip] as int)].edge == ep
                    };
                    assert(0 <= ip < component@.len() as int);
                    let h = component@[ip] as int;
                    assert(0 <= h < hcnt as int);
                    assert(#[trigger] edge_present@[m@.half_edges[h].edge]);
                    assert(m@.half_edges[h].edge == ep);
                    assert(edge_present@[ep]);
                }
            };
        }
        assert(forall|fp: int|
            0 <= fp < mesh_face_count_spec(m@)
                ==> (#[trigger] face_present@[fp] <==> mesh_component_has_face_spec(
                    m@,
                    component@,
                    fp,
                ))) by {
            assert forall|fp: int|
                0 <= fp < mesh_face_count_spec(m@) implies (#[trigger] face_present@[fp]
                    <==> mesh_component_has_face_spec(m@, component@, fp)) by {
                if face_present@[fp] {
                    assert(exists|ip: int| {
                        &&& 0 <= ip < component@.len() as int
                        &&& #[trigger] m@.half_edges[component@[ip] as int].face == fp
                    });
                    assert(mesh_component_has_face_spec(m@, component@, fp));
                } else if mesh_component_has_face_spec(m@, component@, fp) {
                    let ip = choose|ip: int| {
                        &&& 0 <= ip < component@.len() as int
                        &&& 0 <= (component@[ip] as int)
                        &&& (component@[ip] as int) < mesh_half_edge_count_spec(m@)
                        &&& #[trigger] m@.half_edges[(component@[ip] as int)].face == fp
                    };
                    assert(0 <= ip < component@.len() as int);
                    let h = component@[ip] as int;
                    assert(0 <= h < hcnt as int);
                    assert(#[trigger] face_present@[m@.half_edges[h].face]);
                    assert(m@.half_edges[h].face == fp);
                    assert(face_present@[fp]);
                }
            };
        }
        assert(vcount as int == bool_true_count_spec(vertex_present@));
        assert(ecount as int == bool_true_count_spec(edge_present@));
        assert(fcount as int == bool_true_count_spec(face_present@));
        assert(chi as int == expected as int);
        assert(expected as int == vcount as int - ecount as int + fcount as int);
        assert(mesh_component_euler_characteristic_witness_spec(
            m@,
            component@,
            chi as int,
            vertex_present@,
            edge_present@,
            face_present@,
        ));
        assert(mesh_component_euler_characteristic_spec(m@, component@, chi as int));
    }

    true
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_euler_characteristics_per_component(
    m: &Mesh,
    components: &[Vec<usize>],
    chis: &[isize],
) -> (out: bool)
    ensures
        out ==> mesh_euler_characteristics_per_component_spec(m@, components@, chis@),
{
    if chis.len() != components.len() {
        return false;
    }

    let mut c: usize = 0;
    while c < components.len()
        invariant
            c <= components.len(),
            chis@.len() == components@.len(),
            forall|cp: int|
                #![trigger components@[cp]@]
                0 <= cp < c as int
                    ==> mesh_component_euler_characteristic_spec(
                        m@,
                        components@[cp]@,
                        chis@[cp] as int,
                    ),
    {
        let component = vstd::slice::slice_index_get(components, c);
        let chi = *vstd::slice::slice_index_get(chis, c);
        let ok = runtime_check_component_euler_characteristic(m, component, chi);
        if !ok {
            return false;
        }
        proof {
            assert(*component == components@.index(c as int));
            assert(chi == chis@[c as int]);
            assert(mesh_component_euler_characteristic_spec(m@, component@, chi as int));
            assert(mesh_component_euler_characteristic_spec(
                m@,
                components@[c as int]@,
                chis@[c as int] as int,
            ));
            assert(forall|cp: int|
                #![trigger components@[cp]@]
                0 <= cp < (c + 1) as int
                    ==> mesh_component_euler_characteristic_spec(
                        m@,
                        components@[cp]@,
                        chis@[cp] as int,
                    )) by {
                assert forall|cp: int|
                    #![trigger components@[cp]@]
                    0 <= cp < (c + 1) as int implies mesh_component_euler_characteristic_spec(
                        m@,
                        components@[cp]@,
                        chis@[cp] as int,
                    ) by {
                    if cp < c as int {
                    } else {
                        assert(cp == c as int);
                        assert(mesh_component_euler_characteristic_spec(
                            m@,
                            components@[cp]@,
                            chis@[cp] as int,
                        ));
                    }
                };
            }
        }
        c += 1;
    }

    proof {
        assert(c == components.len());
        assert(mesh_euler_characteristics_per_component_spec(m@, components@, chis@));
    }
    true
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_half_edge_components_partition(
    m: &Mesh,
    components: &[Vec<usize>],
) -> (out: bool)
    ensures
        out ==> mesh_half_edge_components_partition_spec(m@, components@),
{
    let hcnt = m.half_edges.len();
    let mut global_seen = vec![false; hcnt];
    let mut c: usize = 0;
    while c < components.len()
        invariant
            hcnt == m.half_edges.len(),
            0 <= c <= components.len(),
            global_seen@.len() == hcnt as int,
            forall|cp: int|
                #![trigger components@[cp]@]
                0 <= cp < c as int ==> components@[cp]@.len() > 0,
            forall|cp: int, ip: int|
                #![trigger components@[cp]@[ip]]
                0 <= cp < c as int && 0 <= ip < components@[cp]@.len() as int
                    ==> 0 <= mesh_half_edge_component_entry_spec(components@, cp, ip)
                        && mesh_half_edge_component_entry_spec(components@, cp, ip) < (hcnt as int),
            forall|cp: int, i: int, j: int|
                #![trigger components@[cp]@[i], components@[cp]@[j]]
                0 <= cp < c as int
                    && 0 <= i
                    && i < j
                    && j < components@[cp]@.len() as int
                    ==> components@[cp]@[i] != components@[cp]@[j],
            forall|hp: int|
                0 <= hp < (hcnt as int) && #[trigger] global_seen@[hp]
                    ==> exists|cp: int| {
                        &&& 0 <= cp < c as int
                        &&& mesh_half_edge_component_contains_spec(m@, components@, cp, hp)
                    },
            forall|cp: int, hp: int|
                0 <= cp < c as int && mesh_half_edge_component_contains_spec(m@, components@, cp, hp)
                    ==> global_seen@[hp],
            forall|cp1: int, cp2: int, hp: int|
                0 <= cp1 < c as int
                    && 0 <= cp2 < c as int
                    && mesh_half_edge_component_contains_spec(m@, components@, cp1, hp)
                    && mesh_half_edge_component_contains_spec(m@, components@, cp2, hp)
                    ==> cp1 == cp2,
    {
        let component = vstd::slice::slice_index_get(components, c);
        let clen = component.len();
        if clen == 0 {
            return false;
        }

        let mut local_seen = vec![false; hcnt];
        let ghost global_seen_before = global_seen@;
        proof {
            assert(*component == components@.index(c as int));
            assert(global_seen_before.len() == hcnt as int);
            assert(forall|hp: int|
                0 <= hp < (hcnt as int) && #[trigger] global_seen_before[hp]
                    ==> exists|cp: int| {
                        &&& 0 <= cp < c as int
                        &&& mesh_half_edge_component_contains_spec(m@, components@, cp, hp)
                    });
            assert(forall|cp: int, hp: int|
                0 <= cp < c as int && mesh_half_edge_component_contains_spec(m@, components@, cp, hp)
                    ==> global_seen_before[hp]);
        }

        let mut i: usize = 0;
        while i < clen
            invariant
                hcnt == m.half_edges.len(),
                0 <= c < components.len(),
                *component == components@.index(c as int),
                clen == component.len(),
                component@.len() == clen as int,
                0 <= i <= clen,
                local_seen@.len() == hcnt as int,
                global_seen@.len() == hcnt as int,
                global_seen_before.len() == hcnt as int,
                forall|hp: int| 0 <= hp < (hcnt as int) && #[trigger] global_seen_before[hp] ==> global_seen@[hp],
                forall|hp: int|
                    0 <= hp < (hcnt as int) && #[trigger] global_seen_before[hp]
                        ==> exists|cp: int| {
                            &&& 0 <= cp < c as int
                            &&& mesh_half_edge_component_contains_spec(m@, components@, cp, hp)
                        },
                forall|cp: int, hp: int|
                    0 <= cp < c as int && mesh_half_edge_component_contains_spec(m@, components@, cp, hp)
                        ==> global_seen_before[hp],
                forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < i as int
                        ==> 0 <= component@[ip] as int
                            && (component@[ip] as int) < (hcnt as int),
                forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < i as int ==> #[trigger] local_seen@[component@[ip] as int],
                forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < i as int ==> #[trigger] global_seen@[component@[ip] as int],
                forall|ip1: int, ip2: int|
                    #![trigger component@[ip1], component@[ip2]]
                    0 <= ip1
                        && ip1 < ip2
                        && ip2 < i as int
                        ==> component@[ip1] != component@[ip2],
                forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < i as int ==> !global_seen_before[component@[ip] as int],
                forall|hp: int|
                    0 <= hp < (hcnt as int) && #[trigger] global_seen@[hp]
                        ==> global_seen_before[hp]
                            || exists|ip: int| {
                                &&& 0 <= ip < i as int
                                &&& #[trigger] component@[ip] as int == hp
                            },
                forall|hp: int|
                    0 <= hp < (hcnt as int)
                        && (global_seen_before[hp] || exists|ip: int| {
                            &&& 0 <= ip < i as int
                            &&& #[trigger] component@[ip] as int == hp
                        })
                        ==> global_seen@[hp],
        {
            let h = component[i];
            if h >= hcnt {
                return false;
            }
            if local_seen[h] {
                return false;
            }
            if global_seen[h] {
                return false;
            }

            let ghost local_seen_before_iter = local_seen@;
            let ghost global_seen_before_iter = global_seen@;

            local_seen[h] = true;
            global_seen[h] = true;

            proof {
                assert(component@[i as int] == h);
                assert(0 <= h as int);
                assert((h as int) < (hcnt as int));
                assert(!local_seen_before_iter[h as int]);
                assert(!global_seen_before_iter[h as int]);
                assert(global_seen_before_iter == global_seen_before
                    || global_seen_before_iter.len() == global_seen_before.len());
                assert(forall|hp: int| 0 <= hp < (hcnt as int) && #[trigger] global_seen_before[hp]
                    ==> global_seen_before_iter[hp]) by {
                    assert forall|hp: int|
                        0 <= hp < (hcnt as int) && #[trigger] global_seen_before[hp]
                            implies global_seen_before_iter[hp] by {
                        assert(global_seen_before[hp] ==> global_seen_before_iter[hp]);
                    };
                }
                assert(!global_seen_before[h as int]);
                assert(forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < (i + 1) as int
                        ==> 0 <= component@[ip] as int
                            && (component@[ip] as int) < (hcnt as int)) by {
                    assert forall|ip: int|
                        #![trigger component@[ip]]
                        0 <= ip < (i + 1) as int
                            implies 0 <= component@[ip] as int
                                && (component@[ip] as int) < (hcnt as int) by {
                        if ip < i as int {
                        } else {
                            assert(ip == i as int);
                            assert(component@[ip] as int == h as int);
                        }
                    };
                }
                assert(forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < (i + 1) as int ==> #[trigger] local_seen@[component@[ip] as int]) by {
                    assert forall|ip: int|
                        #![trigger component@[ip]]
                        0 <= ip < (i + 1) as int implies #[trigger] local_seen@[component@[ip] as int] by {
                        if ip < i as int {
                            assert(local_seen_before_iter[component@[ip] as int]);
                            assert(local_seen@[component@[ip] as int]);
                        } else {
                            assert(ip == i as int);
                            assert(component@[ip] as int == h as int);
                            assert(local_seen@[h as int]);
                        }
                    };
                }
                assert(forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < (i + 1) as int ==> #[trigger] global_seen@[component@[ip] as int]) by {
                    assert forall|ip: int|
                        #![trigger component@[ip]]
                        0 <= ip < (i + 1) as int implies #[trigger] global_seen@[component@[ip] as int] by {
                        if ip < i as int {
                            assert(global_seen_before_iter[component@[ip] as int]);
                            assert(global_seen@[component@[ip] as int]);
                        } else {
                            assert(ip == i as int);
                            assert(component@[ip] as int == h as int);
                            assert(global_seen@[h as int]);
                        }
                    };
                }
                assert(forall|ip1: int, ip2: int|
                    #![trigger component@[ip1], component@[ip2]]
                    0 <= ip1
                        && ip1 < ip2
                        && ip2 < (i + 1) as int
                        ==> component@[ip1] != component@[ip2]) by {
                    assert forall|ip1: int, ip2: int|
                        #![trigger component@[ip1], component@[ip2]]
                        0 <= ip1
                            && ip1 < ip2
                            && ip2 < (i + 1) as int
                            implies component@[ip1] != component@[ip2] by {
                        if ip2 < i as int {
                        } else {
                            assert(ip2 == i as int);
                            assert(local_seen_before_iter[component@[ip1] as int]);
                            assert(!local_seen_before_iter[h as int]);
                            assert(component@[ip2] as int == h as int);
                            assert(component@[ip1] as int != component@[ip2] as int);
                        }
                    };
                }
                assert(forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < (i + 1) as int ==> !global_seen_before[component@[ip] as int]) by {
                    assert forall|ip: int|
                        #![trigger component@[ip]]
                        0 <= ip < (i + 1) as int implies !global_seen_before[component@[ip] as int] by {
                        if ip < i as int {
                        } else {
                            assert(ip == i as int);
                            assert(component@[ip] as int == h as int);
                            assert(!global_seen_before[h as int]);
                        }
                    };
                }
                assert(forall|hp: int|
                    0 <= hp < (hcnt as int) && #[trigger] global_seen@[hp]
                        ==> global_seen_before[hp]
                            || exists|ip: int| {
                                &&& 0 <= ip < (i + 1) as int
                                &&& #[trigger] component@[ip] as int == hp
                            }) by {
                    assert forall|hp: int|
                        0 <= hp < (hcnt as int) && #[trigger] global_seen@[hp]
                            implies global_seen_before[hp]
                                || exists|ip: int| {
                                    &&& 0 <= ip < (i + 1) as int
                                    &&& #[trigger] component@[ip] as int == hp
                                } by {
                        if global_seen_before_iter[hp] {
                            if global_seen_before[hp] {
                                assert(global_seen_before[hp]);
                            } else {
                                assert(exists|ip: int| {
                                    &&& 0 <= ip < i as int
                                    &&& #[trigger] component@[ip] as int == hp
                                });
                                assert(exists|ip: int| {
                                    &&& 0 <= ip < (i + 1) as int
                                    &&& #[trigger] component@[ip] as int == hp
                                });
                            }
                        } else {
                            assert(hp == h as int);
                            assert(exists|ip: int| {
                                &&& 0 <= ip < (i + 1) as int
                                &&& #[trigger] component@[ip] as int == hp
                            });
                        }
                    };
                }
                assert(forall|hp: int|
                    0 <= hp < (hcnt as int)
                        && (global_seen_before[hp] || exists|ip: int| {
                            &&& 0 <= ip < (i + 1) as int
                            &&& #[trigger] component@[ip] as int == hp
                        })
                        ==> global_seen@[hp]) by {
                    assert forall|hp: int|
                        0 <= hp < (hcnt as int)
                            && (global_seen_before[hp] || exists|ip: int| {
                                &&& 0 <= ip < (i + 1) as int
                                &&& #[trigger] component@[ip] as int == hp
                            })
                            implies #[trigger] global_seen@[hp] by {
                        if global_seen_before[hp] {
                            assert(global_seen_before_iter[hp]);
                            assert(global_seen@[hp]);
                        } else {
                            assert(exists|ip: int| {
                                &&& 0 <= ip < (i + 1) as int
                                &&& #[trigger] component@[ip] as int == hp
                            });
                            assert(hp == h as int || exists|ip: int| {
                                &&& 0 <= ip < i as int
                                &&& #[trigger] component@[ip] as int == hp
                            });
                            if hp == h as int {
                                assert(global_seen@[h as int]);
                            } else {
                                assert(exists|ip: int| {
                                    &&& 0 <= ip < i as int
                                    &&& #[trigger] component@[ip] as int == hp
                                });
                                assert(global_seen_before_iter[hp]);
                                assert(global_seen@[hp]);
                            }
                        }
                    };
                }
            }

            i += 1;
        }

        proof {
            assert(i == clen);
            assert(clen > 0);
            assert(forall|cp: int|
                #![trigger components@[cp]@]
                0 <= cp < (c + 1) as int ==> components@[cp]@.len() > 0) by {
                assert forall|cp: int|
                    #![trigger components@[cp]@]
                    0 <= cp < (c + 1) as int implies components@[cp]@.len() > 0 by {
                    if cp < c as int {
                    } else {
                        assert(cp == c as int);
                        assert(components@[cp] == *component);
                        assert(components@[cp]@.len() == clen as int);
                    }
                };
            }
            assert(forall|cp: int, ip: int|
                #![trigger components@[cp]@[ip]]
                0 <= cp < (c + 1) as int && 0 <= ip < components@[cp]@.len() as int
                    ==> 0 <= mesh_half_edge_component_entry_spec(components@, cp, ip)
                        && mesh_half_edge_component_entry_spec(components@, cp, ip) < (hcnt as int)) by {
                assert forall|cp: int, ip: int|
                    #![trigger components@[cp]@[ip]]
                    0 <= cp < (c + 1) as int && 0 <= ip < components@[cp]@.len() as int
                        implies 0 <= mesh_half_edge_component_entry_spec(components@, cp, ip)
                            && mesh_half_edge_component_entry_spec(components@, cp, ip) < (hcnt as int) by {
                    if cp < c as int {
                    } else {
                        assert(cp == c as int);
                        assert(components@[cp] == *component);
                        assert(0 <= ip < clen as int);
                    }
                };
            }
            assert(forall|cp: int, i1: int, i2: int|
                #![trigger components@[cp]@[i1], components@[cp]@[i2]]
                0 <= cp < (c + 1) as int
                    && 0 <= i1
                    && i1 < i2
                    && i2 < components@[cp]@.len() as int
                    ==> components@[cp]@[i1] != components@[cp]@[i2]) by {
                assert forall|cp: int, i1: int, i2: int|
                    #![trigger components@[cp]@[i1], components@[cp]@[i2]]
                    0 <= cp < (c + 1) as int
                        && 0 <= i1
                        && i1 < i2
                        && i2 < components@[cp]@.len() as int
                        implies components@[cp]@[i1] != components@[cp]@[i2] by {
                    if cp < c as int {
                    } else {
                        assert(cp == c as int);
                        assert(components@[cp] == *component);
                        assert(0 <= i1);
                        assert(i1 < i2);
                        assert(i2 < i as int);
                    }
                };
            }
            assert(forall|hp: int|
                0 <= hp < (hcnt as int) && #[trigger] global_seen@[hp]
                    ==> exists|cp: int| {
                        &&& 0 <= cp < (c + 1) as int
                        &&& mesh_half_edge_component_contains_spec(m@, components@, cp, hp)
                    }) by {
                assert forall|hp: int|
                    0 <= hp < (hcnt as int) && #[trigger] global_seen@[hp]
                        implies exists|cp: int| {
                            &&& 0 <= cp < (c + 1) as int
                            &&& mesh_half_edge_component_contains_spec(m@, components@, cp, hp)
                        } by {
                    if global_seen_before[hp] {
                        assert(exists|cp: int| {
                            &&& 0 <= cp < c as int
                            &&& mesh_half_edge_component_contains_spec(m@, components@, cp, hp)
                        });
                    } else {
                        assert(exists|ip: int| {
                            &&& 0 <= ip < i as int
                            &&& #[trigger] component@[ip] as int == hp
                        });
                        assert(mesh_half_edge_component_contains_spec(m@, components@, c as int, hp));
                    }
                };
            }
            assert(forall|cp: int, hp: int|
                0 <= cp < (c + 1) as int && mesh_half_edge_component_contains_spec(m@, components@, cp, hp)
                    ==> global_seen@[hp]) by {
                assert forall|cp: int, hp: int|
                    0 <= cp < (c + 1) as int && mesh_half_edge_component_contains_spec(m@, components@, cp, hp)
                        implies global_seen@[hp] by {
                    if cp < c as int {
                        assert(global_seen_before[hp]);
                        assert(global_seen@[hp]);
                    } else {
                        assert(cp == c as int);
                        assert(exists|ip: int|
                            0 <= ip < component@.len() as int && #[trigger] component@[ip] as int == hp);
                        assert(exists|ip: int|
                            0 <= ip < i as int && #[trigger] component@[ip] as int == hp);
                        assert(global_seen@[hp]);
                    }
                };
            }
            assert(forall|cp1: int, cp2: int, hp: int|
                0 <= cp1 < (c + 1) as int
                    && 0 <= cp2 < (c + 1) as int
                    && mesh_half_edge_component_contains_spec(m@, components@, cp1, hp)
                    && mesh_half_edge_component_contains_spec(m@, components@, cp2, hp)
                    ==> cp1 == cp2) by {
                assert forall|cp1: int, cp2: int, hp: int|
                    0 <= cp1 < (c + 1) as int
                        && 0 <= cp2 < (c + 1) as int
                        && mesh_half_edge_component_contains_spec(m@, components@, cp1, hp)
                        && mesh_half_edge_component_contains_spec(m@, components@, cp2, hp)
                        implies cp1 == cp2 by {
                    if cp1 < c as int && cp2 < c as int {
                    } else if cp1 == c as int && cp2 == c as int {
                    } else if cp1 == c as int {
                        assert(cp2 < c as int);
                        assert(global_seen_before[hp]);
                        assert(exists|ip: int|
                            0 <= ip < component@.len() as int && #[trigger] component@[ip] as int == hp);
                        assert(exists|ip: int|
                            0 <= ip < i as int && #[trigger] component@[ip] as int == hp);
                        assert(!global_seen_before[hp]);
                    } else {
                        assert(cp2 == c as int);
                        assert(cp1 < c as int);
                        assert(global_seen_before[hp]);
                        assert(exists|ip: int|
                            0 <= ip < component@.len() as int && #[trigger] component@[ip] as int == hp);
                        assert(exists|ip: int|
                            0 <= ip < i as int && #[trigger] component@[ip] as int == hp);
                        assert(!global_seen_before[hp]);
                    }
                };
            }
        }

        c += 1;
    }

    let mut h: usize = 0;
    while h < hcnt
        invariant
            hcnt == m.half_edges.len(),
            c == components.len(),
            global_seen@.len() == hcnt as int,
            0 <= h <= hcnt,
            forall|cp: int|
                #![trigger components@[cp]@]
                0 <= cp < c as int ==> components@[cp]@.len() > 0,
            forall|cp: int, ip: int|
                #![trigger components@[cp]@[ip]]
                0 <= cp < c as int && 0 <= ip < components@[cp]@.len() as int
                    ==> 0 <= mesh_half_edge_component_entry_spec(components@, cp, ip)
                        && mesh_half_edge_component_entry_spec(components@, cp, ip) < (hcnt as int),
            forall|cp: int, i: int, j: int|
                #![trigger components@[cp]@[i], components@[cp]@[j]]
                0 <= cp < c as int
                    && 0 <= i
                    && i < j
                    && j < components@[cp]@.len() as int
                    ==> components@[cp]@[i] != components@[cp]@[j],
            forall|hp: int|
                0 <= hp < (hcnt as int) && #[trigger] global_seen@[hp]
                    ==> exists|cp: int| {
                        &&& 0 <= cp < c as int
                        &&& mesh_half_edge_component_contains_spec(m@, components@, cp, hp)
                    },
            forall|cp: int, hp: int|
                0 <= cp < c as int && mesh_half_edge_component_contains_spec(m@, components@, cp, hp)
                    ==> global_seen@[hp],
            forall|cp1: int, cp2: int, hp: int|
                0 <= cp1 < c as int
                    && 0 <= cp2 < c as int
                    && mesh_half_edge_component_contains_spec(m@, components@, cp1, hp)
                    && mesh_half_edge_component_contains_spec(m@, components@, cp2, hp)
                    ==> cp1 == cp2,
            forall|hp: int| 0 <= hp < h as int ==> global_seen@[hp],
    {
        if !global_seen[h] {
            return false;
        }

        proof {
            assert(forall|hp: int| 0 <= hp < (h + 1) as int ==> global_seen@[hp]) by {
                assert forall|hp: int|
                    0 <= hp < (h + 1) as int implies #[trigger] global_seen@[hp] by {
                    if hp < h as int {
                    } else {
                        assert(hp == h as int);
                    }
                };
            }
        }

        h += 1;
    }

    proof {
        assert(h == hcnt);
        assert(c == components.len());
        assert(mesh_half_edge_count_spec(m@) == hcnt as int);
        assert(forall|hp: int| 0 <= hp < mesh_half_edge_count_spec(m@) ==> global_seen@[hp]) by {
            assert forall|hp: int|
                0 <= hp < mesh_half_edge_count_spec(m@) implies #[trigger] global_seen@[hp] by {
                assert(mesh_half_edge_count_spec(m@) == h as int);
                assert(0 <= hp < h as int);
            };
        }
        assert(mesh_half_edge_components_cover_all_spec(m@, components@)) by {
            assert forall|hp: int|
                0 <= hp < mesh_half_edge_count_spec(m@)
                    implies mesh_half_edge_has_component_spec(m@, components@, hp) by {
                assert(global_seen@[hp]);
                assert(exists|cp: int| {
                    &&& 0 <= cp < c as int
                    &&& mesh_half_edge_component_contains_spec(m@, components@, cp, hp)
                });
                assert(c == components.len());
            };
        }
        assert(mesh_half_edge_components_partition_spec(m@, components@));
    }
    true
}

#[verifier::exec_allows_no_decreases_clause]
#[verifier::rlimit(300)]
#[allow(dead_code)]
pub fn runtime_check_half_edge_components_neighbor_closed(
    m: &Mesh,
    components: &[Vec<usize>],
) -> (out: bool)
    ensures
        out ==> mesh_half_edge_components_neighbor_closed_spec(m@, components@),
{
    let hcnt = m.half_edges.len();
    let mut c: usize = 0;
    while c < components.len()
        invariant
            hcnt == m.half_edges.len(),
            0 <= c <= components.len(),
            forall|cp: int|
                #![trigger components@[cp]@]
                0 <= cp < c as int
                    ==> mesh_half_edge_component_neighbor_closed_at_spec(m@, components@, cp),
    {
        let component = vstd::slice::slice_index_get(components, c);
        let clen = component.len();
        if clen == 0 {
            return false;
        }

        let mut in_component = vec![false; hcnt];

        let mut i: usize = 0;
        while i < clen
            invariant
                hcnt == m.half_edges.len(),
                0 <= c < components.len(),
                *component == components@.index(c as int),
                clen == component.len(),
                component@.len() == clen as int,
                0 <= i <= clen,
                in_component@.len() == hcnt as int,
                forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < i as int ==> 0 <= component@[ip] as int
                        && (component@[ip] as int) < (hcnt as int),
                forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < i as int ==> #[trigger] in_component@[component@[ip] as int],
                forall|ip1: int, ip2: int|
                    #![trigger component@[ip1], component@[ip2]]
                    0 <= ip1 && ip1 < ip2 && ip2 < i as int ==> component@[ip1] != component@[ip2],
                forall|hp: int|
                    0 <= hp < hcnt as int && #[trigger] in_component@[hp]
                        ==> exists|ip: int| {
                            &&& 0 <= ip < i as int
                            &&& #[trigger] component@[ip] as int == hp
                        },
        {
            let h = component[i];
            if h >= hcnt {
                return false;
            }
            if in_component[h] {
                return false;
            }

            let ghost in_component_before = in_component@;
            in_component[h] = true;

            proof {
                assert(component@[i as int] == h);
                assert(forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < (i + 1) as int ==> 0 <= component@[ip] as int
                        && (component@[ip] as int) < (hcnt as int)) by {
                    assert forall|ip: int|
                        #![trigger component@[ip]]
                        0 <= ip < (i + 1) as int implies 0 <= component@[ip] as int
                            && (component@[ip] as int) < (hcnt as int) by {
                        if ip < i as int {
                        } else {
                            assert(ip == i as int);
                            assert(component@[ip] as int == h as int);
                        }
                    };
                }
                assert(forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < (i + 1) as int ==> #[trigger] in_component@[component@[ip] as int]) by {
                    assert forall|ip: int|
                        #![trigger component@[ip]]
                        0 <= ip < (i + 1) as int implies #[trigger] in_component@[component@[ip] as int] by {
                        if ip < i as int {
                            assert(in_component_before[component@[ip] as int]);
                            assert(in_component@[component@[ip] as int]);
                        } else {
                            assert(ip == i as int);
                            assert(component@[ip] as int == h as int);
                            assert(in_component@[h as int]);
                        }
                    };
                }
                assert(forall|ip1: int, ip2: int|
                    #![trigger component@[ip1], component@[ip2]]
                    0 <= ip1 && ip1 < ip2 && ip2 < (i + 1) as int ==> component@[ip1] != component@[ip2]) by {
                    assert forall|ip1: int, ip2: int|
                        #![trigger component@[ip1], component@[ip2]]
                        0 <= ip1 && ip1 < ip2 && ip2 < (i + 1) as int
                            implies component@[ip1] != component@[ip2] by {
                        if ip2 < i as int {
                        } else {
                            assert(ip2 == i as int);
                            assert(component@[ip2] as int == h as int);
                            assert(in_component_before[component@[ip1] as int]);
                            assert(!in_component_before[h as int]);
                            assert(component@[ip1] as int != component@[ip2] as int);
                        }
                    };
                }
                assert(forall|hp: int|
                    0 <= hp < hcnt as int && #[trigger] in_component@[hp]
                        ==> exists|ip: int| {
                            &&& 0 <= ip < (i + 1) as int
                            &&& #[trigger] component@[ip] as int == hp
                        }) by {
                    assert forall|hp: int|
                        0 <= hp < hcnt as int && #[trigger] in_component@[hp]
                            implies exists|ip: int| {
                                &&& 0 <= ip < (i + 1) as int
                                &&& #[trigger] component@[ip] as int == hp
                            } by {
                        if hp == h as int {
                            assert(exists|ip: int| {
                                &&& 0 <= ip < (i + 1) as int
                                &&& #[trigger] component@[ip] as int == hp
                            });
                        } else {
                            assert(in_component_before[hp]);
                            assert(exists|ip: int| {
                                &&& 0 <= ip < i as int
                                &&& #[trigger] component@[ip] as int == hp
                            });
                            let ip = choose|ip: int| {
                                &&& 0 <= ip < i as int
                                &&& #[trigger] component@[ip] as int == hp
                            };
                            assert(0 <= ip < (i + 1) as int);
                            assert(component@[ip] as int == hp);
                            assert(exists|ip2: int| {
                                &&& 0 <= ip2 < (i + 1) as int
                                &&& #[trigger] component@[ip2] as int == hp
                            });
                        }
                    };
                }
            }

            i += 1;
        }

        let mut k: usize = 0;
        while k < clen
            invariant
                hcnt == m.half_edges.len(),
                0 <= c < components.len(),
                *component == components@.index(c as int),
                clen == component.len(),
                component@.len() == clen as int,
                0 <= k <= clen,
                in_component@.len() == hcnt as int,
                forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < clen as int ==> 0 <= component@[ip] as int
                        && (component@[ip] as int) < (hcnt as int),
                forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < clen as int ==> #[trigger] in_component@[component@[ip] as int],
                forall|ip1: int, ip2: int|
                    #![trigger component@[ip1], component@[ip2]]
                    0 <= ip1 && ip1 < ip2 && ip2 < clen as int ==> component@[ip1] != component@[ip2],
                forall|hp: int|
                    0 <= hp < hcnt as int && #[trigger] in_component@[hp]
                        ==> exists|ip: int| {
                            &&& 0 <= ip < clen as int
                            &&& #[trigger] component@[ip] as int == hp
                        },
                forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < k as int ==> {
                        let hp = component@[ip] as int;
                        let t = m@.half_edges[hp].twin;
                        let n = m@.half_edges[hp].next;
                        let p = m@.half_edges[hp].prev;
                        &&& 0 <= t < hcnt as int
                        &&& 0 <= n < hcnt as int
                        &&& 0 <= p < hcnt as int
                        &&& in_component@[t]
                        &&& in_component@[n]
                        &&& in_component@[p]
                    },
        {
            let h = component[k];
            let he = &m.half_edges[h];
            let t = he.twin;
            let n = he.next;
            let p = he.prev;

            if t >= hcnt || n >= hcnt || p >= hcnt {
                return false;
            }
            if !in_component[t] || !in_component[n] || !in_component[p] {
                return false;
            }

            proof {
                assert(component@[k as int] as int == h as int);
                assert(m@.half_edges[h as int].twin == t as int);
                assert(m@.half_edges[h as int].next == n as int);
                assert(m@.half_edges[h as int].prev == p as int);
                assert(in_component@[t as int]);
                assert(in_component@[n as int]);
                assert(in_component@[p as int]);
                assert(forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < (k + 1) as int ==> {
                        let hp = component@[ip] as int;
                        let tp = m@.half_edges[hp].twin;
                        let np = m@.half_edges[hp].next;
                        let pp = m@.half_edges[hp].prev;
                        &&& 0 <= tp < hcnt as int
                        &&& 0 <= np < hcnt as int
                        &&& 0 <= pp < hcnt as int
                        &&& in_component@[tp]
                        &&& in_component@[np]
                        &&& in_component@[pp]
                    }) by {
                    assert forall|ip: int|
                        #![trigger component@[ip]]
                        0 <= ip < (k + 1) as int implies {
                            let hp = component@[ip] as int;
                            let tp = m@.half_edges[hp].twin;
                            let np = m@.half_edges[hp].next;
                            let pp = m@.half_edges[hp].prev;
                            &&& 0 <= tp < hcnt as int
                            &&& 0 <= np < hcnt as int
                            &&& 0 <= pp < hcnt as int
                            &&& in_component@[tp]
                            &&& in_component@[np]
                            &&& in_component@[pp]
                        } by {
                        if ip < k as int {
                        } else {
                            assert(ip == k as int);
                            assert(component@[ip] as int == h as int);
                            assert(m@.half_edges[component@[ip] as int].twin == t as int);
                            assert(m@.half_edges[component@[ip] as int].next == n as int);
                            assert(m@.half_edges[component@[ip] as int].prev == p as int);
                        }
                    };
                }
            }

            k += 1;
        }

        proof {
            assert(k == clen);
            assert(mesh_half_edge_component_neighbor_closed_at_spec(m@, components@, c as int)) by {
                assert forall|h: int|
                    #![trigger mesh_half_edge_component_contains_spec(m@, components@, c as int, h)]
                    mesh_half_edge_component_contains_spec(m@, components@, c as int, h) implies {
                        let t = m@.half_edges[h].twin;
                        let n = m@.half_edges[h].next;
                        let p = m@.half_edges[h].prev;
                        &&& 0 <= t < mesh_half_edge_count_spec(m@)
                        &&& 0 <= n < mesh_half_edge_count_spec(m@)
                        &&& 0 <= p < mesh_half_edge_count_spec(m@)
                        &&& mesh_half_edge_component_contains_spec(m@, components@, c as int, t)
                        &&& mesh_half_edge_component_contains_spec(m@, components@, c as int, n)
                        &&& mesh_half_edge_component_contains_spec(m@, components@, c as int, p)
                    } by {
                    assert(exists|ip: int|
                        #![trigger mesh_half_edge_component_entry_spec(components@, c as int, ip)]
                        0 <= ip < components@[c as int]@.len() as int
                            && mesh_half_edge_component_entry_spec(components@, c as int, ip) == h);
                    let ip = choose|ip: int| {
                        &&& 0 <= ip < components@[c as int]@.len() as int
                        &&& mesh_half_edge_component_entry_spec(components@, c as int, ip) == h
                    };
                    assert(components@[c as int] == *component);
                    assert(components@[c as int]@.len() == clen as int);
                    assert(0 <= ip < clen as int);
                    assert(mesh_half_edge_component_entry_spec(components@, c as int, ip) == component@[ip] as int);
                    assert(component@[ip] as int == h);
                    assert(0 <= ip < k as int);

                    let t = m@.half_edges[h].twin;
                    let n = m@.half_edges[h].next;
                    let p = m@.half_edges[h].prev;
                    assert(0 <= t < hcnt as int);
                    assert(0 <= n < hcnt as int);
                    assert(0 <= p < hcnt as int);
                    assert(in_component@[t]);
                    assert(in_component@[n]);
                    assert(in_component@[p]);

                    assert(exists|jt: int| {
                        &&& 0 <= jt < clen as int
                        &&& #[trigger] component@[jt] as int == t
                    });
                    let jt = choose|jt: int| {
                        &&& 0 <= jt < clen as int
                        &&& #[trigger] component@[jt] as int == t
                    };
                    assert(0 <= jt < components@[c as int]@.len() as int);
                    assert(mesh_half_edge_component_entry_spec(components@, c as int, jt) == t);
                    assert(mesh_half_edge_component_contains_spec(m@, components@, c as int, t));

                    assert(exists|jn: int| {
                        &&& 0 <= jn < clen as int
                        &&& #[trigger] component@[jn] as int == n
                    });
                    let jn = choose|jn: int| {
                        &&& 0 <= jn < clen as int
                        &&& #[trigger] component@[jn] as int == n
                    };
                    assert(0 <= jn < components@[c as int]@.len() as int);
                    assert(mesh_half_edge_component_entry_spec(components@, c as int, jn) == n);
                    assert(mesh_half_edge_component_contains_spec(m@, components@, c as int, n));

                    assert(exists|jp: int| {
                        &&& 0 <= jp < clen as int
                        &&& #[trigger] component@[jp] as int == p
                    });
                    let jp = choose|jp: int| {
                        &&& 0 <= jp < clen as int
                        &&& #[trigger] component@[jp] as int == p
                    };
                    assert(0 <= jp < components@[c as int]@.len() as int);
                    assert(mesh_half_edge_component_entry_spec(components@, c as int, jp) == p);
                    assert(mesh_half_edge_component_contains_spec(m@, components@, c as int, p));
                };
            }

            assert(forall|cp: int|
                #![trigger components@[cp]@]
                0 <= cp < (c + 1) as int
                    ==> mesh_half_edge_component_neighbor_closed_at_spec(m@, components@, cp)) by {
                assert forall|cp: int|
                    #![trigger components@[cp]@]
                    0 <= cp < (c + 1) as int
                        implies mesh_half_edge_component_neighbor_closed_at_spec(m@, components@, cp) by {
                    if cp < c as int {
                    } else {
                        assert(cp == c as int);
                        assert(mesh_half_edge_component_neighbor_closed_at_spec(m@, components@, c as int));
                    }
                };
            }
        }

        c += 1;
    }

    proof {
        assert(c == components.len());
        assert(mesh_half_edge_components_neighbor_closed_spec(m@, components@)) by {
            assert forall|cp: int|
                #![trigger components@[cp]@]
                0 <= cp < components@.len() as int
                    implies mesh_half_edge_component_neighbor_closed_at_spec(m@, components@, cp) by {
                assert(components@.len() as int == c as int);
                assert(0 <= cp < c as int);
            };
        }
    }
    true
}

#[allow(dead_code)]
pub fn half_edge_components_constructive(
    m: &Mesh,
) -> (out: Option<Vec<Vec<usize>>>)
    ensures
        match out {
            Option::Some(components) => mesh_half_edge_components_partition_neighbor_closed_spec(m@, components@),
            Option::None => true,
        },
{
    let components = ex_mesh_half_edge_components(m);
    let partition_ok = runtime_check_half_edge_components_partition(m, &components);
    if !partition_ok {
        return Option::None;
    }
    let neighbor_closed_ok = runtime_check_half_edge_components_neighbor_closed(m, &components);
    if neighbor_closed_ok {
        proof {
            assert(mesh_half_edge_components_partition_spec(m@, components@));
            assert(mesh_half_edge_components_neighbor_closed_spec(m@, components@));
            assert(mesh_half_edge_components_partition_neighbor_closed_spec(m@, components@));
        }
        Option::Some(components)
    } else {
        Option::None
    }
}

#[allow(dead_code)]
pub fn component_count_constructive(
    m: &Mesh,
) -> (out: Option<usize>)
    ensures
        match out {
            Option::Some(count) => mesh_component_count_partition_witness_spec(m@, count as int),
            Option::None => true,
        },
{
    let components = ex_mesh_half_edge_components(m);
    let components_ok = runtime_check_half_edge_components_partition(m, &components);
    if !components_ok {
        return Option::None;
    }
    let neighbor_closed_ok = runtime_check_half_edge_components_neighbor_closed(m, &components);
    if !neighbor_closed_ok {
        return Option::None;
    }

    let count = ex_mesh_component_count(m);
    if count != components.len() {
        return Option::None;
    }

    proof {
        assert(mesh_half_edge_components_partition_spec(m@, components@));
        assert(mesh_half_edge_components_neighbor_closed_spec(m@, components@));
        assert(mesh_half_edge_components_partition_neighbor_closed_spec(m@, components@));
        assert(count as int == components@.len() as int);
        assert(mesh_component_count_partition_witness_spec(m@, count as int));
    }

    Option::Some(count)
}

#[allow(dead_code)]
pub fn euler_characteristics_per_component_constructive(
    m: &Mesh,
) -> (out: Option<Vec<isize>>)
    ensures
        match out {
            Option::Some(chis) => mesh_euler_characteristics_partition_witness_spec(m@, chis@),
            Option::None => true,
        },
{
    let components = ex_mesh_half_edge_components(m);
    let partition_ok = runtime_check_half_edge_components_partition(m, &components);
    if !partition_ok {
        return Option::None;
    }

    let neighbor_closed_ok = runtime_check_half_edge_components_neighbor_closed(m, &components);
    if !neighbor_closed_ok {
        return Option::None;
    }

    let chis = ex_mesh_euler_characteristics_per_component(m);
    let chis_ok = runtime_check_euler_characteristics_per_component(m, &components, &chis);
    if !chis_ok {
        return Option::None;
    }

    proof {
        assert(mesh_half_edge_components_partition_spec(m@, components@));
        assert(mesh_half_edge_components_neighbor_closed_spec(m@, components@));
        assert(mesh_half_edge_components_partition_neighbor_closed_spec(m@, components@));
        assert(mesh_euler_characteristics_per_component_spec(m@, components@, chis@));
        assert(mesh_euler_characteristics_partition_witness_spec(m@, chis@));
    }

    Option::Some(chis)
}

} // verus!
