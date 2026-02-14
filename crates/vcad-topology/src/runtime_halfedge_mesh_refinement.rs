#![cfg(feature = "verus-proofs")]

use crate::halfedge_mesh::Mesh;
use vstd::prelude::*;
use vstd::view::View;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExMesh(Mesh);

#[derive(Structural, Copy, Clone, PartialEq, Eq)]
pub struct HalfEdgeModel {
    pub twin: int,
    pub next: int,
    pub prev: int,
    pub vertex: int,
    pub edge: int,
    pub face: int,
}

pub struct MeshModel {
    pub vertex_half_edges: Seq<int>,
    pub edge_half_edges: Seq<int>,
    pub face_half_edges: Seq<int>,
    pub half_edges: Seq<HalfEdgeModel>,
}

impl View for Mesh {
    type V = MeshModel;

    uninterp spec fn view(&self) -> MeshModel;
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

pub open spec fn mesh_edge_exactly_two_half_edges_spec(m: MeshModel) -> bool {
    forall|e: int| 0 <= e < mesh_edge_count_spec(m) ==> {
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

pub open spec fn input_face_to_vertex_spec(face_cycles: Seq<Seq<int>>, f: int, i: int) -> int {
    let n = face_cycles[f].len() as int;
    if n > 0 {
        face_cycles[f][(i + 1) % n]
    } else {
        0
    }
}

pub open spec fn input_face_prev_local_index_spec(face_cycles: Seq<Seq<int>>, f: int, i: int) -> int {
    let n = face_cycles[f].len() as int;
    if n > 0 {
        (i + n - 1) % n
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
            let next_i = (i + 1) % n;
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

} // verus!
