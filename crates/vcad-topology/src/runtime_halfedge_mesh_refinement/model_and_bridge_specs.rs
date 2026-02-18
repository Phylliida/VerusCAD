verus! {
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

pub(crate) proof fn lemma_usize_loop_exit_eq(idx: usize, bound: usize)
    requires
        idx <= bound,
        !(idx < bound),
    ensures
        idx == bound,
{
    if bound == 0 {
        assert(idx == 0);
    } else {
        assert(!(idx <= bound - 1)) by {
            if idx <= bound - 1 {
                assert(idx < bound);
                assert(false);
            }
        };
        #[cfg(verus_keep_ghost)]
        Scalar::lemma_nat_le_and_not_le_prev_implies_eq(idx as nat, bound as nat);
        #[cfg(verus_keep_ghost)]
        assert(idx == bound);
        #[cfg(not(verus_keep_ghost))]
        {
            // Rust test-mode fallback: this module is typechecked without ghost
            // proof dependencies such as `vcad_math::scalar::Scalar`.
        }
    }
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

pub open spec fn mesh_prev_next_inverse_at_spec(m: MeshModel, h: int) -> bool {
    &&& 0 <= m.half_edges[h].next < mesh_half_edge_count_spec(m)
    &&& 0 <= m.half_edges[h].prev < mesh_half_edge_count_spec(m)
    &&& m.half_edges[m.half_edges[h].next].prev == h
    &&& m.half_edges[m.half_edges[h].prev].next == h
}

pub open spec fn mesh_prev_next_inverse_spec(m: MeshModel) -> bool {
    forall|h: int|
        0 <= h < mesh_half_edge_count_spec(m)
            ==> #[trigger] mesh_prev_next_inverse_at_spec(m, h)
}

pub open spec fn mesh_no_degenerate_edges_at_spec(m: MeshModel, h: int) -> bool {
    &&& 0 <= m.half_edges[h].twin < mesh_half_edge_count_spec(m)
    &&& 0 <= m.half_edges[h].next < mesh_half_edge_count_spec(m)
    &&& m.half_edges[h].vertex != m.half_edges[m.half_edges[h].twin].vertex
    &&& m.half_edges[h].vertex != m.half_edges[m.half_edges[h].next].vertex
}

pub open spec fn mesh_no_degenerate_edges_spec(m: MeshModel) -> bool {
    forall|h: int|
        0 <= h < mesh_half_edge_count_spec(m)
            ==> #[trigger] mesh_no_degenerate_edges_at_spec(m, h)
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

pub open spec fn mesh_face_next_cycles_witness_spec(
    m: MeshModel,
    face_cycle_lens: Seq<usize>,
) -> bool {
    &&& face_cycle_lens.len() == mesh_face_count_spec(m)
    &&& forall|f: int|
        #![trigger face_cycle_lens[f]]
        0 <= f < mesh_face_count_spec(m)
            ==> mesh_face_cycle_witness_spec(m, f, face_cycle_lens[f] as int)
}

pub open spec fn mesh_face_next_cycles_spec(m: MeshModel) -> bool {
    exists|face_cycle_lens: Seq<usize>| mesh_face_next_cycles_witness_spec(m, face_cycle_lens)
}

pub open spec fn kernel_mesh_matches_mesh_model_spec(km: &kernels::KernelMesh, m: MeshModel) -> bool {
    &&& km.vertex_half_edges@.len() == mesh_vertex_count_spec(m)
    &&& km.edge_half_edges@.len() == mesh_edge_count_spec(m)
    &&& km.face_half_edges@.len() == mesh_face_count_spec(m)
    &&& km.half_edges@.len() == mesh_half_edge_count_spec(m)
    &&& forall|v: int|
        0 <= v < mesh_vertex_count_spec(m)
            ==> (#[trigger] km.vertex_half_edges@[v] as int) == m.vertex_half_edges[v]
    &&& forall|e: int|
        0 <= e < mesh_edge_count_spec(m)
            ==> (#[trigger] km.edge_half_edges@[e] as int) == m.edge_half_edges[e]
    &&& forall|f: int|
        0 <= f < mesh_face_count_spec(m)
            ==> (#[trigger] km.face_half_edges@[f] as int) == m.face_half_edges[f]
    &&& forall|h: int| 0 <= h < mesh_half_edge_count_spec(m) ==> {
        let khe = #[trigger] km.half_edges@[h];
        let mhe = m.half_edges[h];
        &&& (khe.twin as int) == mhe.twin
        &&& (khe.next as int) == mhe.next
        &&& (khe.prev as int) == mhe.prev
        &&& (khe.vertex as int) == mhe.vertex
        &&& (khe.edge as int) == mhe.edge
        &&& (khe.face as int) == mhe.face
    }
}

pub open spec fn mesh_face_representative_cycle_kernel_bridge_witness_spec(
    m: MeshModel,
    f: int,
    k: int,
) -> bool {
    let hcnt = mesh_half_edge_count_spec(m);
    let start = m.face_half_edges[f];
    &&& 3 <= k <= hcnt
    &&& mesh_next_iter_spec(m, start, k as nat) == start
    &&& forall|i: int|
        0 <= i < k ==> #[trigger] m.half_edges[mesh_next_iter_spec(m, start, i as nat)].face == f
    &&& forall|i: int, j: int|
        #![trigger mesh_next_iter_spec(m, start, i as nat), mesh_next_iter_spec(m, start, j as nat)]
        0 <= i < j < k
            ==> mesh_next_iter_spec(m, start, i as nat) != mesh_next_iter_spec(
                m,
                start,
                j as nat,
            )
}

pub open spec fn mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_spec(
    m: MeshModel,
) -> bool {
    exists|face_cycle_lens: Seq<usize>, covered: Seq<bool>| {
        mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_witness_spec(
            m,
            face_cycle_lens,
            covered,
        )
    }
}

pub open spec fn mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_witness_spec(
    m: MeshModel,
    face_cycle_lens: Seq<usize>,
    covered: Seq<bool>,
) -> bool {
    &&& face_cycle_lens.len() == mesh_face_count_spec(m)
    &&& covered.len() == mesh_half_edge_count_spec(m)
    &&& forall|f: int|
        #![trigger face_cycle_lens[f]]
        0 <= f < mesh_face_count_spec(m)
            ==> mesh_face_representative_cycle_kernel_bridge_witness_spec(
                m,
                f,
                face_cycle_lens[f] as int,
            )
    &&& forall|h: int|
        #![trigger h + 0]
        0 <= h < mesh_half_edge_count_spec(m) && #[trigger] covered[h]
            ==> exists|f: int, i: int| {
                &&& 0 <= f < mesh_face_count_spec(m)
                &&& 0 <= i < face_cycle_lens[f] as int
                &&& #[trigger] mesh_next_iter_spec(m, m.face_half_edges[f], i as nat) == h
            }
    &&& forall|h: int| 0 <= h < mesh_half_edge_count_spec(m) ==> #[trigger] covered[h]
    &&& forall|f1: int, i1: int, f2: int, i2: int|
        #![trigger mesh_next_iter_spec(m, m.face_half_edges[f1], i1 as nat), mesh_next_iter_spec(m, m.face_half_edges[f2], i2 as nat)]
        0 <= f1 < mesh_face_count_spec(m)
            && 0 <= f2 < mesh_face_count_spec(m)
            && 0 <= i1 < face_cycle_lens[f1] as int
            && 0 <= i2 < face_cycle_lens[f2] as int
            && mesh_next_iter_spec(m, m.face_half_edges[f1], i1 as nat)
                == mesh_next_iter_spec(m, m.face_half_edges[f2], i2 as nat)
            ==> f1 == f2
}

pub open spec fn mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_total_spec(
    m: MeshModel,
) -> bool {
    mesh_index_bounds_spec(m) && mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_spec(m)
}

pub open spec fn mesh_vertex_representative_cycle_kernel_bridge_witness_spec(
    m: MeshModel,
    v: int,
    k: int,
) -> bool {
    let start = m.vertex_half_edges[v];
    &&& 1 <= k <= mesh_half_edge_count_spec(m)
    &&& mesh_vertex_ring_iter_spec(m, start, k as nat) == start
    &&& forall|i: int|
        0 <= i < k ==> #[trigger] m.half_edges[mesh_vertex_ring_iter_spec(m, start, i as nat)].vertex == v
}

pub open spec fn mesh_vertex_representative_cycles_kernel_bridge_spec(m: MeshModel) -> bool {
    exists|vertex_cycle_lens: Seq<usize>| {
        &&& vertex_cycle_lens.len() == mesh_vertex_count_spec(m)
        &&& forall|v: int|
            #![trigger vertex_cycle_lens[v]]
            0 <= v < mesh_vertex_count_spec(m)
                ==> mesh_vertex_representative_cycle_kernel_bridge_witness_spec(
                    m,
                    v,
                    vertex_cycle_lens[v] as int,
                )
    }
}

pub open spec fn mesh_vertex_representative_cycles_kernel_bridge_total_spec(m: MeshModel) -> bool {
    mesh_index_bounds_spec(m) && mesh_vertex_representative_cycles_kernel_bridge_spec(m)
}
} // verus!
