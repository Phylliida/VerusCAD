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

pub open spec fn mesh_twin_faces_distinct_at_spec(m: MeshModel, h: int) -> bool {
    let hcnt = mesh_half_edge_count_spec(m);
    let t = m.half_edges[h].twin;
    &&& 0 <= h < hcnt
    &&& 0 <= t < hcnt
    &&& m.half_edges[h].face != m.half_edges[t].face
}

pub open spec fn mesh_twin_faces_distinct_spec(m: MeshModel) -> bool {
    forall|h: int|
        0 <= h < mesh_half_edge_count_spec(m)
            ==> #[trigger] mesh_twin_faces_distinct_at_spec(m, h)
}

pub open spec fn mesh_shared_edge_local_orientation_consistency_spec(m: MeshModel) -> bool {
    &&& mesh_twin_faces_distinct_spec(m)
    &&& from_face_cycles_twin_endpoint_correspondence_spec(m)
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

pub open spec fn mesh_half_edge_belongs_to_face_spec(m: MeshModel, f: int, h: int) -> bool {
    &&& 0 <= f < mesh_face_count_spec(m)
    &&& 0 <= h < mesh_half_edge_count_spec(m)
    &&& m.half_edges[h].face == f
}

pub open spec fn mesh_faces_share_vertex_spec(m: MeshModel, f1: int, f2: int) -> bool {
    exists|h1: int, h2: int| {
        &&& mesh_half_edge_belongs_to_face_spec(m, f1, h1)
        &&& mesh_half_edge_belongs_to_face_spec(m, f2, h2)
        &&& #[trigger] m.half_edges[h1].vertex == #[trigger] m.half_edges[h2].vertex
    }
}

pub open spec fn mesh_faces_share_edge_spec(m: MeshModel, f1: int, f2: int) -> bool {
    exists|h1: int, h2: int| {
        &&& mesh_half_edge_belongs_to_face_spec(m, f1, h1)
        &&& mesh_half_edge_belongs_to_face_spec(m, f2, h2)
        &&& #[trigger] m.half_edges[h1].edge == #[trigger] m.half_edges[h2].edge
    }
}

pub open spec fn mesh_faces_disjoint_boundary_spec(m: MeshModel, f1: int, f2: int) -> bool {
    &&& 0 <= f1 < mesh_face_count_spec(m)
    &&& 0 <= f2 < mesh_face_count_spec(m)
    &&& !mesh_faces_share_vertex_spec(m, f1, f2)
    &&& !mesh_faces_share_edge_spec(m, f1, f2)
}

pub open spec fn mesh_faces_share_vertex_index_spec(
    m: MeshModel,
    f1: int,
    f2: int,
    v: int,
) -> bool {
    &&& 0 <= v < mesh_vertex_count_spec(m)
    &&& exists|h1: int, h2: int| {
        &&& mesh_half_edge_belongs_to_face_spec(m, f1, h1)
        &&& mesh_half_edge_belongs_to_face_spec(m, f2, h2)
        &&& #[trigger] m.half_edges[h1].vertex == v
        &&& #[trigger] m.half_edges[h2].vertex == v
    }
}

pub open spec fn mesh_faces_share_edge_index_spec(
    m: MeshModel,
    f1: int,
    f2: int,
    e: int,
) -> bool {
    &&& 0 <= e < mesh_edge_count_spec(m)
    &&& exists|h1: int, h2: int| {
        &&& mesh_half_edge_belongs_to_face_spec(m, f1, h1)
        &&& mesh_half_edge_belongs_to_face_spec(m, f2, h2)
        &&& #[trigger] m.half_edges[h1].edge == e
        &&& #[trigger] m.half_edges[h2].edge == e
    }
}

pub open spec fn mesh_faces_share_exactly_one_vertex_spec(m: MeshModel, f1: int, f2: int) -> bool {
    &&& 0 <= f1 < mesh_face_count_spec(m)
    &&& 0 <= f2 < mesh_face_count_spec(m)
    &&& exists|v: int| {
        &&& mesh_faces_share_vertex_index_spec(m, f1, f2, v)
        &&& forall|vp: int| #[trigger] mesh_faces_share_vertex_index_spec(m, f1, f2, vp) ==> vp == v
    }
}

pub open spec fn mesh_faces_share_exactly_two_vertices_spec(
    m: MeshModel,
    f1: int,
    f2: int,
) -> bool {
    &&& 0 <= f1 < mesh_face_count_spec(m)
    &&& 0 <= f2 < mesh_face_count_spec(m)
    &&& exists|v0: int, v1: int| {
        &&& v0 != v1
        &&& mesh_faces_share_vertex_index_spec(m, f1, f2, v0)
        &&& mesh_faces_share_vertex_index_spec(m, f1, f2, v1)
        &&& forall|vp: int| #[trigger] mesh_faces_share_vertex_index_spec(
            m,
            f1,
            f2,
            vp,
        ) ==> (vp == v0 || vp == v1)
    }
}

pub open spec fn mesh_faces_share_exactly_one_edge_spec(m: MeshModel, f1: int, f2: int) -> bool {
    &&& 0 <= f1 < mesh_face_count_spec(m)
    &&& 0 <= f2 < mesh_face_count_spec(m)
    &&& exists|e: int| {
        &&& mesh_faces_share_edge_index_spec(m, f1, f2, e)
        &&& forall|ep: int| #[trigger] mesh_faces_share_edge_index_spec(m, f1, f2, ep) ==> ep == e
    }
}

pub open spec fn mesh_faces_allowed_contact_relation_spec(m: MeshModel, f1: int, f2: int) -> bool {
    &&& 0 <= f1 < mesh_face_count_spec(m)
    &&& 0 <= f2 < mesh_face_count_spec(m)
    &&& f1 != f2
    &&& (
        mesh_faces_disjoint_boundary_spec(m, f1, f2)
            || (mesh_faces_share_exactly_one_vertex_spec(m, f1, f2) && !mesh_faces_share_edge_spec(
                m,
                f1,
                f2,
            ))
            || (mesh_faces_share_exactly_one_edge_spec(m, f1, f2)
                && mesh_faces_share_exactly_two_vertices_spec(m, f1, f2))
    )
}

pub open spec fn mesh_faces_share_zero_or_one_vertices_spec(m: MeshModel, f1: int, f2: int) -> bool {
    &&& 0 <= f1 < mesh_face_count_spec(m)
    &&& 0 <= f2 < mesh_face_count_spec(m)
    &&& (
        !mesh_faces_share_vertex_spec(m, f1, f2)
            || mesh_faces_share_exactly_one_vertex_spec(m, f1, f2)
    )
}

pub open spec fn mesh_faces_allowed_contact_runtime_branch_classifier_spec(
    m: MeshModel,
    f1: int,
    f2: int,
) -> bool {
    &&& 0 <= f1 < mesh_face_count_spec(m)
    &&& 0 <= f2 < mesh_face_count_spec(m)
    &&& f1 != f2
    &&& (
        (!mesh_faces_share_edge_spec(m, f1, f2)
            && mesh_faces_share_zero_or_one_vertices_spec(m, f1, f2))
            || (mesh_faces_share_exactly_one_edge_spec(m, f1, f2)
                && mesh_faces_share_exactly_two_vertices_spec(m, f1, f2))
    )
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_faces_share_exactly_one_vertex_implies_share_vertex(
    m: MeshModel,
    f1: int,
    f2: int,
)
    requires
        mesh_faces_share_exactly_one_vertex_spec(m, f1, f2),
    ensures
        mesh_faces_share_vertex_spec(m, f1, f2),
{
    let v = choose|v: int| {
        &&& mesh_faces_share_vertex_index_spec(m, f1, f2, v)
        &&& forall|vp: int| #[trigger] mesh_faces_share_vertex_index_spec(m, f1, f2, vp) ==> vp == v
    };
    assert(mesh_faces_share_vertex_index_spec(m, f1, f2, v));
    assert(mesh_faces_share_vertex_spec(m, f1, f2));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_faces_share_exactly_one_edge_implies_share_edge(
    m: MeshModel,
    f1: int,
    f2: int,
)
    requires
        mesh_faces_share_exactly_one_edge_spec(m, f1, f2),
    ensures
        mesh_faces_share_edge_spec(m, f1, f2),
{
    let e = choose|e: int| {
        &&& mesh_faces_share_edge_index_spec(m, f1, f2, e)
        &&& forall|ep: int| #[trigger] mesh_faces_share_edge_index_spec(m, f1, f2, ep) ==> ep == e
    };
    assert(mesh_faces_share_edge_index_spec(m, f1, f2, e));
    assert(mesh_faces_share_edge_spec(m, f1, f2));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_faces_allowed_contact_relation_iff_runtime_branch_classifier(
    m: MeshModel,
    f1: int,
    f2: int,
)
    ensures
        mesh_faces_allowed_contact_relation_spec(m, f1, f2)
            == mesh_faces_allowed_contact_runtime_branch_classifier_spec(m, f1, f2),
{
    assert(
        mesh_faces_allowed_contact_relation_spec(m, f1, f2)
            ==> mesh_faces_allowed_contact_runtime_branch_classifier_spec(m, f1, f2)
    ) by {
        if mesh_faces_allowed_contact_relation_spec(m, f1, f2) {
            if mesh_faces_disjoint_boundary_spec(m, f1, f2) {
                assert(!mesh_faces_share_edge_spec(m, f1, f2));
                assert(mesh_faces_share_zero_or_one_vertices_spec(m, f1, f2));
            } else if
                mesh_faces_share_exactly_one_vertex_spec(m, f1, f2)
                    && !mesh_faces_share_edge_spec(m, f1, f2)
            {
                assert(mesh_faces_share_zero_or_one_vertices_spec(m, f1, f2));
            } else {
                assert(mesh_faces_share_exactly_one_edge_spec(m, f1, f2));
                assert(mesh_faces_share_exactly_two_vertices_spec(m, f1, f2));
            }
            assert(mesh_faces_allowed_contact_runtime_branch_classifier_spec(m, f1, f2));
        }
    };

    assert(
        mesh_faces_allowed_contact_runtime_branch_classifier_spec(m, f1, f2)
            ==> mesh_faces_allowed_contact_relation_spec(m, f1, f2)
    ) by {
        if mesh_faces_allowed_contact_runtime_branch_classifier_spec(m, f1, f2) {
            if mesh_faces_share_exactly_one_edge_spec(m, f1, f2)
                && mesh_faces_share_exactly_two_vertices_spec(m, f1, f2)
            {
                assert(mesh_faces_allowed_contact_relation_spec(m, f1, f2));
            } else {
                assert(!mesh_faces_share_edge_spec(m, f1, f2));
                assert(mesh_faces_share_zero_or_one_vertices_spec(m, f1, f2));
                if !mesh_faces_share_vertex_spec(m, f1, f2) {
                    assert(mesh_faces_disjoint_boundary_spec(m, f1, f2));
                } else {
                    assert(mesh_faces_share_exactly_one_vertex_spec(m, f1, f2)) by {
                        assert(
                            !mesh_faces_share_vertex_spec(m, f1, f2)
                                || mesh_faces_share_exactly_one_vertex_spec(m, f1, f2)
                        );
                    };
                }
                assert(mesh_faces_allowed_contact_relation_spec(m, f1, f2));
            }
        }
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_faces_shared_boundary_runtime_branch_classifier_not_non_adjacent_forbidden_relation(
    m: MeshModel,
    f1: int,
    f2: int,
    geometric_intersection_exists: bool,
)
    requires
        mesh_faces_allowed_contact_runtime_branch_classifier_spec(m, f1, f2),
        mesh_faces_share_vertex_spec(m, f1, f2) || mesh_faces_share_edge_spec(m, f1, f2),
    ensures
        mesh_faces_allowed_contact_relation_spec(m, f1, f2),
        !mesh_non_adjacent_face_pair_forbidden_intersection_relation_spec(
            m,
            f1,
            f2,
            geometric_intersection_exists,
        ),
{
    lemma_mesh_faces_allowed_contact_relation_iff_runtime_branch_classifier(m, f1, f2);
    assert(mesh_faces_allowed_contact_relation_spec(m, f1, f2));

    assert(!mesh_faces_disjoint_boundary_spec(m, f1, f2)) by {
        if mesh_faces_disjoint_boundary_spec(m, f1, f2) {
            assert(!mesh_faces_share_vertex_spec(m, f1, f2));
            assert(!mesh_faces_share_edge_spec(m, f1, f2));
            assert(mesh_faces_share_vertex_spec(m, f1, f2) || mesh_faces_share_edge_spec(m, f1, f2));
            if mesh_faces_share_vertex_spec(m, f1, f2) {
                assert(false);
            } else {
                assert(mesh_faces_share_edge_spec(m, f1, f2));
                assert(false);
            }
        }
    };

    assert(!mesh_non_adjacent_face_pair_forbidden_intersection_relation_spec(
        m,
        f1,
        f2,
        geometric_intersection_exists,
    )) by {
        if mesh_non_adjacent_face_pair_forbidden_intersection_relation_spec(
            m,
            f1,
            f2,
            geometric_intersection_exists,
        ) {
            assert(mesh_faces_disjoint_boundary_spec(m, f1, f2));
            assert(!mesh_faces_disjoint_boundary_spec(m, f1, f2));
            assert(false);
        }
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_faces_shared_boundary_allowed_contact_not_non_adjacent_forbidden_relation(
    m: MeshModel,
    f1: int,
    f2: int,
    geometric_intersection_exists: bool,
)
    requires
        0 <= f1 < mesh_face_count_spec(m),
        0 <= f2 < mesh_face_count_spec(m),
        f1 != f2,
        (mesh_faces_share_exactly_one_vertex_spec(m, f1, f2) && !mesh_faces_share_edge_spec(m, f1, f2))
            || (mesh_faces_share_exactly_one_edge_spec(m, f1, f2)
                && mesh_faces_share_exactly_two_vertices_spec(m, f1, f2)),
    ensures
        mesh_faces_allowed_contact_relation_spec(m, f1, f2),
        mesh_faces_allowed_contact_runtime_branch_classifier_spec(m, f1, f2),
        !mesh_non_adjacent_face_pair_forbidden_intersection_relation_spec(
            m,
            f1,
            f2,
            geometric_intersection_exists,
        ),
{
    let mut shared_boundary = false;
    if mesh_faces_share_exactly_one_vertex_spec(m, f1, f2) && !mesh_faces_share_edge_spec(m, f1, f2) {
        assert(mesh_faces_allowed_contact_relation_spec(m, f1, f2));
        lemma_mesh_faces_share_exactly_one_vertex_implies_share_vertex(m, f1, f2);
        assert(mesh_faces_share_vertex_spec(m, f1, f2));
        shared_boundary = true;
    } else {
        assert(
            mesh_faces_share_exactly_one_edge_spec(m, f1, f2)
                && mesh_faces_share_exactly_two_vertices_spec(m, f1, f2)
        ) by {
            assert(
                (mesh_faces_share_exactly_one_vertex_spec(m, f1, f2)
                    && !mesh_faces_share_edge_spec(m, f1, f2))
                    || (mesh_faces_share_exactly_one_edge_spec(m, f1, f2)
                        && mesh_faces_share_exactly_two_vertices_spec(m, f1, f2))
            );
        };
        assert(mesh_faces_allowed_contact_relation_spec(m, f1, f2));
        lemma_mesh_faces_share_exactly_one_edge_implies_share_edge(m, f1, f2);
        assert(mesh_faces_share_edge_spec(m, f1, f2));
        shared_boundary = true;
    }
    assert(shared_boundary);
    assert(mesh_faces_share_vertex_spec(m, f1, f2) || mesh_faces_share_edge_spec(m, f1, f2));

    lemma_mesh_faces_allowed_contact_relation_iff_runtime_branch_classifier(m, f1, f2);
    assert(mesh_faces_allowed_contact_runtime_branch_classifier_spec(m, f1, f2));

    lemma_mesh_faces_shared_boundary_runtime_branch_classifier_not_non_adjacent_forbidden_relation(
        m,
        f1,
        f2,
        geometric_intersection_exists,
    );
    assert(!mesh_non_adjacent_face_pair_forbidden_intersection_relation_spec(
        m,
        f1,
        f2,
        geometric_intersection_exists,
    ));
}

pub open spec fn mesh_non_adjacent_face_pair_forbidden_intersection_relation_spec(
    m: MeshModel,
    f1: int,
    f2: int,
    geometric_intersection_exists: bool,
) -> bool {
    &&& 0 <= f1 < mesh_face_count_spec(m)
    &&& 0 <= f2 < mesh_face_count_spec(m)
    &&& f1 != f2
    &&& mesh_faces_disjoint_boundary_spec(m, f1, f2)
    &&& geometric_intersection_exists
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_default_point3_spec() -> vcad_math::point3::Point3 {
    vcad_math::point3::Point3::from_ints_spec(0, 0, 0)
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_geometry_input_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
) -> bool {
    vertex_positions.len() == mesh_vertex_count_spec(m)
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_runtime_vertex_positions_spec(m: &Mesh) -> Seq<vcad_math::point3::Point3> {
    Seq::new(m.vertices@.len(), |i: int| m.vertices@[i].position@)
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_runtime_geometry_bridge_spec(m: &Mesh) -> bool {
    let vertex_positions = mesh_runtime_vertex_positions_spec(m);
    &&& mesh_geometry_input_spec(m@, vertex_positions)
    &&& forall|v: int|
        0 <= v < mesh_vertex_count_spec(m@)
            ==> #[trigger] vertex_positions[v] == #[trigger] m.vertices@[v].position@
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_cycle_half_edge_or_default_spec(m: MeshModel, f: int, i: nat) -> int {
    if 0 <= f < mesh_face_count_spec(m) {
        let h = mesh_next_iter_spec(m, m.face_half_edges[f], i);
        if 0 <= h < mesh_half_edge_count_spec(m) {
            h
        } else {
            0
        }
    } else {
        0
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_cycle_vertex_index_or_default_spec(m: MeshModel, f: int, i: nat) -> int {
    let h = mesh_face_cycle_half_edge_or_default_spec(m, f, i);
    if 0 <= h < mesh_half_edge_count_spec(m) {
        let v = m.half_edges[h].vertex;
        if 0 <= v < mesh_vertex_count_spec(m) {
            v
        } else {
            0
        }
    } else {
        0
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_cycle_vertex_position_or_default_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    i: nat,
) -> vcad_math::point3::Point3 {
    let v = mesh_face_cycle_vertex_index_or_default_spec(m, f, i);
    if 0 <= v < vertex_positions.len() {
        vertex_positions[v]
    } else {
        mesh_default_point3_spec()
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_cycle_vertex_position_or_default_at_int_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    i: int,
) -> vcad_math::point3::Point3 {
    if i < 0 {
        mesh_default_point3_spec()
    } else {
        mesh_face_cycle_vertex_position_or_default_spec(m, vertex_positions, f, i as nat)
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_ordered_vertex_positions_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
) -> Seq<vcad_math::point3::Point3> {
    if k < 0 {
        Seq::<vcad_math::point3::Point3>::empty()
    } else {
        Seq::new(
            k as nat,
            |i: int| mesh_face_cycle_vertex_position_or_default_spec(m, vertex_positions, f, i as nat),
        )
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_runtime_face_ordered_vertex_positions_spec(
    m: &Mesh,
    f: int,
    k: int,
) -> Seq<vcad_math::point3::Point3> {
    mesh_face_ordered_vertex_positions_spec(m@, mesh_runtime_vertex_positions_spec(m), f, k)
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_points_collinear3_spec(
    a: vcad_math::point3::Point3,
    b: vcad_math::point3::Point3,
    c: vcad_math::point3::Point3,
) -> bool {
    b.sub_spec(a).cross_spec(c.sub_spec(a)).norm2_spec().signum() == 0
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_has_non_collinear_corner_triplet_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
) -> bool {
    exists|k: int, i: int| {
        &&& mesh_index_bounds_spec(m)
        &&& mesh_geometry_input_spec(m, vertex_positions)
        &&& 0 <= f < mesh_face_count_spec(m)
        &&& #[trigger] mesh_face_cycle_witness_spec(m, f, k)
        &&& 0 <= i
        &&& i + 2 < k
        &&& !mesh_points_collinear3_spec(
            #[trigger] mesh_face_cycle_vertex_position_or_default_at_int_spec(
                m,
                vertex_positions,
                f,
                i,
            ),
            #[trigger] mesh_face_cycle_vertex_position_or_default_at_int_spec(
                m,
                vertex_positions,
                f,
                i + 1,
            ),
            #[trigger] mesh_face_cycle_vertex_position_or_default_at_int_spec(
                m,
                vertex_positions,
                f,
                i + 2,
            ),
        )
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_all_faces_have_non_collinear_corner_triplets_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
) -> bool {
    &&& mesh_geometry_input_spec(m, vertex_positions)
    &&& forall|f: int|
        0 <= f < mesh_face_count_spec(m)
            ==> mesh_face_has_non_collinear_corner_triplet_spec(m, vertex_positions, f)
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_coplanar_witness_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
) -> bool {
    &&& mesh_index_bounds_spec(m)
    &&& mesh_geometry_input_spec(m, vertex_positions)
    &&& 0 <= f < mesh_face_count_spec(m)
    &&& #[trigger] mesh_face_cycle_witness_spec(m, f, k)
    &&& forall|i: int, j: int, l: int, d: int|
        0 <= i < k && 0 <= j < k && 0 <= l < k && 0 <= d < k ==> #[trigger]
            vcad_math::orientation3::is_coplanar(
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, i),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, j),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, l),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, d),
            )
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_coplanar_fixed_seed_witness_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
    seed_i: int,
) -> bool {
    let p0 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i);
    let p1 = mesh_face_cycle_vertex_position_or_default_at_int_spec(
        m,
        vertex_positions,
        f,
        seed_i + 1,
    );
    let p2 = mesh_face_cycle_vertex_position_or_default_at_int_spec(
        m,
        vertex_positions,
        f,
        seed_i + 2,
    );
    &&& mesh_index_bounds_spec(m)
    &&& mesh_geometry_input_spec(m, vertex_positions)
    &&& 0 <= f < mesh_face_count_spec(m)
    &&& #[trigger] mesh_face_cycle_witness_spec(m, f, k)
    &&& 0 <= seed_i
    &&& seed_i + 2 < k
    &&& forall|d: int|
        0 <= d < k ==> #[trigger] vcad_math::orientation3::is_coplanar(
            p0,
            p1,
            p2,
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, d),
        )
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_coplanar_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
) -> bool {
    &&& 0 <= f < mesh_face_count_spec(m)
    &&& exists|k: int| #[trigger] mesh_face_coplanar_witness_spec(m, vertex_positions, f, k)
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_all_faces_coplanar_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
) -> bool {
    &&& mesh_geometry_input_spec(m, vertex_positions)
    &&& forall|f: int| 0 <= f < mesh_face_count_spec(m)
        ==> #[trigger] mesh_face_coplanar_spec(m, vertex_positions, f)
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_coplanar_seed0_fixed_witness_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
) -> bool {
    &&& 0 <= f < mesh_face_count_spec(m)
    &&& exists|k: int| #[trigger] mesh_face_coplanar_fixed_seed_witness_spec(
        m,
        vertex_positions,
        f,
        k,
        0,
    )
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_all_faces_coplanar_seed0_fixed_witness_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
) -> bool {
    &&& mesh_geometry_input_spec(m, vertex_positions)
    &&& forall|f: int| 0 <= f < mesh_face_count_spec(m)
        ==> #[trigger] mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f)
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_all_faces_seed0_corner_non_collinear_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
) -> bool {
    &&& mesh_index_bounds_spec(m)
    &&& mesh_face_next_cycles_spec(m)
    &&& mesh_geometry_input_spec(m, vertex_positions)
    &&& forall|f: int|
        0 <= f < mesh_face_count_spec(m)
            ==> !mesh_points_collinear3_spec(
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 0),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 1),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 2),
            )
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_all_faces_seed0_plane_contains_vertices_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
) -> bool {
    &&& mesh_geometry_input_spec(m, vertex_positions)
    &&& forall|f: int|
        0 <= f < mesh_face_count_spec(m)
            ==> #[trigger] face_plane_contains_vertex_spec(
                m,
                vertex_positions,
                f,
                mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
                mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
            )
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_all_faces_oriented_seed0_planes_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
) -> bool {
    &&& mesh_geometry_input_spec(m, vertex_positions)
    &&& forall|f: int|
        0 <= f < mesh_face_count_spec(m)
            ==> #[trigger] mesh_face_oriented_plane_normal_spec(
                m,
                vertex_positions,
                f,
                mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
                mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
            )
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_cycle_position_trace_preserved_across_meshes_spec(
    m_before: MeshModel,
    vertex_positions_before: Seq<vcad_math::point3::Point3>,
    f_before: int,
    m_after: MeshModel,
    vertex_positions_after: Seq<vcad_math::point3::Point3>,
    f_after: int,
    k: int,
) -> bool {
    &&& mesh_index_bounds_spec(m_before)
    &&& mesh_index_bounds_spec(m_after)
    &&& mesh_geometry_input_spec(m_before, vertex_positions_before)
    &&& mesh_geometry_input_spec(m_after, vertex_positions_after)
    &&& 0 <= f_before < mesh_face_count_spec(m_before)
    &&& 0 <= f_after < mesh_face_count_spec(m_after)
    &&& #[trigger] mesh_face_cycle_witness_spec(m_before, f_before, k)
    &&& #[trigger] mesh_face_cycle_witness_spec(m_after, f_after, k)
    &&& forall|i: int|
        0 <= i < k ==> #[trigger] mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m_before,
            vertex_positions_before,
            f_before,
            i,
        ) == mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m_after,
            vertex_positions_after,
            f_after,
            i,
        )
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_projection_axis_from_normal_spec(
    normal: vcad_math::vec3::Vec3,
) -> int {
    if normal.x.signum() != 0 {
        0
    } else if normal.y.signum() != 0 {
        1
    } else {
        2
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_project_point3_to_2d_for_face_axis_spec(
    point: vcad_math::point3::Point3,
    axis: int,
) -> vcad_math::point2::Point2 {
    if axis == 0 {
        vcad_math::point2::Point2 { x: point.y, y: point.z }
    } else if axis == 1 {
        vcad_math::point2::Point2 { x: point.x, y: point.z }
    } else {
        vcad_math::point2::Point2 { x: point.x, y: point.y }
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_cycle_prev_index_spec(i: int, k: int) -> int {
    if i == 0 {
        k - 1
    } else {
        i - 1
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_cycle_next_index_spec(i: int, k: int) -> int {
    if i + 1 < k {
        i + 1
    } else {
        0
    }
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_cycle_prev_next_indices_in_bounds(i: int, k: int)
    requires
        0 < k,
        0 <= i < k,
    ensures
        0 <= mesh_face_cycle_prev_index_spec(i, k) < k,
        0 <= mesh_face_cycle_next_index_spec(i, k) < k,
{
    if i == 0 {
        assert(mesh_face_cycle_prev_index_spec(i, k) == k - 1);
        assert(0 <= k - 1);
        assert(k - 1 < k);
    } else {
        assert(i - 1 >= 0);
        assert(mesh_face_cycle_prev_index_spec(i, k) == i - 1);
        assert(i - 1 < k);
    }

    if i + 1 < k {
        assert(mesh_face_cycle_next_index_spec(i, k) == i + 1);
        assert(0 <= i + 1 < k);
    } else {
        assert(mesh_face_cycle_next_index_spec(i, k) == 0);
        assert(0 < k);
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_projected_turn_sign_at_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
    seed_i: int,
    i: int,
) -> int {
    let normal = mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i);
    let axis = mesh_face_projection_axis_from_normal_spec(normal);
    let prev_point = mesh_face_cycle_vertex_position_or_default_at_int_spec(
        m,
        vertex_positions,
        f,
        mesh_face_cycle_prev_index_spec(i, k),
    );
    let curr_point = mesh_face_cycle_vertex_position_or_default_at_int_spec(
        m,
        vertex_positions,
        f,
        i,
    );
    let next_point = mesh_face_cycle_vertex_position_or_default_at_int_spec(
        m,
        vertex_positions,
        f,
        mesh_face_cycle_next_index_spec(i, k),
    );
    vcad_math::orientation::orient2d_spec(
        mesh_project_point3_to_2d_for_face_axis_spec(prev_point, axis),
        mesh_project_point3_to_2d_for_face_axis_spec(curr_point, axis),
        mesh_project_point3_to_2d_for_face_axis_spec(next_point, axis),
    ).signum()
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_projected_turn_sign_consistency_witness_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
    seed_i: int,
    expected_sign: int,
) -> bool {
    &&& mesh_index_bounds_spec(m)
    &&& mesh_geometry_input_spec(m, vertex_positions)
    &&& 0 <= f < mesh_face_count_spec(m)
    &&& #[trigger] mesh_face_cycle_witness_spec(m, f, k)
    &&& 0 <= seed_i
    &&& seed_i + 2 < k
    &&& mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i).norm2_spec().signum() != 0
    &&& if k == 3 {
        let triangle_turn_sign = mesh_face_projected_turn_sign_at_spec(
            m,
            vertex_positions,
            f,
            k,
            seed_i,
            0,
        );
        &&& expected_sign != 0
        &&& triangle_turn_sign == expected_sign
    } else {
        &&& expected_sign != 0
        &&& forall|i: int|
            0 <= i < k ==> #[trigger] mesh_face_projected_turn_sign_at_spec(
                m,
                vertex_positions,
                f,
                k,
                seed_i,
                i,
            ) == expected_sign
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_projected_turn_sign_consistency_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
) -> bool {
    &&& 0 <= f < mesh_face_count_spec(m)
    &&& exists|k: int, seed_i: int, expected_sign: int| #[trigger]
        mesh_face_projected_turn_sign_consistency_witness_spec(
            m,
            vertex_positions,
            f,
            k,
            seed_i,
            expected_sign,
        )
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_all_faces_projected_turn_sign_consistency_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
) -> bool {
    &&& mesh_geometry_input_spec(m, vertex_positions)
    &&& forall|f: int| 0 <= f < mesh_face_count_spec(m)
        ==> #[trigger] mesh_face_projected_turn_sign_consistency_spec(m, vertex_positions, f)
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_projected_turn_legal_projection_inputs_witness_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
    seed_i: int,
) -> bool {
    let normal = mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i);
    let offset = mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, seed_i);
    &&& mesh_index_bounds_spec(m)
    &&& mesh_geometry_input_spec(m, vertex_positions)
    &&& 0 <= f < mesh_face_count_spec(m)
    &&& #[trigger] mesh_face_cycle_witness_spec(m, f, k)
    &&& 0 <= seed_i
    &&& seed_i + 2 < k
    &&& normal.norm2_spec().signum() != 0
    &&& forall|i: int| 0 <= i < k ==> {
        let prev_i = mesh_face_cycle_prev_index_spec(i, k);
        let next_i = mesh_face_cycle_next_index_spec(i, k);
        &&& 0 <= prev_i < k
        &&& 0 <= next_i < k
        &&& #[trigger] mesh_point_satisfies_plane_relative_to_origin_spec(
            normal,
            offset,
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, i),
        )
        &&& mesh_point_satisfies_plane_relative_to_origin_spec(
            normal,
            offset,
            mesh_face_cycle_vertex_position_or_default_at_int_spec(
                m,
                vertex_positions,
                f,
                prev_i,
            ),
        )
        &&& mesh_point_satisfies_plane_relative_to_origin_spec(
            normal,
            offset,
            mesh_face_cycle_vertex_position_or_default_at_int_spec(
                m,
                vertex_positions,
                f,
                next_i,
            ),
        )
    }
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_projected_turn_sign_witness_and_coplanar_fixed_seed_witness_use_legal_projection_inputs(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
    seed_i: int,
    expected_sign: int,
)
    requires
        mesh_face_projected_turn_sign_consistency_witness_spec(
            m,
            vertex_positions,
            f,
            k,
            seed_i,
            expected_sign,
        ),
        mesh_face_coplanar_fixed_seed_witness_spec(m, vertex_positions, f, k, seed_i),
    ensures
        mesh_face_projected_turn_legal_projection_inputs_witness_spec(
            m,
            vertex_positions,
            f,
            k,
            seed_i,
        ),
{
    let normal = mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i);
    let offset = mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, seed_i);

    lemma_mesh_face_coplanar_fixed_seed_witness_implies_seed_plane_contains_vertices(
        m,
        vertex_positions,
        f,
        k,
        seed_i,
    );
    assert(mesh_face_plane_contains_vertex_witness_spec(
        m,
        vertex_positions,
        f,
        k,
        normal,
        offset,
    ));

    assert forall|i: int| 0 <= i < k implies {
        let prev_i = mesh_face_cycle_prev_index_spec(i, k);
        let next_i = mesh_face_cycle_next_index_spec(i, k);
        &&& 0 <= prev_i < k
        &&& 0 <= next_i < k
        &&& #[trigger] mesh_point_satisfies_plane_relative_to_origin_spec(
            normal,
            offset,
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, i),
        )
        &&& mesh_point_satisfies_plane_relative_to_origin_spec(
            normal,
            offset,
            mesh_face_cycle_vertex_position_or_default_at_int_spec(
                m,
                vertex_positions,
                f,
                prev_i,
            ),
        )
        &&& mesh_point_satisfies_plane_relative_to_origin_spec(
            normal,
            offset,
            mesh_face_cycle_vertex_position_or_default_at_int_spec(
                m,
                vertex_positions,
                f,
                next_i,
            ),
        )
    } by {
        let prev_i = mesh_face_cycle_prev_index_spec(i, k);
        let next_i = mesh_face_cycle_next_index_spec(i, k);
        lemma_mesh_face_cycle_prev_next_indices_in_bounds(i, k);
        assert(0 <= prev_i < k);
        assert(0 <= next_i < k);

        assert(mesh_point_satisfies_plane_relative_to_origin_spec(
            normal,
            offset,
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, prev_i),
        ));
        assert(mesh_point_satisfies_plane_relative_to_origin_spec(
            normal,
            offset,
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, i),
        ));
        assert(mesh_point_satisfies_plane_relative_to_origin_spec(
            normal,
            offset,
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, next_i),
        ));
    };
    assert(mesh_face_projected_turn_legal_projection_inputs_witness_spec(
        m,
        vertex_positions,
        f,
        k,
        seed_i,
    ));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_projected_turn_sign_witness_uses_legal_projection_inputs(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
    seed_i: int,
    expected_sign: int,
)
    requires
        mesh_face_projected_turn_sign_consistency_witness_spec(
            m,
            vertex_positions,
            f,
            k,
            seed_i,
            expected_sign,
        ),
        mesh_face_coplanar_witness_spec(m, vertex_positions, f, k),
    ensures
        mesh_face_projected_turn_legal_projection_inputs_witness_spec(
            m,
            vertex_positions,
            f,
            k,
            seed_i,
        ),
{
    lemma_mesh_face_coplanar_witness_implies_fixed_seed_witness(
        m,
        vertex_positions,
        f,
        k,
        seed_i,
    );
    lemma_mesh_face_projected_turn_sign_witness_and_coplanar_fixed_seed_witness_use_legal_projection_inputs(
        m,
        vertex_positions,
        f,
        k,
        seed_i,
        expected_sign,
    );
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_triangle_face_projected_turn_sign_consistency_trivial(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    seed_i: int,
)
    requires
        mesh_index_bounds_spec(m),
        mesh_geometry_input_spec(m, vertex_positions),
        0 <= f < mesh_face_count_spec(m),
        mesh_face_cycle_witness_spec(m, f, 3),
        0 <= seed_i,
        seed_i + 2 < 3,
        mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i).norm2_spec().signum() != 0,
        mesh_face_projected_turn_sign_at_spec(m, vertex_positions, f, 3, seed_i, 0) != 0,
    ensures
        mesh_face_projected_turn_sign_consistency_spec(m, vertex_positions, f),
{
    let expected_sign = mesh_face_projected_turn_sign_at_spec(m, vertex_positions, f, 3, seed_i, 0);
    assert(expected_sign != 0);

    assert(mesh_face_projected_turn_sign_consistency_witness_spec(
        m,
        vertex_positions,
        f,
        3,
        seed_i,
        expected_sign,
    ));
    assert(exists|k: int, si: int, s: int| #[trigger]
        mesh_face_projected_turn_sign_consistency_witness_spec(
            m,
            vertex_positions,
            f,
            k,
            si,
            s,
        )) by {
        let k = 3;
        let si = seed_i;
        let s = expected_sign;
        assert(mesh_face_projected_turn_sign_consistency_witness_spec(
            m,
            vertex_positions,
            f,
            k,
            si,
            s,
        ));
    };
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_cycle_shift_index_spec(i: int, shift: int, k: int) -> int {
    if i + shift < k {
        i + shift
    } else {
        i + shift - k
    }
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_cycle_shift_index_in_bounds(i: int, shift: int, k: int)
    requires
        0 < k,
        0 <= i < k,
        0 <= shift < k,
    ensures
        0 <= mesh_face_cycle_shift_index_spec(i, shift, k) < k,
{
    if i + shift < k {
        assert(0 <= i + shift);
    } else {
        assert(k <= i + shift) by {
            if k <= i + shift {
            } else {
                assert(i + shift < k);
                assert(false);
            }
        };
        assert(i + shift < i + k);
        assert(i + k < k + k);
        assert(i + shift < k + k);
        assert(0 <= i + shift - k);
        assert(i + shift - k < k);
    }
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_coplanar_witness_stable_under_cyclic_reindexing(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
    shift: int,
)
    requires
        mesh_face_coplanar_witness_spec(m, vertex_positions, f, k),
        0 <= shift < k,
    ensures
        forall|i: int, j: int, l: int, d: int|
            0 <= i < k && 0 <= j < k && 0 <= l < k && 0 <= d < k ==> #[trigger]
                vcad_math::orientation3::is_coplanar(
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m,
                        vertex_positions,
                        f,
                        mesh_face_cycle_shift_index_spec(i, shift, k),
                    ),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m,
                        vertex_positions,
                        f,
                        mesh_face_cycle_shift_index_spec(j, shift, k),
                    ),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m,
                        vertex_positions,
                        f,
                        mesh_face_cycle_shift_index_spec(l, shift, k),
                    ),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m,
                        vertex_positions,
                        f,
                        mesh_face_cycle_shift_index_spec(d, shift, k),
                    ),
                ),
{
    assert(3 <= k <= mesh_half_edge_count_spec(m));
    assert(0 < k);

    assert forall|i: int, j: int, l: int, d: int|
        0 <= i < k && 0 <= j < k && 0 <= l < k && 0 <= d < k implies #[trigger]
            vcad_math::orientation3::is_coplanar(
                mesh_face_cycle_vertex_position_or_default_at_int_spec(
                    m,
                    vertex_positions,
                    f,
                    mesh_face_cycle_shift_index_spec(i, shift, k),
                ),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(
                    m,
                    vertex_positions,
                    f,
                    mesh_face_cycle_shift_index_spec(j, shift, k),
                ),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(
                    m,
                    vertex_positions,
                    f,
                    mesh_face_cycle_shift_index_spec(l, shift, k),
                ),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(
                    m,
                    vertex_positions,
                    f,
                    mesh_face_cycle_shift_index_spec(d, shift, k),
                ),
            ) by {
        lemma_mesh_face_cycle_shift_index_in_bounds(i, shift, k);
        lemma_mesh_face_cycle_shift_index_in_bounds(j, shift, k);
        lemma_mesh_face_cycle_shift_index_in_bounds(l, shift, k);
        lemma_mesh_face_cycle_shift_index_in_bounds(d, shift, k);

        let si = mesh_face_cycle_shift_index_spec(i, shift, k);
        let sj = mesh_face_cycle_shift_index_spec(j, shift, k);
        let sl = mesh_face_cycle_shift_index_spec(l, shift, k);
        let sd = mesh_face_cycle_shift_index_spec(d, shift, k);
        assert(0 <= si < k);
        assert(0 <= sj < k);
        assert(0 <= sl < k);
        assert(0 <= sd < k);
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_coplanar_witness_preserved_under_face_cycle_position_trace(
    m_before: MeshModel,
    vertex_positions_before: Seq<vcad_math::point3::Point3>,
    f_before: int,
    m_after: MeshModel,
    vertex_positions_after: Seq<vcad_math::point3::Point3>,
    f_after: int,
    k: int,
)
    requires
        mesh_face_cycle_position_trace_preserved_across_meshes_spec(
            m_before,
            vertex_positions_before,
            f_before,
            m_after,
            vertex_positions_after,
            f_after,
            k,
        ),
        mesh_face_coplanar_witness_spec(m_before, vertex_positions_before, f_before, k),
    ensures
        mesh_face_coplanar_witness_spec(m_after, vertex_positions_after, f_after, k),
{
    assert(mesh_index_bounds_spec(m_after));
    assert(mesh_geometry_input_spec(m_after, vertex_positions_after));
    assert(0 <= f_after < mesh_face_count_spec(m_after));
    assert(mesh_face_cycle_witness_spec(m_after, f_after, k));

    assert forall|i: int, j: int, l: int, d: int|
        0 <= i < k && 0 <= j < k && 0 <= l < k && 0 <= d < k implies #[trigger]
            vcad_math::orientation3::is_coplanar(
                mesh_face_cycle_vertex_position_or_default_at_int_spec(
                    m_after,
                    vertex_positions_after,
                    f_after,
                    i,
                ),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(
                    m_after,
                    vertex_positions_after,
                    f_after,
                    j,
                ),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(
                    m_after,
                    vertex_positions_after,
                    f_after,
                    l,
                ),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(
                    m_after,
                    vertex_positions_after,
                    f_after,
                    d,
                ),
            ) by {
        let bi = mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m_before,
            vertex_positions_before,
            f_before,
            i,
        );
        let bj = mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m_before,
            vertex_positions_before,
            f_before,
            j,
        );
        let bl = mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m_before,
            vertex_positions_before,
            f_before,
            l,
        );
        let bd = mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m_before,
            vertex_positions_before,
            f_before,
            d,
        );

        let ai = mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m_after,
            vertex_positions_after,
            f_after,
            i,
        );
        let aj = mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m_after,
            vertex_positions_after,
            f_after,
            j,
        );
        let al = mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m_after,
            vertex_positions_after,
            f_after,
            l,
        );
        let ad = mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m_after,
            vertex_positions_after,
            f_after,
            d,
        );

        assert(ai == bi);
        assert(aj == bj);
        assert(al == bl);
        assert(ad == bd);
        assert(vcad_math::orientation3::is_coplanar(bi, bj, bl, bd));
    };
    assert(mesh_face_coplanar_witness_spec(m_after, vertex_positions_after, f_after, k));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_coplanar_witness_implies_fixed_seed_witness(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
    seed_i: int,
)
    requires
        mesh_face_coplanar_witness_spec(m, vertex_positions, f, k),
        0 <= seed_i,
        seed_i + 2 < k,
    ensures
        mesh_face_coplanar_fixed_seed_witness_spec(m, vertex_positions, f, k, seed_i),
{
    let p0 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i);
    let p1 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 1);
    let p2 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 2);

    assert(mesh_index_bounds_spec(m));
    assert(mesh_geometry_input_spec(m, vertex_positions));
    assert(0 <= f < mesh_face_count_spec(m));
    assert(mesh_face_cycle_witness_spec(m, f, k));
    assert(0 <= seed_i < k);
    assert(0 <= seed_i + 1 < k);
    assert(0 <= seed_i + 2 < k);

    assert forall|d: int|
        0 <= d < k implies #[trigger] vcad_math::orientation3::is_coplanar(
            p0,
            p1,
            p2,
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, d),
        ) by {
        assert(0 <= d < k);
        assert(vcad_math::orientation3::is_coplanar(
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 1),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 2),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, d),
        ));
    };

    assert(mesh_face_coplanar_fixed_seed_witness_spec(m, vertex_positions, f, k, seed_i));
}

#[cfg(verus_keep_ghost)]
proof fn lemma_mesh_indices_in_0_1_2(i: int)
    requires
        0 <= i < 3,
    ensures
        i == 0 || i == 1 || i == 2,
{
    if i <= 0 {
        assert(0 <= i);
        assert(i == 0);
    } else if i <= 1 {
        assert(i > 0);
        assert(i >= 1) by {
            if i >= 1 {
            } else {
                assert(i < 1);
                assert(i <= 0);
                assert(false);
            }
        };
        assert(i == 1);
    } else {
        assert(i > 1);
        assert(i < 3);
        assert(i >= 2) by {
            if i >= 2 {
            } else {
                assert(i < 2);
                assert(i <= 1);
                assert(false);
            }
        };
        assert(i <= 2) by {
            if i <= 2 {
            } else {
                assert(i > 2);
                assert(i >= 3);
                assert(false);
            }
        };
        assert(i == 2);
    }
}

#[cfg(verus_keep_ghost)]
proof fn lemma_mesh_orient3d_first_three_repeated_implies_coplanar(
    a: vcad_math::point3::Point3,
    b: vcad_math::point3::Point3,
    c: vcad_math::point3::Point3,
    d: vcad_math::point3::Point3,
)
    ensures
        (a == b || a == c || b == c) ==> vcad_math::orientation3::is_coplanar(a, b, c, d),
{
    let o = vcad_math::orientation3::orient3d_spec(a, b, c, d);
    let z = vcad_math::scalar::Scalar::from_int_spec(0);

    if a == b {
        vcad_math::orientation3::lemma_orient3d_degenerate_repeated_points(a, c, d);
        assert(vcad_math::orientation3::orient3d_spec(a, a, c, d).signum() == 0);
        assert(vcad_math::orientation3::orient3d_spec(a, b, c, d).signum() == 0);
        assert(vcad_math::orientation3::is_coplanar(a, b, c, d));
    } else if b == c {
        let ba = b.sub_spec(a);
        let da = d.sub_spec(a);
        let obb = vcad_math::orientation3::orient3d_spec(a, b, b, d);

        vcad_math::vec3::Vec3::lemma_dot_cross_left_orthogonal(ba, da);
        assert(obb == ba.dot_spec(ba.cross_spec(da)));
        assert(ba.dot_spec(ba.cross_spec(da)).eqv_spec(z));
        vcad_math::scalar::Scalar::lemma_eqv_signum(obb, z);
        assert(z.signum() == 0);
        assert(obb.signum() == 0);
        assert(vcad_math::orientation3::is_coplanar(a, b, b, d));

        assert(o == obb);
        assert(o.signum() == 0);
        assert(vcad_math::orientation3::is_coplanar(a, b, c, d));
    } else if a == c {
        let os = vcad_math::orientation3::orient3d_spec(a, c, b, d);
        vcad_math::orientation3::lemma_orient3d_swap_bc_eqv_neg(a, b, c, d);
        assert(os.eqv_spec(o.neg_spec()));
        assert(os == vcad_math::orientation3::orient3d_spec(a, a, b, d));

        vcad_math::orientation3::lemma_orient3d_degenerate_repeated_points(a, b, d);
        assert(vcad_math::orientation3::orient3d_spec(a, a, b, d).signum() == 0);
        assert(os.signum() == 0);

        vcad_math::scalar::Scalar::lemma_eqv_signum(os, o.neg_spec());
        assert(o.neg_spec().signum() == 0);
        vcad_math::scalar::Scalar::lemma_signum_negate(o);
        assert(o.neg_spec().signum() == -o.signum());
        assert(-o.signum() == 0);
        assert(o.signum() == 0);
        assert(vcad_math::orientation3::is_coplanar(a, b, c, d));
    }
}

#[cfg(verus_keep_ghost)]
proof fn lemma_mesh_scalar_signum_zero_iff_neg_signum_zero(s: vcad_math::scalar::Scalar)
    ensures
        (s.signum() == 0) == (s.neg_spec().signum() == 0),
{
    vcad_math::scalar::Scalar::lemma_signum_negate(s);
    assert(s.neg_spec().signum() == -s.signum());

    if s.signum() == 0 {
        assert(-s.signum() == 0);
        assert(s.neg_spec().signum() == 0);
    } else if s.signum() == 1 {
        assert(-s.signum() == -1);
        assert(s.neg_spec().signum() == -1);
    } else {
        assert(s.signum() == -1);
        assert(-s.signum() == 1);
        assert(s.neg_spec().signum() == 1);
    }
}

#[cfg(verus_keep_ghost)]
proof fn lemma_mesh_orient3d_coplanar_invariant_under_swap_ab(
    a: vcad_math::point3::Point3,
    b: vcad_math::point3::Point3,
    c: vcad_math::point3::Point3,
    d: vcad_math::point3::Point3,
)
    ensures
        vcad_math::orientation3::is_coplanar(a, b, c, d)
            == vcad_math::orientation3::is_coplanar(b, a, c, d),
{
    let o = vcad_math::orientation3::orient3d_spec(a, b, c, d);
    let os = vcad_math::orientation3::orient3d_spec(b, a, c, d);

    vcad_math::orientation3::lemma_orient3d_swap_ab_eqv_neg(a, b, c, d);
    assert(os.eqv_spec(o.neg_spec()));
    vcad_math::scalar::Scalar::lemma_eqv_signum(os, o.neg_spec());
    assert(os.signum() == o.neg_spec().signum());
    lemma_mesh_scalar_signum_zero_iff_neg_signum_zero(o);
    assert((o.signum() == 0) == (o.neg_spec().signum() == 0));
    assert((o.signum() == 0) == (os.signum() == 0));

    assert(vcad_math::orientation3::is_coplanar(a, b, c, d) == (o.signum() == 0));
    assert(vcad_math::orientation3::is_coplanar(b, a, c, d) == (os.signum() == 0));
}

#[cfg(verus_keep_ghost)]
proof fn lemma_mesh_orient3d_coplanar_invariant_under_swap_ac(
    a: vcad_math::point3::Point3,
    b: vcad_math::point3::Point3,
    c: vcad_math::point3::Point3,
    d: vcad_math::point3::Point3,
)
    ensures
        vcad_math::orientation3::is_coplanar(a, b, c, d)
            == vcad_math::orientation3::is_coplanar(c, b, a, d),
{
    let o = vcad_math::orientation3::orient3d_spec(a, b, c, d);
    let os = vcad_math::orientation3::orient3d_spec(c, b, a, d);

    vcad_math::orientation3::lemma_orient3d_swap_ac_eqv_neg(a, b, c, d);
    assert(os.eqv_spec(o.neg_spec()));
    vcad_math::scalar::Scalar::lemma_eqv_signum(os, o.neg_spec());
    assert(os.signum() == o.neg_spec().signum());
    lemma_mesh_scalar_signum_zero_iff_neg_signum_zero(o);
    assert((o.signum() == 0) == (o.neg_spec().signum() == 0));
    assert((o.signum() == 0) == (os.signum() == 0));

    assert(vcad_math::orientation3::is_coplanar(a, b, c, d) == (o.signum() == 0));
    assert(vcad_math::orientation3::is_coplanar(c, b, a, d) == (os.signum() == 0));
}

#[cfg(verus_keep_ghost)]
proof fn lemma_mesh_orient3d_coplanar_invariant_under_swap_ad(
    a: vcad_math::point3::Point3,
    b: vcad_math::point3::Point3,
    c: vcad_math::point3::Point3,
    d: vcad_math::point3::Point3,
)
    ensures
        vcad_math::orientation3::is_coplanar(a, b, c, d)
            == vcad_math::orientation3::is_coplanar(d, b, c, a),
{
    let o = vcad_math::orientation3::orient3d_spec(a, b, c, d);
    let os = vcad_math::orientation3::orient3d_spec(d, b, c, a);

    vcad_math::orientation3::lemma_orient3d_swap_ad_eqv_neg(a, b, c, d);
    assert(os.eqv_spec(o.neg_spec()));
    vcad_math::scalar::Scalar::lemma_eqv_signum(os, o.neg_spec());
    assert(os.signum() == o.neg_spec().signum());
    lemma_mesh_scalar_signum_zero_iff_neg_signum_zero(o);
    assert((o.signum() == 0) == (o.neg_spec().signum() == 0));
    assert((o.signum() == 0) == (os.signum() == 0));

    assert(vcad_math::orientation3::is_coplanar(a, b, c, d) == (o.signum() == 0));
    assert(vcad_math::orientation3::is_coplanar(d, b, c, a) == (os.signum() == 0));
}

#[cfg(verus_keep_ghost)]
proof fn lemma_mesh_orient3d_coplanar_invariant_under_swap_bc(
    a: vcad_math::point3::Point3,
    b: vcad_math::point3::Point3,
    c: vcad_math::point3::Point3,
    d: vcad_math::point3::Point3,
)
    ensures
        vcad_math::orientation3::is_coplanar(a, b, c, d)
            == vcad_math::orientation3::is_coplanar(a, c, b, d),
{
    let o = vcad_math::orientation3::orient3d_spec(a, b, c, d);
    let os = vcad_math::orientation3::orient3d_spec(a, c, b, d);

    vcad_math::orientation3::lemma_orient3d_swap_bc_eqv_neg(a, b, c, d);
    assert(os.eqv_spec(o.neg_spec()));
    vcad_math::scalar::Scalar::lemma_eqv_signum(os, o.neg_spec());
    assert(os.signum() == o.neg_spec().signum());
    lemma_mesh_scalar_signum_zero_iff_neg_signum_zero(o);
    assert((o.signum() == 0) == (o.neg_spec().signum() == 0));
    assert((o.signum() == 0) == (os.signum() == 0));

    assert(vcad_math::orientation3::is_coplanar(a, b, c, d) == (o.signum() == 0));
    assert(vcad_math::orientation3::is_coplanar(a, c, b, d) == (os.signum() == 0));
}

#[cfg(verus_keep_ghost)]
proof fn lemma_mesh_orient3d_coplanar_invariant_under_swap_bd(
    a: vcad_math::point3::Point3,
    b: vcad_math::point3::Point3,
    c: vcad_math::point3::Point3,
    d: vcad_math::point3::Point3,
)
    ensures
        vcad_math::orientation3::is_coplanar(a, b, c, d)
            == vcad_math::orientation3::is_coplanar(a, d, c, b),
{
    let o = vcad_math::orientation3::orient3d_spec(a, b, c, d);
    let os = vcad_math::orientation3::orient3d_spec(a, d, c, b);

    vcad_math::orientation3::lemma_orient3d_swap_bd_eqv_neg(a, b, c, d);
    assert(os.eqv_spec(o.neg_spec()));
    vcad_math::scalar::Scalar::lemma_eqv_signum(os, o.neg_spec());
    assert(os.signum() == o.neg_spec().signum());
    lemma_mesh_scalar_signum_zero_iff_neg_signum_zero(o);
    assert((o.signum() == 0) == (o.neg_spec().signum() == 0));
    assert((o.signum() == 0) == (os.signum() == 0));

    assert(vcad_math::orientation3::is_coplanar(a, b, c, d) == (o.signum() == 0));
    assert(vcad_math::orientation3::is_coplanar(a, d, c, b) == (os.signum() == 0));
}

#[cfg(verus_keep_ghost)]
proof fn lemma_mesh_orient3d_coplanar_invariant_under_swap_cd(
    a: vcad_math::point3::Point3,
    b: vcad_math::point3::Point3,
    c: vcad_math::point3::Point3,
    d: vcad_math::point3::Point3,
)
    ensures
        vcad_math::orientation3::is_coplanar(a, b, c, d)
            == vcad_math::orientation3::is_coplanar(a, b, d, c),
{
    let o = vcad_math::orientation3::orient3d_spec(a, b, c, d);
    let os = vcad_math::orientation3::orient3d_spec(a, b, d, c);

    vcad_math::orientation3::lemma_orient3d_swap_cd_eqv_neg(a, b, c, d);
    assert(os.eqv_spec(o.neg_spec()));
    vcad_math::scalar::Scalar::lemma_eqv_signum(os, o.neg_spec());
    assert(os.signum() == o.neg_spec().signum());
    lemma_mesh_scalar_signum_zero_iff_neg_signum_zero(o);
    assert((o.signum() == 0) == (o.neg_spec().signum() == 0));
    assert((o.signum() == 0) == (os.signum() == 0));

    assert(vcad_math::orientation3::is_coplanar(a, b, c, d) == (o.signum() == 0));
    assert(vcad_math::orientation3::is_coplanar(a, b, d, c) == (os.signum() == 0));
}

#[cfg(verus_keep_ghost)]
proof fn lemma_mesh_orient3d_any_repeated_implies_coplanar(
    a: vcad_math::point3::Point3,
    b: vcad_math::point3::Point3,
    c: vcad_math::point3::Point3,
    d: vcad_math::point3::Point3,
)
    ensures
        (a == b || a == c || a == d || b == c || b == d || c == d)
            ==> vcad_math::orientation3::is_coplanar(a, b, c, d),
{
    if a == b || a == c || a == d || b == c || b == d || c == d {
        if a == b || a == c || b == c {
            lemma_mesh_orient3d_first_three_repeated_implies_coplanar(a, b, c, d);
            assert(vcad_math::orientation3::is_coplanar(a, b, c, d));
        } else if c == d {
            vcad_math::orientation3::lemma_orient3d_degenerate_repeated_points(a, b, c);
            assert(vcad_math::orientation3::orient3d_spec(a, b, c, c).signum() == 0);
            assert(vcad_math::orientation3::orient3d_spec(a, b, c, d).signum() == 0);
            assert(vcad_math::orientation3::is_coplanar(a, b, c, d));
        } else {
            assert(a == d || b == d);
            lemma_mesh_orient3d_coplanar_invariant_under_swap_cd(a, b, c, d);
            assert(
                vcad_math::orientation3::is_coplanar(a, b, c, d)
                    == vcad_math::orientation3::is_coplanar(a, b, d, c)
            );
            lemma_mesh_orient3d_first_three_repeated_implies_coplanar(a, b, d, c);
            assert(vcad_math::orientation3::is_coplanar(a, b, d, c));
            assert(vcad_math::orientation3::is_coplanar(a, b, c, d));
        }
    }
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_seed0_fixed_witness_implies_coplanar_witness_for_triangle_face(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
)
    requires
        mesh_face_coplanar_fixed_seed_witness_spec(m, vertex_positions, f, 3, 0),
    ensures
        mesh_face_coplanar_witness_spec(m, vertex_positions, f, 3),
{
    let p0 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 0);
    let p1 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 1);
    let p2 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 2);

    assert(mesh_index_bounds_spec(m));
    assert(mesh_geometry_input_spec(m, vertex_positions));
    assert(0 <= f < mesh_face_count_spec(m));
    assert(mesh_face_cycle_witness_spec(m, f, 3));

    assert forall|i: int, j: int, l: int, d: int|
        0 <= i < 3 && 0 <= j < 3 && 0 <= l < 3 && 0 <= d < 3 implies #[trigger]
            vcad_math::orientation3::is_coplanar(
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, i),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, j),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, l),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, d),
            ) by {
        let pi = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, i);
        let pj = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, j);
        let pl = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, l);
        let pd = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, d);
        let base = vcad_math::orientation3::orient3d_spec(p0, p1, p2, pd);

        assert(vcad_math::orientation3::is_coplanar(p0, p1, p2, pd)) by {
            assert(0 <= d < 3);
        };
        assert(base.signum() == 0);

        if i == j || i == l || j == l || i == d || j == d || l == d {
            lemma_mesh_orient3d_any_repeated_implies_coplanar(pi, pj, pl, pd);
            assert(vcad_math::orientation3::is_coplanar(pi, pj, pl, pd));
        } else {
            lemma_mesh_indices_in_0_1_2(i);
            lemma_mesh_indices_in_0_1_2(j);
            lemma_mesh_indices_in_0_1_2(l);

            if i == 0 && j == 1 {
                assert(l == 2);
                assert(pi == p0);
                assert(pj == p1);
                assert(pl == p2);
                assert(vcad_math::orientation3::is_coplanar(pi, pj, pl, pd));
            } else if i == 0 && j == 2 {
                assert(l == 1);
                let os = vcad_math::orientation3::orient3d_spec(p0, p2, p1, pd);
                vcad_math::orientation3::lemma_orient3d_swap_bc_eqv_neg(p0, p1, p2, pd);
                assert(os.eqv_spec(base.neg_spec()));
                vcad_math::scalar::Scalar::lemma_eqv_signum(os, base.neg_spec());
                vcad_math::scalar::Scalar::lemma_signum_negate(base);
                assert(base.neg_spec().signum() == 0);
                assert(os.signum() == 0);
                assert(vcad_math::orientation3::is_coplanar(p0, p2, p1, pd));
                assert(pi == p0);
                assert(pj == p2);
                assert(pl == p1);
                assert(vcad_math::orientation3::is_coplanar(pi, pj, pl, pd));
            } else if i == 1 && j == 0 {
                assert(l == 2);
                let os = vcad_math::orientation3::orient3d_spec(p1, p0, p2, pd);
                vcad_math::orientation3::lemma_orient3d_swap_ab_eqv_neg(p0, p1, p2, pd);
                assert(os.eqv_spec(base.neg_spec()));
                vcad_math::scalar::Scalar::lemma_eqv_signum(os, base.neg_spec());
                vcad_math::scalar::Scalar::lemma_signum_negate(base);
                assert(base.neg_spec().signum() == 0);
                assert(os.signum() == 0);
                assert(vcad_math::orientation3::is_coplanar(p1, p0, p2, pd));
                assert(pi == p1);
                assert(pj == p0);
                assert(pl == p2);
                assert(vcad_math::orientation3::is_coplanar(pi, pj, pl, pd));
            } else if i == 1 && j == 2 {
                assert(l == 0);
                let o210 = vcad_math::orientation3::orient3d_spec(p2, p1, p0, pd);
                let o120 = vcad_math::orientation3::orient3d_spec(p1, p2, p0, pd);
                vcad_math::orientation3::lemma_orient3d_swap_ac_eqv_neg(p0, p1, p2, pd);
                assert(o210.eqv_spec(base.neg_spec()));
                vcad_math::orientation3::lemma_orient3d_swap_ab_eqv_neg(p2, p1, p0, pd);
                assert(o120.eqv_spec(o210.neg_spec()));
                vcad_math::scalar::Scalar::lemma_eqv_signum(o210, base.neg_spec());
                vcad_math::scalar::Scalar::lemma_signum_negate(base);
                assert(base.neg_spec().signum() == 0);
                assert(o210.signum() == 0);
                vcad_math::scalar::Scalar::lemma_eqv_signum(o120, o210.neg_spec());
                vcad_math::scalar::Scalar::lemma_signum_negate(o210);
                assert(o210.neg_spec().signum() == 0);
                assert(o120.signum() == 0);
                assert(vcad_math::orientation3::is_coplanar(p1, p2, p0, pd));
                assert(pi == p1);
                assert(pj == p2);
                assert(pl == p0);
                assert(vcad_math::orientation3::is_coplanar(pi, pj, pl, pd));
            } else if i == 2 && j == 0 {
                assert(l == 1);
                let o021 = vcad_math::orientation3::orient3d_spec(p0, p2, p1, pd);
                let o201 = vcad_math::orientation3::orient3d_spec(p2, p0, p1, pd);
                vcad_math::orientation3::lemma_orient3d_swap_bc_eqv_neg(p0, p1, p2, pd);
                assert(o021.eqv_spec(base.neg_spec()));
                vcad_math::orientation3::lemma_orient3d_swap_ab_eqv_neg(p0, p2, p1, pd);
                assert(o201.eqv_spec(o021.neg_spec()));
                vcad_math::scalar::Scalar::lemma_eqv_signum(o021, base.neg_spec());
                vcad_math::scalar::Scalar::lemma_signum_negate(base);
                assert(base.neg_spec().signum() == 0);
                assert(o021.signum() == 0);
                vcad_math::scalar::Scalar::lemma_eqv_signum(o201, o021.neg_spec());
                vcad_math::scalar::Scalar::lemma_signum_negate(o021);
                assert(o021.neg_spec().signum() == 0);
                assert(o201.signum() == 0);
                assert(vcad_math::orientation3::is_coplanar(p2, p0, p1, pd));
                assert(pi == p2);
                assert(pj == p0);
                assert(pl == p1);
                assert(vcad_math::orientation3::is_coplanar(pi, pj, pl, pd));
            } else {
                assert(i == 2 && j == 1);
                assert(l == 0);
                let os = vcad_math::orientation3::orient3d_spec(p2, p1, p0, pd);
                vcad_math::orientation3::lemma_orient3d_swap_ac_eqv_neg(p0, p1, p2, pd);
                assert(os.eqv_spec(base.neg_spec()));
                vcad_math::scalar::Scalar::lemma_eqv_signum(os, base.neg_spec());
                vcad_math::scalar::Scalar::lemma_signum_negate(base);
                assert(base.neg_spec().signum() == 0);
                assert(os.signum() == 0);
                assert(vcad_math::orientation3::is_coplanar(p2, p1, p0, pd));
                assert(pi == p2);
                assert(pj == p1);
                assert(pl == p0);
                assert(vcad_math::orientation3::is_coplanar(pi, pj, pl, pd));
            }
        }
    };

    assert(mesh_face_coplanar_witness_spec(m, vertex_positions, f, 3));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_cycle_witness_length_unique(
    m: MeshModel,
    f: int,
    k1: int,
    k2: int,
)
    requires
        0 <= f < mesh_face_count_spec(m),
        mesh_face_cycle_witness_spec(m, f, k1),
        mesh_face_cycle_witness_spec(m, f, k2),
    ensures
        k1 == k2,
{
    let start = m.face_half_edges[f];

    assert(3 <= k1);
    assert(3 <= k2);
    assert(mesh_next_iter_spec(m, start, k1 as nat) == start);
    assert(mesh_next_iter_spec(m, start, k2 as nat) == start);
    assert(mesh_next_iter_spec(m, start, 0) == start);

    if k1 < k2 {
        let i0: int = 0;
        let j0: int = k1;
        assert(0 <= 0 < k1);
        assert(0 <= k1 < k2);
        assert(0 <= i0 < j0 < k2);
        assert(mesh_next_iter_spec(m, start, i0 as nat) == mesh_next_iter_spec(m, start, j0 as nat));
        assert(forall|i: int, j: int|
            #![trigger mesh_next_iter_spec(m, start, i as nat), mesh_next_iter_spec(m, start, j as nat)]
            0 <= i < j < k2 ==> mesh_next_iter_spec(m, start, i as nat) != mesh_next_iter_spec(
                m,
                start,
                j as nat,
            ));
        assert(mesh_next_iter_spec(m, start, i0 as nat) != mesh_next_iter_spec(m, start, j0 as nat)) by {
            assert(0 <= i0 < j0 < k2);
            assert(forall|i: int, j: int|
                #![trigger mesh_next_iter_spec(m, start, i as nat), mesh_next_iter_spec(m, start, j as nat)]
                0 <= i < j < k2 ==> mesh_next_iter_spec(m, start, i as nat) != mesh_next_iter_spec(
                    m,
                    start,
                    j as nat,
                ));
        };
        assert(false);
    }

    if k2 < k1 {
        let i0: int = 0;
        let j0: int = k2;
        assert(0 <= 0 < k2);
        assert(0 <= k2 < k1);
        assert(0 <= i0 < j0 < k1);
        assert(mesh_next_iter_spec(m, start, i0 as nat) == mesh_next_iter_spec(m, start, j0 as nat));
        assert(forall|i: int, j: int|
            #![trigger mesh_next_iter_spec(m, start, i as nat), mesh_next_iter_spec(m, start, j as nat)]
            0 <= i < j < k1 ==> mesh_next_iter_spec(m, start, i as nat) != mesh_next_iter_spec(
                m,
                start,
                j as nat,
            ));
        assert(mesh_next_iter_spec(m, start, i0 as nat) != mesh_next_iter_spec(m, start, j0 as nat)) by {
            assert(0 <= i0 < j0 < k1);
            assert(forall|i: int, j: int|
                #![trigger mesh_next_iter_spec(m, start, i as nat), mesh_next_iter_spec(m, start, j as nat)]
                0 <= i < j < k1 ==> mesh_next_iter_spec(m, start, i as nat) != mesh_next_iter_spec(
                    m,
                    start,
                    j as nat,
                ));
        };
        assert(false);
    }

    assert(k1 == k2);
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_coplanar_spec_and_face_cycle_witness_imply_coplanar_witness_at_cycle_len(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
)
    requires
        mesh_face_coplanar_spec(m, vertex_positions, f),
        mesh_face_cycle_witness_spec(m, f, k),
    ensures
        mesh_face_coplanar_witness_spec(m, vertex_positions, f, k),
{
    assert(0 <= f < mesh_face_count_spec(m));
    let kw = choose|kw: int| mesh_face_coplanar_witness_spec(m, vertex_positions, f, kw);
    assert(mesh_face_coplanar_witness_spec(m, vertex_positions, f, kw));
    assert(mesh_face_cycle_witness_spec(m, f, kw));
    lemma_mesh_face_cycle_witness_length_unique(m, f, kw, k);
    assert(kw == k);
    assert(mesh_face_coplanar_witness_spec(m, vertex_positions, f, k));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_coplanar_spec_and_face_cycle_witness_imply_seed0_fixed_witness_at_cycle_len(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
)
    requires
        mesh_face_coplanar_spec(m, vertex_positions, f),
        mesh_face_cycle_witness_spec(m, f, k),
    ensures
        mesh_face_coplanar_fixed_seed_witness_spec(m, vertex_positions, f, k, 0),
{
    lemma_mesh_face_coplanar_spec_and_face_cycle_witness_imply_coplanar_witness_at_cycle_len(
        m,
        vertex_positions,
        f,
        k,
    );
    assert(3 <= k);
    lemma_mesh_face_coplanar_witness_implies_fixed_seed_witness(m, vertex_positions, f, k, 0);
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_coplanar_seed0_fixed_witness_and_face_cycle_witness_imply_fixed_witness_at_cycle_len(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
)
    requires
        mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f),
        mesh_face_cycle_witness_spec(m, f, k),
    ensures
        mesh_face_coplanar_fixed_seed_witness_spec(m, vertex_positions, f, k, 0),
{
    assert(0 <= f < mesh_face_count_spec(m));
    let kw = choose|kw: int| mesh_face_coplanar_fixed_seed_witness_spec(
        m,
        vertex_positions,
        f,
        kw,
        0,
    );
    assert(mesh_face_coplanar_fixed_seed_witness_spec(m, vertex_positions, f, kw, 0));
    assert(mesh_face_cycle_witness_spec(m, f, kw));
    lemma_mesh_face_cycle_witness_length_unique(m, f, kw, k);
    assert(kw == k);
    assert(mesh_face_coplanar_fixed_seed_witness_spec(m, vertex_positions, f, k, 0));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_all_faces_coplanar_seed0_fixed_witness_and_face_next_cycles_witness_imply_all_faces_seed0_fixed_witness_at_cycle_lens(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    face_cycle_lens: Seq<usize>,
)
    requires
        mesh_all_faces_coplanar_seed0_fixed_witness_spec(m, vertex_positions),
        mesh_face_next_cycles_witness_spec(m, face_cycle_lens),
    ensures
        forall|f: int|
            0 <= f < mesh_face_count_spec(m)
                ==> #[trigger] mesh_face_coplanar_fixed_seed_witness_spec(
                    m,
                    vertex_positions,
                    f,
                    face_cycle_lens[f] as int,
                    0,
                ),
{
    assert(mesh_geometry_input_spec(m, vertex_positions));
    assert(face_cycle_lens.len() == mesh_face_count_spec(m));
    assert forall|f: int|
        0 <= f < mesh_face_count_spec(m)
            implies #[trigger] mesh_face_coplanar_fixed_seed_witness_spec(
                m,
                vertex_positions,
                f,
                face_cycle_lens[f] as int,
                0,
            ) by {
        assert(mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f));
        assert(mesh_face_cycle_witness_spec(m, f, face_cycle_lens[f] as int));
        lemma_mesh_face_coplanar_seed0_fixed_witness_and_face_cycle_witness_imply_fixed_witness_at_cycle_len(
            m,
            vertex_positions,
            f,
            face_cycle_lens[f] as int,
        );
    };
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_plane_offset_relative_to_origin_spec(
    normal: vcad_math::vec3::Vec3,
    point: vcad_math::point3::Point3,
) -> vcad_math::scalar::Scalar {
    let origin = vcad_math::point3::Point3::from_ints_spec(0, 0, 0);
    normal.dot_spec(point.sub_spec(origin))
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_point_plane_value_relative_to_origin_spec(
    normal: vcad_math::vec3::Vec3,
    offset: vcad_math::scalar::Scalar,
    point: vcad_math::point3::Point3,
) -> vcad_math::scalar::Scalar {
    mesh_plane_offset_relative_to_origin_spec(normal, point).sub_spec(offset)
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_point_satisfies_plane_relative_to_origin_spec(
    normal: vcad_math::vec3::Vec3,
    offset: vcad_math::scalar::Scalar,
    point: vcad_math::point3::Point3,
) -> bool {
    mesh_point_plane_value_relative_to_origin_spec(normal, offset, point).signum() == 0
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_seed_plane_normal_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    seed_i: int,
) -> vcad_math::vec3::Vec3 {
    let p0 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i);
    let p1 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 1);
    let p2 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 2);
    p1.sub_spec(p0).cross_spec(p2.sub_spec(p0))
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_seed_plane_edge_direction_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    seed_i: int,
) -> vcad_math::vec3::Vec3 {
    let p0 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i);
    let p1 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 1);
    p1.sub_spec(p0)
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_seed_plane_corner_direction_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    seed_i: int,
) -> vcad_math::vec3::Vec3 {
    let p0 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i);
    let p2 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 2);
    p2.sub_spec(p0)
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_seed_plane_normal_decomposes_into_seed_directions(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    seed_i: int,
)
    ensures
        mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i)
            == mesh_face_seed_plane_edge_direction_spec(m, vertex_positions, f, seed_i).cross_spec(
                mesh_face_seed_plane_corner_direction_spec(m, vertex_positions, f, seed_i),
            ),
{
    let p0 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i);
    let p1 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 1);
    let p2 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 2);
    assert(
        mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i)
            == p1.sub_spec(p0).cross_spec(p2.sub_spec(p0))
    );
    assert(mesh_face_seed_plane_edge_direction_spec(m, vertex_positions, f, seed_i) == p1.sub_spec(p0));
    assert(mesh_face_seed_plane_corner_direction_spec(m, vertex_positions, f, seed_i) == p2.sub_spec(p0));
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_seed_plane_offset_relative_to_origin_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    seed_i: int,
) -> vcad_math::scalar::Scalar {
    let p0 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i);
    mesh_plane_offset_relative_to_origin_spec(
        mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i),
        p0,
    )
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_point_plane_value_relative_to_origin_matches_relative_dot(
    normal: vcad_math::vec3::Vec3,
    plane_point: vcad_math::point3::Point3,
    point: vcad_math::point3::Point3,
)
    ensures
        mesh_point_plane_value_relative_to_origin_spec(
            normal,
            mesh_plane_offset_relative_to_origin_spec(normal, plane_point),
            point,
        ).eqv_spec(normal.dot_spec(point.sub_spec(plane_point))),
{
    let origin = vcad_math::point3::Point3::from_ints_spec(0, 0, 0);
    let point_from_origin = point.sub_spec(origin);
    let plane_from_origin = plane_point.sub_spec(origin);
    let point_from_plane = point.sub_spec(plane_point);
    let point_from_plane_plus_origin = point_from_plane.add_spec(plane_from_origin);
    let dot_point_from_origin = normal.dot_spec(point_from_origin);
    let dot_point_from_plane = normal.dot_spec(point_from_plane);
    let dot_plane_from_origin = normal.dot_spec(plane_from_origin);
    let dot_split = normal.dot_spec(point_from_plane_plus_origin);

    vcad_math::point3::Point3::lemma_sub_chain_eqv(point, plane_point, origin);
    vcad_math::vec3::Vec3::lemma_eqv_from_components(point_from_origin, point_from_plane_plus_origin);
    vcad_math::vec3::Vec3::lemma_dot_eqv_congruence(
        normal,
        normal,
        point_from_origin,
        point_from_plane_plus_origin,
    );
    vcad_math::vec3::Vec3::lemma_dot_linear_right(normal, point_from_plane, plane_from_origin);
    assert(dot_point_from_origin.eqv_spec(dot_split));
    assert(dot_split.eqv_spec(dot_point_from_plane.add_spec(dot_plane_from_origin)));
    vcad_math::scalar::Scalar::lemma_eqv_transitive(
        dot_point_from_origin,
        dot_split,
        dot_point_from_plane.add_spec(dot_plane_from_origin),
    );
    assert(dot_point_from_origin.eqv_spec(dot_point_from_plane.add_spec(dot_plane_from_origin)));

    vcad_math::scalar::Scalar::lemma_eqv_sub_congruence(
        dot_point_from_origin,
        dot_point_from_plane.add_spec(dot_plane_from_origin),
        dot_plane_from_origin,
        dot_plane_from_origin,
    );
    assert(
        dot_point_from_origin.sub_spec(dot_plane_from_origin).eqv_spec(
            dot_point_from_plane.add_spec(dot_plane_from_origin).sub_spec(dot_plane_from_origin)
        )
    );

    vcad_math::scalar::Scalar::lemma_add_commutative(dot_point_from_plane, dot_plane_from_origin);
    vcad_math::scalar::Scalar::lemma_eqv_sub_congruence(
        dot_point_from_plane.add_spec(dot_plane_from_origin),
        dot_plane_from_origin.add_spec(dot_point_from_plane),
        dot_plane_from_origin,
        dot_plane_from_origin,
    );
    vcad_math::scalar::Scalar::lemma_add_then_sub_cancel(dot_plane_from_origin, dot_point_from_plane);

    vcad_math::scalar::Scalar::lemma_eqv_transitive(
        dot_point_from_origin.sub_spec(dot_plane_from_origin),
        dot_point_from_plane.add_spec(dot_plane_from_origin).sub_spec(dot_plane_from_origin),
        dot_plane_from_origin.add_spec(dot_point_from_plane).sub_spec(dot_plane_from_origin),
    );
    vcad_math::scalar::Scalar::lemma_eqv_transitive(
        dot_point_from_origin.sub_spec(dot_plane_from_origin),
        dot_plane_from_origin.add_spec(dot_point_from_plane).sub_spec(dot_plane_from_origin),
        dot_point_from_plane,
    );

    assert(mesh_plane_offset_relative_to_origin_spec(normal, plane_point) == dot_plane_from_origin);
    assert(
        mesh_point_plane_value_relative_to_origin_spec(
            normal,
            mesh_plane_offset_relative_to_origin_spec(normal, plane_point),
            point,
        ).eqv_spec(dot_point_from_plane)
    );
    assert(dot_point_from_plane == normal.dot_spec(point.sub_spec(plane_point)));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_points_on_same_plane_relative_to_origin_imply_normal_orthogonal_delta(
    normal: vcad_math::vec3::Vec3,
    offset: vcad_math::scalar::Scalar,
    a: vcad_math::point3::Point3,
    b: vcad_math::point3::Point3,
)
    requires
        mesh_point_satisfies_plane_relative_to_origin_spec(normal, offset, a),
        mesh_point_satisfies_plane_relative_to_origin_spec(normal, offset, b),
    ensures
        normal.dot_spec(b.sub_spec(a)).signum() == 0,
{
    let z = vcad_math::scalar::Scalar::from_int_spec(0);
    let off_a = mesh_plane_offset_relative_to_origin_spec(normal, a);
    let off_b = mesh_plane_offset_relative_to_origin_spec(normal, b);
    let va = mesh_point_plane_value_relative_to_origin_spec(normal, offset, a);
    let vb = mesh_point_plane_value_relative_to_origin_spec(normal, offset, b);
    let dot_ba = normal.dot_spec(b.sub_spec(a));

    assert(va.signum() == 0);
    assert(vb.signum() == 0);

    assert(va.num == 0) by {
        if va.num > 0 {
            assert(va.signum() == 1);
            assert(false);
        } else if va.num < 0 {
            assert(va.signum() == -1);
            assert(false);
        }
    };
    assert(vb.num == 0) by {
        if vb.num > 0 {
            assert(vb.signum() == 1);
            assert(false);
        } else if vb.num < 0 {
            assert(vb.signum() == -1);
            assert(false);
        }
    };

    assert(va == off_a.sub_spec(offset));
    assert(vb == off_b.sub_spec(offset));

    assert(off_a.eqv_spec(offset)) by {
        assert(va.num == off_a.num * offset.denom() + (-offset.num) * off_a.denom());
        assert(off_a.num * offset.denom() + (-offset.num) * off_a.denom() == 0);
        assert(
            off_a.num * offset.denom() + (-offset.num) * off_a.denom()
                == off_a.num * offset.denom() - offset.num * off_a.denom()
        ) by (nonlinear_arith);
        assert(off_a.num * offset.denom() - offset.num * off_a.denom() == 0);
        assert(
            (off_a.num * offset.denom() == offset.num * off_a.denom())
                == (off_a.num * offset.denom() + (-offset.num) * off_a.denom() == 0)
        ) by (nonlinear_arith);
        assert(off_a.num * offset.denom() == offset.num * off_a.denom());
        assert(off_a.eqv_spec(offset));
    };
    assert(off_b.eqv_spec(offset)) by {
        assert(vb.num == off_b.num * offset.denom() + (-offset.num) * off_b.denom());
        assert(off_b.num * offset.denom() + (-offset.num) * off_b.denom() == 0);
        assert(
            off_b.num * offset.denom() + (-offset.num) * off_b.denom()
                == off_b.num * offset.denom() - offset.num * off_b.denom()
        ) by (nonlinear_arith);
        assert(off_b.num * offset.denom() - offset.num * off_b.denom() == 0);
        assert(
            (off_b.num * offset.denom() == offset.num * off_b.denom())
                == (off_b.num * offset.denom() + (-offset.num) * off_b.denom() == 0)
        ) by (nonlinear_arith);
        assert(off_b.num * offset.denom() == offset.num * off_b.denom());
        assert(off_b.eqv_spec(offset));
    };

    vcad_math::scalar::Scalar::lemma_eqv_symmetric(off_a, offset);
    assert(offset.eqv_spec(off_a));
    vcad_math::scalar::Scalar::lemma_eqv_transitive(off_b, offset, off_a);
    assert(off_b.eqv_spec(off_a));

    vcad_math::scalar::Scalar::lemma_sub_eqv_zero_iff_eqv(off_b, off_a);
    assert(off_b.sub_spec(off_a).eqv_spec(z));

    lemma_mesh_point_plane_value_relative_to_origin_matches_relative_dot(normal, a, b);
    assert(mesh_point_plane_value_relative_to_origin_spec(
        normal,
        mesh_plane_offset_relative_to_origin_spec(normal, a),
        b,
    ).eqv_spec(dot_ba));
    assert(mesh_point_plane_value_relative_to_origin_spec(
        normal,
        mesh_plane_offset_relative_to_origin_spec(normal, a),
        b,
    ) == off_b.sub_spec(off_a));

    vcad_math::scalar::Scalar::lemma_eqv_symmetric(
        mesh_point_plane_value_relative_to_origin_spec(
            normal,
            mesh_plane_offset_relative_to_origin_spec(normal, a),
            b,
        ),
        dot_ba,
    );
    assert(dot_ba.eqv_spec(off_b.sub_spec(off_a)));
    vcad_math::scalar::Scalar::lemma_eqv_transitive(dot_ba, off_b.sub_spec(off_a), z);
    assert(dot_ba.eqv_spec(z));
    vcad_math::scalar::Scalar::lemma_eqv_signum(dot_ba, z);
    assert(z.signum() == 0);
    assert(dot_ba.signum() == 0);
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_plane_contains_vertex_witness_implies_normal_orthogonal_face_chords(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
    normal: vcad_math::vec3::Vec3,
    offset: vcad_math::scalar::Scalar,
)
    requires
        mesh_face_plane_contains_vertex_witness_spec(m, vertex_positions, f, k, normal, offset),
    ensures
        forall|i: int, j: int|
            0 <= i < k && 0 <= j < k ==> #[trigger] normal.dot_spec(
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, j).sub_spec(
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m,
                        vertex_positions,
                        f,
                        i,
                    ),
                ),
            ).signum() == 0,
{
    assert forall|i: int, j: int|
        0 <= i < k && 0 <= j < k implies #[trigger] normal.dot_spec(
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, j).sub_spec(
                mesh_face_cycle_vertex_position_or_default_at_int_spec(
                    m,
                    vertex_positions,
                    f,
                    i,
                ),
            ),
        ).signum() == 0 by {
        let pi = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, i);
        let pj = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, j);
        assert(mesh_point_satisfies_plane_relative_to_origin_spec(normal, offset, pi));
        assert(mesh_point_satisfies_plane_relative_to_origin_spec(normal, offset, pj));
        lemma_mesh_points_on_same_plane_relative_to_origin_imply_normal_orthogonal_delta(
            normal,
            offset,
            pi,
            pj,
        );
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_coplanar_witness_seed_plane_contains_vertices(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
    seed_i: int,
)
    requires
        mesh_face_coplanar_witness_spec(m, vertex_positions, f, k),
        0 <= seed_i,
        seed_i + 2 < k,
    ensures
        mesh_face_plane_contains_vertex_witness_spec(
            m,
            vertex_positions,
            f,
            k,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, seed_i),
        ),
{
    lemma_mesh_face_coplanar_witness_implies_fixed_seed_witness(m, vertex_positions, f, k, seed_i);
    lemma_mesh_face_coplanar_fixed_seed_witness_implies_seed_plane_contains_vertices(
        m,
        vertex_positions,
        f,
        k,
        seed_i,
    );
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_coplanar_fixed_seed_witness_implies_seed_plane_contains_vertices(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
    seed_i: int,
)
    requires
        mesh_face_coplanar_fixed_seed_witness_spec(m, vertex_positions, f, k, seed_i),
    ensures
        mesh_face_plane_contains_vertex_witness_spec(
            m,
            vertex_positions,
            f,
            k,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, seed_i),
        ),
{
    let p0 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i);
    let p1 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 1);
    let p2 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 2);
    let normal = mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i);
    let offset = mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, seed_i);
    let ba = p1.sub_spec(p0);
    let ca = p2.sub_spec(p0);

    assert(mesh_index_bounds_spec(m));
    assert(mesh_geometry_input_spec(m, vertex_positions));
    assert(0 <= f < mesh_face_count_spec(m));
    assert(mesh_face_cycle_witness_spec(m, f, k));
    assert(0 <= seed_i < k);
    assert(0 <= seed_i + 1 < k);
    assert(0 <= seed_i + 2 < k);

    assert forall|j: int| 0 <= j < k implies #[trigger] mesh_point_satisfies_plane_relative_to_origin_spec(
        normal,
        offset,
        mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, j),
    ) by {
        let pj = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, j);
        let da = pj.sub_spec(p0);
        let orient = vcad_math::orientation3::orient3d_spec(p0, p1, p2, pj);
        let plane_value = mesh_point_plane_value_relative_to_origin_spec(normal, offset, pj);

        assert(vcad_math::orientation3::is_coplanar(p0, p1, p2, pj));
        assert(orient.signum() == 0);

        lemma_mesh_point_plane_value_relative_to_origin_matches_relative_dot(normal, p0, pj);
        assert(plane_value.eqv_spec(normal.dot_spec(da)));

        vcad_math::vec3::Vec3::lemma_dot_symmetric(normal, da);
        vcad_math::vec3::Vec3::lemma_dot_cross_cyclic(da, ba, ca);
        assert(da.dot_spec(ba.cross_spec(ca)).eqv_spec(orient));
        assert(da.dot_spec(normal).eqv_spec(orient));
        vcad_math::scalar::Scalar::lemma_eqv_transitive(
            normal.dot_spec(da),
            da.dot_spec(normal),
            orient,
        );
        assert(normal.dot_spec(da).eqv_spec(orient));
        vcad_math::scalar::Scalar::lemma_eqv_transitive(
            plane_value,
            normal.dot_spec(da),
            orient,
        );
        assert(plane_value.eqv_spec(orient));
        vcad_math::scalar::Scalar::lemma_eqv_signum(plane_value, orient);
        assert(plane_value.signum() == orient.signum());
        assert(plane_value.signum() == 0);
    };

    assert(mesh_face_plane_contains_vertex_witness_spec(m, vertex_positions, f, k, normal, offset));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_coplanar_spec_implies_seed0_plane_contains_vertices(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
)
    requires
        mesh_face_coplanar_spec(m, vertex_positions, f),
    ensures
        face_plane_contains_vertex_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ),
{
    let k = choose|k: int| mesh_face_coplanar_witness_spec(m, vertex_positions, f, k);
    assert(mesh_face_coplanar_witness_spec(m, vertex_positions, f, k));
    assert(3 <= k);
    lemma_mesh_face_coplanar_witness_seed_plane_contains_vertices(m, vertex_positions, f, k, 0);
    assert(face_plane_contains_vertex_spec(
        m,
        vertex_positions,
        f,
        mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
        mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
    )) by {
        assert(0 <= f < mesh_face_count_spec(m));
        let kw = k;
        assert(mesh_face_plane_contains_vertex_witness_spec(
            m,
            vertex_positions,
            f,
            kw,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ));
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_coplanar_spec_implies_seed0_fixed_witness(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
)
    requires
        mesh_face_coplanar_spec(m, vertex_positions, f),
    ensures
        mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f),
{
    let k = choose|k: int| mesh_face_coplanar_witness_spec(m, vertex_positions, f, k);
    assert(mesh_face_coplanar_witness_spec(m, vertex_positions, f, k));
    assert(3 <= k);
    lemma_mesh_face_coplanar_witness_implies_fixed_seed_witness(m, vertex_positions, f, k, 0);

    assert(mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f)) by {
        assert(0 <= f < mesh_face_count_spec(m));
        let kw = k;
        assert(mesh_face_coplanar_fixed_seed_witness_spec(m, vertex_positions, f, kw, 0));
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_all_faces_coplanar_spec_implies_all_faces_seed0_fixed_witness(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
)
    requires
        mesh_all_faces_coplanar_spec(m, vertex_positions),
    ensures
        mesh_all_faces_coplanar_seed0_fixed_witness_spec(m, vertex_positions),
{
    assert(mesh_geometry_input_spec(m, vertex_positions));
    assert forall|f: int|
        0 <= f < mesh_face_count_spec(m) implies #[trigger] mesh_face_coplanar_seed0_fixed_witness_spec(
            m,
            vertex_positions,
            f,
        ) by {
        assert(mesh_face_coplanar_spec(m, vertex_positions, f));
        lemma_mesh_face_coplanar_spec_implies_seed0_fixed_witness(m, vertex_positions, f);
    };
    assert(mesh_all_faces_coplanar_seed0_fixed_witness_spec(m, vertex_positions));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_coplanar_seed0_fixed_witness_implies_seed0_plane_contains_vertices(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
)
    requires
        mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f),
    ensures
        face_plane_contains_vertex_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ),
{
    let k = choose|k: int| mesh_face_coplanar_fixed_seed_witness_spec(m, vertex_positions, f, k, 0);
    assert(mesh_face_coplanar_fixed_seed_witness_spec(m, vertex_positions, f, k, 0));
    lemma_mesh_face_coplanar_fixed_seed_witness_implies_seed_plane_contains_vertices(
        m,
        vertex_positions,
        f,
        k,
        0,
    );
    assert(face_plane_contains_vertex_spec(
        m,
        vertex_positions,
        f,
        mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
        mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
    )) by {
        assert(0 <= f < mesh_face_count_spec(m));
        let kw = k;
        assert(mesh_face_plane_contains_vertex_witness_spec(
            m,
            vertex_positions,
            f,
            kw,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ));
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_all_faces_coplanar_seed0_fixed_witness_implies_all_faces_seed0_plane_contains_vertices(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
)
    requires
        mesh_all_faces_coplanar_seed0_fixed_witness_spec(m, vertex_positions),
    ensures
        mesh_all_faces_seed0_plane_contains_vertices_spec(m, vertex_positions),
{
    assert(mesh_geometry_input_spec(m, vertex_positions));
    assert forall|f: int|
        0 <= f < mesh_face_count_spec(m) implies #[trigger] face_plane_contains_vertex_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ) by {
        assert(mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f));
        lemma_mesh_face_coplanar_seed0_fixed_witness_implies_seed0_plane_contains_vertices(
            m,
            vertex_positions,
            f,
        );
    };
    assert(mesh_all_faces_seed0_plane_contains_vertices_spec(m, vertex_positions));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_seed_plane_contains_vertices_witness_implies_coplanar_fixed_seed_witness(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
    seed_i: int,
)
    requires
        mesh_face_plane_contains_vertex_witness_spec(
            m,
            vertex_positions,
            f,
            k,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, seed_i),
        ),
        0 <= seed_i,
        seed_i + 2 < k,
    ensures
        mesh_face_coplanar_fixed_seed_witness_spec(m, vertex_positions, f, k, seed_i),
{
    let p0 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i);
    let p1 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 1);
    let p2 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 2);
    let normal = mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i);
    let offset = mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, seed_i);
    let ba = p1.sub_spec(p0);
    let ca = p2.sub_spec(p0);

    assert(mesh_index_bounds_spec(m));
    assert(mesh_geometry_input_spec(m, vertex_positions));
    assert(0 <= f < mesh_face_count_spec(m));
    assert(mesh_face_cycle_witness_spec(m, f, k));
    assert(0 <= seed_i < k);
    assert(0 <= seed_i + 1 < k);
    assert(0 <= seed_i + 2 < k);

    assert forall|d: int|
        0 <= d < k implies #[trigger] vcad_math::orientation3::is_coplanar(
            p0,
            p1,
            p2,
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, d),
        ) by {
        let pd = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, d);
        let da = pd.sub_spec(p0);
        let plane_value = mesh_point_plane_value_relative_to_origin_spec(normal, offset, pd);
        let orient = vcad_math::orientation3::orient3d_spec(p0, p1, p2, pd);

        assert(mesh_point_satisfies_plane_relative_to_origin_spec(normal, offset, pd));
        assert(plane_value.signum() == 0);

        lemma_mesh_point_plane_value_relative_to_origin_matches_relative_dot(normal, p0, pd);
        assert(plane_value.eqv_spec(normal.dot_spec(da)));

        vcad_math::vec3::Vec3::lemma_dot_symmetric(normal, da);
        vcad_math::vec3::Vec3::lemma_dot_cross_cyclic(da, ba, ca);
        assert(da.dot_spec(ba.cross_spec(ca)).eqv_spec(orient));
        assert(da.dot_spec(normal).eqv_spec(orient));
        vcad_math::scalar::Scalar::lemma_eqv_transitive(
            normal.dot_spec(da),
            da.dot_spec(normal),
            orient,
        );
        assert(normal.dot_spec(da).eqv_spec(orient));
        vcad_math::scalar::Scalar::lemma_eqv_transitive(
            plane_value,
            normal.dot_spec(da),
            orient,
        );
        assert(plane_value.eqv_spec(orient));
        vcad_math::scalar::Scalar::lemma_eqv_signum(plane_value, orient);
        assert(orient.signum() == plane_value.signum());
        assert(orient.signum() == 0);
        assert(vcad_math::orientation3::is_coplanar(p0, p1, p2, pd));
    };

    assert(mesh_face_coplanar_fixed_seed_witness_spec(m, vertex_positions, f, k, seed_i));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_seed0_plane_contains_vertices_implies_seed0_fixed_witness(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
)
    requires
        face_plane_contains_vertex_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ),
    ensures
        mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f),
{
    let k = choose|k: int| mesh_face_plane_contains_vertex_witness_spec(
        m,
        vertex_positions,
        f,
        k,
        mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
        mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
    );
    assert(mesh_face_plane_contains_vertex_witness_spec(
        m,
        vertex_positions,
        f,
        k,
        mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
        mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
    ));
    assert(3 <= k);
    lemma_mesh_face_seed_plane_contains_vertices_witness_implies_coplanar_fixed_seed_witness(
        m,
        vertex_positions,
        f,
        k,
        0,
    );
    assert(mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f)) by {
        let kw = k;
        assert(mesh_face_coplanar_fixed_seed_witness_spec(m, vertex_positions, f, kw, 0));
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_seed0_fixed_witness_iff_seed0_plane_contains_vertices(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
)
    ensures
        mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f) == face_plane_contains_vertex_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ),
{
    assert(
        mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f) ==> face_plane_contains_vertex_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        )
    ) by {
        if mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f) {
            lemma_mesh_face_coplanar_seed0_fixed_witness_implies_seed0_plane_contains_vertices(
                m,
                vertex_positions,
                f,
            );
        }
    };
    assert(
        face_plane_contains_vertex_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ) ==> mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f)
    ) by {
        if face_plane_contains_vertex_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ) {
            lemma_mesh_face_seed0_plane_contains_vertices_implies_seed0_fixed_witness(
                m,
                vertex_positions,
                f,
            );
        }
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_all_faces_seed0_plane_contains_vertices_implies_all_faces_seed0_fixed_witness(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
)
    requires
        mesh_all_faces_seed0_plane_contains_vertices_spec(m, vertex_positions),
    ensures
        mesh_all_faces_coplanar_seed0_fixed_witness_spec(m, vertex_positions),
{
    assert(mesh_geometry_input_spec(m, vertex_positions));
    assert forall|f: int|
        0 <= f < mesh_face_count_spec(m) implies #[trigger] mesh_face_coplanar_seed0_fixed_witness_spec(
            m,
            vertex_positions,
            f,
        ) by {
        assert(face_plane_contains_vertex_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ));
        lemma_mesh_face_seed0_plane_contains_vertices_implies_seed0_fixed_witness(
            m,
            vertex_positions,
            f,
        );
    };
    assert(mesh_all_faces_coplanar_seed0_fixed_witness_spec(m, vertex_positions));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_all_faces_seed0_fixed_witness_iff_all_faces_seed0_plane_contains_vertices(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
)
    ensures
        mesh_all_faces_coplanar_seed0_fixed_witness_spec(m, vertex_positions)
            == mesh_all_faces_seed0_plane_contains_vertices_spec(m, vertex_positions),
{
    assert(
        mesh_all_faces_coplanar_seed0_fixed_witness_spec(m, vertex_positions)
            ==> mesh_all_faces_seed0_plane_contains_vertices_spec(m, vertex_positions)
    ) by {
        if mesh_all_faces_coplanar_seed0_fixed_witness_spec(m, vertex_positions) {
            lemma_mesh_all_faces_coplanar_seed0_fixed_witness_implies_all_faces_seed0_plane_contains_vertices(
                m,
                vertex_positions,
            );
        }
    };
    assert(
        mesh_all_faces_seed0_plane_contains_vertices_spec(m, vertex_positions)
            ==> mesh_all_faces_coplanar_seed0_fixed_witness_spec(m, vertex_positions)
    ) by {
        if mesh_all_faces_seed0_plane_contains_vertices_spec(m, vertex_positions) {
            lemma_mesh_all_faces_seed0_plane_contains_vertices_implies_all_faces_seed0_fixed_witness(
                m,
                vertex_positions,
            );
        }
    };
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_plane_contains_vertex_witness_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
    normal: vcad_math::vec3::Vec3,
    offset: vcad_math::scalar::Scalar,
) -> bool {
    &&& mesh_index_bounds_spec(m)
    &&& mesh_geometry_input_spec(m, vertex_positions)
    &&& 0 <= f < mesh_face_count_spec(m)
    &&& #[trigger] mesh_face_cycle_witness_spec(m, f, k)
    &&& forall|i: int|
        0 <= i < k ==> #[trigger] mesh_point_satisfies_plane_relative_to_origin_spec(
            normal,
            offset,
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, i),
        )
}

#[cfg(verus_keep_ghost)]
pub open spec fn face_plane_contains_vertex_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    normal: vcad_math::vec3::Vec3,
    offset: vcad_math::scalar::Scalar,
) -> bool {
    &&& 0 <= f < mesh_face_count_spec(m)
    &&& exists|k: int|
        #[trigger] mesh_face_plane_contains_vertex_witness_spec(
            m,
            vertex_positions,
            f,
            k,
            normal,
            offset,
        )
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_winding_orients_plane_normal_with_seed_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
    seed_i: int,
    normal: vcad_math::vec3::Vec3,
) -> bool {
    let seed_normal = mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i);
    &&& mesh_index_bounds_spec(m)
    &&& mesh_geometry_input_spec(m, vertex_positions)
    &&& 0 <= f < mesh_face_count_spec(m)
    &&& #[trigger] mesh_face_cycle_witness_spec(m, f, k)
    &&& 0 <= seed_i
    &&& seed_i + 2 < k
    &&& seed_normal.norm2_spec().signum() != 0
    &&& normal.norm2_spec().signum() != 0
    &&& normal.dot_spec(seed_normal).signum() == 1
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_face_oriented_plane_normal_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    normal: vcad_math::vec3::Vec3,
    offset: vcad_math::scalar::Scalar,
) -> bool {
    &&& 0 <= f < mesh_face_count_spec(m)
    &&& face_plane_contains_vertex_spec(m, vertex_positions, f, normal, offset)
    &&& exists|k: int, seed_i: int| #[trigger] mesh_face_winding_orients_plane_normal_with_seed_spec(
        m,
        vertex_positions,
        f,
        k,
        seed_i,
        normal,
    )
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_non_collinear_seed_normal_self_dot_sign_is_positive(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    seed_i: int,
)
    requires
        mesh_index_bounds_spec(m),
        mesh_geometry_input_spec(m, vertex_positions),
        0 <= f < mesh_face_count_spec(m),
        !mesh_points_collinear3_spec(
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 1),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 2),
        ),
    ensures
        mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i).dot_spec(
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i),
        ).signum() == 1,
{
    let p0 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i);
    let p1 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 1);
    let p2 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 2);
    let seed_normal = mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i);
    let n2 = seed_normal.norm2_spec();
    let z = vcad_math::scalar::Scalar::from_int_spec(0);

    assert(!mesh_points_collinear3_spec(p0, p1, p2));
    assert(seed_normal == p1.sub_spec(p0).cross_spec(p2.sub_spec(p0)));
    assert(seed_normal.norm2_spec().signum() != 0);
    vcad_math::vec3::Vec3::lemma_norm2_nonnegative(seed_normal);
    assert(z.le_spec(n2));
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(z.le_spec(n2) == (z.num * n2.denom() <= n2.num * z.denom()));
    assert(0 * n2.denom() == 0);
    assert(n2.num * 1 == n2.num);
    assert(0 <= n2.num);

    assert(n2.signum() != -1) by {
        if n2.signum() == -1 {
            assert(n2.num < 0) by {
                if n2.num > 0 {
                    assert(n2.signum() == 1);
                    assert(false);
                } else if n2.num < 0 {
                } else {
                    assert(n2.num == 0);
                    assert(n2.signum() == 0);
                    assert(false);
                }
            };
            assert(false);
        }
    };
    vcad_math::scalar::Scalar::lemma_signum_cases(n2);
    assert(n2.signum() == 1);
    assert(seed_normal.dot_spec(seed_normal) == n2);
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_coplanar_witness_non_collinear_seed_implies_oriented_seed_plane(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
    seed_i: int,
)
    requires
        mesh_face_coplanar_witness_spec(m, vertex_positions, f, k),
        0 <= seed_i,
        seed_i + 2 < k,
        !mesh_points_collinear3_spec(
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 1),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i + 2),
        ),
    ensures
        mesh_face_oriented_plane_normal_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, seed_i),
        ),
{
    let normal = mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i);
    let offset = mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, seed_i);

    lemma_mesh_face_coplanar_witness_seed_plane_contains_vertices(m, vertex_positions, f, k, seed_i);
    lemma_mesh_non_collinear_seed_normal_self_dot_sign_is_positive(m, vertex_positions, f, seed_i);

    assert(face_plane_contains_vertex_spec(m, vertex_positions, f, normal, offset)) by {
        let kw = k;
        assert(mesh_face_plane_contains_vertex_witness_spec(
            m,
            vertex_positions,
            f,
            kw,
            normal,
            offset,
        ));
    };

    assert(mesh_face_winding_orients_plane_normal_with_seed_spec(
        m,
        vertex_positions,
        f,
        k,
        seed_i,
        normal,
    )) by {
        assert(mesh_index_bounds_spec(m));
        assert(mesh_geometry_input_spec(m, vertex_positions));
        assert(0 <= f < mesh_face_count_spec(m));
        assert(mesh_face_cycle_witness_spec(m, f, k));
        assert(0 <= seed_i);
        assert(seed_i + 2 < k);
        assert(normal.norm2_spec().signum() != 0);
        assert(normal.dot_spec(normal).signum() == 1);
    };

    assert(mesh_face_oriented_plane_normal_spec(m, vertex_positions, f, normal, offset)) by {
        assert(0 <= f < mesh_face_count_spec(m));
        assert(face_plane_contains_vertex_spec(m, vertex_positions, f, normal, offset));
        assert(exists|kw: int, si: int| #[trigger] mesh_face_winding_orients_plane_normal_with_seed_spec(
            m,
            vertex_positions,
            f,
            kw,
            si,
            normal,
        )) by {
            let kw = k;
            let si = seed_i;
            assert(mesh_face_winding_orients_plane_normal_with_seed_spec(
                m,
                vertex_positions,
                f,
                kw,
                si,
                normal,
            ));
        };
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_coplanar_fixed_seed_witness_non_collinear_seed_implies_oriented_seed_plane(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
    k: int,
    seed_i: int,
)
    requires
        mesh_face_coplanar_fixed_seed_witness_spec(m, vertex_positions, f, k, seed_i),
        !mesh_points_collinear3_spec(
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, seed_i),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(
                m,
                vertex_positions,
                f,
                seed_i + 1,
            ),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(
                m,
                vertex_positions,
                f,
                seed_i + 2,
            ),
        ),
    ensures
        mesh_face_oriented_plane_normal_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, seed_i),
        ),
{
    let normal = mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i);
    let offset = mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, seed_i);

    lemma_mesh_face_coplanar_fixed_seed_witness_implies_seed_plane_contains_vertices(
        m,
        vertex_positions,
        f,
        k,
        seed_i,
    );
    lemma_mesh_non_collinear_seed_normal_self_dot_sign_is_positive(m, vertex_positions, f, seed_i);

    assert(face_plane_contains_vertex_spec(m, vertex_positions, f, normal, offset)) by {
        let kw = k;
        assert(mesh_face_plane_contains_vertex_witness_spec(
            m,
            vertex_positions,
            f,
            kw,
            normal,
            offset,
        ));
    };

    assert(mesh_face_winding_orients_plane_normal_with_seed_spec(
        m,
        vertex_positions,
        f,
        k,
        seed_i,
        normal,
    )) by {
        let seed_normal = mesh_face_seed_plane_normal_spec(m, vertex_positions, f, seed_i);
        assert(mesh_index_bounds_spec(m));
        assert(mesh_geometry_input_spec(m, vertex_positions));
        assert(0 <= f < mesh_face_count_spec(m));
        assert(mesh_face_cycle_witness_spec(m, f, k));
        assert(0 <= seed_i);
        assert(seed_i + 2 < k);
        assert(seed_normal == normal);
        assert(seed_normal.dot_spec(seed_normal).signum() == 1);
        assert(seed_normal.norm2_spec().signum() != 0);
        assert(normal.norm2_spec().signum() != 0);
        assert(normal.dot_spec(seed_normal).signum() == 1);
    };

    assert(mesh_face_oriented_plane_normal_spec(m, vertex_positions, f, normal, offset)) by {
        assert(0 <= f < mesh_face_count_spec(m));
        assert(face_plane_contains_vertex_spec(m, vertex_positions, f, normal, offset));
        assert(exists|kw: int, si: int| #[trigger] mesh_face_winding_orients_plane_normal_with_seed_spec(
            m,
            vertex_positions,
            f,
            kw,
            si,
            normal,
        )) by {
            let kw = k;
            let si = seed_i;
            assert(mesh_face_winding_orients_plane_normal_with_seed_spec(
                m,
                vertex_positions,
                f,
                kw,
                si,
                normal,
            ));
        };
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_coplanar_seed0_fixed_witness_non_collinear_seed0_implies_oriented_seed0_plane(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
)
    requires
        mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f),
        !mesh_points_collinear3_spec(
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 0),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 1),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 2),
        ),
    ensures
        mesh_face_oriented_plane_normal_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ),
{
    let k = choose|k: int| mesh_face_coplanar_fixed_seed_witness_spec(m, vertex_positions, f, k, 0);
    assert(mesh_face_coplanar_fixed_seed_witness_spec(m, vertex_positions, f, k, 0));
    lemma_mesh_face_coplanar_fixed_seed_witness_non_collinear_seed_implies_oriented_seed_plane(
        m,
        vertex_positions,
        f,
        k,
        0,
    );
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_coplanar_spec_and_seed0_non_collinear_imply_oriented_seed0_plane(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
)
    requires
        mesh_face_coplanar_spec(m, vertex_positions, f),
        !mesh_points_collinear3_spec(
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 0),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 1),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 2),
        ),
    ensures
        mesh_face_oriented_plane_normal_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ),
{
    lemma_mesh_face_coplanar_spec_implies_seed0_fixed_witness(m, vertex_positions, f);
    assert(mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f));
    lemma_mesh_face_coplanar_seed0_fixed_witness_non_collinear_seed0_implies_oriented_seed0_plane(
        m,
        vertex_positions,
        f,
    );
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_all_faces_coplanar_spec_and_seed0_non_collinear_imply_all_faces_oriented_seed0_planes(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
)
    requires
        mesh_all_faces_coplanar_spec(m, vertex_positions),
        mesh_all_faces_seed0_corner_non_collinear_spec(m, vertex_positions),
    ensures
        mesh_all_faces_oriented_seed0_planes_spec(m, vertex_positions),
{
    assert(mesh_geometry_input_spec(m, vertex_positions));
    assert forall|f: int|
        0 <= f < mesh_face_count_spec(m)
            implies #[trigger] mesh_face_oriented_plane_normal_spec(
                m,
                vertex_positions,
                f,
                mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
                mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
            ) by {
        assert(mesh_face_coplanar_spec(m, vertex_positions, f));
        assert(!mesh_points_collinear3_spec(
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 0),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 1),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 2),
        ));
        lemma_mesh_face_coplanar_spec_and_seed0_non_collinear_imply_oriented_seed0_plane(
            m,
            vertex_positions,
            f,
        );
    };
    assert(mesh_all_faces_oriented_seed0_planes_spec(m, vertex_positions));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_all_faces_coplanar_seed0_fixed_witness_and_seed0_non_collinear_imply_all_faces_oriented_seed0_planes(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
)
    requires
        mesh_all_faces_coplanar_seed0_fixed_witness_spec(m, vertex_positions),
        mesh_all_faces_seed0_corner_non_collinear_spec(m, vertex_positions),
    ensures
        mesh_all_faces_oriented_seed0_planes_spec(m, vertex_positions),
{
    assert(mesh_geometry_input_spec(m, vertex_positions));
    assert forall|f: int|
        0 <= f < mesh_face_count_spec(m)
            implies #[trigger] mesh_face_oriented_plane_normal_spec(
                m,
                vertex_positions,
                f,
                mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
                mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
            ) by {
        assert(mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f));
        assert(!mesh_points_collinear3_spec(
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 0),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 1),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 2),
        ));
        lemma_mesh_face_coplanar_seed0_fixed_witness_non_collinear_seed0_implies_oriented_seed0_plane(
            m,
            vertex_positions,
            f,
        );
    };
    assert(mesh_all_faces_oriented_seed0_planes_spec(m, vertex_positions));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_oriented_seed0_plane_implies_seed0_plane_contains_vertices(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
)
    requires
        mesh_face_oriented_plane_normal_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ),
    ensures
        face_plane_contains_vertex_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ),
{
    assert(face_plane_contains_vertex_spec(
        m,
        vertex_positions,
        f,
        mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
        mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
    )) by {
        assert(mesh_face_oriented_plane_normal_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ));
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_oriented_seed0_plane_implies_seed0_non_collinear(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
)
    requires
        mesh_face_oriented_plane_normal_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ),
    ensures
        !mesh_points_collinear3_spec(
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 0),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 1),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 2),
        ),
{
    let normal = mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0);
    let p0 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 0);
    let p1 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 1);
    let p2 = mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 2);

    let (k, seed_i) = choose|k: int, seed_i: int| #[trigger]
        mesh_face_winding_orients_plane_normal_with_seed_spec(
        m,
        vertex_positions,
        f,
        k,
        seed_i,
        normal,
    );
    assert(mesh_face_winding_orients_plane_normal_with_seed_spec(
        m,
        vertex_positions,
        f,
        k,
        seed_i,
        normal,
    ));
    assert(normal.norm2_spec().signum() != 0);

    assert(!mesh_points_collinear3_spec(p0, p1, p2)) by {
        if mesh_points_collinear3_spec(p0, p1, p2) {
            assert(normal == p1.sub_spec(p0).cross_spec(p2.sub_spec(p0)));
            assert(normal.norm2_spec().signum() == 0);
            assert(false);
        }
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_oriented_seed0_plane_iff_seed0_fixed_witness_and_seed0_non_collinear(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
)
    ensures
        mesh_face_oriented_plane_normal_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ) == (
            mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f)
                && !mesh_points_collinear3_spec(
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 0),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 1),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 2),
                )
        ),
{
    assert(
        mesh_face_oriented_plane_normal_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ) ==> (
            mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f)
                && !mesh_points_collinear3_spec(
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 0),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 1),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 2),
                )
        )
    ) by {
        if mesh_face_oriented_plane_normal_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ) {
            lemma_mesh_face_oriented_seed0_plane_implies_seed0_fixed_witness(m, vertex_positions, f);
            lemma_mesh_face_oriented_seed0_plane_implies_seed0_non_collinear(m, vertex_positions, f);
            assert(
                mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f)
                    && !mesh_points_collinear3_spec(
                        mesh_face_cycle_vertex_position_or_default_at_int_spec(
                            m,
                            vertex_positions,
                            f,
                            0,
                        ),
                        mesh_face_cycle_vertex_position_or_default_at_int_spec(
                            m,
                            vertex_positions,
                            f,
                            1,
                        ),
                        mesh_face_cycle_vertex_position_or_default_at_int_spec(
                            m,
                            vertex_positions,
                            f,
                            2,
                        ),
                    )
            );
        }
    };
    assert(
        (
            mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f)
                && !mesh_points_collinear3_spec(
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 0),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 1),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 2),
                )
        ) ==> mesh_face_oriented_plane_normal_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        )
    ) by {
        if
            mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f)
                && !mesh_points_collinear3_spec(
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 0),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 1),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 2),
                )
        {
            lemma_mesh_face_coplanar_seed0_fixed_witness_non_collinear_seed0_implies_oriented_seed0_plane(
                m,
                vertex_positions,
                f,
            );
            assert(mesh_face_oriented_plane_normal_spec(
                m,
                vertex_positions,
                f,
                mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
                mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
            ));
        }
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_oriented_seed0_plane_iff_seed0_plane_contains_vertices_and_seed0_non_collinear(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
)
    ensures
        mesh_face_oriented_plane_normal_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ) == (
            face_plane_contains_vertex_spec(
                m,
                vertex_positions,
                f,
                mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
                mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
            ) && !mesh_points_collinear3_spec(
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 0),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 1),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 2),
            )
        ),
{
    assert(
        mesh_face_oriented_plane_normal_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ) ==> (
            face_plane_contains_vertex_spec(
                m,
                vertex_positions,
                f,
                mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
                mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
            ) && !mesh_points_collinear3_spec(
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 0),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 1),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 2),
            )
        )
    ) by {
        if mesh_face_oriented_plane_normal_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ) {
            lemma_mesh_face_oriented_seed0_plane_implies_seed0_plane_contains_vertices(
                m,
                vertex_positions,
                f,
            );
            lemma_mesh_face_oriented_seed0_plane_implies_seed0_non_collinear(m, vertex_positions, f);
            assert(
                face_plane_contains_vertex_spec(
                    m,
                    vertex_positions,
                    f,
                    mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
                    mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
                ) && !mesh_points_collinear3_spec(
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m,
                        vertex_positions,
                        f,
                        0,
                    ),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m,
                        vertex_positions,
                        f,
                        1,
                    ),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m,
                        vertex_positions,
                        f,
                        2,
                    ),
                )
            );
        }
    };
    assert(
        (
            face_plane_contains_vertex_spec(
                m,
                vertex_positions,
                f,
                mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
                mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
            ) && !mesh_points_collinear3_spec(
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 0),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 1),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 2),
            )
        ) ==> mesh_face_oriented_plane_normal_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        )
    ) by {
        if
            face_plane_contains_vertex_spec(
                m,
                vertex_positions,
                f,
                mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
                mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
            ) && !mesh_points_collinear3_spec(
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 0),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 1),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 2),
            )
        {
            lemma_mesh_face_seed0_plane_contains_vertices_implies_seed0_fixed_witness(
                m,
                vertex_positions,
                f,
            );
            assert(mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f));
            lemma_mesh_face_coplanar_seed0_fixed_witness_non_collinear_seed0_implies_oriented_seed0_plane(
                m,
                vertex_positions,
                f,
            );
            assert(mesh_face_oriented_plane_normal_spec(
                m,
                vertex_positions,
                f,
                mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
                mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
            ));
        }
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_oriented_seed0_plane_implies_seed0_fixed_witness(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    f: int,
)
    requires
        mesh_face_oriented_plane_normal_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ),
    ensures
        mesh_face_coplanar_seed0_fixed_witness_spec(m, vertex_positions, f),
{
    lemma_mesh_face_oriented_seed0_plane_implies_seed0_plane_contains_vertices(m, vertex_positions, f);
    lemma_mesh_face_seed0_plane_contains_vertices_implies_seed0_fixed_witness(
        m,
        vertex_positions,
        f,
    );
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_all_faces_oriented_seed0_planes_imply_all_faces_seed0_fixed_witness(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
)
    requires
        mesh_all_faces_oriented_seed0_planes_spec(m, vertex_positions),
    ensures
        mesh_all_faces_coplanar_seed0_fixed_witness_spec(m, vertex_positions),
{
    assert(mesh_geometry_input_spec(m, vertex_positions));
    assert forall|f: int|
        0 <= f < mesh_face_count_spec(m) implies #[trigger] mesh_face_coplanar_seed0_fixed_witness_spec(
            m,
            vertex_positions,
            f,
        ) by {
        assert(mesh_face_oriented_plane_normal_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ));
        lemma_mesh_face_oriented_seed0_plane_implies_seed0_fixed_witness(m, vertex_positions, f);
    };
    assert(mesh_all_faces_coplanar_seed0_fixed_witness_spec(m, vertex_positions));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_all_faces_oriented_seed0_planes_and_index_bounds_and_face_cycles_imply_all_faces_seed0_corner_non_collinear(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
)
    requires
        mesh_all_faces_oriented_seed0_planes_spec(m, vertex_positions),
        mesh_index_bounds_spec(m),
        mesh_face_next_cycles_spec(m),
    ensures
        mesh_all_faces_seed0_corner_non_collinear_spec(m, vertex_positions),
{
    assert(mesh_geometry_input_spec(m, vertex_positions));
    assert forall|f: int|
        0 <= f < mesh_face_count_spec(m) implies !mesh_points_collinear3_spec(
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 0),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 1),
            mesh_face_cycle_vertex_position_or_default_at_int_spec(m, vertex_positions, f, 2),
        ) by {
        assert(mesh_face_oriented_plane_normal_spec(
            m,
            vertex_positions,
            f,
            mesh_face_seed_plane_normal_spec(m, vertex_positions, f, 0),
            mesh_face_seed_plane_offset_relative_to_origin_spec(m, vertex_positions, f, 0),
        ));
        lemma_mesh_face_oriented_seed0_plane_implies_seed0_non_collinear(m, vertex_positions, f);
    };
    assert(mesh_all_faces_seed0_corner_non_collinear_spec(m, vertex_positions));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_all_faces_oriented_seed0_planes_and_index_bounds_and_face_cycles_iff_seed0_plane_contains_vertices_and_seed0_non_collinear(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
)
    requires
        mesh_index_bounds_spec(m),
        mesh_face_next_cycles_spec(m),
    ensures
        mesh_all_faces_oriented_seed0_planes_spec(m, vertex_positions) == (
            mesh_all_faces_seed0_plane_contains_vertices_spec(m, vertex_positions)
                && mesh_all_faces_seed0_corner_non_collinear_spec(m, vertex_positions)
        ),
{
    assert(
        mesh_all_faces_oriented_seed0_planes_spec(m, vertex_positions) ==> (
            mesh_all_faces_seed0_plane_contains_vertices_spec(m, vertex_positions)
                && mesh_all_faces_seed0_corner_non_collinear_spec(m, vertex_positions)
        )
    ) by {
        if mesh_all_faces_oriented_seed0_planes_spec(m, vertex_positions) {
            lemma_mesh_all_faces_oriented_seed0_planes_imply_all_faces_seed0_fixed_witness(
                m,
                vertex_positions,
            );
            lemma_mesh_all_faces_coplanar_seed0_fixed_witness_implies_all_faces_seed0_plane_contains_vertices(
                m,
                vertex_positions,
            );
            lemma_mesh_all_faces_oriented_seed0_planes_and_index_bounds_and_face_cycles_imply_all_faces_seed0_corner_non_collinear(
                m,
                vertex_positions,
            );
            assert(
                mesh_all_faces_seed0_plane_contains_vertices_spec(m, vertex_positions)
                    && mesh_all_faces_seed0_corner_non_collinear_spec(m, vertex_positions)
            );
        }
    };
    assert(
        (
            mesh_all_faces_seed0_plane_contains_vertices_spec(m, vertex_positions)
                && mesh_all_faces_seed0_corner_non_collinear_spec(m, vertex_positions)
        ) ==> mesh_all_faces_oriented_seed0_planes_spec(m, vertex_positions)
    ) by {
        if
            mesh_all_faces_seed0_plane_contains_vertices_spec(m, vertex_positions)
                && mesh_all_faces_seed0_corner_non_collinear_spec(m, vertex_positions)
        {
            lemma_mesh_all_faces_seed0_plane_contains_vertices_implies_all_faces_seed0_fixed_witness(
                m,
                vertex_positions,
            );
            lemma_mesh_all_faces_coplanar_seed0_fixed_witness_and_seed0_non_collinear_imply_all_faces_oriented_seed0_planes(
                m,
                vertex_positions,
            );
            assert(mesh_all_faces_oriented_seed0_planes_spec(m, vertex_positions));
        }
    };
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_runtime_face_oriented_plane_normal_spec(
    m: &Mesh,
    f: int,
    normal: vcad_math::vec3::Vec3,
    offset: vcad_math::scalar::Scalar,
) -> bool {
    mesh_face_oriented_plane_normal_spec(m@, mesh_runtime_vertex_positions_spec(m), f, normal, offset)
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_runtime_face_coplanar_spec(m: &Mesh, f: int) -> bool {
    mesh_face_coplanar_spec(m@, mesh_runtime_vertex_positions_spec(m), f)
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_runtime_all_faces_coplanar_spec(m: &Mesh) -> bool {
    mesh_all_faces_coplanar_spec(m@, mesh_runtime_vertex_positions_spec(m))
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_runtime_face_coplanar_seed0_fixed_witness_spec(m: &Mesh, f: int) -> bool {
    mesh_face_coplanar_seed0_fixed_witness_spec(m@, mesh_runtime_vertex_positions_spec(m), f)
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_runtime_face_seed0_corner_non_collinear_spec(m: &Mesh, f: int) -> bool {
    !mesh_points_collinear3_spec(
        mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m@,
            mesh_runtime_vertex_positions_spec(m),
            f,
            0,
        ),
        mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m@,
            mesh_runtime_vertex_positions_spec(m),
            f,
            1,
        ),
        mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m@,
            mesh_runtime_vertex_positions_spec(m),
            f,
            2,
        ),
    )
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_runtime_face_seed0_plane_contains_vertices_spec(m: &Mesh, f: int) -> bool {
    face_plane_contains_vertex_spec(
        m@,
        mesh_runtime_vertex_positions_spec(m),
        f,
        mesh_face_seed_plane_normal_spec(m@, mesh_runtime_vertex_positions_spec(m), f, 0),
        mesh_face_seed_plane_offset_relative_to_origin_spec(
            m@,
            mesh_runtime_vertex_positions_spec(m),
            f,
            0,
        ),
    )
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m: &Mesh) -> bool {
    mesh_all_faces_coplanar_seed0_fixed_witness_spec(m@, mesh_runtime_vertex_positions_spec(m))
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m: &Mesh) -> bool {
    mesh_all_faces_seed0_corner_non_collinear_spec(m@, mesh_runtime_vertex_positions_spec(m))
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m: &Mesh) -> bool {
    mesh_all_faces_seed0_plane_contains_vertices_spec(m@, mesh_runtime_vertex_positions_spec(m))
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_runtime_all_faces_oriented_seed0_planes_spec(m: &Mesh) -> bool {
    mesh_all_faces_oriented_seed0_planes_spec(m@, mesh_runtime_vertex_positions_spec(m))
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_runtime_face_oriented_seed0_plane_spec(m: &Mesh, f: int) -> bool {
    mesh_face_oriented_plane_normal_spec(
        m@,
        mesh_runtime_vertex_positions_spec(m),
        f,
        mesh_face_seed_plane_normal_spec(m@, mesh_runtime_vertex_positions_spec(m), f, 0),
        mesh_face_seed_plane_offset_relative_to_origin_spec(
            m@,
            mesh_runtime_vertex_positions_spec(m),
            f,
            0,
        ),
    )
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_runtime_face_oriented_seed0_plane_iff_seed0_fixed_witness_and_seed0_non_collinear(
    m: &Mesh,
    f: int,
)
    ensures
        mesh_runtime_face_oriented_seed0_plane_spec(m, f) == (
            mesh_runtime_face_coplanar_seed0_fixed_witness_spec(m, f)
                && mesh_runtime_face_seed0_corner_non_collinear_spec(m, f)
        ),
{
    lemma_mesh_face_oriented_seed0_plane_iff_seed0_fixed_witness_and_seed0_non_collinear(
        m@,
        mesh_runtime_vertex_positions_spec(m),
        f,
    );
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_runtime_face_oriented_seed0_plane_iff_seed0_plane_contains_vertices_and_seed0_non_collinear(
    m: &Mesh,
    f: int,
)
    ensures
        mesh_runtime_face_oriented_seed0_plane_spec(m, f) == (
            mesh_runtime_face_seed0_plane_contains_vertices_spec(m, f)
                && mesh_runtime_face_seed0_corner_non_collinear_spec(m, f)
        ),
{
    lemma_mesh_face_oriented_seed0_plane_iff_seed0_plane_contains_vertices_and_seed0_non_collinear(
        m@,
        mesh_runtime_vertex_positions_spec(m),
        f,
    );
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_runtime_all_faces_coplanar_spec_and_seed0_non_collinear_imply_all_faces_oriented_seed0_planes(
    m: &Mesh,
)
    requires
        mesh_runtime_all_faces_coplanar_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
    ensures
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    lemma_mesh_all_faces_coplanar_spec_and_seed0_non_collinear_imply_all_faces_oriented_seed0_planes(
        m@,
        mesh_runtime_vertex_positions_spec(m),
    );
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_runtime_all_faces_coplanar_spec_implies_all_faces_seed0_fixed_witness(
    m: &Mesh,
)
    requires
        mesh_runtime_all_faces_coplanar_spec(m),
    ensures
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
{
    lemma_mesh_all_faces_coplanar_spec_implies_all_faces_seed0_fixed_witness(
        m@,
        mesh_runtime_vertex_positions_spec(m),
    );
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_runtime_all_faces_coplanar_spec_and_face_next_cycles_witness_imply_all_faces_seed0_fixed_witness_at_cycle_lens(
    m: &Mesh,
    face_cycle_lens: Seq<usize>,
)
    requires
        mesh_runtime_all_faces_coplanar_spec(m),
        mesh_face_next_cycles_witness_spec(m@, face_cycle_lens),
    ensures
        forall|f: int|
            0 <= f < mesh_face_count_spec(m@)
                ==> #[trigger] mesh_face_coplanar_fixed_seed_witness_spec(
                    m@,
                    mesh_runtime_vertex_positions_spec(m),
                    f,
                    face_cycle_lens[f] as int,
                    0,
                ),
{
    assert(mesh_runtime_all_faces_coplanar_spec(m));
    assert(mesh_face_next_cycles_witness_spec(m@, face_cycle_lens));
    assert(mesh_geometry_input_spec(m@, mesh_runtime_vertex_positions_spec(m)));
    assert(face_cycle_lens.len() == mesh_face_count_spec(m@));

    assert forall|f: int|
        0 <= f < mesh_face_count_spec(m@)
            implies #[trigger] mesh_face_coplanar_fixed_seed_witness_spec(
                m@,
                mesh_runtime_vertex_positions_spec(m),
                f,
                face_cycle_lens[f] as int,
                0,
            ) by {
        assert(mesh_face_cycle_witness_spec(m@, f, face_cycle_lens[f] as int));
        assert(mesh_runtime_face_coplanar_spec(m, f));
        lemma_mesh_face_coplanar_spec_and_face_cycle_witness_imply_seed0_fixed_witness_at_cycle_len(
            m@,
            mesh_runtime_vertex_positions_spec(m),
            f,
            face_cycle_lens[f] as int,
        );
        assert(mesh_face_coplanar_fixed_seed_witness_spec(
            m@,
            mesh_runtime_vertex_positions_spec(m),
            f,
            face_cycle_lens[f] as int,
            0,
        ));
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_and_face_next_cycles_witness_imply_all_faces_seed0_fixed_witness_at_cycle_lens(
    m: &Mesh,
    face_cycle_lens: Seq<usize>,
)
    requires
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_face_next_cycles_witness_spec(m@, face_cycle_lens),
    ensures
        forall|f: int|
            0 <= f < mesh_face_count_spec(m@)
                ==> #[trigger] mesh_face_coplanar_fixed_seed_witness_spec(
                    m@,
                    mesh_runtime_vertex_positions_spec(m),
                    f,
                    face_cycle_lens[f] as int,
                    0,
                ),
{
    lemma_mesh_all_faces_coplanar_seed0_fixed_witness_and_face_next_cycles_witness_imply_all_faces_seed0_fixed_witness_at_cycle_lens(
        m@,
        mesh_runtime_vertex_positions_spec(m),
        face_cycle_lens,
    );
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_implies_all_faces_seed0_plane_contains_vertices(
    m: &Mesh,
)
    requires
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
    ensures
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
{
    lemma_mesh_all_faces_coplanar_seed0_fixed_witness_implies_all_faces_seed0_plane_contains_vertices(
        m@,
        mesh_runtime_vertex_positions_spec(m),
    );
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_runtime_all_faces_seed0_plane_contains_vertices_implies_all_faces_seed0_fixed_witness(
    m: &Mesh,
)
    requires
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
    ensures
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
{
    lemma_mesh_all_faces_seed0_plane_contains_vertices_implies_all_faces_seed0_fixed_witness(
        m@,
        mesh_runtime_vertex_positions_spec(m),
    );
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_runtime_all_faces_seed0_fixed_witness_iff_all_faces_seed0_plane_contains_vertices(
    m: &Mesh,
)
    ensures
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m)
            == mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
{
    assert(
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m)
            ==> mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m)
    ) by {
        if mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m) {
            lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_implies_all_faces_seed0_plane_contains_vertices(
                m,
            );
        }
    };
    assert(
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m)
            ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m)
    ) by {
        if mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m) {
            lemma_mesh_runtime_all_faces_seed0_plane_contains_vertices_implies_all_faces_seed0_fixed_witness(
                m,
            );
        }
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_runtime_all_faces_oriented_seed0_planes_imply_all_faces_seed0_fixed_witness(
    m: &Mesh,
)
    requires
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
    ensures
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
{
    lemma_mesh_all_faces_oriented_seed0_planes_imply_all_faces_seed0_fixed_witness(
        m@,
        mesh_runtime_vertex_positions_spec(m),
    );
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_runtime_all_faces_oriented_seed0_planes_and_index_bounds_and_face_cycles_imply_all_faces_seed0_corner_non_collinear(
    m: &Mesh,
)
    requires
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
        mesh_index_bounds_spec(m@),
        mesh_face_next_cycles_spec(m@),
    ensures
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
{
    lemma_mesh_all_faces_oriented_seed0_planes_and_index_bounds_and_face_cycles_imply_all_faces_seed0_corner_non_collinear(
        m@,
        mesh_runtime_vertex_positions_spec(m),
    );
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_and_seed0_non_collinear_imply_all_faces_oriented_seed0_planes(
    m: &Mesh,
)
    requires
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
    ensures
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    lemma_mesh_all_faces_coplanar_seed0_fixed_witness_and_seed0_non_collinear_imply_all_faces_oriented_seed0_planes(
        m@,
        mesh_runtime_vertex_positions_spec(m),
    );
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_runtime_all_faces_oriented_seed0_planes_and_index_bounds_and_face_cycles_iff_seed0_fixed_witness_and_seed0_non_collinear(
    m: &Mesh,
)
    requires
        mesh_index_bounds_spec(m@),
        mesh_face_next_cycles_spec(m@),
    ensures
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m) == (
            mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m)
                && mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
        ),
{
    assert(
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m) ==> (
            mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m)
                && mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
        )
    ) by {
        if mesh_runtime_all_faces_oriented_seed0_planes_spec(m) {
            lemma_mesh_runtime_all_faces_oriented_seed0_planes_imply_all_faces_seed0_fixed_witness(
                m,
            );
            lemma_mesh_runtime_all_faces_oriented_seed0_planes_and_index_bounds_and_face_cycles_imply_all_faces_seed0_corner_non_collinear(
                m,
            );
            assert(
                mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m)
                    && mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
            );
        }
    };
    assert(
        (
            mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m)
                && mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
        ) ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m)
    ) by {
        if
            mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m)
                && mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
        {
            lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_and_seed0_non_collinear_imply_all_faces_oriented_seed0_planes(
                m,
            );
            assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
        }
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_runtime_all_faces_oriented_seed0_planes_and_index_bounds_and_face_cycles_iff_seed0_plane_contains_vertices_and_seed0_non_collinear(
    m: &Mesh,
)
    requires
        mesh_index_bounds_spec(m@),
        mesh_face_next_cycles_spec(m@),
    ensures
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m) == (
            mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m)
                && mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
        ),
{
    lemma_mesh_all_faces_oriented_seed0_planes_and_index_bounds_and_face_cycles_iff_seed0_plane_contains_vertices_and_seed0_non_collinear(
        m@,
        mesh_runtime_vertex_positions_spec(m),
    );
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

#[cfg(verus_keep_ghost)]
pub open spec fn kernel_mesh_runtime_geometry_bridge_spec(
    km: &kernels::KernelMesh,
    m: &Mesh,
) -> bool {
    &&& kernel_mesh_matches_mesh_model_spec(km, m@)
    &&& mesh_runtime_geometry_bridge_spec(m)
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
