#![cfg(feature = "verus-proofs")]

use crate::halfedge_mesh::{Edge, Face, HalfEdge, Mesh, MeshBuildError, Vertex};
use crate::verified_checker_kernels as kernels;
use vcad_math::runtime_point3::RuntimePoint3;
#[cfg(verus_keep_ghost)]
use vcad_math::scalar::Scalar;
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

#[verifier::external_body]
fn ex_from_face_cycles_constructive_abort() -> ! {
    std::process::abort();
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

proof fn lemma_usize_loop_exit_eq(idx: usize, bound: usize)
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

pub proof fn lemma_mesh_next_or_self_in_bounds(m: MeshModel, h: int)
    requires
        mesh_index_bounds_spec(m),
        0 <= h < mesh_half_edge_count_spec(m),
    ensures
        0 <= mesh_next_or_self_spec(m, h) < mesh_half_edge_count_spec(m),
{
    assert(mesh_next_or_self_spec(m, h) == m.half_edges[h].next);
    assert(0 <= m.half_edges[h].next < mesh_half_edge_count_spec(m));
}

pub proof fn lemma_mesh_next_iter_in_bounds(m: MeshModel, h: int, n: nat)
    requires
        mesh_index_bounds_spec(m),
        0 <= h < mesh_half_edge_count_spec(m),
    ensures
        0 <= mesh_next_iter_spec(m, h, n) < mesh_half_edge_count_spec(m),
    decreases n,
{
    if n == 0 {
    } else {
        let prev = (n - 1) as nat;
        lemma_mesh_next_iter_in_bounds(m, h, prev);
        lemma_mesh_next_or_self_in_bounds(m, mesh_next_iter_spec(m, h, prev));
    }
}

pub proof fn lemma_face_bridge_witness_implies_face_cycle_coverage(
    m: MeshModel,
    face_cycle_lens: Seq<usize>,
    covered: Seq<bool>,
    f: int,
)
    requires
        mesh_index_bounds_spec(m),
        mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_witness_spec(
            m,
            face_cycle_lens,
            covered,
        ),
        0 <= f < mesh_face_count_spec(m),
    ensures
        forall|h: int|
            0 <= h < mesh_half_edge_count_spec(m) && #[trigger] m.half_edges[h].face == f
                ==> exists|i: int| {
                    &&& 0 <= i < face_cycle_lens[f] as int
                    &&& #[trigger] mesh_next_iter_spec(m, m.face_half_edges[f], i as nat) == h
                },
{
    let hcnt = mesh_half_edge_count_spec(m);
    let k = face_cycle_lens[f] as int;
    assert(forall|h: int|
        0 <= h < hcnt && #[trigger] m.half_edges[h].face == f ==> exists|i: int| {
            &&& 0 <= i < k
            &&& #[trigger] mesh_next_iter_spec(m, m.face_half_edges[f], i as nat) == h
        }) by {
        assert forall|h: int|
            0 <= h < hcnt && #[trigger] m.half_edges[h].face == f implies exists|i: int| {
                &&& 0 <= i < k
                &&& #[trigger] mesh_next_iter_spec(m, m.face_half_edges[f], i as nat) == h
            } by {
            assert(covered[h]);
            let (fw, iw) = choose|fw: int, iw: int| {
                &&& 0 <= fw < mesh_face_count_spec(m)
                &&& 0 <= iw < face_cycle_lens[fw] as int
                &&& #[trigger] mesh_next_iter_spec(m, m.face_half_edges[fw], iw as nat) == h
            };
            assert(0 <= fw < mesh_face_count_spec(m));
            assert(0 <= iw < face_cycle_lens[fw] as int);
            assert(mesh_face_representative_cycle_kernel_bridge_witness_spec(
                m,
                fw,
                face_cycle_lens[fw] as int,
            ));
            assert(#[trigger] m.half_edges[mesh_next_iter_spec(
                m,
                m.face_half_edges[fw],
                iw as nat,
            )].face == fw);
            assert(mesh_next_iter_spec(m, m.face_half_edges[fw], iw as nat) == h);
            assert(m.half_edges[h].face == fw);
            assert(m.half_edges[h].face == f);
            assert(fw == f);
            assert(0 <= iw < k);
            assert(exists|i: int| {
                &&& 0 <= i < k
                &&& #[trigger] mesh_next_iter_spec(m, m.face_half_edges[f], i as nat) == h
            }) by {
                let i = iw;
                assert(0 <= i < k);
                assert(mesh_next_iter_spec(m, m.face_half_edges[f], i as nat) == h);
            };
        };
    };
}

pub proof fn lemma_face_bridge_witness_implies_face_cycle_witness(
    m: MeshModel,
    face_cycle_lens: Seq<usize>,
    covered: Seq<bool>,
    f: int,
)
    requires
        mesh_index_bounds_spec(m),
        mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_witness_spec(
            m,
            face_cycle_lens,
            covered,
        ),
        0 <= f < mesh_face_count_spec(m),
    ensures
        mesh_face_cycle_witness_spec(m, f, face_cycle_lens[f] as int),
{
    let hcnt = mesh_half_edge_count_spec(m);
    let k = face_cycle_lens[f] as int;
    let start = m.face_half_edges[f];
    assert(mesh_face_representative_cycle_kernel_bridge_witness_spec(m, f, k));
    assert(0 <= start < hcnt);

    assert(forall|i: int|
        0 <= i < k ==> 0 <= #[trigger] mesh_next_iter_spec(m, start, i as nat) < hcnt) by {
        assert forall|i: int|
            0 <= i < k implies 0 <= #[trigger] mesh_next_iter_spec(m, start, i as nat) < hcnt by {
            lemma_mesh_next_iter_in_bounds(m, start, i as nat);
        };
    };
    assert(forall|i: int|
        0 <= i < k ==> #[trigger] m.half_edges[mesh_next_iter_spec(m, start, i as nat)].face == f);

    lemma_face_bridge_witness_implies_face_cycle_coverage(m, face_cycle_lens, covered, f);
    assert(forall|h: int|
        0 <= h < hcnt && #[trigger] m.half_edges[h].face == f ==> exists|i: int| {
            &&& 0 <= i < k
            &&& #[trigger] mesh_next_iter_spec(m, start, i as nat) == h
        });

    assert(mesh_face_cycle_witness_spec(m, f, k)) by {
        assert(3 <= k <= hcnt);
        assert(mesh_next_iter_spec(m, start, k as nat) == start);
        assert(forall|i: int|
            0 <= i < k ==> {
                let h = mesh_next_iter_spec(m, start, i as nat);
                &&& 0 <= h < hcnt
                &&& #[trigger] m.half_edges[mesh_next_iter_spec(m, start, i as nat)].face == f
            }) by {
            assert forall|i: int|
                0 <= i < k implies {
                    let h = mesh_next_iter_spec(m, start, i as nat);
                    &&& 0 <= h < hcnt
                    &&& #[trigger] m.half_edges[mesh_next_iter_spec(m, start, i as nat)].face == f
                } by {
                assert(0 <= mesh_next_iter_spec(m, start, i as nat) < hcnt);
                assert(#[trigger] m.half_edges[mesh_next_iter_spec(m, start, i as nat)].face == f);
            };
        };
        assert(forall|i: int, j: int|
            #![trigger mesh_next_iter_spec(m, start, i as nat), mesh_next_iter_spec(m, start, j as nat)]
            0 <= i < j < k ==> mesh_next_iter_spec(m, start, i as nat) != mesh_next_iter_spec(
                m,
                start,
                j as nat,
            ));
        assert(forall|h: int|
            0 <= h < hcnt && #[trigger] m.half_edges[h].face == f ==> exists|i: int|
                #![trigger mesh_next_iter_spec(m, start, i as nat)]
                0 <= i < k && mesh_next_iter_spec(m, start, i as nat) == h);
    };
}

pub proof fn lemma_face_bridge_total_implies_face_next_cycles(m: MeshModel)
    requires
        mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_total_spec(m),
    ensures
        mesh_face_next_cycles_spec(m),
{
    assert(mesh_index_bounds_spec(m));
    assert(mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_spec(m));
    let (face_cycle_lens, covered) = choose|face_cycle_lens: Seq<usize>, covered: Seq<bool>| {
        mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_witness_spec(
            m,
            face_cycle_lens,
            covered,
        )
    };
    assert(mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_witness_spec(
        m,
        face_cycle_lens,
        covered,
    ));
    assert(mesh_face_next_cycles_witness_spec(m, face_cycle_lens)) by {
        assert(face_cycle_lens.len() == mesh_face_count_spec(m));
        assert(forall|f: int|
            #![trigger face_cycle_lens[f]]
            0 <= f < mesh_face_count_spec(m)
                ==> mesh_face_cycle_witness_spec(m, f, face_cycle_lens[f] as int)) by {
            assert forall|f: int|
                #![trigger face_cycle_lens[f]]
                0 <= f < mesh_face_count_spec(m)
                    implies mesh_face_cycle_witness_spec(m, f, face_cycle_lens[f] as int)
                by {
                lemma_face_bridge_witness_implies_face_cycle_witness(m, face_cycle_lens, covered, f);
            };
        };
    };
    assert(exists|face_cycle_lens2: Seq<usize>| mesh_face_next_cycles_witness_spec(m, face_cycle_lens2))
        by {
        let face_cycle_lens2 = face_cycle_lens;
        assert(mesh_face_next_cycles_witness_spec(m, face_cycle_lens2));
    };
    assert(mesh_face_next_cycles_spec(m));
}

pub open spec fn kernel_face_cover_step_witness_spec(
    km: &kernels::KernelMesh,
    face_cycle_lens: Seq<usize>,
    h: int,
    w: (int, int),
) -> bool {
    &&& 0 <= w.0 < kernels::kernel_face_count_spec(km)
    &&& 0 <= w.1 < face_cycle_lens[w.0] as int
    &&& kernels::kernel_next_iter_spec(km, km.face_half_edges@[w.0] as int, w.1 as nat) == h
}

pub proof fn lemma_kernel_next_or_self_matches_mesh(
    km: &kernels::KernelMesh,
    m: MeshModel,
    h: int,
)
    requires
        kernel_mesh_matches_mesh_model_spec(km, m),
    ensures
        kernels::kernel_next_or_self_spec(km, h) == mesh_next_or_self_spec(m, h),
{
    let hcnt = mesh_half_edge_count_spec(m);
    assert(hcnt == kernels::kernel_half_edge_count_spec(km));
    if 0 <= h < hcnt {
        let kn = km.half_edges@[h].next as int;
        let mn = m.half_edges[h].next;
        assert(kn == mn);
        if 0 <= kn < hcnt {
            assert(kernels::kernel_next_or_self_spec(km, h) == kn);
            assert(mesh_next_or_self_spec(m, h) == mn);
        } else {
            assert(kernels::kernel_next_or_self_spec(km, h) == h);
            assert(mesh_next_or_self_spec(m, h) == h);
        }
    } else {
        assert(kernels::kernel_next_or_self_spec(km, h) == h);
        assert(mesh_next_or_self_spec(m, h) == h);
    }
}

pub proof fn lemma_kernel_next_iter_matches_mesh(
    km: &kernels::KernelMesh,
    m: MeshModel,
    h: int,
    n: nat,
)
    requires
        kernel_mesh_matches_mesh_model_spec(km, m),
    ensures
        kernels::kernel_next_iter_spec(km, h, n) == mesh_next_iter_spec(m, h, n),
    decreases n,
{
    if n == 0 {
    } else {
        let prev = (n - 1) as nat;
        lemma_kernel_next_iter_matches_mesh(km, m, h, prev);
        lemma_kernel_next_or_self_matches_mesh(km, m, kernels::kernel_next_iter_spec(km, h, prev));
        assert(kernels::kernel_next_iter_spec(km, h, n)
            == kernels::kernel_next_or_self_spec(km, kernels::kernel_next_iter_spec(km, h, prev)));
        assert(mesh_next_iter_spec(m, h, n)
            == mesh_next_or_self_spec(m, mesh_next_iter_spec(m, h, prev)));
        assert(kernels::kernel_next_iter_spec(km, h, prev) == mesh_next_iter_spec(m, h, prev));
    }
}

pub proof fn lemma_kernel_vertex_ring_succ_or_self_matches_mesh(
    km: &kernels::KernelMesh,
    m: MeshModel,
    h: int,
)
    requires
        kernel_mesh_matches_mesh_model_spec(km, m),
    ensures
        kernels::kernel_vertex_ring_succ_or_self_spec(km, h) == mesh_vertex_ring_succ_or_self_spec(m, h),
{
    let hcnt = mesh_half_edge_count_spec(m);
    assert(hcnt == kernels::kernel_half_edge_count_spec(km));
    if 0 <= h < hcnt {
        let kt = km.half_edges@[h].twin as int;
        let mt = m.half_edges[h].twin;
        assert(kt == mt);
        if 0 <= kt < hcnt {
            let kn = km.half_edges@[kt].next as int;
            let mn = m.half_edges[kt].next;
            assert(kn == mn);
            if 0 <= kn < hcnt {
                assert(kernels::kernel_vertex_ring_succ_or_self_spec(km, h) == kn);
                assert(mesh_vertex_ring_succ_or_self_spec(m, h) == mn);
            } else {
                assert(kernels::kernel_vertex_ring_succ_or_self_spec(km, h) == h);
                assert(mesh_vertex_ring_succ_or_self_spec(m, h) == h);
            }
        } else {
            assert(kernels::kernel_vertex_ring_succ_or_self_spec(km, h) == h);
            assert(mesh_vertex_ring_succ_or_self_spec(m, h) == h);
        }
    } else {
        assert(kernels::kernel_vertex_ring_succ_or_self_spec(km, h) == h);
        assert(mesh_vertex_ring_succ_or_self_spec(m, h) == h);
    }
}

pub proof fn lemma_kernel_vertex_ring_iter_matches_mesh(
    km: &kernels::KernelMesh,
    m: MeshModel,
    h: int,
    n: nat,
)
    requires
        kernel_mesh_matches_mesh_model_spec(km, m),
    ensures
        kernels::kernel_vertex_ring_iter_spec(km, h, n) == mesh_vertex_ring_iter_spec(m, h, n),
    decreases n,
{
    if n == 0 {
    } else {
        let prev = (n - 1) as nat;
        lemma_kernel_vertex_ring_iter_matches_mesh(km, m, h, prev);
        lemma_kernel_vertex_ring_succ_or_self_matches_mesh(
            km,
            m,
            kernels::kernel_vertex_ring_iter_spec(km, h, prev),
        );
        assert(kernels::kernel_vertex_ring_iter_spec(km, h, n)
            == kernels::kernel_vertex_ring_succ_or_self_spec(
            km,
            kernels::kernel_vertex_ring_iter_spec(km, h, prev),
        ));
        assert(mesh_vertex_ring_iter_spec(m, h, n)
            == mesh_vertex_ring_succ_or_self_spec(m, mesh_vertex_ring_iter_spec(m, h, prev)));
        assert(kernels::kernel_vertex_ring_iter_spec(km, h, prev)
            == mesh_vertex_ring_iter_spec(m, h, prev));
    }
}

pub proof fn lemma_kernel_face_cycle_witness_matches_mesh(
    km: &kernels::KernelMesh,
    m: MeshModel,
    f: int,
    k: int,
)
    requires
        kernel_mesh_matches_mesh_model_spec(km, m),
        kernels::kernel_index_bounds_spec(km),
        0 <= f < kernels::kernel_face_count_spec(km),
        kernels::kernel_face_representative_cycle_witness_spec(km, f, k),
    ensures
        mesh_face_representative_cycle_kernel_bridge_witness_spec(m, f, k),
{
    let hcnt = mesh_half_edge_count_spec(m);
    let start_k = km.face_half_edges@[f] as int;
    let start_m = m.face_half_edges[f];
    assert(hcnt == kernels::kernel_half_edge_count_spec(km));
    assert(start_k == start_m);

    assert(3 <= k <= hcnt);
    lemma_kernel_next_iter_matches_mesh(km, m, start_k, k as nat);
    assert(mesh_next_iter_spec(m, start_m, k as nat) == start_m);

    assert(forall|i: int|
        0 <= i < k ==> #[trigger] m.half_edges[mesh_next_iter_spec(m, start_m, i as nat)].face == f) by {
        assert forall|i: int|
            0 <= i < k implies #[trigger] m.half_edges[mesh_next_iter_spec(m, start_m, i as nat)].face == f by {
            kernels::lemma_kernel_next_iter_in_bounds(km, start_k, i as nat);
            let hi = kernels::kernel_next_iter_spec(km, start_k, i as nat);
            assert(0 <= hi < kernels::kernel_half_edge_count_spec(km));
            lemma_kernel_next_iter_matches_mesh(km, m, start_k, i as nat);
            assert(hi == mesh_next_iter_spec(m, start_m, i as nat));
            assert((#[trigger] km.half_edges@[hi]).face as int == m.half_edges[hi].face);
            assert(km.half_edges@[hi].face as int == f);
            assert(m.half_edges[mesh_next_iter_spec(m, start_m, i as nat)].face == f);
        };
    };
    assert(forall|i: int, j: int|
        #![trigger mesh_next_iter_spec(m, start_m, i as nat), mesh_next_iter_spec(m, start_m, j as nat)]
        0 <= i < j < k
            ==> mesh_next_iter_spec(m, start_m, i as nat) != mesh_next_iter_spec(
                m,
                start_m,
                j as nat,
            )) by {
        assert forall|i: int, j: int|
            #![trigger mesh_next_iter_spec(m, start_m, i as nat), mesh_next_iter_spec(m, start_m, j as nat)]
            0 <= i < j < k
                implies mesh_next_iter_spec(m, start_m, i as nat) != mesh_next_iter_spec(
                    m,
                    start_m,
                    j as nat,
                ) by {
            lemma_kernel_next_iter_matches_mesh(km, m, start_k, i as nat);
            lemma_kernel_next_iter_matches_mesh(km, m, start_k, j as nat);
            assert(kernels::kernel_next_iter_spec(km, start_k, i as nat)
                != kernels::kernel_next_iter_spec(km, start_k, j as nat));
            assert(mesh_next_iter_spec(m, start_m, i as nat)
                == kernels::kernel_next_iter_spec(km, start_k, i as nat));
            assert(mesh_next_iter_spec(m, start_m, j as nat)
                == kernels::kernel_next_iter_spec(km, start_k, j as nat));
        };
    };
}

pub proof fn lemma_kernel_index_bounds_implies_mesh_index_bounds(
    km: &kernels::KernelMesh,
    m: MeshModel,
)
    requires
        kernel_mesh_matches_mesh_model_spec(km, m),
        kernels::kernel_index_bounds_spec(km),
    ensures
        mesh_index_bounds_spec(m),
{
    let hcnt = mesh_half_edge_count_spec(m);
    let vcnt = mesh_vertex_count_spec(m);
    let ecnt = mesh_edge_count_spec(m);
    let fcnt = mesh_face_count_spec(m);
    assert(hcnt == kernels::kernel_half_edge_count_spec(km));
    assert(vcnt == kernels::kernel_vertex_count_spec(km));
    assert(ecnt == kernels::kernel_edge_count_spec(km));
    assert(fcnt == kernels::kernel_face_count_spec(km));

    assert(forall|v: int|
        0 <= v < vcnt ==> 0 <= #[trigger] m.vertex_half_edges[v] < hcnt) by {
        assert forall|v: int| 0 <= v < vcnt implies 0 <= #[trigger] m.vertex_half_edges[v] < hcnt by {
            assert((#[trigger] km.vertex_half_edges@[v] as int) == m.vertex_half_edges[v]);
            assert((km.vertex_half_edges@[v] as int) < hcnt);
            assert(0 <= km.vertex_half_edges@[v] as int);
        };
    };

    assert(forall|e: int|
        0 <= e < ecnt ==> 0 <= #[trigger] m.edge_half_edges[e] < hcnt) by {
        assert forall|e: int| 0 <= e < ecnt implies 0 <= #[trigger] m.edge_half_edges[e] < hcnt by {
            assert((#[trigger] km.edge_half_edges@[e] as int) == m.edge_half_edges[e]);
            assert((km.edge_half_edges@[e] as int) < hcnt);
            assert(0 <= km.edge_half_edges@[e] as int);
        };
    };

    assert(forall|f: int|
        0 <= f < fcnt ==> 0 <= #[trigger] m.face_half_edges[f] < hcnt) by {
        assert forall|f: int| 0 <= f < fcnt implies 0 <= #[trigger] m.face_half_edges[f] < hcnt by {
            assert((#[trigger] km.face_half_edges@[f] as int) == m.face_half_edges[f]);
            assert((km.face_half_edges@[f] as int) < hcnt);
            assert(0 <= km.face_half_edges@[f] as int);
        };
    };

    assert(forall|h: int| 0 <= h < hcnt ==> {
        let he = #[trigger] m.half_edges[h];
        &&& 0 <= he.twin < hcnt
        &&& 0 <= he.next < hcnt
        &&& 0 <= he.prev < hcnt
        &&& 0 <= he.vertex < vcnt
        &&& 0 <= he.edge < ecnt
        &&& 0 <= he.face < fcnt
    }) by {
        assert forall|h: int| 0 <= h < hcnt implies {
            let he = #[trigger] m.half_edges[h];
            &&& 0 <= he.twin < hcnt
            &&& 0 <= he.next < hcnt
            &&& 0 <= he.prev < hcnt
            &&& 0 <= he.vertex < vcnt
            &&& 0 <= he.edge < ecnt
            &&& 0 <= he.face < fcnt
        } by {
            let khe = #[trigger] km.half_edges@[h];
            assert((khe.twin as int) == m.half_edges[h].twin);
            assert((khe.next as int) == m.half_edges[h].next);
            assert((khe.prev as int) == m.half_edges[h].prev);
            assert((khe.vertex as int) == m.half_edges[h].vertex);
            assert((khe.edge as int) == m.half_edges[h].edge);
            assert((khe.face as int) == m.half_edges[h].face);

            assert((khe.twin as int) < hcnt);
            assert((khe.next as int) < hcnt);
            assert((khe.prev as int) < hcnt);
            assert((khe.vertex as int) < vcnt);
            assert((khe.edge as int) < ecnt);
            assert((khe.face as int) < fcnt);

            assert(0 <= khe.twin as int);
            assert(0 <= khe.next as int);
            assert(0 <= khe.prev as int);
            assert(0 <= khe.vertex as int);
            assert(0 <= khe.edge as int);
            assert(0 <= khe.face as int);
        };
    };
    assert(mesh_index_bounds_spec(m));
}

pub proof fn lemma_kernel_face_cycles_cover_all_matches_mesh(
    km: &kernels::KernelMesh,
    m: MeshModel,
)
    requires
        kernel_mesh_matches_mesh_model_spec(km, m),
        kernels::kernel_face_representative_cycles_cover_all_half_edges_total_spec(km),
    ensures
        mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_total_spec(m),
{
    lemma_kernel_index_bounds_implies_mesh_index_bounds(km, m);
    reveal(kernels::kernel_face_representative_cycles_cover_all_half_edges_spec);
    assert(kernels::kernel_face_representative_cycles_cover_all_half_edges_spec(km));
    assert(exists|face_cycle_lens: Seq<usize>, covered: Seq<bool>| {
        kernels::kernel_face_representative_cycles_cover_all_half_edges_witness_spec(
            km,
            face_cycle_lens,
            covered,
        )
    });
    let (face_cycle_lens, covered) = choose|face_cycle_lens: Seq<usize>, covered: Seq<bool>| {
        kernels::kernel_face_representative_cycles_cover_all_half_edges_witness_spec(
            km,
            face_cycle_lens,
            covered,
        )
    };
    assert(kernels::kernel_face_representative_cycles_cover_all_half_edges_witness_spec(
        km,
        face_cycle_lens,
        covered,
    ));

    assert(mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_spec(m)) by {
        assert(face_cycle_lens.len() == mesh_face_count_spec(m));
        assert(covered.len() == mesh_half_edge_count_spec(m));

        assert(forall|f: int|
            #![trigger face_cycle_lens[f]]
            0 <= f < mesh_face_count_spec(m)
                ==> mesh_face_representative_cycle_kernel_bridge_witness_spec(
                    m,
                    f,
                    face_cycle_lens[f] as int,
                )) by {
            assert forall|f: int|
                #![trigger face_cycle_lens[f]]
                0 <= f < mesh_face_count_spec(m)
                    implies mesh_face_representative_cycle_kernel_bridge_witness_spec(
                        m,
                        f,
                        face_cycle_lens[f] as int,
                    ) by {
                lemma_kernel_face_cycle_witness_matches_mesh(km, m, f, face_cycle_lens[f] as int);
            };
        };

        assert(forall|h: int|
            #![trigger h + 0]
            0 <= h < mesh_half_edge_count_spec(m) && #[trigger] covered[h]
                ==> exists|f: int, i: int| {
                    &&& 0 <= f < mesh_face_count_spec(m)
                    &&& 0 <= i < face_cycle_lens[f] as int
                    &&& #[trigger] mesh_next_iter_spec(m, m.face_half_edges[f], i as nat) == h
                }) by {
            assert forall|h: int|
                #![trigger h + 0]
                0 <= h < mesh_half_edge_count_spec(m) && #[trigger] covered[h]
                    implies exists|f: int, i: int| {
                        &&& 0 <= f < mesh_face_count_spec(m)
                        &&& 0 <= i < face_cycle_lens[f] as int
                        &&& #[trigger] mesh_next_iter_spec(m, m.face_half_edges[f], i as nat) == h
                    } by {
                let (fw, iw) = choose|f: int, i: int| {
                    &&& 0 <= f < kernels::kernel_face_count_spec(km)
                    &&& 0 <= i < face_cycle_lens[f] as int
                    &&& #[trigger] kernels::kernel_next_iter_spec(
                        km,
                        km.face_half_edges@[f] as int,
                        i as nat,
                    ) == h
                };
                assert(kernel_face_cover_step_witness_spec(km, face_cycle_lens, h, (fw, iw)));
                assert(exists|f: int, i: int| {
                    kernel_face_cover_step_witness_spec(km, face_cycle_lens, h, (f, i))
                });
                let (f0, i0) = choose|f: int, i: int| {
                    kernel_face_cover_step_witness_spec(km, face_cycle_lens, h, (f, i))
                };
                assert(0 <= f0 < mesh_face_count_spec(m));
                assert(0 <= i0 < face_cycle_lens[f0] as int);
                lemma_kernel_next_iter_matches_mesh(km, m, km.face_half_edges@[f0] as int, i0 as nat);
                assert(km.face_half_edges@[f0] as int == m.face_half_edges[f0]);
                assert(mesh_next_iter_spec(m, m.face_half_edges[f0], i0 as nat) == h);
            };
        };

        assert(forall|h: int| 0 <= h < mesh_half_edge_count_spec(m) ==> #[trigger] covered[h]) by {
            assert forall|h: int| 0 <= h < mesh_half_edge_count_spec(m) implies #[trigger] covered[h] by {
            };
        };

        assert(forall|f1: int, i1: int, f2: int, i2: int|
            #![trigger mesh_next_iter_spec(m, m.face_half_edges[f1], i1 as nat), mesh_next_iter_spec(m, m.face_half_edges[f2], i2 as nat)]
            0 <= f1 < mesh_face_count_spec(m)
                && 0 <= f2 < mesh_face_count_spec(m)
                && 0 <= i1 < face_cycle_lens[f1] as int
                && 0 <= i2 < face_cycle_lens[f2] as int
                && mesh_next_iter_spec(m, m.face_half_edges[f1], i1 as nat)
                    == mesh_next_iter_spec(m, m.face_half_edges[f2], i2 as nat)
                ==> f1 == f2) by {
            assert forall|f1: int, i1: int, f2: int, i2: int|
                0 <= f1 < mesh_face_count_spec(m)
                    && 0 <= f2 < mesh_face_count_spec(m)
                    && 0 <= i1 < face_cycle_lens[f1] as int
                    && 0 <= i2 < face_cycle_lens[f2] as int
                    && #[trigger] mesh_next_iter_spec(m, m.face_half_edges[f1], i1 as nat)
                        == #[trigger] mesh_next_iter_spec(m, m.face_half_edges[f2], i2 as nat)
                    implies f1 == f2 by {
                assert(0 <= f1 < kernels::kernel_face_count_spec(km));
                assert(0 <= f2 < kernels::kernel_face_count_spec(km));
                lemma_kernel_next_iter_matches_mesh(km, m, km.face_half_edges@[f1] as int, i1 as nat);
                lemma_kernel_next_iter_matches_mesh(km, m, km.face_half_edges@[f2] as int, i2 as nat);
                assert(km.face_half_edges@[f1] as int == m.face_half_edges[f1]);
                assert(km.face_half_edges@[f2] as int == m.face_half_edges[f2]);
                assert(kernels::kernel_next_iter_spec(km, km.face_half_edges@[f1] as int, i1 as nat)
                    == mesh_next_iter_spec(m, m.face_half_edges[f1], i1 as nat));
                assert(kernels::kernel_next_iter_spec(km, km.face_half_edges@[f2] as int, i2 as nat)
                    == mesh_next_iter_spec(m, m.face_half_edges[f2], i2 as nat));
                assert(kernels::kernel_next_iter_spec(km, km.face_half_edges@[f1] as int, i1 as nat)
                    == kernels::kernel_next_iter_spec(km, km.face_half_edges@[f2] as int, i2 as nat));
            };
        };

        assert(mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_witness_spec(
            m,
            face_cycle_lens,
            covered,
        ));
        assert(exists|face_cycle_lens2: Seq<usize>, covered2: Seq<bool>| {
            mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_witness_spec(
                m,
                face_cycle_lens2,
                covered2,
            )
        }) by {
            let face_cycle_lens2 = face_cycle_lens;
            let covered2 = covered;
            assert(mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_witness_spec(
                m,
                face_cycle_lens2,
                covered2,
            ));
        };
    }
    assert(mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_total_spec(m));
}

pub proof fn lemma_kernel_vertex_cycle_witness_matches_mesh(
    km: &kernels::KernelMesh,
    m: MeshModel,
    v: int,
    k: int,
)
    requires
        kernel_mesh_matches_mesh_model_spec(km, m),
        kernels::kernel_index_bounds_spec(km),
        0 <= v < kernels::kernel_vertex_count_spec(km),
        kernels::kernel_vertex_representative_cycle_witness_spec(km, v, k),
    ensures
        mesh_vertex_representative_cycle_kernel_bridge_witness_spec(m, v, k),
{
    let hcnt = mesh_half_edge_count_spec(m);
    let start_k = km.vertex_half_edges@[v] as int;
    let start_m = m.vertex_half_edges[v];
    assert(hcnt == kernels::kernel_half_edge_count_spec(km));
    assert(start_k == start_m);
    assert(0 <= start_k < kernels::kernel_half_edge_count_spec(km));

    assert(1 <= k <= hcnt);
    lemma_kernel_vertex_ring_iter_matches_mesh(km, m, start_k, k as nat);
    assert(mesh_vertex_ring_iter_spec(m, start_m, k as nat) == start_m);

    assert(forall|i: int|
        0 <= i < k ==> #[trigger] m.half_edges[mesh_vertex_ring_iter_spec(m, start_m, i as nat)].vertex == v) by {
        assert forall|i: int|
            0 <= i < k implies #[trigger] m.half_edges[mesh_vertex_ring_iter_spec(m, start_m, i as nat)].vertex == v by {
            kernels::lemma_kernel_vertex_ring_iter_in_bounds(km, start_k, i as nat);
            let hi = kernels::kernel_vertex_ring_iter_spec(km, start_k, i as nat);
            assert(0 <= hi < kernels::kernel_half_edge_count_spec(km));
            lemma_kernel_vertex_ring_iter_matches_mesh(km, m, start_k, i as nat);
            assert(hi == mesh_vertex_ring_iter_spec(m, start_m, i as nat));
            assert((#[trigger] km.half_edges@[hi]).vertex as int == m.half_edges[hi].vertex);
            assert(km.half_edges@[hi].vertex as int == v);
            assert(m.half_edges[mesh_vertex_ring_iter_spec(m, start_m, i as nat)].vertex == v);
        };
    };
}

pub proof fn lemma_kernel_vertex_cycle_witness_implies_mesh_vertex_ring_witness(
    km: &kernels::KernelMesh,
    m: MeshModel,
    v: int,
    k: int,
)
    requires
        kernel_mesh_matches_mesh_model_spec(km, m),
        kernels::kernel_index_bounds_spec(km),
        0 <= v < kernels::kernel_vertex_count_spec(km),
        kernels::kernel_vertex_representative_cycle_witness_spec(km, v, k),
    ensures
        mesh_vertex_ring_witness_spec(m, v, k),
{
    let hcnt = mesh_half_edge_count_spec(m);
    let start_k = km.vertex_half_edges@[v] as int;
    let start_m = m.vertex_half_edges[v];
    assert(hcnt == kernels::kernel_half_edge_count_spec(km));
    assert(start_k == start_m);
    assert(0 <= start_k < kernels::kernel_half_edge_count_spec(km));

    lemma_kernel_vertex_cycle_witness_matches_mesh(km, m, v, k);
    assert(mesh_vertex_representative_cycle_kernel_bridge_witness_spec(m, v, k));

    assert(mesh_vertex_ring_witness_spec(m, v, k)) by {
        assert(1 <= k <= hcnt);
        assert(mesh_vertex_ring_iter_spec(m, start_m, k as nat) == start_m);
        assert(forall|i: int|
            0 <= i < k ==> 0 <= #[trigger] mesh_vertex_ring_iter_spec(m, start_m, i as nat) < hcnt) by {
            assert forall|i: int|
                0 <= i < k implies 0 <= #[trigger] mesh_vertex_ring_iter_spec(m, start_m, i as nat) < hcnt by {
                kernels::lemma_kernel_vertex_ring_iter_in_bounds(km, start_k, i as nat);
                let hi = kernels::kernel_vertex_ring_iter_spec(km, start_k, i as nat);
                assert(0 <= hi < kernels::kernel_half_edge_count_spec(km));
                lemma_kernel_vertex_ring_iter_matches_mesh(km, m, start_k, i as nat);
                assert(hi == mesh_vertex_ring_iter_spec(m, start_m, i as nat));
            };
        };
        assert(forall|i: int|
            0 <= i < k ==> #[trigger] m.half_edges[mesh_vertex_ring_iter_spec(m, start_m, i as nat)].vertex == v) by {
            assert forall|i: int|
                0 <= i < k implies #[trigger] m.half_edges[mesh_vertex_ring_iter_spec(m, start_m, i as nat)].vertex == v by {
                assert(#[trigger] m.half_edges[mesh_vertex_ring_iter_spec(m, start_m, i as nat)].vertex == v);
            };
        };
        assert(forall|i: int|
            0 <= i < k ==> {
                let h = mesh_vertex_ring_iter_spec(m, start_m, i as nat);
                &&& 0 <= h < hcnt
                &&& #[trigger] m.half_edges[mesh_vertex_ring_iter_spec(m, start_m, i as nat)].vertex == v
            }) by {
            assert forall|i: int|
                0 <= i < k implies {
                    let h = mesh_vertex_ring_iter_spec(m, start_m, i as nat);
                    &&& 0 <= h < hcnt
                    &&& #[trigger] m.half_edges[mesh_vertex_ring_iter_spec(m, start_m, i as nat)].vertex == v
                } by {
                assert(0 <= mesh_vertex_ring_iter_spec(m, start_m, i as nat) < hcnt);
                assert(#[trigger] m.half_edges[mesh_vertex_ring_iter_spec(m, start_m, i as nat)].vertex == v);
            };
        };
        assert(forall|i: int, j: int|
            #![trigger mesh_vertex_ring_iter_spec(m, start_m, i as nat), mesh_vertex_ring_iter_spec(m, start_m, j as nat)]
            0 <= i < j < k
                ==> mesh_vertex_ring_iter_spec(m, start_m, i as nat) != mesh_vertex_ring_iter_spec(
                    m,
                    start_m,
                    j as nat,
                )) by {
            assert forall|i: int, j: int|
                #![trigger mesh_vertex_ring_iter_spec(m, start_m, i as nat), mesh_vertex_ring_iter_spec(m, start_m, j as nat)]
                0 <= i < j < k
                    implies mesh_vertex_ring_iter_spec(m, start_m, i as nat)
                        != mesh_vertex_ring_iter_spec(m, start_m, j as nat) by {
                lemma_kernel_vertex_ring_iter_matches_mesh(km, m, start_k, i as nat);
                lemma_kernel_vertex_ring_iter_matches_mesh(km, m, start_k, j as nat);
                assert(kernels::kernel_vertex_ring_iter_spec(km, start_k, i as nat)
                    != kernels::kernel_vertex_ring_iter_spec(km, start_k, j as nat));
                assert(mesh_vertex_ring_iter_spec(m, start_m, i as nat)
                    == kernels::kernel_vertex_ring_iter_spec(km, start_k, i as nat));
                assert(mesh_vertex_ring_iter_spec(m, start_m, j as nat)
                    == kernels::kernel_vertex_ring_iter_spec(km, start_k, j as nat));
            };
        };
        assert(forall|h: int|
            0 <= h < hcnt && #[trigger] m.half_edges[h].vertex == v ==> exists|i: int|
                #![trigger mesh_vertex_ring_iter_spec(m, start_m, i as nat)]
                0 <= i < k && mesh_vertex_ring_iter_spec(m, start_m, i as nat) == h) by {
            assert forall|h: int|
                0 <= h < hcnt && #[trigger] m.half_edges[h].vertex == v implies exists|i: int|
                    #![trigger mesh_vertex_ring_iter_spec(m, start_m, i as nat)]
                    0 <= i < k && mesh_vertex_ring_iter_spec(m, start_m, i as nat) == h by {
                assert((#[trigger] km.half_edges@[h]).vertex as int == m.half_edges[h].vertex);
                assert(km.half_edges@[h].vertex as int == v);
                let i0 = choose|i: int| {
                    &&& 0 <= i < k
                    &&& #[trigger] kernels::kernel_vertex_ring_iter_spec(km, start_k, i as nat) == h
                };
                assert(0 <= i0 < k);
                lemma_kernel_vertex_ring_iter_matches_mesh(km, m, start_k, i0 as nat);
                assert(mesh_vertex_ring_iter_spec(m, start_m, i0 as nat)
                    == kernels::kernel_vertex_ring_iter_spec(km, start_k, i0 as nat));
                assert(mesh_vertex_ring_iter_spec(m, start_m, i0 as nat) == h);
            };
        };
    };
}

pub proof fn lemma_kernel_vertex_manifold_total_implies_mesh_vertex_manifold(
    km: &kernels::KernelMesh,
    m: MeshModel,
)
    requires
        kernel_mesh_matches_mesh_model_spec(km, m),
        kernels::kernel_vertex_manifold_single_cycle_total_spec(km),
    ensures
        mesh_vertex_manifold_single_cycle_spec(m),
{
    assert(kernels::kernel_index_bounds_spec(km));
    reveal(kernels::kernel_vertex_manifold_single_cycle_basic_spec);
    assert(kernels::kernel_vertex_manifold_single_cycle_basic_spec(km));
    let vertex_cycle_lens = choose|vertex_cycle_lens: Seq<usize>| {
        &&& vertex_cycle_lens.len() == kernels::kernel_vertex_count_spec(km)
        &&& forall|v: int|
            #![trigger vertex_cycle_lens[v]]
            0 <= v < kernels::kernel_vertex_count_spec(km)
                ==> kernels::kernel_vertex_representative_cycle_witness_spec(
                    km,
                    v,
                    vertex_cycle_lens[v] as int,
                )
    };
    assert(vertex_cycle_lens.len() == mesh_vertex_count_spec(m));
    assert(forall|vp: int|
        #![trigger vertex_cycle_lens[vp]]
        0 <= vp < kernels::kernel_vertex_count_spec(km)
            ==> kernels::kernel_vertex_representative_cycle_witness_spec(
                km,
                vp,
                vertex_cycle_lens[vp] as int,
            ));
    assert(mesh_vertex_manifold_single_cycle_witness_spec(m, vertex_cycle_lens)) by {
        assert(vertex_cycle_lens.len() == mesh_vertex_count_spec(m));
        assert(forall|v: int|
            #![trigger vertex_cycle_lens[v]]
            0 <= v < mesh_vertex_count_spec(m)
                ==> mesh_vertex_ring_witness_spec(m, v, vertex_cycle_lens[v] as int)) by {
            assert forall|v: int|
                #![trigger vertex_cycle_lens[v]]
                0 <= v < mesh_vertex_count_spec(m)
                    implies mesh_vertex_ring_witness_spec(m, v, vertex_cycle_lens[v] as int) by {
                assert(v < vertex_cycle_lens.len());
                assert(0 <= v < kernels::kernel_vertex_count_spec(km));
                let k = vertex_cycle_lens[v] as int;
                assert(kernels::kernel_vertex_representative_cycle_witness_spec(km, v, k));
                lemma_kernel_vertex_cycle_witness_implies_mesh_vertex_ring_witness(km, m, v, k);
                assert(mesh_vertex_ring_witness_spec(m, v, k));
            };
        };
    };
    assert(exists|vertex_cycle_lens2: Seq<usize>| mesh_vertex_manifold_single_cycle_witness_spec(m, vertex_cycle_lens2))
        by {
        let vertex_cycle_lens2 = vertex_cycle_lens;
        assert(mesh_vertex_manifold_single_cycle_witness_spec(m, vertex_cycle_lens2));
    };
    assert(mesh_vertex_manifold_single_cycle_spec(m));
}

pub proof fn lemma_kernel_vertex_manifold_matches_mesh(
    km: &kernels::KernelMesh,
    m: MeshModel,
)
    requires
        kernel_mesh_matches_mesh_model_spec(km, m),
        kernels::kernel_vertex_manifold_single_cycle_total_spec(km),
    ensures
        mesh_vertex_representative_cycles_kernel_bridge_total_spec(m),
{
    lemma_kernel_index_bounds_implies_mesh_index_bounds(km, m);

    reveal(kernels::kernel_vertex_manifold_single_cycle_basic_spec);
    assert(kernels::kernel_vertex_manifold_single_cycle_basic_spec(km));
    assert(exists|vertex_cycle_lens: Seq<usize>| {
        &&& vertex_cycle_lens.len() == kernels::kernel_vertex_count_spec(km)
        &&& forall|v: int|
            #![trigger vertex_cycle_lens[v]]
            0 <= v < kernels::kernel_vertex_count_spec(km)
                ==> kernels::kernel_vertex_representative_cycle_witness_spec(
                    km,
                    v,
                    vertex_cycle_lens[v] as int,
                )
    });
    let vertex_cycle_lens = choose|vertex_cycle_lens: Seq<usize>| {
        &&& vertex_cycle_lens.len() == kernels::kernel_vertex_count_spec(km)
        &&& forall|v: int|
            #![trigger vertex_cycle_lens[v]]
            0 <= v < kernels::kernel_vertex_count_spec(km)
                ==> kernels::kernel_vertex_representative_cycle_witness_spec(
                    km,
                    v,
                    vertex_cycle_lens[v] as int,
                )
    };
    assert(mesh_vertex_representative_cycles_kernel_bridge_spec(m)) by {
        assert(vertex_cycle_lens.len() == mesh_vertex_count_spec(m));
        assert(forall|v: int|
            #![trigger vertex_cycle_lens[v]]
            0 <= v < mesh_vertex_count_spec(m)
                ==> mesh_vertex_representative_cycle_kernel_bridge_witness_spec(
                    m,
                    v,
                    vertex_cycle_lens[v] as int,
                )) by {
            assert forall|v: int|
                #![trigger vertex_cycle_lens[v]]
                0 <= v < mesh_vertex_count_spec(m)
                    implies mesh_vertex_representative_cycle_kernel_bridge_witness_spec(
                        m,
                        v,
                        vertex_cycle_lens[v] as int,
                    ) by {
                lemma_kernel_vertex_cycle_witness_matches_mesh(km, m, v, vertex_cycle_lens[v] as int);
            };
        };
        assert(exists|vertex_cycle_lens2: Seq<usize>| {
            &&& vertex_cycle_lens2.len() == mesh_vertex_count_spec(m)
            &&& forall|v: int|
                #![trigger vertex_cycle_lens2[v]]
                0 <= v < mesh_vertex_count_spec(m)
                    ==> mesh_vertex_representative_cycle_kernel_bridge_witness_spec(
                        m,
                        v,
                        vertex_cycle_lens2[v] as int,
                    )
        }) by {
            let vertex_cycle_lens2 = vertex_cycle_lens;
            assert(vertex_cycle_lens2.len() == mesh_vertex_count_spec(m));
            assert(forall|v: int|
                #![trigger vertex_cycle_lens2[v]]
                0 <= v < mesh_vertex_count_spec(m)
                    ==> mesh_vertex_representative_cycle_kernel_bridge_witness_spec(
                        m,
                        v,
                        vertex_cycle_lens2[v] as int,
                    ));
        };
    }
    assert(mesh_vertex_representative_cycles_kernel_bridge_total_spec(m));
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

pub open spec fn mesh_vertex_manifold_single_cycle_witness_spec(
    m: MeshModel,
    vertex_cycle_lens: Seq<usize>,
) -> bool {
    &&& vertex_cycle_lens.len() == mesh_vertex_count_spec(m)
    &&& forall|v: int|
        #![trigger vertex_cycle_lens[v]]
        0 <= v < mesh_vertex_count_spec(m)
            ==> mesh_vertex_ring_witness_spec(m, v, vertex_cycle_lens[v] as int)
}

pub open spec fn mesh_vertex_manifold_single_cycle_spec(m: MeshModel) -> bool {
    exists|vertex_cycle_lens: Seq<usize>| mesh_vertex_manifold_single_cycle_witness_spec(m, vertex_cycle_lens)
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
        &&& path[0] == from
        &&& path[(path.len() - 1) as int] == to
        &&& mesh_half_edge_walk_spec(m, path)
    }
}

pub proof fn lemma_mesh_half_edge_connected_refl(m: MeshModel, h: int)
    requires
        0 <= h < mesh_half_edge_count_spec(m),
    ensures
        mesh_half_edge_connected_spec(m, h, h),
{
    let path = Seq::<int>::empty().push(h);
    assert(path.len() > 0);
    assert(path[0] == h);
    assert(path[(path.len() - 1) as int] == h);
    assert(mesh_half_edge_walk_spec(m, path)) by {
        assert(path.len() > 0);
        assert(forall|i: int| 0 <= i < path.len() as int ==> 0 <= #[trigger] path[i] < mesh_half_edge_count_spec(m))
            by {
            assert forall|i: int| 0 <= i < path.len() as int implies 0 <= #[trigger] path[i]
                < mesh_half_edge_count_spec(m) by {
                assert(i == 0);
                assert(path[i] == h);
            };
        }
        assert(forall|i: int|
            0 <= i < (path.len() as int) - 1
                ==> mesh_half_edge_adjacent_spec(m, path[i], #[trigger] path[i + 1])) by {
            assert forall|i: int|
                0 <= i < (path.len() as int) - 1
                    implies mesh_half_edge_adjacent_spec(m, path[i], #[trigger] path[i + 1]) by {
            };
        }
    }
    assert(mesh_half_edge_connected_spec(m, h, h));
}

pub proof fn lemma_mesh_half_edge_connected_extend_direct_step(
    m: MeshModel,
    from: int,
    mid: int,
    to: int,
)
    requires
        mesh_half_edge_connected_spec(m, from, mid),
        mesh_half_edge_direct_step_spec(m, mid, to),
    ensures
        mesh_half_edge_connected_spec(m, from, to),
{
    let hcnt = mesh_half_edge_count_spec(m);
    let path = choose|path: Seq<int>| {
        &&& 0 <= from < hcnt
        &&& 0 <= mid < hcnt
        &&& 0 < path.len()
        &&& path[0] == from
        &&& path[(path.len() - 1) as int] == mid
        &&& mesh_half_edge_walk_spec(m, path)
    };
    let path2 = path.push(to);
    assert(path2.len() > 0);
    assert(path2[0] == from);
    assert(path2[(path2.len() - 1) as int] == to);
    assert(path2.len() == path.len() + 1);
    assert(mesh_half_edge_walk_spec(m, path2)) by {
        assert(path2.len() > 0);
        assert(forall|i: int| 0 <= i < path2.len() as int ==> 0 <= #[trigger] path2[i] < hcnt) by {
            assert forall|i: int| 0 <= i < path2.len() as int implies 0 <= #[trigger] path2[i] < hcnt by {
                if i < path.len() as int {
                    assert(path2[i] == path[i]);
                    assert(0 <= path[i] < hcnt);
                } else {
                    assert(i == path.len() as int);
                    assert(path2[i] == to);
                    assert(0 <= to < hcnt);
                }
            };
        }
        assert(forall|i: int|
            0 <= i < (path2.len() as int) - 1
                ==> mesh_half_edge_adjacent_spec(m, path2[i], #[trigger] path2[i + 1])) by {
            assert forall|i: int|
                0 <= i < (path2.len() as int) - 1
                    implies mesh_half_edge_adjacent_spec(m, path2[i], #[trigger] path2[i + 1]) by {
                if i < (path.len() as int) - 1 {
                    assert(path2[i] == path[i]);
                    assert(path2[i + 1] == path[i + 1]);
                    assert(mesh_half_edge_adjacent_spec(m, path[i], path[i + 1]));
                } else {
                    assert(i == (path.len() as int) - 1);
                    assert(path2[i] == path[(path.len() - 1) as int]);
                    assert(path[(path.len() - 1) as int] == mid);
                    assert(path2[i + 1] == to);
                    assert(mesh_half_edge_direct_step_spec(m, mid, to));
                    assert(mesh_half_edge_adjacent_spec(m, mid, to));
                }
            };
        }
    }
    assert(mesh_half_edge_connected_spec(m, from, to));
}

pub proof fn lemma_mesh_half_edge_connected_symmetric(m: MeshModel, from: int, to: int)
    requires
        mesh_half_edge_connected_spec(m, from, to),
    ensures
        mesh_half_edge_connected_spec(m, to, from),
{
    let hcnt = mesh_half_edge_count_spec(m);
    let path = choose|path: Seq<int>| {
        &&& 0 <= from < hcnt
        &&& 0 <= to < hcnt
        &&& 0 < path.len()
        &&& path[0] == from
        &&& path[(path.len() - 1) as int] == to
        &&& mesh_half_edge_walk_spec(m, path)
    };

    let rev_path = Seq::new(path.len(), |i: int| path[(path.len() - 1 - i) as int]);
    assert(path.len() > 0);
    assert(rev_path.len() == path.len());
    assert(rev_path.len() > 0);
    assert(rev_path[0] == to);
    assert(rev_path[(rev_path.len() - 1) as int] == from);

    assert(mesh_half_edge_walk_spec(m, rev_path)) by {
        assert(rev_path.len() > 0);
        assert(forall|i: int| 0 <= i < rev_path.len() as int ==> 0 <= #[trigger] rev_path[i] < hcnt) by {
            assert forall|i: int|
                0 <= i < rev_path.len() as int implies 0 <= #[trigger] rev_path[i] < hcnt by {
                let j = path.len() - 1 - i;
                assert(0 <= j < path.len() as int);
                assert(rev_path[i] == path[j]);
                assert(0 <= path[j] < hcnt);
            };
        }
        assert(forall|i: int|
            0 <= i < (rev_path.len() as int) - 1
                ==> mesh_half_edge_adjacent_spec(m, rev_path[i], #[trigger] rev_path[i + 1])) by {
            assert forall|i: int|
                0 <= i < (rev_path.len() as int) - 1
                    implies mesh_half_edge_adjacent_spec(m, rev_path[i], #[trigger] rev_path[i + 1]) by {
                let j = path.len() - 2 - i;
                assert(0 <= j < (path.len() as int) - 1);
                assert(rev_path[i] == path[j + 1]);
                assert(rev_path[i + 1] == path[j]);
                assert(mesh_half_edge_adjacent_spec(m, path[j], path[j + 1]));
                if mesh_half_edge_direct_step_spec(m, path[j], path[j + 1]) {
                    assert(mesh_half_edge_adjacent_spec(m, path[j + 1], path[j]));
                } else {
                    assert(mesh_half_edge_direct_step_spec(m, path[j + 1], path[j]));
                    assert(mesh_half_edge_adjacent_spec(m, path[j + 1], path[j]));
                }
                assert(mesh_half_edge_adjacent_spec(m, rev_path[i], rev_path[i + 1]));
            };
        }
    }

    assert(mesh_half_edge_connected_spec(m, to, from)) by {
        assert(exists|p: Seq<int>| {
            &&& 0 <= to < hcnt
            &&& 0 <= from < hcnt
            &&& 0 < p.len()
            &&& p[0] == to
            &&& p[(p.len() - 1) as int] == from
            &&& mesh_half_edge_walk_spec(m, p)
        }) by {
            let p = rev_path;
            assert(0 <= to < hcnt);
            assert(0 <= from < hcnt);
            assert(0 < p.len());
            assert(p[0] == to);
            assert(p[(p.len() - 1) as int] == from);
            assert(mesh_half_edge_walk_spec(m, p));
        };
    }
}

pub proof fn lemma_mesh_half_edge_walk_closed_set_contains_index(
    m: MeshModel,
    path: Seq<int>,
    i: int,
    in_set: Seq<bool>,
)
    requires
        in_set.len() == mesh_half_edge_count_spec(m),
        mesh_half_edge_walk_spec(m, path),
        0 <= i < path.len() as int,
        in_set[path[0]],
        forall|a: int, b: int|
            #![trigger in_set[a], mesh_half_edge_adjacent_spec(m, a, b)]
            0 <= a < mesh_half_edge_count_spec(m)
                && 0 <= b < mesh_half_edge_count_spec(m)
                && in_set[a]
                && mesh_half_edge_adjacent_spec(m, a, b)
                ==> in_set[b],
    ensures
        in_set[path[i]],
    decreases i,
{
    let hcnt = mesh_half_edge_count_spec(m);
    if i == 0 {
        assert(path[i] == path[0]);
        assert(in_set[path[i]]);
    } else {
        assert(0 <= i - 1 < path.len() as int);
        lemma_mesh_half_edge_walk_closed_set_contains_index(m, path, i - 1, in_set);

        let prev = path[(i - 1) as int];
        let cur = path[i];
        assert(0 <= prev < hcnt);
        assert(0 <= cur < hcnt);
        assert(i - 1 < path.len() as int - 1);
        let j = i - 1;
        assert(0 <= j < path.len() as int - 1);
        assert(mesh_half_edge_adjacent_spec(m, path[j], path[j + 1]));
        assert(j + 1 == i);
        assert(path[j] == path[(i - 1) as int]);
        assert(path[j + 1] == path[i]);
        assert(mesh_half_edge_adjacent_spec(m, prev, cur));
        assert(in_set[prev]);
        assert(in_set[cur]);
    }
}

pub proof fn lemma_mesh_half_edge_closed_set_contains_connected(
    m: MeshModel,
    rep: int,
    h: int,
    in_set: Seq<bool>,
)
    requires
        in_set.len() == mesh_half_edge_count_spec(m),
        0 <= rep < mesh_half_edge_count_spec(m),
        0 <= h < mesh_half_edge_count_spec(m),
        in_set[rep],
        forall|a: int, b: int|
            #![trigger in_set[a], mesh_half_edge_adjacent_spec(m, a, b)]
            0 <= a < mesh_half_edge_count_spec(m)
                && 0 <= b < mesh_half_edge_count_spec(m)
                && in_set[a]
                && mesh_half_edge_adjacent_spec(m, a, b)
                ==> in_set[b],
        mesh_half_edge_connected_spec(m, rep, h),
    ensures
        in_set[h],
{
    let hcnt = mesh_half_edge_count_spec(m);
    let path = choose|path: Seq<int>| {
        &&& 0 <= rep < hcnt
        &&& 0 <= h < hcnt
        &&& 0 < path.len()
        &&& path[0] == rep
        &&& path[(path.len() - 1) as int] == h
        &&& mesh_half_edge_walk_spec(m, path)
    };

    assert(path.len() > 0);
    assert(path[0] == rep);
    assert(in_set[path[0]]);
    assert(0 <= path.len() - 1);
    assert(path.len() - 1 < path.len());
    lemma_mesh_half_edge_walk_closed_set_contains_index(m, path, path.len() - 1, in_set);
    assert(path[(path.len() - 1) as int] == h);
    assert(in_set[h]);
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

pub open spec fn mesh_half_edge_component_representative_connected_at_spec(
    m: MeshModel,
    components: Seq<Vec<usize>>,
    c: int,
) -> bool {
    &&& 0 <= c < components.len() as int
    &&& components[c]@.len() > 0
    &&& forall|h: int|
        #![trigger mesh_half_edge_component_contains_spec(m, components, c, h)]
        mesh_half_edge_component_contains_spec(m, components, c, h)
            ==> mesh_half_edge_connected_spec(
                m,
                mesh_half_edge_component_entry_spec(components, c, 0),
                h,
            )
}

pub open spec fn mesh_half_edge_components_representative_connected_spec(
    m: MeshModel,
    components: Seq<Vec<usize>>,
) -> bool {
    forall|c: int|
        #![trigger components[c]@]
        0 <= c < components.len() as int
            ==> mesh_half_edge_component_representative_connected_at_spec(m, components, c)
}

pub open spec fn mesh_half_edge_component_representative_minimal_at_spec(
    m: MeshModel,
    components: Seq<Vec<usize>>,
    c: int,
) -> bool {
    &&& 0 <= c < components.len() as int
    &&& components[c]@.len() > 0
    &&& forall|h: int|
        #![trigger mesh_half_edge_component_contains_spec(m, components, c, h)]
        mesh_half_edge_component_contains_spec(m, components, c, h)
            ==> mesh_half_edge_component_entry_spec(components, c, 0) <= h
}

pub open spec fn mesh_half_edge_components_representative_minimal_spec(
    m: MeshModel,
    components: Seq<Vec<usize>>,
) -> bool {
    forall|c: int|
        #![trigger components[c]@]
        0 <= c < components.len() as int
            ==> mesh_half_edge_component_representative_minimal_at_spec(m, components, c)
}

pub open spec fn mesh_half_edge_component_representative_complete_at_spec(
    m: MeshModel,
    components: Seq<Vec<usize>>,
    c: int,
) -> bool {
    &&& 0 <= c < components.len() as int
    &&& components[c]@.len() > 0
    &&& forall|h: int|
        #![trigger mesh_half_edge_connected_spec(m, mesh_half_edge_component_entry_spec(components, c, 0), h)]
        0 <= h < mesh_half_edge_count_spec(m)
            && mesh_half_edge_connected_spec(m, mesh_half_edge_component_entry_spec(components, c, 0), h)
            ==> mesh_half_edge_component_contains_spec(m, components, c, h)
}

pub open spec fn mesh_half_edge_components_representative_complete_spec(
    m: MeshModel,
    components: Seq<Vec<usize>>,
) -> bool {
    forall|c: int|
        #![trigger components[c]@]
        0 <= c < components.len() as int
            ==> mesh_half_edge_component_representative_complete_at_spec(m, components, c)
}

pub open spec fn mesh_half_edge_components_partition_neighbor_closed_spec(
    m: MeshModel,
    components: Seq<Vec<usize>>,
) -> bool {
    &&& mesh_half_edge_components_partition_spec(m, components)
    &&& mesh_half_edge_components_neighbor_closed_spec(m, components)
    &&& mesh_half_edge_components_representative_connected_spec(m, components)
    &&& mesh_half_edge_components_representative_minimal_spec(m, components)
    &&& mesh_half_edge_components_representative_complete_spec(m, components)
}

pub open spec fn mesh_component_count_partition_witness_spec(m: MeshModel, count: int) -> bool {
    exists|components: Seq<Vec<usize>>| {
        &&& mesh_half_edge_components_partition_neighbor_closed_spec(m, components)
        &&& count == components.len() as int
    }
}

pub proof fn lemma_component_partition_entry_is_model_representative(
    m: MeshModel,
    components: Seq<Vec<usize>>,
    c: int,
)
    requires
        mesh_half_edge_components_partition_neighbor_closed_spec(m, components),
        0 <= c < components.len() as int,
    ensures
        mesh_component_representative_spec(m, mesh_half_edge_component_entry_spec(components, c, 0)),
{
    let hcnt = mesh_half_edge_count_spec(m);
    let r = mesh_half_edge_component_entry_spec(components, c, 0);

    assert(components[c]@.len() > 0);
    assert(0 <= 0 < components[c]@.len() as int);
    assert(0 <= r < hcnt);

    assert(forall|h: int| 0 <= h < hcnt && mesh_half_edge_connected_spec(m, r, h) ==> r <= h) by {
        assert forall|h: int| 0 <= h < hcnt && mesh_half_edge_connected_spec(m, r, h) implies r <= h by {
            assert(mesh_half_edge_component_representative_complete_at_spec(m, components, c));
            assert(mesh_half_edge_component_contains_spec(m, components, c, h));
            assert(mesh_half_edge_component_representative_minimal_at_spec(m, components, c));
            assert(r <= h);
        };
    }

    assert(mesh_component_representative_spec(m, r));
}

pub proof fn lemma_model_representative_in_partition_representative_set(
    m: MeshModel,
    components: Seq<Vec<usize>>,
    r: int,
)
    requires
        mesh_half_edge_components_partition_neighbor_closed_spec(m, components),
        0 <= r < mesh_half_edge_count_spec(m),
        mesh_component_representative_spec(m, r),
    ensures
        vstd::set_lib::set_int_range(0, components.len() as int).map(
            |c: int| mesh_half_edge_component_entry_spec(components, c, 0),
        ).contains(r),
{
    let hcnt = mesh_half_edge_count_spec(m);
    let reps = vstd::set_lib::set_int_range(0, components.len() as int).map(
        |c: int| mesh_half_edge_component_entry_spec(components, c, 0),
    );

    assert(mesh_half_edge_components_cover_all_spec(m, components));
    assert(mesh_half_edge_has_component_spec(m, components, r));
    let c = choose|c: int| {
        &&& 0 <= c < components.len() as int
        &&& mesh_half_edge_component_contains_spec(m, components, c, r)
    };
    assert(0 <= c < components.len() as int);
    assert(mesh_half_edge_component_contains_spec(m, components, c, r));

    let cr = mesh_half_edge_component_entry_spec(components, c, 0);
    assert(mesh_half_edge_component_representative_connected_at_spec(m, components, c));
    assert(mesh_half_edge_connected_spec(m, cr, r));
    lemma_mesh_half_edge_connected_symmetric(m, cr, r);
    assert(mesh_half_edge_connected_spec(m, r, cr));

    assert(r <= cr);
    assert(mesh_half_edge_component_representative_minimal_at_spec(m, components, c));
    assert(cr <= r);
    assert(cr == r);

    assert(vstd::set_lib::set_int_range(0, components.len() as int).contains(c));
    assert(exists|cp: int|
        vstd::set_lib::set_int_range(0, components.len() as int).contains(cp)
            && r == mesh_half_edge_component_entry_spec(components, cp, 0));
    assert(reps.contains(r));
}

pub proof fn lemma_component_partition_count_matches_model_component_count(
    m: MeshModel,
    components: Seq<Vec<usize>>,
)
    requires
        mesh_half_edge_components_partition_neighbor_closed_spec(m, components),
    ensures
        components.len() as int == mesh_component_count_spec(m),
{
    let hcnt = mesh_half_edge_count_spec(m);
    let index_set = vstd::set_lib::set_int_range(0, components.len() as int);
    let rep_set = index_set.map(|c: int| mesh_half_edge_component_entry_spec(components, c, 0));
    let model_set = Set::new(|r: int| 0 <= r < hcnt && mesh_component_representative_spec(m, r));

    vstd::set_lib::lemma_int_range(0, components.len() as int);

    assert(vstd::relations::injective_on(
        |c: int| mesh_half_edge_component_entry_spec(components, c, 0),
        index_set,
    )) by {
        assert forall|c1: int, c2: int|
            index_set.contains(c1)
                && index_set.contains(c2)
                && mesh_half_edge_component_entry_spec(components, c1, 0)
                    == mesh_half_edge_component_entry_spec(components, c2, 0)
                implies c1 == c2 by {
            let h = mesh_half_edge_component_entry_spec(components, c1, 0);
            assert(0 <= c1 < components.len() as int);
            assert(0 <= c2 < components.len() as int);
            assert(components[c1]@.len() > 0);
            assert(components[c2]@.len() > 0);
            assert(0 <= 0 < components[c1]@.len() as int);
            assert(0 <= 0 < components[c2]@.len() as int);
            assert(mesh_half_edge_component_contains_spec(m, components, c1, h));
            assert(mesh_half_edge_component_contains_spec(m, components, c2, h));
            assert(c1 == c2);
        };
    };

    vstd::set_lib::lemma_map_size(index_set, rep_set, |c: int| mesh_half_edge_component_entry_spec(components, c, 0));
    assert(rep_set.finite());
    assert(index_set.len() == rep_set.len());
    assert(index_set.len() == components.len() as int);
    assert(rep_set.len() as int == components.len() as int);

    assert(rep_set.subset_of(model_set)) by {
        assert forall|r: int| rep_set.contains(r) implies model_set.contains(r) by {
            let c = choose|c: int| {
                &&& index_set.contains(c)
                &&& r == mesh_half_edge_component_entry_spec(components, c, 0)
            };
            assert(index_set.contains(c));
            assert(0 <= c < components.len() as int);
            assert(r == mesh_half_edge_component_entry_spec(components, c, 0));
            lemma_component_partition_entry_is_model_representative(m, components, c);
            assert(mesh_component_representative_spec(m, mesh_half_edge_component_entry_spec(components, c, 0)));
            assert(mesh_component_representative_spec(m, r));
            assert(0 <= r < hcnt);
        };
    };

    assert(model_set.subset_of(rep_set)) by {
        assert forall|r: int| model_set.contains(r) implies rep_set.contains(r) by {
            assert(0 <= r < hcnt && mesh_component_representative_spec(m, r));
            lemma_model_representative_in_partition_representative_set(m, components, r);
            assert(rep_set.contains(r));
        };
    };

    vstd::set_lib::lemma_set_subset_finite(rep_set, model_set);
    vstd::set_lib::lemma_len_subset(rep_set, model_set);
    vstd::set_lib::lemma_len_subset(model_set, rep_set);
    assert(rep_set.len() == model_set.len());
    assert(model_set.len() as int == mesh_component_count_spec(m));
    assert(components.len() as int == mesh_component_count_spec(m));
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
        &&& chis.len() as int == mesh_component_count_spec(m)
    }
}

pub open spec fn mesh_euler_formula_closed_components_partition_witness_spec(m: MeshModel) -> bool {
    exists|components: Seq<Vec<usize>>, chis: Seq<isize>| {
        &&& mesh_half_edge_components_partition_neighbor_closed_spec(m, components)
        &&& mesh_euler_characteristics_per_component_spec(m, components, chis)
        &&& chis.len() as int == mesh_component_count_spec(m)
        &&& chis.len() > 0
        &&& forall|c: int|
            #![trigger chis[c]]
            0 <= c < chis.len() as int ==> chis[c] as int == 2
    }
}

/// Closed-component Euler gate model: the mesh has a checked half-edge
/// partition witness whose per-component Euler characteristics are all `2`
/// (with an explicit non-empty component list).
pub open spec fn mesh_euler_closed_components_spec(m: MeshModel) -> bool {
    mesh_euler_formula_closed_components_partition_witness_spec(m)
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

#[derive(Structural, Copy, Clone, PartialEq, Eq)]
pub struct StructuralValidityGateWitness {
    pub api_ok: bool,
    pub vertex_count_positive: bool,
    pub edge_count_positive: bool,
    pub face_count_positive: bool,
    pub half_edge_count_positive: bool,
    pub index_bounds_ok: bool,
    pub twin_involution_ok: bool,
    pub prev_next_inverse_ok: bool,
    pub face_cycles_ok: bool,
    pub no_degenerate_edges_ok: bool,
    pub vertex_manifold_ok: bool,
    pub edge_two_half_edges_ok: bool,
}

pub open spec fn structural_validity_gate_witness_spec(w: StructuralValidityGateWitness) -> bool {
    w.api_ok == (
        w.vertex_count_positive
            && w.edge_count_positive
            && w.face_count_positive
            && w.half_edge_count_positive
            && w.index_bounds_ok
            && w.twin_involution_ok
            && w.prev_next_inverse_ok
            && w.face_cycles_ok
            && w.no_degenerate_edges_ok
            && w.vertex_manifold_ok
            && w.edge_two_half_edges_ok
    )
}

pub open spec fn structural_validity_gate_model_link_spec(
    m: MeshModel,
    w: StructuralValidityGateWitness,
) -> bool {
    &&& (w.vertex_count_positive ==> mesh_vertex_count_spec(m) > 0)
    &&& (w.edge_count_positive ==> mesh_edge_count_spec(m) > 0)
    &&& (w.face_count_positive ==> mesh_face_count_spec(m) > 0)
    &&& (w.half_edge_count_positive ==> mesh_half_edge_count_spec(m) > 0)
    &&& (w.index_bounds_ok ==> mesh_index_bounds_spec(m))
    &&& (w.twin_involution_ok ==> from_face_cycles_twin_assignment_total_involution_spec(m))
    &&& (w.prev_next_inverse_ok ==> mesh_prev_next_inverse_spec(m))
    &&& (w.face_cycles_ok ==> mesh_face_next_cycles_spec(m))
    &&& (w.no_degenerate_edges_ok ==> mesh_no_degenerate_edges_spec(m))
    &&& (w.vertex_manifold_ok ==> mesh_vertex_manifold_single_cycle_spec(m))
    &&& (w.edge_two_half_edges_ok ==> mesh_edge_exactly_two_half_edges_spec(m))
}

#[derive(Structural, Copy, Clone, PartialEq, Eq)]
pub struct ValidityGateWitness {
    pub api_ok: bool,
    pub structural_ok: bool,
    pub euler_ok: bool,
}

pub open spec fn validity_gate_witness_spec(w: ValidityGateWitness) -> bool {
    w.api_ok == (w.structural_ok && w.euler_ok)
}

#[derive(Structural, Copy, Clone, PartialEq, Eq)]
pub struct EulerFormulaClosedComponentsGateWitness {
    pub api_ok: bool,
    pub chis_non_empty: bool,
    pub chis_all_two: bool,
}

pub open spec fn euler_formula_closed_components_gate_witness_spec(
    w: EulerFormulaClosedComponentsGateWitness,
) -> bool {
    w.api_ok == (w.chis_non_empty && w.chis_all_two)
}

pub open spec fn euler_formula_closed_components_gate_model_link_spec(
    m: MeshModel,
    w: EulerFormulaClosedComponentsGateWitness,
) -> bool {
    w.api_ok ==> mesh_euler_closed_components_spec(m)
}

pub open spec fn validity_gate_model_link_spec(m: MeshModel, w: ValidityGateWitness) -> bool {
    &&& (w.structural_ok ==> exists|sw: StructuralValidityGateWitness| {
        &&& structural_validity_gate_witness_spec(sw)
        &&& structural_validity_gate_model_link_spec(m, sw)
        &&& sw.api_ok == w.structural_ok
    })
    &&& (w.euler_ok ==> exists|ew: EulerFormulaClosedComponentsGateWitness| {
        &&& euler_formula_closed_components_gate_witness_spec(ew)
        &&& euler_formula_closed_components_gate_model_link_spec(m, ew)
        &&& ew.api_ok == w.euler_ok
    })
}

pub proof fn lemma_structural_validity_gate_witness_api_ok_implies_mesh_structurally_valid(
    m: MeshModel,
    w: StructuralValidityGateWitness,
)
    requires
        structural_validity_gate_witness_spec(w),
        structural_validity_gate_model_link_spec(m, w),
        w.api_ok,
    ensures
        mesh_structurally_valid_spec(m),
{
    assert(w.api_ok == (
        w.vertex_count_positive
            && w.edge_count_positive
            && w.face_count_positive
            && w.half_edge_count_positive
            && w.index_bounds_ok
            && w.twin_involution_ok
            && w.prev_next_inverse_ok
            && w.face_cycles_ok
            && w.no_degenerate_edges_ok
            && w.vertex_manifold_ok
            && w.edge_two_half_edges_ok
    ));
    assert(
        w.vertex_count_positive
            && w.edge_count_positive
            && w.face_count_positive
            && w.half_edge_count_positive
            && w.index_bounds_ok
            && w.twin_involution_ok
            && w.prev_next_inverse_ok
            && w.face_cycles_ok
            && w.no_degenerate_edges_ok
            && w.vertex_manifold_ok
            && w.edge_two_half_edges_ok
    );
    assert(w.vertex_count_positive ==> mesh_vertex_count_spec(m) > 0);
    assert(w.edge_count_positive ==> mesh_edge_count_spec(m) > 0);
    assert(w.face_count_positive ==> mesh_face_count_spec(m) > 0);
    assert(w.half_edge_count_positive ==> mesh_half_edge_count_spec(m) > 0);
    assert(w.index_bounds_ok ==> mesh_index_bounds_spec(m));
    assert(w.twin_involution_ok ==> from_face_cycles_twin_assignment_total_involution_spec(m));
    assert(w.prev_next_inverse_ok ==> mesh_prev_next_inverse_spec(m));
    assert(w.face_cycles_ok ==> mesh_face_next_cycles_spec(m));
    assert(w.no_degenerate_edges_ok ==> mesh_no_degenerate_edges_spec(m));
    assert(w.vertex_manifold_ok ==> mesh_vertex_manifold_single_cycle_spec(m));
    assert(w.edge_two_half_edges_ok ==> mesh_edge_exactly_two_half_edges_spec(m));

    assert(mesh_vertex_count_spec(m) > 0);
    assert(mesh_edge_count_spec(m) > 0);
    assert(mesh_face_count_spec(m) > 0);
    assert(mesh_half_edge_count_spec(m) > 0);
    assert(mesh_index_bounds_spec(m));
    assert(from_face_cycles_twin_assignment_total_involution_spec(m));
    assert(mesh_twin_involution_spec(m));
    assert(mesh_prev_next_inverse_spec(m));
    assert(mesh_face_next_cycles_spec(m));
    assert(mesh_no_degenerate_edges_spec(m));
    assert(mesh_vertex_manifold_single_cycle_spec(m));
    assert(mesh_edge_exactly_two_half_edges_spec(m));
    assert(mesh_structurally_valid_spec(m));
}

pub proof fn lemma_validity_gate_witness_api_ok_implies_mesh_valid(
    m: MeshModel,
    w: ValidityGateWitness,
)
    requires
        validity_gate_witness_spec(w),
        validity_gate_model_link_spec(m, w),
        w.api_ok,
    ensures
        mesh_valid_spec(m),
{
    assert(w.api_ok == (w.structural_ok && w.euler_ok));
    assert(w.structural_ok && w.euler_ok);

    assert(w.structural_ok ==> exists|sw: StructuralValidityGateWitness| {
        &&& structural_validity_gate_witness_spec(sw)
        &&& structural_validity_gate_model_link_spec(m, sw)
        &&& sw.api_ok == w.structural_ok
    });
    assert(exists|sw: StructuralValidityGateWitness| {
        &&& structural_validity_gate_witness_spec(sw)
        &&& structural_validity_gate_model_link_spec(m, sw)
        &&& sw.api_ok == w.structural_ok
    });
    let sw = choose|sw: StructuralValidityGateWitness| {
        &&& structural_validity_gate_witness_spec(sw)
        &&& structural_validity_gate_model_link_spec(m, sw)
        &&& sw.api_ok == w.structural_ok
    };
    assert(sw.api_ok == w.structural_ok);
    assert(sw.api_ok);
    lemma_structural_validity_gate_witness_api_ok_implies_mesh_structurally_valid(m, sw);
    assert(mesh_structurally_valid_spec(m));

    assert(w.euler_ok ==> exists|ew: EulerFormulaClosedComponentsGateWitness| {
        &&& euler_formula_closed_components_gate_witness_spec(ew)
        &&& euler_formula_closed_components_gate_model_link_spec(m, ew)
        &&& ew.api_ok == w.euler_ok
    });
    assert(exists|ew: EulerFormulaClosedComponentsGateWitness| {
        &&& euler_formula_closed_components_gate_witness_spec(ew)
        &&& euler_formula_closed_components_gate_model_link_spec(m, ew)
        &&& ew.api_ok == w.euler_ok
    });
    let ew = choose|ew: EulerFormulaClosedComponentsGateWitness| {
        &&& euler_formula_closed_components_gate_witness_spec(ew)
        &&& euler_formula_closed_components_gate_model_link_spec(m, ew)
        &&& ew.api_ok == w.euler_ok
    };
    assert(ew.api_ok == w.euler_ok);
    assert(ew.api_ok);
    assert(euler_formula_closed_components_gate_model_link_spec(m, ew));
    assert(ew.api_ok ==> mesh_euler_closed_components_spec(m));
    assert(mesh_euler_closed_components_spec(m));

    assert(mesh_valid_spec(m));
}

pub open spec fn mesh_counts_spec(
    m: MeshModel,
    vertex_count: int,
    edge_count: int,
    face_count: int,
    half_edge_count: int,
) -> bool {
    &&& mesh_vertex_count_spec(m) == vertex_count
    &&& mesh_edge_count_spec(m) == edge_count
    &&& mesh_face_count_spec(m) == face_count
    &&& mesh_half_edge_count_spec(m) == half_edge_count
}

pub open spec fn mesh_tetrahedron_counts_spec(m: MeshModel) -> bool {
    mesh_counts_spec(m, 4, 6, 4, 12)
}

pub open spec fn mesh_cube_counts_spec(m: MeshModel) -> bool {
    mesh_counts_spec(m, 8, 12, 6, 24)
}

pub open spec fn mesh_triangular_prism_counts_spec(m: MeshModel) -> bool {
    mesh_counts_spec(m, 6, 9, 5, 18)
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

pub open spec fn from_face_cycles_no_self_loop_edges_spec(face_cycles: Seq<Seq<int>>) -> bool {
    forall|f: int, i: int|
        #![trigger input_face_from_vertex_spec(face_cycles, f, i), input_face_to_vertex_spec(face_cycles, f, i)]
        input_face_local_index_valid_spec(face_cycles, f, i)
            ==> input_face_from_vertex_spec(face_cycles, f, i)
                != input_face_to_vertex_spec(face_cycles, f, i)
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

pub open spec fn from_face_cycles_vertex_has_incident_spec(
    face_cycles: Seq<Seq<int>>,
    v: int,
) -> bool {
    exists|f: int, i: int| {
        &&& input_face_local_index_valid_spec(face_cycles, f, i)
        &&& #[trigger] input_face_from_vertex_spec(face_cycles, f, i) == v
    }
}

pub open spec fn from_face_cycles_no_isolated_vertices_spec(vertex_count: int, face_cycles: Seq<Seq<int>>) -> bool {
    forall|v: int|
        #![trigger from_face_cycles_vertex_has_incident_spec(face_cycles, v)]
        0 <= v < vertex_count ==> from_face_cycles_vertex_has_incident_spec(face_cycles, v)
}

pub open spec fn input_face_local_index_before_spec(
    face_cycles: Seq<Seq<int>>,
    f: int,
    i: int,
    face_limit: int,
    local_limit: int,
) -> bool {
    &&& input_face_local_index_valid_spec(face_cycles, f, i)
    &&& (f < face_limit || (f == face_limit && i < local_limit))
}

pub open spec fn from_face_cycles_oriented_edge_match_spec(
    face_cycles: Seq<Seq<int>>,
    f1: int,
    i1: int,
    f2: int,
    i2: int,
) -> bool {
    &&& input_face_from_vertex_spec(face_cycles, f1, i1) == input_face_from_vertex_spec(face_cycles, f2, i2)
    &&& input_face_to_vertex_spec(face_cycles, f1, i1) == input_face_to_vertex_spec(face_cycles, f2, i2)
}

pub open spec fn from_face_cycles_oriented_edge_not_in_prefix_spec(
    face_cycles: Seq<Seq<int>>,
    f: int,
    i: int,
    face_limit: int,
    local_limit: int,
) -> bool {
    forall|fp: int, ip: int|
        #![trigger input_face_local_index_before_spec(face_cycles, fp, ip, face_limit, local_limit)]
        input_face_local_index_before_spec(face_cycles, fp, ip, face_limit, local_limit)
            ==> !from_face_cycles_oriented_edge_match_spec(face_cycles, f, i, fp, ip)
}

pub open spec fn from_face_cycles_no_duplicate_oriented_edges_prefix_spec(
    face_cycles: Seq<Seq<int>>,
    face_limit: int,
    local_limit: int,
) -> bool {
    forall|f1: int, i1: int, f2: int, i2: int|
        #![trigger input_face_local_index_before_spec(face_cycles, f1, i1, face_limit, local_limit), input_face_local_index_before_spec(face_cycles, f2, i2, face_limit, local_limit)]
        input_face_local_index_before_spec(face_cycles, f1, i1, face_limit, local_limit)
            && input_face_local_index_before_spec(face_cycles, f2, i2, face_limit, local_limit)
            && from_face_cycles_oriented_edge_match_spec(face_cycles, f1, i1, f2, i2)
            ==> f1 == f2 && i1 == i2
}

pub open spec fn from_face_cycles_all_oriented_edges_have_twin_prefix_spec(
    face_cycles: Seq<Seq<int>>,
    face_limit: int,
    local_limit: int,
) -> bool {
    forall|f: int, i: int|
        #![trigger input_face_local_index_before_spec(face_cycles, f, i, face_limit, local_limit)]
        input_face_local_index_before_spec(face_cycles, f, i, face_limit, local_limit) ==> exists|g: int, j: int| {
            &&& input_face_local_index_valid_spec(face_cycles, g, j)
            &&& #[trigger] input_face_from_vertex_spec(face_cycles, g, j)
                == input_face_to_vertex_spec(face_cycles, f, i)
            &&& #[trigger] input_face_to_vertex_spec(face_cycles, g, j)
                == input_face_from_vertex_spec(face_cycles, f, i)
        }
}

pub proof fn lemma_from_face_cycles_no_duplicate_prefix_complete(face_cycles: Seq<Seq<int>>)
    ensures
        from_face_cycles_no_duplicate_oriented_edges_prefix_spec(
            face_cycles,
            face_cycles.len() as int,
            0,
        ) ==> from_face_cycles_no_duplicate_oriented_edges_spec(face_cycles),
{
    if from_face_cycles_no_duplicate_oriented_edges_prefix_spec(face_cycles, face_cycles.len() as int, 0) {
        assert(from_face_cycles_no_duplicate_oriented_edges_spec(face_cycles)) by {
            assert forall|f1: int, i1: int, f2: int, i2: int|
                input_face_local_index_valid_spec(face_cycles, f1, i1)
                    && input_face_local_index_valid_spec(face_cycles, f2, i2)
                    && input_face_from_vertex_spec(face_cycles, f1, i1)
                        == input_face_from_vertex_spec(face_cycles, f2, i2)
                    && input_face_to_vertex_spec(face_cycles, f1, i1)
                        == input_face_to_vertex_spec(face_cycles, f2, i2)
                    implies f1 == f2 && i1 == i2 by {
                assert(input_face_local_index_before_spec(face_cycles, f1, i1, face_cycles.len() as int, 0));
                assert(input_face_local_index_before_spec(face_cycles, f2, i2, face_cycles.len() as int, 0));
                assert(from_face_cycles_oriented_edge_match_spec(face_cycles, f1, i1, f2, i2));
            };
        };
    }
}

pub open spec fn from_face_cycles_prefix_contains_vertex_spec(
    face_cycles: Seq<Seq<int>>,
    face_limit: int,
    local_limit: int,
    v: int,
) -> bool {
    exists|w: (int, int)| {
        &&& input_face_local_index_valid_spec(face_cycles, w.0, w.1)
        &&& (w.0 < face_limit || (w.0 == face_limit && w.1 < local_limit))
        &&& #[trigger] input_face_from_vertex_spec(face_cycles, w.0, w.1) == v
    }
}

pub proof fn lemma_from_face_cycles_prefix_contains_vertex_step_local(
    face_cycles: Seq<Seq<int>>,
    face_limit: int,
    local_limit: int,
    v: int,
)
    ensures
        from_face_cycles_prefix_contains_vertex_spec(face_cycles, face_limit, local_limit, v)
            ==> from_face_cycles_prefix_contains_vertex_spec(face_cycles, face_limit, local_limit + 1, v),
{
    if from_face_cycles_prefix_contains_vertex_spec(face_cycles, face_limit, local_limit, v) {
        let w = choose|w: (int, int)| {
            &&& input_face_local_index_valid_spec(face_cycles, w.0, w.1)
            &&& (w.0 < face_limit || (w.0 == face_limit && w.1 < local_limit))
            &&& #[trigger] input_face_from_vertex_spec(face_cycles, w.0, w.1) == v
        };
        let f = w.0;
        let i = w.1;
        assert(exists|f2: int, i2: int| {
            &&& input_face_local_index_valid_spec(face_cycles, f2, i2)
            &&& (f2 < face_limit || (f2 == face_limit && i2 < local_limit + 1))
            &&& #[trigger] input_face_from_vertex_spec(face_cycles, f2, i2) == v
        }) by {
            assert(input_face_local_index_valid_spec(face_cycles, f, i));
            if f < face_limit {
            } else {
                assert(f == face_limit);
                assert(i < local_limit);
                assert(i < local_limit + 1);
            }
            assert(input_face_from_vertex_spec(face_cycles, f, i) == v);
        };
    }
}

pub proof fn lemma_from_face_cycles_prefix_contains_vertex_promote_face(
    face_cycles: Seq<Seq<int>>,
    face_limit: int,
    local_limit: int,
    v: int,
)
    ensures
        from_face_cycles_prefix_contains_vertex_spec(face_cycles, face_limit, local_limit, v)
            ==> from_face_cycles_prefix_contains_vertex_spec(face_cycles, face_limit + 1, 0, v),
{
    if from_face_cycles_prefix_contains_vertex_spec(face_cycles, face_limit, local_limit, v) {
        let w = choose|w: (int, int)| {
            &&& input_face_local_index_valid_spec(face_cycles, w.0, w.1)
            &&& (w.0 < face_limit || (w.0 == face_limit && w.1 < local_limit))
            &&& #[trigger] input_face_from_vertex_spec(face_cycles, w.0, w.1) == v
        };
        let f = w.0;
        let i = w.1;
        assert(exists|f2: int, i2: int| {
            &&& input_face_local_index_valid_spec(face_cycles, f2, i2)
            &&& (f2 < face_limit + 1 || (f2 == face_limit + 1 && i2 < 0))
            &&& #[trigger] input_face_from_vertex_spec(face_cycles, f2, i2) == v
        }) by {
            assert(input_face_local_index_valid_spec(face_cycles, f, i));
            if f < face_limit {
                assert(f < face_limit + 1);
            } else {
                assert(f == face_limit);
                assert(f < face_limit + 1);
            }
            assert(input_face_from_vertex_spec(face_cycles, f, i) == v);
        };
    }
}

pub proof fn lemma_from_face_cycles_prefix_contains_vertex_implies_contains(
    face_cycles: Seq<Seq<int>>,
    face_limit: int,
    local_limit: int,
    v: int,
)
    ensures
        from_face_cycles_prefix_contains_vertex_spec(face_cycles, face_limit, local_limit, v)
            ==> exists|f: int, i: int| {
                &&& input_face_local_index_valid_spec(face_cycles, f, i)
                &&& #[trigger] input_face_from_vertex_spec(face_cycles, f, i) == v
            },
{
    if from_face_cycles_prefix_contains_vertex_spec(face_cycles, face_limit, local_limit, v) {
        let w = choose|w: (int, int)| {
            &&& input_face_local_index_valid_spec(face_cycles, w.0, w.1)
            &&& (w.0 < face_limit || (w.0 == face_limit && w.1 < local_limit))
            &&& #[trigger] input_face_from_vertex_spec(face_cycles, w.0, w.1) == v
        };
        let f = w.0;
        let i = w.1;
        assert(exists|f2: int, i2: int| {
            &&& input_face_local_index_valid_spec(face_cycles, f2, i2)
            &&& #[trigger] input_face_from_vertex_spec(face_cycles, f2, i2) == v
        }) by {
            assert(input_face_local_index_valid_spec(face_cycles, f, i));
            assert(input_face_from_vertex_spec(face_cycles, f, i) == v);
        };
    }
}

pub open spec fn from_face_cycles_failure_spec(vertex_count: int, face_cycles: Seq<Seq<int>>) -> bool {
    !from_face_cycles_basic_input_spec(vertex_count, face_cycles)
        || !from_face_cycles_no_self_loop_edges_spec(face_cycles)
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

pub proof fn lemma_face_cycles_exec_to_model_face_entry_exec(
    face_cycles: &[Vec<usize>],
    f: usize,
    face: &Vec<usize>,
    i: usize,
)
    requires
        f < face_cycles.len(),
        *face == face_cycles@.index(f as int),
        i < face.len(),
    ensures
        face_cycles_exec_to_model_spec(face_cycles@)[f as int][i as int] == face@[i as int] as int,
{
    assert(face_cycles@.index(f as int) == face_cycles@[f as int]);
    assert(face_cycles@[f as int] == *face);
    assert(face_cycles_exec_to_model_spec(face_cycles@)[f as int]
        == Seq::new(face_cycles@[f as int]@.len(), |j: int| face_cycles@[f as int]@[j] as int));
    assert(face@.len() == face.len());
    assert(face_cycles@[f as int]@.len() == face@.len());
    assert(0 <= i as int);
    assert((i as int) < face_cycles@[f as int]@.len());
    assert(face_cycles_exec_to_model_spec(face_cycles@)[f as int][i as int]
        == face_cycles@[f as int]@[i as int] as int);
    assert(face_cycles@[f as int]@[i as int] == face@[i as int]);
}

pub proof fn lemma_face_cycles_exec_to_model_oriented_edge_exec(
    face_cycles: &[Vec<usize>],
    f: usize,
    face: &Vec<usize>,
    i: usize,
    next_i: usize,
)
    requires
        f < face_cycles.len(),
        *face == face_cycles@.index(f as int),
        i < face.len(),
        next_i == if i + 1 < face.len() { i + 1 } else { 0 },
    ensures
        input_face_local_index_valid_spec(face_cycles_exec_to_model_spec(face_cycles@), f as int, i as int),
        input_face_local_index_valid_spec(face_cycles_exec_to_model_spec(face_cycles@), f as int, next_i as int),
        input_face_from_vertex_spec(face_cycles_exec_to_model_spec(face_cycles@), f as int, i as int)
            == face@[i as int] as int,
        input_face_to_vertex_spec(face_cycles_exec_to_model_spec(face_cycles@), f as int, i as int)
            == face@[next_i as int] as int,
{
    let model_cycles = face_cycles_exec_to_model_spec(face_cycles@);
    let n = face.len();
    assert(n > 0);
    lemma_face_cycles_exec_to_model_face_len_exec(face_cycles, f, face, n);
    lemma_face_cycles_exec_to_model_face_entry_exec(face_cycles, f, face, i);
    lemma_face_cycles_exec_to_model_face_entry_exec(face_cycles, f, face, next_i);

    assert(model_cycles[f as int].len() == n as int);
    assert(0 <= i as int);
    assert((i as int) < (model_cycles[f as int].len() as int));
    assert(0 <= next_i as int);
    assert((next_i as int) < (model_cycles[f as int].len() as int));
    assert(input_face_local_index_valid_spec(model_cycles, f as int, i as int));
    assert(input_face_local_index_valid_spec(model_cycles, f as int, next_i as int));
    assert(input_face_from_vertex_spec(model_cycles, f as int, i as int) == face@[i as int] as int);

    if i + 1 < n {
        assert(next_i == i + 1);
        assert(input_face_next_local_index_spec(model_cycles, f as int, i as int) == i as int + 1);
    } else {
        assert(next_i == 0);
        assert(input_face_next_local_index_spec(model_cycles, f as int, i as int) == 0);
    }
    assert(input_face_to_vertex_spec(model_cycles, f as int, i as int)
        == model_cycles[f as int][next_i as int]);
    assert(model_cycles[f as int][next_i as int] == face@[next_i as int] as int);
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

pub open spec fn from_face_cycles_vertex_assignment_at_spec(
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
    f: int,
    i: int,
) -> bool {
    let h = input_face_half_edge_index_spec(face_cycles, f, i);
    m.half_edges[h].vertex == input_face_from_vertex_spec(face_cycles, f, i)
}

pub open spec fn from_face_cycles_vertex_assignment_coherent_spec(
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
) -> bool {
    forall|f: int, i: int|
        #![trigger m.half_edges[input_face_half_edge_index_spec(face_cycles, f, i)]]
        input_face_local_index_valid_spec(face_cycles, f, i)
            ==> from_face_cycles_vertex_assignment_at_spec(face_cycles, m, f, i)
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

pub open spec fn from_face_cycles_twin_endpoint_correspondence_at_spec(
    m: MeshModel,
    h: int,
) -> bool {
    let hcnt = mesh_half_edge_count_spec(m);
    let t = m.half_edges[h].twin;
    &&& 0 <= t < hcnt
    &&& mesh_half_edge_from_vertex_spec(m, t) == mesh_half_edge_to_vertex_spec(m, h)
    &&& mesh_half_edge_to_vertex_spec(m, t) == mesh_half_edge_from_vertex_spec(m, h)
}

pub open spec fn from_face_cycles_twin_endpoint_correspondence_spec(m: MeshModel) -> bool {
    let hcnt = mesh_half_edge_count_spec(m);
    forall|h: int|
        #![trigger m.half_edges[h].twin]
        0 <= h < hcnt ==> from_face_cycles_twin_endpoint_correspondence_at_spec(m, h)
}

pub open spec fn from_face_cycles_undirected_edge_pair_equivalent_spec(
    m: MeshModel,
    h1: int,
    h2: int,
) -> bool {
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

pub open spec fn from_face_cycles_undirected_edge_equivalence_spec(m: MeshModel) -> bool {
    let hcnt = mesh_half_edge_count_spec(m);
    forall|h1: int, h2: int|
        #![trigger from_face_cycles_undirected_edge_pair_equivalent_spec(m, h1, h2)]
        0 <= h1 < hcnt && 0 <= h2 < hcnt
            ==> from_face_cycles_undirected_edge_pair_equivalent_spec(m, h1, h2)
}

pub open spec fn from_face_cycles_counts_index_face_starts_spec(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
) -> bool {
    &&& mesh_vertex_count_spec(m) == vertex_count
    &&& mesh_face_count_spec(m) == face_cycles.len() as int
    &&& mesh_half_edge_count_spec(m) == input_half_edge_count_spec(face_cycles)
    &&& mesh_index_bounds_spec(m)
    &&& forall|f: int|
        #![trigger m.face_half_edges[f]]
        0 <= f < face_cycles.len() as int
            ==> m.face_half_edges[f] == input_face_cycle_start_spec(face_cycles, f)
}

pub open spec fn from_face_cycles_structural_core_spec(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
) -> bool {
    &&& from_face_cycles_basic_input_spec(vertex_count, face_cycles)
    &&& from_face_cycles_no_self_loop_edges_spec(face_cycles)
    &&& from_face_cycles_no_duplicate_oriented_edges_spec(face_cycles)
    &&& from_face_cycles_all_oriented_edges_have_twin_spec(face_cycles)
    &&& from_face_cycles_no_isolated_vertices_spec(vertex_count, face_cycles)
    &&& from_face_cycles_counts_index_face_starts_spec(vertex_count, face_cycles, m)
    &&& from_face_cycles_next_prev_face_coherent_spec(face_cycles, m)
    &&& from_face_cycles_vertex_assignment_coherent_spec(face_cycles, m)
    &&& from_face_cycles_twin_assignment_total_involution_spec(m)
    &&& from_face_cycles_twin_endpoint_correspondence_spec(m)
    &&& from_face_cycles_undirected_edge_equivalence_spec(m)
    &&& mesh_edge_exactly_two_half_edges_spec(m)
    &&& from_face_cycles_vertex_representatives_spec(m)
}

pub open spec fn from_face_cycles_success_spec(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
) -> bool {
    &&& from_face_cycles_basic_input_spec(vertex_count, face_cycles)
    &&& from_face_cycles_no_self_loop_edges_spec(face_cycles)
    &&& from_face_cycles_no_duplicate_oriented_edges_spec(face_cycles)
    &&& from_face_cycles_all_oriented_edges_have_twin_spec(face_cycles)
    &&& from_face_cycles_no_isolated_vertices_spec(vertex_count, face_cycles)
    &&& from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m)
    &&& from_face_cycles_vertex_representatives_spec(m)
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

pub proof fn lemma_from_face_cycles_incidence_implies_vertex_assignment_coherent(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
)
    ensures
        from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m)
            ==> from_face_cycles_vertex_assignment_coherent_spec(face_cycles, m),
{
    if from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m) {
        assert(from_face_cycles_vertex_assignment_coherent_spec(face_cycles, m));
    }
}

pub proof fn lemma_from_face_cycles_success_implies_vertex_assignment_coherent(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
)
    ensures
        from_face_cycles_success_spec(vertex_count, face_cycles, m)
            ==> from_face_cycles_vertex_assignment_coherent_spec(face_cycles, m),
{
    if from_face_cycles_success_spec(vertex_count, face_cycles, m) {
        assert(from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m));
        lemma_from_face_cycles_incidence_implies_vertex_assignment_coherent(vertex_count, face_cycles, m);
    }
}

pub proof fn lemma_from_face_cycles_incidence_implies_twin_endpoint_correspondence(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
)
    ensures
        from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m)
            ==> from_face_cycles_twin_endpoint_correspondence_spec(m),
{
    if from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m) {
        let hcnt = mesh_half_edge_count_spec(m);
        assert(forall|h: int|
            #![trigger m.half_edges[h].twin]
            0 <= h < hcnt ==> from_face_cycles_twin_endpoint_correspondence_at_spec(m, h)) by {
            assert forall|h: int|
                #![trigger m.half_edges[h].twin]
                0 <= h < hcnt implies from_face_cycles_twin_endpoint_correspondence_at_spec(m, h) by {
                let t = m.half_edges[h].twin;
                assert(0 <= t < hcnt);
                assert(mesh_half_edge_from_vertex_spec(m, t) == mesh_half_edge_to_vertex_spec(m, h));
                assert(mesh_half_edge_to_vertex_spec(m, t) == mesh_half_edge_from_vertex_spec(m, h));
                assert(from_face_cycles_twin_endpoint_correspondence_at_spec(m, h));
            };
        }
        assert(from_face_cycles_twin_endpoint_correspondence_spec(m));
    }
}

pub proof fn lemma_from_face_cycles_success_implies_twin_endpoint_correspondence(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
)
    ensures
        from_face_cycles_success_spec(vertex_count, face_cycles, m)
            ==> from_face_cycles_twin_endpoint_correspondence_spec(m),
{
    if from_face_cycles_success_spec(vertex_count, face_cycles, m) {
        assert(from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m));
        lemma_from_face_cycles_incidence_implies_twin_endpoint_correspondence(
            vertex_count,
            face_cycles,
            m,
        );
    }
}

pub proof fn lemma_from_face_cycles_incidence_implies_undirected_edge_equivalence(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
)
    ensures
        from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m)
            ==> from_face_cycles_undirected_edge_equivalence_spec(m),
{
    if from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m) {
        assert(from_face_cycles_undirected_edge_equivalence_spec(m));
    }
}

pub proof fn lemma_from_face_cycles_success_implies_undirected_edge_equivalence(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
)
    ensures
        from_face_cycles_success_spec(vertex_count, face_cycles, m)
            ==> from_face_cycles_undirected_edge_equivalence_spec(m),
{
    if from_face_cycles_success_spec(vertex_count, face_cycles, m) {
        assert(from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m));
        lemma_from_face_cycles_incidence_implies_undirected_edge_equivalence(
            vertex_count,
            face_cycles,
            m,
        );
    }
}

pub proof fn lemma_mesh_undirected_key_symmetric(a: int, b: int)
    ensures
        mesh_undirected_key_spec(a, b) == mesh_undirected_key_spec(b, a),
{
    if a <= b {
        if b <= a {
            assert(a == b);
            assert(mesh_undirected_key_spec(a, b) == (a, b));
            assert(mesh_undirected_key_spec(b, a) == (b, a));
        } else {
            assert(mesh_undirected_key_spec(a, b) == (a, b));
            assert(mesh_undirected_key_spec(b, a) == (a, b));
        }
    } else {
        assert(b <= a);
        assert(mesh_undirected_key_spec(a, b) == (b, a));
        if a <= b {
            assert(false);
        } else {
            assert(mesh_undirected_key_spec(b, a) == (b, a));
        }
    }
}

pub proof fn lemma_input_half_edge_index_covered_prefix(
    face_cycles: Seq<Seq<int>>,
    face_limit: int,
    h: int,
)
    requires
        0 <= face_limit <= face_cycles.len() as int,
        0 <= h < input_face_cycle_start_spec(face_cycles, face_limit),
    ensures
        exists|w: (int, int)| {
            &&& 0 <= w.0 < face_limit
            &&& input_face_local_index_valid_spec(face_cycles, w.0, w.1)
            &&& h == input_face_half_edge_index_spec(face_cycles, w.0, w.1)
        },
    decreases face_limit
{
    if face_limit == 0 {
        assert(input_face_cycle_start_spec(face_cycles, face_limit) == 0);
        assert(false);
    } else {
        let prev_face_limit = face_limit - 1;
        let prev_start = input_face_cycle_start_spec(face_cycles, prev_face_limit);
        let prev_len = face_cycles[prev_face_limit].len() as int;
        assert(input_face_cycle_start_spec(face_cycles, face_limit) == prev_start + prev_len);

        if h < prev_start {
            lemma_input_half_edge_index_covered_prefix(face_cycles, prev_face_limit, h);
            let w = choose|w: (int, int)| {
                &&& 0 <= w.0 < prev_face_limit
                &&& input_face_local_index_valid_spec(face_cycles, w.0, w.1)
                &&& h == input_face_half_edge_index_spec(face_cycles, w.0, w.1)
            };
            assert(exists|w2: (int, int)| {
                &&& 0 <= w2.0 < face_limit
                &&& input_face_local_index_valid_spec(face_cycles, w2.0, w2.1)
                &&& h == input_face_half_edge_index_spec(face_cycles, w2.0, w2.1)
            }) by {
                let w2 = (w.0, w.1);
                assert(0 <= w.0 < prev_face_limit);
                assert(prev_face_limit < face_limit);
                assert(0 <= w.0 < face_limit);
                assert(input_face_local_index_valid_spec(face_cycles, w.0, w.1));
                assert(h == input_face_half_edge_index_spec(face_cycles, w.0, w.1));
                assert(w2.0 == w.0);
                assert(w2.1 == w.1);
            };
        } else {
            let i = h - prev_start;
            assert(0 <= i);
            assert(i < prev_len);
            assert(0 <= prev_face_limit < face_limit);
            assert(input_face_local_index_valid_spec(face_cycles, prev_face_limit, i));
            assert(h == input_face_half_edge_index_spec(face_cycles, prev_face_limit, i));
            assert(exists|w2: (int, int)| {
                &&& 0 <= w2.0 < face_limit
                &&& input_face_local_index_valid_spec(face_cycles, w2.0, w2.1)
                &&& h == input_face_half_edge_index_spec(face_cycles, w2.0, w2.1)
            }) by {
                let w2 = (prev_face_limit, i);
                assert(0 <= prev_face_limit < face_limit);
                assert(input_face_local_index_valid_spec(face_cycles, prev_face_limit, i));
                assert(h == input_face_half_edge_index_spec(face_cycles, prev_face_limit, i));
                assert(w2.0 == prev_face_limit);
                assert(w2.1 == i);
            };
        }
    }
}

pub proof fn lemma_input_half_edge_index_covered(face_cycles: Seq<Seq<int>>, h: int)
    requires
        0 <= h < input_half_edge_count_spec(face_cycles),
    ensures
        exists|w: (int, int)| {
            &&& input_face_local_index_valid_spec(face_cycles, w.0, w.1)
            &&& h == input_face_half_edge_index_spec(face_cycles, w.0, w.1)
        },
{
    let face_limit = face_cycles.len() as int;
    lemma_input_half_edge_index_covered_prefix(face_cycles, face_limit, h);
    let w = choose|w: (int, int)| {
        &&& 0 <= w.0 < face_limit
        &&& input_face_local_index_valid_spec(face_cycles, w.0, w.1)
        &&& h == input_face_half_edge_index_spec(face_cycles, w.0, w.1)
    };
    assert(exists|w2: (int, int)| {
        &&& input_face_local_index_valid_spec(face_cycles, w2.0, w2.1)
        &&& h == input_face_half_edge_index_spec(face_cycles, w2.0, w2.1)
    }) by {
        assert(input_face_local_index_valid_spec(face_cycles, w.0, w.1));
        assert(h == input_face_half_edge_index_spec(face_cycles, w.0, w.1));
    };
}

pub proof fn lemma_input_face_next_local_index_valid(face_cycles: Seq<Seq<int>>, f: int, i: int)
    requires
        input_face_local_index_valid_spec(face_cycles, f, i),
    ensures
        input_face_local_index_valid_spec(
            face_cycles,
            f,
            input_face_next_local_index_spec(face_cycles, f, i),
        ),
{
    let n = face_cycles[f].len() as int;
    assert(0 <= i < n);
    assert(n > 0);
    let next_i = input_face_next_local_index_spec(face_cycles, f, i);
    if i + 1 < n {
        assert(next_i == i + 1);
        assert(0 <= next_i < n);
    } else {
        assert(next_i == 0);
        assert(0 <= next_i < n);
    }
}

pub proof fn lemma_from_face_cycles_incidence_oriented_edge_projection(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
    f: int,
    i: int,
)
    requires
        from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m),
        input_face_local_index_valid_spec(face_cycles, f, i),
    ensures
        mesh_half_edge_from_vertex_spec(m, input_face_half_edge_index_spec(face_cycles, f, i))
            == input_face_from_vertex_spec(face_cycles, f, i),
        mesh_half_edge_to_vertex_spec(m, input_face_half_edge_index_spec(face_cycles, f, i))
            == input_face_to_vertex_spec(face_cycles, f, i),
{
    let h = input_face_half_edge_index_spec(face_cycles, f, i);
    let next_i = input_face_next_local_index_spec(face_cycles, f, i);
    lemma_input_face_next_local_index_valid(face_cycles, f, i);

    assert(m.half_edges[h].vertex == input_face_from_vertex_spec(face_cycles, f, i));
    assert(m.half_edges[h].next == input_face_half_edge_index_spec(face_cycles, f, next_i));
    assert(m.half_edges[input_face_half_edge_index_spec(face_cycles, f, next_i)].vertex
        == input_face_from_vertex_spec(face_cycles, f, next_i));
    assert(input_face_to_vertex_spec(face_cycles, f, i)
        == input_face_from_vertex_spec(face_cycles, f, next_i));
}

pub proof fn lemma_from_face_cycles_success_implies_mesh_no_self_loop_half_edges(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
)
    ensures
        from_face_cycles_success_spec(vertex_count, face_cycles, m)
            ==> (forall|h: int|
                0 <= h < mesh_half_edge_count_spec(m)
                    ==> mesh_half_edge_from_vertex_spec(m, h) != mesh_half_edge_to_vertex_spec(m, h)),
{
    if from_face_cycles_success_spec(vertex_count, face_cycles, m) {
        assert(from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m));
        assert(from_face_cycles_no_self_loop_edges_spec(face_cycles));
        assert(mesh_half_edge_count_spec(m) == input_half_edge_count_spec(face_cycles));
        let hcnt = mesh_half_edge_count_spec(m);

        assert(forall|h: int|
            0 <= h < hcnt
                ==> mesh_half_edge_from_vertex_spec(m, h) != mesh_half_edge_to_vertex_spec(m, h)) by {
            assert forall|h: int|
                0 <= h < hcnt implies mesh_half_edge_from_vertex_spec(m, h)
                    != mesh_half_edge_to_vertex_spec(m, h) by {
                lemma_input_half_edge_index_covered(face_cycles, h);
                let w = choose|w: (int, int)| {
                    &&& input_face_local_index_valid_spec(face_cycles, w.0, w.1)
                    &&& h == input_face_half_edge_index_spec(face_cycles, w.0, w.1)
                };
                let f = w.0;
                let i = w.1;
                assert(input_face_local_index_valid_spec(face_cycles, f, i));
                assert(h == input_face_half_edge_index_spec(face_cycles, f, i));
                lemma_from_face_cycles_incidence_oriented_edge_projection(
                    vertex_count,
                    face_cycles,
                    m,
                    f,
                    i,
                );
                assert(mesh_half_edge_from_vertex_spec(m, h)
                    == input_face_from_vertex_spec(face_cycles, f, i));
                assert(mesh_half_edge_to_vertex_spec(m, h)
                    == input_face_to_vertex_spec(face_cycles, f, i));
                assert(input_face_from_vertex_spec(face_cycles, f, i)
                    != input_face_to_vertex_spec(face_cycles, f, i));
            };
        };
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(600)]
pub proof fn lemma_from_face_cycles_success_implies_oriented_half_edge_unique(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
    h1: int,
    h2: int,
)
    requires
        from_face_cycles_success_spec(vertex_count, face_cycles, m),
        0 <= h1 < mesh_half_edge_count_spec(m),
        0 <= h2 < mesh_half_edge_count_spec(m),
        mesh_half_edge_from_vertex_spec(m, h1) == mesh_half_edge_from_vertex_spec(m, h2),
        mesh_half_edge_to_vertex_spec(m, h1) == mesh_half_edge_to_vertex_spec(m, h2),
    ensures
        h1 == h2,
{
    assert(from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m));
    assert(from_face_cycles_no_duplicate_oriented_edges_spec(face_cycles));
    assert(mesh_half_edge_count_spec(m) == input_half_edge_count_spec(face_cycles));

    lemma_input_half_edge_index_covered(face_cycles, h1);
    lemma_input_half_edge_index_covered(face_cycles, h2);
    let w1 = choose|w: (int, int)| {
        &&& input_face_local_index_valid_spec(face_cycles, w.0, w.1)
        &&& h1 == input_face_half_edge_index_spec(face_cycles, w.0, w.1)
    };
    let w2 = choose|w: (int, int)| {
        &&& input_face_local_index_valid_spec(face_cycles, w.0, w.1)
        &&& h2 == input_face_half_edge_index_spec(face_cycles, w.0, w.1)
    };
    let f1 = w1.0;
    let i1 = w1.1;
    let f2 = w2.0;
    let i2 = w2.1;

    assert(input_face_local_index_valid_spec(face_cycles, f1, i1));
    assert(input_face_local_index_valid_spec(face_cycles, f2, i2));
    assert(h1 == input_face_half_edge_index_spec(face_cycles, f1, i1));
    assert(h2 == input_face_half_edge_index_spec(face_cycles, f2, i2));

    lemma_from_face_cycles_incidence_oriented_edge_projection(vertex_count, face_cycles, m, f1, i1);
    lemma_from_face_cycles_incidence_oriented_edge_projection(vertex_count, face_cycles, m, f2, i2);
    assert(mesh_half_edge_from_vertex_spec(m, h1) == input_face_from_vertex_spec(face_cycles, f1, i1));
    assert(mesh_half_edge_to_vertex_spec(m, h1) == input_face_to_vertex_spec(face_cycles, f1, i1));
    assert(mesh_half_edge_from_vertex_spec(m, h2) == input_face_from_vertex_spec(face_cycles, f2, i2));
    assert(mesh_half_edge_to_vertex_spec(m, h2) == input_face_to_vertex_spec(face_cycles, f2, i2));

    assert(input_face_from_vertex_spec(face_cycles, f1, i1)
        == input_face_from_vertex_spec(face_cycles, f2, i2));
    assert(input_face_to_vertex_spec(face_cycles, f1, i1)
        == input_face_to_vertex_spec(face_cycles, f2, i2));
    assert(f1 == f2 && i1 == i2);
    assert(h1 == input_face_half_edge_index_spec(face_cycles, f1, i1));
    assert(h2 == input_face_half_edge_index_spec(face_cycles, f2, i2));
}

pub proof fn lemma_undirected_key_equal_non_self_loop_implies_oriented_or_reversed(
    a: int,
    b: int,
    c: int,
    d: int,
)
    requires
        mesh_undirected_key_spec(a, b) == mesh_undirected_key_spec(c, d),
        a != b,
        c != d,
    ensures
        (a == c && b == d) || (a == d && b == c),
{
    if a <= b {
        assert(mesh_undirected_key_spec(a, b) == (a, b));
        assert(mesh_undirected_key_spec(c, d) == (a, b));
        if c <= d {
            assert(mesh_undirected_key_spec(c, d) == (c, d));
            assert(c == a && d == b);
        } else {
            assert(mesh_undirected_key_spec(c, d) == (d, c));
            assert(d == a && c == b);
        }
    } else {
        assert(mesh_undirected_key_spec(a, b) == (b, a));
        assert(mesh_undirected_key_spec(c, d) == (b, a));
        if c <= d {
            assert(mesh_undirected_key_spec(c, d) == (c, d));
            assert(c == b && d == a);
        } else {
            assert(mesh_undirected_key_spec(c, d) == (d, c));
            assert(d == b && c == a);
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(700)]
pub proof fn lemma_from_face_cycles_success_implies_edge_exactly_two_half_edges_at(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
    e: int,
)
    requires
        from_face_cycles_success_spec(vertex_count, face_cycles, m),
        0 <= e < mesh_edge_count_spec(m),
    ensures
        mesh_edge_exactly_two_half_edges_at_spec(m, e),
{
    let hcnt = mesh_half_edge_count_spec(m);
    let h0 = m.edge_half_edges[e];
    let h1 = m.half_edges[h0].twin;

    assert(from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m));
    lemma_from_face_cycles_success_implies_twin_endpoint_correspondence(vertex_count, face_cycles, m);
    lemma_from_face_cycles_success_implies_undirected_edge_equivalence(vertex_count, face_cycles, m);
    lemma_from_face_cycles_success_implies_mesh_no_self_loop_half_edges(vertex_count, face_cycles, m);

    assert(0 <= h0 < hcnt);
    assert(m.half_edges[h0].edge == e);

    assert(from_face_cycles_twin_endpoint_correspondence_spec(m));
    assert(from_face_cycles_twin_endpoint_correspondence_at_spec(m, h0));
    assert(0 <= h1 < hcnt);
    assert(mesh_half_edge_from_vertex_spec(m, h1) == mesh_half_edge_to_vertex_spec(m, h0));
    assert(mesh_half_edge_to_vertex_spec(m, h1) == mesh_half_edge_from_vertex_spec(m, h0));

    assert(mesh_undirected_key_spec(
        mesh_half_edge_from_vertex_spec(m, h1),
        mesh_half_edge_to_vertex_spec(m, h1),
    ) == mesh_undirected_key_spec(
        mesh_half_edge_to_vertex_spec(m, h0),
        mesh_half_edge_from_vertex_spec(m, h0),
    ));
    lemma_mesh_undirected_key_symmetric(
        mesh_half_edge_from_vertex_spec(m, h0),
        mesh_half_edge_to_vertex_spec(m, h0),
    );
    assert(mesh_undirected_key_spec(
        mesh_half_edge_to_vertex_spec(m, h0),
        mesh_half_edge_from_vertex_spec(m, h0),
    ) == mesh_undirected_key_spec(
        mesh_half_edge_from_vertex_spec(m, h0),
        mesh_half_edge_to_vertex_spec(m, h0),
    ));
    assert(mesh_undirected_key_spec(
        mesh_half_edge_from_vertex_spec(m, h1),
        mesh_half_edge_to_vertex_spec(m, h1),
    ) == mesh_undirected_key_spec(
        mesh_half_edge_from_vertex_spec(m, h0),
        mesh_half_edge_to_vertex_spec(m, h0),
    ));
    assert(from_face_cycles_undirected_edge_equivalence_spec(m));
    assert(from_face_cycles_undirected_edge_pair_equivalent_spec(m, h1, h0));
    assert(m.half_edges[h1].edge == m.half_edges[h0].edge);
    assert(m.half_edges[h1].edge == e);

    assert(mesh_half_edge_from_vertex_spec(m, h0) != mesh_half_edge_to_vertex_spec(m, h0));
    if h0 == h1 {
        assert(mesh_half_edge_from_vertex_spec(m, h0) == mesh_half_edge_to_vertex_spec(m, h0));
        assert(false);
    }
    assert(h0 != h1);

    let h2 = m.half_edges[h1].twin;
    assert(from_face_cycles_twin_endpoint_correspondence_at_spec(m, h1));
    assert(0 <= h2 < hcnt);
    assert(mesh_half_edge_from_vertex_spec(m, h2) == mesh_half_edge_to_vertex_spec(m, h1));
    assert(mesh_half_edge_to_vertex_spec(m, h2) == mesh_half_edge_from_vertex_spec(m, h1));
    assert(mesh_half_edge_from_vertex_spec(m, h2) == mesh_half_edge_from_vertex_spec(m, h0));
    assert(mesh_half_edge_to_vertex_spec(m, h2) == mesh_half_edge_to_vertex_spec(m, h0));
    lemma_from_face_cycles_success_implies_oriented_half_edge_unique(
        vertex_count,
        face_cycles,
        m,
        h2,
        h0,
    );
    assert(m.half_edges[h1].twin == h0);

    assert(forall|h: int|
        0 <= h < hcnt ==> (#[trigger] m.half_edges[h].edge == e ==> (h == h0 || h == h1))) by {
        assert forall|h: int|
            0 <= h < hcnt && #[trigger] m.half_edges[h].edge == e implies (h == h0 || h == h1) by {
            assert(from_face_cycles_undirected_edge_pair_equivalent_spec(m, h, h0));
            assert(mesh_undirected_key_spec(
                mesh_half_edge_from_vertex_spec(m, h),
                mesh_half_edge_to_vertex_spec(m, h),
            ) == mesh_undirected_key_spec(
                mesh_half_edge_from_vertex_spec(m, h0),
                mesh_half_edge_to_vertex_spec(m, h0),
            ));
            assert(mesh_half_edge_from_vertex_spec(m, h) != mesh_half_edge_to_vertex_spec(m, h));
            assert(mesh_half_edge_from_vertex_spec(m, h0) != mesh_half_edge_to_vertex_spec(m, h0));
            lemma_undirected_key_equal_non_self_loop_implies_oriented_or_reversed(
                mesh_half_edge_from_vertex_spec(m, h),
                mesh_half_edge_to_vertex_spec(m, h),
                mesh_half_edge_from_vertex_spec(m, h0),
                mesh_half_edge_to_vertex_spec(m, h0),
            );
            if mesh_half_edge_from_vertex_spec(m, h) == mesh_half_edge_from_vertex_spec(m, h0)
                && mesh_half_edge_to_vertex_spec(m, h) == mesh_half_edge_to_vertex_spec(m, h0) {
                lemma_from_face_cycles_success_implies_oriented_half_edge_unique(
                    vertex_count,
                    face_cycles,
                    m,
                    h,
                    h0,
                );
                assert(h == h0 || h == h1);
            } else {
                assert(mesh_half_edge_from_vertex_spec(m, h)
                    == mesh_half_edge_to_vertex_spec(m, h0));
                assert(mesh_half_edge_to_vertex_spec(m, h)
                    == mesh_half_edge_from_vertex_spec(m, h0));
                assert(mesh_half_edge_from_vertex_spec(m, h1)
                    == mesh_half_edge_to_vertex_spec(m, h0));
                assert(mesh_half_edge_to_vertex_spec(m, h1)
                    == mesh_half_edge_from_vertex_spec(m, h0));
                assert(mesh_half_edge_from_vertex_spec(m, h)
                    == mesh_half_edge_from_vertex_spec(m, h1));
                assert(mesh_half_edge_to_vertex_spec(m, h)
                    == mesh_half_edge_to_vertex_spec(m, h1));
                lemma_from_face_cycles_success_implies_oriented_half_edge_unique(
                    vertex_count,
                    face_cycles,
                    m,
                    h,
                    h1,
                );
                assert(h == h1);
                assert(h == h0 || h == h1);
            }
        };
    };
    assert(mesh_edge_exactly_two_half_edges_at_spec(m, e));
}

pub proof fn lemma_from_face_cycles_success_implies_edge_exactly_two_half_edges(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
)
    ensures
        from_face_cycles_success_spec(vertex_count, face_cycles, m)
            ==> mesh_edge_exactly_two_half_edges_spec(m),
{
    if from_face_cycles_success_spec(vertex_count, face_cycles, m) {
        let ecnt = mesh_edge_count_spec(m);
        assert(forall|e: int| 0 <= e < ecnt ==> mesh_edge_exactly_two_half_edges_at_spec(m, e)) by {
            assert forall|e: int| 0 <= e < ecnt implies mesh_edge_exactly_two_half_edges_at_spec(m, e) by {
                lemma_from_face_cycles_success_implies_edge_exactly_two_half_edges_at(
                    vertex_count,
                    face_cycles,
                    m,
                    e,
                );
            };
        };
        assert(mesh_edge_exactly_two_half_edges_spec(m));
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

pub proof fn lemma_from_face_cycles_structural_core_implies_incidence(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
)
    ensures
        from_face_cycles_structural_core_spec(vertex_count, face_cycles, m)
            ==> from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m),
{
    if from_face_cycles_structural_core_spec(vertex_count, face_cycles, m) {
        let fcnt = face_cycles.len() as int;
        let hcnt = input_half_edge_count_spec(face_cycles);

        assert(mesh_vertex_count_spec(m) == vertex_count);
        assert(mesh_face_count_spec(m) == fcnt);
        assert(mesh_half_edge_count_spec(m) == hcnt);
        assert(mesh_index_bounds_spec(m));
        assert(forall|f: int|
            #![trigger m.face_half_edges[f]]
            0 <= f < fcnt ==> m.face_half_edges[f] == input_face_cycle_start_spec(face_cycles, f));

        assert(forall|f: int, i: int|
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
            }) by {
            assert forall|f: int, i: int|
                #![trigger m.half_edges[input_face_half_edge_index_spec(face_cycles, f, i)]]
                input_face_local_index_valid_spec(face_cycles, f, i) implies {
                    let n = face_cycles[f].len() as int;
                    let h = input_face_half_edge_index_spec(face_cycles, f, i);
                    let next_i = input_face_next_local_index_spec(face_cycles, f, i);
                    let prev_i = input_face_prev_local_index_spec(face_cycles, f, i);
                    &&& m.half_edges[h].face == f
                    &&& m.half_edges[h].vertex == input_face_from_vertex_spec(face_cycles, f, i)
                    &&& m.half_edges[h].next == input_face_half_edge_index_spec(face_cycles, f, next_i)
                    &&& m.half_edges[h].prev == input_face_half_edge_index_spec(face_cycles, f, prev_i)
                } by {
                assert(from_face_cycles_next_prev_face_coherent_spec(face_cycles, m));
                assert(from_face_cycles_next_prev_face_at_spec(face_cycles, m, f, i));
                assert(from_face_cycles_vertex_assignment_coherent_spec(face_cycles, m));
                assert(from_face_cycles_vertex_assignment_at_spec(face_cycles, m, f, i));
            };
        };

        assert(forall|h: int|
            #![trigger m.half_edges[h].twin]
            0 <= h < hcnt ==> {
                let t = m.half_edges[h].twin;
                &&& 0 <= t < hcnt
                &&& mesh_half_edge_from_vertex_spec(m, t) == mesh_half_edge_to_vertex_spec(m, h)
                &&& mesh_half_edge_to_vertex_spec(m, t) == mesh_half_edge_from_vertex_spec(m, h)
            }) by {
            assert forall|h: int|
                #![trigger m.half_edges[h].twin]
                0 <= h < hcnt implies {
                    let t = m.half_edges[h].twin;
                    &&& 0 <= t < hcnt
                    &&& mesh_half_edge_from_vertex_spec(m, t) == mesh_half_edge_to_vertex_spec(m, h)
                    &&& mesh_half_edge_to_vertex_spec(m, t) == mesh_half_edge_from_vertex_spec(m, h)
                } by {
                assert(from_face_cycles_twin_endpoint_correspondence_spec(m));
                assert(from_face_cycles_twin_endpoint_correspondence_at_spec(m, h));
            };
        };

        assert(forall|h1: int, h2: int|
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
            }) by {
            assert forall|h1: int, h2: int|
                #![trigger m.half_edges[h1].edge, m.half_edges[h2].edge]
                0 <= h1 < hcnt && 0 <= h2 < hcnt implies {
                    (m.half_edges[h1].edge == m.half_edges[h2].edge) <==> (
                        mesh_undirected_key_spec(
                            mesh_half_edge_from_vertex_spec(m, h1),
                            mesh_half_edge_to_vertex_spec(m, h1),
                        ) == mesh_undirected_key_spec(
                            mesh_half_edge_from_vertex_spec(m, h2),
                            mesh_half_edge_to_vertex_spec(m, h2),
                        )
                    )
                } by {
                assert(from_face_cycles_undirected_edge_equivalence_spec(m));
                assert(from_face_cycles_undirected_edge_pair_equivalent_spec(m, h1, h2));
            };
        };

        assert(forall|e: int|
            #![trigger m.edge_half_edges[e]]
            0 <= e < mesh_edge_count_spec(m) ==> {
                let h = m.edge_half_edges[e];
                &&& 0 <= h < hcnt
                &&& m.half_edges[h].edge == e
            }) by {
            assert forall|e: int|
                #![trigger m.edge_half_edges[e]]
                0 <= e < mesh_edge_count_spec(m) implies {
                    let h = m.edge_half_edges[e];
                    &&& 0 <= h < hcnt
                    &&& m.half_edges[h].edge == e
                } by {
                assert(mesh_edge_exactly_two_half_edges_spec(m));
                assert(mesh_edge_exactly_two_half_edges_at_spec(m, e));
            };
        };

        assert(forall|h: int| 0 <= h < hcnt ==> 0 <= #[trigger] m.half_edges[h].edge < mesh_edge_count_spec(m));

        assert(forall|v: int|
            #![trigger m.vertex_half_edges[v]]
            0 <= v < vertex_count ==> {
                let h = m.vertex_half_edges[v];
                &&& 0 <= h < hcnt
                &&& m.half_edges[h].vertex == v
            }) by {
            assert(mesh_vertex_representative_valid_nonisolated_spec(m));
        };

        assert(from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m));
    }
}

pub proof fn lemma_from_face_cycles_structural_core_implies_success(
    vertex_count: int,
    face_cycles: Seq<Seq<int>>,
    m: MeshModel,
)
    ensures
        from_face_cycles_structural_core_spec(vertex_count, face_cycles, m)
            ==> from_face_cycles_success_spec(vertex_count, face_cycles, m),
{
    if from_face_cycles_structural_core_spec(vertex_count, face_cycles, m) {
        assert(from_face_cycles_basic_input_spec(vertex_count, face_cycles));
        assert(from_face_cycles_no_self_loop_edges_spec(face_cycles));
        assert(from_face_cycles_no_duplicate_oriented_edges_spec(face_cycles));
        assert(from_face_cycles_all_oriented_edges_have_twin_spec(face_cycles));
        assert(from_face_cycles_no_isolated_vertices_spec(vertex_count, face_cycles));
        lemma_from_face_cycles_structural_core_implies_incidence(vertex_count, face_cycles, m);
        assert(from_face_cycles_incidence_model_spec(vertex_count, face_cycles, m));
        assert(from_face_cycles_success_spec(vertex_count, face_cycles, m));
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
        !out ==> !from_face_cycles_basic_input_spec(
            vertex_count as int,
            face_cycles_exec_to_model_spec(face_cycles@),
        ),
{
    if vertex_count == 0 {
        proof {
            let model_cycles = face_cycles_exec_to_model_spec(face_cycles@);
            assert(!from_face_cycles_basic_input_spec(vertex_count as int, model_cycles));
        }
        return false;
    }
    if face_cycles.len() == 0 {
        proof {
            let model_cycles = face_cycles_exec_to_model_spec(face_cycles@);
            assert(!from_face_cycles_basic_input_spec(vertex_count as int, model_cycles));
        }
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
            proof {
                assert(*face == face_cycles@.index(f as int));
                lemma_face_cycles_exec_to_model_face_len_exec(face_cycles, f, face, n);
                assert(model_cycles[f as int].len() == n as int);
                assert(!from_face_cycles_basic_input_spec(vertex_count as int, model_cycles)) by {
                    if from_face_cycles_basic_input_spec(vertex_count as int, model_cycles) {
                        assert(0 <= (f as int) && (f as int) < model_cycles.len() as int);
                        assert(model_cycles[f as int].len() as int >= 3);
                        assert(model_cycles[f as int].len() == n as int);
                        assert(n as int >= 3);
                        assert(n < 3);
                        assert(false);
                    }
                };
            }
            return false;
        }

        proof {
            assert(*face == face_cycles@.index(f as int));
            lemma_face_cycles_exec_to_model_face_len_exec(face_cycles, f, face, n);
            assert(face@.len() == n as int);
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
                proof {
                    lemma_face_cycles_exec_to_model_face_entry_exec(face_cycles, f, face, i);
                    assert(model_cycles[f as int][i as int] == v as int);
                    assert(!from_face_cycles_basic_input_spec(vertex_count as int, model_cycles)) by {
                        if from_face_cycles_basic_input_spec(vertex_count as int, model_cycles) {
                            assert(0 <= (f as int) && (f as int) < model_cycles.len() as int);
                            assert(0 <= (i as int) && (i as int) < (n as int));
                            assert(model_cycles[f as int].len() == n as int);
                            assert(0 <= (i as int) && (i as int) < model_cycles[f as int].len() as int);
                            assert(0 <= model_cycles[f as int][i as int] < vertex_count as int);
                            assert(v as int == model_cycles[f as int][i as int]);
                            assert(v >= vertex_count);
                            assert(v as int >= vertex_count as int);
                            assert(false);
                        }
                    };
                }
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
pub fn runtime_check_from_face_cycles_no_self_loop_edges(
    face_cycles: &[Vec<usize>],
) -> (out: bool)
    ensures
        out ==> from_face_cycles_no_self_loop_edges_spec(
            face_cycles_exec_to_model_spec(face_cycles@),
        ),
        !out ==> !from_face_cycles_no_self_loop_edges_spec(
            face_cycles_exec_to_model_spec(face_cycles@),
        ),
{
    let ghost model_cycles = face_cycles_exec_to_model_spec(face_cycles@);
    proof {
        assert(model_cycles.len() == face_cycles.len() as int);
    }

    let mut f: usize = 0;
    while f < face_cycles.len()
        invariant
            0 <= f <= face_cycles.len(),
            model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
            model_cycles.len() == face_cycles.len() as int,
            forall|fp: int, ip: int|
                #![trigger input_face_from_vertex_spec(model_cycles, fp, ip), input_face_to_vertex_spec(model_cycles, fp, ip)]
                0 <= fp < f as int
                    && input_face_local_index_valid_spec(model_cycles, fp, ip)
                    ==> input_face_from_vertex_spec(model_cycles, fp, ip)
                        != input_face_to_vertex_spec(model_cycles, fp, ip),
    {
        let face = vstd::slice::slice_index_get(face_cycles, f);
        let n = face.len();
        proof {
            assert(*face == face_cycles@.index(f as int));
            lemma_face_cycles_exec_to_model_face_len_exec(face_cycles, f, face, n);
            assert(model_cycles[f as int].len() == n as int);
        }

        let mut i: usize = 0;
        while i < n
            invariant
                0 <= f < face_cycles.len(),
                0 <= i <= n,
                n == face.len(),
                *face == face_cycles@.index(f as int),
                model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
                model_cycles.len() == face_cycles.len() as int,
                model_cycles[f as int].len() == n as int,
                forall|fp: int, ip: int|
                    #![trigger input_face_from_vertex_spec(model_cycles, fp, ip), input_face_to_vertex_spec(model_cycles, fp, ip)]
                    0 <= fp < f as int
                        && input_face_local_index_valid_spec(model_cycles, fp, ip)
                        ==> input_face_from_vertex_spec(model_cycles, fp, ip)
                            != input_face_to_vertex_spec(model_cycles, fp, ip),
                forall|ip: int|
                    #![trigger input_face_from_vertex_spec(model_cycles, f as int, ip), input_face_to_vertex_spec(model_cycles, f as int, ip)]
                    0 <= ip < i as int
                        ==> input_face_from_vertex_spec(model_cycles, f as int, ip)
                            != input_face_to_vertex_spec(model_cycles, f as int, ip),
        {
            let next_i = if i + 1 < n { i + 1 } else { 0 };
            let from = face[i];
            let to = face[next_i];
            proof {
                lemma_face_cycles_exec_to_model_oriented_edge_exec(face_cycles, f, face, i, next_i);
                assert(input_face_from_vertex_spec(model_cycles, f as int, i as int) == from as int);
                assert(input_face_to_vertex_spec(model_cycles, f as int, i as int) == to as int);
            }

            if from == to {
                proof {
                    assert(!from_face_cycles_no_self_loop_edges_spec(model_cycles)) by {
                        if from_face_cycles_no_self_loop_edges_spec(model_cycles) {
                            assert(input_face_local_index_valid_spec(model_cycles, f as int, i as int));
                            assert(input_face_from_vertex_spec(model_cycles, f as int, i as int)
                                != input_face_to_vertex_spec(model_cycles, f as int, i as int));
                            assert(from as int == to as int);
                            assert(false);
                        }
                    };
                }
                return false;
            }

            proof {
                assert(from as int != to as int);
                assert(forall|ip: int|
                    #![trigger input_face_from_vertex_spec(model_cycles, f as int, ip), input_face_to_vertex_spec(model_cycles, f as int, ip)]
                    0 <= ip < (i + 1) as int
                        ==> input_face_from_vertex_spec(model_cycles, f as int, ip)
                            != input_face_to_vertex_spec(model_cycles, f as int, ip)) by {
                    assert forall|ip: int|
                        #![trigger input_face_from_vertex_spec(model_cycles, f as int, ip), input_face_to_vertex_spec(model_cycles, f as int, ip)]
                        0 <= ip < (i + 1) as int
                            implies input_face_from_vertex_spec(model_cycles, f as int, ip)
                                != input_face_to_vertex_spec(model_cycles, f as int, ip) by {
                        if ip < i as int {
                            assert(0 <= ip < i as int);
                        } else {
                            assert(ip == i as int);
                            assert(input_face_from_vertex_spec(model_cycles, f as int, ip) == from as int);
                            assert(input_face_to_vertex_spec(model_cycles, f as int, ip) == to as int);
                        }
                    };
                }
            }

            i += 1;
        }

        proof {
            assert(i == n);
            assert(forall|fp: int, ip: int|
                #![trigger input_face_from_vertex_spec(model_cycles, fp, ip), input_face_to_vertex_spec(model_cycles, fp, ip)]
                0 <= fp < (f + 1) as int
                    && input_face_local_index_valid_spec(model_cycles, fp, ip)
                    ==> input_face_from_vertex_spec(model_cycles, fp, ip)
                        != input_face_to_vertex_spec(model_cycles, fp, ip)) by {
                assert forall|fp: int, ip: int|
                    #![trigger input_face_from_vertex_spec(model_cycles, fp, ip), input_face_to_vertex_spec(model_cycles, fp, ip)]
                    0 <= fp < (f + 1) as int
                        && input_face_local_index_valid_spec(model_cycles, fp, ip)
                        implies input_face_from_vertex_spec(model_cycles, fp, ip)
                            != input_face_to_vertex_spec(model_cycles, fp, ip) by {
                    if fp < f as int {
                    } else {
                        assert(fp == f as int);
                        assert(model_cycles[f as int].len() == n as int);
                        assert(0 <= ip < n as int);
                        assert(0 <= ip < i as int);
                        assert(forall|jp: int|
                            #![trigger input_face_from_vertex_spec(model_cycles, f as int, jp), input_face_to_vertex_spec(model_cycles, f as int, jp)]
                            0 <= jp < i as int
                                ==> input_face_from_vertex_spec(model_cycles, f as int, jp)
                                    != input_face_to_vertex_spec(model_cycles, f as int, jp));
                    }
                };
            };
        }

        f += 1;
    }

    proof {
        assert(f == face_cycles.len());
        assert(from_face_cycles_no_self_loop_edges_spec(model_cycles)) by {
            assert forall|fp: int, ip: int|
                #![trigger input_face_from_vertex_spec(model_cycles, fp, ip), input_face_to_vertex_spec(model_cycles, fp, ip)]
                input_face_local_index_valid_spec(model_cycles, fp, ip)
                    implies input_face_from_vertex_spec(model_cycles, fp, ip)
                        != input_face_to_vertex_spec(model_cycles, fp, ip) by {
                assert(0 <= fp < face_cycles.len() as int);
                assert(0 <= fp < f as int);
            };
        };
    }
    true
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_from_face_cycles_no_duplicate_oriented_edges(
    face_cycles: &[Vec<usize>],
) -> (out: bool)
    ensures
        out ==> from_face_cycles_no_duplicate_oriented_edges_spec(
            face_cycles_exec_to_model_spec(face_cycles@),
        ),
{
    let ghost model_cycles = face_cycles_exec_to_model_spec(face_cycles@);
    proof {
        assert(model_cycles.len() == face_cycles.len() as int);
    }

    let mut f: usize = 0;
    while f < face_cycles.len()
        invariant
            0 <= f <= face_cycles.len(),
            model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
            model_cycles.len() == face_cycles.len() as int,
            from_face_cycles_no_duplicate_oriented_edges_prefix_spec(model_cycles, f as int, 0),
    {
        let face = vstd::slice::slice_index_get(face_cycles, f);
        let n = face.len();
        proof {
            assert(*face == face_cycles@.index(f as int));
            lemma_face_cycles_exec_to_model_face_len_exec(face_cycles, f, face, n);
            assert(model_cycles[f as int].len() == n as int);
        }

        let mut i: usize = 0;
        while i < n
            invariant
                0 <= f < face_cycles.len(),
                0 <= i <= n,
                n == face.len(),
                *face == face_cycles@.index(f as int),
                model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
                model_cycles.len() == face_cycles.len() as int,
                model_cycles[f as int].len() == n as int,
                from_face_cycles_no_duplicate_oriented_edges_prefix_spec(model_cycles, f as int, i as int),
        {
            let next_i = if i + 1 < n { i + 1 } else { 0 };
            let from = face[i];
            let to = face[next_i];
            proof {
                lemma_face_cycles_exec_to_model_oriented_edge_exec(face_cycles, f, face, i, next_i);
                assert(input_face_from_vertex_spec(model_cycles, f as int, i as int) == from as int);
                assert(input_face_to_vertex_spec(model_cycles, f as int, i as int) == to as int);
            }

            let mut g: usize = 0;
            while g < f
                invariant
                    0 <= g <= f,
                    0 <= f < face_cycles.len(),
                    g < face_cycles.len(),
                    i < n,
                    n == face.len(),
                    *face == face_cycles@.index(f as int),
                    next_i == if i + 1 < face.len() { i + 1 } else { 0 },
                    model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
                    model_cycles.len() == face_cycles.len() as int,
                    model_cycles[f as int].len() == n as int,
                    input_face_from_vertex_spec(model_cycles, f as int, i as int) == from as int,
                    input_face_to_vertex_spec(model_cycles, f as int, i as int) == to as int,
                    from_face_cycles_oriented_edge_not_in_prefix_spec(
                        model_cycles,
                        f as int,
                        i as int,
                        g as int,
                        0,
                    ),
            {
                let face_prev = vstd::slice::slice_index_get(face_cycles, g);
                let n_prev = face_prev.len();
                proof {
                    assert(*face_prev == face_cycles@.index(g as int));
                    lemma_face_cycles_exec_to_model_face_len_exec(face_cycles, g, face_prev, n_prev);
                    assert(model_cycles[g as int].len() == n_prev as int);
                }

                let mut j: usize = 0;
                while j < n_prev
                    invariant
                        0 <= g < f,
                        0 <= f < face_cycles.len(),
                        g < face_cycles.len(),
                        0 <= j <= n_prev,
                        n_prev == face_prev.len(),
                        *face_prev == face_cycles@.index(g as int),
                        i < n,
                        n == face.len(),
                        *face == face_cycles@.index(f as int),
                        next_i == if i + 1 < face.len() { i + 1 } else { 0 },
                        model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
                        model_cycles.len() == face_cycles.len() as int,
                        model_cycles[f as int].len() == n as int,
                        model_cycles[g as int].len() == n_prev as int,
                        input_face_from_vertex_spec(model_cycles, f as int, i as int) == from as int,
                        input_face_to_vertex_spec(model_cycles, f as int, i as int) == to as int,
                        from_face_cycles_oriented_edge_not_in_prefix_spec(
                            model_cycles,
                            f as int,
                            i as int,
                            g as int,
                            j as int,
                        ),
                {
                    let next_j = if j + 1 < n_prev { j + 1 } else { 0 };
                    let from_prev = face_prev[j];
                    let to_prev = face_prev[next_j];
                    let duplicate = from == from_prev && to == to_prev;
                    if duplicate {
                        return false;
                    }

                    proof {
                        lemma_face_cycles_exec_to_model_oriented_edge_exec(face_cycles, g, face_prev, j, next_j);
                        assert(input_face_from_vertex_spec(model_cycles, g as int, j as int) == from_prev as int);
                        assert(input_face_to_vertex_spec(model_cycles, g as int, j as int) == to_prev as int);
                        assert(!duplicate);
                        assert(from_face_cycles_oriented_edge_not_in_prefix_spec(
                            model_cycles,
                            f as int,
                            i as int,
                            g as int,
                            (j + 1) as int,
                        )) by {
                            assert forall|fp: int, ip: int|
                                input_face_local_index_before_spec(
                                    model_cycles,
                                    fp,
                                    ip,
                                    g as int,
                                    (j + 1) as int,
                                ) implies !from_face_cycles_oriented_edge_match_spec(
                                    model_cycles,
                                    f as int,
                                    i as int,
                                    fp,
                                    ip,
                                ) by {
                                if fp < g as int || (fp == g as int && ip < j as int) {
                                    assert(input_face_local_index_before_spec(
                                        model_cycles,
                                        fp,
                                        ip,
                                        g as int,
                                        j as int,
                                    ));
                                    assert(from_face_cycles_oriented_edge_not_in_prefix_spec(
                                        model_cycles,
                                        f as int,
                                        i as int,
                                        g as int,
                                        j as int,
                                    ));
                                } else {
                                    assert(fp == g as int && ip == j as int);
                                    if from_face_cycles_oriented_edge_match_spec(
                                        model_cycles,
                                        f as int,
                                        i as int,
                                        fp,
                                        ip,
                                    ) {
                                        assert(input_face_from_vertex_spec(
                                            model_cycles,
                                            f as int,
                                            i as int,
                                        ) == input_face_from_vertex_spec(model_cycles, g as int, j as int));
                                        assert(input_face_to_vertex_spec(
                                            model_cycles,
                                            f as int,
                                            i as int,
                                        ) == input_face_to_vertex_spec(model_cycles, g as int, j as int));
                                        assert(from == from_prev);
                                        assert(to == to_prev);
                                        assert(duplicate);
                                        assert(false);
                                    }
                                }
                            };
                        }
                    }

                    j += 1;
                }

                proof {
                    assert(j == n_prev);
                    assert(from_face_cycles_oriented_edge_not_in_prefix_spec(
                        model_cycles,
                        f as int,
                        i as int,
                        (g + 1) as int,
                        0,
                    )) by {
                        assert forall|fp: int, ip: int|
                            input_face_local_index_before_spec(
                                model_cycles,
                                fp,
                                ip,
                                (g + 1) as int,
                                0,
                            ) implies !from_face_cycles_oriented_edge_match_spec(
                                model_cycles,
                                f as int,
                                i as int,
                                fp,
                                ip,
                            ) by {
                            if fp < g as int {
                                assert(input_face_local_index_before_spec(model_cycles, fp, ip, g as int, 0));
                                assert(from_face_cycles_oriented_edge_not_in_prefix_spec(
                                    model_cycles,
                                    f as int,
                                    i as int,
                                    g as int,
                                    0,
                                ));
                            } else {
                                assert(fp == g as int);
                                assert(0 <= ip < model_cycles[g as int].len() as int);
                                assert(model_cycles[g as int].len() == n_prev as int);
                                assert(input_face_local_index_before_spec(
                                    model_cycles,
                                    fp,
                                    ip,
                                    g as int,
                                    n_prev as int,
                                ));
                                assert(from_face_cycles_oriented_edge_not_in_prefix_spec(
                                    model_cycles,
                                    f as int,
                                    i as int,
                                    g as int,
                                    n_prev as int,
                                ));
                            }
                        };
                    }
                }

                g += 1;
            }

            let mut j: usize = 0;
            while j < i
                invariant
                    0 <= f < face_cycles.len(),
                    0 <= j <= i,
                    i < n,
                    n == face.len(),
                    *face == face_cycles@.index(f as int),
                    next_i == if i + 1 < face.len() { i + 1 } else { 0 },
                    model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
                    model_cycles.len() == face_cycles.len() as int,
                    model_cycles[f as int].len() == n as int,
                    input_face_from_vertex_spec(model_cycles, f as int, i as int) == from as int,
                    input_face_to_vertex_spec(model_cycles, f as int, i as int) == to as int,
                    from_face_cycles_oriented_edge_not_in_prefix_spec(
                        model_cycles,
                        f as int,
                        i as int,
                        f as int,
                        j as int,
                    ),
            {
                let next_j = if j + 1 < n { j + 1 } else { 0 };
                let from_prev = face[j];
                let to_prev = face[next_j];
                let duplicate = from == from_prev && to == to_prev;
                if duplicate {
                    return false;
                }

                proof {
                    lemma_face_cycles_exec_to_model_oriented_edge_exec(face_cycles, f, face, j, next_j);
                    assert(input_face_from_vertex_spec(model_cycles, f as int, j as int) == from_prev as int);
                    assert(input_face_to_vertex_spec(model_cycles, f as int, j as int) == to_prev as int);
                    assert(!duplicate);
                    assert(from_face_cycles_oriented_edge_not_in_prefix_spec(
                        model_cycles,
                        f as int,
                        i as int,
                        f as int,
                        (j + 1) as int,
                    )) by {
                        assert forall|fp: int, ip: int|
                            input_face_local_index_before_spec(
                                model_cycles,
                                fp,
                                ip,
                                f as int,
                                (j + 1) as int,
                            ) implies !from_face_cycles_oriented_edge_match_spec(
                                model_cycles,
                                f as int,
                                i as int,
                                fp,
                                ip,
                            ) by {
                            if fp < f as int || (fp == f as int && ip < j as int) {
                                assert(input_face_local_index_before_spec(
                                    model_cycles,
                                    fp,
                                    ip,
                                    f as int,
                                    j as int,
                                ));
                                assert(from_face_cycles_oriented_edge_not_in_prefix_spec(
                                    model_cycles,
                                    f as int,
                                    i as int,
                                    f as int,
                                    j as int,
                                ));
                            } else {
                                assert(fp == f as int && ip == j as int);
                                if from_face_cycles_oriented_edge_match_spec(
                                    model_cycles,
                                    f as int,
                                    i as int,
                                    fp,
                                    ip,
                                ) {
                                    assert(input_face_from_vertex_spec(
                                        model_cycles,
                                        f as int,
                                        i as int,
                                    ) == input_face_from_vertex_spec(model_cycles, f as int, j as int));
                                    assert(input_face_to_vertex_spec(
                                        model_cycles,
                                        f as int,
                                        i as int,
                                    ) == input_face_to_vertex_spec(model_cycles, f as int, j as int));
                                    assert(from == from_prev);
                                    assert(to == to_prev);
                                    assert(duplicate);
                                    assert(false);
                                }
                            }
                        };
                    }
                }

                j += 1;
            }

            proof {
                assert(from_face_cycles_oriented_edge_not_in_prefix_spec(
                    model_cycles,
                    f as int,
                    i as int,
                    f as int,
                    i as int,
                ));
                assert(from_face_cycles_no_duplicate_oriented_edges_prefix_spec(
                    model_cycles,
                    f as int,
                    (i + 1) as int,
                )) by {
                    assert forall|f1: int, i1: int, f2: int, i2: int|
                        input_face_local_index_before_spec(model_cycles, f1, i1, f as int, (i + 1) as int)
                            && input_face_local_index_before_spec(
                                model_cycles,
                                f2,
                                i2,
                                f as int,
                                (i + 1) as int,
                            )
                            && from_face_cycles_oriented_edge_match_spec(model_cycles, f1, i1, f2, i2)
                            implies f1 == f2 && i1 == i2 by {
                        let first_is_current = f1 == f as int && i1 == i as int;
                        let second_is_current = f2 == f as int && i2 == i as int;
                        if !first_is_current && !second_is_current {
                            assert(input_face_local_index_before_spec(model_cycles, f1, i1, f as int, i as int));
                            assert(input_face_local_index_before_spec(model_cycles, f2, i2, f as int, i as int));
                            assert(from_face_cycles_no_duplicate_oriented_edges_prefix_spec(
                                model_cycles,
                                f as int,
                                i as int,
                            ));
                        } else if first_is_current && second_is_current {
                        } else if first_is_current {
                            assert(input_face_local_index_before_spec(model_cycles, f2, i2, f as int, i as int));
                            assert(from_face_cycles_oriented_edge_not_in_prefix_spec(
                                model_cycles,
                                f as int,
                                i as int,
                                f as int,
                                i as int,
                            ));
                            assert(!from_face_cycles_oriented_edge_match_spec(
                                model_cycles,
                                f as int,
                                i as int,
                                f2,
                                i2,
                            ));
                            assert(false);
                        } else {
                            assert(input_face_local_index_before_spec(model_cycles, f1, i1, f as int, i as int));
                            assert(from_face_cycles_oriented_edge_not_in_prefix_spec(
                                model_cycles,
                                f as int,
                                i as int,
                                f as int,
                                i as int,
                            ));
                            assert(!from_face_cycles_oriented_edge_match_spec(
                                model_cycles,
                                f as int,
                                i as int,
                                f1,
                                i1,
                            ));
                            assert(false);
                        }
                    };
                }
            }

            i += 1;
        }

        proof {
            assert(i == n);
            assert(from_face_cycles_no_duplicate_oriented_edges_prefix_spec(
                model_cycles,
                (f + 1) as int,
                0,
            )) by {
                assert forall|f1: int, i1: int, f2: int, i2: int|
                    input_face_local_index_before_spec(model_cycles, f1, i1, (f + 1) as int, 0)
                        && input_face_local_index_before_spec(model_cycles, f2, i2, (f + 1) as int, 0)
                        && from_face_cycles_oriented_edge_match_spec(model_cycles, f1, i1, f2, i2)
                        implies f1 == f2 && i1 == i2 by {
                    assert(0 <= f1 < (f + 1) as int);
                    assert(0 <= f2 < (f + 1) as int);
                    if f1 < f as int {
                        assert(input_face_local_index_before_spec(model_cycles, f1, i1, f as int, i as int));
                    } else {
                        assert(f1 == f as int);
                        assert(0 <= i1 < model_cycles[f as int].len() as int);
                        assert(model_cycles[f as int].len() == n as int);
                        assert(input_face_local_index_before_spec(model_cycles, f1, i1, f as int, i as int));
                    }
                    if f2 < f as int {
                        assert(input_face_local_index_before_spec(model_cycles, f2, i2, f as int, i as int));
                    } else {
                        assert(f2 == f as int);
                        assert(0 <= i2 < model_cycles[f as int].len() as int);
                        assert(model_cycles[f as int].len() == n as int);
                        assert(input_face_local_index_before_spec(model_cycles, f2, i2, f as int, i as int));
                    }
                    assert(from_face_cycles_no_duplicate_oriented_edges_prefix_spec(
                        model_cycles,
                        f as int,
                        i as int,
                    ));
                };
            }
        }

        f += 1;
    }

    proof {
        assert(f == face_cycles.len());
        assert(from_face_cycles_no_duplicate_oriented_edges_prefix_spec(
            model_cycles,
            face_cycles.len() as int,
            0,
        ));
        lemma_from_face_cycles_no_duplicate_prefix_complete(model_cycles);
        assert(from_face_cycles_no_duplicate_oriented_edges_spec(model_cycles));
    }
    true
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_from_face_cycles_all_oriented_edges_have_twin(
    face_cycles: &[Vec<usize>],
) -> (out: bool)
    ensures
        out ==> from_face_cycles_all_oriented_edges_have_twin_spec(
            face_cycles_exec_to_model_spec(face_cycles@),
        ),
{
    let ghost model_cycles = face_cycles_exec_to_model_spec(face_cycles@);
    proof {
        assert(model_cycles.len() == face_cycles.len() as int);
    }

    let mut f: usize = 0;
    while f < face_cycles.len()
        invariant
            0 <= f <= face_cycles.len(),
            model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
            model_cycles.len() == face_cycles.len() as int,
            from_face_cycles_all_oriented_edges_have_twin_prefix_spec(model_cycles, f as int, 0),
    {
        let face = vstd::slice::slice_index_get(face_cycles, f);
        let n = face.len();
        proof {
            assert(*face == face_cycles@.index(f as int));
            lemma_face_cycles_exec_to_model_face_len_exec(face_cycles, f, face, n);
            assert(model_cycles[f as int].len() == n as int);
        }

        let mut i: usize = 0;
        while i < n
            invariant
                0 <= f < face_cycles.len(),
                0 <= i <= n,
                n == face.len(),
                *face == face_cycles@.index(f as int),
                model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
                model_cycles.len() == face_cycles.len() as int,
                model_cycles[f as int].len() == n as int,
                from_face_cycles_all_oriented_edges_have_twin_prefix_spec(model_cycles, f as int, i as int),
        {
            let next_i = if i + 1 < n { i + 1 } else { 0 };
            let from = face[i];
            let to = face[next_i];
            proof {
                lemma_face_cycles_exec_to_model_oriented_edge_exec(face_cycles, f, face, i, next_i);
                assert(input_face_from_vertex_spec(model_cycles, f as int, i as int) == from as int);
                assert(input_face_to_vertex_spec(model_cycles, f as int, i as int) == to as int);
            }

            let mut found = false;
            let mut twin_f: usize = 0;
            let mut twin_i: usize = 0;
            let mut g: usize = 0;
            while g < face_cycles.len() && !found
                invariant
                    0 <= g <= face_cycles.len(),
                    0 <= f < face_cycles.len(),
                    i < n,
                    n == face.len(),
                    *face == face_cycles@.index(f as int),
                    next_i == if i + 1 < face.len() { i + 1 } else { 0 },
                    model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
                    model_cycles.len() == face_cycles.len() as int,
                    model_cycles[f as int].len() == n as int,
                    input_face_from_vertex_spec(model_cycles, f as int, i as int) == from as int,
                    input_face_to_vertex_spec(model_cycles, f as int, i as int) == to as int,
                    found ==> {
                        &&& twin_f < face_cycles.len()
                        &&& input_face_local_index_valid_spec(model_cycles, twin_f as int, twin_i as int)
                        &&& input_face_from_vertex_spec(model_cycles, twin_f as int, twin_i as int) == to as int
                        &&& input_face_to_vertex_spec(model_cycles, twin_f as int, twin_i as int) == from as int
                    },
            {
                let face_other = vstd::slice::slice_index_get(face_cycles, g);
                let n_other = face_other.len();
                proof {
                    assert(*face_other == face_cycles@.index(g as int));
                    lemma_face_cycles_exec_to_model_face_len_exec(face_cycles, g, face_other, n_other);
                    assert(model_cycles[g as int].len() == n_other as int);
                }

                let mut j: usize = 0;
                while j < n_other && !found
                    invariant
                        0 <= g < face_cycles.len(),
                        0 <= f < face_cycles.len(),
                        0 <= j <= n_other,
                        n_other == face_other.len(),
                        *face_other == face_cycles@.index(g as int),
                        i < n,
                        n == face.len(),
                        *face == face_cycles@.index(f as int),
                        next_i == if i + 1 < face.len() { i + 1 } else { 0 },
                        model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
                        model_cycles.len() == face_cycles.len() as int,
                        model_cycles[f as int].len() == n as int,
                        model_cycles[g as int].len() == n_other as int,
                        input_face_from_vertex_spec(model_cycles, f as int, i as int) == from as int,
                        input_face_to_vertex_spec(model_cycles, f as int, i as int) == to as int,
                        found ==> {
                            &&& twin_f < face_cycles.len()
                            &&& input_face_local_index_valid_spec(model_cycles, twin_f as int, twin_i as int)
                            &&& input_face_from_vertex_spec(model_cycles, twin_f as int, twin_i as int) == to as int
                            &&& input_face_to_vertex_spec(model_cycles, twin_f as int, twin_i as int) == from as int
                        },
                {
                    let next_j = if j + 1 < n_other { j + 1 } else { 0 };
                    let from_other = face_other[j];
                    let to_other = face_other[next_j];
                    if from == to_other && to == from_other {
                        found = true;
                        twin_f = g;
                        twin_i = j;
                        proof {
                            lemma_face_cycles_exec_to_model_oriented_edge_exec(
                                face_cycles,
                                g,
                                face_other,
                                j,
                                next_j,
                            );
                            assert(input_face_local_index_valid_spec(model_cycles, g as int, j as int));
                            assert(input_face_from_vertex_spec(model_cycles, g as int, j as int) == from_other as int);
                            assert(input_face_to_vertex_spec(model_cycles, g as int, j as int) == to_other as int);
                            assert(from == to_other);
                            assert(to == from_other);
                            assert(twin_f < face_cycles.len());
                            assert(input_face_local_index_valid_spec(model_cycles, twin_f as int, twin_i as int));
                            assert(input_face_from_vertex_spec(model_cycles, twin_f as int, twin_i as int) == to as int);
                            assert(input_face_to_vertex_spec(model_cycles, twin_f as int, twin_i as int) == from as int);
                        }
                    } else {
                        j += 1;
                    }
                }

                if !found {
                    g += 1;
                }
            }

            if !found {
                return false;
            }

            proof {
                assert(found);
                assert(twin_f < face_cycles.len());
                assert(input_face_local_index_valid_spec(model_cycles, twin_f as int, twin_i as int));
                assert(input_face_from_vertex_spec(model_cycles, twin_f as int, twin_i as int) == to as int);
                assert(input_face_to_vertex_spec(model_cycles, twin_f as int, twin_i as int) == from as int);
                assert(from_face_cycles_all_oriented_edges_have_twin_prefix_spec(
                    model_cycles,
                    f as int,
                    (i + 1) as int,
                )) by {
                    assert forall|fp: int, ip: int|
                        #![trigger input_face_local_index_before_spec(
                            model_cycles,
                            fp,
                            ip,
                            f as int,
                            (i + 1) as int,
                        )]
                        input_face_local_index_before_spec(model_cycles, fp, ip, f as int, (i + 1) as int)
                            implies exists|gp: int, jp: int| {
                                &&& input_face_local_index_valid_spec(model_cycles, gp, jp)
                                &&& input_face_from_vertex_spec(model_cycles, gp, jp)
                                    == input_face_to_vertex_spec(model_cycles, fp, ip)
                                &&& input_face_to_vertex_spec(model_cycles, gp, jp)
                                    == input_face_from_vertex_spec(model_cycles, fp, ip)
                            } by {
                        let old_prefix = fp < f as int || (fp == f as int && ip < i as int);
                        if old_prefix {
                            assert(input_face_local_index_before_spec(model_cycles, fp, ip, f as int, i as int));
                            assert(from_face_cycles_all_oriented_edges_have_twin_prefix_spec(
                                model_cycles,
                                f as int,
                                i as int,
                            ));
                        } else {
                            assert(fp == f as int && ip == i as int);
                            assert(input_face_from_vertex_spec(model_cycles, fp, ip) == from as int);
                            assert(input_face_to_vertex_spec(model_cycles, fp, ip) == to as int);
                            assert(exists|gp: int, jp: int| {
                                &&& input_face_local_index_valid_spec(model_cycles, gp, jp)
                                &&& input_face_from_vertex_spec(model_cycles, gp, jp)
                                    == input_face_to_vertex_spec(model_cycles, fp, ip)
                                &&& input_face_to_vertex_spec(model_cycles, gp, jp)
                                    == input_face_from_vertex_spec(model_cycles, fp, ip)
                            }) by {
                                let gp = twin_f as int;
                                let jp = twin_i as int;
                                assert(input_face_local_index_valid_spec(model_cycles, gp, jp));
                                assert(input_face_from_vertex_spec(model_cycles, gp, jp) == to as int);
                                assert(input_face_to_vertex_spec(model_cycles, gp, jp) == from as int);
                                assert(input_face_from_vertex_spec(model_cycles, fp, ip) == from as int);
                                assert(input_face_to_vertex_spec(model_cycles, fp, ip) == to as int);
                                assert(input_face_from_vertex_spec(model_cycles, gp, jp)
                                    == input_face_to_vertex_spec(model_cycles, fp, ip));
                                assert(input_face_to_vertex_spec(model_cycles, gp, jp)
                                    == input_face_from_vertex_spec(model_cycles, fp, ip));
                            };
                        }
                    };
                }
            }

            i += 1;
        }

        proof {
            assert(i == n);
            assert(from_face_cycles_all_oriented_edges_have_twin_prefix_spec(
                model_cycles,
                (f + 1) as int,
                0,
            )) by {
                assert forall|fp: int, ip: int|
                    #![trigger input_face_local_index_before_spec(
                        model_cycles,
                        fp,
                        ip,
                        (f + 1) as int,
                        0,
                    )]
                    input_face_local_index_before_spec(model_cycles, fp, ip, (f + 1) as int, 0)
                        implies exists|gp: int, jp: int| {
                            &&& input_face_local_index_valid_spec(model_cycles, gp, jp)
                            &&& input_face_from_vertex_spec(model_cycles, gp, jp)
                                == input_face_to_vertex_spec(model_cycles, fp, ip)
                            &&& input_face_to_vertex_spec(model_cycles, gp, jp)
                                == input_face_from_vertex_spec(model_cycles, fp, ip)
                        } by {
                    assert(0 <= fp < (f + 1) as int);
                    if fp < f as int {
                        assert(input_face_local_index_before_spec(model_cycles, fp, ip, f as int, i as int));
                    } else {
                        assert(fp == f as int);
                        assert(0 <= ip < model_cycles[f as int].len() as int);
                        assert(model_cycles[f as int].len() == n as int);
                        assert(input_face_local_index_before_spec(model_cycles, fp, ip, f as int, i as int));
                    }
                    assert(from_face_cycles_all_oriented_edges_have_twin_prefix_spec(
                        model_cycles,
                        f as int,
                        i as int,
                    ));
                };
            }
        }

        f += 1;
    }

    proof {
        assert(f == face_cycles.len());
        assert(from_face_cycles_all_oriented_edges_have_twin_prefix_spec(
            model_cycles,
            face_cycles.len() as int,
            0,
        ));
        assert(from_face_cycles_all_oriented_edges_have_twin_spec(model_cycles)) by {
            assert forall|fp: int, ip: int|
                #![trigger input_face_local_index_valid_spec(model_cycles, fp, ip)]
                input_face_local_index_valid_spec(model_cycles, fp, ip) implies exists|gp: int, jp: int| {
                    &&& input_face_local_index_valid_spec(model_cycles, gp, jp)
                    &&& input_face_from_vertex_spec(model_cycles, gp, jp)
                        == input_face_to_vertex_spec(model_cycles, fp, ip)
                    &&& input_face_to_vertex_spec(model_cycles, gp, jp)
                        == input_face_from_vertex_spec(model_cycles, fp, ip)
                } by {
                assert(input_face_local_index_before_spec(
                    model_cycles,
                    fp,
                    ip,
                    face_cycles.len() as int,
                    0,
                ));
                assert(from_face_cycles_all_oriented_edges_have_twin_prefix_spec(
                    model_cycles,
                    face_cycles.len() as int,
                    0,
                ));
            };
        };
    }
    true
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_from_face_cycles_no_isolated_vertices(
    vertex_count: usize,
    face_cycles: &[Vec<usize>],
) -> (out: bool)
    ensures
        out ==> from_face_cycles_no_isolated_vertices_spec(
            vertex_count as int,
            face_cycles_exec_to_model_spec(face_cycles@),
        ),
{
    if vertex_count == 0 {
        return false;
    }

    let ghost model_cycles = face_cycles_exec_to_model_spec(face_cycles@);
    proof {
        assert(model_cycles.len() == face_cycles.len() as int);
    }

    let mut seen = vec![false; vertex_count];
    let mut f: usize = 0;
    while f < face_cycles.len()
        invariant
            vertex_count > 0,
            0 <= f <= face_cycles.len(),
            model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
            model_cycles.len() == face_cycles.len() as int,
            seen@.len() == vertex_count as int,
            forall|vp: int|
                0 <= vp < vertex_count as int && #[trigger] seen@[vp]
                    ==> from_face_cycles_prefix_contains_vertex_spec(model_cycles, f as int, 0, vp),
    {
        let face = vstd::slice::slice_index_get(face_cycles, f);
        let n = face.len();
        proof {
            assert(*face == face_cycles@.index(f as int));
            lemma_face_cycles_exec_to_model_face_len_exec(face_cycles, f, face, n);
            assert(model_cycles[f as int].len() == n as int);
        }

        let mut i: usize = 0;
        while i < n
            invariant
                vertex_count > 0,
                0 <= f < face_cycles.len(),
                0 <= i <= n,
                n == face.len(),
                face@.len() == n as int,
                *face == face_cycles@.index(f as int),
                model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
                model_cycles.len() == face_cycles.len() as int,
                model_cycles[f as int].len() == n as int,
                seen@.len() == vertex_count as int,
                forall|vp: int|
                    0 <= vp < vertex_count as int && #[trigger] seen@[vp]
                        ==> from_face_cycles_prefix_contains_vertex_spec(model_cycles, f as int, i as int, vp),
        {
            let v = face[i];
            if v >= vertex_count {
                return false;
            }

            let ghost seen_before = seen@;
            seen[v] = true;

            proof {
                lemma_face_cycles_exec_to_model_face_entry_exec(face_cycles, f, face, i);
                assert(model_cycles[f as int][i as int] == v as int);
                assert(input_face_local_index_valid_spec(model_cycles, f as int, i as int));
                assert(forall|vp: int|
                    0 <= vp < vertex_count as int && #[trigger] seen@[vp]
                        ==> from_face_cycles_prefix_contains_vertex_spec(
                            model_cycles,
                            f as int,
                            (i + 1) as int,
                            vp,
                        )) by {
                    assert forall|vp: int|
                        0 <= vp < vertex_count as int && #[trigger] seen@[vp]
                            implies from_face_cycles_prefix_contains_vertex_spec(
                                model_cycles,
                                f as int,
                                (i + 1) as int,
                                vp,
                            ) by {
                        if seen_before[vp] {
                            assert(from_face_cycles_prefix_contains_vertex_spec(
                                model_cycles,
                                f as int,
                                i as int,
                                vp,
                            ));
                            lemma_from_face_cycles_prefix_contains_vertex_step_local(
                                model_cycles,
                                f as int,
                                i as int,
                                vp,
                            );
                        } else {
                            assert(vp == v as int);
                            assert(exists|w: (int, int)| {
                                &&& input_face_local_index_valid_spec(model_cycles, w.0, w.1)
                                &&& (w.0 < f as int || (w.0 == f as int && w.1 < (i + 1) as int))
                                &&& #[trigger] input_face_from_vertex_spec(model_cycles, w.0, w.1) == vp
                            }) by {
                                let w = (f as int, i as int);
                                assert(input_face_local_index_valid_spec(model_cycles, w.0, w.1));
                                assert(w.0 == f as int);
                                assert(w.1 == i as int);
                                assert(w.0 == f as int && w.1 < (i + 1) as int);
                                assert(input_face_from_vertex_spec(model_cycles, w.0, w.1) == v as int);
                                assert(vp == v as int);
                                assert(input_face_from_vertex_spec(model_cycles, w.0, w.1) == vp);
                            };
                            assert(from_face_cycles_prefix_contains_vertex_spec(
                                model_cycles,
                                f as int,
                                (i + 1) as int,
                                vp,
                            ));
                        }
                    };
                }
            }

            i += 1;
        }

        proof {
            assert(i == n);
            assert(forall|vp: int|
                0 <= vp < vertex_count as int && #[trigger] seen@[vp]
                    ==> from_face_cycles_prefix_contains_vertex_spec(
                        model_cycles,
                        (f + 1) as int,
                        0,
                        vp,
                    )) by {
                assert forall|vp: int|
                    0 <= vp < vertex_count as int && #[trigger] seen@[vp]
                        implies from_face_cycles_prefix_contains_vertex_spec(
                            model_cycles,
                            (f + 1) as int,
                            0,
                            vp,
                        ) by {
                    assert(from_face_cycles_prefix_contains_vertex_spec(
                        model_cycles,
                        f as int,
                        i as int,
                        vp,
                    ));
                    lemma_from_face_cycles_prefix_contains_vertex_promote_face(
                        model_cycles,
                        f as int,
                        i as int,
                        vp,
                    );
                };
            }
        }

        f += 1;
    }

    let mut v: usize = 0;
    while v < vertex_count
        invariant
            vertex_count > 0,
            0 <= v <= vertex_count,
            f == face_cycles.len(),
            model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
            model_cycles.len() == face_cycles.len() as int,
            seen@.len() == vertex_count as int,
            forall|vp: int|
                0 <= vp < vertex_count as int && #[trigger] seen@[vp]
                    ==> from_face_cycles_prefix_contains_vertex_spec(
                        model_cycles,
                        face_cycles.len() as int,
                        0,
                        vp,
                    ),
            forall|vp: int|
                0 <= vp < v as int
                    ==> from_face_cycles_prefix_contains_vertex_spec(
                        model_cycles,
                        face_cycles.len() as int,
                        0,
                        vp,
                    ),
    {
        if !seen[v] {
            return false;
        }

        proof {
            assert(seen@[v as int]);
            assert(from_face_cycles_prefix_contains_vertex_spec(
                model_cycles,
                face_cycles.len() as int,
                0,
                v as int,
            ));
            assert(forall|vp: int|
                0 <= vp < (v + 1) as int
                    ==> from_face_cycles_prefix_contains_vertex_spec(
                        model_cycles,
                        face_cycles.len() as int,
                        0,
                        vp,
                    )) by {
                assert forall|vp: int|
                    0 <= vp < (v + 1) as int
                        implies from_face_cycles_prefix_contains_vertex_spec(
                            model_cycles,
                            face_cycles.len() as int,
                            0,
                            vp,
                        ) by {
                    if vp < v as int {
                    } else {
                        assert(vp == v as int);
                        assert(from_face_cycles_prefix_contains_vertex_spec(
                            model_cycles,
                            face_cycles.len() as int,
                            0,
                            v as int,
                        ));
                    }
                };
            }
        }

        v += 1;
    }

    proof {
        assert(v == vertex_count);
        assert(forall|vp: int|
            0 <= vp < vertex_count as int
                ==> from_face_cycles_prefix_contains_vertex_spec(
                    model_cycles,
                    face_cycles.len() as int,
                    0,
                    vp,
                )) by {
            assert forall|vp: int|
                0 <= vp < vertex_count as int
                    implies from_face_cycles_prefix_contains_vertex_spec(
                        model_cycles,
                        face_cycles.len() as int,
                        0,
                        vp,
                    ) by {
                assert(vertex_count as int == v as int);
                assert(0 <= vp < v as int);
            };
        }
        assert(from_face_cycles_no_isolated_vertices_spec(vertex_count as int, model_cycles)) by {
            assert forall|vp: int|
                #![trigger from_face_cycles_vertex_has_incident_spec(model_cycles, vp)]
                0 <= vp < vertex_count as int
                    implies from_face_cycles_vertex_has_incident_spec(model_cycles, vp) by {
                assert(from_face_cycles_prefix_contains_vertex_spec(
                    model_cycles,
                    face_cycles.len() as int,
                    0,
                    vp,
                ));
                lemma_from_face_cycles_prefix_contains_vertex_implies_contains(
                    model_cycles,
                    face_cycles.len() as int,
                    0,
                    vp,
                );
                assert(from_face_cycles_vertex_has_incident_spec(model_cycles, vp));
            };
        }
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
        out ==> from_face_cycles_next_prev_face_coherent_spec(
            face_cycles_exec_to_model_spec(face_cycles@),
            m@,
        )
            && from_face_cycles_vertex_assignment_coherent_spec(
            face_cycles_exec_to_model_spec(face_cycles@),
            m@,
        ),
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
            forall|fp: int, ip: int|
                0 <= fp < f as int && input_face_local_index_valid_spec(model_cycles, fp, ip)
                    ==> from_face_cycles_vertex_assignment_at_spec(model_cycles, m@, fp, ip),
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
            assert(*face == face_cycles@.index(f as int));
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
                n == face.len(),
                face@.len() == n as int,
                *face == face_cycles@.index(f as int),
                start as int == input_face_cycle_start_spec(model_cycles, f as int),
                forall|fp: int, ip: int|
                    0 <= fp < f as int && input_face_local_index_valid_spec(model_cycles, fp, ip)
                        ==> from_face_cycles_next_prev_face_at_spec(model_cycles, m@, fp, ip),
                forall|fp: int, ip: int|
                    0 <= fp < f as int && input_face_local_index_valid_spec(model_cycles, fp, ip)
                        ==> from_face_cycles_vertex_assignment_at_spec(model_cycles, m@, fp, ip),
                forall|ip: int|
                    0 <= ip < i as int && input_face_local_index_valid_spec(model_cycles, f as int, ip)
                        ==> from_face_cycles_next_prev_face_at_spec(model_cycles, m@, f as int, ip),
                forall|ip: int|
                    0 <= ip < i as int && input_face_local_index_valid_spec(model_cycles, f as int, ip)
                        ==> from_face_cycles_vertex_assignment_at_spec(model_cycles, m@, f as int, ip),
        {
            proof {
                assert(i < face.len());
            }
            let next_i = if i + 1 < n { i + 1 } else { 0 };
            let prev_i = if i == 0 { n - 1 } else { i - 1 };
            let expected_vertex = face[i];

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
            if he.face != f || he.vertex != expected_vertex || he.next != expected_next || he.prev != expected_prev {
                return false;
            }

            proof {
                assert(0 <= i as int && (i as int) < (n as int));
                assert(input_face_local_index_valid_spec(model_cycles, f as int, i as int));
                lemma_face_cycles_exec_to_model_face_entry_exec(face_cycles, f, face, i);
                assert(h as int == input_face_half_edge_index_spec(model_cycles, f as int, i as int));
                assert(input_face_from_vertex_spec(model_cycles, f as int, i as int) == expected_vertex as int);
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
                assert(m.half_edges@[h as int].vertex == he.vertex as int);
                assert(m.half_edges@[h as int].next == he.next as int);
                assert(m.half_edges@[h as int].prev == he.prev as int);
                assert(from_face_cycles_next_prev_face_at_spec(model_cycles, m@, f as int, i as int));
                assert(from_face_cycles_vertex_assignment_at_spec(model_cycles, m@, f as int, i as int));
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
            assert forall|fp: int, ip: int|
                0 <= fp < (f + 1) as int && input_face_local_index_valid_spec(model_cycles, fp, ip)
                    implies from_face_cycles_vertex_assignment_at_spec(model_cycles, m@, fp, ip) by {
                if 0 <= fp < f as int {
                    assert(from_face_cycles_vertex_assignment_at_spec(model_cycles, m@, fp, ip));
                } else {
                    assert(fp == f as int);
                    assert(0 <= ip < i as int);
                    assert(from_face_cycles_vertex_assignment_at_spec(model_cycles, m@, f as int, ip));
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
        assert(forall|fp: int, ip: int|
            0 <= fp < face_cycles.len() as int && input_face_local_index_valid_spec(model_cycles, fp, ip)
                ==> from_face_cycles_vertex_assignment_at_spec(model_cycles, m@, fp, ip));
        assert(from_face_cycles_next_prev_face_coherent_spec(model_cycles, m@));
        assert(from_face_cycles_vertex_assignment_coherent_spec(model_cycles, m@));
    }
    true
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_from_face_cycles_counts_index_face_starts(
    vertex_count: usize,
    m: &Mesh,
    face_cycles: &[Vec<usize>],
) -> (out: bool)
    ensures
        out ==> from_face_cycles_counts_index_face_starts_spec(
            vertex_count as int,
            face_cycles_exec_to_model_spec(face_cycles@),
            m@,
        ),
{
    if m.vertices.len() != vertex_count {
        return false;
    }
    if m.faces.len() != face_cycles.len() {
        return false;
    }

    let ghost model_cycles = face_cycles_exec_to_model_spec(face_cycles@);

    let mut start: usize = 0;
    let mut f: usize = 0;
    while f < face_cycles.len()
        invariant
            vertex_count == m.vertices.len(),
            m.faces.len() == face_cycles.len(),
            0 <= f <= face_cycles.len(),
            model_cycles == face_cycles_exec_to_model_spec(face_cycles@),
            model_cycles.len() == face_cycles.len() as int,
            start as int == input_face_cycle_start_spec(model_cycles, f as int),
            forall|fp: int|
                #![trigger m@.face_half_edges[fp]]
                0 <= fp < f as int
                    ==> m@.face_half_edges[fp] == input_face_cycle_start_spec(model_cycles, fp),
    {
        let face = vstd::slice::slice_index_get(face_cycles, f);
        let n = face.len();
        let face_he = m.faces[f].half_edge;
        if face_he != start {
            return false;
        }
        let next_start = match start.checked_add(n) {
            Some(v) => v,
            None => return false,
        };

        proof {
            assert(*face == face_cycles@.index(f as int));
            lemma_face_cycles_exec_to_model_face_len_exec(face_cycles, f, face, n);
            assert(model_cycles[f as int].len() == n as int);
            assert(m@.face_half_edges[f as int] == face_he as int);
            assert(face_he == start);
            assert(input_face_cycle_start_spec(model_cycles, f as int) == start as int);
            assert(m@.face_half_edges[f as int] == input_face_cycle_start_spec(model_cycles, f as int));
            assert(forall|fp: int|
                #![trigger m@.face_half_edges[fp]]
                0 <= fp < (f + 1) as int
                    ==> m@.face_half_edges[fp] == input_face_cycle_start_spec(model_cycles, fp)) by {
                assert forall|fp: int|
                    #![trigger m@.face_half_edges[fp]]
                    0 <= fp < (f + 1) as int
                        implies m@.face_half_edges[fp] == input_face_cycle_start_spec(model_cycles, fp) by {
                    if fp < f as int {
                    } else {
                        assert(fp == f as int);
                        assert(m@.face_half_edges[fp] == input_face_cycle_start_spec(model_cycles, fp));
                    }
                };
            };
            assert(input_face_cycle_start_spec(model_cycles, f as int + 1)
                == input_face_cycle_start_spec(model_cycles, f as int) + model_cycles[f as int].len() as int);
            assert(next_start as int == start as int + n as int);
            assert(next_start as int == input_face_cycle_start_spec(model_cycles, (f + 1) as int));
        }

        start = next_start;
        f += 1;
    }

    if m.half_edges.len() != start {
        return false;
    }

    let index_ok = runtime_check_index_bounds(m);
    if !index_ok {
        return false;
    }

    proof {
        assert(mesh_vertex_count_spec(m@) == m.vertices@.len() as int);
        assert(m.vertices@.len() == m.vertices.len());
        assert(m.vertices.len() == vertex_count);
        assert(mesh_vertex_count_spec(m@) == vertex_count as int);

        assert(mesh_face_count_spec(m@) == m.faces@.len() as int);
        assert(m.faces@.len() == m.faces.len());
        assert(m.faces.len() == face_cycles.len());
        assert(mesh_face_count_spec(m@) == face_cycles.len() as int);

        assert(mesh_half_edge_count_spec(m@) == m.half_edges@.len() as int);
        assert(m.half_edges@.len() == m.half_edges.len());
        assert(m.half_edges.len() == start);
        assert(mesh_half_edge_count_spec(m@) == start as int);

        assert(f == face_cycles.len());
        assert(start as int == input_face_cycle_start_spec(model_cycles, f as int));
        assert(input_half_edge_count_spec(model_cycles) == start as int);
        assert(mesh_half_edge_count_spec(m@) == input_half_edge_count_spec(model_cycles));

        assert(mesh_index_bounds_spec(m@));

        assert(forall|fp: int|
            #![trigger m@.face_half_edges[fp]]
            0 <= fp < face_cycles.len() as int
                ==> m@.face_half_edges[fp] == input_face_cycle_start_spec(model_cycles, fp)) by {
            assert forall|fp: int|
                #![trigger m@.face_half_edges[fp]]
                0 <= fp < face_cycles.len() as int
                    implies m@.face_half_edges[fp] == input_face_cycle_start_spec(model_cycles, fp) by {
                assert(face_cycles.len() as int == f as int);
                assert(0 <= fp < f as int);
            };
        };

        assert(from_face_cycles_counts_index_face_starts_spec(vertex_count as int, model_cycles, m@));
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
            Result::Ok(m) => from_face_cycles_structural_core_spec(
                vertex_positions@.len() as int,
                face_cycles_exec_to_model_spec(face_cycles@),
                m@,
            ) && from_face_cycles_success_spec(
                vertex_positions@.len() as int,
                face_cycles_exec_to_model_spec(face_cycles@),
                m@,
            ),
            Result::Err(_) => from_face_cycles_failure_spec(
                vertex_positions@.len() as int,
                face_cycles_exec_to_model_spec(face_cycles@),
            ),
        },
{
    let vertex_count = vertex_positions.len();
    let ghost model_cycles = face_cycles_exec_to_model_spec(face_cycles@);
    let input_ok = runtime_check_from_face_cycles_basic_input(vertex_count, face_cycles);
    if !input_ok {
        proof {
            assert(!from_face_cycles_basic_input_spec(vertex_count as int, model_cycles));
            assert(from_face_cycles_failure_spec(vertex_count as int, model_cycles));
        }
        return Result::Err(mesh_build_error_empty_face_set());
    }
    let no_self_loop_ok = runtime_check_from_face_cycles_no_self_loop_edges(face_cycles);
    if !no_self_loop_ok {
        proof {
            assert(!from_face_cycles_no_self_loop_edges_spec(model_cycles));
            assert(from_face_cycles_failure_spec(vertex_count as int, model_cycles));
        }
        return Result::Err(mesh_build_error_empty_face_set());
    }
    let no_duplicate_ok = runtime_check_from_face_cycles_no_duplicate_oriented_edges(face_cycles);
    if !no_duplicate_ok {
        ex_from_face_cycles_constructive_abort();
    }
    let all_twin_ok = runtime_check_from_face_cycles_all_oriented_edges_have_twin(face_cycles);
    if !all_twin_ok {
        ex_from_face_cycles_constructive_abort();
    }
    let no_isolated_ok = runtime_check_from_face_cycles_no_isolated_vertices(vertex_count, face_cycles);
    if !no_isolated_ok {
        ex_from_face_cycles_constructive_abort();
    }

    let out0 = ex_mesh_from_face_cycles(vertex_positions, face_cycles);
    match out0 {
        Result::Ok(m) => {
            let counts_index_face_starts_ok = runtime_check_from_face_cycles_counts_index_face_starts(
                vertex_count,
                &m,
                face_cycles,
            );
            if !counts_index_face_starts_ok {
                ex_from_face_cycles_constructive_abort();
            } else {
                let next_prev_ok = runtime_check_from_face_cycles_next_prev_face_coherent(&m, face_cycles);
                if !next_prev_ok {
                    ex_from_face_cycles_constructive_abort();
                } else {
                    let twin_ok = runtime_check_twin_assignment_total_involution(&m);
                    if !twin_ok {
                        ex_from_face_cycles_constructive_abort();
                    } else {
                        let twin_endpoints_ok = runtime_check_twin_endpoint_correspondence(&m);
                        if !twin_endpoints_ok {
                            ex_from_face_cycles_constructive_abort();
                        } else {
                            let undirected_edge_ok = runtime_check_from_face_cycles_undirected_edge_equivalence(
                                &m,
                            );
                            if !undirected_edge_ok {
                                ex_from_face_cycles_constructive_abort();
                            } else {
                                let edge_ok = runtime_check_edge_exactly_two_half_edges(&m);
                                if !edge_ok {
                                    ex_from_face_cycles_constructive_abort();
                                } else {
                                    let vertex_ok = runtime_check_vertex_representative_valid_nonisolated(&m);
                                    if !vertex_ok {
                                        ex_from_face_cycles_constructive_abort();
                                    } else {
                                        proof {
                                            assert(input_ok);
                                            assert(no_self_loop_ok);
                                            assert(no_duplicate_ok);
                                            assert(all_twin_ok);
                                            assert(no_isolated_ok);
                                            assert(counts_index_face_starts_ok);
                                            assert(undirected_edge_ok);
                                            assert(from_face_cycles_basic_input_spec(vertex_count as int, model_cycles));
                                            assert(from_face_cycles_no_self_loop_edges_spec(model_cycles));
                                            assert(from_face_cycles_no_duplicate_oriented_edges_spec(model_cycles));
                                            assert(from_face_cycles_all_oriented_edges_have_twin_spec(model_cycles));
                                            assert(from_face_cycles_no_isolated_vertices_spec(vertex_count as int, model_cycles));
                                            assert(from_face_cycles_counts_index_face_starts_spec(
                                                vertex_count as int,
                                                model_cycles,
                                                m@,
                                            ));
                                            assert(from_face_cycles_next_prev_face_coherent_spec(model_cycles, m@));
                                            assert(from_face_cycles_vertex_assignment_coherent_spec(model_cycles, m@));
                                            assert(from_face_cycles_twin_assignment_total_involution_spec(m@));
                                            assert(from_face_cycles_twin_endpoint_correspondence_spec(m@));
                                            assert(from_face_cycles_undirected_edge_equivalence_spec(m@));
                                            assert(mesh_edge_exactly_two_half_edges_spec(m@));
                                            assert(from_face_cycles_vertex_representatives_spec(m@));
                                            assert(from_face_cycles_structural_core_spec(
                                                vertex_count as int,
                                                model_cycles,
                                                m@,
                                            ));
                                            lemma_from_face_cycles_structural_core_implies_success(
                                                vertex_count as int,
                                                model_cycles,
                                                m@,
                                            );
                                            assert(from_face_cycles_success_spec(
                                                vertex_count as int,
                                                model_cycles,
                                                m@,
                                            ));
                                        }
                                        Result::Ok(m)
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        Result::Err(_) => ex_from_face_cycles_constructive_abort(),
    }
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_index_bounds(m: &Mesh) -> (out: bool)
    ensures
        out ==> mesh_index_bounds_spec(m@),
{
    let vcnt = m.vertices.len();
    let ecnt = m.edges.len();
    let fcnt = m.faces.len();
    let hcnt = m.half_edges.len();

    let mut v: usize = 0;
    while v < vcnt
        invariant
            vcnt == m.vertices.len(),
            hcnt == m.half_edges.len(),
            0 <= v <= vcnt,
            forall|vp: int|
                0 <= vp < v as int
                    ==> 0 <= #[trigger] m@.vertex_half_edges[vp] < (hcnt as int),
    {
        let he = m.vertices[v].half_edge;
        if he >= hcnt {
            return false;
        }

        proof {
            assert(m@.vertex_half_edges[v as int] == he as int);
            assert(0 <= #[trigger] m@.vertex_half_edges[v as int] < (hcnt as int));
            assert(forall|vp: int|
                0 <= vp < (v + 1) as int
                    ==> 0 <= #[trigger] m@.vertex_half_edges[vp] < (hcnt as int)) by {
                assert forall|vp: int|
                    0 <= vp < (v + 1) as int
                        implies 0 <= #[trigger] m@.vertex_half_edges[vp] < (hcnt as int) by {
                    if vp < v as int {
                        assert(0 <= vp < v as int);
                    } else {
                        assert(vp == v as int);
                        assert(m@.vertex_half_edges[vp] == he as int);
                    }
                };
            }
        }

        v += 1;
    }

    let mut e: usize = 0;
    while e < ecnt
        invariant
            ecnt == m.edges.len(),
            hcnt == m.half_edges.len(),
            0 <= e <= ecnt,
            forall|ep: int|
                0 <= ep < e as int
                    ==> 0 <= #[trigger] m@.edge_half_edges[ep] < (hcnt as int),
    {
        let he = m.edges[e].half_edge;
        if he >= hcnt {
            return false;
        }

        proof {
            assert(m@.edge_half_edges[e as int] == he as int);
            assert(0 <= #[trigger] m@.edge_half_edges[e as int] < (hcnt as int));
            assert(forall|ep: int|
                0 <= ep < (e + 1) as int
                    ==> 0 <= #[trigger] m@.edge_half_edges[ep] < (hcnt as int)) by {
                assert forall|ep: int|
                    0 <= ep < (e + 1) as int
                        implies 0 <= #[trigger] m@.edge_half_edges[ep] < (hcnt as int) by {
                    if ep < e as int {
                        assert(0 <= ep < e as int);
                    } else {
                        assert(ep == e as int);
                        assert(m@.edge_half_edges[ep] == he as int);
                    }
                };
            }
        }

        e += 1;
    }

    let mut f: usize = 0;
    while f < fcnt
        invariant
            fcnt == m.faces.len(),
            hcnt == m.half_edges.len(),
            0 <= f <= fcnt,
            forall|fp: int|
                0 <= fp < f as int
                    ==> 0 <= #[trigger] m@.face_half_edges[fp] < (hcnt as int),
    {
        let he = m.faces[f].half_edge;
        if he >= hcnt {
            return false;
        }

        proof {
            assert(m@.face_half_edges[f as int] == he as int);
            assert(0 <= #[trigger] m@.face_half_edges[f as int] < (hcnt as int));
            assert(forall|fp: int|
                0 <= fp < (f + 1) as int
                    ==> 0 <= #[trigger] m@.face_half_edges[fp] < (hcnt as int)) by {
                assert forall|fp: int|
                    0 <= fp < (f + 1) as int
                        implies 0 <= #[trigger] m@.face_half_edges[fp] < (hcnt as int) by {
                    if fp < f as int {
                        assert(0 <= fp < f as int);
                    } else {
                        assert(fp == f as int);
                        assert(m@.face_half_edges[fp] == he as int);
                    }
                };
            }
        }

        f += 1;
    }

    let mut h: usize = 0;
    while h < hcnt
        invariant
            vcnt == m.vertices.len(),
            ecnt == m.edges.len(),
            fcnt == m.faces.len(),
            hcnt == m.half_edges.len(),
            0 <= h <= hcnt,
            forall|hp: int| 0 <= hp < h as int ==> {
                let he = #[trigger] m@.half_edges[hp];
                &&& 0 <= he.twin < (hcnt as int)
                &&& 0 <= he.next < (hcnt as int)
                &&& 0 <= he.prev < (hcnt as int)
                &&& 0 <= he.vertex < (vcnt as int)
                &&& 0 <= he.edge < (ecnt as int)
                &&& 0 <= he.face < (fcnt as int)
            },
    {
        let he = &m.half_edges[h];
        if he.twin >= hcnt
            || he.next >= hcnt
            || he.prev >= hcnt
            || he.vertex >= vcnt
            || he.edge >= ecnt
            || he.face >= fcnt
        {
            return false;
        }

        proof {
            assert(m@.half_edges[h as int].twin == he.twin as int);
            assert(m@.half_edges[h as int].next == he.next as int);
            assert(m@.half_edges[h as int].prev == he.prev as int);
            assert(m@.half_edges[h as int].vertex == he.vertex as int);
            assert(m@.half_edges[h as int].edge == he.edge as int);
            assert(m@.half_edges[h as int].face == he.face as int);
            assert(0 <= m@.half_edges[h as int].twin < (hcnt as int));
            assert(0 <= m@.half_edges[h as int].next < (hcnt as int));
            assert(0 <= m@.half_edges[h as int].prev < (hcnt as int));
            assert(0 <= m@.half_edges[h as int].vertex < (vcnt as int));
            assert(0 <= m@.half_edges[h as int].edge < (ecnt as int));
            assert(0 <= m@.half_edges[h as int].face < (fcnt as int));

            assert(forall|hp: int| 0 <= hp < (h + 1) as int ==> {
                let he2 = #[trigger] m@.half_edges[hp];
                &&& 0 <= he2.twin < (hcnt as int)
                &&& 0 <= he2.next < (hcnt as int)
                &&& 0 <= he2.prev < (hcnt as int)
                &&& 0 <= he2.vertex < (vcnt as int)
                &&& 0 <= he2.edge < (ecnt as int)
                &&& 0 <= he2.face < (fcnt as int)
            }) by {
                assert forall|hp: int| 0 <= hp < (h + 1) as int implies {
                    let he2 = #[trigger] m@.half_edges[hp];
                    &&& 0 <= he2.twin < (hcnt as int)
                    &&& 0 <= he2.next < (hcnt as int)
                    &&& 0 <= he2.prev < (hcnt as int)
                    &&& 0 <= he2.vertex < (vcnt as int)
                    &&& 0 <= he2.edge < (ecnt as int)
                    &&& 0 <= he2.face < (fcnt as int)
                } by {
                    if hp < h as int {
                        assert(0 <= hp < h as int);
                    } else {
                        assert(hp == h as int);
                        assert(0 <= m@.half_edges[hp].twin < (hcnt as int));
                        assert(0 <= m@.half_edges[hp].next < (hcnt as int));
                        assert(0 <= m@.half_edges[hp].prev < (hcnt as int));
                        assert(0 <= m@.half_edges[hp].vertex < (vcnt as int));
                        assert(0 <= m@.half_edges[hp].edge < (ecnt as int));
                        assert(0 <= m@.half_edges[hp].face < (fcnt as int));
                    }
                };
            }
        }

        h += 1;
    }

    proof {
        assert(v == vcnt);
        assert(e == ecnt);
        assert(f == fcnt);
        assert(h == hcnt);

        assert(mesh_vertex_count_spec(m@) == m@.vertex_half_edges.len() as int);
        assert(mesh_edge_count_spec(m@) == m@.edge_half_edges.len() as int);
        assert(mesh_face_count_spec(m@) == m@.face_half_edges.len() as int);
        assert(mesh_half_edge_count_spec(m@) == m@.half_edges.len() as int);

        assert(m@.vertex_half_edges.len() == m.vertices@.len());
        assert(m@.edge_half_edges.len() == m.edges@.len());
        assert(m@.face_half_edges.len() == m.faces@.len());
        assert(m@.half_edges.len() == m.half_edges@.len());

        assert(m.vertices@.len() == m.vertices.len());
        assert(m.edges@.len() == m.edges.len());
        assert(m.faces@.len() == m.faces.len());
        assert(m.half_edges@.len() == m.half_edges.len());

        assert(mesh_vertex_count_spec(m@) == vcnt as int);
        assert(mesh_edge_count_spec(m@) == ecnt as int);
        assert(mesh_face_count_spec(m@) == fcnt as int);
        assert(mesh_half_edge_count_spec(m@) == hcnt as int);

        assert(forall|vp: int|
            0 <= vp < mesh_vertex_count_spec(m@)
                ==> 0 <= #[trigger] m@.vertex_half_edges[vp] < mesh_half_edge_count_spec(m@)) by {
            assert forall|vp: int|
                0 <= vp < mesh_vertex_count_spec(m@)
                    implies 0 <= #[trigger] m@.vertex_half_edges[vp] < mesh_half_edge_count_spec(m@) by {
                assert(mesh_vertex_count_spec(m@) == v as int);
                assert(mesh_half_edge_count_spec(m@) == hcnt as int);
                assert(0 <= vp < v as int);
            };
        }
        assert(forall|ep: int|
            0 <= ep < mesh_edge_count_spec(m@)
                ==> 0 <= #[trigger] m@.edge_half_edges[ep] < mesh_half_edge_count_spec(m@)) by {
            assert forall|ep: int|
                0 <= ep < mesh_edge_count_spec(m@)
                    implies 0 <= #[trigger] m@.edge_half_edges[ep] < mesh_half_edge_count_spec(m@) by {
                assert(mesh_edge_count_spec(m@) == e as int);
                assert(mesh_half_edge_count_spec(m@) == hcnt as int);
                assert(0 <= ep < e as int);
            };
        }
        assert(forall|fp: int|
            0 <= fp < mesh_face_count_spec(m@)
                ==> 0 <= #[trigger] m@.face_half_edges[fp] < mesh_half_edge_count_spec(m@)) by {
            assert forall|fp: int|
                0 <= fp < mesh_face_count_spec(m@)
                    implies 0 <= #[trigger] m@.face_half_edges[fp] < mesh_half_edge_count_spec(m@) by {
                assert(mesh_face_count_spec(m@) == f as int);
                assert(mesh_half_edge_count_spec(m@) == hcnt as int);
                assert(0 <= fp < f as int);
            };
        }
        assert(forall|hp: int| 0 <= hp < mesh_half_edge_count_spec(m@) ==> {
            let he = #[trigger] m@.half_edges[hp];
            &&& 0 <= he.twin < mesh_half_edge_count_spec(m@)
            &&& 0 <= he.next < mesh_half_edge_count_spec(m@)
            &&& 0 <= he.prev < mesh_half_edge_count_spec(m@)
            &&& 0 <= he.vertex < mesh_vertex_count_spec(m@)
            &&& 0 <= he.edge < mesh_edge_count_spec(m@)
            &&& 0 <= he.face < mesh_face_count_spec(m@)
        }) by {
            assert forall|hp: int| 0 <= hp < mesh_half_edge_count_spec(m@) implies {
                let he = #[trigger] m@.half_edges[hp];
                &&& 0 <= he.twin < mesh_half_edge_count_spec(m@)
                &&& 0 <= he.next < mesh_half_edge_count_spec(m@)
                &&& 0 <= he.prev < mesh_half_edge_count_spec(m@)
                &&& 0 <= he.vertex < mesh_vertex_count_spec(m@)
                &&& 0 <= he.edge < mesh_edge_count_spec(m@)
                &&& 0 <= he.face < mesh_face_count_spec(m@)
            } by {
                assert(mesh_half_edge_count_spec(m@) == h as int);
                assert(mesh_vertex_count_spec(m@) == vcnt as int);
                assert(mesh_edge_count_spec(m@) == ecnt as int);
                assert(mesh_face_count_spec(m@) == fcnt as int);
                assert(0 <= hp < h as int);
            };
        }
        assert(mesh_index_bounds_spec(m@));
    }

    true
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

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_twin_endpoint_correspondence(m: &Mesh) -> (out: bool)
    ensures
        out ==> from_face_cycles_twin_endpoint_correspondence_spec(m@),
{
    let index_ok = runtime_check_index_bounds(m);
    if !index_ok {
        return false;
    }

    let hcnt = m.half_edges.len();
    let mut h: usize = 0;
    while h < hcnt
        invariant
            hcnt == m.half_edges.len(),
            mesh_index_bounds_spec(m@),
            0 <= h <= hcnt,
            forall|hp: int|
                #![trigger m@.half_edges[hp].twin]
                0 <= hp < h as int ==> from_face_cycles_twin_endpoint_correspondence_at_spec(m@, hp),
    {
        let he = &m.half_edges[h];
        let t = he.twin;
        if t >= hcnt {
            return false;
        }
        let n = he.next;
        if n >= hcnt {
            return false;
        }
        let tn = m.half_edges[t].next;
        if tn >= hcnt {
            return false;
        }

        let from_h = he.vertex;
        let to_h = m.half_edges[n].vertex;
        let from_t = m.half_edges[t].vertex;
        let to_t = m.half_edges[tn].vertex;

        if from_t != to_h {
            return false;
        }
        if to_t != from_h {
            return false;
        }

        proof {
            assert(mesh_half_edge_count_spec(m@) == hcnt as int);
            assert(m@.half_edges[h as int].twin == t as int);
            assert(m@.half_edges[h as int].next == n as int);
            assert(m@.half_edges[h as int].vertex == from_h as int);
            assert(m@.half_edges[n as int].vertex == to_h as int);
            assert(m@.half_edges[t as int].next == tn as int);
            assert(m@.half_edges[t as int].vertex == from_t as int);
            assert(m@.half_edges[tn as int].vertex == to_t as int);

            assert(mesh_half_edge_from_vertex_spec(m@, t as int) == from_t as int);
            assert(mesh_half_edge_to_vertex_spec(m@, h as int) == to_h as int);
            assert(mesh_half_edge_to_vertex_spec(m@, t as int) == to_t as int);
            assert(mesh_half_edge_from_vertex_spec(m@, h as int) == from_h as int);
            assert(from_t as int == to_h as int);
            assert(to_t as int == from_h as int);
            assert(from_face_cycles_twin_endpoint_correspondence_at_spec(m@, h as int));

            assert(forall|hp: int|
                #![trigger m@.half_edges[hp].twin]
                0 <= hp < (h + 1) as int
                    ==> from_face_cycles_twin_endpoint_correspondence_at_spec(m@, hp)) by {
                assert forall|hp: int|
                    #![trigger m@.half_edges[hp].twin]
                    0 <= hp < (h + 1) as int
                        implies from_face_cycles_twin_endpoint_correspondence_at_spec(m@, hp) by {
                    if hp < h as int {
                        assert(0 <= hp < h as int);
                    } else {
                        assert(hp == h as int);
                        assert(from_face_cycles_twin_endpoint_correspondence_at_spec(m@, hp));
                    }
                };
            };
        }

        h += 1;
    }

    proof {
        assert(index_ok);
        assert(mesh_half_edge_count_spec(m@) == hcnt as int);
        assert(forall|hp: int|
            #![trigger m@.half_edges[hp].twin]
            0 <= hp < mesh_half_edge_count_spec(m@)
                ==> from_face_cycles_twin_endpoint_correspondence_at_spec(m@, hp)) by {
            assert forall|hp: int|
                #![trigger m@.half_edges[hp].twin]
                0 <= hp < mesh_half_edge_count_spec(m@)
                    implies from_face_cycles_twin_endpoint_correspondence_at_spec(m@, hp) by {
                assert(mesh_half_edge_count_spec(m@) == h as int);
                assert(0 <= hp < h as int);
            };
        };
        assert(from_face_cycles_twin_endpoint_correspondence_spec(m@));
    }
    true
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_from_face_cycles_undirected_edge_equivalence(m: &Mesh) -> (out: bool)
    ensures
        out ==> from_face_cycles_undirected_edge_equivalence_spec(m@),
{
    let index_ok = runtime_check_index_bounds(m);
    if !index_ok {
        return false;
    }

    let hcnt = m.half_edges.len();
    let mut h1: usize = 0;
    while h1 < hcnt
        invariant
            hcnt == m.half_edges.len(),
            mesh_index_bounds_spec(m@),
            0 <= h1 <= hcnt,
            forall|hp1: int, hp2: int|
                #![trigger from_face_cycles_undirected_edge_pair_equivalent_spec(m@, hp1, hp2)]
                0 <= hp1 < h1 as int && 0 <= hp2 < hcnt as int
                    ==> from_face_cycles_undirected_edge_pair_equivalent_spec(m@, hp1, hp2),
    {
        let mut h2: usize = 0;
        while h2 < hcnt
            invariant
                hcnt == m.half_edges.len(),
                mesh_index_bounds_spec(m@),
                0 <= h1 < hcnt,
                0 <= h2 <= hcnt,
                forall|hp1: int, hp2: int|
                    #![trigger from_face_cycles_undirected_edge_pair_equivalent_spec(m@, hp1, hp2)]
                    0 <= hp1 < h1 as int && 0 <= hp2 < hcnt as int
                        ==> from_face_cycles_undirected_edge_pair_equivalent_spec(m@, hp1, hp2),
                forall|hp2: int|
                    #![trigger from_face_cycles_undirected_edge_pair_equivalent_spec(m@, h1 as int, hp2)]
                    0 <= hp2 < h2 as int
                        ==> from_face_cycles_undirected_edge_pair_equivalent_spec(m@, h1 as int, hp2),
        {
            let he1 = &m.half_edges[h1];
            let he2 = &m.half_edges[h2];
            let n1 = he1.next;
            let n2 = he2.next;
            if n1 >= hcnt || n2 >= hcnt {
                return false;
            }

            let from1 = he1.vertex;
            let to1 = m.half_edges[n1].vertex;
            let from2 = he2.vertex;
            let to2 = m.half_edges[n2].vertex;

            let key1_a = if from1 <= to1 { from1 } else { to1 };
            let key1_b = if from1 <= to1 { to1 } else { from1 };
            let key2_a = if from2 <= to2 { from2 } else { to2 };
            let key2_b = if from2 <= to2 { to2 } else { from2 };
            let same_edge = he1.edge == he2.edge;
            let same_key = key1_a == key2_a && key1_b == key2_b;
            if same_edge != same_key {
                return false;
            }

            proof {
                let h1i = h1 as int;
                let h2i = h2 as int;
                let key1_model = mesh_undirected_key_spec(
                    mesh_half_edge_from_vertex_spec(m@, h1i),
                    mesh_half_edge_to_vertex_spec(m@, h1i),
                );
                let key2_model = mesh_undirected_key_spec(
                    mesh_half_edge_from_vertex_spec(m@, h2i),
                    mesh_half_edge_to_vertex_spec(m@, h2i),
                );

                assert(mesh_half_edge_count_spec(m@) == hcnt as int);
                assert(0 <= h1i < hcnt as int);
                assert(0 <= h2i < hcnt as int);
                assert(m@.half_edges[h1i].edge == he1.edge as int);
                assert(m@.half_edges[h2i].edge == he2.edge as int);
                assert(m@.half_edges[h1i].next == n1 as int);
                assert(m@.half_edges[h2i].next == n2 as int);
                assert(m@.half_edges[h1i].vertex == from1 as int);
                assert(m@.half_edges[h2i].vertex == from2 as int);
                assert(m@.half_edges[n1 as int].vertex == to1 as int);
                assert(m@.half_edges[n2 as int].vertex == to2 as int);
                assert(mesh_half_edge_from_vertex_spec(m@, h1i) == from1 as int);
                assert(mesh_half_edge_to_vertex_spec(m@, h1i) == to1 as int);
                assert(mesh_half_edge_from_vertex_spec(m@, h2i) == from2 as int);
                assert(mesh_half_edge_to_vertex_spec(m@, h2i) == to2 as int);

                if from1 <= to1 {
                    assert(key1_a == from1);
                    assert(key1_b == to1);
                    assert(key1_model == (key1_a as int, key1_b as int));
                } else {
                    assert(key1_a == to1);
                    assert(key1_b == from1);
                    assert(key1_model == (key1_a as int, key1_b as int));
                }
                if from2 <= to2 {
                    assert(key2_a == from2);
                    assert(key2_b == to2);
                    assert(key2_model == (key2_a as int, key2_b as int));
                } else {
                    assert(key2_a == to2);
                    assert(key2_b == from2);
                    assert(key2_model == (key2_a as int, key2_b as int));
                }

                if same_edge {
                    assert(same_key);
                    assert(m@.half_edges[h1i].edge == m@.half_edges[h2i].edge);
                    assert(key1_a == key2_a);
                    assert(key1_b == key2_b);
                    assert((key1_a as int, key1_b as int) == (key2_a as int, key2_b as int));
                    assert(key1_model == key2_model);
                } else {
                    assert(!same_key);
                    assert(m@.half_edges[h1i].edge != m@.half_edges[h2i].edge);
                    assert(key1_a != key2_a || key1_b != key2_b);
                    assert((key1_a as int, key1_b as int) != (key2_a as int, key2_b as int));
                    assert(key1_model != key2_model);
                }
                assert(from_face_cycles_undirected_edge_pair_equivalent_spec(m@, h1i, h2i));

                assert(forall|hp2: int|
                    #![trigger from_face_cycles_undirected_edge_pair_equivalent_spec(m@, h1 as int, hp2)]
                    0 <= hp2 < (h2 + 1) as int
                        ==> from_face_cycles_undirected_edge_pair_equivalent_spec(m@, h1 as int, hp2)) by {
                    assert forall|hp2: int|
                        #![trigger from_face_cycles_undirected_edge_pair_equivalent_spec(m@, h1 as int, hp2)]
                        0 <= hp2 < (h2 + 1) as int
                            implies from_face_cycles_undirected_edge_pair_equivalent_spec(m@, h1 as int, hp2) by {
                        if hp2 < h2 as int {
                            assert(0 <= hp2 < h2 as int);
                        } else {
                            assert(hp2 == h2 as int);
                            assert(from_face_cycles_undirected_edge_pair_equivalent_spec(m@, h1 as int, hp2));
                        }
                    };
                };
            }

            h2 += 1;
        }

        proof {
            assert(h2 == hcnt);
            assert(forall|hp1: int, hp2: int|
                #![trigger from_face_cycles_undirected_edge_pair_equivalent_spec(m@, hp1, hp2)]
                0 <= hp1 < (h1 + 1) as int && 0 <= hp2 < hcnt as int
                    ==> from_face_cycles_undirected_edge_pair_equivalent_spec(m@, hp1, hp2)) by {
                assert forall|hp1: int, hp2: int|
                    #![trigger from_face_cycles_undirected_edge_pair_equivalent_spec(m@, hp1, hp2)]
                    0 <= hp1 < (h1 + 1) as int && 0 <= hp2 < hcnt as int
                        implies from_face_cycles_undirected_edge_pair_equivalent_spec(m@, hp1, hp2) by {
                    if hp1 < h1 as int {
                        assert(0 <= hp1 < h1 as int);
                    } else {
                        assert(hp1 == h1 as int);
                        assert(0 <= hp2 < h2 as int);
                    }
                };
            };
        }

        h1 += 1;
    }

    proof {
        assert(index_ok);
        assert(h1 == hcnt);
        assert(mesh_half_edge_count_spec(m@) == hcnt as int);
        assert(forall|hp1: int, hp2: int|
            #![trigger from_face_cycles_undirected_edge_pair_equivalent_spec(m@, hp1, hp2)]
            0 <= hp1 < mesh_half_edge_count_spec(m@)
                && 0 <= hp2 < mesh_half_edge_count_spec(m@)
                ==> from_face_cycles_undirected_edge_pair_equivalent_spec(m@, hp1, hp2)) by {
            assert forall|hp1: int, hp2: int|
                #![trigger from_face_cycles_undirected_edge_pair_equivalent_spec(m@, hp1, hp2)]
                0 <= hp1 < mesh_half_edge_count_spec(m@)
                    && 0 <= hp2 < mesh_half_edge_count_spec(m@)
                    implies from_face_cycles_undirected_edge_pair_equivalent_spec(m@, hp1, hp2) by {
                assert(mesh_half_edge_count_spec(m@) == h1 as int);
                assert(0 <= hp1 < h1 as int);
                assert(0 <= hp2 < hcnt as int);
            };
        };
        assert(from_face_cycles_undirected_edge_equivalence_spec(m@));
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
pub fn runtime_check_prev_next_inverse(m: &Mesh) -> (out: bool)
    ensures
        out ==> mesh_prev_next_inverse_spec(m@),
{
    let hcnt = m.half_edges.len();
    let mut h: usize = 0;
    while h < hcnt
        invariant
            hcnt == m.half_edges.len(),
            0 <= h <= hcnt,
            forall|hp: int|
                0 <= hp < h as int
                    ==> #[trigger] m@.half_edges[m@.half_edges[hp].next].prev == hp,
            forall|hp: int|
                0 <= hp < h as int
                    ==> #[trigger] m@.half_edges[m@.half_edges[hp].prev].next == hp,
    {
        let he = &m.half_edges[h];
        let n = he.next;
        let p = he.prev;
        if n >= hcnt || p >= hcnt {
            return false;
        }
        if m.half_edges[n].prev != h {
            return false;
        }
        if m.half_edges[p].next != h {
            return false;
        }

        proof {
            assert(mesh_half_edge_count_spec(m@) == hcnt as int);
            assert(m@.half_edges[h as int].next == n as int);
            assert(m@.half_edges[h as int].prev == p as int);
            assert(m@.half_edges[n as int].prev == m.half_edges@[n as int].prev);
            assert(m@.half_edges[p as int].next == m.half_edges@[p as int].next);
            assert(m.half_edges@[n as int].prev == h as int);
            assert(m.half_edges@[p as int].next == h as int);
            assert(#[trigger] m@.half_edges[m@.half_edges[h as int].next].prev == h as int);
            assert(#[trigger] m@.half_edges[m@.half_edges[h as int].prev].next == h as int);

            assert(forall|hp: int|
                0 <= hp < (h + 1) as int
                    ==> #[trigger] m@.half_edges[m@.half_edges[hp].next].prev == hp) by {
                assert forall|hp: int|
                    0 <= hp < (h + 1) as int
                        implies #[trigger] m@.half_edges[m@.half_edges[hp].next].prev == hp by {
                    if hp < h as int {
                        assert(0 <= hp < h as int);
                    } else {
                        assert(hp == h as int);
                        assert(#[trigger] m@.half_edges[m@.half_edges[hp].next].prev == hp);
                    }
                };
            };
            assert(forall|hp: int|
                0 <= hp < (h + 1) as int
                    ==> #[trigger] m@.half_edges[m@.half_edges[hp].prev].next == hp) by {
                assert forall|hp: int|
                    0 <= hp < (h + 1) as int
                        implies #[trigger] m@.half_edges[m@.half_edges[hp].prev].next == hp by {
                    if hp < h as int {
                        assert(0 <= hp < h as int);
                    } else {
                        assert(hp == h as int);
                        assert(#[trigger] m@.half_edges[m@.half_edges[hp].prev].next == hp);
                    }
                };
            };
        }

        h += 1;
    }

    proof {
        assert(mesh_half_edge_count_spec(m@) == hcnt as int);
        assert(forall|hp: int|
            0 <= hp < mesh_half_edge_count_spec(m@)
                ==> #[trigger] m@.half_edges[m@.half_edges[hp].next].prev == hp) by {
            assert forall|hp: int|
                0 <= hp < mesh_half_edge_count_spec(m@)
                    implies #[trigger] m@.half_edges[m@.half_edges[hp].next].prev == hp by {
                assert(mesh_half_edge_count_spec(m@) == h as int);
                assert(0 <= hp < h as int);
            };
        };
        assert(forall|hp: int|
            0 <= hp < mesh_half_edge_count_spec(m@)
                ==> #[trigger] m@.half_edges[m@.half_edges[hp].prev].next == hp) by {
            assert forall|hp: int|
                0 <= hp < mesh_half_edge_count_spec(m@)
                    implies #[trigger] m@.half_edges[m@.half_edges[hp].prev].next == hp by {
                assert(mesh_half_edge_count_spec(m@) == h as int);
                assert(0 <= hp < h as int);
            };
        };
        assert(mesh_prev_next_inverse_spec(m@)) by {
            assert forall|hp: int| 0 <= hp < mesh_half_edge_count_spec(m@) implies {
                &&& #[trigger] m@.half_edges[m@.half_edges[hp].next].prev == hp
                &&& #[trigger] m@.half_edges[m@.half_edges[hp].prev].next == hp
            } by {
                assert(#[trigger] m@.half_edges[m@.half_edges[hp].next].prev == hp);
                assert(#[trigger] m@.half_edges[m@.half_edges[hp].prev].next == hp);
            };
        };
    }
    true
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_no_degenerate_edges(m: &Mesh) -> (out: bool)
    ensures
        out ==> mesh_no_degenerate_edges_spec(m@),
{
    let hcnt = m.half_edges.len();
    let mut h: usize = 0;
    while h < hcnt
        invariant
            hcnt == m.half_edges.len(),
            0 <= h <= hcnt,
            forall|hp: int|
                0 <= hp < h as int
                    ==> #[trigger] m@.half_edges[hp].vertex
                        != m@.half_edges[m@.half_edges[hp].twin].vertex,
            forall|hp: int|
                0 <= hp < h as int
                    ==> #[trigger] m@.half_edges[hp].vertex
                        != m@.half_edges[m@.half_edges[hp].next].vertex,
    {
        let he = &m.half_edges[h];
        let t = he.twin;
        let n = he.next;
        if t >= hcnt || n >= hcnt {
            return false;
        }
        let tv = m.half_edges[t].vertex;
        if he.vertex == tv {
            return false;
        }
        let nv = m.half_edges[n].vertex;
        if he.vertex == nv {
            return false;
        }

        proof {
            assert(mesh_half_edge_count_spec(m@) == hcnt as int);
            assert(m@.half_edges[h as int].twin == t as int);
            assert(m@.half_edges[h as int].next == n as int);
            assert(m@.half_edges[h as int].vertex == he.vertex as int);
            assert(m@.half_edges[t as int].vertex == m.half_edges@[t as int].vertex);
            assert(m@.half_edges[n as int].vertex == m.half_edges@[n as int].vertex);
            assert(m.half_edges@[t as int].vertex == tv as int);
            assert(m.half_edges@[n as int].vertex == nv as int);
            assert(he.vertex as int != tv as int);
            assert(he.vertex as int != nv as int);
            assert(#[trigger] m@.half_edges[h as int].vertex
                != m@.half_edges[m@.half_edges[h as int].twin].vertex);
            assert(#[trigger] m@.half_edges[h as int].vertex
                != m@.half_edges[m@.half_edges[h as int].next].vertex);

            assert(forall|hp: int|
                0 <= hp < (h + 1) as int
                    ==> #[trigger] m@.half_edges[hp].vertex
                        != m@.half_edges[m@.half_edges[hp].twin].vertex) by {
                assert forall|hp: int|
                    0 <= hp < (h + 1) as int
                        implies #[trigger] m@.half_edges[hp].vertex
                            != m@.half_edges[m@.half_edges[hp].twin].vertex by {
                    if hp < h as int {
                        assert(0 <= hp < h as int);
                    } else {
                        assert(hp == h as int);
                        assert(#[trigger] m@.half_edges[hp].vertex
                            != m@.half_edges[m@.half_edges[hp].twin].vertex);
                    }
                };
            };
            assert(forall|hp: int|
                0 <= hp < (h + 1) as int
                    ==> #[trigger] m@.half_edges[hp].vertex
                        != m@.half_edges[m@.half_edges[hp].next].vertex) by {
                assert forall|hp: int|
                    0 <= hp < (h + 1) as int
                        implies #[trigger] m@.half_edges[hp].vertex
                            != m@.half_edges[m@.half_edges[hp].next].vertex by {
                    if hp < h as int {
                        assert(0 <= hp < h as int);
                    } else {
                        assert(hp == h as int);
                        assert(#[trigger] m@.half_edges[hp].vertex
                            != m@.half_edges[m@.half_edges[hp].next].vertex);
                    }
                };
            };
        }

        h += 1;
    }

    proof {
        assert(mesh_half_edge_count_spec(m@) == hcnt as int);
        assert(forall|hp: int|
            0 <= hp < mesh_half_edge_count_spec(m@)
                ==> #[trigger] m@.half_edges[hp].vertex
                    != m@.half_edges[m@.half_edges[hp].twin].vertex) by {
            assert forall|hp: int|
                0 <= hp < mesh_half_edge_count_spec(m@)
                    implies #[trigger] m@.half_edges[hp].vertex
                        != m@.half_edges[m@.half_edges[hp].twin].vertex by {
                assert(mesh_half_edge_count_spec(m@) == h as int);
                assert(0 <= hp < h as int);
            };
        };
        assert(forall|hp: int|
            0 <= hp < mesh_half_edge_count_spec(m@)
                ==> #[trigger] m@.half_edges[hp].vertex
                    != m@.half_edges[m@.half_edges[hp].next].vertex) by {
            assert forall|hp: int|
                0 <= hp < mesh_half_edge_count_spec(m@)
                    implies #[trigger] m@.half_edges[hp].vertex
                        != m@.half_edges[m@.half_edges[hp].next].vertex by {
                assert(mesh_half_edge_count_spec(m@) == h as int);
                assert(0 <= hp < h as int);
            };
        };
        assert(mesh_no_degenerate_edges_spec(m@)) by {
            assert forall|hp: int| 0 <= hp < mesh_half_edge_count_spec(m@) implies {
                &&& #[trigger] m@.half_edges[hp].vertex != m@.half_edges[m@.half_edges[hp].twin].vertex
                &&& #[trigger] m@.half_edges[hp].vertex != m@.half_edges[m@.half_edges[hp].next].vertex
            } by {
                assert(#[trigger] m@.half_edges[hp].vertex
                    != m@.half_edges[m@.half_edges[hp].twin].vertex);
                assert(#[trigger] m@.half_edges[hp].vertex
                    != m@.half_edges[m@.half_edges[hp].next].vertex);
            };
        };
    }
    true
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
        assert(!(v < m.vertices.len()));
        lemma_usize_loop_exit_eq(v, m.vertices.len());
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

#[verifier::exec_allows_no_decreases_clause]
pub fn runtime_mesh_to_kernel_mesh(m: &Mesh) -> (km: kernels::KernelMesh)
    ensures
        kernel_mesh_matches_mesh_model_spec(&km, m@),
{
    let mut vertex_half_edges: Vec<usize> = Vec::new();
    let mut v: usize = 0;
    while v < m.vertices.len()
        invariant
            0 <= v <= m.vertices.len(),
            vertex_half_edges@.len() == v as int,
            forall|vp: int|
                0 <= vp < v as int
                    ==> (#[trigger] vertex_half_edges@[vp] as int) == m@.vertex_half_edges[vp],
    {
        let he = m.vertices[v].half_edge;
        vertex_half_edges.push(he);
        proof {
            assert(m@.vertex_half_edges[v as int] == he as int);
            assert(forall|vp: int|
                0 <= vp < (v + 1) as int
                    ==> (#[trigger] vertex_half_edges@[vp] as int) == m@.vertex_half_edges[vp]) by {
                assert forall|vp: int|
                    0 <= vp < (v + 1) as int
                        implies (#[trigger] vertex_half_edges@[vp] as int) == m@.vertex_half_edges[vp] by {
                    if vp < v as int {
                    } else {
                        assert(vp == v as int);
                        assert(vertex_half_edges@[vp] == he);
                    }
                };
            };
        }
        v += 1;
    }

    let mut edge_half_edges: Vec<usize> = Vec::new();
    let mut e: usize = 0;
    while e < m.edges.len()
        invariant
            0 <= e <= m.edges.len(),
            edge_half_edges@.len() == e as int,
            forall|ep: int|
                0 <= ep < e as int
                    ==> (#[trigger] edge_half_edges@[ep] as int) == m@.edge_half_edges[ep],
    {
        let he = m.edges[e].half_edge;
        edge_half_edges.push(he);
        proof {
            assert(m@.edge_half_edges[e as int] == he as int);
            assert(forall|ep: int|
                0 <= ep < (e + 1) as int
                    ==> (#[trigger] edge_half_edges@[ep] as int) == m@.edge_half_edges[ep]) by {
                assert forall|ep: int|
                    0 <= ep < (e + 1) as int
                        implies (#[trigger] edge_half_edges@[ep] as int) == m@.edge_half_edges[ep] by {
                    if ep < e as int {
                    } else {
                        assert(ep == e as int);
                        assert(edge_half_edges@[ep] == he);
                    }
                };
            };
        }
        e += 1;
    }

    let mut face_half_edges: Vec<usize> = Vec::new();
    let mut f: usize = 0;
    while f < m.faces.len()
        invariant
            0 <= f <= m.faces.len(),
            face_half_edges@.len() == f as int,
            forall|fp: int|
                0 <= fp < f as int
                    ==> (#[trigger] face_half_edges@[fp] as int) == m@.face_half_edges[fp],
    {
        let he = m.faces[f].half_edge;
        face_half_edges.push(he);
        proof {
            assert(m@.face_half_edges[f as int] == he as int);
            assert(forall|fp: int|
                0 <= fp < (f + 1) as int
                    ==> (#[trigger] face_half_edges@[fp] as int) == m@.face_half_edges[fp]) by {
                assert forall|fp: int|
                    0 <= fp < (f + 1) as int
                        implies (#[trigger] face_half_edges@[fp] as int) == m@.face_half_edges[fp] by {
                    if fp < f as int {
                    } else {
                        assert(fp == f as int);
                        assert(face_half_edges@[fp] == he);
                    }
                };
            };
        }
        f += 1;
    }

    let mut half_edges: Vec<kernels::KernelHalfEdge> = Vec::new();
    let mut h: usize = 0;
    while h < m.half_edges.len()
        invariant
            0 <= h <= m.half_edges.len(),
            half_edges@.len() == h as int,
            forall|hp: int| 0 <= hp < h as int ==> {
                let khe = #[trigger] half_edges@[hp];
                let mhe = m@.half_edges[hp];
                &&& (khe.twin as int) == mhe.twin
                &&& (khe.next as int) == mhe.next
                &&& (khe.prev as int) == mhe.prev
                &&& (khe.vertex as int) == mhe.vertex
                &&& (khe.edge as int) == mhe.edge
                &&& (khe.face as int) == mhe.face
            },
    {
        let he = &m.half_edges[h];
        let khe = kernels::KernelHalfEdge {
            twin: he.twin,
            next: he.next,
            prev: he.prev,
            vertex: he.vertex,
            edge: he.edge,
            face: he.face,
        };
        half_edges.push(khe);
        proof {
            assert(m@.half_edges[h as int].twin == he.twin as int);
            assert(m@.half_edges[h as int].next == he.next as int);
            assert(m@.half_edges[h as int].prev == he.prev as int);
            assert(m@.half_edges[h as int].vertex == he.vertex as int);
            assert(m@.half_edges[h as int].edge == he.edge as int);
            assert(m@.half_edges[h as int].face == he.face as int);
            assert(forall|hp: int| 0 <= hp < (h + 1) as int ==> {
                let khe0 = #[trigger] half_edges@[hp];
                let mhe0 = m@.half_edges[hp];
                &&& (khe0.twin as int) == mhe0.twin
                &&& (khe0.next as int) == mhe0.next
                &&& (khe0.prev as int) == mhe0.prev
                &&& (khe0.vertex as int) == mhe0.vertex
                &&& (khe0.edge as int) == mhe0.edge
                &&& (khe0.face as int) == mhe0.face
            }) by {
                assert forall|hp: int| 0 <= hp < (h + 1) as int implies {
                    let khe0 = #[trigger] half_edges@[hp];
                    let mhe0 = m@.half_edges[hp];
                    &&& (khe0.twin as int) == mhe0.twin
                    &&& (khe0.next as int) == mhe0.next
                    &&& (khe0.prev as int) == mhe0.prev
                    &&& (khe0.vertex as int) == mhe0.vertex
                    &&& (khe0.edge as int) == mhe0.edge
                    &&& (khe0.face as int) == mhe0.face
                } by {
                    if hp < h as int {
                    } else {
                        assert(hp == h as int);
                        assert(half_edges@[hp] == khe);
                    }
                };
            };
        }
        h += 1;
    }

    let km = kernels::KernelMesh {
        vertex_half_edges,
        edge_half_edges,
        face_half_edges,
        half_edges,
    };

    proof {
        assert(mesh_vertex_count_spec(m@) == m.vertices@.len() as int);
        assert(mesh_edge_count_spec(m@) == m.edges@.len() as int);
        assert(mesh_face_count_spec(m@) == m.faces@.len() as int);
        assert(mesh_half_edge_count_spec(m@) == m.half_edges@.len() as int);
        assert(m.vertices@.len() == m.vertices.len());
        assert(m.edges@.len() == m.edges.len());
        assert(m.faces@.len() == m.faces.len());
        assert(m.half_edges@.len() == m.half_edges.len());

        assert(km.vertex_half_edges@.len() == mesh_vertex_count_spec(m@));
        assert(km.edge_half_edges@.len() == mesh_edge_count_spec(m@));
        assert(km.face_half_edges@.len() == mesh_face_count_spec(m@));
        assert(km.half_edges@.len() == mesh_half_edge_count_spec(m@));

        assert(forall|vp: int|
            0 <= vp < mesh_vertex_count_spec(m@)
                ==> (#[trigger] km.vertex_half_edges@[vp] as int) == m@.vertex_half_edges[vp]) by {
            assert forall|vp: int|
                0 <= vp < mesh_vertex_count_spec(m@)
                    implies (#[trigger] km.vertex_half_edges@[vp] as int) == m@.vertex_half_edges[vp] by {
                assert(mesh_vertex_count_spec(m@) == v as int);
                assert(0 <= vp < v as int);
            };
        };
        assert(forall|ep: int|
            0 <= ep < mesh_edge_count_spec(m@)
                ==> (#[trigger] km.edge_half_edges@[ep] as int) == m@.edge_half_edges[ep]) by {
            assert forall|ep: int|
                0 <= ep < mesh_edge_count_spec(m@)
                    implies (#[trigger] km.edge_half_edges@[ep] as int) == m@.edge_half_edges[ep] by {
                assert(mesh_edge_count_spec(m@) == e as int);
                assert(0 <= ep < e as int);
            };
        };
        assert(forall|fp: int|
            0 <= fp < mesh_face_count_spec(m@)
                ==> (#[trigger] km.face_half_edges@[fp] as int) == m@.face_half_edges[fp]) by {
            assert forall|fp: int|
                0 <= fp < mesh_face_count_spec(m@)
                    implies (#[trigger] km.face_half_edges@[fp] as int) == m@.face_half_edges[fp] by {
                assert(mesh_face_count_spec(m@) == f as int);
                assert(0 <= fp < f as int);
            };
        };
        assert(forall|hp: int| 0 <= hp < mesh_half_edge_count_spec(m@) ==> {
            let khe0 = #[trigger] km.half_edges@[hp];
            let mhe0 = m@.half_edges[hp];
            &&& (khe0.twin as int) == mhe0.twin
            &&& (khe0.next as int) == mhe0.next
            &&& (khe0.prev as int) == mhe0.prev
            &&& (khe0.vertex as int) == mhe0.vertex
            &&& (khe0.edge as int) == mhe0.edge
            &&& (khe0.face as int) == mhe0.face
        }) by {
            assert forall|hp: int| 0 <= hp < mesh_half_edge_count_spec(m@) implies {
                let khe0 = #[trigger] km.half_edges@[hp];
                let mhe0 = m@.half_edges[hp];
                &&& (khe0.twin as int) == mhe0.twin
                &&& (khe0.next as int) == mhe0.next
                &&& (khe0.prev as int) == mhe0.prev
                &&& (khe0.vertex as int) == mhe0.vertex
                &&& (khe0.edge as int) == mhe0.edge
                &&& (khe0.face as int) == mhe0.face
            } by {
                assert(mesh_half_edge_count_spec(m@) == h as int);
                assert(0 <= hp < h as int);
            };
        };
        assert(kernel_mesh_matches_mesh_model_spec(&km, m@));
    }

    km
}

#[allow(dead_code)]
pub fn runtime_check_face_cycles_kernel_bridge(m: &Mesh) -> (out: bool)
    ensures
        out ==> mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_total_spec(m@),
{
    let km = runtime_mesh_to_kernel_mesh(m);
    let ok = kernels::kernel_check_face_cycles(&km);
    if !ok {
        return false;
    }
    proof {
        assert(kernels::kernel_face_representative_cycles_cover_all_half_edges_total_spec(&km));
        lemma_kernel_face_cycles_cover_all_matches_mesh(&km, m@);
        assert(mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_total_spec(m@));
    }
    true
}

#[allow(dead_code)]
pub fn runtime_check_vertex_manifold_kernel_bridge(m: &Mesh) -> (out: bool)
    ensures
        out ==> mesh_vertex_manifold_single_cycle_spec(m@),
{
    let km = runtime_mesh_to_kernel_mesh(m);
    let ok = kernels::kernel_check_vertex_manifold_single_cycle(&km);
    if !ok {
        return false;
    }
    proof {
        assert(kernels::kernel_vertex_manifold_single_cycle_total_spec(&km));
        lemma_kernel_vertex_manifold_total_implies_mesh_vertex_manifold(&km, m@);
        assert(mesh_vertex_manifold_single_cycle_spec(m@));
    }
    true
}

#[verifier::external_body]
pub fn ex_mesh_half_edge_components(m: &Mesh) -> (out: Vec<Vec<usize>>)
{
    m.half_edge_components_for_verification()
}

#[verifier::external_body]
pub fn ex_mesh_euler_characteristics_per_component(m: &Mesh) -> (out: Vec<isize>)
{
    m.euler_characteristics_per_component_for_verification()
}

#[verifier::external_body]
pub fn ex_mesh_check_euler_formula_closed_components(m: &Mesh) -> (out: bool)
{
    m.check_euler_formula_closed_components_for_verification()
}

#[verifier::external_body]
pub fn ex_mesh_tetrahedron() -> (out: Mesh)
{
    Mesh::tetrahedron()
}

#[verifier::external_body]
pub fn ex_mesh_cube() -> (out: Mesh)
{
    Mesh::cube()
}

#[verifier::external_body]
pub fn ex_mesh_triangular_prism() -> (out: Mesh)
{
    Mesh::triangular_prism()
}

#[allow(dead_code)]
pub fn runtime_check_mesh_counts(
    m: &Mesh,
    vertex_count: usize,
    edge_count: usize,
    face_count: usize,
    half_edge_count: usize,
) -> (out: bool)
    ensures
        out ==> mesh_counts_spec(
            m@,
            vertex_count as int,
            edge_count as int,
            face_count as int,
            half_edge_count as int,
        ),
{
    if m.vertices.len() != vertex_count {
        return false;
    }
    if m.edges.len() != edge_count {
        return false;
    }
    if m.faces.len() != face_count {
        return false;
    }
    if m.half_edges.len() != half_edge_count {
        return false;
    }

    proof {
        assert(mesh_vertex_count_spec(m@) == m@.vertex_half_edges.len() as int);
        assert(mesh_edge_count_spec(m@) == m@.edge_half_edges.len() as int);
        assert(mesh_face_count_spec(m@) == m@.face_half_edges.len() as int);
        assert(mesh_half_edge_count_spec(m@) == m@.half_edges.len() as int);

        assert(m@.vertex_half_edges.len() == m.vertices@.len());
        assert(m@.edge_half_edges.len() == m.edges@.len());
        assert(m@.face_half_edges.len() == m.faces@.len());
        assert(m@.half_edges.len() == m.half_edges@.len());

        assert(m.vertices@.len() == m.vertices.len());
        assert(m.edges@.len() == m.edges.len());
        assert(m.faces@.len() == m.faces.len());
        assert(m.half_edges@.len() == m.half_edges.len());

        assert(mesh_counts_spec(
            m@,
            vertex_count as int,
            edge_count as int,
            face_count as int,
            half_edge_count as int,
        ));
    }

    true
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
        assert(!(c < components.len()));
        lemma_usize_loop_exit_eq(c, components.len());
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
        assert(!(c < components.len()));
        lemma_usize_loop_exit_eq(c, components.len());
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
#[verifier::spinoff_prover]
#[verifier::rlimit(600)]
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
        assert(!(c < components.len()));
        lemma_usize_loop_exit_eq(c, components.len());
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

#[verifier::exec_allows_no_decreases_clause]
#[verifier::rlimit(300)]
#[allow(dead_code)]
pub fn runtime_check_half_edge_components_representative_connected(
    m: &Mesh,
    components: &[Vec<usize>],
) -> (out: bool)
    ensures
        out ==> mesh_half_edge_components_representative_connected_spec(m@, components@),
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
                    ==> mesh_half_edge_component_representative_connected_at_spec(m@, components@, cp),
    {
        let component = vstd::slice::slice_index_get(components, c);
        let clen = component.len();
        if clen == 0 {
            return false;
        }

        let rep = component[0];
        if rep >= hcnt {
            return false;
        }

        let mut seen = vec![false; hcnt];
        seen[rep] = true;
        proof {
            assert(*component == components@.index(c as int));
            assert(component@.len() == clen as int);
            assert(component@[0] == rep);
            lemma_mesh_half_edge_connected_refl(m@, rep as int);
            assert(seen@[rep as int]);
            assert(forall|hp: int|
                0 <= hp < hcnt as int && #[trigger] seen@[hp]
                    ==> mesh_half_edge_connected_spec(m@, rep as int, hp)) by {
                assert forall|hp: int|
                    0 <= hp < hcnt as int && #[trigger] seen@[hp]
                        implies mesh_half_edge_connected_spec(m@, rep as int, hp) by {
                    assert(hp == rep as int);
                };
            }
        }

        let mut pass: usize = 0;
        while pass < hcnt
            invariant
                hcnt == m.half_edges.len(),
                0 <= c < components.len(),
                *component == components@.index(c as int),
                clen == component.len(),
                component@.len() == clen as int,
                rep == component[0],
                rep < hcnt,
                seen@.len() == hcnt as int,
                seen@[rep as int],
                0 <= pass <= hcnt,
                forall|hp: int|
                    0 <= hp < hcnt as int && #[trigger] seen@[hp]
                        ==> mesh_half_edge_connected_spec(m@, rep as int, hp),
        {
            let mut h: usize = 0;
            while h < hcnt
                invariant
                    hcnt == m.half_edges.len(),
                    0 <= c < components.len(),
                    *component == components@.index(c as int),
                    clen == component.len(),
                    component@.len() == clen as int,
                    rep == component[0],
                    rep < hcnt,
                    seen@.len() == hcnt as int,
                    seen@[rep as int],
                    0 <= pass < hcnt || hcnt == 0,
                    0 <= h <= hcnt,
                    forall|hp: int|
                        0 <= hp < hcnt as int && #[trigger] seen@[hp]
                            ==> mesh_half_edge_connected_spec(m@, rep as int, hp),
            {
                if seen[h] {
                    let he = &m.half_edges[h];
                    let t = he.twin;
                    let n = he.next;
                    let p = he.prev;

                    if t >= hcnt || n >= hcnt || p >= hcnt {
                        return false;
                    }

                    if !seen[t] {
                        let ghost seen_before_t = seen@;
                        seen[t] = true;
                        proof {
                            assert(seen_before_t[h as int]);
                            assert(mesh_half_edge_connected_spec(m@, rep as int, h as int));
                            assert(m@.half_edges[h as int].twin == t as int);
                            assert(mesh_half_edge_direct_step_spec(m@, h as int, t as int));
                            lemma_mesh_half_edge_connected_extend_direct_step(m@, rep as int, h as int, t as int);
                            assert(mesh_half_edge_connected_spec(m@, rep as int, t as int));
                            assert(forall|hp: int|
                                0 <= hp < hcnt as int && #[trigger] seen@[hp]
                                    ==> mesh_half_edge_connected_spec(m@, rep as int, hp)) by {
                                assert forall|hp: int|
                                    0 <= hp < hcnt as int && #[trigger] seen@[hp]
                                        implies mesh_half_edge_connected_spec(m@, rep as int, hp) by {
                                    if hp == t as int {
                                        assert(mesh_half_edge_connected_spec(m@, rep as int, hp));
                                    } else {
                                        assert(seen_before_t[hp]);
                                        assert(mesh_half_edge_connected_spec(m@, rep as int, hp));
                                    }
                                };
                            }
                        }
                    }

                    if !seen[n] {
                        let ghost seen_before_n = seen@;
                        seen[n] = true;
                        proof {
                            assert(seen_before_n[h as int]);
                            assert(mesh_half_edge_connected_spec(m@, rep as int, h as int));
                            assert(m@.half_edges[h as int].next == n as int);
                            assert(mesh_half_edge_direct_step_spec(m@, h as int, n as int));
                            lemma_mesh_half_edge_connected_extend_direct_step(m@, rep as int, h as int, n as int);
                            assert(mesh_half_edge_connected_spec(m@, rep as int, n as int));
                            assert(forall|hp: int|
                                0 <= hp < hcnt as int && #[trigger] seen@[hp]
                                    ==> mesh_half_edge_connected_spec(m@, rep as int, hp)) by {
                                assert forall|hp: int|
                                    0 <= hp < hcnt as int && #[trigger] seen@[hp]
                                        implies mesh_half_edge_connected_spec(m@, rep as int, hp) by {
                                    if hp == n as int {
                                        assert(mesh_half_edge_connected_spec(m@, rep as int, hp));
                                    } else {
                                        assert(seen_before_n[hp]);
                                        assert(mesh_half_edge_connected_spec(m@, rep as int, hp));
                                    }
                                };
                            }
                        }
                    }

                    if !seen[p] {
                        let ghost seen_before_p = seen@;
                        seen[p] = true;
                        proof {
                            assert(seen_before_p[h as int]);
                            assert(mesh_half_edge_connected_spec(m@, rep as int, h as int));
                            assert(m@.half_edges[h as int].prev == p as int);
                            assert(mesh_half_edge_direct_step_spec(m@, h as int, p as int));
                            lemma_mesh_half_edge_connected_extend_direct_step(m@, rep as int, h as int, p as int);
                            assert(mesh_half_edge_connected_spec(m@, rep as int, p as int));
                            assert(forall|hp: int|
                                0 <= hp < hcnt as int && #[trigger] seen@[hp]
                                    ==> mesh_half_edge_connected_spec(m@, rep as int, hp)) by {
                                assert forall|hp: int|
                                    0 <= hp < hcnt as int && #[trigger] seen@[hp]
                                        implies mesh_half_edge_connected_spec(m@, rep as int, hp) by {
                                    if hp == p as int {
                                        assert(mesh_half_edge_connected_spec(m@, rep as int, hp));
                                    } else {
                                        assert(seen_before_p[hp]);
                                        assert(mesh_half_edge_connected_spec(m@, rep as int, hp));
                                    }
                                };
                            }
                        }
                    }
                }

                h += 1;
            }

            pass += 1;
        }

        let mut i: usize = 0;
        while i < clen
            invariant
                hcnt == m.half_edges.len(),
                0 <= c < components.len(),
                *component == components@.index(c as int),
                clen == component.len(),
                component@.len() == clen as int,
                rep == component[0],
                rep < hcnt,
                seen@.len() == hcnt as int,
                seen@[rep as int],
                0 <= i <= clen,
                forall|hp: int|
                    0 <= hp < hcnt as int && #[trigger] seen@[hp]
                        ==> mesh_half_edge_connected_spec(m@, rep as int, hp),
                forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < i as int
                        ==> 0 <= (component@[ip] as int)
                            && (component@[ip] as int) < (hcnt as int)
                            && #[trigger] seen@[component@[ip] as int],
        {
            let h = component[i];
            if h >= hcnt {
                return false;
            }
            if !seen[h] {
                return false;
            }

            proof {
                assert(component@[i as int] == h);
                assert(forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < (i + 1) as int
                        ==> 0 <= (component@[ip] as int)
                            && (component@[ip] as int) < (hcnt as int)
                            && #[trigger] seen@[component@[ip] as int]) by {
                    assert forall|ip: int|
                        #![trigger component@[ip]]
                        0 <= ip < (i + 1) as int
                            implies 0 <= (component@[ip] as int)
                                && (component@[ip] as int) < (hcnt as int)
                                && #[trigger] seen@[component@[ip] as int] by {
                        if ip < i as int {
                        } else {
                            assert(ip == i as int);
                            assert(component@[ip] as int == h as int);
                            assert(0 <= (h as int));
                            assert((h as int) < (hcnt as int));
                            assert(seen@[h as int]);
                        }
                    };
                }
            }

            i += 1;
        }

        proof {
            assert(i == clen);
            assert(mesh_half_edge_component_representative_connected_at_spec(m@, components@, c as int)) by {
                assert(0 <= c as int);
                assert((c as int) < (components@.len() as int));
                assert(components@[c as int]@.len() > 0);
                assert(mesh_half_edge_component_entry_spec(components@, c as int, 0) == rep as int);
                assert forall|h: int|
                    #![trigger mesh_half_edge_component_contains_spec(m@, components@, c as int, h)]
                    mesh_half_edge_component_contains_spec(m@, components@, c as int, h)
                        implies mesh_half_edge_connected_spec(
                        m@,
                        mesh_half_edge_component_entry_spec(components@, c as int, 0),
                        h,
                    ) by {
                    let ip = choose|ip: int| {
                        &&& 0 <= ip < components@[c as int]@.len() as int
                        &&& mesh_half_edge_component_entry_spec(components@, c as int, ip) == h
                    };
                    assert(components@[c as int] == *component);
                    assert(components@[c as int]@.len() == clen as int);
                    assert(0 <= ip < clen as int);
                    assert(component@[ip] as int == h);
                    assert(0 <= ip < i as int);
                    assert(seen@[h]);
                    assert(mesh_half_edge_connected_spec(m@, rep as int, h));
                };
            }
            assert(forall|cp: int|
                #![trigger components@[cp]@]
                0 <= cp < (c + 1) as int
                    ==> mesh_half_edge_component_representative_connected_at_spec(m@, components@, cp)) by {
                assert forall|cp: int|
                    #![trigger components@[cp]@]
                    0 <= cp < (c + 1) as int
                        implies mesh_half_edge_component_representative_connected_at_spec(m@, components@, cp) by {
                    if cp < c as int {
                    } else {
                        assert(cp == c as int);
                        assert(mesh_half_edge_component_representative_connected_at_spec(m@, components@, cp));
                    }
                };
            }
        }

        c += 1;
    }

    proof {
        assert(!(c < components.len()));
        lemma_usize_loop_exit_eq(c, components.len());
        assert(mesh_half_edge_components_representative_connected_spec(m@, components@)) by {
            assert forall|cp: int|
                #![trigger components@[cp]@]
                0 <= cp < components@.len() as int
                    implies mesh_half_edge_component_representative_connected_at_spec(m@, components@, cp) by {
                assert(components@.len() as int == c as int);
                assert(0 <= cp < c as int);
            };
        }
    }
    true
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_half_edge_components_representative_minimal(
    m: &Mesh,
    components: &[Vec<usize>],
) -> (out: bool)
    ensures
        out ==> mesh_half_edge_components_representative_minimal_spec(m@, components@),
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
                    ==> mesh_half_edge_component_representative_minimal_at_spec(m@, components@, cp),
    {
        let component = vstd::slice::slice_index_get(components, c);
        let clen = component.len();
        if clen == 0 {
            return false;
        }

        let rep = component[0];
        if rep >= hcnt {
            return false;
        }

        let mut i: usize = 0;
        while i < clen
            invariant
                hcnt == m.half_edges.len(),
                0 <= c < components.len(),
                *component == components@.index(c as int),
                clen == component.len(),
                component@.len() == clen as int,
                rep == component[0],
                rep < hcnt,
                0 <= i <= clen,
                forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < i as int
                        ==> 0 <= (component@[ip] as int)
                            && (component@[ip] as int) < (hcnt as int)
                            && (rep as int) <= #[trigger] (component@[ip] as int),
        {
            let h = component[i];
            if h >= hcnt {
                return false;
            }
            if rep > h {
                return false;
            }

            proof {
                assert(component@[i as int] == h);
                assert(forall|ip: int|
                    #![trigger component@[ip]]
                    0 <= ip < (i + 1) as int
                        ==> 0 <= (component@[ip] as int)
                            && (component@[ip] as int) < (hcnt as int)
                            && (rep as int) <= #[trigger] (component@[ip] as int)) by {
                    assert forall|ip: int|
                        #![trigger component@[ip]]
                        0 <= ip < (i + 1) as int
                            implies 0 <= (component@[ip] as int)
                                && (component@[ip] as int) < (hcnt as int)
                                && (rep as int) <= #[trigger] (component@[ip] as int) by {
                        if ip < i as int {
                        } else {
                            assert(ip == i as int);
                            assert(component@[ip] as int == h as int);
                            assert(0 <= (h as int));
                            assert((h as int) < (hcnt as int));
                            assert((rep as int) <= (h as int));
                        }
                    };
                }
            }

            i += 1;
        }

        proof {
            assert(i == clen);
            assert(mesh_half_edge_component_representative_minimal_at_spec(m@, components@, c as int)) by {
                assert(0 <= c as int);
                assert((c as int) < (components@.len() as int));
                assert(components@[c as int]@.len() > 0);
                assert(mesh_half_edge_component_entry_spec(components@, c as int, 0) == rep as int);
                assert forall|h: int|
                    #![trigger mesh_half_edge_component_contains_spec(m@, components@, c as int, h)]
                    mesh_half_edge_component_contains_spec(m@, components@, c as int, h)
                        implies mesh_half_edge_component_entry_spec(components@, c as int, 0) <= h by {
                    let ip = choose|ip: int| {
                        &&& 0 <= ip < components@[c as int]@.len() as int
                        &&& mesh_half_edge_component_entry_spec(components@, c as int, ip) == h
                    };
                    assert(components@[c as int] == *component);
                    assert(components@[c as int]@.len() == clen as int);
                    assert(0 <= ip < clen as int);
                    assert(0 <= ip < i as int);
                    assert(component@[ip] as int == h);
                    assert((rep as int) <= (component@[ip] as int));
                    assert(mesh_half_edge_component_entry_spec(components@, c as int, 0) == rep as int);
                };
            }
            assert(forall|cp: int|
                #![trigger components@[cp]@]
                0 <= cp < (c + 1) as int
                    ==> mesh_half_edge_component_representative_minimal_at_spec(m@, components@, cp)) by {
                assert forall|cp: int|
                    #![trigger components@[cp]@]
                    0 <= cp < (c + 1) as int
                        implies mesh_half_edge_component_representative_minimal_at_spec(m@, components@, cp) by {
                    if cp < c as int {
                    } else {
                        assert(cp == c as int);
                        assert(mesh_half_edge_component_representative_minimal_at_spec(m@, components@, cp));
                    }
                };
            }
        }

        c += 1;
    }

    proof {
        assert(!(c < components.len()));
        lemma_usize_loop_exit_eq(c, components.len());
        assert(mesh_half_edge_components_representative_minimal_spec(m@, components@)) by {
            assert forall|cp: int|
                #![trigger components@[cp]@]
                0 <= cp < components@.len() as int
                    implies mesh_half_edge_component_representative_minimal_at_spec(m@, components@, cp) by {
                assert(components@.len() as int == c as int);
                assert(0 <= cp < c as int);
            };
        }
    }
    true
}

#[verifier::exec_allows_no_decreases_clause]
#[verifier::rlimit(400)]
#[allow(dead_code)]
pub fn runtime_check_half_edge_components_representative_complete(
    m: &Mesh,
    components: &[Vec<usize>],
) -> (out: bool)
    ensures
        out ==> mesh_half_edge_components_representative_complete_spec(m@, components@),
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
                    ==> mesh_half_edge_component_representative_complete_at_spec(m@, components@, cp),
    {
        let component = vstd::slice::slice_index_get(components, c);
        let clen = component.len();
        if clen == 0 {
            return false;
        }

        let rep = component[0];
        if rep >= hcnt {
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
                rep == component[0],
                rep < hcnt,
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

        let mut h: usize = 0;
        while h < hcnt
            invariant
                hcnt == m.half_edges.len(),
                0 <= c < components.len(),
                *component == components@.index(c as int),
                clen == component.len(),
                component@.len() == clen as int,
                rep == component[0],
                rep < hcnt,
                in_component@.len() == hcnt as int,
                0 <= h <= hcnt,
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
                forall|hp: int|
                    #![trigger m@.half_edges[hp]]
                    0 <= hp < h as int ==> {
                        let t = m@.half_edges[hp].twin;
                        let n = m@.half_edges[hp].next;
                        let p = m@.half_edges[hp].prev;
                        &&& 0 <= t < hcnt as int
                        &&& 0 <= n < hcnt as int
                        &&& 0 <= p < hcnt as int
                    },
                forall|hp: int|
                    0 <= hp < h as int && #[trigger] in_component@[hp] ==> {
                        let t = m@.half_edges[hp].twin;
                        let n = m@.half_edges[hp].next;
                        let p = m@.half_edges[hp].prev;
                        &&& in_component@[t]
                        &&& in_component@[n]
                        &&& in_component@[p]
                    },
                forall|hp: int|
                    0 <= hp < h as int && !#[trigger] in_component@[hp] ==> {
                        let t = m@.half_edges[hp].twin;
                        let n = m@.half_edges[hp].next;
                        let p = m@.half_edges[hp].prev;
                        &&& !in_component@[t]
                        &&& !in_component@[n]
                        &&& !in_component@[p]
                    },
        {
            let he = &m.half_edges[h];
            let t = he.twin;
            let n = he.next;
            let p = he.prev;
            let h_in = in_component[h];
            if t >= hcnt || n >= hcnt || p >= hcnt {
                return false;
            }
            let t_in = in_component[t];
            let n_in = in_component[n];
            let p_in = in_component[p];
            if h_in {
                if !t_in || !n_in || !p_in {
                    return false;
                }
            } else {
                if t_in || n_in || p_in {
                    return false;
                }
            }

            proof {
                assert(m@.half_edges[h as int].twin == t as int);
                assert(m@.half_edges[h as int].next == n as int);
                assert(m@.half_edges[h as int].prev == p as int);
                assert(in_component@[h as int] == h_in);
                assert(in_component@[t as int] == t_in);
                assert(in_component@[n as int] == n_in);
                assert(in_component@[p as int] == p_in);

                assert(forall|hp: int|
                    #![trigger m@.half_edges[hp]]
                    0 <= hp < (h + 1) as int ==> {
                        let tp = m@.half_edges[hp].twin;
                        let np = m@.half_edges[hp].next;
                        let pp = m@.half_edges[hp].prev;
                        &&& 0 <= tp < hcnt as int
                        &&& 0 <= np < hcnt as int
                        &&& 0 <= pp < hcnt as int
                    }) by {
                    assert forall|hp: int|
                        #![trigger m@.half_edges[hp]]
                        0 <= hp < (h + 1) as int implies {
                            let tp = m@.half_edges[hp].twin;
                            let np = m@.half_edges[hp].next;
                            let pp = m@.half_edges[hp].prev;
                            &&& 0 <= tp < hcnt as int
                            &&& 0 <= np < hcnt as int
                            &&& 0 <= pp < hcnt as int
                        } by {
                        if hp < h as int {
                        } else {
                            assert(hp == h as int);
                            assert(m@.half_edges[hp].twin == t as int);
                            assert(m@.half_edges[hp].next == n as int);
                            assert(m@.half_edges[hp].prev == p as int);
                            assert(t < hcnt);
                            assert(n < hcnt);
                            assert(p < hcnt);
                        }
                    };
                };

                assert(forall|hp: int|
                    0 <= hp < (h + 1) as int && #[trigger] in_component@[hp] ==> {
                        let tp = m@.half_edges[hp].twin;
                        let np = m@.half_edges[hp].next;
                        let pp = m@.half_edges[hp].prev;
                        &&& in_component@[tp]
                        &&& in_component@[np]
                        &&& in_component@[pp]
                    }) by {
                    assert forall|hp: int|
                        0 <= hp < (h + 1) as int && #[trigger] in_component@[hp] implies {
                            let tp = m@.half_edges[hp].twin;
                            let np = m@.half_edges[hp].next;
                            let pp = m@.half_edges[hp].prev;
                            &&& in_component@[tp]
                            &&& in_component@[np]
                            &&& in_component@[pp]
                        } by {
                        if hp < h as int {
                        } else {
                            assert(hp == h as int);
                            assert(in_component@[h as int]);
                            assert(in_component@[t as int]);
                            assert(in_component@[n as int]);
                            assert(in_component@[p as int]);
                        }
                    };
                };

                assert(forall|hp: int|
                    0 <= hp < (h + 1) as int && !#[trigger] in_component@[hp] ==> {
                        let tp = m@.half_edges[hp].twin;
                        let np = m@.half_edges[hp].next;
                        let pp = m@.half_edges[hp].prev;
                        &&& !in_component@[tp]
                        &&& !in_component@[np]
                        &&& !in_component@[pp]
                    }) by {
                    assert forall|hp: int|
                        0 <= hp < (h + 1) as int && !#[trigger] in_component@[hp] implies {
                            let tp = m@.half_edges[hp].twin;
                            let np = m@.half_edges[hp].next;
                            let pp = m@.half_edges[hp].prev;
                            &&& !in_component@[tp]
                            &&& !in_component@[np]
                            &&& !in_component@[pp]
                        } by {
                        if hp < h as int {
                        } else {
                            assert(hp == h as int);
                            assert(!in_component@[h as int]);
                            assert(!in_component@[t as int]);
                            assert(!in_component@[n as int]);
                            assert(!in_component@[p as int]);
                        }
                    };
                };
            }

            h += 1;
        }

        proof {
            assert(h == hcnt);
            assert(mesh_half_edge_component_representative_complete_at_spec(m@, components@, c as int)) by {
                assert(0 <= c as int);
                assert((c as int) < components@.len() as int);
                assert(components@[c as int]@.len() > 0);
                assert(mesh_half_edge_component_entry_spec(components@, c as int, 0) == rep as int);
                assert(0 <= 0 < clen as int);
                assert(component@[0] as int == rep as int);
                assert(in_component@[rep as int]);

                assert(forall|a: int, b: int|
                    #![trigger in_component@[a], mesh_half_edge_adjacent_spec(m@, a, b)]
                    0 <= a < hcnt as int
                        && 0 <= b < hcnt as int
                        && in_component@[a]
                        && mesh_half_edge_adjacent_spec(m@, a, b)
                        ==> in_component@[b]) by {
                    assert forall|a: int, b: int|
                        #![trigger in_component@[a], mesh_half_edge_adjacent_spec(m@, a, b)]
                        0 <= a < hcnt as int
                            && 0 <= b < hcnt as int
                            && in_component@[a]
                            && mesh_half_edge_adjacent_spec(m@, a, b)
                            implies in_component@[b] by {
                        if mesh_half_edge_direct_step_spec(m@, a, b) {
                            let ta = m@.half_edges[a].twin;
                            let na = m@.half_edges[a].next;
                            let pa = m@.half_edges[a].prev;
                            assert(0 <= a < h as int);
                            assert(0 <= ta < hcnt as int);
                            assert(0 <= na < hcnt as int);
                            assert(0 <= pa < hcnt as int);
                            assert(in_component@[ta]);
                            assert(in_component@[na]);
                            assert(in_component@[pa]);
                            assert(b == ta || b == na || b == pa);
                            if b == ta {
                                assert(in_component@[b]);
                            } else if b == na {
                                assert(in_component@[b]);
                            } else {
                                assert(in_component@[b]);
                            }
                        } else {
                            assert(mesh_half_edge_direct_step_spec(m@, b, a));
                            if !in_component@[b] {
                                let tb = m@.half_edges[b].twin;
                                let nb = m@.half_edges[b].next;
                                let pb = m@.half_edges[b].prev;
                                assert(0 <= b < h as int);
                                assert(0 <= tb < hcnt as int);
                                assert(0 <= nb < hcnt as int);
                                assert(0 <= pb < hcnt as int);
                                assert(!in_component@[tb]);
                                assert(!in_component@[nb]);
                                assert(!in_component@[pb]);
                                assert(a == tb || a == nb || a == pb);
                                if a == tb {
                                    assert(!in_component@[a]);
                                } else if a == nb {
                                    assert(!in_component@[a]);
                                } else {
                                    assert(!in_component@[a]);
                                }
                                assert(false);
                            }
                            assert(in_component@[b]);
                        }
                    };
                };

                assert forall|target: int|
                    #![trigger mesh_half_edge_connected_spec(m@, mesh_half_edge_component_entry_spec(components@, c as int, 0), target)]
                    0 <= target < hcnt as int
                        && mesh_half_edge_connected_spec(
                            m@,
                            mesh_half_edge_component_entry_spec(components@, c as int, 0),
                            target,
                        )
                        implies mesh_half_edge_component_contains_spec(m@, components@, c as int, target) by {
                    assert(mesh_half_edge_connected_spec(m@, rep as int, target));
                    lemma_mesh_half_edge_closed_set_contains_connected(m@, rep as int, target, in_component@);
                    assert(in_component@[target]);
                    assert(exists|ip: int| {
                        &&& 0 <= ip < clen as int
                        &&& #[trigger] component@[ip] as int == target
                    });
                    let ip = choose|ip: int| {
                        &&& 0 <= ip < clen as int
                        &&& #[trigger] component@[ip] as int == target
                    };
                    assert(0 <= ip < components@[c as int]@.len() as int);
                    assert(mesh_half_edge_component_entry_spec(components@, c as int, ip) == target);
                    assert(mesh_half_edge_component_contains_spec(m@, components@, c as int, target));
                };
            }
            assert(forall|cp: int|
                #![trigger components@[cp]@]
                0 <= cp < (c + 1) as int
                    ==> mesh_half_edge_component_representative_complete_at_spec(m@, components@, cp)) by {
                assert forall|cp: int|
                    #![trigger components@[cp]@]
                    0 <= cp < (c + 1) as int
                        implies mesh_half_edge_component_representative_complete_at_spec(m@, components@, cp) by {
                    if cp < c as int {
                    } else {
                        assert(cp == c as int);
                        assert(mesh_half_edge_component_representative_complete_at_spec(m@, components@, cp));
                    }
                };
            }
        }

        c += 1;
    }

    proof {
        assert(!(c < components.len()));
        lemma_usize_loop_exit_eq(c, components.len());
        assert(mesh_half_edge_components_representative_complete_spec(m@, components@)) by {
            assert forall|cp: int|
                #![trigger components@[cp]@]
                0 <= cp < components@.len() as int
                    implies mesh_half_edge_component_representative_complete_at_spec(m@, components@, cp) by {
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
    if !neighbor_closed_ok {
        return Option::None;
    }
    let representative_connected_ok = runtime_check_half_edge_components_representative_connected(
        m,
        &components,
    );
    if !representative_connected_ok {
        return Option::None;
    }
    let representative_minimal_ok = runtime_check_half_edge_components_representative_minimal(
        m,
        &components,
    );
    if !representative_minimal_ok {
        return Option::None;
    }
    let representative_complete_ok = runtime_check_half_edge_components_representative_complete(
        m,
        &components,
    );
    if !representative_complete_ok {
        Option::None
    } else {
        proof {
            assert(mesh_half_edge_components_partition_spec(m@, components@));
            assert(mesh_half_edge_components_neighbor_closed_spec(m@, components@));
            assert(mesh_half_edge_components_representative_connected_spec(m@, components@));
            assert(mesh_half_edge_components_representative_minimal_spec(m@, components@));
            assert(mesh_half_edge_components_representative_complete_spec(m@, components@));
            assert(mesh_half_edge_components_partition_neighbor_closed_spec(m@, components@));
        }
        Option::Some(components)
    }
}

#[allow(dead_code)]
pub fn component_count_constructive(
    m: &Mesh,
) -> (out: Option<usize>)
    ensures
        match out {
            Option::Some(count) => mesh_component_count_partition_witness_spec(m@, count as int)
                && count as int == mesh_component_count_spec(m@),
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
    let representative_connected_ok = runtime_check_half_edge_components_representative_connected(
        m,
        &components,
    );
    if !representative_connected_ok {
        return Option::None;
    }
    let representative_minimal_ok = runtime_check_half_edge_components_representative_minimal(
        m,
        &components,
    );
    if !representative_minimal_ok {
        return Option::None;
    }
    let representative_complete_ok = runtime_check_half_edge_components_representative_complete(
        m,
        &components,
    );
    if !representative_complete_ok {
        return Option::None;
    }

    let count = components.len();

    proof {
        assert(mesh_half_edge_components_partition_spec(m@, components@));
        assert(mesh_half_edge_components_neighbor_closed_spec(m@, components@));
        assert(mesh_half_edge_components_representative_connected_spec(m@, components@));
        assert(mesh_half_edge_components_representative_minimal_spec(m@, components@));
        assert(mesh_half_edge_components_representative_complete_spec(m@, components@));
        assert(mesh_half_edge_components_partition_neighbor_closed_spec(m@, components@));
        lemma_component_partition_count_matches_model_component_count(m@, components@);
        assert(components@.len() as int == mesh_component_count_spec(m@));
        assert(count as int == components@.len() as int);
        assert(count as int == mesh_component_count_spec(m@));
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
    let representative_connected_ok = runtime_check_half_edge_components_representative_connected(
        m,
        &components,
    );
    if !representative_connected_ok {
        return Option::None;
    }
    let representative_minimal_ok = runtime_check_half_edge_components_representative_minimal(
        m,
        &components,
    );
    if !representative_minimal_ok {
        return Option::None;
    }
    let representative_complete_ok = runtime_check_half_edge_components_representative_complete(
        m,
        &components,
    );
    if !representative_complete_ok {
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
        assert(mesh_half_edge_components_representative_connected_spec(m@, components@));
        assert(mesh_half_edge_components_representative_minimal_spec(m@, components@));
        assert(mesh_half_edge_components_representative_complete_spec(m@, components@));
        assert(mesh_half_edge_components_partition_neighbor_closed_spec(m@, components@));
        assert(mesh_euler_characteristics_per_component_spec(m@, components@, chis@));
        lemma_component_partition_count_matches_model_component_count(m@, components@);
        assert(components@.len() as int == mesh_component_count_spec(m@));
        assert(chis@.len() as int == components@.len() as int);
        assert(chis@.len() as int == mesh_component_count_spec(m@));
        assert(mesh_euler_characteristics_partition_witness_spec(m@, chis@));
    }

    Option::Some(chis)
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn check_euler_formula_closed_components_constructive(
    m: &Mesh,
) -> (out: Option<EulerFormulaClosedComponentsGateWitness>)
    ensures
        match out {
            Option::Some(w) => euler_formula_closed_components_gate_witness_spec(w)
                && euler_formula_closed_components_gate_model_link_spec(m@, w)
                && (w.api_ok ==> mesh_euler_closed_components_spec(m@)),
            Option::None => true,
        },
{
    let api_ok = ex_mesh_check_euler_formula_closed_components(m);

    let components = ex_mesh_half_edge_components(m);
    let partition_ok = runtime_check_half_edge_components_partition(m, &components);
    if !partition_ok {
        return Option::None;
    }

    let neighbor_closed_ok = runtime_check_half_edge_components_neighbor_closed(m, &components);
    if !neighbor_closed_ok {
        return Option::None;
    }
    let representative_connected_ok = runtime_check_half_edge_components_representative_connected(
        m,
        &components,
    );
    if !representative_connected_ok {
        return Option::None;
    }
    let representative_minimal_ok = runtime_check_half_edge_components_representative_minimal(
        m,
        &components,
    );
    if !representative_minimal_ok {
        return Option::None;
    }
    let representative_complete_ok = runtime_check_half_edge_components_representative_complete(
        m,
        &components,
    );
    if !representative_complete_ok {
        return Option::None;
    }

    let chis = ex_mesh_euler_characteristics_per_component(m);
    let chis_ok = runtime_check_euler_characteristics_per_component(m, &components, &chis);
    if !chis_ok {
        return Option::None;
    }
    let chis_non_empty = chis.len() > 0;
    let mut seen_non_two = false;

    let mut c: usize = 0;
    while c < chis.len()
        invariant
            c <= chis.len(),
            !seen_non_two ==> forall|cp: int|
                #![trigger chis@[cp]]
                0 <= cp < c as int ==> chis@[cp] as int == 2,
    {
        let seen_non_two_before = seen_non_two;
        let chi = *vstd::slice::slice_index_get(&chis, c);
        if chi != 2 {
            seen_non_two = true;
        }
        proof {
            assert(chi == chis@[c as int]);
            if !seen_non_two {
                assert(!seen_non_two_before);
                assert(chi as int == 2);
                assert(forall|cp: int|
                    #![trigger chis@[cp]]
                    0 <= cp < (c + 1) as int ==> chis@[cp] as int == 2) by {
                    assert forall|cp: int|
                        #![trigger chis@[cp]]
                        0 <= cp < (c + 1) as int implies chis@[cp] as int == 2 by {
                        if cp < c as int {
                        } else {
                            assert(cp == c as int);
                            assert(chis@[cp] as int == chi as int);
                            assert(chi as int == 2);
                        }
                    };
                }
            }
        }
        c += 1;
    }

    let chis_all_two = !seen_non_two;
    let formula_ok = chis_non_empty && chis_all_two;
    if api_ok != formula_ok {
        return Option::None;
    }

    let w = EulerFormulaClosedComponentsGateWitness {
        api_ok,
        chis_non_empty,
        chis_all_two,
    };

    proof {
        assert(!(c < chis.len()));
        lemma_usize_loop_exit_eq(c, chis.len());
        assert(w.api_ok == formula_ok);
        assert(euler_formula_closed_components_gate_witness_spec(w));
        if w.chis_all_two {
            assert(forall|cp: int|
                #![trigger chis@[cp]]
                0 <= cp < chis@.len() as int ==> chis@[cp] as int == 2) by {
                assert forall|cp: int|
                    #![trigger chis@[cp]]
                    0 <= cp < chis@.len() as int implies chis@[cp] as int == 2 by {
                    assert(chis@.len() as int == c as int);
                    assert(0 <= cp < c as int);
                };
            }
        }
        assert(mesh_half_edge_components_partition_spec(m@, components@));
        assert(mesh_half_edge_components_neighbor_closed_spec(m@, components@));
        assert(mesh_half_edge_components_representative_connected_spec(m@, components@));
        assert(mesh_half_edge_components_representative_minimal_spec(m@, components@));
        assert(mesh_half_edge_components_representative_complete_spec(m@, components@));
        assert(mesh_half_edge_components_partition_neighbor_closed_spec(m@, components@));
        assert(mesh_euler_characteristics_per_component_spec(m@, components@, chis@));
        lemma_component_partition_count_matches_model_component_count(m@, components@);
        assert(components@.len() as int == mesh_component_count_spec(m@));
        assert(chis@.len() as int == components@.len() as int);
        assert(chis@.len() as int == mesh_component_count_spec(m@));
        if w.api_ok {
            assert(w.chis_non_empty);
            assert(w.chis_all_two);
            assert(chis@.len() > 0);
            assert(forall|cp: int|
                #![trigger chis@[cp]]
                0 <= cp < chis@.len() as int ==> chis@[cp] as int == 2);
            assert(mesh_euler_formula_closed_components_partition_witness_spec(m@));
            assert(mesh_euler_closed_components_spec(m@));
        }
        assert(euler_formula_closed_components_gate_model_link_spec(m@, w));
        assert(w.api_ok ==> mesh_euler_closed_components_spec(m@)) by {
            if w.api_ok {
                assert(mesh_euler_closed_components_spec(m@));
            }
        };
    }

    Option::Some(w)
}

#[allow(dead_code)]
pub fn is_structurally_valid_constructive(
    m: &Mesh,
) -> (out: Option<StructuralValidityGateWitness>)
    ensures
        match out {
            Option::Some(w) => structural_validity_gate_witness_spec(w)
                && structural_validity_gate_model_link_spec(m@, w),
            Option::None => true,
        },
{
    let vertex_count_positive = m.vertices.len() > 0;
    let edge_count_positive = m.edges.len() > 0;
    let face_count_positive = m.faces.len() > 0;
    let half_edge_count_positive = m.half_edges.len() > 0;

    let index_bounds_ok = runtime_check_index_bounds(m);
    let twin_involution_ok = runtime_check_twin_assignment_total_involution(m);
    let prev_next_inverse_ok = runtime_check_prev_next_inverse(m);
    let face_cycles_ok = runtime_check_face_cycles_kernel_bridge(m);
    let no_degenerate_edges_ok = runtime_check_no_degenerate_edges(m);
    let vertex_manifold_ok = runtime_check_vertex_manifold_kernel_bridge(m);
    let edge_two_half_edges_ok = runtime_check_edge_exactly_two_half_edges(m);

    let formula_ok = vertex_count_positive
        && edge_count_positive
        && face_count_positive
        && half_edge_count_positive
        && index_bounds_ok
        && twin_involution_ok
        && prev_next_inverse_ok
        && face_cycles_ok
        && no_degenerate_edges_ok
        && vertex_manifold_ok
        && edge_two_half_edges_ok;

    let api_ok = formula_ok;

    let w = StructuralValidityGateWitness {
        api_ok,
        vertex_count_positive,
        edge_count_positive,
        face_count_positive,
        half_edge_count_positive,
        index_bounds_ok,
        twin_involution_ok,
        prev_next_inverse_ok,
        face_cycles_ok,
        no_degenerate_edges_ok,
        vertex_manifold_ok,
        edge_two_half_edges_ok,
    };

    proof {
        assert(api_ok == formula_ok);
        assert(structural_validity_gate_witness_spec(w));
        assert(w.vertex_count_positive ==> mesh_vertex_count_spec(m@) > 0) by {
            if w.vertex_count_positive {
                assert(w.vertex_count_positive == vertex_count_positive);
                assert(m.vertices.len() > 0);
                assert(m.vertices@.len() == m.vertices.len() as int);
                assert(mesh_vertex_count_spec(m@) == m@.vertex_half_edges.len() as int);
                assert(m@.vertex_half_edges.len() == m.vertices@.len());
                assert(mesh_vertex_count_spec(m@) == m.vertices.len() as int);
                assert(mesh_vertex_count_spec(m@) > 0);
            }
        };
        assert(w.edge_count_positive ==> mesh_edge_count_spec(m@) > 0) by {
            if w.edge_count_positive {
                assert(w.edge_count_positive == edge_count_positive);
                assert(m.edges.len() > 0);
                assert(m.edges@.len() == m.edges.len() as int);
                assert(mesh_edge_count_spec(m@) == m@.edge_half_edges.len() as int);
                assert(m@.edge_half_edges.len() == m.edges@.len());
                assert(mesh_edge_count_spec(m@) == m.edges.len() as int);
                assert(mesh_edge_count_spec(m@) > 0);
            }
        };
        assert(w.face_count_positive ==> mesh_face_count_spec(m@) > 0) by {
            if w.face_count_positive {
                assert(w.face_count_positive == face_count_positive);
                assert(m.faces.len() > 0);
                assert(m.faces@.len() == m.faces.len() as int);
                assert(mesh_face_count_spec(m@) == m@.face_half_edges.len() as int);
                assert(m@.face_half_edges.len() == m.faces@.len());
                assert(mesh_face_count_spec(m@) == m.faces.len() as int);
                assert(mesh_face_count_spec(m@) > 0);
            }
        };
        assert(w.half_edge_count_positive ==> mesh_half_edge_count_spec(m@) > 0) by {
            if w.half_edge_count_positive {
                assert(w.half_edge_count_positive == half_edge_count_positive);
                assert(m.half_edges.len() > 0);
                assert(m.half_edges@.len() == m.half_edges.len() as int);
                assert(mesh_half_edge_count_spec(m@) == m@.half_edges.len() as int);
                assert(m@.half_edges.len() == m.half_edges@.len());
                assert(mesh_half_edge_count_spec(m@) == m.half_edges.len() as int);
                assert(mesh_half_edge_count_spec(m@) > 0);
            }
        };
        if w.index_bounds_ok {
            assert(mesh_index_bounds_spec(m@));
        }
        if w.twin_involution_ok {
            assert(from_face_cycles_twin_assignment_total_involution_spec(m@));
        }
        if w.prev_next_inverse_ok {
            assert(mesh_prev_next_inverse_spec(m@));
        }
        if w.face_cycles_ok {
            assert(mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_total_spec(m@));
            lemma_face_bridge_total_implies_face_next_cycles(m@);
            assert(mesh_face_next_cycles_spec(m@));
        }
        if w.no_degenerate_edges_ok {
            assert(mesh_no_degenerate_edges_spec(m@));
        }
        if w.vertex_manifold_ok {
            assert(mesh_vertex_manifold_single_cycle_spec(m@));
        }
        if w.edge_two_half_edges_ok {
            assert(mesh_edge_exactly_two_half_edges_spec(m@));
        }
        assert(structural_validity_gate_model_link_spec(m@, w));
    }

    Option::Some(w)
}

#[allow(dead_code)]
pub fn is_valid_constructive(
    m: &Mesh,
) -> (out: Option<ValidityGateWitness>)
    ensures
        match out {
            Option::Some(w) => validity_gate_witness_spec(w)
                && validity_gate_model_link_spec(m@, w)
                && (w.api_ok ==> mesh_valid_spec(m@)),
            Option::None => true,
        },
{
    let structural_w = match is_structurally_valid_constructive(m) {
        Option::Some(w) => w,
        Option::None => return Option::None,
    };
    let euler_w = match check_euler_formula_closed_components_constructive(m) {
        Option::Some(w) => w,
        Option::None => return Option::None,
    };
    let euler_ok = euler_w.api_ok;
    let structural_ok = structural_w.api_ok;
    let api_ok = structural_ok && euler_ok;

    let w = ValidityGateWitness {
        api_ok,
        structural_ok,
        euler_ok,
    };

    proof {
        assert(structural_validity_gate_witness_spec(structural_w));
        assert(structural_validity_gate_model_link_spec(m@, structural_w));
        assert(euler_formula_closed_components_gate_witness_spec(euler_w));
        assert(euler_formula_closed_components_gate_model_link_spec(m@, euler_w));
        assert(exists|sw: StructuralValidityGateWitness| {
            &&& structural_validity_gate_witness_spec(sw)
            &&& structural_validity_gate_model_link_spec(m@, sw)
            &&& sw.api_ok == w.structural_ok
        }) by {
            let sw = structural_w;
            assert(structural_validity_gate_witness_spec(sw));
            assert(structural_validity_gate_model_link_spec(m@, sw));
            assert(sw.api_ok == w.structural_ok);
        };
        assert(exists|ew: EulerFormulaClosedComponentsGateWitness| {
            &&& euler_formula_closed_components_gate_witness_spec(ew)
            &&& euler_formula_closed_components_gate_model_link_spec(m@, ew)
            &&& ew.api_ok == w.euler_ok
        }) by {
            let ew = euler_w;
            assert(euler_formula_closed_components_gate_witness_spec(ew));
            assert(euler_formula_closed_components_gate_model_link_spec(m@, ew));
            assert(ew.api_ok == w.euler_ok);
        };
        assert(validity_gate_witness_spec(w));
        assert(validity_gate_model_link_spec(m@, w));
        if w.api_ok {
            lemma_validity_gate_witness_api_ok_implies_mesh_valid(m@, w);
            assert(mesh_valid_spec(m@));
        }
        assert(w.api_ok ==> mesh_valid_spec(m@)) by {
            if w.api_ok {
                assert(mesh_valid_spec(m@));
            }
        };
    }

    Option::Some(w)
}

#[allow(dead_code)]
pub fn tetrahedron_constructive_counts() -> (out: Option<Mesh>)
    ensures
        match out {
            Option::Some(m) => mesh_tetrahedron_counts_spec(m@),
            Option::None => true,
        },
{
    let m = ex_mesh_tetrahedron();
    let counts_ok = runtime_check_mesh_counts(&m, 4, 6, 4, 12);
    if !counts_ok {
        return Option::None;
    }

    proof {
        assert(mesh_counts_spec(m@, 4, 6, 4, 12));
        assert(mesh_tetrahedron_counts_spec(m@));
    }

    Option::Some(m)
}

#[allow(dead_code)]
pub fn tetrahedron_constructive_counts_and_is_valid() -> (out: Option<(Mesh, ValidityGateWitness)>)
    ensures
        match out {
            Option::Some((m, w)) => mesh_tetrahedron_counts_spec(m@) && validity_gate_witness_spec(w)
                && validity_gate_model_link_spec(m@, w) && w.api_ok && mesh_valid_spec(m@),
            Option::None => true,
        },
{
    let counted = tetrahedron_constructive_counts();
    match counted {
        Option::Some(m) => {
            let valid = is_valid_constructive(&m);
            match valid {
                Option::Some(w) => {
                    if !w.api_ok {
                        Option::None
                    } else {
                        proof {
                            assert(mesh_tetrahedron_counts_spec(m@));
                            assert(validity_gate_witness_spec(w));
                            assert(validity_gate_model_link_spec(m@, w));
                            lemma_validity_gate_witness_api_ok_implies_mesh_valid(m@, w);
                            assert(mesh_valid_spec(m@));
                        }
                        Option::Some((m, w))
                    }
                }
                Option::None => Option::None,
            }
        }
        Option::None => Option::None,
    }
}

#[allow(dead_code)]
pub fn cube_constructive_counts() -> (out: Option<Mesh>)
    ensures
        match out {
            Option::Some(m) => mesh_cube_counts_spec(m@),
            Option::None => true,
        },
{
    let m = ex_mesh_cube();
    let counts_ok = runtime_check_mesh_counts(&m, 8, 12, 6, 24);
    if !counts_ok {
        return Option::None;
    }

    proof {
        assert(mesh_counts_spec(m@, 8, 12, 6, 24));
        assert(mesh_cube_counts_spec(m@));
    }

    Option::Some(m)
}

#[allow(dead_code)]
pub fn cube_constructive_counts_and_is_valid() -> (out: Option<(Mesh, ValidityGateWitness)>)
    ensures
        match out {
            Option::Some((m, w)) => mesh_cube_counts_spec(m@) && validity_gate_witness_spec(w)
                && validity_gate_model_link_spec(m@, w) && w.api_ok && mesh_valid_spec(m@),
            Option::None => true,
        },
{
    let counted = cube_constructive_counts();
    match counted {
        Option::Some(m) => {
            let valid = is_valid_constructive(&m);
            match valid {
                Option::Some(w) => {
                    if !w.api_ok {
                        Option::None
                    } else {
                        proof {
                            assert(mesh_cube_counts_spec(m@));
                            assert(validity_gate_witness_spec(w));
                            assert(validity_gate_model_link_spec(m@, w));
                            lemma_validity_gate_witness_api_ok_implies_mesh_valid(m@, w);
                            assert(mesh_valid_spec(m@));
                        }
                        Option::Some((m, w))
                    }
                }
                Option::None => Option::None,
            }
        }
        Option::None => Option::None,
    }
}

#[allow(dead_code)]
pub fn triangular_prism_constructive_counts() -> (out: Option<Mesh>)
    ensures
        match out {
            Option::Some(m) => mesh_triangular_prism_counts_spec(m@),
            Option::None => true,
        },
{
    let m = ex_mesh_triangular_prism();
    let counts_ok = runtime_check_mesh_counts(&m, 6, 9, 5, 18);
    if !counts_ok {
        return Option::None;
    }

    proof {
        assert(mesh_counts_spec(m@, 6, 9, 5, 18));
        assert(mesh_triangular_prism_counts_spec(m@));
    }

    Option::Some(m)
}

#[allow(dead_code)]
pub fn triangular_prism_constructive_counts_and_is_valid() -> (out: Option<(Mesh, ValidityGateWitness)>)
    ensures
        match out {
            Option::Some((m, w)) => mesh_triangular_prism_counts_spec(m@)
                && validity_gate_witness_spec(w) && validity_gate_model_link_spec(m@, w)
                && w.api_ok && mesh_valid_spec(m@),
            Option::None => true,
        },
{
    let counted = triangular_prism_constructive_counts();
    match counted {
        Option::Some(m) => {
            let valid = is_valid_constructive(&m);
            match valid {
                Option::Some(w) => {
                    if !w.api_ok {
                        Option::None
                    } else {
                        proof {
                            assert(mesh_triangular_prism_counts_spec(m@));
                            assert(validity_gate_witness_spec(w));
                            assert(validity_gate_model_link_spec(m@, w));
                            lemma_validity_gate_witness_api_ok_implies_mesh_valid(m@, w);
                            assert(mesh_valid_spec(m@));
                        }
                        Option::Some((m, w))
                    }
                }
                Option::None => Option::None,
            }
        }
        Option::None => Option::None,
    }
}

} // verus!
