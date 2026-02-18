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
    &&& forall|h1: int, h2: int|
        mesh_half_edge_belongs_to_face_spec(m, f1, h1)
            && mesh_half_edge_belongs_to_face_spec(m, f2, h2) ==> {
            &&& #[trigger] m.half_edges[h1].vertex != #[trigger] m.half_edges[h2].vertex
            &&& #[trigger] m.half_edges[h1].edge != #[trigger] m.half_edges[h2].edge
        }
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
pub open spec fn mesh_runtime_face_coplanar_spec(m: &Mesh, f: int) -> bool {
    mesh_face_coplanar_spec(m@, mesh_runtime_vertex_positions_spec(m), f)
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_runtime_all_faces_coplanar_spec(m: &Mesh) -> bool {
    mesh_all_faces_coplanar_spec(m@, mesh_runtime_vertex_positions_spec(m))
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
