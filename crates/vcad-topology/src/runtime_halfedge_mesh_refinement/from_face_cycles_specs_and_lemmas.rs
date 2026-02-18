verus! {
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

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_half_edge_from_position_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    h: int,
) -> vcad_math::point3::Point3 {
    vertex_positions[mesh_half_edge_from_vertex_spec(m, h)]
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_half_edge_to_position_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    h: int,
) -> vcad_math::point3::Point3 {
    vertex_positions[mesh_half_edge_to_vertex_spec(m, h)]
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_half_edge_segment_geometry_at_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    h: int,
) -> bool {
    &&& mesh_index_bounds_spec(m)
    &&& mesh_geometry_input_spec(m, vertex_positions)
    &&& 0 <= h < mesh_half_edge_count_spec(m)
    &&& 0 <= mesh_half_edge_from_vertex_spec(m, h) < vertex_positions.len()
    &&& 0 <= mesh_half_edge_to_vertex_spec(m, h) < vertex_positions.len()
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_all_half_edges_segment_geometry_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
) -> bool {
    forall|h: int|
        0 <= h < mesh_half_edge_count_spec(m)
            ==> #[trigger] mesh_half_edge_segment_geometry_at_spec(m, vertex_positions, h)
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_half_edge_segment_geometry_at_from_model_and_positions(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    h: int,
)
    requires
        mesh_index_bounds_spec(m),
        mesh_geometry_input_spec(m, vertex_positions),
        0 <= h < mesh_half_edge_count_spec(m),
    ensures
        mesh_half_edge_segment_geometry_at_spec(m, vertex_positions, h),
{
    let hcnt = mesh_half_edge_count_spec(m);
    let vcnt = mesh_vertex_count_spec(m);
    let n = m.half_edges[h].next;
    assert(0 <= m.half_edges[h].vertex < vcnt);
    assert(0 <= n < hcnt);
    assert(0 <= m.half_edges[n].vertex < vcnt);
    assert(vcnt == vertex_positions.len());
    assert(mesh_half_edge_from_vertex_spec(m, h) == m.half_edges[h].vertex);
    assert(mesh_half_edge_to_vertex_spec(m, h) == m.half_edges[n].vertex);
    assert(0 <= mesh_half_edge_from_vertex_spec(m, h) < vertex_positions.len());
    assert(0 <= mesh_half_edge_to_vertex_spec(m, h) < vertex_positions.len());
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_all_half_edges_segment_geometry_from_model_and_positions(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
)
    requires
        mesh_index_bounds_spec(m),
        mesh_geometry_input_spec(m, vertex_positions),
    ensures
        mesh_all_half_edges_segment_geometry_spec(m, vertex_positions),
{
    assert forall|h: int|
        0 <= h < mesh_half_edge_count_spec(m) implies #[trigger]
            mesh_half_edge_segment_geometry_at_spec(m, vertex_positions, h) by {
        lemma_mesh_half_edge_segment_geometry_at_from_model_and_positions(m, vertex_positions, h);
    };
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

pub open spec fn from_face_cycles_twin_assignment_total_involution_at_spec(
    m: MeshModel,
    h: int,
) -> bool {
    let hcnt = mesh_half_edge_count_spec(m);
    &&& 0 <= m.half_edges[h].twin < hcnt
    &&& m.half_edges[m.half_edges[h].twin].twin == h
}

pub open spec fn from_face_cycles_twin_assignment_total_involution_spec(m: MeshModel) -> bool {
    let hcnt = mesh_half_edge_count_spec(m);
    forall|h: int|
        #![trigger from_face_cycles_twin_assignment_total_involution_at_spec(m, h)]
        0 <= h < hcnt ==> from_face_cycles_twin_assignment_total_involution_at_spec(m, h)
}

#[verifier::spinoff_prover]
pub proof fn lemma_twin_assignment_total_involution_implies_mesh_twin_involution(m: MeshModel)
    ensures
        from_face_cycles_twin_assignment_total_involution_spec(m) ==> mesh_twin_involution_spec(m),
{
    if from_face_cycles_twin_assignment_total_involution_spec(m) {
        assert(mesh_twin_involution_spec(m)) by {
            assert forall|h: int|
                0 <= h < mesh_half_edge_count_spec(m)
                    implies #[trigger] m.half_edges[m.half_edges[h].twin].twin == h by {
                assert(from_face_cycles_twin_assignment_total_involution_at_spec(m, h));
                assert(m.half_edges[m.half_edges[h].twin].twin == h);
            };
        };
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

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_twin_half_edges_reverse_segment_at_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    h: int,
) -> bool {
    let hcnt = mesh_half_edge_count_spec(m);
    let t = m.half_edges[h].twin;
    &&& mesh_index_bounds_spec(m)
    &&& mesh_geometry_input_spec(m, vertex_positions)
    &&& 0 <= h < hcnt
    &&& 0 <= t < hcnt
    &&& mesh_half_edge_from_position_spec(m, vertex_positions, t)
        == mesh_half_edge_to_position_spec(m, vertex_positions, h)
    &&& mesh_half_edge_to_position_spec(m, vertex_positions, t)
        == mesh_half_edge_from_position_spec(m, vertex_positions, h)
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_all_twin_half_edges_reverse_segments_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
) -> bool {
    forall|h: int|
        0 <= h < mesh_half_edge_count_spec(m)
            ==> #[trigger] mesh_twin_half_edges_reverse_segment_at_spec(m, vertex_positions, h)
}

#[cfg(verus_keep_ghost)]
#[verifier::spinoff_prover]
pub proof fn lemma_mesh_twin_half_edges_reverse_segment_at_from_model_and_positions(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    h: int,
)
    requires
        mesh_index_bounds_spec(m),
        mesh_geometry_input_spec(m, vertex_positions),
        from_face_cycles_twin_endpoint_correspondence_spec(m),
        0 <= h < mesh_half_edge_count_spec(m),
    ensures
        mesh_twin_half_edges_reverse_segment_at_spec(m, vertex_positions, h),
{
    let hcnt = mesh_half_edge_count_spec(m);
    let vcnt = mesh_vertex_count_spec(m);
    assert(from_face_cycles_twin_endpoint_correspondence_at_spec(m, h));
    let t = m.half_edges[h].twin;
    assert(0 <= t < hcnt);
    assert(mesh_half_edge_from_vertex_spec(m, t) == mesh_half_edge_to_vertex_spec(m, h));
    assert(mesh_half_edge_to_vertex_spec(m, t) == mesh_half_edge_from_vertex_spec(m, h));

    let from_t = mesh_half_edge_from_vertex_spec(m, t);
    let to_h = mesh_half_edge_to_vertex_spec(m, h);
    let to_t = mesh_half_edge_to_vertex_spec(m, t);
    let from_h = mesh_half_edge_from_vertex_spec(m, h);
    let n_h = m.half_edges[h].next;
    let n_t = m.half_edges[t].next;
    assert(0 <= m.half_edges[h].vertex < vcnt);
    assert(0 <= m.half_edges[t].vertex < vcnt);
    assert(0 <= n_h < hcnt);
    assert(0 <= n_t < hcnt);
    assert(0 <= m.half_edges[n_h].vertex < vcnt);
    assert(0 <= m.half_edges[n_t].vertex < vcnt);
    assert(mesh_half_edge_from_vertex_spec(m, h) == m.half_edges[h].vertex);
    assert(mesh_half_edge_from_vertex_spec(m, t) == m.half_edges[t].vertex);
    assert(mesh_half_edge_to_vertex_spec(m, h) == m.half_edges[n_h].vertex);
    assert(mesh_half_edge_to_vertex_spec(m, t) == m.half_edges[n_t].vertex);
    assert(vcnt == vertex_positions.len());
    assert(from_t == to_h);
    assert(to_t == from_h);
    assert(0 <= from_t < vertex_positions.len());
    assert(0 <= to_h < vertex_positions.len());
    assert(0 <= to_t < vertex_positions.len());
    assert(0 <= from_h < vertex_positions.len());
    assert(vertex_positions[from_t] == vertex_positions[to_h]);
    assert(vertex_positions[to_t] == vertex_positions[from_h]);
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_all_twin_half_edges_reverse_segments_from_model_and_positions(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
)
    requires
        mesh_index_bounds_spec(m),
        mesh_geometry_input_spec(m, vertex_positions),
        from_face_cycles_twin_endpoint_correspondence_spec(m),
    ensures
        mesh_all_twin_half_edges_reverse_segments_spec(m, vertex_positions),
{
    assert forall|h: int|
        0 <= h < mesh_half_edge_count_spec(m) implies #[trigger]
            mesh_twin_half_edges_reverse_segment_at_spec(m, vertex_positions, h) by {
        lemma_mesh_twin_half_edges_reverse_segment_at_from_model_and_positions(m, vertex_positions, h);
    };
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_half_edge_direction_vector_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    h: int,
) -> vcad_math::vec3::Vec3 {
    mesh_half_edge_to_position_spec(m, vertex_positions, h).sub_spec(
        mesh_half_edge_from_position_spec(m, vertex_positions, h),
    )
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_twin_half_edges_opposite_direction_vectors_at_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    h: int,
) -> bool {
    let t = m.half_edges[h].twin;
    &&& mesh_twin_half_edges_reverse_segment_at_spec(m, vertex_positions, h)
    &&& mesh_half_edge_direction_vector_spec(m, vertex_positions, t)
        == mesh_half_edge_direction_vector_spec(m, vertex_positions, h).neg_spec()
}

#[cfg(verus_keep_ghost)]
pub open spec fn mesh_all_twin_half_edges_opposite_direction_vectors_spec(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
) -> bool {
    forall|h: int|
        0 <= h < mesh_half_edge_count_spec(m) ==> #[trigger]
            mesh_twin_half_edges_opposite_direction_vectors_at_spec(m, vertex_positions, h)
}

#[cfg(verus_keep_ghost)]
#[verifier::spinoff_prover]
pub proof fn lemma_mesh_twin_half_edges_opposite_direction_vectors_at_from_model_and_positions(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
    h: int,
)
    requires
        mesh_index_bounds_spec(m),
        mesh_geometry_input_spec(m, vertex_positions),
        from_face_cycles_twin_endpoint_correspondence_spec(m),
        0 <= h < mesh_half_edge_count_spec(m),
    ensures
        mesh_twin_half_edges_opposite_direction_vectors_at_spec(m, vertex_positions, h),
{
    lemma_mesh_twin_half_edges_reverse_segment_at_from_model_and_positions(m, vertex_positions, h);

    let t = m.half_edges[h].twin;
    let h_from = mesh_half_edge_from_position_spec(m, vertex_positions, h);
    let h_to = mesh_half_edge_to_position_spec(m, vertex_positions, h);
    let t_from = mesh_half_edge_from_position_spec(m, vertex_positions, t);
    let t_to = mesh_half_edge_to_position_spec(m, vertex_positions, t);

    assert(mesh_twin_half_edges_reverse_segment_at_spec(m, vertex_positions, h));
    assert(t_from == h_to);
    assert(t_to == h_from);
    assert(mesh_half_edge_direction_vector_spec(m, vertex_positions, t) == t_to.sub_spec(t_from));
    assert(mesh_half_edge_direction_vector_spec(m, vertex_positions, h) == h_to.sub_spec(h_from));
    assert(t_to.sub_spec(t_from) == h_from.sub_spec(h_to));
    vcad_math::point3::Point3::lemma_sub_antisymmetric(h_from, h_to);
    assert(h_from.sub_spec(h_to) == h_to.sub_spec(h_from).neg_spec());
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_all_twin_half_edges_opposite_direction_vectors_from_model_and_positions(
    m: MeshModel,
    vertex_positions: Seq<vcad_math::point3::Point3>,
)
    requires
        mesh_index_bounds_spec(m),
        mesh_geometry_input_spec(m, vertex_positions),
        from_face_cycles_twin_endpoint_correspondence_spec(m),
    ensures
        mesh_all_twin_half_edges_opposite_direction_vectors_spec(m, vertex_positions),
{
    assert forall|h: int|
        0 <= h < mesh_half_edge_count_spec(m) implies #[trigger]
            mesh_twin_half_edges_opposite_direction_vectors_at_spec(m, vertex_positions, h) by {
        lemma_mesh_twin_half_edges_opposite_direction_vectors_at_from_model_and_positions(
            m,
            vertex_positions,
            h,
        );
    };
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
} // verus!
