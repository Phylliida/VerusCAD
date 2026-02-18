verus! {
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

#[verifier::spinoff_prover]
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
    lemma_twin_assignment_total_involution_implies_mesh_twin_involution(m);
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
} // verus!
