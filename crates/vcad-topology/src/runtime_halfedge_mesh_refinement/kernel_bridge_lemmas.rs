verus! {
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

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_runtime_geometry_bridge_holds(m: &Mesh)
    ensures
        mesh_runtime_geometry_bridge_spec(m),
{
    let vertex_positions = mesh_runtime_vertex_positions_spec(m);
    assert(mesh_geometry_input_spec(m@, vertex_positions)) by {
        assert(vertex_positions.len() == m.vertices@.len());
        assert(mesh_vertex_count_spec(m@) == m@.vertex_half_edges.len() as int);
        assert(m@.vertex_half_edges.len() == m.vertices@.len());
    };
    assert(forall|v: int|
        0 <= v < mesh_vertex_count_spec(m@)
            ==> #[trigger] vertex_positions[v] == #[trigger] m.vertices@[v].position@) by {
        assert forall|v: int|
            0 <= v < mesh_vertex_count_spec(m@)
                implies #[trigger] vertex_positions[v] == #[trigger] m.vertices@[v].position@ by {
            assert(mesh_vertex_count_spec(m@) == m.vertices@.len() as int);
        };
    };
    assert(mesh_runtime_geometry_bridge_spec(m));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_kernel_mesh_runtime_geometry_bridge_holds(
    km: &kernels::KernelMesh,
    m: &Mesh,
)
    requires
        kernel_mesh_matches_mesh_model_spec(km, m@),
    ensures
        kernel_mesh_runtime_geometry_bridge_spec(km, m),
{
    lemma_mesh_runtime_geometry_bridge_holds(m);
    assert(kernel_mesh_matches_mesh_model_spec(km, m@));
    assert(mesh_runtime_geometry_bridge_spec(m));
    assert(kernel_mesh_runtime_geometry_bridge_spec(km, m));
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_cycle_half_edge_or_default_matches_model(
    m: MeshModel,
    f: int,
    k: int,
    i: int,
)
    requires
        mesh_index_bounds_spec(m),
        0 <= f < mesh_face_count_spec(m),
        mesh_face_cycle_witness_spec(m, f, k),
        0 <= i < k,
    ensures
        mesh_face_cycle_half_edge_or_default_spec(m, f, i as nat)
            == mesh_next_iter_spec(m, m.face_half_edges[f], i as nat),
{
    assert(0 <= f < mesh_face_count_spec(m));
    let start = m.face_half_edges[f];
    assert(0 <= start < mesh_half_edge_count_spec(m));
    lemma_mesh_next_iter_in_bounds(m, start, i as nat);
    let h = mesh_next_iter_spec(m, start, i as nat);
    assert(0 <= h < mesh_half_edge_count_spec(m));
    assert(mesh_face_cycle_half_edge_or_default_spec(m, f, i as nat) == h);
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_face_cycle_vertex_index_or_default_matches_model(
    m: MeshModel,
    f: int,
    k: int,
    i: int,
)
    requires
        mesh_index_bounds_spec(m),
        0 <= f < mesh_face_count_spec(m),
        mesh_face_cycle_witness_spec(m, f, k),
        0 <= i < k,
    ensures
        mesh_face_cycle_vertex_index_or_default_spec(m, f, i as nat)
            == m.half_edges[mesh_next_iter_spec(m, m.face_half_edges[f], i as nat)].vertex,
{
    assert(0 <= f < mesh_face_count_spec(m));
    let start = m.face_half_edges[f];
    let h = mesh_next_iter_spec(m, start, i as nat);
    lemma_mesh_face_cycle_half_edge_or_default_matches_model(m, f, k, i);
    assert(0 <= m.half_edges[h].vertex < mesh_vertex_count_spec(m));
    assert(mesh_face_cycle_vertex_index_or_default_spec(m, f, i as nat) == m.half_edges[h].vertex);
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_runtime_face_cycle_vertex_position_matches_runtime_positions(
    m: &Mesh,
    f: int,
    k: int,
    i: int,
)
    requires
        mesh_index_bounds_spec(m@),
        0 <= f < mesh_face_count_spec(m@),
        mesh_face_cycle_witness_spec(m@, f, k),
        0 <= i < k,
    ensures {
        let h = mesh_next_iter_spec(m@, m@.face_half_edges[f], i as nat);
        let v = m@.half_edges[h].vertex;
        mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m@,
            mesh_runtime_vertex_positions_spec(m),
            f,
            i,
        ) == mesh_runtime_vertex_positions_spec(m)[v]
    },
{
    let h = mesh_next_iter_spec(m@, m@.face_half_edges[f], i as nat);
    let v = m@.half_edges[h].vertex;
    lemma_mesh_runtime_geometry_bridge_holds(m);
    lemma_mesh_face_cycle_vertex_index_or_default_matches_model(m@, f, k, i);
    assert(0 <= v < mesh_vertex_count_spec(m@));
    assert(mesh_runtime_vertex_positions_spec(m).len() == mesh_vertex_count_spec(m@));
    assert(mesh_face_cycle_vertex_position_or_default_at_int_spec(
        m@,
        mesh_runtime_vertex_positions_spec(m),
        f,
        i,
    ) == mesh_runtime_vertex_positions_spec(m)[v]);
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_mesh_runtime_face_ordered_vertex_positions_match_cycle(
    m: &Mesh,
    f: int,
    k: int,
)
    requires
        mesh_index_bounds_spec(m@),
        0 <= f < mesh_face_count_spec(m@),
        mesh_face_cycle_witness_spec(m@, f, k),
    ensures
        forall|i: int| 0 <= i < k ==> {
            let h = mesh_next_iter_spec(m@, m@.face_half_edges[f], i as nat);
            let v = m@.half_edges[h].vertex;
            #[trigger] mesh_runtime_face_ordered_vertex_positions_spec(m, f, k)[i]
                == mesh_runtime_vertex_positions_spec(m)[v]
        },
{
    assert(forall|i: int| 0 <= i < k ==> {
        let h = mesh_next_iter_spec(m@, m@.face_half_edges[f], i as nat);
        let v = m@.half_edges[h].vertex;
        #[trigger] mesh_runtime_face_ordered_vertex_positions_spec(m, f, k)[i]
            == mesh_runtime_vertex_positions_spec(m)[v]
    }) by {
        assert forall|i: int| 0 <= i < k implies {
            let h = mesh_next_iter_spec(m@, m@.face_half_edges[f], i as nat);
            let v = m@.half_edges[h].vertex;
            #[trigger] mesh_runtime_face_ordered_vertex_positions_spec(m, f, k)[i]
                == mesh_runtime_vertex_positions_spec(m)[v]
        } by {
            lemma_mesh_runtime_face_cycle_vertex_position_matches_runtime_positions(m, f, k, i);
            assert(mesh_runtime_face_ordered_vertex_positions_spec(m, f, k)[i]
                == mesh_face_cycle_vertex_position_or_default_spec(
                    m@,
                    mesh_runtime_vertex_positions_spec(m),
                    f,
                    i as nat,
                ));
            assert(mesh_face_cycle_vertex_position_or_default_at_int_spec(
                m@,
                mesh_runtime_vertex_positions_spec(m),
                f,
                i,
            ) == mesh_face_cycle_vertex_position_or_default_spec(
                m@,
                mesh_runtime_vertex_positions_spec(m),
                f,
                i as nat,
            ));
        };
    };
}
} // verus!
