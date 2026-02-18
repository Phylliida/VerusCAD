#![cfg(feature = "verus-proofs")]

use vstd::prelude::*;

verus! {

#[derive(Structural, Copy, Clone, PartialEq, Eq)]
pub struct KernelHalfEdge {
    pub twin: usize,
    pub next: usize,
    pub prev: usize,
    pub vertex: usize,
    pub edge: usize,
    pub face: usize,
}

pub struct KernelMesh {
    pub vertex_half_edges: Vec<usize>,
    pub edge_half_edges: Vec<usize>,
    pub face_half_edges: Vec<usize>,
    pub half_edges: Vec<KernelHalfEdge>,
}

pub open spec fn kernel_vertex_count_spec(m: &KernelMesh) -> int {
    m.vertex_half_edges@.len() as int
}

pub open spec fn kernel_edge_count_spec(m: &KernelMesh) -> int {
    m.edge_half_edges@.len() as int
}

pub open spec fn kernel_face_count_spec(m: &KernelMesh) -> int {
    m.face_half_edges@.len() as int
}

pub open spec fn kernel_half_edge_count_spec(m: &KernelMesh) -> int {
    m.half_edges@.len() as int
}

pub open spec fn kernel_index_bounds_spec(m: &KernelMesh) -> bool {
    &&& forall|v: int|
        0 <= v < kernel_vertex_count_spec(m)
            ==> (#[trigger] m.vertex_half_edges@[v] as int) < kernel_half_edge_count_spec(m)
    &&& forall|e: int|
        0 <= e < kernel_edge_count_spec(m)
            ==> (#[trigger] m.edge_half_edges@[e] as int) < kernel_half_edge_count_spec(m)
    &&& forall|f: int|
        0 <= f < kernel_face_count_spec(m)
            ==> (#[trigger] m.face_half_edges@[f] as int) < kernel_half_edge_count_spec(m)
    &&& forall|h: int| 0 <= h < kernel_half_edge_count_spec(m) ==> {
        let he = #[trigger] m.half_edges@[h];
        &&& (he.twin as int) < kernel_half_edge_count_spec(m)
        &&& (he.next as int) < kernel_half_edge_count_spec(m)
        &&& (he.prev as int) < kernel_half_edge_count_spec(m)
        &&& (he.vertex as int) < kernel_vertex_count_spec(m)
        &&& (he.edge as int) < kernel_edge_count_spec(m)
        &&& (he.face as int) < kernel_face_count_spec(m)
    }
}

pub open spec fn kernel_twin_involution_spec(m: &KernelMesh) -> bool {
    forall|h: int|
        0 <= h < kernel_half_edge_count_spec(m)
            ==> (#[trigger] m.half_edges@[m.half_edges@[h].twin as int].twin as int) == h
}

pub open spec fn kernel_twin_involution_total_spec(m: &KernelMesh) -> bool {
    kernel_index_bounds_spec(m) && kernel_twin_involution_spec(m)
}

pub open spec fn kernel_next_prev_inverse_only_spec(m: &KernelMesh) -> bool {
    forall|h: int| 0 <= h < kernel_half_edge_count_spec(m) ==> kernel_next_prev_inverse_at_spec(m, h)
}

pub open spec fn kernel_prev_next_inverse_only_spec(m: &KernelMesh) -> bool {
    forall|h: int| 0 <= h < kernel_half_edge_count_spec(m) ==> kernel_prev_next_inverse_at_spec(m, h)
}

pub open spec fn kernel_prev_next_inverse_spec(m: &KernelMesh) -> bool {
    kernel_next_prev_inverse_only_spec(m) && kernel_prev_next_inverse_only_spec(m)
}

pub open spec fn kernel_prev_next_inverse_total_spec(m: &KernelMesh) -> bool {
    kernel_index_bounds_spec(m) && kernel_prev_next_inverse_spec(m)
}

pub open spec fn kernel_no_degenerate_edges_spec(m: &KernelMesh) -> bool {
    forall|h: int| 0 <= h < kernel_half_edge_count_spec(m) ==> {
        &&& (#[trigger] m.half_edges@[h].vertex as int)
            != (m.half_edges@[m.half_edges@[h].twin as int].vertex as int)
        &&& (#[trigger] m.half_edges@[h].vertex as int)
            != (m.half_edges@[m.half_edges@[h].next as int].vertex as int)
    }
}

pub open spec fn kernel_no_degenerate_edges_total_spec(m: &KernelMesh) -> bool {
    kernel_index_bounds_spec(m) && kernel_no_degenerate_edges_spec(m)
}

pub open spec fn kernel_edge_exactly_two_half_edges_at_spec(m: &KernelMesh, e: int) -> bool {
    let hcnt = kernel_half_edge_count_spec(m);
    &&& 0 <= e < kernel_edge_count_spec(m)
    &&& exists|h0: int, h1: int| {
        &&& 0 <= h0 < hcnt
        &&& 0 <= h1 < hcnt
        &&& h0 != h1
        &&& (#[trigger] m.half_edges@[h0].edge as int) == e
        &&& (#[trigger] m.half_edges@[h1].edge as int) == e
        &&& (m.half_edges@[h0].twin as int) == h1
        &&& (m.half_edges@[h1].twin as int) == h0
        &&& ((m.edge_half_edges@[e] as int) == h0 || (m.edge_half_edges@[e] as int) == h1)
        &&& forall|h: int|
            0 <= h < hcnt && (#[trigger] m.half_edges@[h].edge as int) == e ==> (h == h0 || h == h1)
    }
}

pub open spec fn kernel_edge_exactly_two_half_edges_spec(m: &KernelMesh) -> bool {
    forall|e: int| 0 <= e < kernel_edge_count_spec(m) ==> kernel_edge_exactly_two_half_edges_at_spec(m, e)
}

pub open spec fn kernel_edge_exactly_two_half_edges_total_spec(m: &KernelMesh) -> bool {
    kernel_index_bounds_spec(m) && kernel_edge_exactly_two_half_edges_spec(m)
}

pub open spec fn kernel_next_or_self_spec(m: &KernelMesh, h: int) -> int {
    let hcnt = kernel_half_edge_count_spec(m);
    if 0 <= h < hcnt {
        let n = m.half_edges@[h].next as int;
        if 0 <= n < hcnt {
            n
        } else {
            h
        }
    } else {
        h
    }
}

pub open spec fn kernel_vertex_ring_succ_or_self_spec(m: &KernelMesh, h: int) -> int {
    let hcnt = kernel_half_edge_count_spec(m);
    if 0 <= h < hcnt {
        let t = m.half_edges@[h].twin as int;
        if 0 <= t < hcnt {
            let n = m.half_edges@[t].next as int;
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

pub open spec fn kernel_next_iter_spec(m: &KernelMesh, h: int, n: nat) -> int
    decreases n
{
    if n == 0 {
        h
    } else {
        kernel_next_or_self_spec(m, kernel_next_iter_spec(m, h, (n - 1) as nat))
    }
}

pub open spec fn kernel_vertex_ring_iter_spec(m: &KernelMesh, h: int, n: nat) -> int
    decreases n
{
    if n == 0 {
        h
    } else {
        kernel_vertex_ring_succ_or_self_spec(m, kernel_vertex_ring_iter_spec(m, h, (n - 1) as nat))
    }
}

pub proof fn lemma_kernel_next_iter_step(m: &KernelMesh, h: int, n: nat)
    ensures
        kernel_next_iter_spec(m, h, (n + 1) as nat)
            == kernel_next_or_self_spec(m, kernel_next_iter_spec(m, h, n)),
{
    assert(kernel_next_iter_spec(m, h, (n + 1) as nat)
        == kernel_next_or_self_spec(m, kernel_next_iter_spec(m, h, n)));
}

pub proof fn lemma_kernel_vertex_ring_iter_step(m: &KernelMesh, h: int, n: nat)
    ensures
        kernel_vertex_ring_iter_spec(m, h, (n + 1) as nat)
            == kernel_vertex_ring_succ_or_self_spec(m, kernel_vertex_ring_iter_spec(m, h, n)),
{
    assert(kernel_vertex_ring_iter_spec(m, h, (n + 1) as nat)
        == kernel_vertex_ring_succ_or_self_spec(m, kernel_vertex_ring_iter_spec(m, h, n)));
}

pub proof fn lemma_kernel_next_or_self_in_bounds(m: &KernelMesh, h: int)
    requires
        kernel_index_bounds_spec(m),
        0 <= h < kernel_half_edge_count_spec(m),
    ensures
        0 <= kernel_next_or_self_spec(m, h) < kernel_half_edge_count_spec(m),
{
    let hcnt = kernel_half_edge_count_spec(m);
    let n = m.half_edges@[h].next as int;
    assert(0 <= n < hcnt);
    assert(kernel_next_or_self_spec(m, h) == n);
}

pub proof fn lemma_kernel_vertex_ring_succ_or_self_in_bounds(m: &KernelMesh, h: int)
    requires
        kernel_index_bounds_spec(m),
        0 <= h < kernel_half_edge_count_spec(m),
    ensures
        0 <= kernel_vertex_ring_succ_or_self_spec(m, h) < kernel_half_edge_count_spec(m),
{
    let hcnt = kernel_half_edge_count_spec(m);
    let t = m.half_edges@[h].twin as int;
    assert(0 <= t < hcnt);
    let n = m.half_edges@[t].next as int;
    assert(0 <= n < hcnt);
    assert(kernel_vertex_ring_succ_or_self_spec(m, h) == n);
}

pub proof fn lemma_kernel_next_iter_in_bounds(m: &KernelMesh, h: int, n: nat)
    requires
        kernel_index_bounds_spec(m),
        0 <= h < kernel_half_edge_count_spec(m),
    ensures
        0 <= kernel_next_iter_spec(m, h, n) < kernel_half_edge_count_spec(m),
    decreases n
{
    if n == 0 {
    } else {
        lemma_kernel_next_iter_in_bounds(m, h, (n - 1) as nat);
        lemma_kernel_next_or_self_in_bounds(m, kernel_next_iter_spec(m, h, (n - 1) as nat));
        lemma_kernel_next_iter_step(m, h, (n - 1) as nat);
    }
}

pub proof fn lemma_kernel_vertex_ring_iter_in_bounds(m: &KernelMesh, h: int, n: nat)
    requires
        kernel_index_bounds_spec(m),
        0 <= h < kernel_half_edge_count_spec(m),
    ensures
        0 <= kernel_vertex_ring_iter_spec(m, h, n) < kernel_half_edge_count_spec(m),
    decreases n
{
    if n == 0 {
    } else {
        lemma_kernel_vertex_ring_iter_in_bounds(m, h, (n - 1) as nat);
        lemma_kernel_vertex_ring_succ_or_self_in_bounds(
            m,
            kernel_vertex_ring_iter_spec(m, h, (n - 1) as nat),
        );
        lemma_kernel_vertex_ring_iter_step(m, h, (n - 1) as nat);
    }
}

pub open spec fn kernel_face_representative_cycle_witness_spec(m: &KernelMesh, f: int, k: int) -> bool {
    let hcnt = kernel_half_edge_count_spec(m);
    let start = m.face_half_edges@[f] as int;
    &&& 3 <= k <= hcnt
    &&& kernel_next_iter_spec(m, start, k as nat) == start
    &&& forall|i: int|
        0 <= i < k ==> {
            let h = kernel_next_iter_spec(m, start, i as nat);
            &&& 0 <= h < hcnt
            &&& #[trigger] m.half_edges@[kernel_next_iter_spec(m, start, i as nat)].face as int == f
        }
}

pub open spec fn kernel_face_representative_cycles_spec(m: &KernelMesh) -> bool {
    forall|f: int|
        #![trigger m.face_half_edges@[f]]
        0 <= f < kernel_face_count_spec(m) ==> exists|k: int| kernel_face_representative_cycle_witness_spec(m, f, k)
}

pub open spec fn kernel_face_representative_cycles_total_spec(m: &KernelMesh) -> bool {
    kernel_index_bounds_spec(m) && kernel_face_representative_cycles_spec(m)
}

pub open spec fn kernel_face_has_incident_half_edge_spec(m: &KernelMesh) -> bool {
    forall|f: int|
        #![trigger m.face_half_edges@[f]]
        0 <= f < kernel_face_count_spec(m) ==> {
            &&& (m.face_half_edges@[f] as int) < kernel_half_edge_count_spec(m)
            &&& #[trigger] m.half_edges@[m.face_half_edges@[f] as int].face as int == f
        }
}

pub open spec fn kernel_face_has_incident_half_edge_total_spec(m: &KernelMesh) -> bool {
    kernel_index_bounds_spec(m) && kernel_face_has_incident_half_edge_spec(m)
}

pub open spec fn kernel_face_representative_closed_min_length_witness_spec(
    m: &KernelMesh,
    f: int,
    k: int,
) -> bool {
    let start = m.face_half_edges@[f] as int;
    &&& 3 <= k <= kernel_half_edge_count_spec(m)
    &&& kernel_next_iter_spec(m, start, k as nat) == start
}

pub open spec fn kernel_face_representative_closed_min_length_spec(m: &KernelMesh) -> bool {
    exists|face_cycle_lens: Seq<usize>| {
        &&& face_cycle_lens.len() == kernel_face_count_spec(m)
        &&& forall|f: int|
            #![trigger face_cycle_lens[f]]
            0 <= f < kernel_face_count_spec(m)
                ==> kernel_face_representative_closed_min_length_witness_spec(
                    m,
                    f,
                    face_cycle_lens[f] as int,
                )
    }
}

pub open spec fn kernel_face_representative_closed_min_length_total_spec(m: &KernelMesh) -> bool {
    kernel_face_has_incident_half_edge_total_spec(m)
        && kernel_face_representative_closed_min_length_spec(m)
}

pub open spec fn kernel_vertex_representative_cycle_witness_spec(m: &KernelMesh, v: int, k: int) -> bool {
    let hcnt = kernel_half_edge_count_spec(m);
    let start = m.vertex_half_edges@[v] as int;
    &&& 1 <= k <= hcnt
    &&& kernel_vertex_ring_iter_spec(m, start, k as nat) == start
    &&& forall|i: int|
        0 <= i < k ==> {
            let h = kernel_vertex_ring_iter_spec(m, start, i as nat);
            &&& 0 <= h < hcnt
            &&& #[trigger] m.half_edges@[kernel_vertex_ring_iter_spec(m, start, i as nat)].vertex as int == v
        }
}

pub open spec fn kernel_vertex_manifold_single_cycle_basic_spec(m: &KernelMesh) -> bool {
    forall|v: int|
        #![trigger m.vertex_half_edges@[v]]
        0 <= v < kernel_vertex_count_spec(m)
            ==> exists|k: int| kernel_vertex_representative_cycle_witness_spec(m, v, k)
}

pub open spec fn kernel_vertex_manifold_single_cycle_total_spec(m: &KernelMesh) -> bool {
    kernel_index_bounds_spec(m) && kernel_vertex_manifold_single_cycle_basic_spec(m)
}

pub open spec fn kernel_vertex_has_incident_half_edge_spec(m: &KernelMesh) -> bool {
    forall|v: int|
        #![trigger m.vertex_half_edges@[v]]
        0 <= v < kernel_vertex_count_spec(m) ==> {
            &&& (m.vertex_half_edges@[v] as int) < kernel_half_edge_count_spec(m)
            &&& #[trigger] m.half_edges@[m.vertex_half_edges@[v] as int].vertex as int == v
        }
}

pub open spec fn kernel_vertex_has_incident_half_edge_total_spec(m: &KernelMesh) -> bool {
    kernel_index_bounds_spec(m) && kernel_vertex_has_incident_half_edge_spec(m)
}

pub open spec fn kernel_next_prev_inverse_at_spec(m: &KernelMesh, h: int) -> bool {
    let hcnt = kernel_half_edge_count_spec(m);
    if 0 <= h < hcnt {
        (m.half_edges@[m.half_edges@[h].next as int].prev as int) == h
    } else {
        false
    }
}

pub open spec fn kernel_prev_next_inverse_at_spec(m: &KernelMesh, h: int) -> bool {
    let hcnt = kernel_half_edge_count_spec(m);
    if 0 <= h < hcnt {
        (m.half_edges@[m.half_edges@[h].prev as int].next as int) == h
    } else {
        false
    }
}

#[verifier::exec_allows_no_decreases_clause]
pub fn kernel_check_index_bounds(m: &KernelMesh) -> (out: bool)
    ensures
        out == kernel_index_bounds_spec(m),
{
    let mut ok = true;
    let mut i: usize = 0;
    while i < m.vertex_half_edges.len()
        invariant
            0 <= i <= m.vertex_half_edges.len(),
            ok == (forall|j: int|
                0 <= j < i as int
                    ==> (#[trigger] m.vertex_half_edges@[j] as int) < m.half_edges@.len() as int),
    {
        if m.vertex_half_edges[i] >= m.half_edges.len() {
            ok = false;
        }
        i += 1;
    }

    let mut i: usize = 0;
    while i < m.edge_half_edges.len()
        invariant
            0 <= i <= m.edge_half_edges.len(),
            ok == (
                (forall|j: int|
                    0 <= j < m.vertex_half_edges@.len() as int
                        ==> (#[trigger] m.vertex_half_edges@[j] as int) < m.half_edges@.len() as int)
                && (forall|j: int|
                    0 <= j < i as int
                        ==> (#[trigger] m.edge_half_edges@[j] as int) < m.half_edges@.len() as int)
            ),
    {
        if m.edge_half_edges[i] >= m.half_edges.len() {
            ok = false;
        }
        i += 1;
    }

    let mut i: usize = 0;
    while i < m.face_half_edges.len()
        invariant
            0 <= i <= m.face_half_edges.len(),
            ok == (
                (forall|j: int|
                    0 <= j < m.vertex_half_edges@.len() as int
                        ==> (#[trigger] m.vertex_half_edges@[j] as int) < m.half_edges@.len() as int)
                && (forall|j: int|
                    0 <= j < m.edge_half_edges@.len() as int
                        ==> (#[trigger] m.edge_half_edges@[j] as int) < m.half_edges@.len() as int)
                && (forall|j: int|
                    0 <= j < i as int
                        ==> (#[trigger] m.face_half_edges@[j] as int) < m.half_edges@.len() as int)
            ),
    {
        if m.face_half_edges[i] >= m.half_edges.len() {
            ok = false;
        }
        i += 1;
    }

    let mut i: usize = 0;
    while i < m.half_edges.len()
        invariant
            0 <= i <= m.half_edges.len(),
            ok == (
                (forall|j: int|
                    0 <= j < m.vertex_half_edges@.len() as int
                        ==> (#[trigger] m.vertex_half_edges@[j] as int) < m.half_edges@.len() as int)
                && (forall|j: int|
                    0 <= j < m.edge_half_edges@.len() as int
                        ==> (#[trigger] m.edge_half_edges@[j] as int) < m.half_edges@.len() as int)
                && (forall|j: int|
                    0 <= j < m.face_half_edges@.len() as int
                        ==> (#[trigger] m.face_half_edges@[j] as int) < m.half_edges@.len() as int)
                && (forall|j: int| 0 <= j < i as int ==> {
                    let he = #[trigger] m.half_edges@[j];
                    &&& (he.twin as int) < m.half_edges@.len() as int
                    &&& (he.next as int) < m.half_edges@.len() as int
                    &&& (he.prev as int) < m.half_edges@.len() as int
                    &&& (he.vertex as int) < m.vertex_half_edges@.len() as int
                    &&& (he.edge as int) < m.edge_half_edges@.len() as int
                    &&& (he.face as int) < m.face_half_edges@.len() as int
                })
            ),
    {
        let he = m.half_edges[i];
        if he.twin >= m.half_edges.len()
            || he.next >= m.half_edges.len()
            || he.prev >= m.half_edges.len()
            || he.vertex >= m.vertex_half_edges.len()
            || he.edge >= m.edge_half_edges.len()
            || he.face >= m.face_half_edges.len()
        {
            ok = false;
        }
        i += 1;
    }

    ok
}

#[verifier::exec_allows_no_decreases_clause]
pub fn kernel_check_twin_involution(m: &KernelMesh) -> (out: bool)
    ensures
        out == kernel_twin_involution_total_spec(m),
{
    let bounds_ok = kernel_check_index_bounds(m);
    if !bounds_ok {
        return false;
    }

    let mut ok = true;
    let mut i: usize = 0;
    while i < m.half_edges.len()
        invariant
            kernel_index_bounds_spec(m),
            0 <= i <= m.half_edges.len(),
            ok == (forall|j: int|
                0 <= j < i as int
                    ==> (#[trigger] m.half_edges@[m.half_edges@[j].twin as int].twin as int) == j),
    {
        let t = m.half_edges[i].twin;
        if t >= m.half_edges.len() {
            ok = false;
        } else if m.half_edges[t].twin != i {
            ok = false;
        }
        i += 1;
    }

    proof {
        assert(bounds_ok);
        assert(kernel_twin_involution_total_spec(m) == (kernel_index_bounds_spec(m) && kernel_twin_involution_spec(m)));
    }
    ok
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(unused_variables, unused_assignments)]
pub fn kernel_check_next_prev_inverse(m: &KernelMesh) -> (out: bool)
    ensures
        out == (kernel_index_bounds_spec(m) && kernel_next_prev_inverse_only_spec(m)),
{
    let bounds_ok = kernel_check_index_bounds(m);
    if !bounds_ok {
        return false;
    }

    let mut ok = true;
    let mut bad_idx: usize = 0;
    let mut i: usize = 0;
    while i < m.half_edges.len()
        invariant
            kernel_index_bounds_spec(m),
            0 <= i <= m.half_edges.len(),
            ok ==> (forall|j: int| 0 <= j < i as int ==> #[trigger] kernel_next_prev_inverse_at_spec(m, j)),
            !ok ==> {
                &&& bad_idx < i
                &&& !kernel_next_prev_inverse_at_spec(m, bad_idx as int)
            },
    {
        let he = m.half_edges[i];
        if m.half_edges[he.next].prev != i {
            if ok {
                bad_idx = i;
            }
            ok = false;
        }
        i += 1;
    }

    proof {
        assert(bounds_ok);
        if ok {
            assert(kernel_next_prev_inverse_only_spec(m));
        } else {
            assert(bad_idx < m.half_edges@.len());
            assert(!kernel_next_prev_inverse_at_spec(m, bad_idx as int));
            if kernel_next_prev_inverse_only_spec(m) {
                assert(kernel_next_prev_inverse_at_spec(m, bad_idx as int));
                assert(false);
            }
            assert(!kernel_next_prev_inverse_only_spec(m));
        }
    }
    ok
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(unused_variables, unused_assignments)]
pub fn kernel_check_prev_next_inverse(m: &KernelMesh) -> (out: bool)
    ensures
        out == (kernel_index_bounds_spec(m) && kernel_prev_next_inverse_only_spec(m)),
{
    let bounds_ok = kernel_check_index_bounds(m);
    if !bounds_ok {
        return false;
    }

    let mut ok = true;
    let mut bad_idx: usize = 0;
    let mut i: usize = 0;
    while i < m.half_edges.len()
        invariant
            kernel_index_bounds_spec(m),
            0 <= i <= m.half_edges.len(),
            ok ==> (forall|j: int| 0 <= j < i as int ==> #[trigger] kernel_prev_next_inverse_at_spec(m, j)),
            !ok ==> {
                &&& bad_idx < i
                &&& !kernel_prev_next_inverse_at_spec(m, bad_idx as int)
            },
    {
        let he = m.half_edges[i];
        if m.half_edges[he.prev].next != i {
            if ok {
                bad_idx = i;
            }
            ok = false;
        }
        i += 1;
    }

    proof {
        assert(bounds_ok);
        if ok {
            assert(kernel_prev_next_inverse_only_spec(m));
        } else {
            assert(bad_idx < m.half_edges@.len());
            assert(!kernel_prev_next_inverse_at_spec(m, bad_idx as int));
            if kernel_prev_next_inverse_only_spec(m) {
                assert(kernel_prev_next_inverse_at_spec(m, bad_idx as int));
                assert(false);
            }
            assert(!kernel_prev_next_inverse_only_spec(m));
        }
    }
    ok
}

#[verifier::exec_allows_no_decreases_clause]
pub fn kernel_check_prev_inverse_of_next(m: &KernelMesh) -> (out: bool)
    ensures
        out == kernel_prev_next_inverse_total_spec(m),
{
    let next_prev_ok = kernel_check_next_prev_inverse(m);
    let prev_next_ok = kernel_check_prev_next_inverse(m);
    let ok = next_prev_ok && prev_next_ok;
    proof {
        assert(kernel_prev_next_inverse_total_spec(m) == (kernel_index_bounds_spec(m) && kernel_prev_next_inverse_spec(m)));
        assert(kernel_prev_next_inverse_spec(m)
            == (kernel_next_prev_inverse_only_spec(m) && kernel_prev_next_inverse_only_spec(m)));
        assert(ok == (kernel_index_bounds_spec(m) && kernel_prev_next_inverse_spec(m)));
    }
    ok
}

#[verifier::exec_allows_no_decreases_clause]
pub fn kernel_check_no_degenerate_edges(m: &KernelMesh) -> (out: bool)
    ensures
        out == kernel_no_degenerate_edges_total_spec(m),
{
    let bounds_ok = kernel_check_index_bounds(m);
    if !bounds_ok {
        return false;
    }

    let mut ok = true;
    let mut i: usize = 0;
    while i < m.half_edges.len()
        invariant
            kernel_index_bounds_spec(m),
            0 <= i <= m.half_edges.len(),
            ok == (forall|j: int|
                0 <= j < i as int ==> {
                    &&& (#[trigger] m.half_edges@[j].vertex as int)
                        != (m.half_edges@[m.half_edges@[j].twin as int].vertex as int)
                    &&& (#[trigger] m.half_edges@[j].vertex as int)
                        != (m.half_edges@[m.half_edges@[j].next as int].vertex as int)
                }),
    {
        let he = m.half_edges[i];
        let t = he.twin;
        let n = he.next;
        if t >= m.half_edges.len() || n >= m.half_edges.len() {
            ok = false;
        } else if he.vertex == m.half_edges[t].vertex || he.vertex == m.half_edges[n].vertex {
            ok = false;
        }
        i += 1;
    }

    proof {
        assert(bounds_ok);
        assert(kernel_no_degenerate_edges_total_spec(m) == (kernel_index_bounds_spec(m) && kernel_no_degenerate_edges_spec(m)));
    }
    ok
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(unused_variables, unused_assignments)]
pub fn kernel_check_face_cycles(m: &KernelMesh) -> (out: bool)
    ensures
        out ==> kernel_face_representative_closed_min_length_total_spec(m),
{
    let bounds_ok = kernel_check_index_bounds(m);
    if !bounds_ok {
        return false;
    }

    let hcnt = m.half_edges.len();
    let fcnt = m.face_half_edges.len();
    let mut global_seen: Vec<bool> = vec![false; hcnt];
    let mut face_cycle_lens: Vec<usize> = Vec::new();
    let mut f: usize = 0;
    while f < fcnt
        invariant
            kernel_index_bounds_spec(m),
            hcnt == m.half_edges.len(),
            fcnt == m.face_half_edges.len(),
            global_seen@.len() == hcnt as int,
            face_cycle_lens@.len() == f as int,
            0 <= f <= fcnt,
            forall|fp: int|
                #![trigger m.face_half_edges@[fp]]
                0 <= fp < f as int
                    ==> (#[trigger] m.half_edges@[m.face_half_edges@[fp] as int].face as int) == fp,
            forall|fp: int|
                #![trigger face_cycle_lens@[fp]]
                0 <= fp < f as int
                    ==> kernel_face_representative_closed_min_length_witness_spec(
                        m,
                        fp,
                        face_cycle_lens@[fp] as int,
                    ),
    {
        let start = m.face_half_edges[f];
        if m.half_edges[start].face != f {
            return false;
        }
        let mut local_seen: Vec<bool> = vec![false; hcnt];
        let mut h = start;
        let mut steps: usize = 0;
        let mut closed = false;
        while steps < hcnt && !closed
            invariant
                kernel_index_bounds_spec(m),
                hcnt == m.half_edges.len(),
                0 <= steps <= hcnt,
                global_seen@.len() == hcnt as int,
                local_seen@.len() == hcnt as int,
                0 <= h < hcnt,
                h as int == kernel_next_iter_spec(m, start as int, steps as nat),
                closed ==> h == start,
        {
            let h_prev = h;
            let steps_prev = steps;

            if local_seen[h] {
                return false;
            }
            if global_seen[h] {
                return false;
            }
            local_seen[h] = true;
            global_seen[h] = true;
            let he = m.half_edges[h];
            if he.face != f {
                return false;
            }
            h = he.next;
            if steps == usize::MAX {
                return false;
            }
            steps += 1;

            proof {
                assert(steps == steps_prev + 1);
                assert(h_prev as int == kernel_next_iter_spec(m, start as int, steps_prev as nat));

                lemma_kernel_next_iter_step(m, start as int, steps_prev as nat);
                assert(0 <= h_prev as int);
                assert((h_prev as int) < (hcnt as int));
                assert((m.half_edges@[h_prev as int].next as int) < hcnt as int);
                assert(kernel_next_or_self_spec(m, h_prev as int) == m.half_edges@[h_prev as int].next as int);
                assert(h as int == kernel_next_iter_spec(m, start as int, steps as nat));
            }

            if h == start {
                closed = true;
            }
        }

        if !closed {
            return false;
        }
        if h != start {
            return false;
        }
        if steps < 3 {
            return false;
        }
        face_cycle_lens.push(steps);

        proof {
            assert(start as int == m.face_half_edges@[f as int] as int);
            assert((m.half_edges@[start as int].face as int) == f as int);
            assert(forall|fp: int|
                #![trigger m.face_half_edges@[fp]]
                0 <= fp < (f + 1) as int
                    ==> (#[trigger] m.half_edges@[m.face_half_edges@[fp] as int].face as int) == fp) by {
                assert forall|fp: int|
                    #![trigger m.face_half_edges@[fp]]
                    0 <= fp < (f + 1) as int
                        implies (#[trigger] m.half_edges@[m.face_half_edges@[fp] as int].face as int) == fp by {
                    if fp < f as int {
                        assert((#[trigger] m.half_edges@[m.face_half_edges@[fp] as int].face as int) == fp);
                    } else {
                        assert(fp == f as int);
                        assert((#[trigger] m.half_edges@[m.face_half_edges@[fp] as int].face as int) == f as int);
                    }
                };
            }
            assert(forall|fp: int|
                #![trigger face_cycle_lens@[fp]]
                0 <= fp < (f + 1) as int
                    ==> kernel_face_representative_closed_min_length_witness_spec(
                        m,
                        fp,
                        face_cycle_lens@[fp] as int,
                    )) by {
                assert forall|fp: int|
                    #![trigger face_cycle_lens@[fp]]
                    0 <= fp < (f + 1) as int
                        implies kernel_face_representative_closed_min_length_witness_spec(
                            m,
                            fp,
                            face_cycle_lens@[fp] as int,
                        ) by {
                    if fp < f as int {
                        assert(kernel_face_representative_closed_min_length_witness_spec(
                            m,
                            fp,
                            face_cycle_lens@[fp] as int,
                        ));
                    } else {
                        assert(fp == f as int);
                        assert((face_cycle_lens@[fp] as int) == steps as int);
                        assert(steps as int <= hcnt as int);
                        assert(3 <= steps as int);
                        assert(h as int == start as int);
                        assert(h as int == kernel_next_iter_spec(m, start as int, steps as nat));
                        assert(kernel_next_iter_spec(m, start as int, steps as nat) == start as int);
                        assert(start as int == m.face_half_edges@[f as int] as int);
                        assert(kernel_face_representative_closed_min_length_witness_spec(
                            m,
                            f as int,
                            steps as int,
                        ));
                        assert(kernel_face_representative_closed_min_length_witness_spec(
                            m,
                            fp,
                            face_cycle_lens@[fp] as int,
                        ));
                    }
                };
            }
        }

        f += 1;
    }

    let mut h: usize = 0;
    while h < hcnt
        invariant
            kernel_index_bounds_spec(m),
            hcnt == m.half_edges.len(),
            global_seen@.len() == hcnt as int,
            0 <= h <= hcnt,
            forall|j: int| 0 <= j < h as int ==> #[trigger] global_seen@[j],
    {
        if !global_seen[h] {
            return false;
        }
        h += 1;
    }

    proof {
        assert(bounds_ok);
        assert(f == fcnt);
        assert(kernel_face_has_incident_half_edge_spec(m)) by {
            assert forall|fp: int|
                #![trigger m.face_half_edges@[fp]]
                0 <= fp < kernel_face_count_spec(m) implies {
                    &&& (m.face_half_edges@[fp] as int) < kernel_half_edge_count_spec(m)
                    &&& #[trigger] m.half_edges@[m.face_half_edges@[fp] as int].face as int == fp
                } by {
                assert(kernel_face_count_spec(m) == fcnt as int);
                assert(kernel_half_edge_count_spec(m) == hcnt as int);
                assert(fp < (fcnt as int));
                assert(fp < f as int);
                assert((m.face_half_edges@[fp] as int) < kernel_half_edge_count_spec(m));
                assert((#[trigger] m.half_edges@[m.face_half_edges@[fp] as int].face as int) == fp);
            };
        }
        assert(kernel_face_representative_closed_min_length_spec(m)) by {
            let cycle_lens = face_cycle_lens@;
            assert(cycle_lens.len() == kernel_face_count_spec(m)) by {
                assert(cycle_lens.len() == f as int);
                assert(kernel_face_count_spec(m) == fcnt as int);
                assert(f == fcnt);
            }
            assert(forall|fp: int|
                #![trigger cycle_lens[fp]]
                0 <= fp < kernel_face_count_spec(m)
                    ==> kernel_face_representative_closed_min_length_witness_spec(
                        m,
                        fp,
                        cycle_lens[fp] as int,
                    )) by {
                assert forall|fp: int|
                    #![trigger cycle_lens[fp]]
                    0 <= fp < kernel_face_count_spec(m)
                        implies kernel_face_representative_closed_min_length_witness_spec(
                            m,
                            fp,
                            cycle_lens[fp] as int,
                        ) by {
                    assert(kernel_face_count_spec(m) == fcnt as int);
                    assert(fp < fcnt as int);
                    assert(fp < f as int);
                    assert(cycle_lens[fp] == face_cycle_lens@[fp]);
                    assert(kernel_face_representative_closed_min_length_witness_spec(
                        m,
                        fp,
                        face_cycle_lens@[fp] as int,
                    ));
                    assert(kernel_face_representative_closed_min_length_witness_spec(
                        m,
                        fp,
                        cycle_lens[fp] as int,
                    ));
                };
            }
            assert(exists|cycle_lens: Seq<usize>| {
                &&& cycle_lens.len() == kernel_face_count_spec(m)
                &&& forall|fp: int|
                    #![trigger cycle_lens[fp]]
                    0 <= fp < kernel_face_count_spec(m)
                        ==> kernel_face_representative_closed_min_length_witness_spec(
                            m,
                            fp,
                            cycle_lens[fp] as int,
                        )
            }) by {
                let cycle_lens = face_cycle_lens@;
                assert(cycle_lens.len() == kernel_face_count_spec(m));
                assert(forall|fp: int|
                    #![trigger cycle_lens[fp]]
                    0 <= fp < kernel_face_count_spec(m)
                        ==> kernel_face_representative_closed_min_length_witness_spec(
                            m,
                            fp,
                            cycle_lens[fp] as int,
                        ));
            };
        }
        assert(kernel_face_representative_closed_min_length_total_spec(m));
    }
    true
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(unused_variables, unused_assignments)]
pub fn kernel_check_vertex_manifold_single_cycle(m: &KernelMesh) -> (out: bool)
    ensures
        out ==> kernel_vertex_has_incident_half_edge_total_spec(m),
{
    let bounds_ok = kernel_check_index_bounds(m);
    if !bounds_ok {
        return false;
    }

    let hcnt = m.half_edges.len();
    let vcnt = m.vertex_half_edges.len();

    let mut v: usize = 0;
    while v < vcnt
        invariant
            kernel_index_bounds_spec(m),
            hcnt == m.half_edges.len(),
            vcnt == m.vertex_half_edges.len(),
            0 <= v <= vcnt,
            forall|vp: int|
                #![trigger m.vertex_half_edges@[vp]]
                0 <= vp < v as int
                    ==> (#[trigger] m.half_edges@[m.vertex_half_edges@[vp] as int].vertex as int) == vp,
    {
        let mut expected: usize = 0;
        let mut hh: usize = 0;
        while hh < hcnt
            invariant
                kernel_index_bounds_spec(m),
                hcnt == m.half_edges.len(),
                0 <= hh <= hcnt,
                0 <= expected <= hh,
        {
            if m.half_edges[hh].vertex == v {
                expected += 1;
            }
            hh += 1;
        }
        if expected == 0 {
            return false;
        }

        let start = m.vertex_half_edges[v];
        if m.half_edges[start].vertex != v {
            return false;
        }

        let mut local_seen: Vec<bool> = vec![false; hcnt];
        let mut h = start;
        let mut steps: usize = 0;
        while steps <= expected
            invariant
                kernel_index_bounds_spec(m),
                hcnt == m.half_edges.len(),
                0 <= steps <= expected + 1,
                local_seen@.len() == hcnt as int,
                0 <= h < hcnt,
                h as int == kernel_vertex_ring_iter_spec(m, start as int, steps as nat),
        {
            let h_prev = h;
            let steps_prev = steps;

            if local_seen[h] {
                return false;
            }
            local_seen[h] = true;
            if m.half_edges[h].vertex != v {
                return false;
            }
            h = m.half_edges[m.half_edges[h].twin].next;
            if steps == usize::MAX {
                return false;
            }
            steps += 1;

            proof {
                assert(steps == steps_prev + 1);
                assert(h_prev as int == kernel_vertex_ring_iter_spec(m, start as int, steps_prev as nat));

                assert(0 <= h_prev as int);
                assert((h_prev as int) < (hcnt as int));
                assert((m.half_edges@[h_prev as int].twin as int) < hcnt as int);
                assert((m.half_edges@[m.half_edges@[h_prev as int].twin as int].next as int) < hcnt as int);
                assert(kernel_vertex_ring_succ_or_self_spec(m, h_prev as int)
                    == m.half_edges@[m.half_edges@[h_prev as int].twin as int].next as int);
                lemma_kernel_vertex_ring_iter_step(m, start as int, steps_prev as nat);
                assert(h as int == kernel_vertex_ring_iter_spec(m, start as int, steps as nat));
            }

            if h == start {
                break;
            }
        }

        if h != start {
            return false;
        }
        if steps != expected {
            return false;
        }

        proof {
            assert(start as int == m.vertex_half_edges@[v as int] as int);
            assert((m.half_edges@[start as int].vertex as int) == v as int);
            assert(forall|vp: int|
                #![trigger m.vertex_half_edges@[vp]]
                0 <= vp < (v + 1) as int
                    ==> (#[trigger] m.half_edges@[m.vertex_half_edges@[vp] as int].vertex as int) == vp) by {
                assert forall|vp: int|
                    #![trigger m.vertex_half_edges@[vp]]
                    0 <= vp < (v + 1) as int
                        implies (#[trigger] m.half_edges@[m.vertex_half_edges@[vp] as int].vertex as int) == vp by {
                    if vp < v as int {
                        assert((#[trigger] m.half_edges@[m.vertex_half_edges@[vp] as int].vertex as int) == vp);
                    } else {
                        assert(vp == v as int);
                        assert((#[trigger] m.half_edges@[m.vertex_half_edges@[vp] as int].vertex as int) == v as int);
                    }
                };
            }
        }
        v += 1;
    }

    proof {
        assert(bounds_ok);
        assert(v == vcnt);
        assert(kernel_vertex_has_incident_half_edge_spec(m)) by {
            assert forall|vp: int|
                #![trigger m.vertex_half_edges@[vp]]
                0 <= vp < kernel_vertex_count_spec(m) implies {
                    &&& (m.vertex_half_edges@[vp] as int) < kernel_half_edge_count_spec(m)
                    &&& #[trigger] m.half_edges@[m.vertex_half_edges@[vp] as int].vertex as int == vp
                } by {
                assert(kernel_vertex_count_spec(m) == vcnt as int);
                assert(kernel_half_edge_count_spec(m) == hcnt as int);
                assert(vp < (vcnt as int));
                assert(vp < v as int);
                assert((m.vertex_half_edges@[vp] as int) < kernel_half_edge_count_spec(m));
                assert((#[trigger] m.half_edges@[m.vertex_half_edges@[vp] as int].vertex as int) == vp);
            };
        }
        assert(kernel_vertex_has_incident_half_edge_total_spec(m));
    }
    true
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(unused_variables, unused_assignments)]
pub fn kernel_check_edge_has_exactly_two_half_edges(m: &KernelMesh) -> (out: bool)
    ensures
        out == kernel_edge_exactly_two_half_edges_total_spec(m),
{
    let bounds_ok = kernel_check_index_bounds(m);
    if !bounds_ok {
        return false;
    }

    let ecnt = m.edge_half_edges.len();
    let hcnt = m.half_edges.len();

    let mut ok = true;
    let mut bad_e: usize = 0;
    let mut e: usize = 0;
    while e < ecnt
        invariant
            kernel_index_bounds_spec(m),
            ecnt == m.edge_half_edges.len(),
            hcnt == m.half_edges.len(),
            0 <= e <= ecnt,
            ok ==> forall|ep: int| 0 <= ep < e as int ==> kernel_edge_exactly_two_half_edges_at_spec(m, ep),
            !ok ==> {
                &&& bad_e < e
                &&& !kernel_edge_exactly_two_half_edges_at_spec(m, bad_e as int)
            },
    {
        let mut count: usize = 0;
        let mut h0: usize = 0;
        let mut h1: usize = 0;
        let mut h2: usize = 0;
        let mut too_many = false;
        let mut h: usize = 0;
        while h < hcnt
            invariant
                kernel_index_bounds_spec(m),
                hcnt == m.half_edges.len(),
                0 <= h <= hcnt,
                count <= 2,
                count == 0 ==> forall|j: int|
                    0 <= j < h as int ==> (#[trigger] m.half_edges@[j].edge as int) != e as int,
                count >= 1 ==> {
                    &&& 0 <= h0 < h
                    &&& (#[trigger] m.half_edges@[h0 as int].edge as int) == e as int
                },
                count >= 2 ==> {
                    &&& 0 <= h1 < h
                    &&& h0 != h1
                    &&& (#[trigger] m.half_edges@[h1 as int].edge as int) == e as int
                },
                too_many ==> {
                    &&& count == 2
                    &&& 0 <= h2 < h
                    &&& h2 != h0
                    &&& h2 != h1
                    &&& (#[trigger] m.half_edges@[h2 as int].edge as int) == e as int
                },
                !too_many && count == 1 ==> forall|j: int|
                    0 <= j < h as int && (#[trigger] m.half_edges@[j].edge as int) == e as int
                        ==> j == h0 as int,
                !too_many && count == 2 ==> forall|j: int|
                    0 <= j < h as int && (#[trigger] m.half_edges@[j].edge as int) == e as int
                        ==> (j == h0 as int || j == h1 as int),
        {
            assert(h < m.half_edges.len());
            if m.half_edges[h].edge == e {
                if count == 0 {
                    h0 = h;
                    count = 1;
                } else if count == 1 {
                    h1 = h;
                    count = 2;
                } else {
                    if !too_many {
                        h2 = h;
                    }
                    too_many = true;
                }
            }
            h += 1;
        }

        let count_two = !too_many && count == 2;
        let mut twins_ok = false;
        let mut rep_ok = false;
        let mut twin0: usize = 0;
        let mut twin1: usize = 0;
        let mut rep: usize = 0;
        if count_two {
            assert(0 <= h0 < hcnt);
            assert(0 <= h1 < hcnt);
            twin0 = m.half_edges[h0].twin;
            twin1 = m.half_edges[h1].twin;
            twins_ok = twin0 == h1 && twin1 == h0;
            assert(e < m.edge_half_edges.len());
            rep = m.edge_half_edges[e];
            rep_ok = rep == h0 || rep == h1;
        }
        let edge_ok = count_two && twins_ok && rep_ok;

        if ok && edge_ok {
            proof {
                assert(kernel_edge_exactly_two_half_edges_at_spec(m, e as int)) by {
                    let w0 = h0 as int;
                    let w1 = h1 as int;
                    assert(0 <= w0 < hcnt as int);
                    assert(0 <= w1 < hcnt as int);
                    assert(w0 != w1);
                    assert((m.half_edges@[w0].edge as int) == e as int);
                    assert((m.half_edges@[w1].edge as int) == e as int);
                    assert((m.half_edges@[w0].twin as int) == w1);
                    assert((m.half_edges@[w1].twin as int) == w0);
                    assert((m.edge_half_edges@[e as int] as int) == w0 || (m.edge_half_edges@[e as int] as int) == w1);
                    assert(!too_many && count == 2);
                    assert(forall|j: int|
                        0 <= j < hcnt as int && (#[trigger] m.half_edges@[j].edge as int) == e as int
                            ==> (j == w0 || j == w1));
                }
            }
        } else {
            if ok {
                bad_e = e;
                proof {
                    assert(h == hcnt);
                    assert(!edge_ok);
                    assert(!kernel_edge_exactly_two_half_edges_at_spec(m, e as int)) by {
                        if kernel_edge_exactly_two_half_edges_at_spec(m, e as int) {
                            let (w0, w1) = choose|w0: int, w1: int| {
                                &&& 0 <= w0 < hcnt as int
                                &&& 0 <= w1 < hcnt as int
                                &&& w0 != w1
                                &&& (#[trigger] m.half_edges@[w0].edge as int) == e as int
                                &&& (#[trigger] m.half_edges@[w1].edge as int) == e as int
                                &&& (m.half_edges@[w0].twin as int) == w1
                                &&& (m.half_edges@[w1].twin as int) == w0
                                &&& ((m.edge_half_edges@[e as int] as int) == w0 || (m.edge_half_edges@[e as int] as int) == w1)
                                &&& forall|hh: int|
                                    0 <= hh < hcnt as int && (#[trigger] m.half_edges@[hh].edge as int) == e as int
                                        ==> (hh == w0 || hh == w1)
                            };

                            if too_many {
                                let i0 = h0 as int;
                                let i1 = h1 as int;
                                let i2 = h2 as int;
                                assert(count == 2);
                                assert(0 <= i0 < hcnt as int);
                                assert(0 <= i1 < hcnt as int);
                                assert(0 <= i2 < hcnt as int);
                                assert(i0 != i1);
                                assert(i2 != i0);
                                assert(i2 != i1);
                                assert((m.half_edges@[i0].edge as int) == e as int);
                                assert((m.half_edges@[i1].edge as int) == e as int);
                                assert((m.half_edges@[i2].edge as int) == e as int);
                                assert(i0 == w0 || i0 == w1);
                                assert(i1 == w0 || i1 == w1);
                                assert(i2 == w0 || i2 == w1);
                                if i0 == w0 {
                                    assert(i1 == w1);
                                    assert(i2 == w0 || i2 == w1);
                                    assert(i2 == i0 || i2 == i1);
                                } else {
                                    assert(i0 == w1);
                                    assert(i1 == w0);
                                    assert(i2 == w0 || i2 == w1);
                                    assert(i2 == i0 || i2 == i1);
                                }
                                assert(false);
                            } else if count == 0 {
                                assert(0 <= w0 < h as int);
                                assert((m.half_edges@[w0].edge as int) != e as int);
                                assert(false);
                            } else if count == 1 {
                                let i0 = h0 as int;
                                assert(0 <= i0 < hcnt as int);
                                assert((m.half_edges@[i0].edge as int) == e as int);
                                assert(w0 == i0);
                                assert(w1 == i0);
                                assert(false);
                            } else {
                                assert(count == 2);
                                assert(count_two);
                                let i0 = h0 as int;
                                let i1 = h1 as int;
                                assert(0 <= i0 < hcnt as int);
                                assert(0 <= i1 < hcnt as int);
                                assert(i0 != i1);
                                assert((m.half_edges@[i0].edge as int) == e as int);
                                assert((m.half_edges@[i1].edge as int) == e as int);
                                assert(w0 == i0 || w0 == i1);
                                assert(w1 == i0 || w1 == i1);
                                assert(w0 != w1);
                                if w0 == i0 {
                                    assert(w1 == i1);
                                    assert((m.half_edges@[i0].twin as int) == i1);
                                    assert((m.half_edges@[i1].twin as int) == i0);
                                    assert((m.edge_half_edges@[e as int] as int) == i0 || (m.edge_half_edges@[e as int] as int) == i1);
                                } else {
                                    assert(w0 == i1);
                                    assert(w1 == i0);
                                    assert((m.half_edges@[i0].twin as int) == i1);
                                    assert((m.half_edges@[i1].twin as int) == i0);
                                    assert((m.edge_half_edges@[e as int] as int) == i0 || (m.edge_half_edges@[e as int] as int) == i1);
                                }
                                assert(twin0 == h1 && twin1 == h0);
                                assert(rep == h0 || rep == h1);
                                assert(twins_ok);
                                assert(rep_ok);
                                assert(edge_ok);
                                assert(false);
                            }
                        }
                    };
                }
            }
            ok = false;
        }

        e += 1;
    }

    proof {
        if ok {
            assert(forall|ep: int| 0 <= ep < ecnt as int ==> kernel_edge_exactly_two_half_edges_at_spec(m, ep));
            assert(kernel_edge_exactly_two_half_edges_spec(m));
            assert(kernel_edge_exactly_two_half_edges_total_spec(m));
        } else {
            assert(bad_e < ecnt);
            assert(!kernel_edge_exactly_two_half_edges_at_spec(m, bad_e as int));
            if kernel_edge_exactly_two_half_edges_spec(m) {
                assert(kernel_edge_exactly_two_half_edges_at_spec(m, bad_e as int));
                assert(false);
            }
            assert(!kernel_edge_exactly_two_half_edges_spec(m));
            assert(!kernel_edge_exactly_two_half_edges_total_spec(m));
        }
    }
    ok
}

} // verus!
