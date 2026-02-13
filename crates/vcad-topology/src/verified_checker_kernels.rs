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

} // verus!
