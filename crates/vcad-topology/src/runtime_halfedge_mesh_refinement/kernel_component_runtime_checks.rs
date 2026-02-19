verus! {
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
    let out0 = runtime_build_mesh_from_face_cycles(vertex_positions, face_cycles);
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

#[cfg(verus_keep_ghost)]
#[allow(dead_code)]
pub fn runtime_mesh_to_kernel_mesh_geometry_bridge(m: &Mesh) -> (km: kernels::KernelMesh)
    ensures
        kernel_mesh_runtime_geometry_bridge_spec(&km, m),
{
    let km = runtime_mesh_to_kernel_mesh(m);
    proof {
        assert(kernel_mesh_matches_mesh_model_spec(&km, m@));
        lemma_kernel_mesh_runtime_geometry_bridge_holds(&km, m);
    }
    km
}

#[allow(dead_code)]
pub fn runtime_check_face_cycles_kernel_bridge(m: &Mesh) -> (out: bool)
    ensures
        out ==> mesh_face_next_cycles_spec(m@),
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
        lemma_face_bridge_total_implies_face_next_cycles(m@);
        assert(mesh_face_next_cycles_spec(m@));
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

#[allow(dead_code)]
pub fn runtime_check_shared_edge_local_orientation_kernel_bridge(m: &Mesh) -> (out: bool)
    ensures
        out ==> mesh_shared_edge_local_orientation_consistency_spec(m@),
{
    let km = runtime_mesh_to_kernel_mesh(m);
    let ok = kernels::kernel_check_shared_edge_local_orientation_consistency(&km);
    if !ok {
        return false;
    }
    proof {
        assert(kernels::kernel_shared_edge_local_orientation_consistency_total_spec(&km));
        lemma_kernel_shared_edge_local_orientation_total_implies_mesh_shared_edge_local_orientation(
            &km,
            m@,
        );
        assert(mesh_shared_edge_local_orientation_consistency_spec(m@));
    }
    true
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_compute_half_edge_components(m: &Mesh) -> (out: Option<Vec<Vec<usize>>>)
{
    let hcnt = m.half_edges.len();
    let mut components: Vec<Vec<usize>> = Vec::new();
    if hcnt == 0 {
        return Option::Some(components);
    }

    let mut visited = vec![false; hcnt];
    let mut start: usize = 0;
    while start < hcnt
        invariant
            hcnt == m.half_edges.len(),
            visited.len() == hcnt,
            start <= hcnt,
    {
        if visited[start] {
            start += 1;
            continue;
        }

        let mut frontier: Vec<usize> = Vec::new();
        let mut component: Vec<usize> = Vec::new();
        frontier.push(start);
        visited[start] = true;

        let mut frontier_idx: usize = 0;
        while frontier_idx < frontier.len()
            invariant
                hcnt == m.half_edges.len(),
                visited.len() == hcnt,
                frontier_idx <= frontier.len(),
        {
            let h = frontier[frontier_idx];
            frontier_idx += 1;
            if h >= hcnt {
                return Option::None;
            }

            component.push(h);
            let he = &m.half_edges[h];

            let twin = he.twin;
            if twin >= hcnt {
                return Option::None;
            }
            if !visited[twin] {
                visited[twin] = true;
                frontier.push(twin);
            }

            let next = he.next;
            if next >= hcnt {
                return Option::None;
            }
            if !visited[next] {
                visited[next] = true;
                frontier.push(next);
            }

            let prev = he.prev;
            if prev >= hcnt {
                return Option::None;
            }
            if !visited[prev] {
                visited[prev] = true;
                frontier.push(prev);
            }
        }

        components.push(component);
        start += 1;
    }

    Option::Some(components)
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
} // verus!
