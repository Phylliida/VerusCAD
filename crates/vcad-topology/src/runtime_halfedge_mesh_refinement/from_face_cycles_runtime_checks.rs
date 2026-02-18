verus! {
#[verifier::exec_allows_no_decreases_clause]
pub(crate) fn runtime_build_mesh_from_face_cycles(
    vertex_positions: Vec<RuntimePoint3>,
    face_cycles: &[Vec<usize>],
) -> (out: Result<Mesh, MeshBuildError>)
{
    let vertex_count = vertex_positions.len();
    if vertex_count == 0 {
        return Result::Err(MeshBuildError::EmptyVertexSet);
    }
    if face_cycles.len() == 0 {
        return Result::Err(MeshBuildError::EmptyFaceSet);
    }

    let mut half_edges: Vec<HalfEdge> = Vec::new();
    let mut faces: Vec<Face> = Vec::with_capacity(face_cycles.len());

    let mut f: usize = 0;
    while f < face_cycles.len()
        invariant
            vertex_count == vertex_positions.len(),
            0 <= f <= face_cycles.len(),
            faces.len() == f,
    {
        let cycle = vstd::slice::slice_index_get(face_cycles, f);
        let n = cycle.len();
        if n < 3 {
            return Result::Err(MeshBuildError::FaceTooSmall { face: f, len: n });
        }

        let start = half_edges.len();
        faces.push(Face { half_edge: start });

        let mut i: usize = 0;
        while i < n
            invariant
                vertex_count == vertex_positions.len(),
                faces.len() == f + 1,
                n == cycle.len(),
                3 <= n,
                0 <= i <= n,
        {
            let v = cycle[i];
            if v >= vertex_count {
                return Result::Err(MeshBuildError::VertexOutOfBounds {
                    face: f,
                    vertex: v,
                    index: i,
                });
            }
            let i_plus_one = match i.checked_add(1) {
                Some(v) => v,
                None => return Result::Err(MeshBuildError::EmptyFaceSet),
            };
            let next_idx = if i_plus_one < n {
                i_plus_one
            } else if i_plus_one == n {
                0
            } else {
                return Result::Err(MeshBuildError::EmptyFaceSet);
            };
            let to = cycle[next_idx];
            if to >= vertex_count {
                return Result::Err(MeshBuildError::VertexOutOfBounds {
                    face: f,
                    vertex: to,
                    index: next_idx,
                });
            }
            if v == to {
                return Result::Err(MeshBuildError::DegenerateOrientedEdge {
                    face: f,
                    index: i,
                    vertex: v,
                });
            }

            let next = match start.checked_add(next_idx) {
                Some(v) => v,
                None => return Result::Err(MeshBuildError::EmptyFaceSet),
            };
            let prev_idx = if i == 0 { n - 1 } else { i - 1 };
            let prev = match start.checked_add(prev_idx) {
                Some(v) => v,
                None => return Result::Err(MeshBuildError::EmptyFaceSet),
            };
            half_edges.push(HalfEdge {
                twin: usize::MAX,
                next,
                prev,
                vertex: v,
                edge: usize::MAX,
                face: f,
            });
            i += 1;
        }

        f += 1;
    }

    let hcnt = half_edges.len();

    let mut h: usize = 0;
    while h < hcnt
        invariant
            vertex_count == vertex_positions.len(),
            half_edges.len() == hcnt,
            0 <= h <= hcnt,
    {
        let from = half_edges[h].vertex;
        let next = half_edges[h].next;
        if next >= hcnt {
            return Result::Err(MeshBuildError::EmptyFaceSet);
        }
        let to = half_edges[next].vertex;

        let mut twin_opt: Option<usize> = None;
        let mut t: usize = 0;
        while t < hcnt
            invariant
                vertex_count == vertex_positions.len(),
                half_edges.len() == hcnt,
                0 <= t <= hcnt,
        {
            let t_next = half_edges[t].next;
            if t_next >= hcnt {
                return Result::Err(MeshBuildError::EmptyFaceSet);
            }
            let t_from = half_edges[t].vertex;
            let t_to = half_edges[t_next].vertex;
            if t_from == to && t_to == from {
                twin_opt = Some(t);
                break;
            }
            t += 1;
        }

        match twin_opt {
            Some(twin) => {
                let next_h = half_edges[h].next;
                let prev_h = half_edges[h].prev;
                let vertex_h = half_edges[h].vertex;
                let edge_h = half_edges[h].edge;
                let face_h = half_edges[h].face;
                half_edges.set(h, HalfEdge {
                    twin,
                    next: next_h,
                    prev: prev_h,
                    vertex: vertex_h,
                    edge: edge_h,
                    face: face_h,
                });
            }
            None => {
                return Result::Err(MeshBuildError::MissingTwinForHalfEdge {
                    half_edge: h,
                    from,
                    to,
                });
            }
        }

        h += 1;
    }

    let mut edges: Vec<Edge> = Vec::new();
    let mut h2: usize = 0;
    while h2 < hcnt
        invariant
            vertex_count == vertex_positions.len(),
            half_edges.len() == hcnt,
            0 <= h2 <= hcnt,
    {
        if half_edges[h2].edge == usize::MAX {
            let twin = half_edges[h2].twin;
            if twin >= hcnt {
                let next = half_edges[h2].next;
                if next >= hcnt {
                    return Result::Err(MeshBuildError::EmptyFaceSet);
                }
                return Result::Err(MeshBuildError::MissingTwinForHalfEdge {
                    half_edge: h2,
                    from: half_edges[h2].vertex,
                    to: half_edges[next].vertex,
                });
            }
            let edge = edges.len();
            edges.push(Edge { half_edge: h2 });
            let twin_h2 = half_edges[h2].twin;
            let next_h2 = half_edges[h2].next;
            let prev_h2 = half_edges[h2].prev;
            let vertex_h2 = half_edges[h2].vertex;
            let face_h2 = half_edges[h2].face;
            half_edges.set(h2, HalfEdge {
                twin: twin_h2,
                next: next_h2,
                prev: prev_h2,
                vertex: vertex_h2,
                edge,
                face: face_h2,
            });

            let twin_twin = half_edges[twin].twin;
            let twin_next = half_edges[twin].next;
            let twin_prev = half_edges[twin].prev;
            let twin_vertex = half_edges[twin].vertex;
            let twin_face = half_edges[twin].face;
            half_edges.set(twin, HalfEdge {
                twin: twin_twin,
                next: twin_next,
                prev: twin_prev,
                vertex: twin_vertex,
                edge,
                face: twin_face,
            });
        }
        h2 += 1;
    }

    let mut first_outgoing: Vec<Option<usize>> = vec![None; vertex_count];
    let mut h3: usize = 0;
    while h3 < hcnt
        invariant
            vertex_count == vertex_positions.len(),
            half_edges.len() == hcnt,
            first_outgoing.len() == vertex_count,
            0 <= h3 <= hcnt,
    {
        let v = half_edges[h3].vertex;
        if v >= vertex_count {
            return Result::Err(MeshBuildError::VertexOutOfBounds {
                face: half_edges[h3].face,
                vertex: v,
                index: 0,
            });
        }
        if first_outgoing[v].is_none() {
            first_outgoing.set(v, Some(h3));
        }
        h3 += 1;
    }

    let mut positions = vertex_positions;
    let mut vertices_rev: Vec<Vertex> = Vec::with_capacity(vertex_count);
    let mut remaining: usize = vertex_count;
    while remaining > 0
        invariant
            first_outgoing.len() == vertex_count,
            positions.len() == remaining,
            0 <= remaining <= vertex_count,
            vertices_rev.len() + remaining == vertex_count,
    {
        let vertex_id = remaining - 1;
        let position = match positions.pop() {
            Some(p) => p,
            None => return Result::Err(MeshBuildError::EmptyVertexSet),
        };
        let half_edge = match first_outgoing[vertex_id] {
            Some(hidx) => hidx,
            None => return Result::Err(MeshBuildError::IsolatedVertex { vertex: vertex_id }),
        };
        vertices_rev.push(Vertex { position, half_edge });
        remaining -= 1;
    }

    let mut vertices: Vec<Vertex> = Vec::with_capacity(vertex_count);
    while vertices_rev.len() > 0
        invariant
            vertices.len() + vertices_rev.len() == vertex_count,
    {
        let vertex = match vertices_rev.pop() {
            Some(vtx) => vtx,
            None => return Result::Err(MeshBuildError::EmptyVertexSet),
        };
        vertices.push(vertex);
    }

    Result::Ok(Mesh {
        vertices,
        edges,
        faces,
        half_edges,
    })
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
        !out ==> !from_face_cycles_no_duplicate_oriented_edges_spec(
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
                        proof {
                            lemma_face_cycles_exec_to_model_oriented_edge_exec(
                                face_cycles,
                                g,
                                face_prev,
                                j,
                                next_j,
                            );
                            assert(input_face_from_vertex_spec(model_cycles, g as int, j as int) == from_prev as int);
                            assert(input_face_to_vertex_spec(model_cycles, g as int, j as int) == to_prev as int);
                            assert(input_face_from_vertex_spec(model_cycles, f as int, i as int) == from as int);
                            assert(input_face_to_vertex_spec(model_cycles, f as int, i as int) == to as int);
                            assert(from as int == from_prev as int);
                            assert(to as int == to_prev as int);
                            assert(input_face_from_vertex_spec(model_cycles, f as int, i as int)
                                == input_face_from_vertex_spec(model_cycles, g as int, j as int));
                            assert(input_face_to_vertex_spec(model_cycles, f as int, i as int)
                                == input_face_to_vertex_spec(model_cycles, g as int, j as int));
                            assert(!from_face_cycles_no_duplicate_oriented_edges_spec(model_cycles)) by {
                                if from_face_cycles_no_duplicate_oriented_edges_spec(model_cycles) {
                                    assert(input_face_local_index_valid_spec(model_cycles, f as int, i as int));
                                    assert(input_face_local_index_valid_spec(model_cycles, g as int, j as int));
                                    assert(f as int == g as int && i as int == j as int);
                                    assert((g as int) < (f as int));
                                    assert(false);
                                }
                            };
                        }
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
                    proof {
                        lemma_face_cycles_exec_to_model_oriented_edge_exec(face_cycles, f, face, j, next_j);
                        assert(input_face_from_vertex_spec(model_cycles, f as int, j as int) == from_prev as int);
                        assert(input_face_to_vertex_spec(model_cycles, f as int, j as int) == to_prev as int);
                        assert(input_face_from_vertex_spec(model_cycles, f as int, i as int) == from as int);
                        assert(input_face_to_vertex_spec(model_cycles, f as int, i as int) == to as int);
                        assert(from as int == from_prev as int);
                        assert(to as int == to_prev as int);
                        assert(input_face_from_vertex_spec(model_cycles, f as int, i as int)
                            == input_face_from_vertex_spec(model_cycles, f as int, j as int));
                        assert(input_face_to_vertex_spec(model_cycles, f as int, i as int)
                            == input_face_to_vertex_spec(model_cycles, f as int, j as int));
                        assert(!from_face_cycles_no_duplicate_oriented_edges_spec(model_cycles)) by {
                            if from_face_cycles_no_duplicate_oriented_edges_spec(model_cycles) {
                                assert(input_face_local_index_valid_spec(model_cycles, f as int, i as int));
                                assert(input_face_local_index_valid_spec(model_cycles, f as int, j as int));
                                assert(f as int == f as int && i as int == j as int);
                                assert(0 <= j);
                                assert(j < i);
                                assert(false);
                            }
                        };
                    }
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
        !out ==> !from_face_cycles_all_oriented_edges_have_twin_spec(
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
                    !found ==> forall|gp: int, jp: int|
                        #![trigger input_face_from_vertex_spec(model_cycles, gp, jp), input_face_to_vertex_spec(model_cycles, gp, jp)]
                        0 <= gp < g as int && input_face_local_index_valid_spec(model_cycles, gp, jp)
                            ==> !(input_face_from_vertex_spec(model_cycles, gp, jp) == to as int
                                && input_face_to_vertex_spec(model_cycles, gp, jp) == from as int),
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
                        !found ==> forall|jp: int|
                            #![trigger input_face_from_vertex_spec(model_cycles, g as int, jp), input_face_to_vertex_spec(model_cycles, g as int, jp)]
                            0 <= jp < j as int
                                ==> !(input_face_from_vertex_spec(model_cycles, g as int, jp) == to as int
                                    && input_face_to_vertex_spec(model_cycles, g as int, jp) == from as int),
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
                        proof {
                            lemma_face_cycles_exec_to_model_oriented_edge_exec(
                                face_cycles,
                                g,
                                face_other,
                                j,
                                next_j,
                            );
                            assert(input_face_from_vertex_spec(model_cycles, g as int, j as int) == from_other as int);
                            assert(input_face_to_vertex_spec(model_cycles, g as int, j as int) == to_other as int);
                            assert(!(input_face_from_vertex_spec(model_cycles, g as int, j as int) == to as int
                                && input_face_to_vertex_spec(model_cycles, g as int, j as int) == from as int));
                            assert(forall|jp: int|
                                #![trigger input_face_from_vertex_spec(model_cycles, g as int, jp), input_face_to_vertex_spec(model_cycles, g as int, jp)]
                                0 <= jp < (j + 1) as int
                                    ==> !(input_face_from_vertex_spec(model_cycles, g as int, jp) == to as int
                                        && input_face_to_vertex_spec(model_cycles, g as int, jp) == from as int)) by {
                                assert forall|jp: int|
                                    #![trigger input_face_from_vertex_spec(model_cycles, g as int, jp), input_face_to_vertex_spec(model_cycles, g as int, jp)]
                                    0 <= jp < (j + 1) as int
                                        implies !(input_face_from_vertex_spec(model_cycles, g as int, jp) == to as int
                                            && input_face_to_vertex_spec(model_cycles, g as int, jp) == from as int) by {
                                    if jp < j as int {
                                        assert(!found);
                                        assert(forall|jp0: int|
                                            #![trigger input_face_from_vertex_spec(model_cycles, g as int, jp0), input_face_to_vertex_spec(model_cycles, g as int, jp0)]
                                            0 <= jp0 < j as int
                                                ==> !(input_face_from_vertex_spec(model_cycles, g as int, jp0) == to as int
                                                    && input_face_to_vertex_spec(model_cycles, g as int, jp0) == from as int));
                                    } else {
                                        assert(jp == j as int);
                                        assert(input_face_from_vertex_spec(model_cycles, g as int, jp) == from_other as int);
                                        assert(input_face_to_vertex_spec(model_cycles, g as int, jp) == to_other as int);
                                    }
                                };
                            }
                        }
                        j += 1;
                    }
                }

                if !found {
                    proof {
                        assert(j == n_other);
                        assert(forall|gp: int, jp: int|
                            #![trigger input_face_from_vertex_spec(model_cycles, gp, jp), input_face_to_vertex_spec(model_cycles, gp, jp)]
                            0 <= gp < (g + 1) as int && input_face_local_index_valid_spec(model_cycles, gp, jp)
                                ==> !(input_face_from_vertex_spec(model_cycles, gp, jp) == to as int
                                    && input_face_to_vertex_spec(model_cycles, gp, jp) == from as int)) by {
                            assert forall|gp: int, jp: int|
                                #![trigger input_face_from_vertex_spec(model_cycles, gp, jp), input_face_to_vertex_spec(model_cycles, gp, jp)]
                                0 <= gp < (g + 1) as int && input_face_local_index_valid_spec(model_cycles, gp, jp)
                                    implies !(input_face_from_vertex_spec(model_cycles, gp, jp) == to as int
                                        && input_face_to_vertex_spec(model_cycles, gp, jp) == from as int) by {
                                if gp < g as int {
                                    assert(0 <= gp < g as int);
                                    assert(!found);
                                    assert(forall|gp0: int, jp0: int|
                                        #![trigger input_face_from_vertex_spec(model_cycles, gp0, jp0), input_face_to_vertex_spec(model_cycles, gp0, jp0)]
                                        0 <= gp0 < g as int && input_face_local_index_valid_spec(model_cycles, gp0, jp0)
                                            ==> !(input_face_from_vertex_spec(model_cycles, gp0, jp0) == to as int
                                                && input_face_to_vertex_spec(model_cycles, gp0, jp0) == from as int));
                                } else {
                                    assert(gp == g as int);
                                    assert(0 <= jp < model_cycles[g as int].len() as int);
                                    assert(model_cycles[g as int].len() == n_other as int);
                                    assert(0 <= jp < n_other as int);
                                    assert(0 <= jp < j as int);
                                    assert(!found);
                                    assert(forall|jp0: int|
                                        #![trigger input_face_from_vertex_spec(model_cycles, g as int, jp0), input_face_to_vertex_spec(model_cycles, g as int, jp0)]
                                        0 <= jp0 < j as int
                                            ==> !(input_face_from_vertex_spec(model_cycles, g as int, jp0) == to as int
                                                && input_face_to_vertex_spec(model_cycles, g as int, jp0) == from as int));
                                }
                            };
                        }
                    }
                    g += 1;
                }
            }

            let _ = (twin_f, twin_i);
            if !found {
                proof {
                    assert(g == face_cycles.len());
                    assert(!from_face_cycles_all_oriented_edges_have_twin_spec(model_cycles)) by {
                        if from_face_cycles_all_oriented_edges_have_twin_spec(model_cycles) {
                            assert(input_face_local_index_valid_spec(model_cycles, f as int, i as int));
                            assert(exists|gp: int, jp: int| {
                                &&& input_face_local_index_valid_spec(model_cycles, gp, jp)
                                &&& input_face_from_vertex_spec(model_cycles, gp, jp)
                                    == input_face_to_vertex_spec(model_cycles, f as int, i as int)
                                &&& input_face_to_vertex_spec(model_cycles, gp, jp)
                                    == input_face_from_vertex_spec(model_cycles, f as int, i as int)
                            });
                            let w = choose|w: (int, int)| {
                                &&& input_face_local_index_valid_spec(model_cycles, w.0, w.1)
                                &&& input_face_from_vertex_spec(model_cycles, w.0, w.1)
                                    == input_face_to_vertex_spec(model_cycles, f as int, i as int)
                                &&& input_face_to_vertex_spec(model_cycles, w.0, w.1)
                                    == input_face_from_vertex_spec(model_cycles, f as int, i as int)
                            };
                            let gp = w.0;
                            let jp = w.1;
                            assert(0 <= gp < model_cycles.len());
                            assert(model_cycles.len() == face_cycles.len() as int);
                            assert(g == face_cycles.len());
                            assert(0 <= gp < g as int);
                            assert(input_face_from_vertex_spec(model_cycles, f as int, i as int) == from as int);
                            assert(input_face_to_vertex_spec(model_cycles, f as int, i as int) == to as int);
                            assert(input_face_from_vertex_spec(model_cycles, gp, jp) == to as int);
                            assert(input_face_to_vertex_spec(model_cycles, gp, jp) == from as int);
                            assert(!found);
                            assert(forall|gp0: int, jp0: int|
                                #![trigger input_face_from_vertex_spec(model_cycles, gp0, jp0), input_face_to_vertex_spec(model_cycles, gp0, jp0)]
                                0 <= gp0 < g as int && input_face_local_index_valid_spec(model_cycles, gp0, jp0)
                                    ==> !(input_face_from_vertex_spec(model_cycles, gp0, jp0) == to as int
                                        && input_face_to_vertex_spec(model_cycles, gp0, jp0) == from as int));
                            assert(!(input_face_from_vertex_spec(model_cycles, gp, jp) == to as int
                                && input_face_to_vertex_spec(model_cycles, gp, jp) == from as int));
                            assert(false);
                        }
                    };
                }
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
        !out ==> (
            !from_face_cycles_basic_input_spec(
                vertex_count as int,
                face_cycles_exec_to_model_spec(face_cycles@),
            ) || !from_face_cycles_no_isolated_vertices_spec(
                vertex_count as int,
                face_cycles_exec_to_model_spec(face_cycles@),
            )
        ),
{
    let ghost model_cycles = face_cycles_exec_to_model_spec(face_cycles@);
    if vertex_count == 0 {
        proof {
            assert(!from_face_cycles_basic_input_spec(vertex_count as int, model_cycles)) by {
                if from_face_cycles_basic_input_spec(vertex_count as int, model_cycles) {
                    assert(vertex_count as int > 0);
                    assert(false);
                }
            };
        }
        return false;
    }

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
            forall|fp: int, ip: int|
                #![trigger input_face_local_index_before_spec(model_cycles, fp, ip, f as int, 0)]
                input_face_local_index_before_spec(model_cycles, fp, ip, f as int, 0)
                    && 0 <= #[trigger] input_face_from_vertex_spec(model_cycles, fp, ip) < vertex_count as int
                    ==> seen@[input_face_from_vertex_spec(model_cycles, fp, ip)],
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
                forall|fp: int, ip: int|
                    #![trigger input_face_local_index_before_spec(model_cycles, fp, ip, f as int, i as int)]
                    input_face_local_index_before_spec(model_cycles, fp, ip, f as int, i as int)
                        && 0 <= #[trigger] input_face_from_vertex_spec(model_cycles, fp, ip) < vertex_count as int
                        ==> seen@[input_face_from_vertex_spec(model_cycles, fp, ip)],
        {
            let v = face[i];
            if v >= vertex_count {
                proof {
                    lemma_face_cycles_exec_to_model_face_entry_exec(face_cycles, f, face, i);
                    assert(model_cycles[f as int][i as int] == v as int);
                    assert(input_face_local_index_valid_spec(model_cycles, f as int, i as int));
                    assert(!from_face_cycles_basic_input_spec(vertex_count as int, model_cycles)) by {
                        if from_face_cycles_basic_input_spec(vertex_count as int, model_cycles) {
                            assert(0 <= model_cycles[f as int][i as int] < vertex_count as int);
                            assert(model_cycles[f as int][i as int] == v as int);
                            assert(v < vertex_count);
                            assert(false);
                        }
                    };
                }
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
                assert(forall|fp: int, ip: int|
                    #![trigger input_face_local_index_before_spec(model_cycles, fp, ip, f as int, (i + 1) as int)]
                    input_face_local_index_before_spec(model_cycles, fp, ip, f as int, (i + 1) as int)
                        && 0 <= input_face_from_vertex_spec(model_cycles, fp, ip) < vertex_count as int
                        ==> seen@[input_face_from_vertex_spec(model_cycles, fp, ip)]) by {
                    assert forall|fp: int, ip: int|
                        #![trigger input_face_local_index_before_spec(model_cycles, fp, ip, f as int, (i + 1) as int)]
                        input_face_local_index_before_spec(model_cycles, fp, ip, f as int, (i + 1) as int)
                            && 0 <= input_face_from_vertex_spec(model_cycles, fp, ip) < vertex_count as int
                            implies seen@[input_face_from_vertex_spec(model_cycles, fp, ip)] by {
                        if fp < f as int || (fp == f as int && ip < i as int) {
                            assert(input_face_local_index_before_spec(model_cycles, fp, ip, f as int, i as int));
                            if input_face_from_vertex_spec(model_cycles, fp, ip) == v as int {
                                assert(seen@[v as int]);
                            } else {
                                assert(seen_before[input_face_from_vertex_spec(model_cycles, fp, ip)]);
                                assert(seen@[input_face_from_vertex_spec(model_cycles, fp, ip)]);
                            }
                        } else {
                            assert(fp == f as int && ip == i as int);
                            assert(input_face_from_vertex_spec(model_cycles, fp, ip) == v as int);
                            assert(seen@[v as int]);
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
            assert(forall|fp: int, ip: int|
                #![trigger input_face_local_index_before_spec(model_cycles, fp, ip, (f + 1) as int, 0)]
                input_face_local_index_before_spec(model_cycles, fp, ip, (f + 1) as int, 0)
                    && 0 <= input_face_from_vertex_spec(model_cycles, fp, ip) < vertex_count as int
                    ==> seen@[input_face_from_vertex_spec(model_cycles, fp, ip)]) by {
                assert forall|fp: int, ip: int|
                    #![trigger input_face_local_index_before_spec(model_cycles, fp, ip, (f + 1) as int, 0)]
                    input_face_local_index_before_spec(model_cycles, fp, ip, (f + 1) as int, 0)
                        && 0 <= input_face_from_vertex_spec(model_cycles, fp, ip) < vertex_count as int
                        implies seen@[input_face_from_vertex_spec(model_cycles, fp, ip)] by {
                    assert(0 <= fp < (f + 1) as int);
                    if fp < f as int {
                        assert(input_face_local_index_before_spec(model_cycles, fp, ip, f as int, i as int));
                    } else {
                        assert(fp == f as int);
                        assert(0 <= ip < model_cycles[f as int].len() as int);
                        assert(model_cycles[f as int].len() == n as int);
                        assert(0 <= ip < n as int);
                        assert(0 <= ip < i as int);
                        assert(input_face_local_index_before_spec(model_cycles, fp, ip, f as int, i as int));
                    }
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
            forall|fp: int, ip: int|
                #![trigger input_face_local_index_before_spec(
                    model_cycles,
                    fp,
                    ip,
                    face_cycles.len() as int,
                    0,
                )]
                input_face_local_index_before_spec(
                    model_cycles,
                    fp,
                    ip,
                    face_cycles.len() as int,
                    0,
                ) && 0 <= #[trigger] input_face_from_vertex_spec(model_cycles, fp, ip) < vertex_count as int
                    ==> seen@[input_face_from_vertex_spec(model_cycles, fp, ip)],
    {
        if !seen[v] {
            proof {
                assert(0 <= v as int);
                assert((v as int) < (vertex_count as int));
                assert(!from_face_cycles_no_isolated_vertices_spec(vertex_count as int, model_cycles)) by {
                    if from_face_cycles_no_isolated_vertices_spec(vertex_count as int, model_cycles) {
                        assert(from_face_cycles_vertex_has_incident_spec(model_cycles, v as int));
                        let w = choose|w: (int, int)| {
                            &&& input_face_local_index_valid_spec(model_cycles, w.0, w.1)
                            &&& #[trigger] input_face_from_vertex_spec(model_cycles, w.0, w.1) == v as int
                        };
                        let fp = w.0;
                        let ip = w.1;
                        assert(input_face_local_index_before_spec(
                            model_cycles,
                            fp,
                            ip,
                            face_cycles.len() as int,
                            0,
                        ));
                        assert(0 <= input_face_from_vertex_spec(model_cycles, fp, ip) < vertex_count as int);
                        assert(seen@[input_face_from_vertex_spec(model_cycles, fp, ip)]);
                        assert(input_face_from_vertex_spec(model_cycles, fp, ip) == v as int);
                        assert(seen@[v as int]);
                        assert(!seen@[v as int]);
                        assert(false);
                    }
                };
            }
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
        proof {
            assert(!from_face_cycles_no_duplicate_oriented_edges_spec(model_cycles));
            assert(from_face_cycles_failure_spec(vertex_count as int, model_cycles));
        }
        return Result::Err(mesh_build_error_empty_face_set());
    }
    let all_twin_ok = runtime_check_from_face_cycles_all_oriented_edges_have_twin(face_cycles);
    if !all_twin_ok {
        proof {
            assert(!from_face_cycles_all_oriented_edges_have_twin_spec(model_cycles));
            assert(from_face_cycles_failure_spec(vertex_count as int, model_cycles));
        }
        return Result::Err(mesh_build_error_empty_face_set());
    }
    let no_isolated_ok = runtime_check_from_face_cycles_no_isolated_vertices(vertex_count, face_cycles);
    if !no_isolated_ok {
        proof {
            assert(input_ok);
            assert(from_face_cycles_basic_input_spec(vertex_count as int, model_cycles));
            assert(
                !from_face_cycles_basic_input_spec(vertex_count as int, model_cycles)
                    || !from_face_cycles_no_isolated_vertices_spec(vertex_count as int, model_cycles)
            );
            assert(!from_face_cycles_no_isolated_vertices_spec(vertex_count as int, model_cycles));
            assert(from_face_cycles_failure_spec(vertex_count as int, model_cycles));
        }
        return Result::Err(mesh_build_error_empty_face_set());
    }

    let out0 = runtime_build_mesh_from_face_cycles(vertex_positions, face_cycles);
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
} // verus!
