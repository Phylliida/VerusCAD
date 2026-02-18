verus! {
#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_index_bounds(m: &Mesh) -> (out: bool)
    ensures
        out ==> mesh_index_bounds_spec(m@),
        !out ==> !mesh_index_bounds_spec(m@),
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
            proof {
                assert(v < vcnt);
                assert(mesh_vertex_count_spec(m@) == m@.vertex_half_edges.len() as int);
                assert(m@.vertex_half_edges.len() == m.vertices@.len());
                assert(m.vertices@.len() == m.vertices.len());
                assert(mesh_vertex_count_spec(m@) == vcnt as int);

                assert(mesh_half_edge_count_spec(m@) == m@.half_edges.len() as int);
                assert(m@.half_edges.len() == m.half_edges@.len());
                assert(m.half_edges@.len() == m.half_edges.len());
                assert(mesh_half_edge_count_spec(m@) == hcnt as int);

                assert(0 <= v as int && (v as int) < mesh_vertex_count_spec(m@));
                assert(m@.vertex_half_edges[v as int] == he as int);
                assert(!(0 <= m@.vertex_half_edges[v as int] < mesh_half_edge_count_spec(m@)));
                assert(!mesh_index_bounds_spec(m@)) by {
                    if mesh_index_bounds_spec(m@) {
                        assert(0 <= #[trigger] m@.vertex_half_edges[v as int] < mesh_half_edge_count_spec(m@));
                        assert(false);
                    }
                };
            }
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
            proof {
                assert(e < ecnt);
                assert(mesh_edge_count_spec(m@) == m@.edge_half_edges.len() as int);
                assert(m@.edge_half_edges.len() == m.edges@.len());
                assert(m.edges@.len() == m.edges.len());
                assert(mesh_edge_count_spec(m@) == ecnt as int);

                assert(mesh_half_edge_count_spec(m@) == m@.half_edges.len() as int);
                assert(m@.half_edges.len() == m.half_edges@.len());
                assert(m.half_edges@.len() == m.half_edges.len());
                assert(mesh_half_edge_count_spec(m@) == hcnt as int);

                assert(0 <= e as int && (e as int) < mesh_edge_count_spec(m@));
                assert(m@.edge_half_edges[e as int] == he as int);
                assert(!(0 <= m@.edge_half_edges[e as int] < mesh_half_edge_count_spec(m@)));
                assert(!mesh_index_bounds_spec(m@)) by {
                    if mesh_index_bounds_spec(m@) {
                        assert(0 <= #[trigger] m@.edge_half_edges[e as int] < mesh_half_edge_count_spec(m@));
                        assert(false);
                    }
                };
            }
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
            proof {
                assert(f < fcnt);
                assert(mesh_face_count_spec(m@) == m@.face_half_edges.len() as int);
                assert(m@.face_half_edges.len() == m.faces@.len());
                assert(m.faces@.len() == m.faces.len());
                assert(mesh_face_count_spec(m@) == fcnt as int);

                assert(mesh_half_edge_count_spec(m@) == m@.half_edges.len() as int);
                assert(m@.half_edges.len() == m.half_edges@.len());
                assert(m.half_edges@.len() == m.half_edges.len());
                assert(mesh_half_edge_count_spec(m@) == hcnt as int);

                assert(0 <= f as int && (f as int) < mesh_face_count_spec(m@));
                assert(m@.face_half_edges[f as int] == he as int);
                assert(!(0 <= m@.face_half_edges[f as int] < mesh_half_edge_count_spec(m@)));
                assert(!mesh_index_bounds_spec(m@)) by {
                    if mesh_index_bounds_spec(m@) {
                        assert(0 <= #[trigger] m@.face_half_edges[f as int] < mesh_half_edge_count_spec(m@));
                        assert(false);
                    }
                };
            }
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
            proof {
                assert(h < hcnt);

                assert(mesh_half_edge_count_spec(m@) == m@.half_edges.len() as int);
                assert(m@.half_edges.len() == m.half_edges@.len());
                assert(m.half_edges@.len() == m.half_edges.len());
                assert(mesh_half_edge_count_spec(m@) == hcnt as int);

                assert(mesh_vertex_count_spec(m@) == m@.vertex_half_edges.len() as int);
                assert(m@.vertex_half_edges.len() == m.vertices@.len());
                assert(m.vertices@.len() == m.vertices.len());
                assert(mesh_vertex_count_spec(m@) == vcnt as int);

                assert(mesh_edge_count_spec(m@) == m@.edge_half_edges.len() as int);
                assert(m@.edge_half_edges.len() == m.edges@.len());
                assert(m.edges@.len() == m.edges.len());
                assert(mesh_edge_count_spec(m@) == ecnt as int);

                assert(mesh_face_count_spec(m@) == m@.face_half_edges.len() as int);
                assert(m@.face_half_edges.len() == m.faces@.len());
                assert(m.faces@.len() == m.faces.len());
                assert(mesh_face_count_spec(m@) == fcnt as int);

                assert(0 <= h as int && (h as int) < mesh_half_edge_count_spec(m@));
                assert(m@.half_edges[h as int].twin == he.twin as int);
                assert(m@.half_edges[h as int].next == he.next as int);
                assert(m@.half_edges[h as int].prev == he.prev as int);
                assert(m@.half_edges[h as int].vertex == he.vertex as int);
                assert(m@.half_edges[h as int].edge == he.edge as int);
                assert(m@.half_edges[h as int].face == he.face as int);

                assert(!mesh_index_bounds_spec(m@)) by {
                    if mesh_index_bounds_spec(m@) {
                        assert(0 <= #[trigger] m@.half_edges[h as int].twin < mesh_half_edge_count_spec(m@));
                        assert(0 <= #[trigger] m@.half_edges[h as int].next < mesh_half_edge_count_spec(m@));
                        assert(0 <= #[trigger] m@.half_edges[h as int].prev < mesh_half_edge_count_spec(m@));
                        assert(0 <= #[trigger] m@.half_edges[h as int].vertex < mesh_vertex_count_spec(m@));
                        assert(0 <= #[trigger] m@.half_edges[h as int].edge < mesh_edge_count_spec(m@));
                        assert(0 <= #[trigger] m@.half_edges[h as int].face < mesh_face_count_spec(m@));

                        if he.twin >= hcnt {
                            assert(!(0 <= m@.half_edges[h as int].twin < mesh_half_edge_count_spec(m@)));
                        } else if he.next >= hcnt {
                            assert(!(0 <= m@.half_edges[h as int].next < mesh_half_edge_count_spec(m@)));
                        } else if he.prev >= hcnt {
                            assert(!(0 <= m@.half_edges[h as int].prev < mesh_half_edge_count_spec(m@)));
                        } else if he.vertex >= vcnt {
                            assert(!(0 <= m@.half_edges[h as int].vertex < mesh_vertex_count_spec(m@)));
                        } else if he.edge >= ecnt {
                            assert(!(0 <= m@.half_edges[h as int].edge < mesh_edge_count_spec(m@)));
                        } else {
                            assert(he.face >= fcnt);
                            assert(!(0 <= m@.half_edges[h as int].face < mesh_face_count_spec(m@)));
                        }
                        assert(false);
                    }
                };
            }
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
        !out ==> !from_face_cycles_twin_assignment_total_involution_spec(m@),
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
            proof {
                let hh = h as int;
                assert(mesh_half_edge_count_spec(m@) == hcnt as int);
                assert(0 <= hh);
                assert(hh < mesh_half_edge_count_spec(m@));
                assert(m@.half_edges[hh].twin == t as int);
                assert(!(0 <= m@.half_edges[hh].twin < mesh_half_edge_count_spec(m@)));
                assert(!from_face_cycles_twin_assignment_total_involution_at_spec(m@, hh));
                assert(!from_face_cycles_twin_assignment_total_involution_spec(m@)) by {
                    if from_face_cycles_twin_assignment_total_involution_spec(m@) {
                        assert(from_face_cycles_twin_assignment_total_involution_at_spec(m@, hh));
                        assert(false);
                    }
                };
            }
            return false;
        }
        let tt = m.half_edges[t].twin;
        if tt != h {
            proof {
                let hh = h as int;
                assert(mesh_half_edge_count_spec(m@) == hcnt as int);
                assert(0 <= hh);
                assert(hh < mesh_half_edge_count_spec(m@));
                assert(0 <= t as int);
                assert((t as int) < mesh_half_edge_count_spec(m@));
                assert(m@.half_edges[hh].twin == t as int);
                assert(m@.half_edges[t as int].twin == m.half_edges@[t as int].twin);
                assert(m.half_edges@[t as int].twin == tt as int);
                assert(m@.half_edges[m@.half_edges[hh].twin].twin == tt as int);
                assert(tt != h);
                assert(m@.half_edges[m@.half_edges[hh].twin].twin != hh);
                assert(!from_face_cycles_twin_assignment_total_involution_at_spec(m@, hh));
                assert(!from_face_cycles_twin_assignment_total_involution_spec(m@)) by {
                    if from_face_cycles_twin_assignment_total_involution_spec(m@) {
                        assert(from_face_cycles_twin_assignment_total_involution_at_spec(m@, hh));
                        assert(false);
                    }
                };
            }
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
            #![trigger from_face_cycles_twin_assignment_total_involution_at_spec(m@, hp)]
            0 <= hp < mesh_half_edge_count_spec(m@)
                ==> from_face_cycles_twin_assignment_total_involution_at_spec(m@, hp)) by {
            assert forall|hp: int|
                #![trigger from_face_cycles_twin_assignment_total_involution_at_spec(m@, hp)]
                0 <= hp < mesh_half_edge_count_spec(m@)
                    implies from_face_cycles_twin_assignment_total_involution_at_spec(m@, hp) by {
                assert(mesh_half_edge_count_spec(m@) == h as int);
                assert(0 <= hp < h as int);
                assert(0 <= m@.half_edges[hp].twin < mesh_half_edge_count_spec(m@));
                assert(m@.half_edges[m@.half_edges[hp].twin].twin == hp);
                assert(from_face_cycles_twin_assignment_total_involution_at_spec(m@, hp));
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
pub fn runtime_check_twin_faces_distinct(m: &Mesh) -> (out: bool)
    ensures
        out ==> mesh_twin_faces_distinct_spec(m@),
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
                0 <= hp < h as int ==> #[trigger] mesh_twin_faces_distinct_at_spec(m@, hp),
    {
        let he = &m.half_edges[h];
        let t = he.twin;
        if t >= hcnt {
            return false;
        }

        let twin = &m.half_edges[t];
        if he.face == twin.face {
            return false;
        }

        proof {
            assert(mesh_half_edge_count_spec(m@) == hcnt as int);
            assert(m@.half_edges[h as int].twin == t as int);
            assert(m@.half_edges[h as int].face == he.face as int);
            assert(m@.half_edges[t as int].face == twin.face as int);
            assert(he.face as int != twin.face as int);
            assert(mesh_twin_faces_distinct_at_spec(m@, h as int));

            assert(forall|hp: int|
                0 <= hp < (h + 1) as int ==> #[trigger] mesh_twin_faces_distinct_at_spec(m@, hp)) by {
                assert forall|hp: int|
                    0 <= hp < (h + 1) as int implies #[trigger] mesh_twin_faces_distinct_at_spec(m@, hp) by {
                    if hp < h as int {
                        assert(0 <= hp < h as int);
                    } else {
                        assert(hp == h as int);
                        assert(mesh_twin_faces_distinct_at_spec(m@, hp));
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
            0 <= hp < mesh_half_edge_count_spec(m@)
                ==> #[trigger] mesh_twin_faces_distinct_at_spec(m@, hp)) by {
            assert forall|hp: int|
                0 <= hp < mesh_half_edge_count_spec(m@)
                    implies #[trigger] mesh_twin_faces_distinct_at_spec(m@, hp) by {
                assert(mesh_half_edge_count_spec(m@) == h as int);
                assert(0 <= hp < h as int);
            };
        };
        assert(mesh_twin_faces_distinct_spec(m@));
    }
    true
}

#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_shared_edge_local_orientation_consistency(m: &Mesh) -> (out: bool)
    ensures
        out ==> mesh_shared_edge_local_orientation_consistency_spec(m@),
{
    let twin_faces_distinct_ok = runtime_check_twin_faces_distinct(m);
    if !twin_faces_distinct_ok {
        return false;
    }

    let twin_endpoint_ok = runtime_check_twin_endpoint_correspondence(m);
    if !twin_endpoint_ok {
        return false;
    }

    proof {
        assert(twin_faces_distinct_ok);
        assert(mesh_twin_faces_distinct_spec(m@));
        assert(twin_endpoint_ok);
        assert(from_face_cycles_twin_endpoint_correspondence_spec(m@));
        assert(mesh_shared_edge_local_orientation_consistency_spec(m@));
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
    let out0 = runtime_build_mesh_from_face_cycles(vertex_positions, face_cycles);
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
        !out ==> !mesh_prev_next_inverse_spec(m@),
{
    let hcnt = m.half_edges.len();
    let mut h: usize = 0;
    while h < hcnt
        invariant
            hcnt == m.half_edges.len(),
            0 <= h <= hcnt,
            forall|hp: int|
                0 <= hp < h as int
                    ==> 0 <= #[trigger] m@.half_edges[hp].next < hcnt as int,
            forall|hp: int|
                0 <= hp < h as int
                    ==> 0 <= #[trigger] m@.half_edges[hp].prev < hcnt as int,
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
            proof {
                assert(mesh_half_edge_count_spec(m@) == hcnt as int);
                assert(0 <= (h as int) && (h as int) < mesh_half_edge_count_spec(m@));
                assert(m@.half_edges[h as int].next == n as int);
                assert(m@.half_edges[h as int].prev == p as int);
                assert(!mesh_prev_next_inverse_spec(m@)) by {
                    if mesh_prev_next_inverse_spec(m@) {
                        assert(mesh_prev_next_inverse_at_spec(m@, h as int));
                        if n >= hcnt {
                            assert(!(0 <= m@.half_edges[h as int].next < mesh_half_edge_count_spec(m@)));
                        } else {
                            assert(p >= hcnt);
                            assert(!(0 <= m@.half_edges[h as int].prev < mesh_half_edge_count_spec(m@)));
                        }
                        assert(false);
                    }
                };
            }
            return false;
        }
        if m.half_edges[n].prev != h {
            proof {
                assert(mesh_half_edge_count_spec(m@) == hcnt as int);
                assert(0 <= (h as int) && (h as int) < mesh_half_edge_count_spec(m@));
                assert(m@.half_edges[h as int].next == n as int);
                assert(m@.half_edges[n as int].prev == m.half_edges@[n as int].prev);
                assert(m.half_edges@[n as int].prev != h as int);
                assert(m@.half_edges[m@.half_edges[h as int].next].prev != h as int);
                assert(!mesh_prev_next_inverse_spec(m@)) by {
                    if mesh_prev_next_inverse_spec(m@) {
                        assert(mesh_prev_next_inverse_at_spec(m@, h as int));
                        assert(m@.half_edges[m@.half_edges[h as int].next].prev == h as int);
                        assert(false);
                    }
                };
            }
            return false;
        }
        if m.half_edges[p].next != h {
            proof {
                assert(mesh_half_edge_count_spec(m@) == hcnt as int);
                assert(0 <= (h as int) && (h as int) < mesh_half_edge_count_spec(m@));
                assert(m@.half_edges[h as int].prev == p as int);
                assert(m@.half_edges[p as int].next == m.half_edges@[p as int].next);
                assert(m.half_edges@[p as int].next != h as int);
                assert(m@.half_edges[m@.half_edges[h as int].prev].next != h as int);
                assert(!mesh_prev_next_inverse_spec(m@)) by {
                    if mesh_prev_next_inverse_spec(m@) {
                        assert(mesh_prev_next_inverse_at_spec(m@, h as int));
                        assert(m@.half_edges[m@.half_edges[h as int].prev].next == h as int);
                        assert(false);
                    }
                };
            }
            return false;
        }

        proof {
            assert(mesh_half_edge_count_spec(m@) == hcnt as int);
            assert(m@.half_edges[h as int].next == n as int);
            assert(m@.half_edges[h as int].prev == p as int);
            assert(0 <= (n as int) && (n as int) < mesh_half_edge_count_spec(m@));
            assert(0 <= (p as int) && (p as int) < mesh_half_edge_count_spec(m@));
            assert(0 <= #[trigger] m@.half_edges[h as int].next < hcnt as int);
            assert(0 <= #[trigger] m@.half_edges[h as int].prev < hcnt as int);
            assert(m@.half_edges[n as int].prev == m.half_edges@[n as int].prev);
            assert(m@.half_edges[p as int].next == m.half_edges@[p as int].next);
            assert(m.half_edges@[n as int].prev == h as int);
            assert(m.half_edges@[p as int].next == h as int);
            assert(#[trigger] m@.half_edges[m@.half_edges[h as int].next].prev == h as int);
            assert(#[trigger] m@.half_edges[m@.half_edges[h as int].prev].next == h as int);

            assert(forall|hp: int|
                0 <= hp < (h + 1) as int
                    ==> 0 <= #[trigger] m@.half_edges[hp].next < hcnt as int) by {
                assert forall|hp: int|
                    0 <= hp < (h + 1) as int
                        implies 0 <= #[trigger] m@.half_edges[hp].next < hcnt as int by {
                    if hp < h as int {
                        assert(0 <= hp < h as int);
                    } else {
                        assert(hp == h as int);
                        assert(0 <= #[trigger] m@.half_edges[h as int].next < hcnt as int);
                    }
                };
            };
            assert(forall|hp: int|
                0 <= hp < (h + 1) as int
                    ==> 0 <= #[trigger] m@.half_edges[hp].prev < hcnt as int) by {
                assert forall|hp: int|
                    0 <= hp < (h + 1) as int
                        implies 0 <= #[trigger] m@.half_edges[hp].prev < hcnt as int by {
                    if hp < h as int {
                        assert(0 <= hp < h as int);
                    } else {
                        assert(hp == h as int);
                        assert(0 <= #[trigger] m@.half_edges[h as int].prev < hcnt as int);
                    }
                };
            };
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
                ==> 0 <= #[trigger] m@.half_edges[hp].next < mesh_half_edge_count_spec(m@)) by {
            assert forall|hp: int|
                0 <= hp < mesh_half_edge_count_spec(m@)
                    implies 0 <= #[trigger] m@.half_edges[hp].next < mesh_half_edge_count_spec(m@) by {
                assert(mesh_half_edge_count_spec(m@) == h as int);
                assert(0 <= hp < h as int);
            };
        };
        assert(forall|hp: int|
            0 <= hp < mesh_half_edge_count_spec(m@)
                ==> 0 <= #[trigger] m@.half_edges[hp].prev < mesh_half_edge_count_spec(m@)) by {
            assert forall|hp: int|
                0 <= hp < mesh_half_edge_count_spec(m@)
                    implies 0 <= #[trigger] m@.half_edges[hp].prev < mesh_half_edge_count_spec(m@) by {
                assert(mesh_half_edge_count_spec(m@) == h as int);
                assert(0 <= hp < h as int);
            };
        };
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
            assert forall|hp: int|
                0 <= hp < mesh_half_edge_count_spec(m@) implies #[trigger] mesh_prev_next_inverse_at_spec(m@, hp) by {
                assert(0 <= #[trigger] m@.half_edges[hp].next < mesh_half_edge_count_spec(m@));
                assert(0 <= #[trigger] m@.half_edges[hp].prev < mesh_half_edge_count_spec(m@));
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
        !out ==> !mesh_no_degenerate_edges_spec(m@),
{
    let hcnt = m.half_edges.len();
    let mut h: usize = 0;
    while h < hcnt
        invariant
            hcnt == m.half_edges.len(),
            0 <= h <= hcnt,
            forall|hp: int|
                0 <= hp < h as int
                    ==> 0 <= #[trigger] m@.half_edges[hp].twin < hcnt as int,
            forall|hp: int|
                0 <= hp < h as int
                    ==> 0 <= #[trigger] m@.half_edges[hp].next < hcnt as int,
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
            proof {
                assert(mesh_half_edge_count_spec(m@) == hcnt as int);
                assert(0 <= (h as int) && (h as int) < mesh_half_edge_count_spec(m@));
                assert(m@.half_edges[h as int].twin == t as int);
                assert(m@.half_edges[h as int].next == n as int);
                assert(!mesh_no_degenerate_edges_spec(m@)) by {
                    if mesh_no_degenerate_edges_spec(m@) {
                        assert(mesh_no_degenerate_edges_at_spec(m@, h as int));
                        if t >= hcnt {
                            assert(!(0 <= m@.half_edges[h as int].twin < mesh_half_edge_count_spec(m@)));
                        } else {
                            assert(n >= hcnt);
                            assert(!(0 <= m@.half_edges[h as int].next < mesh_half_edge_count_spec(m@)));
                        }
                        assert(false);
                    }
                };
            }
            return false;
        }
        let tv = m.half_edges[t].vertex;
        if he.vertex == tv {
            proof {
                assert(mesh_half_edge_count_spec(m@) == hcnt as int);
                assert(0 <= (h as int) && (h as int) < mesh_half_edge_count_spec(m@));
                assert(m@.half_edges[h as int].twin == t as int);
                assert(m@.half_edges[h as int].vertex == he.vertex as int);
                assert(m@.half_edges[t as int].vertex == m.half_edges@[t as int].vertex);
                assert(m.half_edges@[t as int].vertex == tv as int);
                assert(he.vertex as int == tv as int);
                assert(m@.half_edges[h as int].vertex == m@.half_edges[t as int].vertex);
                assert(!mesh_no_degenerate_edges_spec(m@)) by {
                    if mesh_no_degenerate_edges_spec(m@) {
                        assert(mesh_no_degenerate_edges_at_spec(m@, h as int));
                        assert(m@.half_edges[h as int].vertex != m@.half_edges[m@.half_edges[h as int].twin].vertex);
                        assert(false);
                    }
                };
            }
            return false;
        }
        let nv = m.half_edges[n].vertex;
        if he.vertex == nv {
            proof {
                assert(mesh_half_edge_count_spec(m@) == hcnt as int);
                assert(0 <= (h as int) && (h as int) < mesh_half_edge_count_spec(m@));
                assert(m@.half_edges[h as int].next == n as int);
                assert(m@.half_edges[h as int].vertex == he.vertex as int);
                assert(m@.half_edges[n as int].vertex == m.half_edges@[n as int].vertex);
                assert(m.half_edges@[n as int].vertex == nv as int);
                assert(he.vertex as int == nv as int);
                assert(m@.half_edges[h as int].vertex == m@.half_edges[n as int].vertex);
                assert(!mesh_no_degenerate_edges_spec(m@)) by {
                    if mesh_no_degenerate_edges_spec(m@) {
                        assert(mesh_no_degenerate_edges_at_spec(m@, h as int));
                        assert(m@.half_edges[h as int].vertex != m@.half_edges[m@.half_edges[h as int].next].vertex);
                        assert(false);
                    }
                };
            }
            return false;
        }

        proof {
            assert(mesh_half_edge_count_spec(m@) == hcnt as int);
            assert(m@.half_edges[h as int].twin == t as int);
            assert(m@.half_edges[h as int].next == n as int);
            assert(0 <= (t as int) && (t as int) < mesh_half_edge_count_spec(m@));
            assert(0 <= (n as int) && (n as int) < mesh_half_edge_count_spec(m@));
            assert(0 <= #[trigger] m@.half_edges[h as int].twin < hcnt as int);
            assert(0 <= #[trigger] m@.half_edges[h as int].next < hcnt as int);
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
                    ==> 0 <= #[trigger] m@.half_edges[hp].twin < hcnt as int) by {
                assert forall|hp: int|
                    0 <= hp < (h + 1) as int
                        implies 0 <= #[trigger] m@.half_edges[hp].twin < hcnt as int by {
                    if hp < h as int {
                        assert(0 <= hp < h as int);
                    } else {
                        assert(hp == h as int);
                        assert(0 <= #[trigger] m@.half_edges[h as int].twin < hcnt as int);
                    }
                };
            };
            assert(forall|hp: int|
                0 <= hp < (h + 1) as int
                    ==> 0 <= #[trigger] m@.half_edges[hp].next < hcnt as int) by {
                assert forall|hp: int|
                    0 <= hp < (h + 1) as int
                        implies 0 <= #[trigger] m@.half_edges[hp].next < hcnt as int by {
                    if hp < h as int {
                        assert(0 <= hp < h as int);
                    } else {
                        assert(hp == h as int);
                        assert(0 <= #[trigger] m@.half_edges[h as int].next < hcnt as int);
                    }
                };
            };
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
                ==> 0 <= #[trigger] m@.half_edges[hp].twin < mesh_half_edge_count_spec(m@)) by {
            assert forall|hp: int|
                0 <= hp < mesh_half_edge_count_spec(m@)
                    implies 0 <= #[trigger] m@.half_edges[hp].twin < mesh_half_edge_count_spec(m@) by {
                assert(mesh_half_edge_count_spec(m@) == h as int);
                assert(0 <= hp < h as int);
            };
        };
        assert(forall|hp: int|
            0 <= hp < mesh_half_edge_count_spec(m@)
                ==> 0 <= #[trigger] m@.half_edges[hp].next < mesh_half_edge_count_spec(m@)) by {
            assert forall|hp: int|
                0 <= hp < mesh_half_edge_count_spec(m@)
                    implies 0 <= #[trigger] m@.half_edges[hp].next < mesh_half_edge_count_spec(m@) by {
                assert(mesh_half_edge_count_spec(m@) == h as int);
                assert(0 <= hp < h as int);
            };
        };
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
            assert forall|hp: int|
                0 <= hp < mesh_half_edge_count_spec(m@) implies #[trigger] mesh_no_degenerate_edges_at_spec(m@, hp) by {
                assert(0 <= #[trigger] m@.half_edges[hp].twin < mesh_half_edge_count_spec(m@));
                assert(0 <= #[trigger] m@.half_edges[hp].next < mesh_half_edge_count_spec(m@));
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
    let out0 = runtime_build_mesh_from_face_cycles(vertex_positions, face_cycles);
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
        !out ==> !mesh_vertex_representative_valid_nonisolated_spec(m@),
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
            proof {
                let vi = v as int;
                assert(mesh_vertex_count_spec(m@) == m.vertices.len() as int);
                assert(0 <= vi < mesh_vertex_count_spec(m@));
                assert(mesh_half_edge_count_spec(m@) == hcnt as int);
                assert(m@.vertex_half_edges[vi] == h as int);
                assert(!(0 <= m@.vertex_half_edges[vi] < mesh_half_edge_count_spec(m@)));
                assert(!mesh_vertex_representative_valid_nonisolated_spec(m@)) by {
                    if mesh_vertex_representative_valid_nonisolated_spec(m@) {
                        assert(0 <= m@.vertex_half_edges[vi] < mesh_half_edge_count_spec(m@));
                        assert(false);
                    }
                };
            }
            return false;
        }
        let hv = m.half_edges[h].vertex;
        if hv != v {
            proof {
                let vi = v as int;
                assert(mesh_vertex_count_spec(m@) == m.vertices.len() as int);
                assert(0 <= vi < mesh_vertex_count_spec(m@));
                assert(mesh_half_edge_count_spec(m@) == hcnt as int);
                assert(m@.vertex_half_edges[vi] == h as int);
                assert(0 <= h as int);
                assert((h as int) < mesh_half_edge_count_spec(m@));
                assert(m@.half_edges[h as int].vertex == m.half_edges@[h as int].vertex);
                assert(m.half_edges@[h as int].vertex == hv as int);
                assert(hv != v);
                assert(m@.half_edges[h as int].vertex != vi);
                assert(m@.half_edges[m@.vertex_half_edges[vi]].vertex == m@.half_edges[h as int].vertex);
                assert(m@.half_edges[m@.vertex_half_edges[vi]].vertex != vi);
                assert(!mesh_vertex_representative_valid_nonisolated_spec(m@)) by {
                    if mesh_vertex_representative_valid_nonisolated_spec(m@) {
                        assert(m@.half_edges[m@.vertex_half_edges[vi]].vertex == vi);
                        assert(false);
                    }
                };
            }
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
} // verus!
