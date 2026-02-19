verus! {
#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_compute_euler_characteristics_from_components(
    m: &Mesh,
    components: &[Vec<usize>],
) -> (out: Option<Vec<isize>>)
{
    let mut chis: Vec<isize> = Vec::new();
    let mut c: usize = 0;
    while c < components.len() {
        let component = vstd::slice::slice_index_get(components, c);

        let mut vertex_present = vec![false; m.vertices.len()];
        let mut edge_present = vec![false; m.edges.len()];
        let mut face_present = vec![false; m.faces.len()];

        let mut i: usize = 0;
        while i < component.len() {
            let h = *vstd::slice::slice_index_get(component, i);
            if h >= m.half_edges.len() {
                return Option::None;
            }
            let he = &m.half_edges[h];
            let v = he.vertex;
            let e = he.edge;
            let f = he.face;
            if v >= vertex_present.len() || e >= edge_present.len() || f >= face_present.len() {
                return Option::None;
            }
            vertex_present[v] = true;
            edge_present[e] = true;
            face_present[f] = true;
            i += 1;
        }

        let vcount = runtime_count_true(&vertex_present) as i128;
        let ecount = runtime_count_true(&edge_present) as i128;
        let fcount = runtime_count_true(&face_present) as i128;
        let expected = vcount - ecount + fcount;
        if expected < isize::MIN as i128 || expected > isize::MAX as i128 {
            return Option::None;
        }
        chis.push(expected as isize);

        c += 1;
    }

    Option::Some(chis)
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
    let components = match runtime_compute_half_edge_components(m) {
        Option::Some(components) => components,
        Option::None => return Option::None,
    };
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
    let components = match half_edge_components_constructive(m) {
        Option::Some(components) => components,
        Option::None => return Option::None,
    };

    let count = components.len();

    proof {
        assert(mesh_half_edge_components_partition_neighbor_closed_spec(m@, components@));
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
    let components = match half_edge_components_constructive(m) {
        Option::Some(components) => components,
        Option::None => return Option::None,
    };

    let chis = match runtime_compute_euler_characteristics_from_components(m, &components) {
        Option::Some(chis) => chis,
        Option::None => return Option::None,
    };
    let chis_ok = runtime_check_euler_characteristics_per_component(m, &components, &chis);
    if !chis_ok {
        return Option::None;
    }

    proof {
        assert(mesh_half_edge_components_partition_neighbor_closed_spec(m@, components@));
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
    let components = match half_edge_components_constructive(m) {
        Option::Some(components) => components,
        Option::None => return Option::None,
    };

    let chis = match runtime_compute_euler_characteristics_from_components(m, &components) {
        Option::Some(chis) => chis,
        Option::None => return Option::None,
    };
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
        let _seen_non_two_before = seen_non_two;
        let chi = *vstd::slice::slice_index_get(&chis, c);
        if chi != 2 {
            seen_non_two = true;
        }
        proof {
            assert(chi == chis@[c as int]);
            if !seen_non_two {
                assert(!_seen_non_two_before);
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
    let api_ok = formula_ok;

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
        assert(mesh_half_edge_components_partition_neighbor_closed_spec(m@, components@));
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

#[cfg(feature = "geometry-checks")]
#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_face_seed0_corner_non_collinearity_bridge(m: &Mesh) -> (out: bool)
    ensures
        out ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
{
    if !m.is_valid() {
        return false;
    }

    let index_bounds_ok = runtime_check_index_bounds(m);
    if !index_bounds_ok {
        return false;
    }

    let face_cycles_ok = runtime_check_face_cycles_kernel_bridge(m);
    if !face_cycles_ok {
        return false;
    }

    let fcnt = m.faces.len();

    proof {
        assert(mesh_index_bounds_spec(m@));
        assert(mesh_face_next_cycles_spec(m@));
        lemma_mesh_runtime_geometry_bridge_holds(m);
        assert(mesh_runtime_geometry_bridge_spec(m));
    }

    let ghost face_cycle_lens = choose|face_cycle_lens: Seq<usize>| mesh_face_next_cycles_witness_spec(
        m@,
        face_cycle_lens,
    );
    let ghost vertex_positions = mesh_runtime_vertex_positions_spec(m);

    proof {
        assert(mesh_face_next_cycles_witness_spec(m@, face_cycle_lens));
        assert(mesh_runtime_geometry_bridge_spec(m));
        assert(mesh_geometry_input_spec(m@, vertex_positions));
        assert(face_cycle_lens.len() == mesh_face_count_spec(m@));
        assert(mesh_face_count_spec(m@) == m@.face_half_edges.len() as int);
        assert(m@.face_half_edges.len() == m.faces@.len());
        assert(m.faces@.len() == m.faces.len());
        assert(face_cycle_lens.len() == fcnt as int);
    }

    let mut f: usize = 0;
    while f < fcnt
        invariant
            fcnt == m.faces.len(),
            face_cycle_lens.len() == fcnt as int,
            f <= fcnt,
            mesh_index_bounds_spec(m@),
            mesh_face_next_cycles_witness_spec(m@, face_cycle_lens),
            mesh_runtime_geometry_bridge_spec(m),
            forall|fp: int|
                0 <= fp < f as int ==> !mesh_points_collinear3_spec(
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m@,
                        vertex_positions,
                        fp,
                        0,
                    ),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m@,
                        vertex_positions,
                        fp,
                        1,
                    ),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m@,
                        vertex_positions,
                        fp,
                        2,
                    ),
                ),
    {
        let h0 = m.faces[f].half_edge;
        let h1 = m.half_edges[h0].next;
        let h2 = m.half_edges[h1].next;

        let a = &m.vertices[m.half_edges[h0].vertex].position;
        let b = &m.vertices[m.half_edges[h1].vertex].position;
        let c = &m.vertices[m.half_edges[h2].vertex].position;

        let col = vcad_geometry::collinearity_coplanarity::collinear3d(a, b, c);
        if col {
            return false;
        }

        proof {
            let fi = f as int;
            let k = face_cycle_lens[fi] as int;
            let start = m@.face_half_edges[fi];
            let p0 = mesh_face_cycle_vertex_position_or_default_at_int_spec(
                m@,
                vertex_positions,
                fi,
                0,
            );
            let p1 = mesh_face_cycle_vertex_position_or_default_at_int_spec(
                m@,
                vertex_positions,
                fi,
                1,
            );
            let p2 = mesh_face_cycle_vertex_position_or_default_at_int_spec(
                m@,
                vertex_positions,
                fi,
                2,
            );

            assert(0 <= fi < face_cycle_lens.len());
            assert(mesh_face_cycle_witness_spec(m@, fi, k));
            assert(3 <= k);
            assert(start == h0 as int);
            assert(0 <= start < mesh_half_edge_count_spec(m@));
            assert(mesh_next_iter_spec(m@, start, 0) == start);
            assert(mesh_next_iter_spec(m@, start, 1) == mesh_next_or_self_spec(m@, start));
            assert(mesh_next_or_self_spec(m@, start) == m@.half_edges[start].next);
            assert(m@.half_edges[start].next == h1 as int);
            assert(mesh_next_iter_spec(m@, start, 1) == h1 as int);
            assert(mesh_next_iter_spec(m@, start, 2) == mesh_next_or_self_spec(
                m@,
                mesh_next_iter_spec(m@, start, 1),
            ));
            assert(mesh_next_or_self_spec(m@, mesh_next_iter_spec(m@, start, 1))
                == m@.half_edges[mesh_next_iter_spec(m@, start, 1)].next);
            assert(mesh_next_iter_spec(m@, start, 2) == h2 as int);

            assert(p0 == a@);
            assert(p1 == b@);
            assert(p2 == c@);

            assert(col == mesh_points_collinear3_spec(a@, b@, c@));
            assert(col == mesh_points_collinear3_spec(p0, p1, p2));
            assert(!col);
            assert(!mesh_points_collinear3_spec(p0, p1, p2));

            assert(forall|fp: int|
                0 <= fp < (f + 1) as int ==> !mesh_points_collinear3_spec(
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m@,
                        vertex_positions,
                        fp,
                        0,
                    ),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m@,
                        vertex_positions,
                        fp,
                        1,
                    ),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m@,
                        vertex_positions,
                        fp,
                        2,
                    ),
                )) by {
                assert forall|fp: int|
                    0 <= fp < (f + 1) as int implies !mesh_points_collinear3_spec(
                        mesh_face_cycle_vertex_position_or_default_at_int_spec(
                            m@,
                            vertex_positions,
                            fp,
                            0,
                        ),
                        mesh_face_cycle_vertex_position_or_default_at_int_spec(
                            m@,
                            vertex_positions,
                            fp,
                            1,
                        ),
                        mesh_face_cycle_vertex_position_or_default_at_int_spec(
                            m@,
                            vertex_positions,
                            fp,
                            2,
                        ),
                    ) by {
                    if fp < f as int {
                    } else {
                        assert(fp == fi);
                        assert(!mesh_points_collinear3_spec(
                            mesh_face_cycle_vertex_position_or_default_at_int_spec(
                                m@,
                                vertex_positions,
                                fi,
                                0,
                            ),
                            mesh_face_cycle_vertex_position_or_default_at_int_spec(
                                m@,
                                vertex_positions,
                                fi,
                                1,
                            ),
                            mesh_face_cycle_vertex_position_or_default_at_int_spec(
                                m@,
                                vertex_positions,
                                fi,
                                2,
                            ),
                        ));
                    }
                };
            };
        }

        f += 1;
    }

    proof {
        lemma_usize_loop_exit_eq(f, fcnt);
        assert(f == fcnt);
        assert(mesh_index_bounds_spec(m@));
        assert(mesh_face_next_cycles_spec(m@));
        assert(mesh_runtime_geometry_bridge_spec(m));
        assert(mesh_geometry_input_spec(m@, vertex_positions));
        assert(face_cycle_lens.len() == fcnt as int);
        assert(forall|fp: int|
            0 <= fp < mesh_face_count_spec(m@) ==> !mesh_points_collinear3_spec(
                mesh_face_cycle_vertex_position_or_default_at_int_spec(
                    m@,
                    vertex_positions,
                    fp,
                    0,
                ),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(
                    m@,
                    vertex_positions,
                    fp,
                    1,
                ),
                mesh_face_cycle_vertex_position_or_default_at_int_spec(
                    m@,
                    vertex_positions,
                    fp,
                    2,
                ),
            )) by {
            assert forall|fp: int|
                0 <= fp < mesh_face_count_spec(m@) implies !mesh_points_collinear3_spec(
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m@,
                        vertex_positions,
                        fp,
                        0,
                    ),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m@,
                        vertex_positions,
                        fp,
                        1,
                    ),
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m@,
                        vertex_positions,
                        fp,
                        2,
                    ),
                ) by {
                assert(mesh_face_count_spec(m@) == face_cycle_lens.len());
                assert(face_cycle_lens.len() == fcnt as int);
                assert(0 <= fp < f as int);
            };
        };
        assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
    }

    true
}

#[cfg(feature = "geometry-checks")]
#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_no_zero_length_geometric_edges_sound_bridge(
    m: &Mesh,
) -> (out: bool)
    ensures
        out ==> mesh_valid_spec(m@),
        out ==> mesh_runtime_all_half_edges_non_zero_geometric_length_spec(m),
{
    use vcad_math::runtime_scalar::RuntimeSign::*;

    let runtime_ok = m.check_no_zero_length_geometric_edges();
    if !runtime_ok {
        return false;
    }

    let validity_w = match is_valid_constructive(m) {
        Option::Some(w) => w,
        Option::None => return false,
    };
    if !validity_w.api_ok {
        return false;
    }

    let hcnt = m.half_edges.len();
    let ghost vertex_positions = mesh_runtime_vertex_positions_spec(m);

    proof {
        assert(validity_gate_witness_spec(validity_w));
        assert(validity_gate_model_link_spec(m@, validity_w));
        lemma_validity_gate_witness_api_ok_implies_mesh_valid(m@, validity_w);
        assert(mesh_valid_spec(m@));
        assert(mesh_structurally_valid_spec(m@));
        assert(mesh_index_bounds_spec(m@));
        lemma_mesh_runtime_geometry_bridge_holds(m);
        assert(mesh_runtime_geometry_bridge_spec(m));
        assert(mesh_geometry_input_spec(m@, vertex_positions));
        assert(mesh_half_edge_count_spec(m@) == hcnt as int);
    }

    let mut h: usize = 0;
    while h < hcnt
        invariant
            hcnt == m.half_edges.len(),
            mesh_half_edge_count_spec(m@) == hcnt as int,
            mesh_valid_spec(m@),
            mesh_index_bounds_spec(m@),
            mesh_runtime_geometry_bridge_spec(m),
            mesh_geometry_input_spec(m@, vertex_positions),
            0 <= h <= hcnt,
            forall|hp: int|
                0 <= hp < h as int
                    ==> #[trigger] mesh_half_edge_non_zero_geometric_length_at_spec(
                        m@,
                        vertex_positions,
                        hp,
                    ),
    {
        let he = &m.half_edges[h];
        let a = &m.vertices[he.vertex].position;
        let b = &m.vertices[m.half_edges[he.next].vertex].position;

        let d2 = a.dist2(b);
        let d2_sign = d2.sign();
        if let Zero = d2_sign {
            return false;
        }

        proof {
            let hi = h as int;
            assert(0 <= hi < mesh_half_edge_count_spec(m@));
            assert(mesh_geometry_input_spec(m@, vertex_positions));
            lemma_mesh_half_edge_segment_geometry_at_from_model_and_positions(m@, vertex_positions, hi);
            assert(mesh_half_edge_segment_geometry_at_spec(m@, vertex_positions, hi));

            assert(m@.half_edges[hi].vertex == he.vertex as int);
            assert(m@.half_edges[hi].next == he.next as int);
            assert(mesh_half_edge_from_position_spec(m@, vertex_positions, hi) == a@);
            assert(mesh_half_edge_to_position_spec(m@, vertex_positions, hi) == b@);

            assert((d2_sign is Zero) == (d2@.signum() == 0));
            assert(d2@.signum() != 0);
            assert(!d2@.eqv_spec(Scalar::from_int_spec(0))) by {
                if d2@.eqv_spec(Scalar::from_int_spec(0)) {
                    Scalar::lemma_eqv_signum(d2@, Scalar::from_int_spec(0));
                    assert(d2@.signum() == 0);
                    assert(false);
                }
            };

            vcad_math::point3::lemma_dist2_zero_iff_equal_points(a@, b@);
            assert(d2@ == vcad_math::point3::dist2_spec(a@, b@));
            assert(!a@.eqv_spec(b@)) by {
                if a@.eqv_spec(b@) {
                    assert(vcad_math::point3::dist2_spec(a@, b@).eqv_spec(Scalar::from_int_spec(0)));
                    assert(d2@.eqv_spec(Scalar::from_int_spec(0)));
                    assert(false);
                }
            };
            assert(!mesh_half_edge_from_position_spec(m@, vertex_positions, hi).eqv_spec(
                mesh_half_edge_to_position_spec(m@, vertex_positions, hi),
            ));
            assert(mesh_half_edge_non_zero_geometric_length_at_spec(m@, vertex_positions, hi));

            assert(forall|hp: int|
                0 <= hp < (h + 1) as int
                    ==> #[trigger] mesh_half_edge_non_zero_geometric_length_at_spec(
                        m@,
                        vertex_positions,
                        hp,
                    )) by {
                assert forall|hp: int|
                    0 <= hp < (h + 1) as int
                        implies #[trigger] mesh_half_edge_non_zero_geometric_length_at_spec(
                            m@,
                            vertex_positions,
                            hp,
                        ) by {
                    if hp < h as int {
                    } else {
                        assert(hp == hi);
                        assert(mesh_half_edge_non_zero_geometric_length_at_spec(m@, vertex_positions, hp));
                    }
                };
            };
        }

        h += 1;
    }

    proof {
        lemma_usize_loop_exit_eq(h, hcnt);
        assert(h == hcnt);
        assert(forall|hp: int|
            0 <= hp < mesh_half_edge_count_spec(m@)
                ==> #[trigger] mesh_half_edge_non_zero_geometric_length_at_spec(
                    m@,
                    vertex_positions,
                    hp,
                )) by {
            assert forall|hp: int|
                0 <= hp < mesh_half_edge_count_spec(m@)
                    implies #[trigger] mesh_half_edge_non_zero_geometric_length_at_spec(
                        m@,
                        vertex_positions,
                        hp,
                    ) by {
                assert(mesh_half_edge_count_spec(m@) == hcnt as int);
                assert(0 <= hp < h as int);
            };
        };
        assert(mesh_all_half_edges_non_zero_geometric_length_spec(m@, vertex_positions));
        assert(mesh_runtime_all_half_edges_non_zero_geometric_length_spec(m));
        assert(mesh_valid_spec(m@));
    }

    true
}

#[cfg(feature = "geometry-checks")]
#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_bridge(m: &Mesh) -> (out: bool)
    ensures
        out ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        out ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        out ==> mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        out ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
        out ==> exists|face_cycle_lens: Seq<usize>| {
            &&& mesh_face_next_cycles_witness_spec(m@, face_cycle_lens)
            &&& forall|f: int|
                0 <= f < mesh_face_count_spec(m@)
                    ==> #[trigger] mesh_face_coplanar_fixed_seed_witness_spec(
                        m@,
                        mesh_runtime_vertex_positions_spec(m),
                        f,
                        face_cycle_lens[f] as int,
                        0,
                    )
        },
{
    if !m.is_valid() {
        return false;
    }

    let index_bounds_ok = runtime_check_index_bounds(m);
    if !index_bounds_ok {
        return false;
    }

    let face_cycles_ok = runtime_check_face_cycles_kernel_bridge(m);
    if !face_cycles_ok {
        return false;
    }

    if !m.check_face_corner_non_collinearity() {
        return false;
    }
    let seed0_corner_non_collinearity_ok = runtime_check_face_seed0_corner_non_collinearity_bridge(
        m,
    );
    if !seed0_corner_non_collinearity_ok {
        return false;
    }

    let fcnt = m.faces.len();
    let hcnt = m.half_edges.len();

    proof {
        assert(mesh_index_bounds_spec(m@));
        assert(mesh_face_next_cycles_spec(m@));
        lemma_mesh_runtime_geometry_bridge_holds(m);
        assert(mesh_runtime_geometry_bridge_spec(m));
    }

    let ghost face_cycle_lens = choose|face_cycle_lens: Seq<usize>| mesh_face_next_cycles_witness_spec(
        m@,
        face_cycle_lens,
    );
    let ghost vertex_positions = mesh_runtime_vertex_positions_spec(m);

    proof {
        assert(mesh_face_next_cycles_witness_spec(m@, face_cycle_lens));
        assert(mesh_runtime_geometry_bridge_spec(m));
        assert(mesh_geometry_input_spec(m@, vertex_positions));
        assert(face_cycle_lens.len() == mesh_face_count_spec(m@));
        assert(mesh_face_count_spec(m@) == m@.face_half_edges.len() as int);
        assert(m@.face_half_edges.len() == m.faces@.len());
        assert(m.faces@.len() == m.faces.len());
        assert(face_cycle_lens.len() == fcnt as int);
    }

    let mut f: usize = 0;
    while f < fcnt
        invariant
            fcnt == m.faces.len(),
            hcnt == m.half_edges.len(),
            face_cycle_lens.len() == fcnt as int,
            f <= fcnt,
            mesh_index_bounds_spec(m@),
            mesh_face_next_cycles_witness_spec(m@, face_cycle_lens),
            mesh_runtime_geometry_bridge_spec(m),
            forall|fp: int|
                0 <= fp < f as int
                    ==> #[trigger] mesh_face_coplanar_seed0_fixed_witness_spec(
                        m@,
                        vertex_positions,
                        fp,
                    ),
    {
        let h0 = m.faces[f].half_edge;
        let h1 = m.half_edges[h0].next;
        let h2 = m.half_edges[h1].next;

        let a = &m.vertices[m.half_edges[h0].vertex].position;
        let b = &m.vertices[m.half_edges[h1].vertex].position;
        let c = &m.vertices[m.half_edges[h2].vertex].position;

        let ghost fi = f as int;
        let ghost k = face_cycle_lens[fi] as int;
        let ghost start = m@.face_half_edges[fi];
        let ghost p0 = mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m@,
            vertex_positions,
            fi,
            0,
        );
        let ghost p1 = mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m@,
            vertex_positions,
            fi,
            1,
        );
        let ghost p2 = mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m@,
            vertex_positions,
            fi,
            2,
        );

        proof {
            assert(0 <= fi < face_cycle_lens.len());
            assert(mesh_face_cycle_witness_spec(m@, fi, k));
            assert(3 <= k);
            assert(k <= hcnt as int);
            assert(start == h0 as int);
            assert(0 <= start < mesh_half_edge_count_spec(m@));
            assert(mesh_next_iter_spec(m@, start, 0) == start);
            assert(mesh_next_iter_spec(m@, start, 1) == mesh_next_or_self_spec(m@, start));
            assert(mesh_next_or_self_spec(m@, start) == m@.half_edges[start].next);
            assert(m@.half_edges[start].next == h1 as int);
            assert(mesh_next_iter_spec(m@, start, 1) == h1 as int);
            assert(mesh_next_iter_spec(m@, start, 2) == mesh_next_or_self_spec(
                m@,
                mesh_next_iter_spec(m@, start, 1),
            ));
            assert(mesh_next_or_self_spec(m@, mesh_next_iter_spec(m@, start, 1))
                == m@.half_edges[mesh_next_iter_spec(m@, start, 1)].next);
            assert(mesh_next_iter_spec(m@, start, 2) == h2 as int);

            assert(p0 == a@);
            assert(p1 == b@);
            assert(p2 == c@);
        }

        let mut h: usize = m.half_edges[h2].next;
        let mut steps: usize = 3;

        proof {
            assert(mesh_next_iter_spec(m@, start, 3) == mesh_next_or_self_spec(
                m@,
                mesh_next_iter_spec(m@, start, 2),
            ));
            assert(mesh_next_or_self_spec(m@, mesh_next_iter_spec(m@, start, 2))
                == m@.half_edges[mesh_next_iter_spec(m@, start, 2)].next);
            assert(mesh_next_iter_spec(m@, start, 2) == h2 as int);
            assert(m@.half_edges[h2 as int].next == h as int);
            assert(h as int == mesh_next_iter_spec(m@, start, 3));
            assert((steps as int) == 3);
            assert((steps as int) <= k);
            assert(steps <= hcnt);

            let o_d0 = vcad_math::orientation3::orient3d_spec(p0, p1, p2, p0);
            let o_rep0 = vcad_math::orientation3::orient3d_spec(p0, p0, p1, p2);
            vcad_math::orientation3::lemma_orient3d_cycle_bcd_eqv(p0, p1, p2, p0);
            assert(o_d0.eqv_spec(o_rep0));
            vcad_math::orientation3::lemma_orient3d_degenerate_repeated_points(p0, p1, p2);
            assert(o_rep0.signum() == 0);
            vcad_math::scalar::Scalar::lemma_eqv_signum(o_d0, o_rep0);
            assert(o_d0.signum() == 0);
            assert(vcad_math::orientation3::is_coplanar(p0, p1, p2, p0));

            let o_d1 = vcad_math::orientation3::orient3d_spec(p0, p1, p2, p1);
            let o_rep1 = vcad_math::orientation3::orient3d_spec(p0, p2, p1, p1);
            vcad_math::orientation3::lemma_orient3d_cycle_bcd_eqv(p0, p1, p2, p1);
            assert(o_d1.eqv_spec(o_rep1));
            vcad_math::orientation3::lemma_orient3d_degenerate_repeated_points(p0, p2, p1);
            assert(o_rep1.signum() == 0);
            vcad_math::scalar::Scalar::lemma_eqv_signum(o_d1, o_rep1);
            assert(o_d1.signum() == 0);
            assert(vcad_math::orientation3::is_coplanar(p0, p1, p2, p1));

            vcad_math::orientation3::lemma_orient3d_degenerate_repeated_points(p0, p1, p2);
            assert(vcad_math::orientation3::is_coplanar(p0, p1, p2, p2));

            assert(forall|d: int|
                0 <= d < (steps as int)
                    ==> #[trigger] vcad_math::orientation3::is_coplanar(
                        p0,
                        p1,
                        p2,
                        mesh_face_cycle_vertex_position_or_default_at_int_spec(
                            m@,
                            vertex_positions,
                            fi,
                            d,
                        ),
                    )) by {
                assert forall|d: int|
                    0 <= d < (steps as int)
                        implies #[trigger] vcad_math::orientation3::is_coplanar(
                            p0,
                            p1,
                            p2,
                            mesh_face_cycle_vertex_position_or_default_at_int_spec(
                                m@,
                                vertex_positions,
                                fi,
                                d,
                            ),
                        ) by {
                    assert(0 <= d < 3);
                    if d == 0 {
                        assert(mesh_face_cycle_vertex_position_or_default_at_int_spec(
                            m@,
                            vertex_positions,
                            fi,
                            d,
                        ) == p0);
                        assert(vcad_math::orientation3::is_coplanar(p0, p1, p2, p0));
                    } else if d == 1 {
                        assert(mesh_face_cycle_vertex_position_or_default_at_int_spec(
                            m@,
                            vertex_positions,
                            fi,
                            d,
                        ) == p1);
                        assert(vcad_math::orientation3::is_coplanar(p0, p1, p2, p1));
                    } else {
                        assert(d == 2);
                        assert(mesh_face_cycle_vertex_position_or_default_at_int_spec(
                            m@,
                            vertex_positions,
                            fi,
                            d,
                        ) == p2);
                        assert(vcad_math::orientation3::is_coplanar(p0, p1, p2, p2));
                    }
                };
            };
        }

        while h != h0
            invariant
                hcnt == m.half_edges.len(),
                steps <= hcnt,
                0 <= (steps as int) && (steps as int) <= k,
                mesh_index_bounds_spec(m@),
                mesh_runtime_geometry_bridge_spec(m),
                mesh_face_cycle_witness_spec(m@, fi, k),
                start == h0 as int,
                h == mesh_next_iter_spec(m@, start, steps as nat) as usize,
                p0 == a@,
                p1 == b@,
                p2 == c@,
                forall|d: int|
                    0 <= d < (steps as int)
                        ==> #[trigger] vcad_math::orientation3::is_coplanar(
                            p0,
                            p1,
                            p2,
                            mesh_face_cycle_vertex_position_or_default_at_int_spec(
                                m@,
                                vertex_positions,
                                fi,
                                d,
                            ),
                        ),
        {
            proof {
                assert((steps as int) <= k);
                if (steps as int) == k {
                    assert(mesh_next_iter_spec(m@, start, k as nat) == start);
                    assert(h as int == mesh_next_iter_spec(m@, start, steps as nat));
                    assert(h as int == start);
                    assert(h == h0);
                    assert(false);
                }
                assert((steps as int) < k);
            }

            let d = &m.vertices[m.half_edges[h].vertex].position;
            let cop = vcad_geometry::collinearity_coplanarity::coplanar(a, b, c, d);
            if !cop {
                return false;
            }

            proof {
                let di = steps as int;
                let hp = mesh_next_iter_spec(m@, start, steps as nat);
                assert(h as int == hp);
                assert(0 <= hp < mesh_half_edge_count_spec(m@));
                assert(0 <= m@.half_edges[hp].vertex < mesh_vertex_count_spec(m@));
                assert(mesh_face_cycle_vertex_index_or_default_spec(m@, fi, steps as nat)
                    == m@.half_edges[hp].vertex);
                assert(mesh_face_cycle_vertex_position_or_default_at_int_spec(
                    m@,
                    vertex_positions,
                    fi,
                    di,
                ) == vertex_positions[m@.half_edges[hp].vertex]);
                assert(vertex_positions[m@.half_edges[hp].vertex]
                    == m.vertices@[m@.half_edges[hp].vertex].position@);
                assert(d@ == m.vertices@[m@.half_edges[hp].vertex].position@);
                assert(d@
                    == mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m@,
                        vertex_positions,
                        fi,
                        di,
                    ));
                assert(cop == vcad_math::orientation3::is_coplanar(a@, b@, c@, d@));
                assert(vcad_math::orientation3::is_coplanar(
                    p0,
                    p1,
                    p2,
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m@,
                        vertex_positions,
                        fi,
                        di,
                    ),
                ));
            }

            let _h_prev = h;
            h = m.half_edges[h].next;
            steps += 1;
            if steps > hcnt {
                return false;
            }

            proof {
                let old_steps = (steps - 1) as int;
                assert(0 <= old_steps < k);
                assert(_h_prev as int == mesh_next_iter_spec(m@, start, old_steps as nat));
                assert(0 <= _h_prev as int);
                assert((_h_prev as int) < mesh_half_edge_count_spec(m@));
                assert(
                    mesh_next_or_self_spec(m@, _h_prev as int)
                        == m@.half_edges[(_h_prev as int)].next
                );
                assert(mesh_next_iter_spec(m@, start, steps as nat)
                    == mesh_next_or_self_spec(m@, mesh_next_iter_spec(m@, start, old_steps as nat)));
                assert(h as int == m@.half_edges[(_h_prev as int)].next);
                assert(h as int == mesh_next_iter_spec(m@, start, steps as nat));

                assert(forall|d: int|
                    0 <= d < (steps as int)
                        ==> #[trigger] vcad_math::orientation3::is_coplanar(
                            p0,
                            p1,
                            p2,
                            mesh_face_cycle_vertex_position_or_default_at_int_spec(
                                m@,
                                vertex_positions,
                                fi,
                                d,
                            ),
                        )) by {
                assert forall|d: int|
                    0 <= d < (steps as int)
                        implies #[trigger] vcad_math::orientation3::is_coplanar(
                            p0,
                            p1,
                                p2,
                                mesh_face_cycle_vertex_position_or_default_at_int_spec(
                                    m@,
                                    vertex_positions,
                                    fi,
                                    d,
                                ),
                            ) by {
                        if d < old_steps {
                        } else {
                            assert(d == old_steps);
                            assert(vcad_math::orientation3::is_coplanar(
                                p0,
                                p1,
                                p2,
                                mesh_face_cycle_vertex_position_or_default_at_int_spec(
                                    m@,
                                    vertex_positions,
                                    fi,
                                    d,
                                ),
                            ));
                        }
                    };
                };

                assert((steps as int) <= k) by {
                    assert(old_steps < k);
                };
            }
        }

        proof {
            assert(h == h0);
            assert(steps > 0);
            assert(h as int == mesh_next_iter_spec(m@, start, steps as nat));
            assert(h as int == start);
            assert((steps as int) <= k);
            if (steps as int) < k {
                assert(0 <= 0 < k);
                assert(0 <= (steps as int) < k);
                assert(mesh_next_iter_spec(m@, start, 0) == start);
                assert(mesh_next_iter_spec(m@, start, steps as nat) == start);
                assert(mesh_next_iter_spec(m@, start, 0) == mesh_next_iter_spec(
                    m@,
                    start,
                    steps as nat,
                ));
                assert(0 < (steps as int));
                assert(false);
            }
            assert((steps as int) == k);
            assert(forall|d: int|
                0 <= d < k
                    ==> #[trigger] vcad_math::orientation3::is_coplanar(
                        p0,
                        p1,
                        p2,
                        mesh_face_cycle_vertex_position_or_default_at_int_spec(
                            m@,
                            vertex_positions,
                            fi,
                            d,
                        ),
                    )) by {
                assert forall|d: int|
                    0 <= d < k
                        implies #[trigger] vcad_math::orientation3::is_coplanar(
                            p0,
                            p1,
                            p2,
                            mesh_face_cycle_vertex_position_or_default_at_int_spec(
                                m@,
                                vertex_positions,
                                fi,
                                d,
                            ),
                    ) by {
                    assert(0 <= d < (steps as int));
                };
            };
            assert(mesh_face_coplanar_fixed_seed_witness_spec(m@, vertex_positions, fi, k, 0));
            assert(mesh_face_coplanar_seed0_fixed_witness_spec(m@, vertex_positions, fi)) by {
                let kw = k;
                assert(mesh_face_coplanar_fixed_seed_witness_spec(m@, vertex_positions, fi, kw, 0));
            };
            assert(forall|fp: int|
                0 <= fp < (f + 1) as int
                    ==> #[trigger] mesh_face_coplanar_seed0_fixed_witness_spec(
                        m@,
                        vertex_positions,
                        fp,
                    )) by {
                assert forall|fp: int|
                    0 <= fp < (f + 1) as int
                        implies #[trigger] mesh_face_coplanar_seed0_fixed_witness_spec(
                            m@,
                            vertex_positions,
                            fp,
                        ) by {
                    if fp < f as int {
                    } else {
                        assert(fp == fi);
                        assert(mesh_face_coplanar_seed0_fixed_witness_spec(m@, vertex_positions, fi));
                    }
                };
            };
        }

        f += 1;
    }

    proof {
        lemma_usize_loop_exit_eq(f, fcnt);
        assert(f == fcnt);
        assert(mesh_runtime_geometry_bridge_spec(m));
        assert(mesh_geometry_input_spec(m@, vertex_positions));
        assert(face_cycle_lens.len() == fcnt as int);
        assert(forall|fp: int|
            0 <= fp < mesh_face_count_spec(m@)
                ==> #[trigger] mesh_face_coplanar_seed0_fixed_witness_spec(
                    m@,
                    vertex_positions,
                    fp,
                )) by {
            assert forall|fp: int|
                0 <= fp < mesh_face_count_spec(m@)
                    implies #[trigger] mesh_face_coplanar_seed0_fixed_witness_spec(
                        m@,
                        vertex_positions,
                        fp,
                    ) by {
                assert(mesh_face_count_spec(m@) == face_cycle_lens.len());
                assert(face_cycle_lens.len() == fcnt as int);
                assert(0 <= fp < f as int);
            };
        };
        assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_and_face_next_cycles_witness_imply_all_faces_seed0_fixed_witness_at_cycle_lens(
            m,
            face_cycle_lens,
        );
        assert(exists|face_cycle_lens0: Seq<usize>| {
            &&& mesh_face_next_cycles_witness_spec(m@, face_cycle_lens0)
            &&& forall|f: int|
                0 <= f < mesh_face_count_spec(m@)
                    ==> #[trigger] mesh_face_coplanar_fixed_seed_witness_spec(
                        m@,
                        mesh_runtime_vertex_positions_spec(m),
                        f,
                        face_cycle_lens0[f] as int,
                        0,
                    )
        }) by {
            let face_cycle_lens0 = face_cycle_lens;
            assert(mesh_face_next_cycles_witness_spec(m@, face_cycle_lens0));
            assert(forall|f: int|
                0 <= f < mesh_face_count_spec(m@)
                    ==> #[trigger] mesh_face_coplanar_fixed_seed_witness_spec(
                        m@,
                        mesh_runtime_vertex_positions_spec(m),
                        f,
                        face_cycle_lens0[f] as int,
                        0,
                    ));
        };
        lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_implies_all_faces_seed0_plane_contains_vertices(
            m,
        );
        assert(mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
        assert(seed0_corner_non_collinearity_ok);
        assert(seed0_corner_non_collinearity_ok ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_and_seed0_non_collinear_imply_all_faces_oriented_seed0_planes(
            m,
        );
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
    }

    true
}

#[cfg(feature = "geometry-checks")]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_sound_bridge(
    m: &Mesh,
) -> (out: bool)
    ensures
        out ==> mesh_valid_spec(m@),
        out ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        out ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        out ==> mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        out ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    let runtime_ok = m.check_face_coplanarity();
    if !runtime_ok {
        return false;
    }

    let bridge_ok = runtime_check_face_coplanarity_seed0_fixed_witness_bridge(m);
    if !bridge_ok {
        return false;
    }

    let validity_w = match is_valid_constructive(m) {
        Option::Some(w) => w,
        Option::None => return false,
    };
    if !validity_w.api_ok {
        return false;
    }

    proof {
        assert(validity_gate_witness_spec(validity_w));
        assert(validity_gate_model_link_spec(m@, validity_w));
        lemma_validity_gate_witness_api_ok_implies_mesh_valid(m@, validity_w);
        assert(mesh_valid_spec(m@));

        assert(bridge_ok ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        assert(bridge_ok ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        assert(bridge_ok ==> mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
        assert(bridge_ok ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
        assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        assert(mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
    }

    true
}

#[cfg(feature = "geometry-checks")]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_triangle_or_quad_sound_bridge(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_runtime_all_faces_triangle_or_quad_cycles_spec(m),
    ensures
        out ==> mesh_valid_spec(m@),
        out ==> mesh_runtime_all_faces_coplanar_spec(m),
        out ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        out ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        out ==> mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        out ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    let seed0_sound_ok = runtime_check_face_coplanarity_seed0_fixed_witness_sound_bridge(m);
    if !seed0_sound_ok {
        return false;
    }

    proof {
        assert(seed0_sound_ok ==> mesh_valid_spec(m@));
        assert(seed0_sound_ok ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        assert(seed0_sound_ok ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        assert(seed0_sound_ok ==> mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
        assert(seed0_sound_ok ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m));

        assert(mesh_valid_spec(m@));
        assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        assert(mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));

        assert(mesh_runtime_all_faces_triangle_or_quad_cycles_spec(m));
        lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_and_triangle_or_quad_cycles_imply_all_faces_coplanar(
            m,
        );
        assert(mesh_runtime_all_faces_coplanar_spec(m));
    }

    true
}

#[cfg(feature = "geometry-checks")]
#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_triangle_or_quad_sound_complete_bridge(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_runtime_all_faces_triangle_or_quad_cycles_spec(m),
    ensures
        out == m.check_face_coplanarity(),
        out ==> mesh_valid_spec(m@),
        out ==> mesh_runtime_all_faces_coplanar_spec(m),
        out ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        out ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        out ==> mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        out ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    let sound_ok = runtime_check_face_coplanarity_seed0_fixed_witness_triangle_or_quad_sound_bridge(m);
    if !sound_ok {
        return false;
    }

    proof {
        assert(sound_ok ==> mesh_valid_spec(m@));
        assert(sound_ok ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
        assert(sound_ok);
        assert(mesh_valid_spec(m@));
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
    }

    let runtime_sound_complete_ok =
        runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_sound_complete_bridge(
            m,
        );

    proof {
        assert(runtime_sound_complete_ok == m.check_face_coplanarity());
        assert(sound_ok ==> mesh_valid_spec(m@));
        assert(sound_ok ==> mesh_runtime_all_faces_coplanar_spec(m));
        assert(sound_ok ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        assert(sound_ok ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        assert(sound_ok ==> mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
        assert(sound_ok ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
        assert(runtime_sound_complete_ok ==> mesh_valid_spec(m@)) by {
            if runtime_sound_complete_ok {
                assert(sound_ok);
                assert(mesh_valid_spec(m@));
            }
        };
        assert(runtime_sound_complete_ok ==> mesh_runtime_all_faces_coplanar_spec(m)) by {
            if runtime_sound_complete_ok {
                assert(sound_ok);
                assert(mesh_runtime_all_faces_coplanar_spec(m));
            }
        };
        assert(runtime_sound_complete_ok ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m)) by {
            if runtime_sound_complete_ok {
                assert(sound_ok);
                assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
            }
        };
        assert(runtime_sound_complete_ok ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)) by {
            if runtime_sound_complete_ok {
                assert(sound_ok);
                assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
            }
        };
        assert(runtime_sound_complete_ok ==> mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m)) by {
            if runtime_sound_complete_ok {
                assert(sound_ok);
                assert(mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
            }
        };
        assert(runtime_sound_complete_ok ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m)) by {
            if runtime_sound_complete_ok {
                assert(sound_ok);
                assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
            }
        };
    }

    runtime_sound_complete_ok
}

#[cfg(feature = "geometry-checks")]
#[allow(dead_code)]
pub fn runtime_check_face_convexity_triangle_projected_turn_sound_bridge(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_runtime_all_faces_triangle_cycles_spec(m),
    ensures
        out ==> mesh_valid_spec(m@),
        out ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        out ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        out ==> mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        out ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
        out ==> mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m),
{
    let runtime_ok = m.check_face_convexity();
    if !runtime_ok {
        return false;
    }

    let coplanarity_bridge_ok = runtime_check_face_coplanarity_seed0_fixed_witness_sound_bridge(m);
    if !coplanarity_bridge_ok {
        return false;
    }

    proof {
        assert(coplanarity_bridge_ok ==> mesh_valid_spec(m@));
        assert(coplanarity_bridge_ok ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        assert(coplanarity_bridge_ok ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        assert(coplanarity_bridge_ok ==> mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
        assert(coplanarity_bridge_ok ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
        assert(mesh_valid_spec(m@));
        assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        assert(mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
        assert(mesh_runtime_all_faces_triangle_cycles_spec(m));
        lemma_mesh_runtime_all_faces_seed0_corner_non_collinear_and_triangle_cycles_imply_all_faces_projected_turn_sign_consistency(
            m,
        );
        assert(mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m));
    }

    true
}

#[cfg(feature = "geometry-checks")]
#[allow(dead_code)]
pub fn runtime_check_face_convexity_triangle_projected_turn_complete_from_runtime_with_geometry_preconditions(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_runtime_geometric_topological_consistency_with_geometry_spec(m),
        mesh_runtime_all_faces_triangle_cycles_spec(m),
    ensures
        out,
        mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m),
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
        mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m),
{
    let _coplanarity_complete_ok =
        runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_runtime_with_geometry_preconditions(
            m,
        );

    proof {
        assert(_coplanarity_complete_ok);
        assert(mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m));
        assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        assert(mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
        assert(mesh_runtime_geometric_topological_consistency_with_geometry_spec(m));
        assert(mesh_runtime_all_faces_triangle_cycles_spec(m));
        lemma_mesh_runtime_geometric_topological_consistency_with_geometry_and_triangle_cycles_imply_all_faces_projected_turn_sign_consistency(
            m,
        );
        assert(mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m));
    }

    true
}

#[cfg(feature = "geometry-checks")]
#[allow(dead_code)]
pub fn runtime_check_face_convexity_triangle_projected_turn_complete_from_runtime_with_geometry_and_non_zero_edges_preconditions(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_runtime_geometric_topological_consistency_with_geometry_and_non_zero_edges_spec(m),
        mesh_runtime_all_faces_triangle_cycles_spec(m),
    ensures
        out,
        mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m),
        mesh_runtime_geometric_topological_consistency_with_geometry_spec(m),
        mesh_runtime_geometric_topological_consistency_with_geometry_and_non_zero_edges_spec(m),
        mesh_runtime_all_half_edges_non_zero_geometric_length_spec(m),
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
        mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m),
{
    let out0 =
        runtime_check_face_convexity_triangle_projected_turn_complete_from_runtime_with_geometry_preconditions(
            m,
        );

    proof {
        assert(out0);
        assert(mesh_runtime_geometric_topological_consistency_with_geometry_and_non_zero_edges_spec(m));
        assert(mesh_runtime_geometric_topological_consistency_with_geometry_spec(m));
        assert(mesh_runtime_all_half_edges_non_zero_geometric_length_spec(m));
        assert(mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m));
        assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        assert(mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
        assert(mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m));
    }

    out0
}

#[cfg(feature = "geometry-checks")]
#[allow(dead_code)]
pub fn runtime_check_face_convexity_triangle_projected_turn_complete_from_phase5_runtime_bundle_preconditions(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m),
        mesh_runtime_all_faces_triangle_cycles_spec(m),
    ensures
        out,
        mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m),
        mesh_runtime_geometric_topological_consistency_with_geometry_spec(m),
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
        mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m),
{
    proof {
        lemma_mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_implies_mesh_geometric_topological_consistency_with_geometry(
            m,
        );
        assert(mesh_runtime_geometric_topological_consistency_with_geometry_spec(m));
    }
    runtime_check_face_convexity_triangle_projected_turn_complete_from_runtime_with_geometry_preconditions(
        m,
    )
}

#[cfg(feature = "geometry-checks")]
#[allow(dead_code)]
pub fn runtime_check_face_convexity_triangle_projected_turn_complete_from_phase5_runtime_bundle_sound_bridge(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_runtime_all_faces_triangle_cycles_spec(m),
    ensures
        out == runtime_check_geometric_topological_consistency_sound_bridge(m),
        out ==> mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m),
        out ==> mesh_runtime_geometric_topological_consistency_with_geometry_spec(m),
        out ==> mesh_runtime_geometric_topological_consistency_with_geometry_and_non_zero_edges_spec(m),
        out ==> mesh_runtime_all_half_edges_non_zero_geometric_length_spec(m),
        out ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        out ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        out ==> mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        out ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
        out ==> mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m),
        out ==> (
            mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m)
                == mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
        ),
{
    let geometric_sound_ok = runtime_check_geometric_topological_consistency_sound_bridge(m);
    if !geometric_sound_ok {
        return false;
    }

    let _complete_ok =
        runtime_check_face_convexity_triangle_projected_turn_complete_from_runtime_with_geometry_and_non_zero_edges_preconditions(
            m,
        );

    proof {
        assert(_complete_ok);
        assert(
            geometric_sound_ok
                ==> mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m)
        );
        assert(geometric_sound_ok ==> mesh_runtime_geometric_topological_consistency_with_geometry_spec(m));
        assert(
            geometric_sound_ok
                ==> mesh_runtime_geometric_topological_consistency_with_geometry_and_non_zero_edges_spec(
                    m,
                )
        );
        assert(mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m));
        assert(mesh_runtime_geometric_topological_consistency_with_geometry_spec(m));
        assert(mesh_runtime_geometric_topological_consistency_with_geometry_and_non_zero_edges_spec(m));
        assert(mesh_runtime_all_half_edges_non_zero_geometric_length_spec(m));
        assert(_complete_ok);
        assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        assert(mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
        assert(mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m));
        assert(mesh_runtime_all_faces_triangle_cycles_spec(m));
        lemma_mesh_runtime_geometric_topological_consistency_with_geometry_and_non_zero_edges_and_triangle_cycles_projected_turn_sign_consistency_iff_seed0_corner_non_collinear(
            m,
        );
        assert(
            mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m)
                == mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
        );
    }

    geometric_sound_ok
}

#[cfg(feature = "geometry-checks")]
#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
#[allow(unused_variables)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_complete_under_preconditions(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_index_bounds_spec(m@),
        mesh_face_next_cycles_spec(m@),
        mesh_runtime_geometry_bridge_spec(m),
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
    ensures
        out,
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    let fcnt = m.faces.len();
    let hcnt = m.half_edges.len();

    let ghost face_cycle_lens = choose|face_cycle_lens: Seq<usize>| mesh_face_next_cycles_witness_spec(
        m@,
        face_cycle_lens,
    );
    let ghost vertex_positions = mesh_runtime_vertex_positions_spec(m);

    proof {
        assert(mesh_face_next_cycles_witness_spec(m@, face_cycle_lens));
        assert(mesh_runtime_geometry_bridge_spec(m));
        assert(mesh_geometry_input_spec(m@, vertex_positions));
        assert(face_cycle_lens.len() == mesh_face_count_spec(m@));
        assert(mesh_face_count_spec(m@) == m@.face_half_edges.len() as int);
        assert(m@.face_half_edges.len() == m.faces@.len());
        assert(m.faces@.len() == m.faces.len());
        assert(face_cycle_lens.len() == fcnt as int);
        lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_and_face_next_cycles_witness_imply_all_faces_seed0_fixed_witness_at_cycle_lens(
            m,
            face_cycle_lens,
        );
        assert(forall|f: int|
            0 <= f < mesh_face_count_spec(m@)
                ==> #[trigger] mesh_face_coplanar_fixed_seed_witness_spec(
                    m@,
                    vertex_positions,
                    f,
                    face_cycle_lens[f] as int,
                    0,
                ));
    }

    let mut f: usize = 0;
    while f < fcnt
        invariant
            fcnt == m.faces.len(),
            hcnt == m.half_edges.len(),
            face_cycle_lens.len() == fcnt as int,
            f <= fcnt,
            mesh_index_bounds_spec(m@),
            mesh_face_next_cycles_witness_spec(m@, face_cycle_lens),
            mesh_runtime_geometry_bridge_spec(m),
            mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
            mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
            forall|fp: int|
                0 <= fp < mesh_face_count_spec(m@)
                    ==> #[trigger] mesh_face_coplanar_fixed_seed_witness_spec(
                        m@,
                        vertex_positions,
                        fp,
                        face_cycle_lens[fp] as int,
                        0,
                    ),
    {
        let h0 = m.faces[f].half_edge;
        let h1 = m.half_edges[h0].next;
        let h2 = m.half_edges[h1].next;

        let a = &m.vertices[m.half_edges[h0].vertex].position;
        let b = &m.vertices[m.half_edges[h1].vertex].position;
        let c = &m.vertices[m.half_edges[h2].vertex].position;

        let ghost fi = f as int;
        let ghost k = face_cycle_lens[fi] as int;
        let ghost start = m@.face_half_edges[fi];
        let ghost p0 = mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m@,
            vertex_positions,
            fi,
            0,
        );
        let ghost p1 = mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m@,
            vertex_positions,
            fi,
            1,
        );
        let ghost p2 = mesh_face_cycle_vertex_position_or_default_at_int_spec(
            m@,
            vertex_positions,
            fi,
            2,
        );

        proof {
            assert(0 <= fi < face_cycle_lens.len());
            assert(mesh_face_coplanar_fixed_seed_witness_spec(m@, vertex_positions, fi, k, 0));
            assert(mesh_face_cycle_witness_spec(m@, fi, k));
            assert(3 <= k);
            assert(k <= hcnt as int);
            assert(start == h0 as int);
            assert(0 <= start < mesh_half_edge_count_spec(m@));
            assert(mesh_next_iter_spec(m@, start, 0) == start);
            assert(mesh_next_iter_spec(m@, start, 1) == mesh_next_or_self_spec(m@, start));
            assert(mesh_next_or_self_spec(m@, start) == m@.half_edges[start].next);
            assert(m@.half_edges[start].next == h1 as int);
            assert(mesh_next_iter_spec(m@, start, 1) == h1 as int);
            assert(mesh_next_iter_spec(m@, start, 2) == mesh_next_or_self_spec(
                m@,
                mesh_next_iter_spec(m@, start, 1),
            ));
            assert(mesh_next_or_self_spec(m@, mesh_next_iter_spec(m@, start, 1))
                == m@.half_edges[mesh_next_iter_spec(m@, start, 1)].next);
            assert(mesh_next_iter_spec(m@, start, 2) == h2 as int);

            assert(p0 == a@);
            assert(p1 == b@);
            assert(p2 == c@);
        }

        let mut h: usize = m.half_edges[h2].next;
        let mut steps: usize = 3;

        proof {
            assert(mesh_next_iter_spec(m@, start, 3) == mesh_next_or_self_spec(
                m@,
                mesh_next_iter_spec(m@, start, 2),
            ));
            assert(mesh_next_or_self_spec(m@, mesh_next_iter_spec(m@, start, 2))
                == m@.half_edges[mesh_next_iter_spec(m@, start, 2)].next);
            assert(mesh_next_iter_spec(m@, start, 2) == h2 as int);
            assert(m@.half_edges[h2 as int].next == h as int);
            assert(h as int == mesh_next_iter_spec(m@, start, 3));
            assert((steps as int) == 3);
            assert((steps as int) <= k);
            assert(steps <= hcnt);
        }

        while h != h0
            invariant
                hcnt == m.half_edges.len(),
                steps <= hcnt,
                0 <= (steps as int) && (steps as int) <= k,
                mesh_index_bounds_spec(m@),
                mesh_runtime_geometry_bridge_spec(m),
                mesh_face_cycle_witness_spec(m@, fi, k),
                mesh_face_coplanar_fixed_seed_witness_spec(m@, vertex_positions, fi, k, 0),
                start == h0 as int,
                h == mesh_next_iter_spec(m@, start, steps as nat) as usize,
                p0 == a@,
                p1 == b@,
                p2 == c@,
        {
            proof {
                assert((steps as int) <= k);
                if (steps as int) == k {
                    assert(mesh_next_iter_spec(m@, start, k as nat) == start);
                    assert(h as int == mesh_next_iter_spec(m@, start, steps as nat));
                    assert(h as int == start);
                    assert(h == h0);
                    assert(false);
                }
                assert((steps as int) < k);
            }

            let d = &m.vertices[m.half_edges[h].vertex].position;
            let cop = vcad_geometry::collinearity_coplanarity::coplanar(a, b, c, d);
            proof {
                let di = steps as int;
                let hp = mesh_next_iter_spec(m@, start, steps as nat);
                assert(h as int == hp);
                assert(0 <= hp < mesh_half_edge_count_spec(m@));
                assert(0 <= m@.half_edges[hp].vertex < mesh_vertex_count_spec(m@));
                assert(mesh_face_cycle_vertex_index_or_default_spec(m@, fi, steps as nat)
                    == m@.half_edges[hp].vertex);
                assert(mesh_face_cycle_vertex_position_or_default_at_int_spec(
                    m@,
                    vertex_positions,
                    fi,
                    di,
                ) == vertex_positions[m@.half_edges[hp].vertex]);
                assert(vertex_positions[m@.half_edges[hp].vertex]
                    == m.vertices@[m@.half_edges[hp].vertex].position@);
                assert(d@ == m.vertices@[m@.half_edges[hp].vertex].position@);
                assert(d@
                    == mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m@,
                        vertex_positions,
                        fi,
                        di,
                    ));
                assert(0 <= di < k);
                assert(vcad_math::orientation3::is_coplanar(
                    p0,
                    p1,
                    p2,
                    mesh_face_cycle_vertex_position_or_default_at_int_spec(
                        m@,
                        vertex_positions,
                        fi,
                        di,
                    ),
                ));
                assert(cop == vcad_math::orientation3::is_coplanar(a@, b@, c@, d@));
                assert(cop);
            }
            if !cop {
                return false;
            }

            let h_prev = h;
            h = m.half_edges[h].next;
            steps += 1;

            proof {
                let old_steps = (steps - 1) as int;
                assert(0 <= old_steps < k);
                assert(h_prev as int == mesh_next_iter_spec(m@, start, old_steps as nat));
                assert(0 <= h_prev as int);
                assert((h_prev as int) < mesh_half_edge_count_spec(m@));
                assert(
                    mesh_next_or_self_spec(m@, h_prev as int) == m@.half_edges[h_prev as int].next
                );
                assert(mesh_next_iter_spec(m@, start, steps as nat)
                    == mesh_next_or_self_spec(m@, mesh_next_iter_spec(m@, start, old_steps as nat)));
                assert(h as int == m@.half_edges[h_prev as int].next);
                assert(h as int == mesh_next_iter_spec(m@, start, steps as nat));
                assert((steps as int) <= k) by {
                    assert(old_steps < k);
                };
                assert(steps <= hcnt) by {
                    assert((steps as int) <= k);
                    assert(k <= hcnt as int);
                };
            }
        }

        proof {
            assert(h == h0);
            assert(h as int == mesh_next_iter_spec(m@, start, steps as nat));
            assert(h as int == start);
            assert((steps as int) <= k);
            if (steps as int) < k {
                assert(0 <= 0 < k);
                assert(0 <= (steps as int) < k);
                assert(mesh_next_iter_spec(m@, start, 0) == start);
                assert(mesh_next_iter_spec(m@, start, steps as nat) == start);
                assert(mesh_next_iter_spec(m@, start, 0) == mesh_next_iter_spec(
                    m@,
                    start,
                    steps as nat,
                ));
                assert(0 < (steps as int));
                assert(false);
            }
            assert((steps as int) == k);
        }

        f += 1;
    }

    proof {
        lemma_usize_loop_exit_eq(f, fcnt);
        assert(f == fcnt);
        lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_implies_all_faces_seed0_plane_contains_vertices(
            m,
        );
        assert(mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
        lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_and_seed0_non_collinear_imply_all_faces_oriented_seed0_planes(
            m,
        );
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
    }

    true
}

#[cfg(feature = "geometry-checks")]
#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_full_coplanarity_preconditions(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_index_bounds_spec(m@),
        mesh_face_next_cycles_spec(m@),
        mesh_runtime_geometry_bridge_spec(m),
        mesh_runtime_all_faces_coplanar_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
    ensures
        out,
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    proof {
        lemma_mesh_runtime_all_faces_coplanar_spec_implies_all_faces_seed0_fixed_witness(m);
        assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
    }
    runtime_check_face_coplanarity_seed0_fixed_witness_complete_under_preconditions(m)
}

#[cfg(feature = "geometry-checks")]
#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_full_coplanarity_preconditions(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_valid_spec(m@),
        mesh_runtime_all_faces_coplanar_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
    ensures
        out,
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    proof {
        lemma_mesh_runtime_geometry_bridge_holds(m);
        assert(mesh_runtime_geometry_bridge_spec(m));
        assert(mesh_structurally_valid_spec(m@));
        assert(mesh_index_bounds_spec(m@));
        assert(mesh_face_next_cycles_spec(m@));
    }
    runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_full_coplanarity_preconditions(m)
}

#[cfg(feature = "geometry-checks")]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_full_coplanarity_sound_complete_bridge(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_valid_spec(m@),
        mesh_runtime_all_faces_coplanar_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
    ensures
        out == m.check_face_coplanarity(),
        mesh_runtime_all_faces_coplanar_spec(m),
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    let _complete_ok =
        runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_full_coplanarity_preconditions(
            m,
        );
    let runtime_ok = m.check_face_coplanarity();

    proof {
        assert(_complete_ok);
        assert(mesh_runtime_all_faces_coplanar_spec(m));
        assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        assert(mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
    }

    runtime_ok
}

#[cfg(feature = "geometry-checks")]
#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_preconditions(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_valid_spec(m@),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
    ensures
        out,
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    proof {
        lemma_mesh_runtime_geometry_bridge_holds(m);
        assert(mesh_runtime_geometry_bridge_spec(m));
        assert(mesh_structurally_valid_spec(m@));
        assert(mesh_index_bounds_spec(m@));
        assert(mesh_face_next_cycles_spec(m@));
        lemma_mesh_runtime_all_faces_oriented_seed0_planes_and_index_bounds_and_face_cycles_iff_seed0_fixed_witness_and_seed0_non_collinear(
            m,
        );
        assert(
            mesh_runtime_all_faces_oriented_seed0_planes_spec(m) == (
                mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m)
                    && mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
            )
        );
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
        assert(
            mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m)
                && mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
        );
        assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
    }
    runtime_check_face_coplanarity_seed0_fixed_witness_complete_under_preconditions(m)
}

#[cfg(feature = "geometry-checks")]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_sound_complete_bridge(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_valid_spec(m@),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
    ensures
        out == m.check_face_coplanarity(),
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    let _complete_ok =
        runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_preconditions(
            m,
        );
    let runtime_ok = m.check_face_coplanarity();

    proof {
        assert(_complete_ok);
        assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        assert(mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
    }

    runtime_ok
}

#[cfg(feature = "geometry-checks")]
#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_and_triangle_face_preconditions(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_valid_spec(m@),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
        mesh_runtime_all_faces_triangle_cycles_spec(m),
    ensures
        out,
        mesh_runtime_all_faces_coplanar_spec(m),
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    let out0 =
        runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_preconditions(
            m,
        );
    proof {
        assert(out0);
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
        assert(mesh_runtime_all_faces_triangle_cycles_spec(m));
        lemma_mesh_runtime_all_faces_oriented_seed0_planes_and_triangle_cycles_imply_all_faces_coplanar(
            m,
        );
        assert(mesh_runtime_all_faces_coplanar_spec(m));
    }
    out0
}

#[cfg(feature = "geometry-checks")]
#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_and_triangle_or_quad_face_preconditions(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_valid_spec(m@),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
        mesh_runtime_all_faces_triangle_or_quad_cycles_spec(m),
    ensures
        out,
        mesh_runtime_all_faces_coplanar_spec(m),
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    let out0 =
        runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_preconditions(
            m,
        );
    proof {
        assert(out0);
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
        assert(mesh_runtime_all_faces_triangle_or_quad_cycles_spec(m));
        lemma_mesh_runtime_all_faces_oriented_seed0_planes_and_triangle_or_quad_cycles_imply_all_faces_coplanar(
            m,
        );
        assert(mesh_runtime_all_faces_coplanar_spec(m));
    }
    out0
}

#[cfg(feature = "geometry-checks")]
#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_and_quad_face_preconditions(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_valid_spec(m@),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
        mesh_runtime_all_faces_quad_cycles_spec(m),
    ensures
        out,
        mesh_runtime_all_faces_coplanar_spec(m),
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    let out0 =
        runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_preconditions(
            m,
        );
    proof {
        assert(out0);
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
        assert(mesh_runtime_all_faces_quad_cycles_spec(m));
        lemma_mesh_runtime_all_faces_oriented_seed0_planes_and_quad_cycles_imply_all_faces_coplanar(
            m,
        );
        assert(mesh_runtime_all_faces_coplanar_spec(m));
    }
    out0
}

#[cfg(feature = "geometry-checks")]
#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_triangle_face_preconditions(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_valid_spec(m@),
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        mesh_runtime_all_faces_triangle_cycles_spec(m),
    ensures
        out,
        mesh_runtime_all_faces_coplanar_spec(m),
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    proof {
        assert(mesh_valid_spec(m@));
        assert(mesh_structurally_valid_spec(m@));
        assert(mesh_index_bounds_spec(m@));
        assert(mesh_face_next_cycles_spec(m@));
        lemma_mesh_runtime_geometry_bridge_holds(m);
        assert(mesh_runtime_geometry_bridge_spec(m));
    }

    let out0 = runtime_check_face_coplanarity_seed0_fixed_witness_complete_under_preconditions(m);
    proof {
        assert(out0);
        assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        assert(mesh_runtime_all_faces_triangle_cycles_spec(m));
        lemma_mesh_runtime_all_faces_coplanar_seed0_fixed_witness_and_triangle_cycles_imply_all_faces_coplanar(
            m,
        );
        assert(mesh_runtime_all_faces_coplanar_spec(m));
    }
    out0
}

#[cfg(feature = "geometry-checks")]
#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_phase5_runtime_bundle_preconditions(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m),
    ensures
        out,
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    proof {
        assert(mesh_valid_spec(m@));
        assert(mesh_structurally_valid_spec(m@));
        assert(mesh_index_bounds_spec(m@));
        assert(mesh_face_next_cycles_spec(m@));
        assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        lemma_mesh_runtime_geometry_bridge_holds(m);
        assert(mesh_runtime_geometry_bridge_spec(m));
    }
    runtime_check_face_coplanarity_seed0_fixed_witness_complete_under_preconditions(m)
}

#[cfg(feature = "geometry-checks")]
#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_phase5_runtime_bundle_and_full_coplanarity_preconditions(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m),
        mesh_runtime_all_faces_coplanar_spec(m),
    ensures
        out,
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_phase5_runtime_bundle_preconditions(m)
}

#[cfg(feature = "geometry-checks")]
#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_runtime_with_geometry_preconditions(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_runtime_geometric_topological_consistency_with_geometry_spec(m),
    ensures
        out,
        mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m),
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    proof {
        lemma_mesh_runtime_geometric_topological_consistency_with_geometry_implies_mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle(
            m,
        );
        assert(mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m));
    }
    runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_phase5_runtime_bundle_preconditions(m)
}

#[cfg(feature = "geometry-checks")]
#[verifier::exec_allows_no_decreases_clause]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_runtime_with_geometry_and_triangle_or_quad_face_preconditions(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_runtime_geometric_topological_consistency_with_geometry_spec(m),
        mesh_runtime_all_faces_triangle_or_quad_cycles_spec(m),
    ensures
        out,
        mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m),
        mesh_runtime_all_faces_coplanar_spec(m),
        mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    let _out0 =
        runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_runtime_with_geometry_preconditions(
            m,
        );

    proof {
        assert(_out0);
        assert(mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m));
        assert(mesh_valid_spec(m@));
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
    }

    let out1 =
        runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_validity_and_oriented_seed0_plane_and_triangle_or_quad_face_preconditions(
            m,
        );

    proof {
        assert(out1);
        assert(mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m));
        assert(mesh_runtime_all_faces_coplanar_spec(m));
        assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        assert(mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
    }

    out1
}

#[cfg(feature = "geometry-checks")]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_phase5_runtime_bundle_sound_bridge(
    m: &Mesh,
) -> (out: bool)
    ensures
        out == runtime_check_geometric_topological_consistency_sound_bridge(m),
        out ==> mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m),
        out ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        out ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        out ==> mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        out ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    let phase5_sound_ok = runtime_check_geometric_topological_consistency_sound_bridge(m);
    if !phase5_sound_ok {
        return false;
    }

    let _complete_ok =
        runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_phase5_runtime_bundle_preconditions(
            m,
        );

    proof {
        assert(_complete_ok);
        assert(phase5_sound_ok ==> mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m));
        assert(mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m));
        assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        assert(mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
    }

    phase5_sound_ok
}

#[cfg(feature = "geometry-checks")]
#[allow(dead_code)]
pub fn runtime_check_face_coplanarity_seed0_fixed_witness_triangle_or_quad_complete_from_phase5_runtime_bundle_sound_bridge(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_runtime_all_faces_triangle_or_quad_cycles_spec(m),
    ensures
        out == runtime_check_geometric_topological_consistency_sound_bridge(m),
        out ==> mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m),
        out ==> mesh_runtime_geometric_topological_consistency_with_geometry_spec(m),
        out ==> mesh_runtime_all_faces_coplanar_spec(m),
        out ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m),
        out ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        out ==> mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m),
        out ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m),
{
    let phase5_sound_ok = runtime_check_geometric_topological_consistency_sound_bridge(m);
    if !phase5_sound_ok {
        return false;
    }

    let _complete_ok =
        runtime_check_face_coplanarity_seed0_fixed_witness_complete_from_runtime_with_geometry_and_triangle_or_quad_face_preconditions(
            m,
        );

    proof {
        assert(_complete_ok);
        assert(
            phase5_sound_ok
                ==> mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m)
        );
        assert(phase5_sound_ok ==> mesh_runtime_geometric_topological_consistency_with_geometry_spec(m));
        assert(mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m));
        assert(mesh_runtime_geometric_topological_consistency_with_geometry_spec(m));
        assert(mesh_runtime_all_faces_coplanar_spec(m));
        assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
        assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        assert(mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
        assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
    }

    phase5_sound_ok
}

#[cfg(feature = "geometry-checks")]
#[allow(dead_code)]
pub fn runtime_check_geometric_topological_consistency_triangle_or_quad_coplanarity_sound_bridge(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_runtime_all_faces_triangle_or_quad_cycles_spec(m),
    ensures
        out == runtime_check_geometric_topological_consistency_sound_bridge(m),
        out ==> mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m),
        out ==> mesh_runtime_geometric_topological_consistency_with_geometry_spec(m),
        out ==> mesh_runtime_all_faces_coplanar_spec(m),
{
    let geometric_sound_ok = runtime_check_geometric_topological_consistency_sound_bridge(m);
    if !geometric_sound_ok {
        return false;
    }

    proof {
        assert(
            geometric_sound_ok
                ==> mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m)
        );
        assert(geometric_sound_ok ==> mesh_runtime_geometric_topological_consistency_with_geometry_spec(m));
        assert(
            geometric_sound_ok
                && mesh_runtime_all_faces_triangle_or_quad_cycles_spec(m)
                ==> mesh_runtime_all_faces_coplanar_spec(m)
        );
        assert(mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m));
        assert(mesh_runtime_geometric_topological_consistency_with_geometry_spec(m));
        assert(mesh_runtime_all_faces_coplanar_spec(m));
    }

    geometric_sound_ok
}

#[cfg(feature = "geometry-checks")]
#[allow(dead_code)]
pub fn check_geometric_topological_consistency_constructive(
    m: &Mesh,
) -> (out: Option<GeometricTopologicalConsistencyGateWitness>)
    ensures
        match out {
            Option::Some(w) => geometric_topological_consistency_gate_witness_spec(w)
                && geometric_topological_consistency_gate_model_link_spec(m@, w)
                && (w.phase4_valid_ok ==> mesh_valid_spec(m@))
                && (w.no_zero_length_geometric_edges_ok
                    ==> mesh_runtime_all_half_edges_non_zero_geometric_length_spec(m))
                && (w.face_corner_non_collinearity_ok
                    ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m))
                && (w.face_coplanarity_ok ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m))
                && (w.face_coplanarity_ok ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m))
                && (w.face_coplanarity_ok ==> mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m))
                && (w.face_coplanarity_ok ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m))
                && (w.api_ok
                    ==> mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(
                        m,
                    ))
                && (w.api_ok ==> mesh_runtime_geometric_topological_consistency_with_geometry_spec(m))
                && (w.api_ok
                    ==> mesh_runtime_geometric_topological_consistency_with_geometry_and_non_zero_edges_spec(
                        m,
                    ))
                && (w.api_ok
                    && mesh_runtime_all_faces_triangle_cycles_spec(m)
                    ==> mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m))
                && (w.api_ok
                    && mesh_runtime_all_faces_triangle_cycles_spec(m)
                    ==> (
                        mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m)
                            == mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
                    ))
                && (w.api_ok
                    && mesh_runtime_all_faces_triangle_or_quad_cycles_spec(m)
                    ==> mesh_runtime_all_faces_coplanar_spec(m))
                && (w.api_ok ==> mesh_geometric_topological_consistency_spec(m@)),
            Option::None => true,
        },
{
    let validity_w = match is_valid_constructive(m) {
        Option::Some(w) => w,
        Option::None => return Option::None,
    };

    let phase4_valid_ok = validity_w.api_ok;
    let no_zero_length_geometric_edges_runtime_ok = m.check_no_zero_length_geometric_edges();
    let no_zero_length_geometric_edges_bridge_ok =
        runtime_check_no_zero_length_geometric_edges_sound_bridge(m);
    let no_zero_length_geometric_edges_ok = no_zero_length_geometric_edges_runtime_ok
        && no_zero_length_geometric_edges_bridge_ok;
    let face_corner_non_collinearity_runtime_ok = m.check_face_corner_non_collinearity();
    let face_corner_non_collinearity_bridge_ok =
        runtime_check_face_seed0_corner_non_collinearity_bridge(m);
    let face_corner_non_collinearity_ok = face_corner_non_collinearity_runtime_ok
        && face_corner_non_collinearity_bridge_ok;
    let face_coplanarity_runtime_ok = m.check_face_coplanarity();
    let face_coplanarity_bridge_ok = runtime_check_face_coplanarity_seed0_fixed_witness_bridge(m);
    let face_coplanarity_ok = face_coplanarity_runtime_ok && face_coplanarity_bridge_ok;
    let face_convexity_ok = m.check_face_convexity();
    let face_plane_consistency_ok = m.check_face_plane_consistency();
    let shared_edge_local_orientation_runtime_ok = m.check_shared_edge_local_orientation_consistency();
    let shared_edge_local_orientation_bridge_ok =
        runtime_check_shared_edge_local_orientation_kernel_bridge(m);
    let shared_edge_local_orientation_ok = shared_edge_local_orientation_runtime_ok
        && shared_edge_local_orientation_bridge_ok;
    let no_forbidden_face_face_intersections_ok = m.check_no_forbidden_face_face_intersections();
    let outward_face_normals_ok = m.check_outward_face_normals();

    let api_ok = phase4_valid_ok
        && no_zero_length_geometric_edges_ok
        && face_corner_non_collinearity_ok
        && face_coplanarity_ok
        && face_convexity_ok
        && face_plane_consistency_ok
        && shared_edge_local_orientation_ok
        && no_forbidden_face_face_intersections_ok
        && outward_face_normals_ok;

    let w = GeometricTopologicalConsistencyGateWitness {
        api_ok,
        phase4_valid_ok,
        no_zero_length_geometric_edges_ok,
        face_corner_non_collinearity_ok,
        face_coplanarity_ok,
        face_convexity_ok,
        face_plane_consistency_ok,
        shared_edge_local_orientation_ok,
        no_forbidden_face_face_intersections_ok,
        outward_face_normals_ok,
    };

    proof {
        assert(validity_gate_witness_spec(validity_w));
        assert(validity_gate_model_link_spec(m@, validity_w));
        assert(geometric_topological_consistency_gate_witness_spec(w));
        assert(w.no_zero_length_geometric_edges_ok == no_zero_length_geometric_edges_ok);
        assert(no_zero_length_geometric_edges_ok
            == (no_zero_length_geometric_edges_runtime_ok && no_zero_length_geometric_edges_bridge_ok));
        assert(w.face_corner_non_collinearity_ok == face_corner_non_collinearity_ok);
        assert(face_corner_non_collinearity_ok
            == (face_corner_non_collinearity_runtime_ok && face_corner_non_collinearity_bridge_ok));
        assert(w.face_coplanarity_ok == face_coplanarity_ok);
        assert(face_coplanarity_ok == (face_coplanarity_runtime_ok && face_coplanarity_bridge_ok));
        if w.phase4_valid_ok {
            lemma_validity_gate_witness_api_ok_implies_mesh_valid(m@, validity_w);
            assert(mesh_valid_spec(m@));
        }
        if w.no_zero_length_geometric_edges_ok {
            assert(no_zero_length_geometric_edges_bridge_ok);
            assert(mesh_runtime_all_half_edges_non_zero_geometric_length_spec(m));
        }
        if w.face_corner_non_collinearity_ok {
            assert(face_corner_non_collinearity_bridge_ok);
            assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        }
        if w.face_coplanarity_ok {
            assert(face_coplanarity_bridge_ok);
            assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
            assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
            assert(mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
            assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
        }
        if w.shared_edge_local_orientation_ok {
            assert(shared_edge_local_orientation_bridge_ok);
            assert(mesh_shared_edge_local_orientation_consistency_spec(m@));
        }
        if w.api_ok {
            lemma_geometric_topological_consistency_gate_witness_api_ok_implies_mesh_geometric_topological_consistency(
                m@,
                w,
            );
            assert(mesh_geometric_topological_consistency_spec(m@));
        }
        assert(geometric_topological_consistency_gate_model_link_spec(m@, w));
        assert(w.phase4_valid_ok ==> mesh_valid_spec(m@)) by {
            if w.phase4_valid_ok {
                assert(mesh_valid_spec(m@));
            }
        };
        assert(
            w.no_zero_length_geometric_edges_ok
                ==> mesh_runtime_all_half_edges_non_zero_geometric_length_spec(m)
        ) by {
            if w.no_zero_length_geometric_edges_ok {
                assert(no_zero_length_geometric_edges_bridge_ok);
                assert(mesh_runtime_all_half_edges_non_zero_geometric_length_spec(m));
            }
        };
        assert(
            w.face_corner_non_collinearity_ok
                ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
        ) by {
            if w.face_corner_non_collinearity_ok {
                assert(face_corner_non_collinearity_bridge_ok);
                assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
            }
        };
        assert(
            w.face_coplanarity_ok ==> mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m)
        ) by {
            if w.face_coplanarity_ok {
                assert(face_coplanarity_bridge_ok);
                assert(mesh_runtime_all_faces_coplanar_seed0_fixed_witness_spec(m));
            }
        };
        assert(
            w.face_coplanarity_ok ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
        ) by {
            if w.face_coplanarity_ok {
                assert(face_coplanarity_bridge_ok);
                assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
            }
        };
        assert(
            w.face_coplanarity_ok ==> mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m)
        ) by {
            if w.face_coplanarity_ok {
                assert(face_coplanarity_bridge_ok);
                assert(mesh_runtime_all_faces_seed0_plane_contains_vertices_spec(m));
            }
        };
        assert(
            w.face_coplanarity_ok ==> mesh_runtime_all_faces_oriented_seed0_planes_spec(m)
        ) by {
            if w.face_coplanarity_ok {
                assert(face_coplanarity_bridge_ok);
                assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
            }
        };
        if w.api_ok {
            lemma_geometric_topological_consistency_gate_witness_api_ok_implies_mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle(
                m,
                w,
            );
            assert(mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m));
            lemma_mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_implies_mesh_geometric_topological_consistency_with_geometry(
                m,
            );
            assert(mesh_runtime_geometric_topological_consistency_with_geometry_spec(m));
        }
        assert(
            w.api_ok ==> mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(
                m,
            )
        ) by {
            if w.api_ok {
                assert(mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m));
            }
        };
        assert(w.api_ok ==> mesh_runtime_geometric_topological_consistency_with_geometry_spec(m)) by {
            if w.api_ok {
                assert(mesh_runtime_geometric_topological_consistency_with_geometry_spec(m));
            }
        };
        assert(
            w.api_ok
                ==> mesh_runtime_geometric_topological_consistency_with_geometry_and_non_zero_edges_spec(
                    m,
                )
        ) by {
            if w.api_ok {
                assert(mesh_runtime_geometric_topological_consistency_with_geometry_spec(m));
                assert(
                    w.api_ok == (
                        w.phase4_valid_ok
                            && w.no_zero_length_geometric_edges_ok
                            && w.face_corner_non_collinearity_ok
                            && w.face_coplanarity_ok
                            && w.face_convexity_ok
                            && w.face_plane_consistency_ok
                            && w.shared_edge_local_orientation_ok
                            && w.no_forbidden_face_face_intersections_ok
                            && w.outward_face_normals_ok
                    )
                );
                assert(w.no_zero_length_geometric_edges_ok);
                assert(mesh_runtime_all_half_edges_non_zero_geometric_length_spec(m));
                assert(
                    mesh_runtime_geometric_topological_consistency_with_geometry_and_non_zero_edges_spec(
                        m,
                    )
                );
            }
        };
        assert(
            w.api_ok
                && mesh_runtime_all_faces_triangle_cycles_spec(m)
                ==> mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m)
        ) by {
            if w.api_ok && mesh_runtime_all_faces_triangle_cycles_spec(m) {
                assert(mesh_runtime_geometric_topological_consistency_with_geometry_spec(m));
                lemma_mesh_runtime_geometric_topological_consistency_with_geometry_and_triangle_cycles_imply_all_faces_projected_turn_sign_consistency(
                    m,
                );
                assert(mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m));
            }
        };
        assert(
            w.api_ok
                && mesh_runtime_all_faces_triangle_cycles_spec(m)
                ==> (
                    mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m)
                        == mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
                )
        ) by {
            if w.api_ok && mesh_runtime_all_faces_triangle_cycles_spec(m) {
                lemma_mesh_runtime_all_faces_triangle_cycles_projected_turn_sign_consistency_iff_seed0_corner_non_collinear(
                    m,
                );
                assert(
                    mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m)
                        == mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
                );
            }
        };
        assert(
            w.api_ok
                && mesh_runtime_all_faces_triangle_or_quad_cycles_spec(m)
                ==> mesh_runtime_all_faces_coplanar_spec(m)
        ) by {
            if w.api_ok && mesh_runtime_all_faces_triangle_or_quad_cycles_spec(m) {
                assert(mesh_runtime_geometric_topological_consistency_with_geometry_spec(m));
                lemma_mesh_runtime_geometric_topological_consistency_with_geometry_implies_mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle(
                    m,
                );
                assert(mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m));
                assert(mesh_runtime_all_faces_oriented_seed0_planes_spec(m));
                lemma_mesh_runtime_all_faces_oriented_seed0_planes_and_triangle_or_quad_cycles_imply_all_faces_coplanar(
                    m,
                );
                assert(mesh_runtime_all_faces_coplanar_spec(m));
            }
        };
        assert(w.api_ok ==> mesh_geometric_topological_consistency_spec(m@)) by {
            if w.api_ok {
                assert(mesh_geometric_topological_consistency_spec(m@));
            }
        };
    }

    Option::Some(w)
}

#[cfg(feature = "geometry-checks")]
#[allow(dead_code)]
pub fn runtime_check_phase4_valid_and_shared_edge_local_orientation_imply_geometric_topological_consistency_spec(
    m: &Mesh,
) -> (out: bool)
    ensures
        out ==> mesh_valid_spec(m@),
        out ==> mesh_shared_edge_local_orientation_consistency_spec(m@),
        out ==> mesh_geometric_topological_consistency_spec(m@),
{
    let validity_w = match is_valid_constructive(m) {
        Option::Some(w) => w,
        Option::None => return false,
    };
    if !validity_w.api_ok {
        return false;
    }

    let shared_edge_local_orientation_runtime_ok = m.check_shared_edge_local_orientation_consistency();
    if !shared_edge_local_orientation_runtime_ok {
        return false;
    }
    let shared_edge_local_orientation_bridge_ok =
        runtime_check_shared_edge_local_orientation_kernel_bridge(m);
    if !shared_edge_local_orientation_bridge_ok {
        return false;
    }

    proof {
        assert(validity_gate_witness_spec(validity_w));
        assert(validity_gate_model_link_spec(m@, validity_w));
        lemma_validity_gate_witness_api_ok_implies_mesh_valid(m@, validity_w);
        assert(mesh_valid_spec(m@));
        assert(shared_edge_local_orientation_bridge_ok);
        assert(mesh_shared_edge_local_orientation_consistency_spec(m@));
        lemma_mesh_valid_and_shared_edge_local_orientation_implies_mesh_geometric_topological_consistency(
            m@,
        );
        assert(mesh_geometric_topological_consistency_spec(m@));
    }

    true
}

#[cfg(feature = "geometry-checks")]
#[allow(dead_code)]
pub fn runtime_check_phase4_valid_and_kernel_shared_edge_local_orientation_imply_geometric_topological_consistency_spec(
    m: &Mesh,
) -> (out: bool)
    ensures
        out ==> mesh_valid_spec(m@),
        out ==> mesh_shared_edge_local_orientation_consistency_spec(m@),
        out ==> mesh_geometric_topological_consistency_spec(m@),
{
    let validity_w = match is_valid_constructive(m) {
        Option::Some(w) => w,
        Option::None => return false,
    };
    if !validity_w.api_ok {
        return false;
    }

    let shared_edge_local_orientation_bridge_ok =
        runtime_check_shared_edge_local_orientation_kernel_bridge(m);
    if !shared_edge_local_orientation_bridge_ok {
        return false;
    }

    proof {
        assert(validity_gate_witness_spec(validity_w));
        assert(validity_gate_model_link_spec(m@, validity_w));
        lemma_validity_gate_witness_api_ok_implies_mesh_valid(m@, validity_w);
        assert(mesh_valid_spec(m@));
        assert(shared_edge_local_orientation_bridge_ok);
        assert(mesh_shared_edge_local_orientation_consistency_spec(m@));
        lemma_mesh_valid_and_shared_edge_local_orientation_implies_mesh_geometric_topological_consistency(
            m@,
        );
        assert(mesh_geometric_topological_consistency_spec(m@));
    }

    true
}

#[cfg(feature = "geometry-checks")]
#[allow(dead_code)]
pub fn runtime_check_geometric_topological_consistency_sound_bridge(m: &Mesh) -> (out: bool)
    ensures
        out ==> mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m),
        out ==> mesh_runtime_geometric_topological_consistency_with_geometry_spec(m),
        out ==> mesh_runtime_geometric_topological_consistency_with_geometry_and_non_zero_edges_spec(m),
        out && mesh_runtime_all_faces_triangle_or_quad_cycles_spec(m)
            ==> mesh_runtime_all_faces_coplanar_spec(m),
        out && mesh_runtime_all_faces_triangle_cycles_spec(m)
            ==> mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m),
        out && mesh_runtime_all_faces_triangle_cycles_spec(m)
            ==> (
                mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m)
                    == mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
            ),
        out ==> mesh_geometric_topological_consistency_spec(m@),
        out ==> mesh_valid_spec(m@),
        out ==> mesh_shared_edge_local_orientation_consistency_spec(m@),
{
    let runtime_ok = m.check_geometric_topological_consistency();
    if !runtime_ok {
        return false;
    }

    let constructive_w = match check_geometric_topological_consistency_constructive(m) {
        Option::Some(w) => w,
        Option::None => return false,
    };
    if !constructive_w.api_ok {
        return false;
    }

    proof {
        assert(geometric_topological_consistency_gate_witness_spec(constructive_w));
        assert(geometric_topological_consistency_gate_model_link_spec(m@, constructive_w));
        assert(
            constructive_w.api_ok
                ==> mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m)
        );
        assert(constructive_w.api_ok ==> mesh_geometric_topological_consistency_spec(m@));
        assert(
            constructive_w.api_ok
                ==> mesh_runtime_geometric_topological_consistency_with_geometry_and_non_zero_edges_spec(
                    m,
                )
        );
        assert(
            constructive_w.api_ok
                && mesh_runtime_all_faces_triangle_or_quad_cycles_spec(m)
                ==> mesh_runtime_all_faces_coplanar_spec(m)
        );
        assert(mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m));
        assert(mesh_runtime_geometric_topological_consistency_with_geometry_and_non_zero_edges_spec(m));
        lemma_mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_implies_mesh_geometric_topological_consistency_with_geometry(
            m,
        );
        assert(mesh_runtime_geometric_topological_consistency_with_geometry_spec(m));
        assert(
            mesh_runtime_all_faces_triangle_or_quad_cycles_spec(m)
                ==> mesh_runtime_all_faces_coplanar_spec(m)
        ) by {
            if mesh_runtime_all_faces_triangle_or_quad_cycles_spec(m) {
                assert(mesh_runtime_all_faces_coplanar_spec(m));
            }
        };
        assert(
            mesh_runtime_all_faces_triangle_cycles_spec(m)
                ==> mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m)
        ) by {
            if mesh_runtime_all_faces_triangle_cycles_spec(m) {
                assert(mesh_runtime_geometric_topological_consistency_with_geometry_spec(m));
                lemma_mesh_runtime_geometric_topological_consistency_with_geometry_and_triangle_cycles_imply_all_faces_projected_turn_sign_consistency(
                    m,
                );
                assert(mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m));
            }
        };
        assert(
            mesh_runtime_all_faces_triangle_cycles_spec(m)
                ==> (
                    mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m)
                        == mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
                )
        ) by {
            if mesh_runtime_all_faces_triangle_cycles_spec(m) {
                lemma_mesh_runtime_all_faces_triangle_cycles_projected_turn_sign_consistency_iff_seed0_corner_non_collinear(
                    m,
                );
                assert(
                    mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m)
                        == mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
                );
            }
        };
        assert(mesh_geometric_topological_consistency_spec(m@));
        lemma_mesh_geometric_topological_consistency_implies_mesh_valid_and_shared_edge_local_orientation(
            m@,
        );
        assert(mesh_valid_spec(m@));
        assert(mesh_shared_edge_local_orientation_consistency_spec(m@));
    }

    true
}

#[cfg(feature = "geometry-checks")]
#[allow(dead_code)]
pub fn runtime_check_geometric_topological_consistency_triangle_projected_turn_sound_bridge(
    m: &Mesh,
) -> (out: bool)
    requires
        mesh_runtime_all_faces_triangle_cycles_spec(m),
    ensures
        out == runtime_check_geometric_topological_consistency_sound_bridge(m),
        out ==> mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m),
        out ==> mesh_runtime_geometric_topological_consistency_with_geometry_spec(m),
        out ==> mesh_geometric_topological_consistency_spec(m@),
        out ==> mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m),
        out ==> mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m),
        out ==> (
            mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m)
                == mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
        ),
{
    let geometric_sound_ok = runtime_check_geometric_topological_consistency_sound_bridge(m);
    if !geometric_sound_ok {
        return false;
    }

    proof {
        assert(
            geometric_sound_ok
                ==> mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m)
        );
        assert(geometric_sound_ok ==> mesh_runtime_geometric_topological_consistency_with_geometry_spec(m));
        assert(geometric_sound_ok ==> mesh_geometric_topological_consistency_spec(m@));
        assert(
            geometric_sound_ok
                ==> mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m)
        );
        assert(mesh_runtime_geometric_topological_consistency_seed0_coplanarity_bundle_spec(m));
        assert(mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m));
        assert(mesh_runtime_geometric_topological_consistency_with_geometry_spec(m));
        assert(mesh_runtime_all_faces_triangle_cycles_spec(m));
        lemma_mesh_runtime_geometric_topological_consistency_with_geometry_and_triangle_cycles_imply_all_faces_projected_turn_sign_consistency(
            m,
        );
        assert(mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m));
        lemma_mesh_runtime_all_faces_triangle_cycles_projected_turn_sign_consistency_iff_seed0_corner_non_collinear(
            m,
        );
        assert(
            mesh_runtime_all_faces_projected_turn_sign_consistency_spec(m)
                == mesh_runtime_all_faces_seed0_corner_non_collinear_spec(m)
        );
    }

    geometric_sound_ok
}

#[cfg(feature = "geometry-checks")]
#[allow(dead_code)]
pub fn is_valid_with_geometry_constructive(
    m: &Mesh,
) -> (out: Option<ValidWithGeometryGateWitness>)
    ensures
        match out {
            Option::Some(w) => valid_with_geometry_gate_witness_spec(w)
                && valid_with_geometry_gate_model_link_spec(m@, w)
                && (w.api_ok ==> mesh_valid_spec(m@))
                && (w.api_ok ==> mesh_valid_with_geometry_spec(m@)),
            Option::None => true,
        },
{
    let validity_w = match is_valid_constructive(m) {
        Option::Some(w) => w,
        Option::None => return Option::None,
    };

    let geometric_w = match check_geometric_topological_consistency_constructive(m) {
        Option::Some(w) => w,
        Option::None => return Option::None,
    };

    let phase4_validity_ok = validity_w.api_ok;
    let geometric_topological_consistency_ok = geometric_w.api_ok;
    let api_ok = phase4_validity_ok && geometric_topological_consistency_ok;

    let w = ValidWithGeometryGateWitness {
        api_ok,
        phase4_validity_ok,
        geometric_topological_consistency_ok,
    };

    proof {
        assert(validity_gate_witness_spec(validity_w));
        assert(validity_gate_model_link_spec(m@, validity_w));
        assert(geometric_topological_consistency_gate_witness_spec(geometric_w));
        assert(geometric_topological_consistency_gate_model_link_spec(m@, geometric_w));
        assert(valid_with_geometry_gate_witness_spec(w));

        assert(exists|vw: ValidityGateWitness| {
            &&& validity_gate_witness_spec(vw)
            &&& validity_gate_model_link_spec(m@, vw)
            &&& vw.api_ok == w.phase4_validity_ok
        }) by {
            let vw = validity_w;
            assert(validity_gate_witness_spec(vw));
            assert(validity_gate_model_link_spec(m@, vw));
            assert(vw.api_ok == w.phase4_validity_ok);
        };

        assert(exists|gw: GeometricTopologicalConsistencyGateWitness| {
            &&& geometric_topological_consistency_gate_witness_spec(gw)
            &&& geometric_topological_consistency_gate_model_link_spec(m@, gw)
            &&& gw.api_ok == w.geometric_topological_consistency_ok
        }) by {
            let gw = geometric_w;
            assert(geometric_topological_consistency_gate_witness_spec(gw));
            assert(geometric_topological_consistency_gate_model_link_spec(m@, gw));
            assert(gw.api_ok == w.geometric_topological_consistency_ok);
        };

        assert(valid_with_geometry_gate_model_link_spec(m@, w));
        if w.api_ok {
            lemma_valid_with_geometry_gate_witness_api_ok_implies_mesh_valid(m@, w);
            assert(mesh_valid_spec(m@));
            assert(mesh_valid_with_geometry_spec(m@));
        }
        assert(w.api_ok ==> mesh_valid_spec(m@)) by {
            if w.api_ok {
                assert(mesh_valid_spec(m@));
            }
        };
        assert(w.api_ok ==> mesh_valid_with_geometry_spec(m@)) by {
            if w.api_ok {
                assert(mesh_valid_with_geometry_spec(m@));
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
    let vertices = vec![
        RuntimePoint3::from_ints(0, 0, 0),
        RuntimePoint3::from_ints(1, 0, 0),
        RuntimePoint3::from_ints(0, 1, 0),
        RuntimePoint3::from_ints(0, 0, 1),
    ];
    let faces = vec![vec![0, 1, 2], vec![0, 3, 1], vec![1, 3, 2], vec![2, 3, 0]];
    let built = from_face_cycles_constructive_next_prev_face(vertices, &faces);
    let m = match built {
        Result::Ok(m) => m,
        Result::Err(_) => return Option::None,
    };
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
    let vertices = vec![
        RuntimePoint3::from_ints(-1, -1, -1),
        RuntimePoint3::from_ints(1, -1, -1),
        RuntimePoint3::from_ints(1, 1, -1),
        RuntimePoint3::from_ints(-1, 1, -1),
        RuntimePoint3::from_ints(-1, -1, 1),
        RuntimePoint3::from_ints(1, -1, 1),
        RuntimePoint3::from_ints(1, 1, 1),
        RuntimePoint3::from_ints(-1, 1, 1),
    ];
    let faces = vec![
        vec![0, 3, 2, 1],
        vec![4, 5, 6, 7],
        vec![0, 1, 5, 4],
        vec![3, 7, 6, 2],
        vec![0, 4, 7, 3],
        vec![1, 2, 6, 5],
    ];
    let built = from_face_cycles_constructive_next_prev_face(vertices, &faces);
    let m = match built {
        Result::Ok(m) => m,
        Result::Err(_) => return Option::None,
    };
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
    let vertices = vec![
        RuntimePoint3::from_ints(0, 0, 0),
        RuntimePoint3::from_ints(2, 0, 0),
        RuntimePoint3::from_ints(1, 2, 0),
        RuntimePoint3::from_ints(0, 0, 1),
        RuntimePoint3::from_ints(2, 0, 1),
        RuntimePoint3::from_ints(1, 2, 1),
    ];
    let faces = vec![
        vec![0, 2, 1],
        vec![3, 4, 5],
        vec![0, 1, 4, 3],
        vec![1, 2, 5, 4],
        vec![2, 0, 3, 5],
    ];
    let built = from_face_cycles_constructive_next_prev_face(vertices, &faces);
    let m = match built {
        Result::Ok(m) => m,
        Result::Err(_) => return Option::None,
    };
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
