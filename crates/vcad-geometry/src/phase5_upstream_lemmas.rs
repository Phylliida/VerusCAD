#[cfg(verus_keep_ghost)]
use vcad_math::orientation3::orient3d_spec;
#[cfg(verus_keep_ghost)]
use vcad_math::point3::Point3;
#[cfg(verus_keep_ghost)]
use vcad_math::scalar::Scalar;
#[cfg(verus_keep_ghost)]
use vcad_math::vec3::Vec3;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {

pub open spec fn normal_nonzero3_spec(normal: Vec3) -> bool {
    !(normal.x.signum() == 0 && normal.y.signum() == 0 && normal.z.signum() == 0)
}

pub open spec fn point3_as_vec_spec(p: Point3) -> Vec3 {
    Vec3 { x: p.x, y: p.y, z: p.z }
}

pub open spec fn plane_dot_spec(normal: Vec3, p: Point3) -> Scalar {
    normal.dot_spec(point3_as_vec_spec(p))
}

pub open spec fn points_on_common_plane_spec(
    a: Point3,
    b: Point3,
    c: Point3,
    d: Point3,
    normal: Vec3,
    offset: Scalar,
) -> bool {
    &&& plane_dot_spec(normal, a).eqv_spec(offset)
    &&& plane_dot_spec(normal, b).eqv_spec(offset)
    &&& plane_dot_spec(normal, c).eqv_spec(offset)
    &&& plane_dot_spec(normal, d).eqv_spec(offset)
}

proof fn lemma_point3_as_vec_sub_spec(p: Point3, q: Point3)
    ensures
        point3_as_vec_spec(p).sub_spec(point3_as_vec_spec(q)) == p.sub_spec(q),
{
    assert(point3_as_vec_spec(p).sub_spec(point3_as_vec_spec(q)).x == p.x.sub_spec(q.x));
    assert(point3_as_vec_spec(p).sub_spec(point3_as_vec_spec(q)).y == p.y.sub_spec(q.y));
    assert(point3_as_vec_spec(p).sub_spec(point3_as_vec_spec(q)).z == p.z.sub_spec(q.z));
    assert(point3_as_vec_spec(p).sub_spec(point3_as_vec_spec(q)) == p.sub_spec(q));
}

proof fn lemma_plane_dot_sub_equals_dot_of_point_diff(normal: Vec3, p: Point3, q: Point3)
    ensures
        plane_dot_spec(normal, p).sub_spec(plane_dot_spec(normal, q)).eqv_spec(
            normal.dot_spec(p.sub_spec(q)),
        ),
{
    let pv = point3_as_vec_spec(p);
    let qv = point3_as_vec_spec(q);
    let ap = plane_dot_spec(normal, p);
    let aq = plane_dot_spec(normal, q);
    let lhs = ap.sub_spec(aq);
    let dot_add = normal.dot_spec(pv.add_spec(qv.neg_spec()));

    Scalar::lemma_sub_is_add_neg(ap, aq);
    assert(lhs == ap.add_spec(aq.neg_spec()));

    Vec3::lemma_dot_linear_right(normal, pv, qv.neg_spec());
    assert(dot_add.eqv_spec(ap.add_spec(normal.dot_spec(qv.neg_spec()))));
    Vec3::lemma_dot_neg_right(normal, qv);
    Scalar::lemma_eqv_add_congruence(
        ap,
        ap,
        normal.dot_spec(qv.neg_spec()),
        aq.neg_spec(),
    );
    assert(ap.add_spec(normal.dot_spec(qv.neg_spec())).eqv_spec(ap.add_spec(aq.neg_spec())));
    Scalar::lemma_eqv_transitive(
        dot_add,
        ap.add_spec(normal.dot_spec(qv.neg_spec())),
        ap.add_spec(aq.neg_spec()),
    );
    assert(dot_add.eqv_spec(ap.add_spec(aq.neg_spec())));
    Scalar::lemma_eqv_symmetric(dot_add, ap.add_spec(aq.neg_spec()));
    assert(ap.add_spec(aq.neg_spec()).eqv_spec(dot_add));
    Scalar::lemma_eqv_transitive(lhs, ap.add_spec(aq.neg_spec()), dot_add);
    assert(lhs.eqv_spec(dot_add));

    lemma_point3_as_vec_sub_spec(p, q);
    Vec3::lemma_sub_is_add_neg(pv, qv);
    assert(pv.sub_spec(qv) == pv.add_spec(qv.neg_spec()));
    assert(p.sub_spec(q) == pv.sub_spec(qv));
    assert(normal.dot_spec(p.sub_spec(q)) == normal.dot_spec(pv.add_spec(qv.neg_spec())));
    assert(normal.dot_spec(p.sub_spec(q)) == dot_add);
    assert(lhs.eqv_spec(normal.dot_spec(p.sub_spec(q))));
}

proof fn lemma_two_plane_points_with_same_offset_imply_orthogonal_difference(
    normal: Vec3,
    p: Point3,
    q: Point3,
    offset: Scalar,
)
    requires
        plane_dot_spec(normal, p).eqv_spec(offset),
        plane_dot_spec(normal, q).eqv_spec(offset),
    ensures
        normal.dot_spec(p.sub_spec(q)).eqv_spec(Scalar::from_int_spec(0)),
{
    let z = Scalar::from_int_spec(0);
    let lhs = plane_dot_spec(normal, p).sub_spec(plane_dot_spec(normal, q));
    let off_diff = offset.sub_spec(offset);

    Scalar::lemma_eqv_sub_congruence(plane_dot_spec(normal, p), offset, plane_dot_spec(normal, q), offset);
    assert(lhs.eqv_spec(off_diff));

    Scalar::lemma_sub_eqv_zero_iff_eqv(offset, offset);
    Scalar::lemma_eqv_reflexive(offset);
    assert(off_diff.eqv_spec(z) == offset.eqv_spec(offset));
    assert(offset.eqv_spec(offset));
    assert(off_diff.eqv_spec(z));
    Scalar::lemma_eqv_transitive(lhs, off_diff, z);
    assert(lhs.eqv_spec(z));

    lemma_plane_dot_sub_equals_dot_of_point_diff(normal, p, q);
    assert(lhs.eqv_spec(normal.dot_spec(p.sub_spec(q))));
    Scalar::lemma_eqv_symmetric(lhs, normal.dot_spec(p.sub_spec(q)));
    assert(normal.dot_spec(p.sub_spec(q)).eqv_spec(lhs));
    Scalar::lemma_eqv_transitive(normal.dot_spec(p.sub_spec(q)), lhs, z);
    assert(normal.dot_spec(p.sub_spec(q)).eqv_spec(z));
}

pub proof fn lemma_three_vectors_orthogonal_to_aligned_nonzero_normal_implies_det_zero(
    u: Vec3,
    v: Vec3,
    w: Vec3,
    normal: Vec3,
)
    requires
        normal_nonzero3_spec(normal),
        normal.eqv_spec(u.cross_spec(v)),
        normal.dot_spec(u).eqv_spec(Scalar::from_int_spec(0)),
        normal.dot_spec(v).eqv_spec(Scalar::from_int_spec(0)),
        normal.dot_spec(w).eqv_spec(Scalar::from_int_spec(0)),
    ensures
        u.dot_spec(v.cross_spec(w)).eqv_spec(Scalar::from_int_spec(0)),
{
    let z = Scalar::from_int_spec(0);
    let w_dot_n = w.dot_spec(normal);
    let w_dot_uv = w.dot_spec(u.cross_spec(v));
    let det = u.dot_spec(v.cross_spec(w));

    assert(normal.dot_spec(u).eqv_spec(z));
    assert(normal.dot_spec(v).eqv_spec(z));
    assert(normal.dot_spec(w).eqv_spec(z));

    Vec3::lemma_dot_symmetric(normal, w);
    assert(normal.dot_spec(w).eqv_spec(w_dot_n));
    Scalar::lemma_eqv_symmetric(normal.dot_spec(w), w_dot_n);
    assert(w_dot_n.eqv_spec(normal.dot_spec(w)));
    Scalar::lemma_eqv_transitive(w_dot_n, normal.dot_spec(w), z);
    assert(w_dot_n.eqv_spec(z));

    Vec3::lemma_dot_eqv_congruence(w, w, normal, u.cross_spec(v));
    assert(w_dot_n.eqv_spec(w_dot_uv));
    Scalar::lemma_eqv_symmetric(w_dot_n, w_dot_uv);
    assert(w_dot_uv.eqv_spec(w_dot_n));
    Scalar::lemma_eqv_transitive(w_dot_uv, w_dot_n, z);
    assert(w_dot_uv.eqv_spec(z));

    Vec3::lemma_dot_cross_cyclic(w, u, v);
    assert(w_dot_uv.eqv_spec(det));
    Scalar::lemma_eqv_symmetric(w_dot_uv, det);
    assert(det.eqv_spec(w_dot_uv));
    Scalar::lemma_eqv_transitive(det, w_dot_uv, z);
    assert(det.eqv_spec(z));
}

pub proof fn lemma_points_on_common_plane_with_aligned_normal_implies_orient3d_zero(
    a: Point3,
    b: Point3,
    c: Point3,
    d: Point3,
    normal: Vec3,
    offset: Scalar,
)
    requires
        points_on_common_plane_spec(a, b, c, d, normal, offset),
        normal_nonzero3_spec(normal),
        normal.eqv_spec(b.sub_spec(a).cross_spec(c.sub_spec(a))),
    ensures
        orient3d_spec(a, b, c, d).eqv_spec(Scalar::from_int_spec(0)),
        orient3d_spec(a, b, c, d).signum() == 0,
{
    let z = Scalar::from_int_spec(0);
    let ba = b.sub_spec(a);
    let ca = c.sub_spec(a);
    let da = d.sub_spec(a);
    let det = orient3d_spec(a, b, c, d);

    lemma_two_plane_points_with_same_offset_imply_orthogonal_difference(normal, b, a, offset);
    lemma_two_plane_points_with_same_offset_imply_orthogonal_difference(normal, c, a, offset);
    lemma_two_plane_points_with_same_offset_imply_orthogonal_difference(normal, d, a, offset);

    assert(normal.dot_spec(ba).eqv_spec(z));
    assert(normal.dot_spec(ca).eqv_spec(z));
    assert(normal.dot_spec(da).eqv_spec(z));

    lemma_three_vectors_orthogonal_to_aligned_nonzero_normal_implies_det_zero(ba, ca, da, normal);
    assert(ba.dot_spec(ca.cross_spec(da)).eqv_spec(z));
    assert(det == ba.dot_spec(ca.cross_spec(da)));
    assert(det.eqv_spec(z));

    Scalar::lemma_eqv_signum(det, z);
    assert(det.signum() == z.signum());
    assert(z.signum() == 0);
}

} // verus!
