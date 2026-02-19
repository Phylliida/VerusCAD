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

pub open spec fn witness_along_normal_spec(
    p0: Point3,
    p1: Point3,
    p2: Point3,
    witness: Point3,
    normal: Vec3,
) -> bool {
    &&& witness.eqv_spec(p0.add_vec_spec(normal))
    &&& normal.eqv_spec(p1.sub_spec(p0).cross_spec(p2.sub_spec(p1)))
}

pub open spec fn det3_spec(u: Vec3, v: Vec3, w: Vec3) -> Scalar {
    u.dot_spec(v.cross_spec(w))
}

pub open spec fn point_in_aabb3_spec(p: Point3, min: Point3, max: Point3) -> bool {
    &&& min.x.le_spec(p.x)
    &&& p.x.le_spec(max.x)
    &&& min.y.le_spec(p.y)
    &&& p.y.le_spec(max.y)
    &&& min.z.le_spec(p.z)
    &&& p.z.le_spec(max.z)
}

pub open spec fn aabb_separated_on_some_axis_spec(
    min_a: Point3,
    max_a: Point3,
    min_b: Point3,
    max_b: Point3,
) -> bool {
    max_a.x.lt_spec(min_b.x)
        || max_b.x.lt_spec(min_a.x)
        || max_a.y.lt_spec(min_b.y)
        || max_b.y.lt_spec(min_a.y)
        || max_a.z.lt_spec(min_b.z)
        || max_b.z.lt_spec(min_a.z)
}

pub open spec fn shape_contained_in_aabb3_spec(
    shape: spec_fn(Point3) -> bool,
    min: Point3,
    max: Point3,
) -> bool {
    forall|p: Point3| #[trigger] shape(p) ==> point_in_aabb3_spec(p, min, max)
}

proof fn lemma_scalar_le_transitive(a: Scalar, b: Scalar, c: Scalar)
    requires
        a.le_spec(b),
        b.le_spec(c),
    ensures
        a.le_spec(c),
{
    assert(a.le_spec(b) == (a.num * b.denom() <= b.num * a.denom()));
    assert(b.le_spec(c) == (b.num * c.denom() <= c.num * b.denom()));
    assert(a.le_spec(c) == (a.num * c.denom() <= c.num * a.denom()));

    assert(b.denom_nat() > 0);
    assert((b.denom_nat() as int) > 0) by (nonlinear_arith);
    assert(b.denom() == b.denom_nat() as int);
    assert(b.denom() > 0);

    assert(
        (a.num * b.denom() <= b.num * a.denom())
            && (b.num * c.denom() <= c.num * b.denom())
            && (b.denom() > 0)
            ==> (a.num * c.denom() <= c.num * a.denom())
    ) by (nonlinear_arith);
    assert(a.num * c.denom() <= c.num * a.denom());
    assert(a.le_spec(c));
}

proof fn lemma_scalar_lt_incompatible_with_reverse_le(a: Scalar, b: Scalar)
    requires
        a.lt_spec(b),
        b.le_spec(a),
    ensures
        false,
{
    let lhs = a.num * b.denom();
    let rhs = b.num * a.denom();
    assert(a.lt_spec(b) == (lhs < rhs));
    assert(b.le_spec(a) == (rhs <= lhs));
    assert(lhs < rhs);
    assert((rhs <= lhs) == !(lhs < rhs)) by (nonlinear_arith);
    assert(!(rhs <= lhs));
    assert(false);
}

proof fn lemma_scalar_zero_le_iff_num_nonnegative(a: Scalar)
    ensures
        Scalar::from_int_spec(0).le_spec(a) == (a.num >= 0),
{
    let z = Scalar::from_int_spec(0);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(z.le_spec(a) == (z.num * a.denom() <= a.num * z.denom()));
    assert(z.le_spec(a) == (0 * a.denom() <= a.num * 1));
    assert((0 * a.denom() <= a.num * 1) == (0 <= a.num)) by (nonlinear_arith);
}

proof fn lemma_scalar_zero_lt_iff_num_positive(a: Scalar)
    ensures
        Scalar::from_int_spec(0).lt_spec(a) == (a.num > 0),
{
    let z = Scalar::from_int_spec(0);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(z.lt_spec(a) == (z.num * a.denom() < a.num * z.denom()));
    assert(z.lt_spec(a) == (0 * a.denom() < a.num * 1));
    assert((0 * a.denom() < a.num * 1) == (0 < a.num)) by (nonlinear_arith);
}

proof fn lemma_nonnegative_weights_summing_to_one_implies_some_positive(
    w0: Scalar,
    w1: Scalar,
)
    requires
        Scalar::from_int_spec(0).le_spec(w0),
        Scalar::from_int_spec(0).le_spec(w1),
        w0.add_spec(w1).eqv_spec(Scalar::from_int_spec(1)),
    ensures
        Scalar::from_int_spec(0).lt_spec(w0) || Scalar::from_int_spec(0).lt_spec(w1),
{
    let z = Scalar::from_int_spec(0);
    let one = Scalar::from_int_spec(1);
    let sum_w = w0.add_spec(w1);

    lemma_scalar_zero_le_iff_num_nonnegative(w0);
    lemma_scalar_zero_le_iff_num_nonnegative(w1);
    assert(w0.num >= 0);
    assert(w1.num >= 0);

    assert(sum_w.eqv_spec(one));
    Scalar::lemma_eqv_signum(sum_w, one);
    assert(one.num == 1);
    assert(one.signum() == 1);
    assert(sum_w.signum() == one.signum());
    if !(sum_w.num > 0) {
        if sum_w.num < 0 {
            assert(sum_w.signum() == -1);
            assert(sum_w.signum() == 1);
            assert(false);
        }
        assert(!(sum_w.num < 0));
        assert((!(sum_w.num > 0) && !(sum_w.num < 0)) ==> (sum_w.num == 0)) by (nonlinear_arith);
        assert(sum_w.num == 0);
        assert(sum_w.signum() == 0);
        assert(sum_w.signum() == 1);
        assert(false);
    }
    assert(sum_w.num > 0);

    if !(z.lt_spec(w0) || z.lt_spec(w1)) {
        lemma_scalar_zero_lt_iff_num_positive(w0);
        lemma_scalar_zero_lt_iff_num_positive(w1);
        assert(!z.lt_spec(w0));
        assert(!z.lt_spec(w1));
        assert(!(w0.num > 0));
        assert(!(w1.num > 0));
        assert((!(w0.num > 0) && w0.num >= 0) ==> (w0.num == 0)) by (nonlinear_arith);
        assert((!(w1.num > 0) && w1.num >= 0) ==> (w1.num == 0)) by (nonlinear_arith);
        assert(w0.num == 0);
        assert(w1.num == 0);

        assert(sum_w.num == w0.num * w1.denom() + w1.num * w0.denom());
        assert(sum_w.num == 0 * w1.denom() + 0 * w0.denom());
        assert(0 * w1.denom() == 0) by (nonlinear_arith);
        assert(0 * w0.denom() == 0) by (nonlinear_arith);
        assert(sum_w.num == 0 + 0);
        assert(sum_w.num == 0);
        assert(false);
    }
}

proof fn lemma_nonnegative_three_weights_summing_to_one_implies_some_positive(
    w0: Scalar,
    w1: Scalar,
    w2: Scalar,
)
    requires
        Scalar::from_int_spec(0).le_spec(w0),
        Scalar::from_int_spec(0).le_spec(w1),
        Scalar::from_int_spec(0).le_spec(w2),
        w0.add_spec(w1).add_spec(w2).eqv_spec(Scalar::from_int_spec(1)),
    ensures
        Scalar::from_int_spec(0).lt_spec(w0)
            || Scalar::from_int_spec(0).lt_spec(w1)
            || Scalar::from_int_spec(0).lt_spec(w2),
{
    let z = Scalar::from_int_spec(0);
    let one = Scalar::from_int_spec(1);
    let sum01 = w0.add_spec(w1);
    let sum = sum01.add_spec(w2);

    lemma_scalar_zero_le_iff_num_nonnegative(w0);
    lemma_scalar_zero_le_iff_num_nonnegative(w1);
    lemma_scalar_zero_le_iff_num_nonnegative(w2);
    assert(w0.num >= 0);
    assert(w1.num >= 0);
    assert(w2.num >= 0);

    if !(z.lt_spec(w0) || z.lt_spec(w1) || z.lt_spec(w2)) {
        lemma_scalar_zero_lt_iff_num_positive(w0);
        lemma_scalar_zero_lt_iff_num_positive(w1);
        lemma_scalar_zero_lt_iff_num_positive(w2);
        assert(!z.lt_spec(w0));
        assert(!z.lt_spec(w1));
        assert(!z.lt_spec(w2));
        assert(!(w0.num > 0));
        assert(!(w1.num > 0));
        assert(!(w2.num > 0));
        assert((!(w0.num > 0) && w0.num >= 0) ==> (w0.num == 0)) by (nonlinear_arith);
        assert((!(w1.num > 0) && w1.num >= 0) ==> (w1.num == 0)) by (nonlinear_arith);
        assert((!(w2.num > 0) && w2.num >= 0) ==> (w2.num == 0)) by (nonlinear_arith);
        assert(w0.num == 0);
        assert(w1.num == 0);
        assert(w2.num == 0);

        assert(sum01.num == w0.num * w1.denom() + w1.num * w0.denom());
        assert(sum01.num == 0 * w1.denom() + 0 * w0.denom());
        assert(0 * w1.denom() == 0) by (nonlinear_arith);
        assert(0 * w0.denom() == 0) by (nonlinear_arith);
        assert(sum01.num == 0 + 0);
        assert(sum01.num == 0);
        assert(sum.num == sum01.num * w2.denom() + w2.num * sum01.denom());
        assert(sum.num == 0 * w2.denom() + 0 * sum01.denom());
        assert(0 * w2.denom() == 0) by (nonlinear_arith);
        assert(0 * sum01.denom() == 0) by (nonlinear_arith);
        assert(sum.num == 0 + 0);
        assert(sum.num == 0);

        assert(sum.eqv_spec(one));
        Scalar::lemma_eqv_signum(sum, one);
        assert(one.num == 1);
        assert(one.signum() == 1);
        assert(sum.signum() == one.signum());
        if !(sum.num > 0) {
            if sum.num < 0 {
                assert(sum.signum() == -1);
                assert(sum.signum() == 1);
                assert(false);
            }
            assert(!(sum.num < 0));
            assert((!(sum.num > 0) && !(sum.num < 0)) ==> (sum.num == 0)) by (nonlinear_arith);
            assert(sum.num == 0);
            assert(sum.signum() == 0);
            assert(sum.signum() == 1);
            assert(false);
        }
        assert(sum.num > 0);
        assert(false);
    }
}

proof fn lemma_scalar_mul_of_nonnegative_and_positive_is_nonnegative(a: Scalar, b: Scalar)
    requires
        Scalar::from_int_spec(0).le_spec(a),
        Scalar::from_int_spec(0).lt_spec(b),
    ensures
        Scalar::from_int_spec(0).le_spec(a.mul_spec(b)),
{
    let z = Scalar::from_int_spec(0);
    let out = a.mul_spec(b);

    lemma_scalar_zero_le_iff_num_nonnegative(a);
    lemma_scalar_zero_lt_iff_num_positive(b);
    assert(a.num >= 0);
    assert(b.num > 0);
    assert(out.num == a.num * b.num);
    assert((a.num >= 0 && b.num > 0) ==> (a.num * b.num >= 0)) by (nonlinear_arith);
    assert(a.num * b.num >= 0);
    assert(out.num >= 0);
    lemma_scalar_zero_le_iff_num_nonnegative(out);
    assert(z.le_spec(out));
}

proof fn lemma_scalar_mul_of_positive_and_positive_is_positive(a: Scalar, b: Scalar)
    requires
        Scalar::from_int_spec(0).lt_spec(a),
        Scalar::from_int_spec(0).lt_spec(b),
    ensures
        Scalar::from_int_spec(0).lt_spec(a.mul_spec(b)),
{
    let z = Scalar::from_int_spec(0);
    let out = a.mul_spec(b);

    lemma_scalar_zero_lt_iff_num_positive(a);
    lemma_scalar_zero_lt_iff_num_positive(b);
    assert(a.num > 0);
    assert(b.num > 0);
    assert(out.num == a.num * b.num);
    assert((a.num > 0 && b.num > 0) ==> (a.num * b.num > 0)) by (nonlinear_arith);
    assert(a.num * b.num > 0);
    assert(out.num > 0);
    lemma_scalar_zero_lt_iff_num_positive(out);
    assert(z.lt_spec(out));
}

proof fn lemma_scalar_add_of_nonnegative_and_nonnegative_is_nonnegative(a: Scalar, b: Scalar)
    requires
        Scalar::from_int_spec(0).le_spec(a),
        Scalar::from_int_spec(0).le_spec(b),
    ensures
        Scalar::from_int_spec(0).le_spec(a.add_spec(b)),
{
    let z = Scalar::from_int_spec(0);
    let out = a.add_spec(b);

    lemma_scalar_zero_le_iff_num_nonnegative(a);
    lemma_scalar_zero_le_iff_num_nonnegative(b);
    assert(a.num >= 0);
    assert(b.num >= 0);
    assert(out.num == a.num * b.denom() + b.num * a.denom());
    assert((a.num >= 0 && b.num >= 0 && a.denom() > 0 && b.denom() > 0)
        ==> (a.num * b.denom() + b.num * a.denom() >= 0)) by (nonlinear_arith);
    assert(a.num * b.denom() + b.num * a.denom() >= 0);
    assert(out.num >= 0);
    lemma_scalar_zero_le_iff_num_nonnegative(out);
    assert(z.le_spec(out));
}

proof fn lemma_scalar_add_of_positive_and_nonnegative_is_positive(pos: Scalar, nonneg: Scalar)
    requires
        Scalar::from_int_spec(0).lt_spec(pos),
        Scalar::from_int_spec(0).le_spec(nonneg),
    ensures
        Scalar::from_int_spec(0).lt_spec(pos.add_spec(nonneg)),
{
    let z = Scalar::from_int_spec(0);
    let out = pos.add_spec(nonneg);

    lemma_scalar_zero_lt_iff_num_positive(pos);
    lemma_scalar_zero_le_iff_num_nonnegative(nonneg);
    assert(pos.num > 0);
    assert(nonneg.num >= 0);
    assert(nonneg.denom_nat() > 0);
    assert((nonneg.denom_nat() as int) > 0) by (nonlinear_arith);
    assert(nonneg.denom() == nonneg.denom_nat() as int);
    assert(nonneg.denom() > 0);
    assert(pos.denom_nat() > 0);
    assert((pos.denom_nat() as int) > 0) by (nonlinear_arith);
    assert(pos.denom() == pos.denom_nat() as int);
    assert(pos.denom() > 0);
    assert((pos.num > 0 && nonneg.denom() > 0) ==> (pos.num * nonneg.denom() > 0)) by (nonlinear_arith);
    assert(pos.num * nonneg.denom() > 0);
    assert((nonneg.num >= 0 && pos.denom() > 0) ==> (nonneg.num * pos.denom() >= 0)) by (nonlinear_arith);
    assert(nonneg.num * pos.denom() >= 0);
    assert(out.num == pos.num * nonneg.denom() + nonneg.num * pos.denom());
    assert((pos.num * nonneg.denom() > 0 && nonneg.num * pos.denom() >= 0)
        ==> (pos.num * nonneg.denom() + nonneg.num * pos.denom() > 0)) by (nonlinear_arith);
    assert(pos.num * nonneg.denom() + nonneg.num * pos.denom() > 0);
    assert(out.num > 0);
    lemma_scalar_zero_lt_iff_num_positive(out);
    assert(z.lt_spec(out));
}

proof fn lemma_scalar_add_of_nonnegative_and_positive_is_positive(nonneg: Scalar, pos: Scalar)
    requires
        Scalar::from_int_spec(0).le_spec(nonneg),
        Scalar::from_int_spec(0).lt_spec(pos),
    ensures
        Scalar::from_int_spec(0).lt_spec(nonneg.add_spec(pos)),
{
    let z = Scalar::from_int_spec(0);
    let out = nonneg.add_spec(pos);

    lemma_scalar_zero_le_iff_num_nonnegative(nonneg);
    lemma_scalar_zero_lt_iff_num_positive(pos);
    assert(nonneg.num >= 0);
    assert(pos.num > 0);
    assert(pos.denom_nat() > 0);
    assert((pos.denom_nat() as int) > 0) by (nonlinear_arith);
    assert(pos.denom() == pos.denom_nat() as int);
    assert(pos.denom() > 0);
    assert(nonneg.denom_nat() > 0);
    assert((nonneg.denom_nat() as int) > 0) by (nonlinear_arith);
    assert(nonneg.denom() == nonneg.denom_nat() as int);
    assert(nonneg.denom() > 0);
    assert((nonneg.num >= 0 && pos.denom() > 0) ==> (nonneg.num * pos.denom() >= 0)) by (nonlinear_arith);
    assert(nonneg.num * pos.denom() >= 0);
    assert((pos.num > 0 && nonneg.denom() > 0) ==> (pos.num * nonneg.denom() > 0)) by (nonlinear_arith);
    assert(pos.num * nonneg.denom() > 0);
    assert(out.num == nonneg.num * pos.denom() + pos.num * nonneg.denom());
    assert((nonneg.num * pos.denom() >= 0 && pos.num * nonneg.denom() > 0)
        ==> (nonneg.num * pos.denom() + pos.num * nonneg.denom() > 0)) by (nonlinear_arith);
    assert(nonneg.num * pos.denom() + pos.num * nonneg.denom() > 0);
    assert(out.num > 0);
    lemma_scalar_zero_lt_iff_num_positive(out);
    assert(z.lt_spec(out));
}

pub proof fn lemma_binary_convex_combination_of_positive_values_is_positive(
    w0: Scalar,
    w1: Scalar,
    x0: Scalar,
    x1: Scalar,
)
    requires
        Scalar::from_int_spec(0).le_spec(w0),
        Scalar::from_int_spec(0).le_spec(w1),
        w0.add_spec(w1).eqv_spec(Scalar::from_int_spec(1)),
        Scalar::from_int_spec(0).lt_spec(x0),
        Scalar::from_int_spec(0).lt_spec(x1),
    ensures
        Scalar::from_int_spec(0).lt_spec(w0.mul_spec(x0).add_spec(w1.mul_spec(x1))),
{
    let z = Scalar::from_int_spec(0);
    let t0 = w0.mul_spec(x0);
    let t1 = w1.mul_spec(x1);
    let out = t0.add_spec(t1);

    lemma_scalar_zero_le_iff_num_nonnegative(w0);
    lemma_scalar_zero_le_iff_num_nonnegative(w1);
    lemma_scalar_zero_lt_iff_num_positive(x0);
    lemma_scalar_zero_lt_iff_num_positive(x1);
    assert(w0.num >= 0);
    assert(w1.num >= 0);
    assert(x0.num > 0);
    assert(x1.num > 0);

    assert(t0.num == w0.num * x0.num);
    assert(t1.num == w1.num * x1.num);
    assert((w0.num >= 0 && x0.num > 0) ==> (w0.num * x0.num >= 0)) by (nonlinear_arith);
    assert((w1.num >= 0 && x1.num > 0) ==> (w1.num * x1.num >= 0)) by (nonlinear_arith);
    assert(w0.num * x0.num >= 0);
    assert(w1.num * x1.num >= 0);
    assert(t0.num >= 0);
    assert(t1.num >= 0);

    assert(t0.denom_nat() > 0);
    assert((t0.denom_nat() as int) > 0) by (nonlinear_arith);
    assert(t0.denom() == t0.denom_nat() as int);
    assert(t0.denom() > 0);
    assert(t1.denom_nat() > 0);
    assert((t1.denom_nat() as int) > 0) by (nonlinear_arith);
    assert(t1.denom() == t1.denom_nat() as int);
    assert(t1.denom() > 0);

    lemma_nonnegative_weights_summing_to_one_implies_some_positive(w0, w1);
    if z.lt_spec(w0) {
        lemma_scalar_zero_lt_iff_num_positive(w0);
        assert(w0.num > 0);
        assert((w0.num > 0 && x0.num > 0) ==> (w0.num * x0.num > 0)) by (nonlinear_arith);
        assert(w0.num * x0.num > 0);
        assert(t0.num > 0);
        assert((t0.num > 0 && t1.denom() > 0) ==> (t0.num * t1.denom() > 0)) by (nonlinear_arith);
        assert(t0.num * t1.denom() > 0);
        assert((t1.num >= 0 && t0.denom() > 0) ==> (t1.num * t0.denom() >= 0)) by (nonlinear_arith);
        assert(t1.num * t0.denom() >= 0);
        assert(out.num == t0.num * t1.denom() + t1.num * t0.denom());
        assert((t0.num * t1.denom() > 0 && t1.num * t0.denom() >= 0)
            ==> (t0.num * t1.denom() + t1.num * t0.denom() > 0)) by (nonlinear_arith);
        assert(t0.num * t1.denom() + t1.num * t0.denom() > 0);
        assert(out.num > 0);
    } else {
        assert(z.lt_spec(w1));
        lemma_scalar_zero_lt_iff_num_positive(w1);
        assert(w1.num > 0);
        assert((w1.num > 0 && x1.num > 0) ==> (w1.num * x1.num > 0)) by (nonlinear_arith);
        assert(w1.num * x1.num > 0);
        assert(t1.num > 0);
        assert((t0.num >= 0 && t1.denom() > 0) ==> (t0.num * t1.denom() >= 0)) by (nonlinear_arith);
        assert(t0.num * t1.denom() >= 0);
        assert((t1.num > 0 && t0.denom() > 0) ==> (t1.num * t0.denom() > 0)) by (nonlinear_arith);
        assert(t1.num * t0.denom() > 0);
        assert(out.num == t0.num * t1.denom() + t1.num * t0.denom());
        assert((t0.num * t1.denom() >= 0 && t1.num * t0.denom() > 0)
            ==> (t0.num * t1.denom() + t1.num * t0.denom() > 0)) by (nonlinear_arith);
        assert(t0.num * t1.denom() + t1.num * t0.denom() > 0);
        assert(out.num > 0);
    }

    lemma_scalar_zero_lt_iff_num_positive(out);
    assert(z.lt_spec(out));
}

pub proof fn lemma_ternary_convex_combination_of_positive_values_is_positive(
    w0: Scalar,
    w1: Scalar,
    w2: Scalar,
    x0: Scalar,
    x1: Scalar,
    x2: Scalar,
)
    requires
        Scalar::from_int_spec(0).le_spec(w0),
        Scalar::from_int_spec(0).le_spec(w1),
        Scalar::from_int_spec(0).le_spec(w2),
        w0.add_spec(w1).add_spec(w2).eqv_spec(Scalar::from_int_spec(1)),
        Scalar::from_int_spec(0).lt_spec(x0),
        Scalar::from_int_spec(0).lt_spec(x1),
        Scalar::from_int_spec(0).lt_spec(x2),
    ensures
        Scalar::from_int_spec(0).lt_spec(
            w0.mul_spec(x0).add_spec(w1.mul_spec(x1)).add_spec(w2.mul_spec(x2)),
        ),
{
    let z = Scalar::from_int_spec(0);
    let t0 = w0.mul_spec(x0);
    let t1 = w1.mul_spec(x1);
    let t2 = w2.mul_spec(x2);
    let s01 = t0.add_spec(t1);
    let out = s01.add_spec(t2);

    lemma_scalar_mul_of_nonnegative_and_positive_is_nonnegative(w0, x0);
    lemma_scalar_mul_of_nonnegative_and_positive_is_nonnegative(w1, x1);
    lemma_scalar_mul_of_nonnegative_and_positive_is_nonnegative(w2, x2);
    assert(z.le_spec(t0));
    assert(z.le_spec(t1));
    assert(z.le_spec(t2));

    lemma_nonnegative_three_weights_summing_to_one_implies_some_positive(w0, w1, w2);
    if z.lt_spec(w0) {
        lemma_scalar_mul_of_positive_and_positive_is_positive(w0, x0);
        assert(z.lt_spec(t0));
        lemma_scalar_add_of_positive_and_nonnegative_is_positive(t0, t1);
        assert(z.lt_spec(s01));
        lemma_scalar_add_of_positive_and_nonnegative_is_positive(s01, t2);
        assert(z.lt_spec(out));
    } else if z.lt_spec(w1) {
        lemma_scalar_mul_of_positive_and_positive_is_positive(w1, x1);
        assert(z.lt_spec(t1));
        lemma_scalar_add_of_nonnegative_and_positive_is_positive(t0, t1);
        assert(z.lt_spec(s01));
        lemma_scalar_add_of_positive_and_nonnegative_is_positive(s01, t2);
        assert(z.lt_spec(out));
    } else {
        assert(z.lt_spec(w2));
        lemma_scalar_mul_of_positive_and_positive_is_positive(w2, x2);
        assert(z.lt_spec(t2));
        lemma_scalar_add_of_nonnegative_and_nonnegative_is_nonnegative(t0, t1);
        assert(z.le_spec(s01));
        lemma_scalar_add_of_nonnegative_and_positive_is_positive(s01, t2);
        assert(z.lt_spec(out));
    }
}

pub proof fn lemma_quaternary_convex_combination_of_positive_values_is_positive(
    w0: Scalar,
    w1: Scalar,
    w2: Scalar,
    w3: Scalar,
    x0: Scalar,
    x1: Scalar,
    x2: Scalar,
    x3: Scalar,
)
    requires
        Scalar::from_int_spec(0).le_spec(w0),
        Scalar::from_int_spec(0).le_spec(w1),
        Scalar::from_int_spec(0).le_spec(w2),
        Scalar::from_int_spec(0).le_spec(w3),
        w0.add_spec(w1).add_spec(w2).add_spec(w3).eqv_spec(Scalar::from_int_spec(1)),
        Scalar::from_int_spec(0).lt_spec(x0),
        Scalar::from_int_spec(0).lt_spec(x1),
        Scalar::from_int_spec(0).lt_spec(x2),
        Scalar::from_int_spec(0).lt_spec(x3),
    ensures
        Scalar::from_int_spec(0).lt_spec(
            w0.mul_spec(x0).add_spec(w1.mul_spec(x1)).add_spec(w2.mul_spec(x2)).add_spec(w3.mul_spec(x3)),
        ),
{
    let z = Scalar::from_int_spec(0);
    let one = Scalar::from_int_spec(1);
    let t0 = w0.mul_spec(x0);
    let t1 = w1.mul_spec(x1);
    let t2 = w2.mul_spec(x2);
    let t3 = w3.mul_spec(x3);
    let s01 = t0.add_spec(t1);
    let s012 = s01.add_spec(t2);
    let out = s012.add_spec(t3);

    lemma_scalar_mul_of_nonnegative_and_positive_is_nonnegative(w0, x0);
    lemma_scalar_mul_of_nonnegative_and_positive_is_nonnegative(w1, x1);
    lemma_scalar_mul_of_nonnegative_and_positive_is_nonnegative(w2, x2);
    lemma_scalar_mul_of_nonnegative_and_positive_is_nonnegative(w3, x3);
    assert(z.le_spec(t0));
    assert(z.le_spec(t1));
    assert(z.le_spec(t2));
    assert(z.le_spec(t3));

    if z.lt_spec(w3) {
        lemma_scalar_mul_of_positive_and_positive_is_positive(w3, x3);
        assert(z.lt_spec(t3));

        lemma_scalar_add_of_nonnegative_and_nonnegative_is_nonnegative(t0, t1);
        assert(z.le_spec(s01));
        lemma_scalar_add_of_nonnegative_and_nonnegative_is_nonnegative(s01, t2);
        assert(z.le_spec(s012));
        lemma_scalar_add_of_nonnegative_and_positive_is_positive(s012, t3);
        assert(z.lt_spec(out));
    } else {
        let wsum = w0.add_spec(w1).add_spec(w2).add_spec(w3);
        assert(wsum.eqv_spec(one));

        lemma_scalar_zero_le_iff_num_nonnegative(w3);
        lemma_scalar_zero_lt_iff_num_positive(w3);
        assert(w3.num >= 0);
        assert(!z.lt_spec(w3));
        assert(!(w3.num > 0));
        assert((w3.num >= 0 && !(w3.num > 0)) ==> (w3.num == 0)) by (nonlinear_arith);
        assert(w3.num == 0);

        if z.lt_spec(w0) {
            lemma_scalar_mul_of_positive_and_positive_is_positive(w0, x0);
            assert(z.lt_spec(t0));
            lemma_scalar_add_of_positive_and_nonnegative_is_positive(t0, t1);
            assert(z.lt_spec(s01));
            lemma_scalar_add_of_positive_and_nonnegative_is_positive(s01, t2);
            assert(z.lt_spec(s012));
        } else if z.lt_spec(w1) {
            lemma_scalar_mul_of_positive_and_positive_is_positive(w1, x1);
            assert(z.lt_spec(t1));
            lemma_scalar_add_of_nonnegative_and_positive_is_positive(t0, t1);
            assert(z.lt_spec(s01));
            lemma_scalar_add_of_positive_and_nonnegative_is_positive(s01, t2);
            assert(z.lt_spec(s012));
        } else {
            if !z.lt_spec(w2) {
                let sum01 = w0.add_spec(w1);
                let sum012 = sum01.add_spec(w2);
                let sum = sum012.add_spec(w3);

                lemma_scalar_zero_le_iff_num_nonnegative(w0);
                lemma_scalar_zero_le_iff_num_nonnegative(w1);
                lemma_scalar_zero_le_iff_num_nonnegative(w2);
                lemma_scalar_zero_lt_iff_num_positive(w0);
                lemma_scalar_zero_lt_iff_num_positive(w1);
                lemma_scalar_zero_lt_iff_num_positive(w2);
                assert(w0.num >= 0);
                assert(w1.num >= 0);
                assert(w2.num >= 0);
                assert(!z.lt_spec(w0));
                assert(!z.lt_spec(w1));
                assert(!z.lt_spec(w2));
                assert(!(w0.num > 0));
                assert(!(w1.num > 0));
                assert(!(w2.num > 0));
                assert((w0.num >= 0 && !(w0.num > 0)) ==> (w0.num == 0)) by (nonlinear_arith);
                assert((w1.num >= 0 && !(w1.num > 0)) ==> (w1.num == 0)) by (nonlinear_arith);
                assert((w2.num >= 0 && !(w2.num > 0)) ==> (w2.num == 0)) by (nonlinear_arith);
                assert(w0.num == 0);
                assert(w1.num == 0);
                assert(w2.num == 0);
                assert(w3.num == 0);

                assert(sum01.num == w0.num * w1.denom() + w1.num * w0.denom());
                assert(sum01.num == 0 * w1.denom() + 0 * w0.denom());
                assert(0 * w1.denom() == 0) by (nonlinear_arith);
                assert(0 * w0.denom() == 0) by (nonlinear_arith);
                assert(sum01.num == 0 + 0);
                assert(sum01.num == 0);

                assert(sum012.num == sum01.num * w2.denom() + w2.num * sum01.denom());
                assert(sum012.num == 0 * w2.denom() + 0 * sum01.denom());
                assert(0 * w2.denom() == 0) by (nonlinear_arith);
                assert(0 * sum01.denom() == 0) by (nonlinear_arith);
                assert(sum012.num == 0 + 0);
                assert(sum012.num == 0);

                assert(sum.num == sum012.num * w3.denom() + w3.num * sum012.denom());
                assert(sum.num == 0 * w3.denom() + 0 * sum012.denom());
                assert(0 * w3.denom() == 0) by (nonlinear_arith);
                assert(0 * sum012.denom() == 0) by (nonlinear_arith);
                assert(sum.num == 0 + 0);
                assert(sum.num == 0);

                assert(sum.eqv_spec(one));
                Scalar::lemma_eqv_signum(sum, one);
                assert(one.num == 1);
                assert(one.signum() == 1);
                assert(sum.signum() == one.signum());
                assert(sum.signum() == 1);
                assert(sum.signum() == 0);
                assert(false);
            }
            assert(z.lt_spec(w2));
            lemma_scalar_mul_of_positive_and_positive_is_positive(w2, x2);
            assert(z.lt_spec(t2));
            lemma_scalar_add_of_nonnegative_and_nonnegative_is_nonnegative(t0, t1);
            assert(z.le_spec(s01));
            lemma_scalar_add_of_nonnegative_and_positive_is_positive(s01, t2);
            assert(z.lt_spec(s012));
        }

        lemma_scalar_add_of_positive_and_nonnegative_is_positive(s012, t3);
        assert(z.lt_spec(out));
    }
}

pub proof fn lemma_aabb_separation_implies_no_common_point(
    p: Point3,
    min_a: Point3,
    max_a: Point3,
    min_b: Point3,
    max_b: Point3,
)
    requires
        aabb_separated_on_some_axis_spec(min_a, max_a, min_b, max_b),
        point_in_aabb3_spec(p, min_a, max_a),
        point_in_aabb3_spec(p, min_b, max_b),
    ensures
        false,
{
    if max_a.x.lt_spec(min_b.x) {
        lemma_scalar_le_transitive(min_b.x, p.x, max_a.x);
        assert(min_b.x.le_spec(max_a.x));
        lemma_scalar_lt_incompatible_with_reverse_le(max_a.x, min_b.x);
    } else if max_b.x.lt_spec(min_a.x) {
        lemma_scalar_le_transitive(min_a.x, p.x, max_b.x);
        assert(min_a.x.le_spec(max_b.x));
        lemma_scalar_lt_incompatible_with_reverse_le(max_b.x, min_a.x);
    } else if max_a.y.lt_spec(min_b.y) {
        lemma_scalar_le_transitive(min_b.y, p.y, max_a.y);
        assert(min_b.y.le_spec(max_a.y));
        lemma_scalar_lt_incompatible_with_reverse_le(max_a.y, min_b.y);
    } else if max_b.y.lt_spec(min_a.y) {
        lemma_scalar_le_transitive(min_a.y, p.y, max_b.y);
        assert(min_a.y.le_spec(max_b.y));
        lemma_scalar_lt_incompatible_with_reverse_le(max_b.y, min_a.y);
    } else if max_a.z.lt_spec(min_b.z) {
        lemma_scalar_le_transitive(min_b.z, p.z, max_a.z);
        assert(min_b.z.le_spec(max_a.z));
        lemma_scalar_lt_incompatible_with_reverse_le(max_a.z, min_b.z);
    } else if max_b.z.lt_spec(min_a.z) {
        lemma_scalar_le_transitive(min_a.z, p.z, max_b.z);
        assert(min_a.z.le_spec(max_b.z));
        lemma_scalar_lt_incompatible_with_reverse_le(max_b.z, min_a.z);
    } else {
        assert(!max_a.x.lt_spec(min_b.x));
        assert(!max_b.x.lt_spec(min_a.x));
        assert(!max_a.y.lt_spec(min_b.y));
        assert(!max_b.y.lt_spec(min_a.y));
        assert(!max_a.z.lt_spec(min_b.z));
        assert(!max_b.z.lt_spec(min_a.z));
        assert(!aabb_separated_on_some_axis_spec(min_a, max_a, min_b, max_b));
        assert(false);
    }
}

pub proof fn lemma_aabb_separation_implies_disjoint_aabbs(
    min_a: Point3,
    max_a: Point3,
    min_b: Point3,
    max_b: Point3,
)
    requires
        aabb_separated_on_some_axis_spec(min_a, max_a, min_b, max_b),
    ensures
        forall|p: Point3|
            !(point_in_aabb3_spec(p, min_a, max_a) && point_in_aabb3_spec(p, min_b, max_b)),
{
    assert forall|p: Point3|
        !(point_in_aabb3_spec(p, min_a, max_a) && point_in_aabb3_spec(p, min_b, max_b))
    by {
        if point_in_aabb3_spec(p, min_a, max_a) && point_in_aabb3_spec(p, min_b, max_b) {
            lemma_aabb_separation_implies_no_common_point(p, min_a, max_a, min_b, max_b);
            assert(false);
        }
    }
}

pub proof fn lemma_aabb_separation_and_containment_implies_disjoint_sets(
    shape_a: spec_fn(Point3) -> bool,
    shape_b: spec_fn(Point3) -> bool,
    min_a: Point3,
    max_a: Point3,
    min_b: Point3,
    max_b: Point3,
)
    requires
        aabb_separated_on_some_axis_spec(min_a, max_a, min_b, max_b),
        shape_contained_in_aabb3_spec(shape_a, min_a, max_a),
        shape_contained_in_aabb3_spec(shape_b, min_b, max_b),
    ensures
        forall|p: Point3| #[trigger] shape_a(p) ==> !shape_b(p),
{
    assert forall|p: Point3| #[trigger] shape_a(p) ==> !shape_b(p) by {
        if shape_a(p) && shape_b(p) {
            assert(shape_contained_in_aabb3_spec(shape_a, min_a, max_a));
            assert(shape_contained_in_aabb3_spec(shape_b, min_b, max_b));
            assert(point_in_aabb3_spec(p, min_a, max_a));
            assert(point_in_aabb3_spec(p, min_b, max_b));
            lemma_aabb_separation_implies_no_common_point(p, min_a, max_a, min_b, max_b);
            assert(false);
        }
    }
}

pub proof fn lemma_witness_along_normal_implies_witness_offset(
    p0: Point3,
    p1: Point3,
    p2: Point3,
    witness: Point3,
    normal: Vec3,
)
    requires
        witness_along_normal_spec(p0, p1, p2, witness, normal),
    ensures
        witness.sub_spec(p0).eqv_spec(normal),
{
    let expected_witness = p0.add_vec_spec(normal);
    let witness_delta = witness.sub_spec(p0);
    let expected_delta = expected_witness.sub_spec(p0);

    assert(witness.eqv_spec(expected_witness));
    Scalar::lemma_eqv_sub_congruence(witness.x, expected_witness.x, p0.x, p0.x);
    Scalar::lemma_eqv_sub_congruence(witness.y, expected_witness.y, p0.y, p0.y);
    Scalar::lemma_eqv_sub_congruence(witness.z, expected_witness.z, p0.z, p0.z);
    assert(witness_delta.x.eqv_spec(expected_delta.x));
    assert(witness_delta.y.eqv_spec(expected_delta.y));
    assert(witness_delta.z.eqv_spec(expected_delta.z));

    Point3::lemma_add_then_sub_cancel(p0, normal);
    assert(expected_delta.eqv_spec(normal));
    assert(expected_delta.x.eqv_spec(normal.x));
    assert(expected_delta.y.eqv_spec(normal.y));
    assert(expected_delta.z.eqv_spec(normal.z));

    Scalar::lemma_eqv_transitive(witness_delta.x, expected_delta.x, normal.x);
    Scalar::lemma_eqv_transitive(witness_delta.y, expected_delta.y, normal.y);
    Scalar::lemma_eqv_transitive(witness_delta.z, expected_delta.z, normal.z);
    Vec3::lemma_eqv_from_components(witness_delta, normal);
    assert(witness_delta.eqv_spec(normal));
}

pub proof fn lemma_det3_linear_first_argument(u: Vec3, t: Vec3, v: Vec3, w: Vec3)
    ensures
        det3_spec(u.add_spec(t), v, w).eqv_spec(det3_spec(u, v, w).add_spec(det3_spec(t, v, w))),
{
    let lhs = det3_spec(u.add_spec(t), v, w);
    let uvw = det3_spec(u, v, w);
    let tvw = det3_spec(t, v, w);
    let c = v.cross_spec(w);

    Vec3::lemma_dot_linear_left(u, t, c);
    assert(u.add_spec(t).dot_spec(c).eqv_spec(u.dot_spec(c).add_spec(t.dot_spec(c))));
    assert(lhs == u.add_spec(t).dot_spec(c));
    assert(uvw == u.dot_spec(c));
    assert(tvw == t.dot_spec(c));
    assert(lhs.eqv_spec(uvw.add_spec(tvw)));
}

pub proof fn lemma_det3_linear_second_argument(u: Vec3, v: Vec3, t: Vec3, w: Vec3)
    ensures
        det3_spec(u, v.add_spec(t), w).eqv_spec(det3_spec(u, v, w).add_spec(det3_spec(u, t, w))),
{
    let lhs = det3_spec(u, v.add_spec(t), w);
    let uvw = det3_spec(u, v, w);
    let utw = det3_spec(u, t, w);
    let c = v.add_spec(t).cross_spec(w);
    let c_split = v.cross_spec(w).add_spec(t.cross_spec(w));

    Vec3::lemma_cross_linear_left(v, t, w);
    assert(c.eqv_spec(c_split));
    Vec3::lemma_dot_eqv_congruence(u, u, c, c_split);
    assert(u.dot_spec(c).eqv_spec(u.dot_spec(c_split)));
    Vec3::lemma_dot_linear_right(u, v.cross_spec(w), t.cross_spec(w));
    assert(u.dot_spec(c_split).eqv_spec(u.dot_spec(v.cross_spec(w)).add_spec(u.dot_spec(t.cross_spec(w)))));
    assert(lhs == u.dot_spec(c));
    assert(uvw == u.dot_spec(v.cross_spec(w)));
    assert(utw == u.dot_spec(t.cross_spec(w)));
    Scalar::lemma_eqv_transitive(
        lhs,
        u.dot_spec(c_split),
        u.dot_spec(v.cross_spec(w)).add_spec(u.dot_spec(t.cross_spec(w))),
    );
    assert(lhs.eqv_spec(uvw.add_spec(utw)));
}

pub proof fn lemma_det3_linear_third_argument(u: Vec3, v: Vec3, w: Vec3, t: Vec3)
    ensures
        det3_spec(u, v, w.add_spec(t)).eqv_spec(det3_spec(u, v, w).add_spec(det3_spec(u, v, t))),
{
    let lhs = det3_spec(u, v, w.add_spec(t));
    let uvw = det3_spec(u, v, w);
    let uvt = det3_spec(u, v, t);
    let c = v.cross_spec(w.add_spec(t));
    let c_split = v.cross_spec(w).add_spec(v.cross_spec(t));

    Vec3::lemma_cross_linear_right(v, w, t);
    assert(c.eqv_spec(c_split));
    Vec3::lemma_dot_eqv_congruence(u, u, c, c_split);
    assert(u.dot_spec(c).eqv_spec(u.dot_spec(c_split)));
    Vec3::lemma_dot_linear_right(u, v.cross_spec(w), v.cross_spec(t));
    assert(u.dot_spec(c_split).eqv_spec(u.dot_spec(v.cross_spec(w)).add_spec(u.dot_spec(v.cross_spec(t)))));
    assert(lhs == u.dot_spec(c));
    assert(uvw == u.dot_spec(v.cross_spec(w)));
    assert(uvt == u.dot_spec(v.cross_spec(t)));
    Scalar::lemma_eqv_transitive(
        lhs,
        u.dot_spec(c_split),
        u.dot_spec(v.cross_spec(w)).add_spec(u.dot_spec(v.cross_spec(t))),
    );
    assert(lhs.eqv_spec(uvw.add_spec(uvt)));
}

pub proof fn lemma_det3_swap_first_second_argument(u: Vec3, v: Vec3, w: Vec3)
    ensures
        det3_spec(v, u, w).eqv_spec(det3_spec(u, v, w).neg_spec()),
{
    let uvw = det3_spec(u, v, w);
    let vuw = det3_spec(v, u, w);

    Vec3::lemma_dot_cross_swap_first_two(u, v, w);
    assert(uvw.eqv_spec(vuw.neg_spec()));

    Scalar::lemma_eqv_neg_congruence(uvw, vuw.neg_spec());
    assert(uvw.neg_spec().eqv_spec(vuw.neg_spec().neg_spec()));
    Scalar::lemma_neg_involution(vuw);
    assert(vuw.neg_spec().neg_spec() == vuw);
    Scalar::lemma_eqv_reflexive(vuw);
    Scalar::lemma_eqv_transitive(uvw.neg_spec(), vuw.neg_spec().neg_spec(), vuw);
    assert(uvw.neg_spec().eqv_spec(vuw));
    Scalar::lemma_eqv_symmetric(uvw.neg_spec(), vuw);
    assert(vuw.eqv_spec(uvw.neg_spec()));
}

pub proof fn lemma_det3_swap_second_third_argument(u: Vec3, v: Vec3, w: Vec3)
    ensures
        det3_spec(u, w, v).eqv_spec(det3_spec(u, v, w).neg_spec()),
{
    let uvw = det3_spec(u, v, w);
    let uwv = det3_spec(u, w, v);
    let wv = w.cross_spec(v);
    let vw = v.cross_spec(w);

    Vec3::lemma_cross_antisymmetric(w, v);
    assert(wv == vw.neg_spec());

    Vec3::lemma_dot_eqv_congruence(u, u, wv, vw.neg_spec());
    assert(u.dot_spec(wv).eqv_spec(u.dot_spec(vw.neg_spec())));
    Vec3::lemma_dot_neg_right(u, vw);
    assert(u.dot_spec(vw.neg_spec()).eqv_spec(u.dot_spec(vw).neg_spec()));
    Scalar::lemma_eqv_transitive(u.dot_spec(wv), u.dot_spec(vw.neg_spec()), u.dot_spec(vw).neg_spec());
    assert(u.dot_spec(wv).eqv_spec(u.dot_spec(vw).neg_spec()));
    assert(uwv == u.dot_spec(wv));
    assert(uvw == u.dot_spec(vw));
    assert(uwv.eqv_spec(uvw.neg_spec()));
}

pub proof fn lemma_det3_swap_first_third_argument(u: Vec3, v: Vec3, w: Vec3)
    ensures
        det3_spec(w, v, u).eqv_spec(det3_spec(u, v, w).neg_spec()),
{
    let uvw = det3_spec(u, v, w);
    let vwu = det3_spec(v, w, u);
    let wvu = det3_spec(w, v, u);

    Vec3::lemma_dot_cross_cyclic(u, v, w);
    assert(uvw.eqv_spec(vwu));

    lemma_det3_swap_first_second_argument(v, w, u);
    assert(wvu.eqv_spec(vwu.neg_spec()));

    Scalar::lemma_eqv_neg_congruence(vwu, uvw);
    assert(vwu.neg_spec().eqv_spec(uvw.neg_spec()));
    Scalar::lemma_eqv_transitive(wvu, vwu.neg_spec(), uvw.neg_spec());
    assert(wvu.eqv_spec(uvw.neg_spec()));
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
