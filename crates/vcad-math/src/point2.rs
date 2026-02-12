use vstd::prelude::*;
use crate::scalar::Scalar;
use crate::vec2::Vec2;

verus! {

pub struct Point2 {
    pub x: Scalar,
    pub y: Scalar,
}

impl Point2 {
    pub open spec fn from_ints_spec(x: int, y: int) -> Self {
        Point2 { x: Scalar { value: x }, y: Scalar { value: y } }
    }

    pub proof fn lemma_eq_from_component_ints(a: Self, b: Self)
        requires
            a.x.as_int() == b.x.as_int(),
            a.y.as_int() == b.y.as_int(),
        ensures
            a == b,
    {
        Scalar::lemma_eq_from_as_int_internal(a.x, b.x);
        Scalar::lemma_eq_from_as_int_internal(a.y, b.y);
        assert(a.x == b.x);
        assert(a.y == b.y);
    }

    pub proof fn from_ints(x: int, y: int) -> (p: Self)
        ensures
            p == Self::from_ints_spec(x, y),
    {
        Point2 { x: Scalar { value: x }, y: Scalar { value: y } }
    }

    pub open spec fn add_vec_spec(self, v: Vec2) -> Self {
        Point2 { x: self.x.add_spec(v.x), y: self.y.add_spec(v.y) }
    }

    pub proof fn add_vec(self, v: Vec2) -> (out: Self)
        ensures
            out == self.add_vec_spec(v),
    {
        Point2 {
            x: Scalar { value: self.x.value + v.x.value },
            y: Scalar { value: self.y.value + v.y.value },
        }
    }

    pub open spec fn sub_spec(self, rhs: Self) -> Vec2 {
        Vec2 { x: self.x.sub_spec(rhs.x), y: self.y.sub_spec(rhs.y) }
    }

    pub proof fn sub(self, rhs: Self) -> (out: Vec2)
        ensures
            out == self.sub_spec(rhs),
    {
        Vec2 {
            x: Scalar { value: self.x.value - rhs.x.value },
            y: Scalar { value: self.y.value - rhs.y.value },
        }
    }

    pub proof fn lemma_add_then_sub_cancel(p: Self, v: Vec2)
        ensures
            p.add_vec_spec(v).sub_spec(p).x.as_int() == v.x.as_int(),
            p.add_vec_spec(v).sub_spec(p).y.as_int() == v.y.as_int(),
    {
        assert((p.x.as_int() + v.x.as_int()) - p.x.as_int() == v.x.as_int()) by (nonlinear_arith);
        assert((p.y.as_int() + v.y.as_int()) - p.y.as_int() == v.y.as_int()) by (nonlinear_arith);
    }

    pub proof fn lemma_sub_then_add_cancel(p: Self, q: Self)
        ensures
            p.add_vec_spec(q.sub_spec(p)).x.as_int() == q.x.as_int(),
            p.add_vec_spec(q.sub_spec(p)).y.as_int() == q.y.as_int(),
    {
        assert(p.x.as_int() + (q.x.as_int() - p.x.as_int()) == q.x.as_int()) by (nonlinear_arith);
        assert(p.y.as_int() + (q.y.as_int() - p.y.as_int()) == q.y.as_int()) by (nonlinear_arith);
    }

    pub proof fn lemma_sub_translation_invariant(p: Self, q: Self, t: Vec2)
        ensures
            p.add_vec_spec(t).sub_spec(q.add_vec_spec(t)).x.as_int() == p.sub_spec(q).x.as_int(),
            p.add_vec_spec(t).sub_spec(q.add_vec_spec(t)).y.as_int() == p.sub_spec(q).y.as_int(),
    {
        assert((p.x.as_int() + t.x.as_int()) - (q.x.as_int() + t.x.as_int())
            == p.x.as_int() - q.x.as_int()) by (nonlinear_arith);
        assert((p.y.as_int() + t.y.as_int()) - (q.y.as_int() + t.y.as_int())
            == p.y.as_int() - q.y.as_int()) by (nonlinear_arith);
    }

    pub proof fn lemma_add_vec_zero_identity(p: Self)
        ensures
            p.add_vec_spec(Vec2::zero_spec()) == p,
    {
        assert(p.x.as_int() + 0 == p.x.as_int()) by (nonlinear_arith);
        assert(p.y.as_int() + 0 == p.y.as_int()) by (nonlinear_arith);
    }

    pub proof fn lemma_add_vec_associative(p: Self, u: Vec2, v: Vec2)
        ensures
            p.add_vec_spec(u).add_vec_spec(v) == p.add_vec_spec(u.add_spec(v)),
    {
        assert((p.x.as_int() + u.x.as_int()) + v.x.as_int() == p.x.as_int() + (u.x.as_int() + v.x.as_int())) by (nonlinear_arith);
        assert((p.y.as_int() + u.y.as_int()) + v.y.as_int() == p.y.as_int() + (u.y.as_int() + v.y.as_int())) by (nonlinear_arith);
    }

    pub proof fn lemma_add_vec_unique(p: Self, u: Vec2, v: Vec2)
        ensures
            p.add_vec_spec(u) == p.add_vec_spec(v) ==> u == v,
    {
        if p.add_vec_spec(u) == p.add_vec_spec(v) {
            assert(p.x.add_spec(u.x).as_int() == p.x.add_spec(v.x).as_int());
            assert(p.y.add_spec(u.y).as_int() == p.y.add_spec(v.y).as_int());
            Scalar::lemma_add_left_cancel_strong(u.x, v.x, p.x);
            Scalar::lemma_add_left_cancel_strong(u.y, v.y, p.y);
            assert(u.x.as_int() == v.x.as_int());
            assert(u.y.as_int() == v.y.as_int());
            Vec2::lemma_eq_from_component_ints(u, v);
        }
    }
}

pub open spec fn dist2_spec(p: Point2, q: Point2) -> Scalar {
    p.sub_spec(q).norm2_spec()
}

pub proof fn lemma_dist2_symmetric(p: Point2, q: Point2)
    ensures
        dist2_spec(p, q) == dist2_spec(q, p),
{
    let lhs = dist2_spec(p, q);
    let rhs = dist2_spec(q, p);
    assert(lhs.as_int()
        == (p.x.as_int() - q.x.as_int()) * (p.x.as_int() - q.x.as_int())
            + (p.y.as_int() - q.y.as_int()) * (p.y.as_int() - q.y.as_int()));
    assert(rhs.as_int()
        == (q.x.as_int() - p.x.as_int()) * (q.x.as_int() - p.x.as_int())
            + (q.y.as_int() - p.y.as_int()) * (q.y.as_int() - p.y.as_int()));
    assert(
        (p.x.as_int() - q.x.as_int()) * (p.x.as_int() - q.x.as_int())
            + (p.y.as_int() - q.y.as_int()) * (p.y.as_int() - q.y.as_int())
        == (q.x.as_int() - p.x.as_int()) * (q.x.as_int() - p.x.as_int())
            + (q.y.as_int() - p.y.as_int()) * (q.y.as_int() - p.y.as_int())
    ) by (nonlinear_arith);
    assert(lhs.as_int() == rhs.as_int());
    Scalar::lemma_eq_from_as_int_internal(lhs, rhs);
}

pub proof fn lemma_dist2_translation_invariant(p: Point2, q: Point2, t: Vec2)
    ensures
        dist2_spec(p.add_vec_spec(t), q.add_vec_spec(t)) == dist2_spec(p, q),
{
    let lhs = dist2_spec(p.add_vec_spec(t), q.add_vec_spec(t));
    let rhs = dist2_spec(p, q);
    assert(lhs.as_int()
        == ((p.x.as_int() + t.x.as_int()) - (q.x.as_int() + t.x.as_int()))
            * ((p.x.as_int() + t.x.as_int()) - (q.x.as_int() + t.x.as_int()))
            + ((p.y.as_int() + t.y.as_int()) - (q.y.as_int() + t.y.as_int()))
                * ((p.y.as_int() + t.y.as_int()) - (q.y.as_int() + t.y.as_int())));
    assert(rhs.as_int()
        == (p.x.as_int() - q.x.as_int()) * (p.x.as_int() - q.x.as_int())
            + (p.y.as_int() - q.y.as_int()) * (p.y.as_int() - q.y.as_int()));
    assert(
        ((p.x.as_int() + t.x.as_int()) - (q.x.as_int() + t.x.as_int()))
            * ((p.x.as_int() + t.x.as_int()) - (q.x.as_int() + t.x.as_int()))
            + ((p.y.as_int() + t.y.as_int()) - (q.y.as_int() + t.y.as_int()))
                * ((p.y.as_int() + t.y.as_int()) - (q.y.as_int() + t.y.as_int()))
        == (p.x.as_int() - q.x.as_int()) * (p.x.as_int() - q.x.as_int())
            + (p.y.as_int() - q.y.as_int()) * (p.y.as_int() - q.y.as_int())
    ) by (nonlinear_arith);
    assert(lhs.as_int() == rhs.as_int());
    Scalar::lemma_eq_from_as_int_internal(lhs, rhs);
}

pub proof fn lemma_dist2_nonnegative(p: Point2, q: Point2)
    ensures
        dist2_spec(p, q).as_int() >= 0,
{
    Vec2::lemma_norm2_nonnegative(p.sub_spec(q));
}

pub proof fn lemma_dist2_is_sub_norm2(p: Point2, q: Point2)
    ensures
        dist2_spec(p, q) == p.sub_spec(q).norm2_spec(),
{
}

pub proof fn lemma_dist2_self_zero(p: Point2)
    ensures
        dist2_spec(p, p).as_int() == 0,
{
    assert(dist2_spec(p, p).as_int() == (p.x.as_int() - p.x.as_int()) * (p.x.as_int() - p.x.as_int())
        + (p.y.as_int() - p.y.as_int()) * (p.y.as_int() - p.y.as_int()));
    assert(dist2_spec(p, p).as_int() == 0) by (nonlinear_arith);
}

pub proof fn lemma_dist2_zero_iff_equal_points(p: Point2, q: Point2)
    ensures
        (dist2_spec(p, q).as_int() == 0) == (p == q),
{
    if dist2_spec(p, q).as_int() == 0 {
        assert(dist2_spec(p, q).as_int()
            == (p.x.as_int() - q.x.as_int()) * (p.x.as_int() - q.x.as_int())
            + (p.y.as_int() - q.y.as_int()) * (p.y.as_int() - q.y.as_int()));
        assert((p.x.as_int() - q.x.as_int()) * (p.x.as_int() - q.x.as_int()) >= 0) by (nonlinear_arith);
        assert((p.y.as_int() - q.y.as_int()) * (p.y.as_int() - q.y.as_int()) >= 0) by (nonlinear_arith);
        assert(
            (((p.x.as_int() - q.x.as_int()) * (p.x.as_int() - q.x.as_int()))
                + ((p.y.as_int() - q.y.as_int()) * (p.y.as_int() - q.y.as_int())) == 0)
            ==> (
                (p.x.as_int() - q.x.as_int()) * (p.x.as_int() - q.x.as_int()) == 0
                && (p.y.as_int() - q.y.as_int()) * (p.y.as_int() - q.y.as_int()) == 0
            )
        ) by (nonlinear_arith);
        assert(
            (p.x.as_int() - q.x.as_int()) * (p.x.as_int() - q.x.as_int()) == 0
            && (p.y.as_int() - q.y.as_int()) * (p.y.as_int() - q.y.as_int()) == 0
        );
        assert(((p.x.as_int() - q.x.as_int()) * (p.x.as_int() - q.x.as_int()) == 0)
            ==> (p.x.as_int() - q.x.as_int() == 0)) by (nonlinear_arith);
        assert(((p.y.as_int() - q.y.as_int()) * (p.y.as_int() - q.y.as_int()) == 0)
            ==> (p.y.as_int() - q.y.as_int() == 0)) by (nonlinear_arith);
        assert(p.x.as_int() - q.x.as_int() == 0);
        assert(p.y.as_int() - q.y.as_int() == 0);
        assert(p.x.as_int() == q.x.as_int());
        assert(p.y.as_int() == q.y.as_int());
        Point2::lemma_eq_from_component_ints(p, q);
    }

    if p == q {
        lemma_dist2_self_zero(p);
        assert(dist2_spec(p, q).as_int() == dist2_spec(p, p).as_int());
        assert(dist2_spec(p, q).as_int() == 0);
    }
}

} // verus!
