use vstd::prelude::*;
use vstd::arithmetic::mul::lemma_mul_by_zero_is_zero;
use crate::scalar::Scalar;
use crate::vec2::Vec2;

verus! {

pub struct Point2 {
    pub x: Scalar,
    pub y: Scalar,
}

impl Point2 {
    pub open spec fn from_ints_spec(x: int, y: int) -> Self {
        Point2 { x: Scalar::from_int_spec(x), y: Scalar::from_int_spec(y) }
    }

    pub open spec fn eqv_spec(self, rhs: Self) -> bool {
        self.x.eqv_spec(rhs.x) && self.y.eqv_spec(rhs.y)
    }

    pub proof fn from_ints(x: int, y: int) -> (p: Self)
        ensures
            p == Self::from_ints_spec(x, y),
    {
        let sx = Scalar::from_int(x);
        let sy = Scalar::from_int(y);
        Point2 { x: sx, y: sy }
    }

    pub open spec fn add_vec_spec(self, v: Vec2) -> Self {
        Point2 { x: self.x.add_spec(v.x), y: self.y.add_spec(v.y) }
    }

    pub proof fn add_vec(self, v: Vec2) -> (out: Self)
        ensures
            out == self.add_vec_spec(v),
    {
        let x = self.x.add(v.x);
        let y = self.y.add(v.y);
        Point2 { x, y }
    }

    pub open spec fn sub_spec(self, rhs: Self) -> Vec2 {
        Vec2 { x: self.x.sub_spec(rhs.x), y: self.y.sub_spec(rhs.y) }
    }

    pub proof fn sub(self, rhs: Self) -> (out: Vec2)
        ensures
            out == self.sub_spec(rhs),
    {
        let x = self.x.sub(rhs.x);
        let y = self.y.sub(rhs.y);
        Vec2 { x, y }
    }

    pub proof fn lemma_eqv_from_components(p: Self, q: Self)
        requires
            p.x.eqv_spec(q.x),
            p.y.eqv_spec(q.y),
        ensures
            p.eqv_spec(q),
    {
        assert(p.eqv_spec(q));
    }

    pub proof fn lemma_add_vec_zero_identity(p: Self)
        ensures
            p.add_vec_spec(Vec2::zero_spec()) == p,
    {
        let z = Vec2::zero_spec();
        let out = p.add_vec_spec(z);
        assert(z.x == Scalar::from_int_spec(0));
        assert(z.y == Scalar::from_int_spec(0));
        Scalar::lemma_add_zero_identity(p.x);
        Scalar::lemma_add_zero_identity(p.y);
        assert(out.x == p.x.add_spec(Scalar::from_int_spec(0)));
        assert(out.y == p.y.add_spec(Scalar::from_int_spec(0)));
        assert(out.x == p.x);
        assert(out.y == p.y);
        assert(out == p);
    }

    pub proof fn lemma_add_vec_associative(p: Self, u: Vec2, v: Vec2)
        ensures
            p.add_vec_spec(u).add_vec_spec(v).eqv_spec(p.add_vec_spec(u.add_spec(v))),
    {
        let lhs = p.add_vec_spec(u).add_vec_spec(v);
        let rhs = p.add_vec_spec(u.add_spec(v));
        Scalar::lemma_add_associative(p.x, u.x, v.x);
        Scalar::lemma_add_associative(p.y, u.y, v.y);
        assert(lhs.x == p.x.add_spec(u.x).add_spec(v.x));
        assert(rhs.x == p.x.add_spec(u.x.add_spec(v.x)));
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y == p.y.add_spec(u.y).add_spec(v.y));
        assert(rhs.y == p.y.add_spec(u.y.add_spec(v.y)));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_sub_then_add_cancel(p: Self, q: Self)
        ensures
            q.add_vec_spec(p.sub_spec(q)).eqv_spec(p),
    {
        let lhs = q.add_vec_spec(p.sub_spec(q));
        Scalar::lemma_sub_then_add_cancel(p.x, q.x);
        Scalar::lemma_sub_then_add_cancel(p.y, q.y);
        assert(lhs.x == q.x.add_spec(p.x.sub_spec(q.x)));
        assert(lhs.y == q.y.add_spec(p.y.sub_spec(q.y)));
        assert(lhs.x.eqv_spec(p.x));
        assert(lhs.y.eqv_spec(p.y));
        assert(lhs.eqv_spec(p));
    }

    pub proof fn lemma_add_then_sub_cancel(p: Self, v: Vec2)
        ensures
            p.add_vec_spec(v).sub_spec(p).eqv_spec(v),
    {
        let lhs = p.add_vec_spec(v).sub_spec(p);
        Scalar::lemma_add_then_sub_cancel(p.x, v.x);
        Scalar::lemma_add_then_sub_cancel(p.y, v.y);
        assert(lhs.x == p.x.add_spec(v.x).sub_spec(p.x));
        assert(lhs.y == p.y.add_spec(v.y).sub_spec(p.y));
        assert(lhs.x.eqv_spec(v.x));
        assert(lhs.y.eqv_spec(v.y));
        assert(lhs.eqv_spec(v));
    }

    pub proof fn lemma_add_vec_unique(p: Self, u: Vec2, v: Vec2)
        requires
            p.add_vec_spec(u).eqv_spec(p.add_vec_spec(v)),
        ensures
            u.eqv_spec(v),
    {
        let pu = p.add_vec_spec(u);
        let pv = p.add_vec_spec(v);
        assert(pu.x.eqv_spec(pv.x));
        assert(pu.y.eqv_spec(pv.y));
        assert(pu.x == p.x.add_spec(u.x));
        assert(pv.x == p.x.add_spec(v.x));
        assert(pu.y == p.y.add_spec(u.y));
        assert(pv.y == p.y.add_spec(v.y));
        Scalar::lemma_add_left_cancel_strong(u.x, v.x, p.x);
        Scalar::lemma_add_left_cancel_strong(u.y, v.y, p.y);
        assert(u.x.eqv_spec(v.x));
        assert(u.y.eqv_spec(v.y));
        assert(u.eqv_spec(v));
    }

    pub proof fn lemma_sub_self_zero_num(p: Self)
        ensures
            p.sub_spec(p).x.num == 0,
            p.sub_spec(p).y.num == 0,
    {
        let d = p.sub_spec(p);
        Scalar::lemma_sub_self_zero_num(p.x);
        Scalar::lemma_sub_self_zero_num(p.y);
        assert(d.x == p.x.sub_spec(p.x));
        assert(d.y == p.y.sub_spec(p.y));
        assert(d.x.num == 0);
        assert(d.y.num == 0);
    }

    pub proof fn lemma_sub_self_zero_signum(p: Self)
        ensures
            p.sub_spec(p).x.signum() == 0,
            p.sub_spec(p).y.signum() == 0,
    {
        let d = p.sub_spec(p);
        Self::lemma_sub_self_zero_num(p);
        Scalar::lemma_signum_zero_iff(d.x);
        Scalar::lemma_signum_zero_iff(d.y);
        assert((d.x.signum() == 0) == (d.x.num == 0));
        assert((d.y.signum() == 0) == (d.y.num == 0));
        assert(d.x.num == 0);
        assert(d.y.num == 0);
        assert(d.x.signum() == 0);
        assert(d.y.signum() == 0);
    }

    pub proof fn lemma_sub_antisymmetric(p: Self, q: Self)
        ensures
            p.sub_spec(q) == q.sub_spec(p).neg_spec(),
    {
        let lhs = p.sub_spec(q);
        let rhs = q.sub_spec(p).neg_spec();
        Scalar::lemma_sub_antisymmetric(p.x, q.x);
        Scalar::lemma_sub_antisymmetric(p.y, q.y);
        assert(lhs.x == p.x.sub_spec(q.x));
        assert(lhs.y == p.y.sub_spec(q.y));
        assert(rhs.x == q.x.sub_spec(p.x).neg_spec());
        assert(rhs.y == q.y.sub_spec(p.y).neg_spec());
        assert(lhs.x == rhs.x);
        assert(lhs.y == rhs.y);
    }

    pub proof fn lemma_sub_chain_eqv(p: Self, q: Self, r: Self)
        ensures
            p.sub_spec(r).x.eqv_spec(p.sub_spec(q).x.add_spec(q.sub_spec(r).x)),
            p.sub_spec(r).y.eqv_spec(p.sub_spec(q).y.add_spec(q.sub_spec(r).y)),
    {
        let pr = p.sub_spec(r);
        let pq = p.sub_spec(q);
        let qr = q.sub_spec(r);
        Scalar::lemma_eqv_sub_chain(p.x, q.x, r.x);
        Scalar::lemma_eqv_sub_chain(p.y, q.y, r.y);
        assert(pr.x == p.x.sub_spec(r.x));
        assert(pr.y == p.y.sub_spec(r.y));
        assert(pq.x == p.x.sub_spec(q.x));
        assert(pq.y == p.y.sub_spec(q.y));
        assert(qr.x == q.x.sub_spec(r.x));
        assert(qr.y == q.y.sub_spec(r.y));
        assert(pr.x.eqv_spec(pq.x.add_spec(qr.x)));
        assert(pr.y.eqv_spec(pq.y.add_spec(qr.y)));
    }
}

pub open spec fn dist2_spec(p: Point2, q: Point2) -> Scalar {
    p.sub_spec(q).norm2_spec()
}

pub proof fn lemma_dist2_is_sub_norm2(p: Point2, q: Point2)
    ensures
        dist2_spec(p, q) == p.sub_spec(q).norm2_spec(),
{
    assert(dist2_spec(p, q) == p.sub_spec(q).norm2_spec());
}

pub proof fn lemma_dist2_self_zero(p: Point2)
    ensures
        dist2_spec(p, p).eqv_spec(Scalar::from_int_spec(0)),
{
    let d = p.sub_spec(p);
    let n = dist2_spec(p, p);
    let z = Scalar::from_int_spec(0);
    let xx = d.x.mul_spec(d.x);
    let yy = d.y.mul_spec(d.y);

    Point2::lemma_sub_self_zero_num(p);
    assert(d.x.num == 0);
    assert(d.y.num == 0);
    Scalar::lemma_mul_left_zero_num(d.x, d.x);
    Scalar::lemma_mul_left_zero_num(d.y, d.y);
    assert(xx.num == 0);
    assert(yy.num == 0);

    assert(n == d.norm2_spec());
    assert(d.norm2_spec() == d.dot_spec(d));
    assert(d.dot_spec(d) == xx.add_spec(yy));
    assert(n == xx.add_spec(yy));
    assert(n.num == xx.num * yy.denom() + yy.num * xx.denom());
    assert(n.num == 0 * yy.denom() + 0 * xx.denom());
    lemma_mul_by_zero_is_zero(yy.denom());
    lemma_mul_by_zero_is_zero(xx.denom());
    assert(0 * yy.denom() == 0);
    assert(0 * xx.denom() == 0);
    assert(n.num == 0);

    assert(z.num == 0);
    assert(n.eqv_spec(z) == (n.num * z.denom() == z.num * n.denom()));
    assert(n.num * z.denom() == 0 * z.denom());
    assert(z.num * n.denom() == 0 * n.denom());
    lemma_mul_by_zero_is_zero(z.denom());
    lemma_mul_by_zero_is_zero(n.denom());
    assert(0 * z.denom() == 0);
    assert(0 * n.denom() == 0);
    assert(n.eqv_spec(z));
}

} // verus!
