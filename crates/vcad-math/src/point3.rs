use crate::scalar::Scalar;
use crate::vec3::Vec3;
use vstd::prelude::*;

verus! {

pub struct Point3 {
    pub x: Scalar,
    pub y: Scalar,
    pub z: Scalar,
}

impl Point3 {
    pub open spec fn from_ints_spec(x: int, y: int, z: int) -> Self {
        Point3 {
            x: Scalar::from_int_spec(x),
            y: Scalar::from_int_spec(y),
            z: Scalar::from_int_spec(z),
        }
    }

    pub proof fn from_ints(x: int, y: int, z: int) -> (p: Self)
        ensures
            p == Self::from_ints_spec(x, y, z),
    {
        Point3 {
            x: Scalar::from_int(x),
            y: Scalar::from_int(y),
            z: Scalar::from_int(z),
        }
    }

    pub open spec fn eqv_spec(self, rhs: Self) -> bool {
        self.x.eqv_spec(rhs.x) && self.y.eqv_spec(rhs.y) && self.z.eqv_spec(rhs.z)
    }

    pub open spec fn add_vec_spec(self, v: Vec3) -> Self {
        Point3 {
            x: self.x.add_spec(v.x),
            y: self.y.add_spec(v.y),
            z: self.z.add_spec(v.z),
        }
    }

    pub proof fn add_vec(self, v: Vec3) -> (out: Self)
        ensures
            out == self.add_vec_spec(v),
    {
        Point3 {
            x: self.x.add(v.x),
            y: self.y.add(v.y),
            z: self.z.add(v.z),
        }
    }

    pub open spec fn sub_spec(self, rhs: Self) -> Vec3 {
        Vec3 {
            x: self.x.sub_spec(rhs.x),
            y: self.y.sub_spec(rhs.y),
            z: self.z.sub_spec(rhs.z),
        }
    }

    pub proof fn sub(self, rhs: Self) -> (out: Vec3)
        ensures
            out == self.sub_spec(rhs),
    {
        Vec3 {
            x: self.x.sub(rhs.x),
            y: self.y.sub(rhs.y),
            z: self.z.sub(rhs.z),
        }
    }

    pub proof fn lemma_eqv_from_components(p: Self, q: Self)
        requires
            p.x.eqv_spec(q.x),
            p.y.eqv_spec(q.y),
            p.z.eqv_spec(q.z),
        ensures
            p.eqv_spec(q),
    {
        assert(p.eqv_spec(q));
    }

    pub proof fn lemma_add_vec_zero_identity(p: Self)
        ensures
            p.add_vec_spec(Vec3::zero_spec()) == p,
    {
        let z = Vec3::zero_spec();
        let out = p.add_vec_spec(z);
        Scalar::lemma_add_zero_identity(p.x);
        Scalar::lemma_add_zero_identity(p.y);
        Scalar::lemma_add_zero_identity(p.z);
        assert(out.x == p.x);
        assert(out.y == p.y);
        assert(out.z == p.z);
        assert(out == p);
    }

    pub proof fn lemma_add_vec_associative(p: Self, u: Vec3, v: Vec3)
        ensures
            p.add_vec_spec(u).add_vec_spec(v).eqv_spec(p.add_vec_spec(u.add_spec(v))),
    {
        let lhs = p.add_vec_spec(u).add_vec_spec(v);
        let rhs = p.add_vec_spec(u.add_spec(v));
        Scalar::lemma_add_associative(p.x, u.x, v.x);
        Scalar::lemma_add_associative(p.y, u.y, v.y);
        Scalar::lemma_add_associative(p.z, u.z, v.z);
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.z.eqv_spec(rhs.z));
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_sub_then_add_cancel(p: Self, q: Self)
        ensures
            q.add_vec_spec(p.sub_spec(q)).eqv_spec(p),
    {
        let lhs = q.add_vec_spec(p.sub_spec(q));
        Scalar::lemma_sub_then_add_cancel(p.x, q.x);
        Scalar::lemma_sub_then_add_cancel(p.y, q.y);
        Scalar::lemma_sub_then_add_cancel(p.z, q.z);
        assert(lhs.x.eqv_spec(p.x));
        assert(lhs.y.eqv_spec(p.y));
        assert(lhs.z.eqv_spec(p.z));
        assert(lhs.eqv_spec(p));
    }

    pub proof fn lemma_add_then_sub_cancel(p: Self, v: Vec3)
        ensures
            p.add_vec_spec(v).sub_spec(p).eqv_spec(v),
    {
        let lhs = p.add_vec_spec(v).sub_spec(p);
        Scalar::lemma_add_then_sub_cancel(p.x, v.x);
        Scalar::lemma_add_then_sub_cancel(p.y, v.y);
        Scalar::lemma_add_then_sub_cancel(p.z, v.z);
        assert(lhs.x.eqv_spec(v.x));
        assert(lhs.y.eqv_spec(v.y));
        assert(lhs.z.eqv_spec(v.z));
        assert(lhs.eqv_spec(v));
    }

    pub proof fn lemma_add_vec_unique(p: Self, u: Vec3, v: Vec3)
        requires
            p.add_vec_spec(u).eqv_spec(p.add_vec_spec(v)),
        ensures
            u.eqv_spec(v),
    {
        let pu = p.add_vec_spec(u);
        let pv = p.add_vec_spec(v);
        assert(pu.x.eqv_spec(pv.x));
        assert(pu.y.eqv_spec(pv.y));
        assert(pu.z.eqv_spec(pv.z));
        Scalar::lemma_add_left_cancel_strong(u.x, v.x, p.x);
        Scalar::lemma_add_left_cancel_strong(u.y, v.y, p.y);
        Scalar::lemma_add_left_cancel_strong(u.z, v.z, p.z);
        assert(u.x.eqv_spec(v.x));
        assert(u.y.eqv_spec(v.y));
        assert(u.z.eqv_spec(v.z));
        assert(u.eqv_spec(v));
    }

    pub proof fn lemma_sub_self_zero_num(p: Self)
        ensures
            p.sub_spec(p).x.num == 0,
            p.sub_spec(p).y.num == 0,
            p.sub_spec(p).z.num == 0,
    {
        let d = p.sub_spec(p);
        Scalar::lemma_sub_self_zero_num(p.x);
        Scalar::lemma_sub_self_zero_num(p.y);
        Scalar::lemma_sub_self_zero_num(p.z);
        assert(d.x.num == 0);
        assert(d.y.num == 0);
        assert(d.z.num == 0);
    }

    pub proof fn lemma_sub_antisymmetric(p: Self, q: Self)
        ensures
            p.sub_spec(q) == q.sub_spec(p).neg_spec(),
    {
        Scalar::lemma_sub_antisymmetric(p.x, q.x);
        Scalar::lemma_sub_antisymmetric(p.y, q.y);
        Scalar::lemma_sub_antisymmetric(p.z, q.z);
        assert(p.sub_spec(q).x == q.sub_spec(p).neg_spec().x);
        assert(p.sub_spec(q).y == q.sub_spec(p).neg_spec().y);
        assert(p.sub_spec(q).z == q.sub_spec(p).neg_spec().z);
        assert(p.sub_spec(q) == q.sub_spec(p).neg_spec());
    }

    pub proof fn lemma_sub_chain_eqv(p: Self, q: Self, r: Self)
        ensures
            p.sub_spec(r).x.eqv_spec(p.sub_spec(q).x.add_spec(q.sub_spec(r).x)),
            p.sub_spec(r).y.eqv_spec(p.sub_spec(q).y.add_spec(q.sub_spec(r).y)),
            p.sub_spec(r).z.eqv_spec(p.sub_spec(q).z.add_spec(q.sub_spec(r).z)),
    {
        Scalar::lemma_eqv_sub_chain(p.x, q.x, r.x);
        Scalar::lemma_eqv_sub_chain(p.y, q.y, r.y);
        Scalar::lemma_eqv_sub_chain(p.z, q.z, r.z);
    }
}

pub open spec fn dist2_spec(p: Point3, q: Point3) -> Scalar {
    p.sub_spec(q).norm2_spec()
}

pub proof fn lemma_dist2_is_sub_norm2(p: Point3, q: Point3)
    ensures
        dist2_spec(p, q) == p.sub_spec(q).norm2_spec(),
{
    assert(dist2_spec(p, q) == p.sub_spec(q).norm2_spec());
}

pub proof fn lemma_sub_translation_invariant(p: Point3, q: Point3, t: Vec3)
    ensures
        p.add_vec_spec(t).sub_spec(q.add_vec_spec(t)).eqv_spec(p.sub_spec(q)),
{
    let lhs = p.add_vec_spec(t).sub_spec(q.add_vec_spec(t));
    let rhs = p.sub_spec(q);
    Scalar::lemma_eqv_sub_cancel_right(p.x, q.x, t.x);
    Scalar::lemma_eqv_sub_cancel_right(p.y, q.y, t.y);
    Scalar::lemma_eqv_sub_cancel_right(p.z, q.z, t.z);
    assert(lhs.x.eqv_spec(rhs.x));
    assert(lhs.y.eqv_spec(rhs.y));
    assert(lhs.z.eqv_spec(rhs.z));
    assert(lhs.eqv_spec(rhs));
}

pub proof fn lemma_dist2_translation_invariant(p: Point3, q: Point3, t: Vec3)
    ensures
        dist2_spec(p.add_vec_spec(t), q.add_vec_spec(t)).eqv_spec(dist2_spec(p, q)),
{
    let lsub = p.add_vec_spec(t).sub_spec(q.add_vec_spec(t));
    let rsub = p.sub_spec(q);
    lemma_sub_translation_invariant(p, q, t);
    assert(lsub.eqv_spec(rsub));
    Vec3::lemma_norm2_eqv_congruence(lsub, rsub);
    assert(lsub.norm2_spec().eqv_spec(rsub.norm2_spec()));
    assert(dist2_spec(p.add_vec_spec(t), q.add_vec_spec(t)).eqv_spec(dist2_spec(p, q)));
}

pub proof fn lemma_dist2_symmetric(p: Point3, q: Point3)
    ensures
        dist2_spec(p, q).eqv_spec(dist2_spec(q, p)),
{
    let d = p.sub_spec(q);
    let dq = q.sub_spec(p);
    Point3::lemma_sub_antisymmetric(q, p);
    assert(dq == d.neg_spec());
    Vec3::lemma_norm2_neg_invariant(d);
    assert(d.neg_spec().norm2_spec().eqv_spec(d.norm2_spec()));
    assert(dq.norm2_spec() == d.neg_spec().norm2_spec());
    assert(dist2_spec(p, q) == d.norm2_spec());
    assert(dist2_spec(q, p) == dq.norm2_spec());
    Scalar::lemma_eqv_symmetric(d.neg_spec().norm2_spec(), d.norm2_spec());
    assert(d.norm2_spec().eqv_spec(d.neg_spec().norm2_spec()));
    Scalar::lemma_eqv_transitive(dist2_spec(p, q), d.norm2_spec(), d.neg_spec().norm2_spec());
    assert(dist2_spec(p, q).eqv_spec(d.neg_spec().norm2_spec()));
    assert(dist2_spec(q, p).eqv_spec(d.neg_spec().norm2_spec()));
    Scalar::lemma_eqv_symmetric(dist2_spec(q, p), d.neg_spec().norm2_spec());
    assert(d.neg_spec().norm2_spec().eqv_spec(dist2_spec(q, p)));
    Scalar::lemma_eqv_transitive(dist2_spec(p, q), d.neg_spec().norm2_spec(), dist2_spec(q, p));
    assert(dist2_spec(p, q).eqv_spec(dist2_spec(q, p)));
}

pub proof fn lemma_dist2_nonnegative(p: Point3, q: Point3)
    ensures
        Scalar::from_int_spec(0).le_spec(dist2_spec(p, q)),
{
    let d = p.sub_spec(q);
    let n = dist2_spec(p, q);
    Vec3::lemma_norm2_nonnegative(d);
    assert(n == d.norm2_spec());
    assert(Scalar::from_int_spec(0).le_spec(d.norm2_spec()));
    assert(Scalar::from_int_spec(0).le_spec(n));
}

pub proof fn lemma_dist2_zero_iff_equal_points(p: Point3, q: Point3)
    ensures
        dist2_spec(p, q).eqv_spec(Scalar::from_int_spec(0)) == p.eqv_spec(q),
{
    let d = p.sub_spec(q);
    let n = dist2_spec(p, q);
    let z = Scalar::from_int_spec(0);
    let zv = Vec3::zero_spec();

    Vec3::lemma_norm2_zero_iff_zero(d);
    assert(n == d.norm2_spec());
    assert(d.norm2_spec().eqv_spec(z) == d.eqv_spec(zv));
    assert(n.eqv_spec(z) == d.eqv_spec(zv));

    if d.eqv_spec(zv) {
        assert(d.x.eqv_spec(zv.x));
        assert(d.y.eqv_spec(zv.y));
        assert(d.z.eqv_spec(zv.z));
        assert(zv.x == z);
        assert(zv.y == z);
        assert(zv.z == z);
        assert(d.x == p.x.sub_spec(q.x));
        assert(d.y == p.y.sub_spec(q.y));
        assert(d.z == p.z.sub_spec(q.z));
        Scalar::lemma_sub_eqv_zero_iff_eqv(p.x, q.x);
        Scalar::lemma_sub_eqv_zero_iff_eqv(p.y, q.y);
        Scalar::lemma_sub_eqv_zero_iff_eqv(p.z, q.z);
        assert(p.x.sub_spec(q.x).eqv_spec(z) == p.x.eqv_spec(q.x));
        assert(p.y.sub_spec(q.y).eqv_spec(z) == p.y.eqv_spec(q.y));
        assert(p.z.sub_spec(q.z).eqv_spec(z) == p.z.eqv_spec(q.z));
        assert(p.x.eqv_spec(q.x));
        assert(p.y.eqv_spec(q.y));
        assert(p.z.eqv_spec(q.z));
        assert(p.eqv_spec(q));
    }

    if p.eqv_spec(q) {
        assert(p.x.eqv_spec(q.x));
        assert(p.y.eqv_spec(q.y));
        assert(p.z.eqv_spec(q.z));
        Scalar::lemma_sub_eqv_zero_iff_eqv(p.x, q.x);
        Scalar::lemma_sub_eqv_zero_iff_eqv(p.y, q.y);
        Scalar::lemma_sub_eqv_zero_iff_eqv(p.z, q.z);
        assert(p.x.sub_spec(q.x).eqv_spec(z) == p.x.eqv_spec(q.x));
        assert(p.y.sub_spec(q.y).eqv_spec(z) == p.y.eqv_spec(q.y));
        assert(p.z.sub_spec(q.z).eqv_spec(z) == p.z.eqv_spec(q.z));
        assert(p.x.sub_spec(q.x).eqv_spec(z));
        assert(p.y.sub_spec(q.y).eqv_spec(z));
        assert(p.z.sub_spec(q.z).eqv_spec(z));
        assert(d.x == p.x.sub_spec(q.x));
        assert(d.y == p.y.sub_spec(q.y));
        assert(d.z == p.z.sub_spec(q.z));
        assert(zv.x == z);
        assert(zv.y == z);
        assert(zv.z == z);
        assert(d.x.eqv_spec(zv.x));
        assert(d.y.eqv_spec(zv.y));
        assert(d.z.eqv_spec(zv.z));
        assert(d.eqv_spec(zv));
    }

    assert((n.eqv_spec(z)) == p.eqv_spec(q));
}

pub proof fn lemma_dist2_self_zero(p: Point3)
    ensures
        dist2_spec(p, p).eqv_spec(Scalar::from_int_spec(0)),
{
    let z = Scalar::from_int_spec(0);
    lemma_dist2_zero_iff_equal_points(p, p);
    Scalar::lemma_eqv_reflexive(p.x);
    Scalar::lemma_eqv_reflexive(p.y);
    Scalar::lemma_eqv_reflexive(p.z);
    assert(p.eqv_spec(p));
    assert(dist2_spec(p, p).eqv_spec(z) == p.eqv_spec(p));
    assert(dist2_spec(p, p).eqv_spec(z));
}

} // verus!
