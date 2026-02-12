use vstd::prelude::*;
use vstd::arithmetic::mul::lemma_mul_by_zero_is_zero;
use crate::scalar::Scalar;

verus! {

pub struct Vec2 {
    pub x: Scalar,
    pub y: Scalar,
}

impl Vec2 {
    pub open spec fn from_ints_spec(x: int, y: int) -> Self {
        Vec2 { x: Scalar::from_int_spec(x), y: Scalar::from_int_spec(y) }
    }

    pub proof fn from_ints(x: int, y: int) -> (v: Self)
        ensures
            v == Self::from_ints_spec(x, y),
    {
        let sx = Scalar::from_int(x);
        let sy = Scalar::from_int(y);
        Vec2 { x: sx, y: sy }
    }

    pub open spec fn zero_spec() -> Self {
        Self::from_ints_spec(0, 0)
    }

    pub open spec fn eqv_spec(self, rhs: Self) -> bool {
        self.x.eqv_spec(rhs.x) && self.y.eqv_spec(rhs.y)
    }

    pub open spec fn add_spec(self, rhs: Self) -> Self {
        Vec2 { x: self.x.add_spec(rhs.x), y: self.y.add_spec(rhs.y) }
    }

    pub proof fn add(self, rhs: Self) -> (out: Self)
        ensures
            out == self.add_spec(rhs),
    {
        let x = self.x.add(rhs.x);
        let y = self.y.add(rhs.y);
        Vec2 { x, y }
    }

    pub open spec fn neg_spec(self) -> Self {
        Vec2 { x: self.x.neg_spec(), y: self.y.neg_spec() }
    }

    pub proof fn neg(self) -> (out: Self)
        ensures
            out == self.neg_spec(),
    {
        let x = self.x.neg();
        let y = self.y.neg();
        Vec2 { x, y }
    }

    pub open spec fn sub_spec(self, rhs: Self) -> Self {
        Vec2 { x: self.x.sub_spec(rhs.x), y: self.y.sub_spec(rhs.y) }
    }

    pub proof fn sub(self, rhs: Self) -> (out: Self)
        ensures
            out == self.sub_spec(rhs),
    {
        let x = self.x.sub(rhs.x);
        let y = self.y.sub(rhs.y);
        Vec2 { x, y }
    }

    pub open spec fn scale_spec(self, k: Scalar) -> Self {
        Vec2 { x: self.x.mul_spec(k), y: self.y.mul_spec(k) }
    }

    pub proof fn scale(self, k: Scalar) -> (out: Self)
        ensures
            out == self.scale_spec(k),
    {
        let x = self.x.mul(k);
        let y = self.y.mul(k);
        Vec2 { x, y }
    }

    pub open spec fn dot_spec(self, rhs: Self) -> Scalar {
        self.x.mul_spec(rhs.x).add_spec(self.y.mul_spec(rhs.y))
    }

    pub proof fn dot(self, rhs: Self) -> (out: Scalar)
        ensures
            out == self.dot_spec(rhs),
    {
        let xx = self.x.mul(rhs.x);
        let yy = self.y.mul(rhs.y);
        xx.add(yy)
    }

    pub open spec fn cross_spec(self, rhs: Self) -> Scalar {
        self.x.mul_spec(rhs.y).sub_spec(self.y.mul_spec(rhs.x))
    }

    pub proof fn cross(self, rhs: Self) -> (out: Scalar)
        ensures
            out == self.cross_spec(rhs),
    {
        let xy = self.x.mul(rhs.y);
        let yx = self.y.mul(rhs.x);
        xy.sub(yx)
    }

    pub open spec fn norm2_spec(self) -> Scalar {
        self.dot_spec(self)
    }

    pub proof fn lemma_eqv_from_components(a: Self, b: Self)
        requires
            a.x.eqv_spec(b.x),
            a.y.eqv_spec(b.y),
        ensures
            a.eqv_spec(b),
    {
        assert(a.eqv_spec(b));
    }

    pub proof fn lemma_eqv_reflexive(a: Self)
        ensures
            a.eqv_spec(a),
    {
        Scalar::lemma_eqv_reflexive(a.x);
        Scalar::lemma_eqv_reflexive(a.y);
        assert(a.eqv_spec(a));
    }

    pub proof fn lemma_add_commutative(a: Self, b: Self)
        ensures
            a.add_spec(b).eqv_spec(b.add_spec(a)),
    {
        let lhs = a.add_spec(b);
        let rhs = b.add_spec(a);
        Scalar::lemma_add_commutative(a.x, b.x);
        Scalar::lemma_add_commutative(a.y, b.y);
        assert(lhs.x == a.x.add_spec(b.x));
        assert(rhs.x == b.x.add_spec(a.x));
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y == a.y.add_spec(b.y));
        assert(rhs.y == b.y.add_spec(a.y));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_add_associative(a: Self, b: Self, c: Self)
        ensures
            a.add_spec(b).add_spec(c).eqv_spec(a.add_spec(b.add_spec(c))),
    {
        let lhs = a.add_spec(b).add_spec(c);
        let rhs = a.add_spec(b.add_spec(c));
        Scalar::lemma_add_associative(a.x, b.x, c.x);
        Scalar::lemma_add_associative(a.y, b.y, c.y);
        assert(lhs.x == a.x.add_spec(b.x).add_spec(c.x));
        assert(rhs.x == a.x.add_spec(b.x.add_spec(c.x)));
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y == a.y.add_spec(b.y).add_spec(c.y));
        assert(rhs.y == a.y.add_spec(b.y.add_spec(c.y)));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_add_zero_identity(a: Self)
        ensures
            a.add_spec(Self::zero_spec()) == a,
            Self::zero_spec().add_spec(a) == a,
    {
        let z = Self::zero_spec();
        let lhs = a.add_spec(z);
        let rhs = z.add_spec(a);
        assert(z.x == Scalar::from_int_spec(0));
        assert(z.y == Scalar::from_int_spec(0));
        Scalar::lemma_add_zero_identity(a.x);
        Scalar::lemma_add_zero_identity(a.y);
        assert(lhs.x == a.x.add_spec(Scalar::from_int_spec(0)));
        assert(lhs.y == a.y.add_spec(Scalar::from_int_spec(0)));
        assert(lhs.x == a.x);
        assert(lhs.y == a.y);
        assert(lhs == a);

        assert(rhs.x == Scalar::from_int_spec(0).add_spec(a.x));
        assert(rhs.y == Scalar::from_int_spec(0).add_spec(a.y));
        assert(rhs.x == a.x);
        assert(rhs.y == a.y);
        assert(rhs == a);
    }

    pub proof fn lemma_add_inverse(a: Self)
        ensures
            a.add_spec(a.neg_spec()).eqv_spec(Self::zero_spec()),
            a.neg_spec().add_spec(a).eqv_spec(Self::zero_spec()),
    {
        let z = Self::zero_spec();
        let lhs = a.add_spec(a.neg_spec());
        let rhs = a.neg_spec().add_spec(a);
        assert(z.x == Scalar::from_int_spec(0));
        assert(z.y == Scalar::from_int_spec(0));
        Scalar::lemma_add_inverse(a.x);
        Scalar::lemma_add_inverse(a.y);
        assert(lhs.x == a.x.add_spec(a.x.neg_spec()));
        assert(lhs.y == a.y.add_spec(a.y.neg_spec()));
        assert(lhs.x.eqv_spec(z.x));
        assert(lhs.y.eqv_spec(z.y));
        assert(lhs.eqv_spec(z));

        assert(rhs.x == a.x.neg_spec().add_spec(a.x));
        assert(rhs.y == a.y.neg_spec().add_spec(a.y));
        assert(rhs.x.eqv_spec(z.x));
        assert(rhs.y.eqv_spec(z.y));
        assert(rhs.eqv_spec(z));
    }

    pub proof fn lemma_neg_involution(a: Self)
        ensures
            a.neg_spec().neg_spec() == a,
    {
        let n = a.neg_spec().neg_spec();
        let nx = a.x.neg_spec().neg_spec();
        let ny = a.y.neg_spec().neg_spec();

        assert(nx.num == -(-a.x.num));
        assert(-(-a.x.num) == a.x.num);
        assert(nx.num == a.x.num);
        assert(nx.den == a.x.den);
        assert(nx == a.x);

        assert(ny.num == -(-a.y.num));
        assert(-(-a.y.num) == a.y.num);
        assert(ny.num == a.y.num);
        assert(ny.den == a.y.den);
        assert(ny == a.y);

        assert(n.x == nx);
        assert(n.y == ny);
        assert(n.x == a.x);
        assert(n.y == a.y);
        assert(n == a);
    }

    pub proof fn lemma_sub_is_add_neg(a: Self, b: Self)
        ensures
            a.sub_spec(b) == a.add_spec(b.neg_spec()),
    {
        let lhs = a.sub_spec(b);
        let rhs = a.add_spec(b.neg_spec());
        Scalar::lemma_sub_is_add_neg(a.x, b.x);
        Scalar::lemma_sub_is_add_neg(a.y, b.y);
        assert(lhs.x == a.x.sub_spec(b.x));
        assert(rhs.x == a.x.add_spec(b.x.neg_spec()));
        assert(lhs.x == rhs.x);
        assert(lhs.y == a.y.sub_spec(b.y));
        assert(rhs.y == a.y.add_spec(b.y.neg_spec()));
        assert(lhs.y == rhs.y);
        assert(lhs == rhs);
    }

    pub proof fn lemma_scale_zero(v: Self)
        ensures
            v.scale_spec(Scalar::from_int_spec(0)).eqv_spec(Self::zero_spec()),
    {
        let z = Self::zero_spec();
        let s = v.scale_spec(Scalar::from_int_spec(0));
        assert(z.x == Scalar::from_int_spec(0));
        assert(z.y == Scalar::from_int_spec(0));
        Scalar::lemma_mul_zero(v.x);
        Scalar::lemma_mul_zero(v.y);
        assert(s.x == v.x.mul_spec(Scalar::from_int_spec(0)));
        assert(s.y == v.y.mul_spec(Scalar::from_int_spec(0)));
        assert(s.x.eqv_spec(z.x));
        assert(s.y.eqv_spec(z.y));
        assert(s.eqv_spec(z));
    }

    pub proof fn lemma_scale_one_identity(v: Self)
        ensures
            v.scale_spec(Scalar::from_int_spec(1)) == v,
    {
        let s = v.scale_spec(Scalar::from_int_spec(1));
        Scalar::lemma_mul_one_identity(v.x);
        Scalar::lemma_mul_one_identity(v.y);
        assert(s.x == v.x.mul_spec(Scalar::from_int_spec(1)));
        assert(s.y == v.y.mul_spec(Scalar::from_int_spec(1)));
        assert(s.x == v.x);
        assert(s.y == v.y);
        assert(s == v);
    }

    pub proof fn lemma_scale_associative(v: Self, k1: Scalar, k2: Scalar)
        ensures
            v.scale_spec(k1).scale_spec(k2).eqv_spec(v.scale_spec(k1.mul_spec(k2))),
    {
        let lhs = v.scale_spec(k1).scale_spec(k2);
        let rhs = v.scale_spec(k1.mul_spec(k2));
        Scalar::lemma_mul_associative(v.x, k1, k2);
        Scalar::lemma_mul_associative(v.y, k1, k2);
        assert(lhs.x == v.x.mul_spec(k1).mul_spec(k2));
        assert(rhs.x == v.x.mul_spec(k1.mul_spec(k2)));
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y == v.y.mul_spec(k1).mul_spec(k2));
        assert(rhs.y == v.y.mul_spec(k1.mul_spec(k2)));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_scale_distributes_over_vec_add(u: Self, v: Self, k: Scalar)
        ensures
            u.add_spec(v).scale_spec(k).eqv_spec(u.scale_spec(k).add_spec(v.scale_spec(k))),
    {
        let lhs = u.add_spec(v).scale_spec(k);
        let rhs = u.scale_spec(k).add_spec(v.scale_spec(k));

        let uxk = u.x.mul_spec(k);
        let vxk = v.x.mul_spec(k);
        let kux = k.mul_spec(u.x);
        let kvx = k.mul_spec(v.x);

        let uyk = u.y.mul_spec(k);
        let vyk = v.y.mul_spec(k);
        let kuy = k.mul_spec(u.y);
        let kvy = k.mul_spec(v.y);

        Scalar::lemma_mul_commutative(u.x.add_spec(v.x), k);
        Scalar::lemma_mul_commutative(u.y.add_spec(v.y), k);
        Scalar::lemma_eqv_mul_distributive_left(k, u.x, v.x);
        Scalar::lemma_eqv_mul_distributive_left(k, u.y, v.y);
        Scalar::lemma_mul_commutative(k, u.x);
        Scalar::lemma_mul_commutative(k, v.x);
        Scalar::lemma_mul_commutative(k, u.y);
        Scalar::lemma_mul_commutative(k, v.y);

        assert(lhs.x == u.x.add_spec(v.x).mul_spec(k));
        assert(lhs.x == k.mul_spec(u.x.add_spec(v.x)));
        assert(k.mul_spec(u.x.add_spec(v.x)).eqv_spec(k.mul_spec(u.x).add_spec(k.mul_spec(v.x))));
        assert(kux == uxk);
        assert(kvx == vxk);
        Scalar::lemma_eqv_reflexive(kux);
        Scalar::lemma_eqv_reflexive(kvx);
        assert(kux.eqv_spec(uxk));
        assert(kvx.eqv_spec(vxk));
        Scalar::lemma_eqv_add_congruence(kux, uxk, kvx, vxk);
        assert(kux.add_spec(kvx).eqv_spec(uxk.add_spec(vxk)));
        Scalar::lemma_eqv_transitive(lhs.x, kux.add_spec(kvx), uxk.add_spec(vxk));
        assert(lhs.x.eqv_spec(uxk.add_spec(vxk)));
        assert(rhs.x == uxk.add_spec(vxk));
        assert(lhs.x.eqv_spec(rhs.x));

        assert(lhs.y == u.y.add_spec(v.y).mul_spec(k));
        assert(lhs.y == k.mul_spec(u.y.add_spec(v.y)));
        assert(k.mul_spec(u.y.add_spec(v.y)).eqv_spec(k.mul_spec(u.y).add_spec(k.mul_spec(v.y))));
        assert(kuy == uyk);
        assert(kvy == vyk);
        Scalar::lemma_eqv_reflexive(kuy);
        Scalar::lemma_eqv_reflexive(kvy);
        assert(kuy.eqv_spec(uyk));
        assert(kvy.eqv_spec(vyk));
        Scalar::lemma_eqv_add_congruence(kuy, uyk, kvy, vyk);
        assert(kuy.add_spec(kvy).eqv_spec(uyk.add_spec(vyk)));
        Scalar::lemma_eqv_transitive(lhs.y, kuy.add_spec(kvy), uyk.add_spec(vyk));
        assert(lhs.y.eqv_spec(uyk.add_spec(vyk)));
        assert(rhs.y == uyk.add_spec(vyk));
        assert(lhs.y.eqv_spec(rhs.y));

        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_scale_distributes_over_scalar_add(v: Self, a: Scalar, b: Scalar)
        ensures
            v.scale_spec(a.add_spec(b)).eqv_spec(v.scale_spec(a).add_spec(v.scale_spec(b))),
    {
        let lhs = v.scale_spec(a.add_spec(b));
        let rhs = v.scale_spec(a).add_spec(v.scale_spec(b));
        Scalar::lemma_mul_distributes_over_add(v.x, a, b);
        Scalar::lemma_mul_distributes_over_add(v.y, a, b);
        assert(lhs.x == v.x.mul_spec(a.add_spec(b)));
        assert(rhs.x == v.x.mul_spec(a).add_spec(v.x.mul_spec(b)));
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y == v.y.mul_spec(a.add_spec(b)));
        assert(rhs.y == v.y.mul_spec(a).add_spec(v.y.mul_spec(b)));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_scale_neg_vector(v: Self, k: Scalar)
        ensures
            v.neg_spec().scale_spec(k) == v.scale_spec(k).neg_spec(),
    {
        let lhs = v.neg_spec().scale_spec(k);
        let rhs = v.scale_spec(k).neg_spec();
        Scalar::lemma_mul_commutative(v.x.neg_spec(), k);
        Scalar::lemma_mul_neg_right(k, v.x);
        Scalar::lemma_mul_commutative(k, v.x);
        assert(lhs.x == v.x.neg_spec().mul_spec(k));
        assert(lhs.x == k.mul_spec(v.x.neg_spec()));
        assert(k.mul_spec(v.x.neg_spec()) == k.mul_spec(v.x).neg_spec());
        assert(k.mul_spec(v.x) == v.x.mul_spec(k));
        assert(lhs.x == v.x.mul_spec(k).neg_spec());
        assert(rhs.x == v.x.mul_spec(k).neg_spec());
        assert(lhs.x == rhs.x);

        Scalar::lemma_mul_commutative(v.y.neg_spec(), k);
        Scalar::lemma_mul_neg_right(k, v.y);
        Scalar::lemma_mul_commutative(k, v.y);
        assert(lhs.y == v.y.neg_spec().mul_spec(k));
        assert(lhs.y == k.mul_spec(v.y.neg_spec()));
        assert(k.mul_spec(v.y.neg_spec()) == k.mul_spec(v.y).neg_spec());
        assert(k.mul_spec(v.y) == v.y.mul_spec(k));
        assert(lhs.y == v.y.mul_spec(k).neg_spec());
        assert(rhs.y == v.y.mul_spec(k).neg_spec());
        assert(lhs.y == rhs.y);

        assert(lhs == rhs);
    }

    pub proof fn lemma_scale_neg_scalar(v: Self, k: Scalar)
        ensures
            v.scale_spec(k.neg_spec()) == v.scale_spec(k).neg_spec(),
    {
        let lhs = v.scale_spec(k.neg_spec());
        let rhs = v.scale_spec(k).neg_spec();
        Scalar::lemma_mul_neg_right(v.x, k);
        Scalar::lemma_mul_neg_right(v.y, k);
        assert(lhs.x == v.x.mul_spec(k.neg_spec()));
        assert(rhs.x == v.x.mul_spec(k).neg_spec());
        assert(lhs.x == rhs.x);
        assert(lhs.y == v.y.mul_spec(k.neg_spec()));
        assert(rhs.y == v.y.mul_spec(k).neg_spec());
        assert(lhs.y == rhs.y);
        assert(lhs == rhs);
    }

    pub proof fn lemma_dot_symmetric(u: Self, v: Self)
        ensures
            u.dot_spec(v).eqv_spec(v.dot_spec(u)),
    {
        let lhs = u.dot_spec(v);
        let rhs = v.dot_spec(u);
        let p = u.x.mul_spec(v.x);
        let q = v.x.mul_spec(u.x);
        let r = u.y.mul_spec(v.y);
        let s = v.y.mul_spec(u.y);

        Scalar::lemma_mul_commutative(u.x, v.x);
        Scalar::lemma_mul_commutative(u.y, v.y);
        assert(p == q);
        assert(r == s);
        assert(lhs == p.add_spec(r));
        assert(rhs == q.add_spec(s));
        assert(rhs == p.add_spec(r));
        assert(lhs == rhs);
        Scalar::lemma_eqv_reflexive(lhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_dot_linear_right(u: Self, v: Self, w: Self)
        ensures
            u.dot_spec(v.add_spec(w)).eqv_spec(u.dot_spec(v).add_spec(u.dot_spec(w))),
    {
        let lhs = u.dot_spec(v.add_spec(w));
        let ux = u.x.mul_spec(v.x.add_spec(w.x));
        let uy = u.y.mul_spec(v.y.add_spec(w.y));
        let ax = u.x.mul_spec(v.x);
        let bx = u.x.mul_spec(w.x);
        let ay = u.y.mul_spec(v.y);
        let by = u.y.mul_spec(w.y);
        let mid = ax.add_spec(bx).add_spec(ay.add_spec(by));
        let rhs = u.dot_spec(v).add_spec(u.dot_spec(w));

        Scalar::lemma_mul_distributes_over_add(u.x, v.x, w.x);
        Scalar::lemma_mul_distributes_over_add(u.y, v.y, w.y);
        assert(lhs == ux.add_spec(uy));
        assert(ux.eqv_spec(ax.add_spec(bx)));
        assert(uy.eqv_spec(ay.add_spec(by)));
        Scalar::lemma_eqv_add_congruence(ux, ax.add_spec(bx), uy, ay.add_spec(by));
        assert(lhs.eqv_spec(mid));

        assert(rhs == ax.add_spec(ay).add_spec(bx.add_spec(by)));
        Scalar::lemma_add_rearrange_2x2(ax, bx, ay, by);
        assert(mid.eqv_spec(rhs));
        Scalar::lemma_eqv_transitive(lhs, mid, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_dot_linear_left(u: Self, v: Self, w: Self)
        ensures
            u.add_spec(v).dot_spec(w).eqv_spec(u.dot_spec(w).add_spec(v.dot_spec(w))),
    {
        let lhs = u.add_spec(v).dot_spec(w);
        let mid1 = w.dot_spec(u.add_spec(v));
        let mid2 = w.dot_spec(u).add_spec(w.dot_spec(v));
        let rhs = u.dot_spec(w).add_spec(v.dot_spec(w));

        Self::lemma_dot_symmetric(u.add_spec(v), w);
        assert(lhs.eqv_spec(mid1));
        Self::lemma_dot_linear_right(w, u, v);
        assert(mid1.eqv_spec(mid2));
        Self::lemma_dot_symmetric(w, u);
        Self::lemma_dot_symmetric(w, v);
        Scalar::lemma_eqv_add_congruence(w.dot_spec(u), u.dot_spec(w), w.dot_spec(v), v.dot_spec(w));
        assert(mid2.eqv_spec(rhs));
        Scalar::lemma_eqv_transitive(lhs, mid1, mid2);
        Scalar::lemma_eqv_transitive(lhs, mid2, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_dot_scale_extract_left(v: Self, w: Self, k: Scalar)
        ensures
            v.scale_spec(k).dot_spec(w).eqv_spec(k.mul_spec(v.dot_spec(w))),
    {
        let lhs = v.scale_spec(k).dot_spec(w);
        let rhs = k.mul_spec(v.dot_spec(w));

        let a1 = v.x.mul_spec(k).mul_spec(w.x);
        let b1 = v.y.mul_spec(k).mul_spec(w.y);
        let a2 = k.mul_spec(v.x).mul_spec(w.x);
        let b2 = k.mul_spec(v.y).mul_spec(w.y);
        let a3 = k.mul_spec(v.x.mul_spec(w.x));
        let b3 = k.mul_spec(v.y.mul_spec(w.y));
        let mid = a3.add_spec(b3);

        Scalar::lemma_mul_commutative(v.x, k);
        Scalar::lemma_mul_commutative(v.y, k);
        assert(v.x.mul_spec(k) == k.mul_spec(v.x));
        assert(v.y.mul_spec(k) == k.mul_spec(v.y));
        assert(a1 == a2);
        assert(b1 == b2);

        Scalar::lemma_mul_associative(k, v.x, w.x);
        Scalar::lemma_mul_associative(k, v.y, w.y);
        Scalar::lemma_eqv_reflexive(a1);
        Scalar::lemma_eqv_reflexive(b1);
        assert(a1.eqv_spec(a2));
        assert(b1.eqv_spec(b2));
        Scalar::lemma_eqv_transitive(a1, a2, a3);
        Scalar::lemma_eqv_transitive(b1, b2, b3);
        assert(a1.eqv_spec(a3));
        assert(b1.eqv_spec(b3));

        assert(lhs == a1.add_spec(b1));
        Scalar::lemma_eqv_add_congruence(a1, a3, b1, b3);
        assert(lhs.eqv_spec(mid));

        Scalar::lemma_eqv_mul_distributive_left(k, v.x.mul_spec(w.x), v.y.mul_spec(w.y));
        assert(rhs == k.mul_spec(v.x.mul_spec(w.x).add_spec(v.y.mul_spec(w.y))));
        assert(v.dot_spec(w) == v.x.mul_spec(w.x).add_spec(v.y.mul_spec(w.y)));
        assert(rhs.eqv_spec(mid));
        Scalar::lemma_eqv_symmetric(rhs, mid);
        assert(mid.eqv_spec(rhs));
        Scalar::lemma_eqv_transitive(lhs, mid, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_cross_scale_extract_left(v: Self, w: Self, k: Scalar)
        ensures
            v.scale_spec(k).cross_spec(w).eqv_spec(k.mul_spec(v.cross_spec(w))),
    {
        let lhs = v.scale_spec(k).cross_spec(w);
        let rhs = k.mul_spec(v.cross_spec(w));
        let p = v.x.mul_spec(w.y);
        let q = v.y.mul_spec(w.x);
        let p1 = v.x.mul_spec(k).mul_spec(w.y);
        let q1 = v.y.mul_spec(k).mul_spec(w.x);
        let p2 = k.mul_spec(p);
        let q2 = k.mul_spec(q);
        let mid = p2.sub_spec(q2);

        let px2 = k.mul_spec(v.x).mul_spec(w.y);
        let qx2 = k.mul_spec(v.y).mul_spec(w.x);
        Scalar::lemma_mul_commutative(v.x, k);
        Scalar::lemma_mul_commutative(v.y, k);
        assert(v.x.mul_spec(k) == k.mul_spec(v.x));
        assert(v.y.mul_spec(k) == k.mul_spec(v.y));
        assert(p1 == px2);
        assert(q1 == qx2);
        Scalar::lemma_mul_associative(k, v.x, w.y);
        Scalar::lemma_mul_associative(k, v.y, w.x);
        Scalar::lemma_eqv_reflexive(p1);
        Scalar::lemma_eqv_reflexive(q1);
        assert(p1.eqv_spec(px2));
        assert(q1.eqv_spec(qx2));
        Scalar::lemma_eqv_transitive(p1, px2, p2);
        Scalar::lemma_eqv_transitive(q1, qx2, q2);
        assert(p1.eqv_spec(p2));
        assert(q1.eqv_spec(q2));

        assert(lhs == p1.sub_spec(q1));
        Scalar::lemma_eqv_sub_congruence(p1, p2, q1, q2);
        assert(lhs.eqv_spec(mid));

        Scalar::lemma_sub_is_add_neg(p, q);
        assert(v.cross_spec(w) == p.sub_spec(q));
        assert(v.cross_spec(w) == p.add_spec(q.neg_spec()));
        assert(rhs == k.mul_spec(p.add_spec(q.neg_spec())));
        Scalar::lemma_eqv_mul_distributive_left(k, p, q.neg_spec());
        assert(rhs.eqv_spec(k.mul_spec(p).add_spec(k.mul_spec(q.neg_spec()))));
        Scalar::lemma_mul_neg_right(k, q);
        assert(k.mul_spec(q.neg_spec()) == k.mul_spec(q).neg_spec());
        assert(rhs.eqv_spec(p2.add_spec(q2.neg_spec())));

        assert(mid == p2.add_spec(q2.neg_spec()));
        Scalar::lemma_eqv_reflexive(mid);
        assert(mid.eqv_spec(p2.add_spec(q2.neg_spec())));
        Scalar::lemma_eqv_symmetric(mid, p2.add_spec(q2.neg_spec()));
        assert(p2.add_spec(q2.neg_spec()).eqv_spec(mid));
        Scalar::lemma_eqv_transitive(rhs, p2.add_spec(q2.neg_spec()), mid);
        assert(rhs.eqv_spec(mid));
        Scalar::lemma_eqv_symmetric(rhs, mid);
        assert(mid.eqv_spec(rhs));
        Scalar::lemma_eqv_transitive(lhs, mid, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_cross_scale_extract_right(v: Self, w: Self, k: Scalar)
        ensures
            v.cross_spec(w.scale_spec(k)).eqv_spec(k.mul_spec(v.cross_spec(w))),
    {
        let lhs = v.cross_spec(w.scale_spec(k));
        let rhs = k.mul_spec(v.cross_spec(w));
        let m = w.scale_spec(k).cross_spec(v);
        let n = k.mul_spec(w.cross_spec(v));
        let nn = n.neg_spec();
        let c = v.cross_spec(w);

        Self::lemma_cross_antisymmetric(v, w.scale_spec(k));
        assert(lhs == m.neg_spec());

        Self::lemma_cross_scale_extract_left(w, v, k);
        assert(m.eqv_spec(n));
        Scalar::lemma_eqv_neg_congruence(m, n);
        assert(m.neg_spec().eqv_spec(nn));
        assert(lhs.eqv_spec(nn));

        Self::lemma_cross_antisymmetric(w, v);
        assert(w.cross_spec(v) == c.neg_spec());
        assert(n == k.mul_spec(c.neg_spec()));
        Scalar::lemma_mul_neg_right(k, c);
        assert(k.mul_spec(c.neg_spec()) == k.mul_spec(c).neg_spec());
        assert(n == rhs.neg_spec());
        assert(nn == rhs.neg_spec().neg_spec());
        assert(rhs.neg_spec().neg_spec().num == -(-rhs.num));
        assert(rhs.neg_spec().neg_spec().num == rhs.num) by (nonlinear_arith);
        assert(rhs.neg_spec().neg_spec().den == rhs.den);
        assert(rhs.neg_spec().neg_spec() == rhs);
        assert(nn == rhs);
        Scalar::lemma_eqv_reflexive(rhs);
        assert(nn.eqv_spec(rhs));

        Scalar::lemma_eqv_transitive(lhs, nn, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_cross_self_zero(v: Self)
        ensures
            v.cross_spec(v).eqv_spec(Scalar::from_int_spec(0)),
    {
        let z = Scalar::from_int_spec(0);
        let c = v.cross_spec(v);
        Self::lemma_cross_self_zero_num(v);
        assert(z.num == 0);
        assert(c.num == 0);
        assert(c.eqv_spec(z) == (c.num * z.denom() == z.num * c.denom()));
        assert(c.num * z.denom() == 0 * z.denom());
        assert(z.num * c.denom() == 0 * c.denom());
        lemma_mul_by_zero_is_zero(z.denom());
        lemma_mul_by_zero_is_zero(c.denom());
        assert(0 * z.denom() == 0);
        assert(0 * c.denom() == 0);
        assert(c.num * z.denom() == z.num * c.denom());
        assert(c.eqv_spec(z));
    }

    pub proof fn lemma_cross_self_zero_num(v: Self)
        ensures
            v.cross_spec(v).num == 0,
    {
        let xy = v.x.mul_spec(v.y);
        let yx = v.y.mul_spec(v.x);
        let n = v.x.num * v.y.num;
        let d = v.x.den * v.y.den + v.x.den + v.y.den;
        let dp1 = (d + 1) as int;

        assert(xy.num == v.x.num * v.y.num);
        assert(yx.num == v.y.num * v.x.num);
        assert(n == v.x.num * v.y.num);
        assert(v.y.num * v.x.num == v.x.num * v.y.num) by (nonlinear_arith);
        assert(v.y.num * v.x.num == n);
        assert(xy.num == n);
        assert(yx.num == n);

        assert(xy.den == v.x.den * v.y.den + v.x.den + v.y.den);
        assert(yx.den == v.y.den * v.x.den + v.y.den + v.x.den);
        assert(d == v.x.den * v.y.den + v.x.den + v.y.den);
        assert(v.y.den * v.x.den + v.y.den + v.x.den
            == v.x.den * v.y.den + v.x.den + v.y.den) by (nonlinear_arith);
        assert(v.y.den * v.x.den + v.y.den + v.x.den == d);
        assert(xy.den == d);
        assert(yx.den == d);
        assert(xy.denom() == dp1);
        assert(yx.denom() == dp1);
        assert(xy.denom() == yx.denom());

        let c = v.cross_spec(v);
        assert(c == xy.sub_spec(yx));
        assert(c.num == xy.num * yx.denom() + (-yx.num) * xy.denom());
        assert(c.num == n * dp1 + (-n) * dp1);
        assert(n * dp1 + (-n) * dp1 == 0) by (nonlinear_arith);
        assert(c.num == 0);
    }

    pub proof fn lemma_cross_self_zero_signum(v: Self)
        ensures
            v.cross_spec(v).signum() == 0,
    {
        let c = v.cross_spec(v);
        Self::lemma_cross_self_zero_num(v);
        assert(c.num == 0);
        Scalar::lemma_signum_zero_iff(c);
        assert((c.signum() == 0) == (c.num == 0));
        assert(c.signum() == 0);
    }

    pub proof fn lemma_cross_left_zero_num(u: Self, v: Self)
        requires
            u.x.num == 0,
            u.y.num == 0,
        ensures
            u.cross_spec(v).num == 0,
    {
        let xy = u.x.mul_spec(v.y);
        let yx = u.y.mul_spec(v.x);
        let c = u.cross_spec(v);
        assert(c == xy.sub_spec(yx));
        Scalar::lemma_mul_left_zero_num(u.x, v.y);
        Scalar::lemma_mul_left_zero_num(u.y, v.x);
        assert(xy.num == 0);
        assert(yx.num == 0);

        Scalar::lemma_sub_both_zero_num(xy, yx);
        assert(c.num == 0);
    }

    pub proof fn lemma_cross_left_zero_signum(u: Self, v: Self)
        requires
            u.x.num == 0,
            u.y.num == 0,
        ensures
            u.cross_spec(v).signum() == 0,
    {
        let c = u.cross_spec(v);
        Self::lemma_cross_left_zero_num(u, v);
        assert(c.num == 0);
        Scalar::lemma_signum_zero_iff(c);
        assert((c.signum() == 0) == (c.num == 0));
        assert(c.signum() == 0);
    }

    pub proof fn lemma_cross_right_zero_num(u: Self, v: Self)
        requires
            v.x.num == 0,
            v.y.num == 0,
        ensures
            u.cross_spec(v).num == 0,
    {
        let xy = u.x.mul_spec(v.y);
        let yx = u.y.mul_spec(v.x);
        let c = u.cross_spec(v);
        assert(c == xy.sub_spec(yx));
        Scalar::lemma_mul_right_zero_num(u.x, v.y);
        Scalar::lemma_mul_right_zero_num(u.y, v.x);
        assert(xy.num == 0);
        assert(yx.num == 0);

        Scalar::lemma_sub_both_zero_num(xy, yx);
        assert(c.num == 0);
    }

    pub proof fn lemma_cross_right_zero_signum(u: Self, v: Self)
        requires
            v.x.num == 0,
            v.y.num == 0,
        ensures
            u.cross_spec(v).signum() == 0,
    {
        let c = u.cross_spec(v);
        Self::lemma_cross_right_zero_num(u, v);
        assert(c.num == 0);
        Scalar::lemma_signum_zero_iff(c);
        assert((c.signum() == 0) == (c.num == 0));
        assert(c.signum() == 0);
    }

    pub proof fn lemma_cross_antisymmetric(a: Self, b: Self)
        ensures
            a.cross_spec(b) == b.cross_spec(a).neg_spec(),
    {
        let p = a.x.mul_spec(b.y);
        let q = a.y.mul_spec(b.x);
        let r = b.x.mul_spec(a.y);
        let s = b.y.mul_spec(a.x);

        Scalar::lemma_mul_commutative(a.y, b.x);
        Scalar::lemma_mul_commutative(a.x, b.y);
        assert(r == q);
        assert(s == p);

        Scalar::lemma_sub_antisymmetric(p, q);
        assert(p.sub_spec(q) == q.sub_spec(p).neg_spec());
        assert(q.sub_spec(p) == r.sub_spec(s));
        assert(p.sub_spec(q) == r.sub_spec(s).neg_spec());

        assert(a.cross_spec(b) == p.sub_spec(q));
        assert(b.cross_spec(a) == r.sub_spec(s));
        assert(a.cross_spec(b) == b.cross_spec(a).neg_spec());
    }

    pub proof fn lemma_cross_eqv_congruence(u1: Self, u2: Self, v1: Self, v2: Self)
        requires
            u1.x.eqv_spec(u2.x),
            u1.y.eqv_spec(u2.y),
            v1.x.eqv_spec(v2.x),
            v1.y.eqv_spec(v2.y),
        ensures
            u1.cross_spec(v1).eqv_spec(u2.cross_spec(v2)),
    {
        let p1 = u1.x.mul_spec(v1.y);
        let q1 = u1.y.mul_spec(v1.x);
        let p2 = u2.x.mul_spec(v2.y);
        let q2 = u2.y.mul_spec(v2.x);

        Scalar::lemma_eqv_mul_congruence(u1.x, u2.x, v1.y, v2.y);
        Scalar::lemma_eqv_mul_congruence(u1.y, u2.y, v1.x, v2.x);
        assert(p1.eqv_spec(p2));
        assert(q1.eqv_spec(q2));

        Scalar::lemma_eqv_sub_congruence(p1, p2, q1, q2);
        assert(p1.sub_spec(q1).eqv_spec(p2.sub_spec(q2)));

        assert(u1.cross_spec(v1) == p1.sub_spec(q1));
        assert(u2.cross_spec(v2) == p2.sub_spec(q2));
        assert(u1.cross_spec(v1).eqv_spec(u2.cross_spec(v2)));
    }

    pub proof fn lemma_cross_neg_right(u: Self, v: Self)
        ensures
            u.cross_spec(v.neg_spec()) == u.cross_spec(v).neg_spec(),
    {
        let lhs = u.cross_spec(v.neg_spec());
        let rhs = u.cross_spec(v).neg_spec();

        let p = u.x.mul_spec(v.y);
        let q = u.y.mul_spec(v.x);
        let pn = u.x.mul_spec(v.y.neg_spec());
        let qn = u.y.mul_spec(v.x.neg_spec());

        Scalar::lemma_mul_neg_right(u.x, v.y);
        Scalar::lemma_mul_neg_right(u.y, v.x);
        Scalar::lemma_sub_neg_both(p, q);

        assert(pn == p.neg_spec());
        assert(qn == q.neg_spec());
        assert(lhs == pn.sub_spec(qn));
        assert(lhs == p.neg_spec().sub_spec(q.neg_spec()));
        assert(p.neg_spec().sub_spec(q.neg_spec()) == p.sub_spec(q).neg_spec());
        assert(rhs == p.sub_spec(q).neg_spec());
        assert(lhs == rhs);
    }

    pub proof fn lemma_cross_add_self_right_eqv(u: Self, v: Self)
        ensures
            u.cross_spec(v.add_spec(u)).eqv_spec(u.cross_spec(v)),
    {
        let p = u.x.mul_spec(v.y);
        let q = u.y.mul_spec(v.x);
        let r = u.x.mul_spec(u.y);
        let s = u.y.mul_spec(u.x);

        let p1 = u.x.mul_spec(v.y.add_spec(u.y));
        let q1 = u.y.mul_spec(v.x.add_spec(u.x));
        let m1 = p.add_spec(r);
        let m2 = q.add_spec(s);
        let lhs = u.cross_spec(v.add_spec(u));
        let mid = m1.sub_spec(m2);
        let rhs = u.cross_spec(v);

        Scalar::lemma_eqv_mul_distributive_left(u.x, v.y, u.y);
        Scalar::lemma_eqv_mul_distributive_left(u.y, v.x, u.x);
        assert(p1.eqv_spec(m1));
        assert(q1.eqv_spec(m2));

        Scalar::lemma_eqv_sub_congruence(p1, m1, q1, m2);
        assert(p1.sub_spec(q1).eqv_spec(m1.sub_spec(m2)));
        assert(lhs == p1.sub_spec(q1));
        assert(mid == m1.sub_spec(m2));
        assert(lhs.eqv_spec(mid));

        Scalar::lemma_mul_commutative(u.y, u.x);
        assert(s == r);
        assert(m2 == q.add_spec(r));
        assert(mid == m1.sub_spec(q.add_spec(r)));

        Scalar::lemma_eqv_sub_cancel_right(p, q, r);
        assert(m1.sub_spec(q.add_spec(r)).eqv_spec(p.sub_spec(q)));
        assert(rhs == p.sub_spec(q));
        assert(mid.eqv_spec(rhs));

        Scalar::lemma_eqv_transitive(lhs, mid, rhs);
        assert(lhs.eqv_spec(rhs));
    }
}

} // verus!
