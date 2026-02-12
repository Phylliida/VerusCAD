use vstd::prelude::*;
use crate::scalar::Scalar;

verus! {

pub struct Vec2 {
    pub x: Scalar,
    pub y: Scalar,
}

impl Vec2 {
    pub open spec fn from_ints_spec(x: int, y: int) -> Self {
        Vec2 { x: Scalar { value: x }, y: Scalar { value: y } }
    }

    pub open spec fn zero_spec() -> Self {
        Vec2 { x: Scalar { value: 0 }, y: Scalar { value: 0 } }
    }

    pub open spec fn neg_spec(self) -> Self {
        Vec2 { x: self.x.neg_spec(), y: self.y.neg_spec() }
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

    pub proof fn from_ints(x: int, y: int) -> (v: Self)
        ensures
            v == Self::from_ints_spec(x, y),
    {
        Vec2 { x: Scalar { value: x }, y: Scalar { value: y } }
    }

    pub open spec fn add_spec(self, rhs: Self) -> Self {
        Vec2 { x: self.x.add_spec(rhs.x), y: self.y.add_spec(rhs.y) }
    }

    pub proof fn add(self, rhs: Self) -> (out: Self)
        ensures
            out == self.add_spec(rhs),
    {
        Vec2 {
            x: Scalar { value: self.x.value + rhs.x.value },
            y: Scalar { value: self.y.value + rhs.y.value },
        }
    }

    pub open spec fn sub_spec(self, rhs: Self) -> Self {
        Vec2 { x: self.x.sub_spec(rhs.x), y: self.y.sub_spec(rhs.y) }
    }

    pub proof fn sub(self, rhs: Self) -> (out: Self)
        ensures
            out == self.sub_spec(rhs),
    {
        Vec2 {
            x: Scalar { value: self.x.value - rhs.x.value },
            y: Scalar { value: self.y.value - rhs.y.value },
        }
    }

    pub open spec fn scale_spec(self, k: Scalar) -> Self {
        Vec2 { x: self.x.mul_spec(k), y: self.y.mul_spec(k) }
    }

    pub proof fn scale(self, k: Scalar) -> (out: Self)
        ensures
            out == self.scale_spec(k),
    {
        Vec2 {
            x: Scalar { value: self.x.value * k.value },
            y: Scalar { value: self.y.value * k.value },
        }
    }

    pub open spec fn dot_spec(self, rhs: Self) -> Scalar {
        self.x.mul_spec(rhs.x).add_spec(self.y.mul_spec(rhs.y))
    }

    pub proof fn dot(self, rhs: Self) -> (out: Scalar)
        ensures
            out == self.dot_spec(rhs),
    {
        Scalar { value: self.x.value * rhs.x.value + self.y.value * rhs.y.value }
    }

    pub open spec fn cross_spec(self, rhs: Self) -> Scalar {
        self.x.mul_spec(rhs.y).sub_spec(self.y.mul_spec(rhs.x))
    }

    pub proof fn cross(self, rhs: Self) -> (out: Scalar)
        ensures
            out == self.cross_spec(rhs),
    {
        Scalar { value: self.x.value * rhs.y.value - self.y.value * rhs.x.value }
    }

    pub open spec fn norm2_spec(self) -> Scalar {
        self.dot_spec(self)
    }

    pub proof fn lemma_dot_symmetric(a: Self, b: Self)
        ensures
            a.dot_spec(b) == b.dot_spec(a),
    {
        let lhs = a.dot_spec(b);
        let rhs = b.dot_spec(a);
        assert(lhs.as_int() == a.x.as_int() * b.x.as_int() + a.y.as_int() * b.y.as_int());
        assert(rhs.as_int() == b.x.as_int() * a.x.as_int() + b.y.as_int() * a.y.as_int());
        assert(a.x.as_int() * b.x.as_int() + a.y.as_int() * b.y.as_int()
            == b.x.as_int() * a.x.as_int() + b.y.as_int() * a.y.as_int()) by (nonlinear_arith);
        assert(lhs.as_int() == rhs.as_int());
        Scalar::lemma_eq_from_as_int_internal(lhs, rhs);
    }

    pub proof fn lemma_cross_antisymmetric(a: Self, b: Self)
        ensures
            a.cross_spec(b) == b.cross_spec(a).neg_spec(),
    {
        let lhs = a.cross_spec(b);
        let rhs = b.cross_spec(a).neg_spec();
        assert(lhs.as_int() == a.x.as_int() * b.y.as_int() - a.y.as_int() * b.x.as_int());
        assert(b.cross_spec(a).as_int() == b.x.as_int() * a.y.as_int() - b.y.as_int() * a.x.as_int());
        assert(rhs.as_int() == -(b.x.as_int() * a.y.as_int() - b.y.as_int() * a.x.as_int()));
        assert(a.x.as_int() * b.y.as_int() - a.y.as_int() * b.x.as_int()
            == -(b.x.as_int() * a.y.as_int() - b.y.as_int() * a.x.as_int())) by (nonlinear_arith);
        assert(lhs.as_int() == rhs.as_int());
        Scalar::lemma_eq_from_as_int_internal(lhs, rhs);
    }

    pub proof fn lemma_add_commutative(a: Self, b: Self)
        ensures
            a.add_spec(b).x.as_int() == b.add_spec(a).x.as_int(),
            a.add_spec(b).y.as_int() == b.add_spec(a).y.as_int(),
    {
        assert(a.x.as_int() + b.x.as_int() == b.x.as_int() + a.x.as_int()) by (nonlinear_arith);
        assert(a.y.as_int() + b.y.as_int() == b.y.as_int() + a.y.as_int()) by (nonlinear_arith);
    }

    pub proof fn lemma_add_associative(a: Self, b: Self, c: Self)
        ensures
            a.add_spec(b).add_spec(c).x.as_int() == a.add_spec(b.add_spec(c)).x.as_int(),
            a.add_spec(b).add_spec(c).y.as_int() == a.add_spec(b.add_spec(c)).y.as_int(),
    {
        assert((a.x.as_int() + b.x.as_int()) + c.x.as_int() == a.x.as_int() + (b.x.as_int() + c.x.as_int())) by (nonlinear_arith);
        assert((a.y.as_int() + b.y.as_int()) + c.y.as_int() == a.y.as_int() + (b.y.as_int() + c.y.as_int())) by (nonlinear_arith);
    }

    pub proof fn lemma_add_zero_identity(v: Self)
        ensures
            v.add_spec(Self::zero_spec()).x.as_int() == v.x.as_int(),
            v.add_spec(Self::zero_spec()).y.as_int() == v.y.as_int(),
            Self::zero_spec().add_spec(v).x.as_int() == v.x.as_int(),
            Self::zero_spec().add_spec(v).y.as_int() == v.y.as_int(),
    {
        assert(v.x.as_int() + 0 == v.x.as_int()) by (nonlinear_arith);
        assert(v.y.as_int() + 0 == v.y.as_int()) by (nonlinear_arith);
        assert(0 + v.x.as_int() == v.x.as_int()) by (nonlinear_arith);
        assert(0 + v.y.as_int() == v.y.as_int()) by (nonlinear_arith);
    }

    pub proof fn lemma_sub_is_add_neg(a: Self, b: Self)
        ensures
            a.sub_spec(b).x.as_int() == a.add_spec(b.neg_spec()).x.as_int(),
            a.sub_spec(b).y.as_int() == a.add_spec(b.neg_spec()).y.as_int(),
    {
        assert(a.x.as_int() - b.x.as_int() == a.x.as_int() + (-b.x.as_int())) by (nonlinear_arith);
        assert(a.y.as_int() - b.y.as_int() == a.y.as_int() + (-b.y.as_int())) by (nonlinear_arith);
    }

    pub proof fn lemma_dot_linear_left(u: Self, v: Self, w: Self)
        ensures
            u.add_spec(v).dot_spec(w) == u.dot_spec(w).add_spec(v.dot_spec(w)),
    {
        let lhs = u.add_spec(v).dot_spec(w);
        let rhs = u.dot_spec(w).add_spec(v.dot_spec(w));
        assert(lhs.as_int()
            == (u.x.as_int() + v.x.as_int()) * w.x.as_int()
            + (u.y.as_int() + v.y.as_int()) * w.y.as_int());
        assert(rhs.as_int()
            == (u.x.as_int() * w.x.as_int() + u.y.as_int() * w.y.as_int())
            + (v.x.as_int() * w.x.as_int() + v.y.as_int() * w.y.as_int()));
        assert(
            (u.x.as_int() + v.x.as_int()) * w.x.as_int()
            + (u.y.as_int() + v.y.as_int()) * w.y.as_int()
            == (u.x.as_int() * w.x.as_int() + u.y.as_int() * w.y.as_int())
            + (v.x.as_int() * w.x.as_int() + v.y.as_int() * w.y.as_int())
        ) by (nonlinear_arith);
        assert(lhs.as_int() == rhs.as_int());
        Scalar::lemma_eq_from_as_int_internal(lhs, rhs);
    }

    pub proof fn lemma_cross_linear_left(u: Self, v: Self, w: Self)
        ensures
            u.add_spec(v).cross_spec(w) == u.cross_spec(w).add_spec(v.cross_spec(w)),
    {
        let lhs = u.add_spec(v).cross_spec(w);
        let rhs = u.cross_spec(w).add_spec(v.cross_spec(w));
        assert(lhs.as_int()
            == (u.x.as_int() + v.x.as_int()) * w.y.as_int()
            - (u.y.as_int() + v.y.as_int()) * w.x.as_int());
        assert(rhs.as_int()
            == (u.x.as_int() * w.y.as_int() - u.y.as_int() * w.x.as_int())
            + (v.x.as_int() * w.y.as_int() - v.y.as_int() * w.x.as_int()));
        assert(
            (u.x.as_int() + v.x.as_int()) * w.y.as_int()
            - (u.y.as_int() + v.y.as_int()) * w.x.as_int()
            == (u.x.as_int() * w.y.as_int() - u.y.as_int() * w.x.as_int())
            + (v.x.as_int() * w.y.as_int() - v.y.as_int() * w.x.as_int())
        ) by (nonlinear_arith);
        assert(lhs.as_int() == rhs.as_int());
        Scalar::lemma_eq_from_as_int_internal(lhs, rhs);
    }

    pub proof fn lemma_cross_self_zero(v: Self)
        ensures
            v.cross_spec(v).as_int() == 0,
    {
        assert(v.cross_spec(v).as_int() == v.x.as_int() * v.y.as_int() - v.y.as_int() * v.x.as_int());
        assert(v.x.as_int() * v.y.as_int() - v.y.as_int() * v.x.as_int() == 0) by (nonlinear_arith);
    }

    pub proof fn lemma_scale_one_identity(v: Self)
        ensures
            v.scale_spec(Scalar { value: 1 }).x.as_int() == v.x.as_int(),
            v.scale_spec(Scalar { value: 1 }).y.as_int() == v.y.as_int(),
    {
        assert(v.x.as_int() * 1 == v.x.as_int()) by (nonlinear_arith);
        assert(v.y.as_int() * 1 == v.y.as_int()) by (nonlinear_arith);
    }

    pub proof fn lemma_scale_zero(v: Self)
        ensures
            v.scale_spec(Scalar { value: 0 }).x.as_int() == 0,
            v.scale_spec(Scalar { value: 0 }).y.as_int() == 0,
    {
        assert(v.x.as_int() * 0 == 0) by (nonlinear_arith);
        assert(v.y.as_int() * 0 == 0) by (nonlinear_arith);
    }

    pub proof fn lemma_scale_distributes_over_vec_add(u: Self, v: Self, k: Scalar)
        ensures
            u.add_spec(v).scale_spec(k).x.as_int() == u.scale_spec(k).add_spec(v.scale_spec(k)).x.as_int(),
            u.add_spec(v).scale_spec(k).y.as_int() == u.scale_spec(k).add_spec(v.scale_spec(k)).y.as_int(),
    {
        assert((u.x.as_int() + v.x.as_int()) * k.as_int() == u.x.as_int() * k.as_int() + v.x.as_int() * k.as_int()) by (nonlinear_arith);
        assert((u.y.as_int() + v.y.as_int()) * k.as_int() == u.y.as_int() * k.as_int() + v.y.as_int() * k.as_int()) by (nonlinear_arith);
    }

    pub proof fn lemma_scale_distributes_over_scalar_add(v: Self, a: Scalar, b: Scalar)
        ensures
            v.scale_spec(a.add_spec(b)).x.as_int() == v.scale_spec(a).add_spec(v.scale_spec(b)).x.as_int(),
            v.scale_spec(a.add_spec(b)).y.as_int() == v.scale_spec(a).add_spec(v.scale_spec(b)).y.as_int(),
    {
        assert(v.x.as_int() * (a.as_int() + b.as_int()) == v.x.as_int() * a.as_int() + v.x.as_int() * b.as_int()) by (nonlinear_arith);
        assert(v.y.as_int() * (a.as_int() + b.as_int()) == v.y.as_int() * a.as_int() + v.y.as_int() * b.as_int()) by (nonlinear_arith);
    }

    pub proof fn lemma_scale_associative(v: Self, a: Scalar, b: Scalar)
        ensures
            v.scale_spec(a.mul_spec(b)).x.as_int() == v.scale_spec(a).scale_spec(b).x.as_int(),
            v.scale_spec(a.mul_spec(b)).y.as_int() == v.scale_spec(a).scale_spec(b).y.as_int(),
    {
        assert(v.x.as_int() * (a.as_int() * b.as_int()) == (v.x.as_int() * a.as_int()) * b.as_int()) by (nonlinear_arith);
        assert(v.y.as_int() * (a.as_int() * b.as_int()) == (v.y.as_int() * a.as_int()) * b.as_int()) by (nonlinear_arith);
    }

    pub proof fn lemma_norm2_nonnegative(v: Self)
        ensures
            v.norm2_spec().as_int() >= 0,
    {
        assert(v.norm2_spec().as_int() == v.x.as_int() * v.x.as_int() + v.y.as_int() * v.y.as_int());
        assert(v.x.as_int() * v.x.as_int() >= 0) by (nonlinear_arith);
        assert(v.y.as_int() * v.y.as_int() >= 0) by (nonlinear_arith);
        assert(v.x.as_int() * v.x.as_int() + v.y.as_int() * v.y.as_int() >= 0) by (nonlinear_arith);
    }

    pub proof fn lemma_neg_involution(v: Self)
        ensures
            v.neg_spec().neg_spec() == v,
    {
        let lhs = v.neg_spec().neg_spec();
        assert(lhs.x.as_int() == -(-v.x.as_int()));
        assert(lhs.y.as_int() == -(-v.y.as_int()));
        assert(-(-v.x.as_int()) == v.x.as_int()) by (nonlinear_arith);
        assert(-(-v.y.as_int()) == v.y.as_int()) by (nonlinear_arith);
        assert(lhs.x.as_int() == v.x.as_int());
        assert(lhs.y.as_int() == v.y.as_int());
        Self::lemma_eq_from_component_ints(lhs, v);
    }

    pub proof fn lemma_add_inverse(v: Self)
        ensures
            v.add_spec(v.neg_spec()) == Self::zero_spec(),
            v.neg_spec().add_spec(v) == Self::zero_spec(),
    {
        let lhs = v.add_spec(v.neg_spec());
        let rhs = v.neg_spec().add_spec(v);
        let z = Self::zero_spec();
        assert(lhs.x.as_int() == v.x.as_int() + (-v.x.as_int()));
        assert(lhs.y.as_int() == v.y.as_int() + (-v.y.as_int()));
        assert(rhs.x.as_int() == (-v.x.as_int()) + v.x.as_int());
        assert(rhs.y.as_int() == (-v.y.as_int()) + v.y.as_int());
        assert(v.x.as_int() + (-v.x.as_int()) == 0) by (nonlinear_arith);
        assert(v.y.as_int() + (-v.y.as_int()) == 0) by (nonlinear_arith);
        assert((-v.x.as_int()) + v.x.as_int() == 0) by (nonlinear_arith);
        assert((-v.y.as_int()) + v.y.as_int() == 0) by (nonlinear_arith);
        assert(lhs.x.as_int() == 0);
        assert(lhs.y.as_int() == 0);
        assert(rhs.x.as_int() == 0);
        assert(rhs.y.as_int() == 0);
        assert(z.x.as_int() == 0);
        assert(z.y.as_int() == 0);
        Self::lemma_eq_from_component_ints(lhs, z);
        Self::lemma_eq_from_component_ints(rhs, z);
    }

    pub proof fn lemma_scale_neg_vector(v: Self, k: Scalar)
        ensures
            v.neg_spec().scale_spec(k) == v.scale_spec(k).neg_spec(),
    {
        let lhs = v.neg_spec().scale_spec(k);
        let rhs = v.scale_spec(k).neg_spec();
        assert(lhs.x.as_int() == (-v.x.as_int()) * k.as_int());
        assert(lhs.y.as_int() == (-v.y.as_int()) * k.as_int());
        assert(rhs.x.as_int() == -(v.x.as_int() * k.as_int()));
        assert(rhs.y.as_int() == -(v.y.as_int() * k.as_int()));
        assert((-v.x.as_int()) * k.as_int() == -(v.x.as_int() * k.as_int())) by (nonlinear_arith);
        assert((-v.y.as_int()) * k.as_int() == -(v.y.as_int() * k.as_int())) by (nonlinear_arith);
        assert(lhs.x.as_int() == rhs.x.as_int());
        assert(lhs.y.as_int() == rhs.y.as_int());
        Self::lemma_eq_from_component_ints(lhs, rhs);
    }

    pub proof fn lemma_scale_neg_scalar(v: Self, k: Scalar)
        ensures
            v.scale_spec(k.neg_spec()) == v.scale_spec(k).neg_spec(),
    {
        let lhs = v.scale_spec(k.neg_spec());
        let rhs = v.scale_spec(k).neg_spec();
        assert(lhs.x.as_int() == v.x.as_int() * (-k.as_int()));
        assert(lhs.y.as_int() == v.y.as_int() * (-k.as_int()));
        assert(rhs.x.as_int() == -(v.x.as_int() * k.as_int()));
        assert(rhs.y.as_int() == -(v.y.as_int() * k.as_int()));
        assert(v.x.as_int() * (-k.as_int()) == -(v.x.as_int() * k.as_int())) by (nonlinear_arith);
        assert(v.y.as_int() * (-k.as_int()) == -(v.y.as_int() * k.as_int())) by (nonlinear_arith);
        assert(lhs.x.as_int() == rhs.x.as_int());
        assert(lhs.y.as_int() == rhs.y.as_int());
        Self::lemma_eq_from_component_ints(lhs, rhs);
    }

    pub proof fn lemma_dot_linear_right(u: Self, v: Self, w: Self)
        ensures
            u.dot_spec(v.add_spec(w)) == u.dot_spec(v).add_spec(u.dot_spec(w)),
    {
        let lhs = u.dot_spec(v.add_spec(w));
        let rhs = u.dot_spec(v).add_spec(u.dot_spec(w));
        assert(lhs.as_int()
            == u.x.as_int() * (v.x.as_int() + w.x.as_int())
            + u.y.as_int() * (v.y.as_int() + w.y.as_int()));
        assert(rhs.as_int()
            == (u.x.as_int() * v.x.as_int() + u.y.as_int() * v.y.as_int())
            + (u.x.as_int() * w.x.as_int() + u.y.as_int() * w.y.as_int()));
        assert(
            u.x.as_int() * (v.x.as_int() + w.x.as_int())
            + u.y.as_int() * (v.y.as_int() + w.y.as_int())
            == (u.x.as_int() * v.x.as_int() + u.y.as_int() * v.y.as_int())
            + (u.x.as_int() * w.x.as_int() + u.y.as_int() * w.y.as_int())
        ) by (nonlinear_arith);
        assert(lhs.as_int() == rhs.as_int());
        Scalar::lemma_eq_from_as_int_internal(lhs, rhs);
    }

    pub proof fn lemma_cross_linear_right(u: Self, v: Self, w: Self)
        ensures
            u.cross_spec(v.add_spec(w)) == u.cross_spec(v).add_spec(u.cross_spec(w)),
    {
        let lhs = u.cross_spec(v.add_spec(w));
        let rhs = u.cross_spec(v).add_spec(u.cross_spec(w));
        assert(lhs.as_int()
            == u.x.as_int() * (v.y.as_int() + w.y.as_int())
            - u.y.as_int() * (v.x.as_int() + w.x.as_int()));
        assert(rhs.as_int()
            == (u.x.as_int() * v.y.as_int() - u.y.as_int() * v.x.as_int())
            + (u.x.as_int() * w.y.as_int() - u.y.as_int() * w.x.as_int()));
        assert(
            u.x.as_int() * (v.y.as_int() + w.y.as_int())
            - u.y.as_int() * (v.x.as_int() + w.x.as_int())
            == (u.x.as_int() * v.y.as_int() - u.y.as_int() * v.x.as_int())
            + (u.x.as_int() * w.y.as_int() - u.y.as_int() * w.x.as_int())
        ) by (nonlinear_arith);
        assert(lhs.as_int() == rhs.as_int());
        Scalar::lemma_eq_from_as_int_internal(lhs, rhs);
    }

    pub proof fn lemma_dot_scale_extract_left(v: Self, w: Self, k: Scalar)
        ensures
            v.scale_spec(k).dot_spec(w) == k.mul_spec(v.dot_spec(w)),
    {
        let lhs = v.scale_spec(k).dot_spec(w);
        let rhs = k.mul_spec(v.dot_spec(w));
        assert(lhs.as_int()
            == (v.x.as_int() * k.as_int()) * w.x.as_int()
            + (v.y.as_int() * k.as_int()) * w.y.as_int());
        assert(rhs.as_int()
            == k.as_int() * (v.x.as_int() * w.x.as_int() + v.y.as_int() * w.y.as_int()));
        assert(
            (v.x.as_int() * k.as_int()) * w.x.as_int()
            + (v.y.as_int() * k.as_int()) * w.y.as_int()
            == k.as_int() * (v.x.as_int() * w.x.as_int() + v.y.as_int() * w.y.as_int())
        ) by (nonlinear_arith);
        assert(lhs.as_int() == rhs.as_int());
        Scalar::lemma_eq_from_as_int_internal(lhs, rhs);
    }

    pub proof fn lemma_cross_scale_extract_left(v: Self, w: Self, k: Scalar)
        ensures
            v.scale_spec(k).cross_spec(w) == k.mul_spec(v.cross_spec(w)),
    {
        let lhs = v.scale_spec(k).cross_spec(w);
        let rhs = k.mul_spec(v.cross_spec(w));
        assert(lhs.as_int()
            == (v.x.as_int() * k.as_int()) * w.y.as_int()
            - (v.y.as_int() * k.as_int()) * w.x.as_int());
        assert(rhs.as_int()
            == k.as_int() * (v.x.as_int() * w.y.as_int() - v.y.as_int() * w.x.as_int()));
        assert(
            (v.x.as_int() * k.as_int()) * w.y.as_int()
            - (v.y.as_int() * k.as_int()) * w.x.as_int()
            == k.as_int() * (v.x.as_int() * w.y.as_int() - v.y.as_int() * w.x.as_int())
        ) by (nonlinear_arith);
        assert(lhs.as_int() == rhs.as_int());
        Scalar::lemma_eq_from_as_int_internal(lhs, rhs);
    }

    pub proof fn lemma_cross_scale_extract_right(v: Self, w: Self, k: Scalar)
        ensures
            v.cross_spec(w.scale_spec(k)) == k.mul_spec(v.cross_spec(w)),
    {
        let lhs = v.cross_spec(w.scale_spec(k));
        let rhs = k.mul_spec(v.cross_spec(w));
        assert(lhs.as_int()
            == v.x.as_int() * (w.y.as_int() * k.as_int())
            - v.y.as_int() * (w.x.as_int() * k.as_int()));
        assert(rhs.as_int()
            == k.as_int() * (v.x.as_int() * w.y.as_int() - v.y.as_int() * w.x.as_int()));
        assert(
            v.x.as_int() * (w.y.as_int() * k.as_int())
            - v.y.as_int() * (w.x.as_int() * k.as_int())
            == k.as_int() * (v.x.as_int() * w.y.as_int() - v.y.as_int() * w.x.as_int())
        ) by (nonlinear_arith);
        assert(lhs.as_int() == rhs.as_int());
        Scalar::lemma_eq_from_as_int_internal(lhs, rhs);
    }

    pub proof fn lemma_norm2_scale(v: Self, k: Scalar)
        ensures
            v.scale_spec(k).norm2_spec().as_int() == k.mul_spec(k).mul_spec(v.norm2_spec()).as_int(),
    {
        assert(v.scale_spec(k).norm2_spec().as_int()
            == (v.x.as_int() * k.as_int()) * (v.x.as_int() * k.as_int())
            + (v.y.as_int() * k.as_int()) * (v.y.as_int() * k.as_int()));
        assert(k.mul_spec(k).mul_spec(v.norm2_spec()).as_int()
            == (k.as_int() * k.as_int()) * (v.x.as_int() * v.x.as_int() + v.y.as_int() * v.y.as_int()));
        assert(
            (v.x.as_int() * k.as_int()) * (v.x.as_int() * k.as_int())
            + (v.y.as_int() * k.as_int()) * (v.y.as_int() * k.as_int())
            == (k.as_int() * k.as_int()) * (v.x.as_int() * v.x.as_int() + v.y.as_int() * v.y.as_int())
        ) by (nonlinear_arith);
    }

    pub proof fn lemma_norm2_zero_iff_zero(v: Self)
        ensures
            (v.norm2_spec().as_int() == 0) == (v == Self::zero_spec()),
    {
        if v.norm2_spec().as_int() == 0 {
            assert(v.norm2_spec().as_int() == v.x.as_int() * v.x.as_int() + v.y.as_int() * v.y.as_int());
            assert(v.x.as_int() * v.x.as_int() >= 0) by (nonlinear_arith);
            assert(v.y.as_int() * v.y.as_int() >= 0) by (nonlinear_arith);
            assert(
                (v.x.as_int() * v.x.as_int() + v.y.as_int() * v.y.as_int() == 0)
                ==> (v.x.as_int() * v.x.as_int() == 0 && v.y.as_int() * v.y.as_int() == 0)
            ) by (nonlinear_arith);
            assert(v.x.as_int() * v.x.as_int() == 0 && v.y.as_int() * v.y.as_int() == 0);
            assert((v.x.as_int() * v.x.as_int() == 0) ==> v.x.as_int() == 0) by (nonlinear_arith);
            assert((v.y.as_int() * v.y.as_int() == 0) ==> v.y.as_int() == 0) by (nonlinear_arith);
            assert(v.x.as_int() == 0);
            assert(v.y.as_int() == 0);
            assert(Self::zero_spec().x.as_int() == 0);
            assert(Self::zero_spec().y.as_int() == 0);
            Self::lemma_eq_from_component_ints(v, Self::zero_spec());
        }

        if v == Self::zero_spec() {
            assert(v.norm2_spec().as_int() == Self::zero_spec().norm2_spec().as_int());
            assert(Self::zero_spec().norm2_spec().as_int() == 0) by (nonlinear_arith);
        }
    }
}

} // verus!
