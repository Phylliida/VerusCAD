use vstd::prelude::*;
use vstd::arithmetic::mul::{
    lemma_mul_cancels_negatives,
    lemma_mul_strict_inequality,
    lemma_mul_strictly_positive,
};

verus! {

/// Prototype scalar type for the verified math layer.
///
/// This first implementation uses exact integers and keeps the API minimal.
/// We can later swap internals to normalized rationals without changing the
/// higher-level geometry APIs.
pub struct Scalar {
    pub value: int,
}

impl Scalar {
    pub open spec fn as_int(self) -> int {
        self.value
    }

    pub proof fn lemma_eq_from_as_int(a: Self, b: Self)
        requires
            a.as_int() == b.as_int(),
        ensures
            a == b,
    {
        assert(a.value == b.value);
    }

    pub proof fn new(value: int) -> (s: Self)
        ensures
            s.as_int() == value,
    {
        Scalar { value }
    }

    pub proof fn zero() -> (s: Self)
        ensures
            s.as_int() == 0,
    {
        Scalar { value: 0 }
    }

    pub proof fn one() -> (s: Self)
        ensures
            s.as_int() == 1,
    {
        Scalar { value: 1 }
    }

    pub open spec fn add_spec(self, rhs: Self) -> Self {
        Scalar { value: self.value + rhs.value }
    }

    pub proof fn add(self, rhs: Self) -> (out: Self)
        ensures
            out == self.add_spec(rhs),
    {
        Scalar { value: self.value + rhs.value }
    }

    pub open spec fn sub_spec(self, rhs: Self) -> Self {
        Scalar { value: self.value - rhs.value }
    }

    pub proof fn sub(self, rhs: Self) -> (out: Self)
        ensures
            out == self.sub_spec(rhs),
    {
        Scalar { value: self.value - rhs.value }
    }

    pub open spec fn mul_spec(self, rhs: Self) -> Self {
        Scalar { value: self.value * rhs.value }
    }

    pub proof fn mul(self, rhs: Self) -> (out: Self)
        ensures
            out == self.mul_spec(rhs),
    {
        Scalar { value: self.value * rhs.value }
    }

    pub open spec fn neg_spec(self) -> Self {
        Scalar { value: -self.value }
    }

    pub open spec fn signum(self) -> int {
        if self.value > 0 {
            1
        } else if self.value < 0 {
            -1
        } else {
            0
        }
    }

    pub proof fn neg(self) -> (out: Self)
        ensures
            out == self.neg_spec(),
    {
        Scalar { value: -self.value }
    }

    pub proof fn lemma_add_commutative(a: Self, b: Self)
        ensures
            a.add_spec(b) == b.add_spec(a),
    {
        let lhs = a.add_spec(b);
        let rhs = b.add_spec(a);
        assert(lhs.as_int() == a.as_int() + b.as_int());
        assert(rhs.as_int() == b.as_int() + a.as_int());
        assert(a.as_int() + b.as_int() == b.as_int() + a.as_int()) by (nonlinear_arith);
        assert(lhs.as_int() == rhs.as_int());
        Self::lemma_eq_from_as_int(lhs, rhs);
    }

    pub proof fn lemma_mul_commutative(a: Self, b: Self)
        ensures
            a.mul_spec(b) == b.mul_spec(a),
    {
        let lhs = a.mul_spec(b);
        let rhs = b.mul_spec(a);
        assert(lhs.as_int() == a.as_int() * b.as_int());
        assert(rhs.as_int() == b.as_int() * a.as_int());
        assert(a.as_int() * b.as_int() == b.as_int() * a.as_int()) by (nonlinear_arith);
        assert(lhs.as_int() == rhs.as_int());
        Self::lemma_eq_from_as_int(lhs, rhs);
    }

    pub proof fn lemma_add_associative(a: Self, b: Self, c: Self)
        ensures
            a.add_spec(b).add_spec(c) == a.add_spec(b.add_spec(c)),
    {
        let lhs = a.add_spec(b).add_spec(c);
        let rhs = a.add_spec(b.add_spec(c));
        assert(lhs.as_int() == (a.as_int() + b.as_int()) + c.as_int());
        assert(rhs.as_int() == a.as_int() + (b.as_int() + c.as_int()));
        assert((a.as_int() + b.as_int()) + c.as_int() == a.as_int() + (b.as_int() + c.as_int())) by (nonlinear_arith);
        assert(lhs.as_int() == rhs.as_int());
        Self::lemma_eq_from_as_int(lhs, rhs);
    }

    pub proof fn lemma_mul_associative(a: Self, b: Self, c: Self)
        ensures
            a.mul_spec(b).mul_spec(c) == a.mul_spec(b.mul_spec(c)),
    {
        let lhs = a.mul_spec(b).mul_spec(c);
        let rhs = a.mul_spec(b.mul_spec(c));
        assert(lhs.as_int() == (a.as_int() * b.as_int()) * c.as_int());
        assert(rhs.as_int() == a.as_int() * (b.as_int() * c.as_int()));
        assert((a.as_int() * b.as_int()) * c.as_int() == a.as_int() * (b.as_int() * c.as_int())) by (nonlinear_arith);
        assert(lhs.as_int() == rhs.as_int());
        Self::lemma_eq_from_as_int(lhs, rhs);
    }

    pub proof fn lemma_mul_distributes_over_add(a: Self, b: Self, c: Self)
        ensures
            a.mul_spec(b.add_spec(c)) == a.mul_spec(b).add_spec(a.mul_spec(c)),
    {
        let lhs = a.mul_spec(b.add_spec(c));
        let rhs = a.mul_spec(b).add_spec(a.mul_spec(c));
        assert(lhs.as_int() == a.as_int() * (b.as_int() + c.as_int()));
        assert(rhs.as_int() == (a.as_int() * b.as_int()) + (a.as_int() * c.as_int()));
        assert(a.as_int() * (b.as_int() + c.as_int()) == (a.as_int() * b.as_int()) + (a.as_int() * c.as_int())) by (nonlinear_arith);
        assert(lhs.as_int() == rhs.as_int());
        Self::lemma_eq_from_as_int(lhs, rhs);
    }

    pub proof fn lemma_add_zero_identity(a: Self)
        ensures
            a.add_spec(Scalar { value: 0 }) == a,
            (Scalar { value: 0 }).add_spec(a) == a,
    {
        let z = Scalar { value: 0 };
        let lhs = a.add_spec(z);
        let rhs = z.add_spec(a);
        assert(lhs.as_int() == a.as_int() + 0);
        assert(rhs.as_int() == 0 + a.as_int());
        assert(a.as_int() + 0 == a.as_int()) by (nonlinear_arith);
        assert(0 + a.as_int() == a.as_int()) by (nonlinear_arith);
        assert(lhs.as_int() == a.as_int());
        assert(rhs.as_int() == a.as_int());
        Self::lemma_eq_from_as_int(lhs, a);
        Self::lemma_eq_from_as_int(rhs, a);
    }

    pub proof fn lemma_mul_one_identity(a: Self)
        ensures
            a.mul_spec(Scalar { value: 1 }) == a,
            (Scalar { value: 1 }).mul_spec(a) == a,
    {
        let o = Scalar { value: 1 };
        let lhs = a.mul_spec(o);
        let rhs = o.mul_spec(a);
        assert(lhs.as_int() == a.as_int() * 1);
        assert(rhs.as_int() == 1 * a.as_int());
        assert(a.as_int() * 1 == a.as_int()) by (nonlinear_arith);
        assert(1 * a.as_int() == a.as_int()) by (nonlinear_arith);
        assert(lhs.as_int() == a.as_int());
        assert(rhs.as_int() == a.as_int());
        Self::lemma_eq_from_as_int(lhs, a);
        Self::lemma_eq_from_as_int(rhs, a);
    }

    pub proof fn lemma_add_inverse(a: Self)
        ensures
            a.add_spec(a.neg_spec()) == (Scalar { value: 0 }),
            a.neg_spec().add_spec(a) == (Scalar { value: 0 }),
    {
        let z = Scalar { value: 0 };
        let lhs = a.add_spec(a.neg_spec());
        let rhs = a.neg_spec().add_spec(a);
        assert(lhs.as_int() == a.as_int() + (-a.as_int()));
        assert(rhs.as_int() == (-a.as_int()) + a.as_int());
        assert(a.as_int() + (-a.as_int()) == 0) by (nonlinear_arith);
        assert((-a.as_int()) + a.as_int() == 0) by (nonlinear_arith);
        assert(lhs.as_int() == 0);
        assert(rhs.as_int() == 0);
        Self::lemma_eq_from_as_int(lhs, z);
        Self::lemma_eq_from_as_int(rhs, z);
    }

    pub proof fn lemma_sub_is_add_neg(a: Self, b: Self)
        ensures
            a.sub_spec(b) == a.add_spec(b.neg_spec()),
    {
        let lhs = a.sub_spec(b);
        let rhs = a.add_spec(b.neg_spec());
        assert(lhs.as_int() == a.as_int() - b.as_int());
        assert(rhs.as_int() == a.as_int() + (-b.as_int()));
        assert(a.as_int() - b.as_int() == a.as_int() + (-b.as_int())) by (nonlinear_arith);
        assert(lhs.as_int() == rhs.as_int());
        Self::lemma_eq_from_as_int(lhs, rhs);
    }

    pub proof fn lemma_signum_positive_iff(a: Self)
        ensures
            (a.signum() == 1) == (a.as_int() > 0),
    {
        assert(a.as_int() == a.value);
        if a.value > 0 {
            assert(a.signum() == 1);
            assert(a.as_int() > 0);
        } else {
            assert(!(a.value > 0));
            assert(a.signum() != 1);
            assert(!(a.as_int() > 0));
        }
    }

    pub proof fn lemma_signum_negative_iff(a: Self)
        ensures
            (a.signum() == -1) == (a.as_int() < 0),
    {
        assert(a.as_int() == a.value);
        if a.value < 0 {
            assert(a.signum() == -1);
            assert(a.as_int() < 0);
        } else {
            assert(!(a.value < 0));
            assert(a.signum() != -1);
            assert(!(a.as_int() < 0));
        }
    }

    pub proof fn lemma_signum_zero_iff(a: Self)
        ensures
            (a.signum() == 0) == (a.as_int() == 0),
    {
        assert(a.as_int() == a.value);
        if a.value == 0 {
            assert(a.signum() == 0);
            assert(a.as_int() == 0);
        } else {
            assert(!(a.value == 0));
            assert(a.signum() != 0);
            assert(!(a.as_int() == 0));
        }
    }

    pub proof fn lemma_signum_cases(a: Self)
        ensures
            a.signum() == 1 || a.signum() == -1 || a.signum() == 0,
    {
        if a.value > 0 {
            assert(a.signum() == 1);
        } else if a.value < 0 {
            assert(a.signum() == -1);
        } else {
            assert(a.signum() == 0);
        }
    }

    pub proof fn lemma_signum_neg(a: Self)
        ensures
            a.neg_spec().signum() == -a.signum(),
    {
        let minus_one = Scalar { value: -1 };
        assert(minus_one.signum() == -1);
        Self::lemma_signum_mul(minus_one, a);
        assert(minus_one.mul_spec(a) == a.neg_spec());
        assert(minus_one.mul_spec(a).signum() == minus_one.signum() * a.signum());
        assert(minus_one.signum() * a.signum() == -1 * a.signum());
        assert(-1 * a.signum() == -a.signum());
    }

    pub proof fn lemma_signum_mul(a: Self, b: Self)
        ensures
            a.mul_spec(b).signum() == a.signum() * b.signum(),
    {
        if a.value == 0 {
            assert(a.mul_spec(b).signum() == 0);
            assert(a.signum() == 0);
            assert(a.signum() * b.signum() == 0);
        } else if b.value == 0 {
            assert(a.mul_spec(b).signum() == 0);
            assert(b.signum() == 0);
            assert(a.signum() * b.signum() == 0);
        } else if a.value > 0 {
            assert(a.signum() == 1);
            if b.value > 0 {
                assert(b.signum() == 1);
                lemma_mul_strictly_positive(a.value, b.value);
                assert(a.value * b.value > 0);
                assert(a.mul_spec(b).signum() == 1);
                assert(a.signum() * b.signum() == 1);
            } else {
                assert(b.value < 0);
                assert(b.signum() == -1);
                lemma_mul_strict_inequality(b.value, 0, a.value);
                assert(b.value * a.value < 0 * a.value);
                assert(0 * a.value == 0);
                assert(a.value * b.value == b.value * a.value);
                assert(a.value * b.value < 0);
                assert(a.mul_spec(b).signum() == -1);
                assert(a.signum() * b.signum() == -1);
            }
        } else {
            assert(a.value < 0);
            assert(a.signum() == -1);
            if b.value > 0 {
                assert(b.signum() == 1);
                lemma_mul_strict_inequality(a.value, 0, b.value);
                assert(a.value * b.value < 0 * b.value);
                assert(0 * b.value == 0);
                assert(a.value * b.value < 0);
                assert(a.mul_spec(b).signum() == -1);
                assert(a.signum() * b.signum() == -1);
            } else {
                assert(b.value < 0);
                assert(b.signum() == -1);
                assert(-a.value > 0);
                assert(-b.value > 0);
                lemma_mul_strictly_positive(-a.value, -b.value);
                assert((-a.value) * (-b.value) > 0);
                lemma_mul_cancels_negatives(a.value, b.value);
                assert(a.value * b.value == (-a.value) * (-b.value));
                assert(a.value * b.value > 0);
                assert(a.mul_spec(b).signum() == 1);
                assert(a.signum() * b.signum() == 1);
            }
        }
    }

    pub proof fn lemma_add_right_cancel(a: Self, b: Self, c: Self)
        ensures
            a.add_spec(c) == b.add_spec(c) ==> a == b,
    {
        if a.add_spec(c) == b.add_spec(c) {
            Self::lemma_add_right_cancel_strong(a, b, c);
        }
    }

    pub proof fn lemma_add_right_cancel_strong(a: Self, b: Self, c: Self)
        requires
            a.add_spec(c) == b.add_spec(c),
        ensures
            a == b,
    {
        assert(a.add_spec(c).as_int() == b.add_spec(c).as_int());
        assert(a.as_int() + c.as_int() == b.as_int() + c.as_int());
        assert((a.as_int() + c.as_int() == b.as_int() + c.as_int()) ==> a.as_int() == b.as_int()) by (nonlinear_arith);
        assert(a.as_int() == b.as_int());
        Self::lemma_eq_from_as_int(a, b);
    }

    pub proof fn lemma_add_left_cancel(a: Self, b: Self, c: Self)
        ensures
            c.add_spec(a) == c.add_spec(b) ==> a == b,
    {
        if c.add_spec(a) == c.add_spec(b) {
            Self::lemma_add_left_cancel_strong(a, b, c);
        }
    }

    pub proof fn lemma_add_left_cancel_strong(a: Self, b: Self, c: Self)
        requires
            c.add_spec(a) == c.add_spec(b),
        ensures
            a == b,
    {
        assert(c.add_spec(a).as_int() == c.add_spec(b).as_int());
        assert(c.as_int() + a.as_int() == c.as_int() + b.as_int());
        assert((c.as_int() + a.as_int() == c.as_int() + b.as_int()) ==> a.as_int() == b.as_int()) by (nonlinear_arith);
        assert(a.as_int() == b.as_int());
        Self::lemma_eq_from_as_int(a, b);
    }

    pub proof fn lemma_mul_zero(a: Self)
        ensures
            a.mul_spec(Scalar { value: 0 }).as_int() == 0,
            (Scalar { value: 0 }).mul_spec(a).as_int() == 0,
    {
        assert(a.value * 0 == 0) by (nonlinear_arith);
        assert(0 * a.value == 0) by (nonlinear_arith);
    }

    pub proof fn lemma_mul_zero_implies_factor_zero(a: Self, b: Self)
        ensures
            a.mul_spec(b).as_int() == 0 ==> a.as_int() == 0 || b.as_int() == 0,
    {
        assert((a.value * b.value == 0) ==> (a.value == 0 || b.value == 0)) by (nonlinear_arith);
    }

    pub proof fn lemma_le_add_monotone(a: Self, b: Self, c: Self)
        ensures
            a.as_int() <= b.as_int() ==> a.add_spec(c).as_int() <= b.add_spec(c).as_int(),
    {
        if a.as_int() <= b.as_int() {
            Self::lemma_le_add_monotone_strong(a, b, c);
        }
    }

    pub proof fn lemma_le_add_monotone_strong(a: Self, b: Self, c: Self)
        requires
            a.as_int() <= b.as_int(),
        ensures
            a.add_spec(c).as_int() <= b.add_spec(c).as_int(),
    {
        assert(a.value <= b.value);
        assert(a.add_spec(c).as_int() == a.value + c.value);
        assert(b.add_spec(c).as_int() == b.value + c.value);
        assert((a.value <= b.value) ==> (a.value + c.value <= b.value + c.value)) by (nonlinear_arith);
        assert(a.value + c.value <= b.value + c.value);
        assert(a.add_spec(c).as_int() <= b.add_spec(c).as_int());
    }

    pub proof fn lemma_le_mul_monotone_nonnegative(a: Self, b: Self, c: Self)
        ensures
            0 <= c.as_int() && a.as_int() <= b.as_int() ==> a.mul_spec(c).as_int() <= b.mul_spec(c).as_int(),
    {
        if 0 <= c.as_int() && a.as_int() <= b.as_int() {
            Self::lemma_le_mul_monotone_nonnegative_strong(a, b, c);
        }
    }

    pub proof fn lemma_le_mul_monotone_nonnegative_strong(a: Self, b: Self, c: Self)
        requires
            0 <= c.as_int(),
            a.as_int() <= b.as_int(),
        ensures
            a.mul_spec(c).as_int() <= b.mul_spec(c).as_int(),
    {
        assert(0 <= c.value);
        assert(a.value <= b.value);
        assert(a.mul_spec(c).as_int() == a.value * c.value);
        assert(b.mul_spec(c).as_int() == b.value * c.value);
        assert((0 <= c.value && a.value <= b.value) ==> (a.value * c.value <= b.value * c.value)) by (nonlinear_arith);
        assert(a.value * c.value <= b.value * c.value);
        assert(a.mul_spec(c).as_int() <= b.mul_spec(c).as_int());
    }
}

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
        Scalar::lemma_eq_from_as_int(a.x, b.x);
        Scalar::lemma_eq_from_as_int(a.y, b.y);
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
            a.dot_spec(b).as_int() == b.dot_spec(a).as_int(),
    {
        assert(a.dot_spec(b).as_int() == a.x.as_int() * b.x.as_int() + a.y.as_int() * b.y.as_int());
        assert(b.dot_spec(a).as_int() == b.x.as_int() * a.x.as_int() + b.y.as_int() * a.y.as_int());
        assert(a.x.as_int() * b.x.as_int() + a.y.as_int() * b.y.as_int()
            == b.x.as_int() * a.x.as_int() + b.y.as_int() * a.y.as_int()) by (nonlinear_arith);
    }

    pub proof fn lemma_cross_antisymmetric(a: Self, b: Self)
        ensures
            a.cross_spec(b).as_int() == -b.cross_spec(a).as_int(),
    {
        assert(a.cross_spec(b).as_int() == a.x.as_int() * b.y.as_int() - a.y.as_int() * b.x.as_int());
        assert(b.cross_spec(a).as_int() == b.x.as_int() * a.y.as_int() - b.y.as_int() * a.x.as_int());
        assert(a.x.as_int() * b.y.as_int() - a.y.as_int() * b.x.as_int()
            == -(b.x.as_int() * a.y.as_int() - b.y.as_int() * a.x.as_int())) by (nonlinear_arith);
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
            u.add_spec(v).dot_spec(w).as_int() == u.dot_spec(w).add_spec(v.dot_spec(w)).as_int(),
    {
        assert(u.add_spec(v).dot_spec(w).as_int()
            == (u.x.as_int() + v.x.as_int()) * w.x.as_int()
            + (u.y.as_int() + v.y.as_int()) * w.y.as_int());
        assert(u.dot_spec(w).add_spec(v.dot_spec(w)).as_int()
            == (u.x.as_int() * w.x.as_int() + u.y.as_int() * w.y.as_int())
            + (v.x.as_int() * w.x.as_int() + v.y.as_int() * w.y.as_int()));
        assert(
            (u.x.as_int() + v.x.as_int()) * w.x.as_int()
            + (u.y.as_int() + v.y.as_int()) * w.y.as_int()
            == (u.x.as_int() * w.x.as_int() + u.y.as_int() * w.y.as_int())
            + (v.x.as_int() * w.x.as_int() + v.y.as_int() * w.y.as_int())
        ) by (nonlinear_arith);
    }

    pub proof fn lemma_cross_linear_left(u: Self, v: Self, w: Self)
        ensures
            u.add_spec(v).cross_spec(w).as_int() == u.cross_spec(w).add_spec(v.cross_spec(w)).as_int(),
    {
        assert(u.add_spec(v).cross_spec(w).as_int()
            == (u.x.as_int() + v.x.as_int()) * w.y.as_int()
            - (u.y.as_int() + v.y.as_int()) * w.x.as_int());
        assert(u.cross_spec(w).add_spec(v.cross_spec(w)).as_int()
            == (u.x.as_int() * w.y.as_int() - u.y.as_int() * w.x.as_int())
            + (v.x.as_int() * w.y.as_int() - v.y.as_int() * w.x.as_int()));
        assert(
            (u.x.as_int() + v.x.as_int()) * w.y.as_int()
            - (u.y.as_int() + v.y.as_int()) * w.x.as_int()
            == (u.x.as_int() * w.y.as_int() - u.y.as_int() * w.x.as_int())
            + (v.x.as_int() * w.y.as_int() - v.y.as_int() * w.x.as_int())
        ) by (nonlinear_arith);
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
            u.dot_spec(v.add_spec(w)).as_int() == u.dot_spec(v).add_spec(u.dot_spec(w)).as_int(),
    {
        assert(u.dot_spec(v.add_spec(w)).as_int()
            == u.x.as_int() * (v.x.as_int() + w.x.as_int())
            + u.y.as_int() * (v.y.as_int() + w.y.as_int()));
        assert(u.dot_spec(v).add_spec(u.dot_spec(w)).as_int()
            == (u.x.as_int() * v.x.as_int() + u.y.as_int() * v.y.as_int())
            + (u.x.as_int() * w.x.as_int() + u.y.as_int() * w.y.as_int()));
        assert(
            u.x.as_int() * (v.x.as_int() + w.x.as_int())
            + u.y.as_int() * (v.y.as_int() + w.y.as_int())
            == (u.x.as_int() * v.x.as_int() + u.y.as_int() * v.y.as_int())
            + (u.x.as_int() * w.x.as_int() + u.y.as_int() * w.y.as_int())
        ) by (nonlinear_arith);
    }

    pub proof fn lemma_cross_linear_right(u: Self, v: Self, w: Self)
        ensures
            u.cross_spec(v.add_spec(w)).as_int() == u.cross_spec(v).add_spec(u.cross_spec(w)).as_int(),
    {
        assert(u.cross_spec(v.add_spec(w)).as_int()
            == u.x.as_int() * (v.y.as_int() + w.y.as_int())
            - u.y.as_int() * (v.x.as_int() + w.x.as_int()));
        assert(u.cross_spec(v).add_spec(u.cross_spec(w)).as_int()
            == (u.x.as_int() * v.y.as_int() - u.y.as_int() * v.x.as_int())
            + (u.x.as_int() * w.y.as_int() - u.y.as_int() * w.x.as_int()));
        assert(
            u.x.as_int() * (v.y.as_int() + w.y.as_int())
            - u.y.as_int() * (v.x.as_int() + w.x.as_int())
            == (u.x.as_int() * v.y.as_int() - u.y.as_int() * v.x.as_int())
            + (u.x.as_int() * w.y.as_int() - u.y.as_int() * w.x.as_int())
        ) by (nonlinear_arith);
    }

    pub proof fn lemma_dot_scale_extract_left(v: Self, w: Self, k: Scalar)
        ensures
            v.scale_spec(k).dot_spec(w).as_int() == k.mul_spec(v.dot_spec(w)).as_int(),
    {
        assert(v.scale_spec(k).dot_spec(w).as_int()
            == (v.x.as_int() * k.as_int()) * w.x.as_int()
            + (v.y.as_int() * k.as_int()) * w.y.as_int());
        assert(k.mul_spec(v.dot_spec(w)).as_int()
            == k.as_int() * (v.x.as_int() * w.x.as_int() + v.y.as_int() * w.y.as_int()));
        assert(
            (v.x.as_int() * k.as_int()) * w.x.as_int()
            + (v.y.as_int() * k.as_int()) * w.y.as_int()
            == k.as_int() * (v.x.as_int() * w.x.as_int() + v.y.as_int() * w.y.as_int())
        ) by (nonlinear_arith);
    }

    pub proof fn lemma_cross_scale_extract_left(v: Self, w: Self, k: Scalar)
        ensures
            v.scale_spec(k).cross_spec(w).as_int() == k.mul_spec(v.cross_spec(w)).as_int(),
    {
        assert(v.scale_spec(k).cross_spec(w).as_int()
            == (v.x.as_int() * k.as_int()) * w.y.as_int()
            - (v.y.as_int() * k.as_int()) * w.x.as_int());
        assert(k.mul_spec(v.cross_spec(w)).as_int()
            == k.as_int() * (v.x.as_int() * w.y.as_int() - v.y.as_int() * w.x.as_int()));
        assert(
            (v.x.as_int() * k.as_int()) * w.y.as_int()
            - (v.y.as_int() * k.as_int()) * w.x.as_int()
            == k.as_int() * (v.x.as_int() * w.y.as_int() - v.y.as_int() * w.x.as_int())
        ) by (nonlinear_arith);
    }

    pub proof fn lemma_cross_scale_extract_right(v: Self, w: Self, k: Scalar)
        ensures
            v.cross_spec(w.scale_spec(k)).as_int() == k.mul_spec(v.cross_spec(w)).as_int(),
    {
        assert(v.cross_spec(w.scale_spec(k)).as_int()
            == v.x.as_int() * (w.y.as_int() * k.as_int())
            - v.y.as_int() * (w.x.as_int() * k.as_int()));
        assert(k.mul_spec(v.cross_spec(w)).as_int()
            == k.as_int() * (v.x.as_int() * w.y.as_int() - v.y.as_int() * w.x.as_int()));
        assert(
            v.x.as_int() * (w.y.as_int() * k.as_int())
            - v.y.as_int() * (w.x.as_int() * k.as_int())
            == k.as_int() * (v.x.as_int() * w.y.as_int() - v.y.as_int() * w.x.as_int())
        ) by (nonlinear_arith);
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
        Scalar::lemma_eq_from_as_int(a.x, b.x);
        Scalar::lemma_eq_from_as_int(a.y, b.y);
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
        dist2_spec(p, q).as_int() == dist2_spec(q, p).as_int(),
{
    assert(dist2_spec(p, q).as_int()
        == (p.x.as_int() - q.x.as_int()) * (p.x.as_int() - q.x.as_int())
            + (p.y.as_int() - q.y.as_int()) * (p.y.as_int() - q.y.as_int()));
    assert(dist2_spec(q, p).as_int()
        == (q.x.as_int() - p.x.as_int()) * (q.x.as_int() - p.x.as_int())
            + (q.y.as_int() - p.y.as_int()) * (q.y.as_int() - p.y.as_int()));
    assert(
        (p.x.as_int() - q.x.as_int()) * (p.x.as_int() - q.x.as_int())
            + (p.y.as_int() - q.y.as_int()) * (p.y.as_int() - q.y.as_int())
        == (q.x.as_int() - p.x.as_int()) * (q.x.as_int() - p.x.as_int())
            + (q.y.as_int() - p.y.as_int()) * (q.y.as_int() - p.y.as_int())
    ) by (nonlinear_arith);
}

pub proof fn lemma_dist2_translation_invariant(p: Point2, q: Point2, t: Vec2)
    ensures
        dist2_spec(p.add_vec_spec(t), q.add_vec_spec(t)).as_int() == dist2_spec(p, q).as_int(),
{
    assert(dist2_spec(p.add_vec_spec(t), q.add_vec_spec(t)).as_int()
        == ((p.x.as_int() + t.x.as_int()) - (q.x.as_int() + t.x.as_int()))
            * ((p.x.as_int() + t.x.as_int()) - (q.x.as_int() + t.x.as_int()))
            + ((p.y.as_int() + t.y.as_int()) - (q.y.as_int() + t.y.as_int()))
                * ((p.y.as_int() + t.y.as_int()) - (q.y.as_int() + t.y.as_int())));
    assert(dist2_spec(p, q).as_int()
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

#[derive(Structural, PartialEq, Eq)]
pub enum Orientation {
    Cw,
    Collinear,
    Ccw,
}

pub open spec fn orient2d_spec(a: Point2, b: Point2, c: Point2) -> Scalar {
    b.sub_spec(a).cross_spec(c.sub_spec(a))
}

pub open spec fn is_ccw(a: Point2, b: Point2, c: Point2) -> bool {
    orient2d_spec(a, b, c).signum() == 1
}

pub open spec fn is_cw(a: Point2, b: Point2, c: Point2) -> bool {
    orient2d_spec(a, b, c).signum() == -1
}

pub open spec fn is_collinear(a: Point2, b: Point2, c: Point2) -> bool {
    orient2d_spec(a, b, c).signum() == 0
}

pub open spec fn orientation_spec(a: Point2, b: Point2, c: Point2) -> Orientation {
    let s = orient2d_spec(a, b, c).signum();
    if s == 1 {
        Orientation::Ccw
    } else if s == -1 {
        Orientation::Cw
    } else {
        Orientation::Collinear
    }
}

pub open spec fn scale_point_from_origin_spec(p: Point2, k: Scalar) -> Point2 {
    Point2 { x: p.x.mul_spec(k), y: p.y.mul_spec(k) }
}

pub proof fn orient2d(a: Point2, b: Point2, c: Point2) -> (out: Scalar)
    ensures
        out == orient2d_spec(a, b, c),
{
    Scalar {
        value:
            (b.x.value - a.x.value) * (c.y.value - a.y.value)
            - (b.y.value - a.y.value) * (c.x.value - a.x.value),
    }
}

pub proof fn orientation(a: Point2, b: Point2, c: Point2) -> (o: Orientation)
    ensures
        o == orientation_spec(a, b, c),
{
    let s = orient2d_spec(a, b, c).signum();
    if s == 1 {
        Orientation::Ccw
    } else if s == -1 {
        Orientation::Cw
    } else {
        Orientation::Collinear
    }
}

pub proof fn lemma_is_ccw_iff_positive(a: Point2, b: Point2, c: Point2)
    ensures
        is_ccw(a, b, c) == (orient2d_spec(a, b, c).as_int() > 0),
{
    let det = orient2d_spec(a, b, c);
    Scalar::lemma_signum_positive_iff(det);
    assert(is_ccw(a, b, c) == (det.signum() == 1));
    assert((det.signum() == 1) == (det.as_int() > 0));
}

pub proof fn lemma_is_cw_iff_negative(a: Point2, b: Point2, c: Point2)
    ensures
        is_cw(a, b, c) == (orient2d_spec(a, b, c).as_int() < 0),
{
    let det = orient2d_spec(a, b, c);
    Scalar::lemma_signum_negative_iff(det);
    assert(is_cw(a, b, c) == (det.signum() == -1));
    assert((det.signum() == -1) == (det.as_int() < 0));
}

pub proof fn lemma_is_collinear_iff_zero(a: Point2, b: Point2, c: Point2)
    ensures
        is_collinear(a, b, c) == (orient2d_spec(a, b, c).as_int() == 0),
{
    let det = orient2d_spec(a, b, c);
    Scalar::lemma_signum_zero_iff(det);
    assert(is_collinear(a, b, c) == (det.signum() == 0));
    assert((det.signum() == 0) == (det.as_int() == 0));
}

pub proof fn lemma_orientation_classes_exhaustive(a: Point2, b: Point2, c: Point2)
    ensures
        is_ccw(a, b, c) || is_cw(a, b, c) || is_collinear(a, b, c),
{
    let det = orient2d_spec(a, b, c);
    Scalar::lemma_signum_cases(det);
    assert(det.signum() == 1 || det.signum() == -1 || det.signum() == 0);
}

pub proof fn lemma_orientation_classes_pairwise_disjoint(a: Point2, b: Point2, c: Point2)
    ensures
        !(is_ccw(a, b, c) && is_cw(a, b, c)),
        !(is_ccw(a, b, c) && is_collinear(a, b, c)),
        !(is_cw(a, b, c) && is_collinear(a, b, c)),
{
    let s = orient2d_spec(a, b, c).signum();
    assert(!(s == 1 && s == -1)) by (nonlinear_arith);
    assert(!(s == 1 && s == 0)) by (nonlinear_arith);
    assert(!(s == -1 && s == 0)) by (nonlinear_arith);
}

pub proof fn lemma_ccw_swap_to_cw(a: Point2, b: Point2, c: Point2)
    ensures
        is_ccw(a, b, c) == is_cw(a, c, b),
{
    lemma_orient2d_swap_antisymmetric(a, b, c);
    let o = orient2d_spec(a, b, c).as_int();
    assert(orient2d_spec(a, c, b).as_int() == -o);
    assert((o > 0) == ((-o) < 0)) by (nonlinear_arith);
}

pub proof fn lemma_orientation_spec_matches_predicates(a: Point2, b: Point2, c: Point2)
    ensures
        (orientation_spec(a, b, c) is Ccw) == is_ccw(a, b, c),
        (orientation_spec(a, b, c) is Cw) == is_cw(a, b, c),
        (orientation_spec(a, b, c) is Collinear) == is_collinear(a, b, c),
{
    let det = orient2d_spec(a, b, c);
    let s = det.signum();
    Scalar::lemma_signum_cases(det);
    if s == 1 {
        assert(orientation_spec(a, b, c) is Ccw);
        assert(!(orientation_spec(a, b, c) is Cw));
        assert(!(orientation_spec(a, b, c) is Collinear));
        assert(is_ccw(a, b, c));
        lemma_orientation_classes_pairwise_disjoint(a, b, c);
        assert(!(is_ccw(a, b, c) && is_cw(a, b, c)));
        assert(!(is_ccw(a, b, c) && is_collinear(a, b, c)));
        assert(!is_cw(a, b, c));
        assert(!is_collinear(a, b, c));
    } else if s == -1 {
        assert(!(orientation_spec(a, b, c) is Ccw));
        assert(orientation_spec(a, b, c) is Cw);
        assert(!(orientation_spec(a, b, c) is Collinear));
        lemma_orientation_classes_pairwise_disjoint(a, b, c);
        assert(is_cw(a, b, c));
        assert(!(is_ccw(a, b, c) && is_cw(a, b, c)));
        assert(!(is_cw(a, b, c) && is_collinear(a, b, c)));
        assert(!is_ccw(a, b, c));
        assert(!is_collinear(a, b, c));
    } else {
        assert(s == 1 || s == -1 || s == 0);
        if s == 1 {
            assert(false);
        } else if s == -1 {
            assert(false);
        } else {
            assert(s == 0);
        }
        assert(!(orientation_spec(a, b, c) is Ccw));
        assert(!(orientation_spec(a, b, c) is Cw));
        assert(orientation_spec(a, b, c) is Collinear);
        lemma_orientation_classes_pairwise_disjoint(a, b, c);
        assert(is_collinear(a, b, c));
        assert(!(is_ccw(a, b, c) && is_collinear(a, b, c)));
        assert(!(is_cw(a, b, c) && is_collinear(a, b, c)));
        assert(!is_ccw(a, b, c));
        assert(!is_cw(a, b, c));
    }
}

pub proof fn lemma_orientation_spec_swap(a: Point2, b: Point2, c: Point2)
    ensures
        (orientation_spec(a, b, c) is Ccw) == (orientation_spec(a, c, b) is Cw),
        (orientation_spec(a, b, c) is Cw) == (orientation_spec(a, c, b) is Ccw),
        (orientation_spec(a, b, c) is Collinear) == (orientation_spec(a, c, b) is Collinear),
{
    lemma_orientation_spec_matches_predicates(a, b, c);
    lemma_orientation_spec_matches_predicates(a, c, b);
    lemma_orient2d_swap_antisymmetric(a, b, c);
    let o = orient2d_spec(a, b, c).as_int();
    assert(orient2d_spec(a, c, b).as_int() == -o);
    assert((o > 0) == ((-o) < 0)) by (nonlinear_arith);
    assert((o < 0) == ((-o) > 0)) by (nonlinear_arith);
    assert((o == 0) == ((-o) == 0)) by (nonlinear_arith);
}

pub proof fn lemma_orient2d_unit_ccw()
    ensures
        orient2d_spec(
            Point2::from_ints_spec(0, 0),
            Point2::from_ints_spec(1, 0),
            Point2::from_ints_spec(0, 1),
        ).as_int() == 1,
{
    assert(orient2d_spec(
        Point2::from_ints_spec(0, 0),
        Point2::from_ints_spec(1, 0),
        Point2::from_ints_spec(0, 1),
    ).as_int() == 1) by (nonlinear_arith);
}

pub proof fn lemma_orient2d_collinear()
    ensures
        orient2d_spec(
            Point2::from_ints_spec(0, 0),
            Point2::from_ints_spec(1, 1),
            Point2::from_ints_spec(2, 2),
        ).as_int() == 0,
{
    assert(orient2d_spec(
        Point2::from_ints_spec(0, 0),
        Point2::from_ints_spec(1, 1),
        Point2::from_ints_spec(2, 2),
    ).as_int() == 0) by (nonlinear_arith);
}

pub proof fn lemma_orient2d_swap_antisymmetric(a: Point2, b: Point2, c: Point2)
    ensures
        orient2d_spec(a, b, c).as_int() == -orient2d_spec(a, c, b).as_int(),
{
    assert(orient2d_spec(a, b, c).as_int()
        == (b.x.as_int() - a.x.as_int()) * (c.y.as_int() - a.y.as_int())
        - (b.y.as_int() - a.y.as_int()) * (c.x.as_int() - a.x.as_int()));
    assert(orient2d_spec(a, c, b).as_int()
        == (c.x.as_int() - a.x.as_int()) * (b.y.as_int() - a.y.as_int())
        - (c.y.as_int() - a.y.as_int()) * (b.x.as_int() - a.x.as_int()));
    assert(
        (b.x.as_int() - a.x.as_int()) * (c.y.as_int() - a.y.as_int())
        - (b.y.as_int() - a.y.as_int()) * (c.x.as_int() - a.x.as_int())
        == -(
            (c.x.as_int() - a.x.as_int()) * (b.y.as_int() - a.y.as_int())
            - (c.y.as_int() - a.y.as_int()) * (b.x.as_int() - a.x.as_int())
        )
    ) by (nonlinear_arith);
}

pub proof fn lemma_orient2d_cyclic_invariant(a: Point2, b: Point2, c: Point2)
    ensures
        orient2d_spec(a, b, c).as_int() == orient2d_spec(b, c, a).as_int(),
{
    assert(orient2d_spec(a, b, c).as_int()
        == (b.x.as_int() - a.x.as_int()) * (c.y.as_int() - a.y.as_int())
        - (b.y.as_int() - a.y.as_int()) * (c.x.as_int() - a.x.as_int()));
    assert(orient2d_spec(b, c, a).as_int()
        == (c.x.as_int() - b.x.as_int()) * (a.y.as_int() - b.y.as_int())
        - (c.y.as_int() - b.y.as_int()) * (a.x.as_int() - b.x.as_int()));
    assert(
        (b.x.as_int() - a.x.as_int()) * (c.y.as_int() - a.y.as_int())
        - (b.y.as_int() - a.y.as_int()) * (c.x.as_int() - a.x.as_int())
        == (c.x.as_int() - b.x.as_int()) * (a.y.as_int() - b.y.as_int())
        - (c.y.as_int() - b.y.as_int()) * (a.x.as_int() - b.x.as_int())
    ) by (nonlinear_arith);
}

pub proof fn lemma_orient2d_translation_invariant(a: Point2, b: Point2, c: Point2, t: Vec2)
    ensures
        orient2d_spec(a.add_vec_spec(t), b.add_vec_spec(t), c.add_vec_spec(t)).as_int()
            == orient2d_spec(a, b, c).as_int(),
{
    assert(orient2d_spec(a.add_vec_spec(t), b.add_vec_spec(t), c.add_vec_spec(t)).as_int()
        == ((b.x.as_int() + t.x.as_int()) - (a.x.as_int() + t.x.as_int()))
            * ((c.y.as_int() + t.y.as_int()) - (a.y.as_int() + t.y.as_int()))
        - ((b.y.as_int() + t.y.as_int()) - (a.y.as_int() + t.y.as_int()))
            * ((c.x.as_int() + t.x.as_int()) - (a.x.as_int() + t.x.as_int())));
    assert(orient2d_spec(a, b, c).as_int()
        == (b.x.as_int() - a.x.as_int()) * (c.y.as_int() - a.y.as_int())
        - (b.y.as_int() - a.y.as_int()) * (c.x.as_int() - a.x.as_int()));
    assert(
        ((b.x.as_int() + t.x.as_int()) - (a.x.as_int() + t.x.as_int()))
            * ((c.y.as_int() + t.y.as_int()) - (a.y.as_int() + t.y.as_int()))
        - ((b.y.as_int() + t.y.as_int()) - (a.y.as_int() + t.y.as_int()))
            * ((c.x.as_int() + t.x.as_int()) - (a.x.as_int() + t.x.as_int()))
        == (b.x.as_int() - a.x.as_int()) * (c.y.as_int() - a.y.as_int())
            - (b.y.as_int() - a.y.as_int()) * (c.x.as_int() - a.x.as_int())
    ) by (nonlinear_arith);
}

pub proof fn lemma_orient2d_degenerate_repeated_points(a: Point2, b: Point2)
    ensures
        orient2d_spec(a, a, b).as_int() == 0,
        orient2d_spec(a, b, a).as_int() == 0,
        orient2d_spec(b, a, a).as_int() == 0,
{
    assert(orient2d_spec(a, a, b).as_int() == 0) by (nonlinear_arith);
    assert(orient2d_spec(a, b, a).as_int() == 0) by (nonlinear_arith);
    assert(orient2d_spec(b, a, a).as_int() == 0) by (nonlinear_arith);
}

pub proof fn lemma_orient2d_permutation_table(a: Point2, b: Point2, c: Point2)
    ensures
        orient2d_spec(a, b, c).as_int() == orient2d_spec(b, c, a).as_int(),
        orient2d_spec(a, b, c).as_int() == orient2d_spec(c, a, b).as_int(),
        orient2d_spec(a, b, c).as_int() == -orient2d_spec(a, c, b).as_int(),
        orient2d_spec(a, b, c).as_int() == -orient2d_spec(b, a, c).as_int(),
        orient2d_spec(a, b, c).as_int() == -orient2d_spec(c, b, a).as_int(),
{
    lemma_orient2d_cyclic_invariant(a, b, c);
    lemma_orient2d_cyclic_invariant(c, a, b);
    lemma_orient2d_swap_antisymmetric(a, b, c);

    lemma_orient2d_cyclic_invariant(b, a, c);
    assert(orient2d_spec(b, a, c).as_int() == orient2d_spec(a, c, b).as_int());
    assert(orient2d_spec(a, b, c).as_int() == -orient2d_spec(b, a, c).as_int());

    lemma_orient2d_cyclic_invariant(c, b, a);
    assert(orient2d_spec(c, b, a).as_int() == orient2d_spec(b, a, c).as_int());
    assert(orient2d_spec(a, b, c).as_int() == -orient2d_spec(c, b, a).as_int());
}

pub proof fn lemma_orientation_spec_exclusive(a: Point2, b: Point2, c: Point2)
    ensures
        (orientation_spec(a, b, c) is Ccw) || (orientation_spec(a, b, c) is Cw)
            || (orientation_spec(a, b, c) is Collinear),
        !((orientation_spec(a, b, c) is Ccw) && (orientation_spec(a, b, c) is Cw)),
        !((orientation_spec(a, b, c) is Ccw) && (orientation_spec(a, b, c) is Collinear)),
        !((orientation_spec(a, b, c) is Cw) && (orientation_spec(a, b, c) is Collinear)),
{
    let o = orientation_spec(a, b, c);
    if o is Ccw {
        assert(!(o is Cw));
        assert(!(o is Collinear));
    } else if o is Cw {
        assert(!(o is Ccw));
        assert(!(o is Collinear));
    } else {
        assert(o is Collinear);
        assert(!(o is Ccw));
        assert(!(o is Cw));
    }
}

pub proof fn lemma_orientation_spec_translation_invariant(a: Point2, b: Point2, c: Point2, t: Vec2)
    ensures
        orientation_spec(a.add_vec_spec(t), b.add_vec_spec(t), c.add_vec_spec(t))
            == orientation_spec(a, b, c),
{
    lemma_orient2d_translation_invariant(a, b, c, t);
    let d0 = orient2d_spec(a, b, c);
    let d1 = orient2d_spec(a.add_vec_spec(t), b.add_vec_spec(t), c.add_vec_spec(t));
    assert(d1.as_int() == d0.as_int());
    Scalar::lemma_eq_from_as_int(d1, d0);
    assert(d1.signum() == d0.signum());
}

pub proof fn lemma_orient2d_scale_from_origin(a: Point2, b: Point2, c: Point2, k: Scalar)
    ensures
        orient2d_spec(
            scale_point_from_origin_spec(a, k),
            scale_point_from_origin_spec(b, k),
            scale_point_from_origin_spec(c, k),
        ).as_int() == k.mul_spec(k).mul_spec(orient2d_spec(a, b, c)).as_int(),
{
    let sa = scale_point_from_origin_spec(a, k);
    let sb = scale_point_from_origin_spec(b, k);
    let sc = scale_point_from_origin_spec(c, k);
    let ba = b.sub_spec(a);
    let ca = c.sub_spec(a);
    let sba = sb.sub_spec(sa);
    let sca = sc.sub_spec(sa);

    assert(sba.x.as_int() == (b.x.as_int() * k.as_int()) - (a.x.as_int() * k.as_int()));
    assert(sba.y.as_int() == (b.y.as_int() * k.as_int()) - (a.y.as_int() * k.as_int()));
    assert(sca.x.as_int() == (c.x.as_int() * k.as_int()) - (a.x.as_int() * k.as_int()));
    assert(sca.y.as_int() == (c.y.as_int() * k.as_int()) - (a.y.as_int() * k.as_int()));
    assert(ba.scale_spec(k).x.as_int() == (b.x.as_int() - a.x.as_int()) * k.as_int());
    assert(ba.scale_spec(k).y.as_int() == (b.y.as_int() - a.y.as_int()) * k.as_int());
    assert(ca.scale_spec(k).x.as_int() == (c.x.as_int() - a.x.as_int()) * k.as_int());
    assert(ca.scale_spec(k).y.as_int() == (c.y.as_int() - a.y.as_int()) * k.as_int());
    assert(((b.x.as_int() * k.as_int()) - (a.x.as_int() * k.as_int()))
        == (b.x.as_int() - a.x.as_int()) * k.as_int()) by (nonlinear_arith);
    assert(((b.y.as_int() * k.as_int()) - (a.y.as_int() * k.as_int()))
        == (b.y.as_int() - a.y.as_int()) * k.as_int()) by (nonlinear_arith);
    assert(((c.x.as_int() * k.as_int()) - (a.x.as_int() * k.as_int()))
        == (c.x.as_int() - a.x.as_int()) * k.as_int()) by (nonlinear_arith);
    assert(((c.y.as_int() * k.as_int()) - (a.y.as_int() * k.as_int()))
        == (c.y.as_int() - a.y.as_int()) * k.as_int()) by (nonlinear_arith);
    assert(sba.x.as_int() == ba.scale_spec(k).x.as_int());
    assert(sba.y.as_int() == ba.scale_spec(k).y.as_int());
    assert(sca.x.as_int() == ca.scale_spec(k).x.as_int());
    assert(sca.y.as_int() == ca.scale_spec(k).y.as_int());
    Vec2::lemma_eq_from_component_ints(sba, ba.scale_spec(k));
    Vec2::lemma_eq_from_component_ints(sca, ca.scale_spec(k));

    Vec2::lemma_cross_scale_extract_left(ba, ca.scale_spec(k), k);
    Vec2::lemma_cross_scale_extract_right(ba, ca, k);
    Scalar::lemma_mul_associative(k, k, ba.cross_spec(ca));

    assert(orient2d_spec(sa, sb, sc).as_int() == sba.cross_spec(sca).as_int());
    assert(orient2d_spec(a, b, c).as_int() == ba.cross_spec(ca).as_int());
    assert(sba.cross_spec(sca).as_int() == ba.scale_spec(k).cross_spec(ca.scale_spec(k)).as_int());
    assert(ba.scale_spec(k).cross_spec(ca.scale_spec(k)).as_int()
        == k.mul_spec(ba.cross_spec(ca.scale_spec(k))).as_int());
    assert(ba.cross_spec(ca.scale_spec(k)).as_int()
        == k.mul_spec(ba.cross_spec(ca)).as_int());
    assert(k.mul_spec(ba.cross_spec(ca.scale_spec(k))).as_int()
        == k.mul_spec(k.mul_spec(ba.cross_spec(ca))).as_int());
    assert(k.mul_spec(k.mul_spec(ba.cross_spec(ca))).as_int()
        == k.mul_spec(k).mul_spec(ba.cross_spec(ca)).as_int());
}

pub proof fn lemma_orientation_spec_scale_nonzero_preserves(a: Point2, b: Point2, c: Point2, k: Scalar)
    ensures
        k.as_int() != 0 ==> orientation_spec(
            scale_point_from_origin_spec(a, k),
            scale_point_from_origin_spec(b, k),
            scale_point_from_origin_spec(c, k),
        ) == orientation_spec(a, b, c),
{
    if k.as_int() != 0 {
        let sa = scale_point_from_origin_spec(a, k);
        let sb = scale_point_from_origin_spec(b, k);
        let sc = scale_point_from_origin_spec(c, k);

        lemma_orient2d_scale_from_origin(a, b, c, k);
        let o = orient2d_spec(a, b, c).as_int();
        let os = orient2d_spec(sa, sb, sc).as_int();
        let k2 = k.as_int() * k.as_int();
        assert(os == k2 * o);
        assert(o * k2 == k2 * o) by (nonlinear_arith);

        if k.as_int() > 0 {
            lemma_mul_strictly_positive(k.as_int(), k.as_int());
            assert(k2 > 0);
        } else {
            assert(k.as_int() < 0);
            assert(-k.as_int() > 0);
            lemma_mul_strictly_positive(-k.as_int(), -k.as_int());
            assert((-k.as_int()) * (-k.as_int()) > 0);
            lemma_mul_cancels_negatives(k.as_int(), k.as_int());
            assert(k2 == (-k.as_int()) * (-k.as_int()));
            assert(k2 > 0);
        }

        if o > 0 {
            lemma_mul_strictly_positive(k2, o);
            assert(os > 0);
            lemma_is_ccw_iff_positive(sa, sb, sc);
            lemma_is_ccw_iff_positive(a, b, c);
            lemma_orientation_spec_matches_predicates(sa, sb, sc);
            lemma_orientation_spec_matches_predicates(a, b, c);
            assert(orientation_spec(sa, sb, sc) is Ccw);
            assert(orientation_spec(a, b, c) is Ccw);
            assert(orientation_spec(sa, sb, sc) == orientation_spec(a, b, c));
        } else if o < 0 {
            lemma_mul_strict_inequality(o, 0, k2);
            assert(o * k2 < 0 * k2);
            assert(0 * k2 == 0);
            assert(os == o * k2);
            assert(os < 0);
            lemma_is_cw_iff_negative(sa, sb, sc);
            lemma_is_cw_iff_negative(a, b, c);
            lemma_orientation_spec_matches_predicates(sa, sb, sc);
            lemma_orientation_spec_matches_predicates(a, b, c);
            assert(orientation_spec(sa, sb, sc) is Cw);
            assert(orientation_spec(a, b, c) is Cw);
            assert(orientation_spec(sa, sb, sc) == orientation_spec(a, b, c));
        } else {
            assert(o == 0);
            assert(k2 * o == k2 * 0);
            assert(k2 * 0 == 0);
            assert(os == 0);
            lemma_is_collinear_iff_zero(sa, sb, sc);
            lemma_is_collinear_iff_zero(a, b, c);
            lemma_orientation_spec_matches_predicates(sa, sb, sc);
            lemma_orientation_spec_matches_predicates(a, b, c);
            assert(orientation_spec(sa, sb, sc) is Collinear);
            assert(orientation_spec(a, b, c) is Collinear);
            assert(orientation_spec(sa, sb, sc) == orientation_spec(a, b, c));
        }
    }
}

pub proof fn lemma_orientation_spec_scale_zero_collinear(a: Point2, b: Point2, c: Point2, k: Scalar)
    ensures
        k.as_int() == 0 ==> (orientation_spec(
            scale_point_from_origin_spec(a, k),
            scale_point_from_origin_spec(b, k),
            scale_point_from_origin_spec(c, k),
        ) is Collinear),
{
    if k.as_int() == 0 {
        let sa = scale_point_from_origin_spec(a, k);
        let sb = scale_point_from_origin_spec(b, k);
        let sc = scale_point_from_origin_spec(c, k);
        lemma_orient2d_scale_from_origin(a, b, c, k);
        assert(k.as_int() * k.as_int() == 0);
        assert(orient2d_spec(sa, sb, sc).as_int() == 0);
        lemma_is_collinear_iff_zero(sa, sb, sc);
        lemma_orientation_spec_matches_predicates(sa, sb, sc);
        assert(orientation_spec(sa, sb, sc) is Collinear);
    }
}

} // verus!
