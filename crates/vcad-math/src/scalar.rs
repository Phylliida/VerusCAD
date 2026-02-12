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

    // Internal bridge for the current integer-backed prototype.
    // This is intentionally non-public so representation-dependent
    // reasoning does not leak into public law APIs.
    pub(crate) proof fn lemma_eq_from_as_int_internal(a: Self, b: Self)
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
        Self::lemma_eq_from_as_int_internal(lhs, rhs);
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
        Self::lemma_eq_from_as_int_internal(lhs, rhs);
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
        Self::lemma_eq_from_as_int_internal(lhs, rhs);
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
        Self::lemma_eq_from_as_int_internal(lhs, rhs);
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
        Self::lemma_eq_from_as_int_internal(lhs, rhs);
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
        Self::lemma_eq_from_as_int_internal(lhs, a);
        Self::lemma_eq_from_as_int_internal(rhs, a);
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
        Self::lemma_eq_from_as_int_internal(lhs, a);
        Self::lemma_eq_from_as_int_internal(rhs, a);
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
        Self::lemma_eq_from_as_int_internal(lhs, z);
        Self::lemma_eq_from_as_int_internal(rhs, z);
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
        Self::lemma_eq_from_as_int_internal(lhs, rhs);
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
        Self::lemma_eq_from_as_int_internal(a, b);
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
        Self::lemma_eq_from_as_int_internal(a, b);
    }

    pub proof fn lemma_mul_zero(a: Self)
        ensures
            a.mul_spec(Scalar { value: 0 }).as_int() == 0,
            (Scalar { value: 0 }).mul_spec(a).as_int() == 0,
    {
        assert(a.mul_spec(Scalar { value: 0 }).as_int() == a.as_int() * 0);
        assert((Scalar { value: 0 }).mul_spec(a).as_int() == 0 * a.as_int());
        assert(a.as_int() * 0 == 0) by (nonlinear_arith);
        assert(0 * a.as_int() == 0) by (nonlinear_arith);
        assert(a.mul_spec(Scalar { value: 0 }).as_int() == 0);
        assert((Scalar { value: 0 }).mul_spec(a).as_int() == 0);
    }

    pub proof fn lemma_mul_zero_implies_factor_zero(a: Self, b: Self)
        ensures
            a.mul_spec(b).as_int() == 0 ==> a.as_int() == 0 || b.as_int() == 0,
    {
        assert(a.mul_spec(b).as_int() == a.as_int() * b.as_int());
        assert((a.as_int() * b.as_int() == 0) ==> (a.as_int() == 0 || b.as_int() == 0)) by (nonlinear_arith);
        assert((a.mul_spec(b).as_int() == 0) ==> (a.as_int() == 0 || b.as_int() == 0));
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
        assert(a.add_spec(c).as_int() == a.as_int() + c.as_int());
        assert(b.add_spec(c).as_int() == b.as_int() + c.as_int());
        assert((a.as_int() <= b.as_int()) ==> (a.as_int() + c.as_int() <= b.as_int() + c.as_int())) by (nonlinear_arith);
        assert(a.as_int() + c.as_int() <= b.as_int() + c.as_int());
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
        assert(a.mul_spec(c).as_int() == a.as_int() * c.as_int());
        assert(b.mul_spec(c).as_int() == b.as_int() * c.as_int());
        assert((0 <= c.as_int() && a.as_int() <= b.as_int()) ==> (a.as_int() * c.as_int() <= b.as_int() * c.as_int())) by (nonlinear_arith);
        assert(a.as_int() * c.as_int() <= b.as_int() * c.as_int());
        assert(a.mul_spec(c).as_int() <= b.mul_spec(c).as_int());
    }
}

} // verus!
