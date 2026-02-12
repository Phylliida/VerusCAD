use vstd::prelude::*;

verus! {

/// Exact rational scalar.
///
/// `den` stores `(effective_denominator - 1)`, so effective denominator is
/// always at least `1`.
pub struct Scalar {
    pub num: int,
    pub den: nat,
}

impl Scalar {
    pub open spec fn dec_nat(x: nat) -> nat {
        (x - 1) as nat
    }

    pub proof fn lemma_dec_nat_plus_one(x: nat)
        requires
            x > 0,
        ensures
            Self::dec_nat(x) + 1 == x,
    {
        assert((x - 1) as nat + 1 == x) by (nonlinear_arith);
    }

    pub open spec fn denom_nat(self) -> nat {
        self.den + 1
    }

    pub open spec fn denom(self) -> int {
        self.denom_nat() as int
    }

    pub open spec fn as_real(self) -> real {
        self.num as real / self.denom_nat() as real
    }

    pub open spec fn from_int_spec(value: int) -> Self {
        Scalar { num: value, den: 0 }
    }

    pub proof fn new(value: int) -> (s: Self)
        ensures
            s == Self::from_int_spec(value),
    {
        Scalar { num: value, den: 0 }
    }

    pub proof fn from_int(value: int) -> (s: Self)
        ensures
            s == Self::from_int_spec(value),
    {
        Self::new(value)
    }

    pub proof fn from_frac(num: int, den: nat) -> (s: Self)
        requires
            den > 0,
        ensures
            s.num == num,
            s.denom_nat() == den,
    {
        let s = Scalar { num, den: Self::dec_nat(den) };
        Self::lemma_dec_nat_plus_one(den);
        assert(s.denom_nat() == den) by (nonlinear_arith);
        s
    }

    pub proof fn zero() -> (s: Self)
        ensures
            s == Self::from_int_spec(0),
    {
        Scalar { num: 0, den: 0 }
    }

    pub proof fn one() -> (s: Self)
        ensures
            s == Self::from_int_spec(1),
    {
        Scalar { num: 1, den: 0 }
    }

    pub open spec fn add_spec(self, rhs: Self) -> Self {
        let d1 = self.denom_nat();
        let d2 = rhs.denom_nat();
        Scalar {
            num: self.num * (d2 as int) + rhs.num * (d1 as int),
            den: Self::dec_nat(d1 * d2),
        }
    }

    pub proof fn add(self, rhs: Self) -> (out: Self)
        ensures
            out == self.add_spec(rhs),
    {
        let d1 = self.denom_nat();
        let d2 = rhs.denom_nat();
        Scalar {
            num: self.num * (d2 as int) + rhs.num * (d1 as int),
            den: Self::dec_nat(d1 * d2),
        }
    }

    pub open spec fn neg_spec(self) -> Self {
        Scalar { num: -self.num, den: self.den }
    }

    pub proof fn neg(self) -> (out: Self)
        ensures
            out == self.neg_spec(),
    {
        Scalar { num: -self.num, den: self.den }
    }

    pub open spec fn sub_spec(self, rhs: Self) -> Self {
        self.add_spec(rhs.neg_spec())
    }

    pub proof fn sub(self, rhs: Self) -> (out: Self)
        ensures
            out == self.sub_spec(rhs),
    {
        let neg_rhs = rhs.neg();
        self.add(neg_rhs)
    }

    pub open spec fn mul_spec(self, rhs: Self) -> Self {
        let d1 = self.denom_nat();
        let d2 = rhs.denom_nat();
        Scalar {
            num: self.num * rhs.num,
            den: Self::dec_nat(d1 * d2),
        }
    }

    pub proof fn mul(self, rhs: Self) -> (out: Self)
        ensures
            out == self.mul_spec(rhs),
    {
        let d1 = self.denom_nat();
        let d2 = rhs.denom_nat();
        Scalar {
            num: self.num * rhs.num,
            den: Self::dec_nat(d1 * d2),
        }
    }

    pub open spec fn signum(self) -> int {
        if self.num > 0 {
            1
        } else if self.num < 0 {
            -1
        } else {
            0
        }
    }

    pub open spec fn eqv_spec(self, rhs: Self) -> bool {
        self.as_real() == rhs.as_real()
    }

    pub proof fn lemma_signum_positive_iff(a: Self)
        ensures
            (a.signum() == 1) == (a.num > 0),
    {
        if a.num > 0 {
            assert(a.signum() == 1);
        } else {
            assert(a.signum() != 1);
        }
    }

    pub proof fn lemma_signum_negative_iff(a: Self)
        ensures
            (a.signum() == -1) == (a.num < 0),
    {
        if a.num < 0 {
            assert(a.signum() == -1);
        } else {
            assert(a.signum() != -1);
        }
    }

    pub proof fn lemma_signum_zero_iff(a: Self)
        ensures
            (a.signum() == 0) == (a.num == 0),
    {
        if a.num == 0 {
            assert(a.signum() == 0);
        } else {
            assert(a.signum() != 0);
        }
    }

    pub proof fn lemma_signum_cases(a: Self)
        ensures
            a.signum() == 1 || a.signum() == -1 || a.signum() == 0,
    {
        if a.num > 0 {
            assert(a.signum() == 1);
        } else if a.num < 0 {
            assert(a.signum() == -1);
        } else {
            assert(a.signum() == 0);
        }
    }
}

} // verus!
