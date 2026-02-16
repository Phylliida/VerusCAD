use core::hash::{Hash, Hasher};
use rug::{Integer, Rational};
#[cfg(verus_keep_ghost)]
use crate::runtime_bigint_witness::RuntimeBigNatWitness;
#[cfg(verus_keep_ghost)]
use crate::scalar::ScalarModel;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::mul::{lemma_mul_basics, lemma_mul_strict_inequality};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::View;

/// Runtime rational scalar backed by `rug::Rational`.
///
/// This type is for executable paths. The proof model remains in `ScalarModel`.
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, Eq, PartialEq))]
#[cfg_attr(verus_keep_ghost, derive(Clone))]
pub struct RuntimeScalar {
    #[cfg(not(verus_keep_ghost))]
    value: Rational,
    #[cfg(verus_keep_ghost)]
    pub sign_witness: RuntimeSign,
    #[cfg(verus_keep_ghost)]
    pub num_abs_witness: RuntimeBigNatWitness,
    #[cfg(verus_keep_ghost)]
    pub den_witness: RuntimeBigNatWitness,
    #[cfg(verus_keep_ghost)]
    pub model: Ghost<ScalarModel>,
}

#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuntimeSign {
    Negative,
    Zero,
    Positive,
}

#[cfg(verus_keep_ghost)]
verus! {
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuntimeSign {
    Negative,
    Zero,
    Positive,
}
}

#[cfg(verus_keep_ghost)]
impl core::fmt::Debug for RuntimeScalar {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("RuntimeScalar")
    }
}

#[cfg(verus_keep_ghost)]
impl PartialEq for RuntimeScalar {
    fn eq(&self, other: &Self) -> bool {
        core::ptr::eq(self, other)
    }
}

#[cfg(verus_keep_ghost)]
impl Eq for RuntimeScalar {}

#[cfg(not(verus_keep_ghost))]
impl RuntimeScalar {
    pub fn from_int(value: i64) -> Self {
        Self { value: Rational::from(value) }
    }

    pub fn from_fraction(num: Integer, den: Integer) -> Option<Self> {
        if den == 0 {
            return None;
        }
        Some(Self { value: Rational::from((num, den)) })
    }

    pub fn value(&self) -> &Rational {
        &self.value
    }

    pub fn add(&self, rhs: &Self) -> Self {
        let mut out = self.value.clone();
        out += &rhs.value;
        Self { value: out }
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        let mut out = self.value.clone();
        out -= &rhs.value;
        Self { value: out }
    }

    pub fn mul(&self, rhs: &Self) -> Self {
        let mut out = self.value.clone();
        out *= &rhs.value;
        Self { value: out }
    }

    pub fn recip(&self) -> Option<Self> {
        if self.value == 0 {
            return None;
        }
        Some(Self { value: Rational::from(1) / self.value.clone() })
    }

    pub fn neg(&self) -> Self {
        Self { value: -self.value.clone() }
    }

    /// Returns the canonical normalized runtime representation.
    ///
    /// `rug::Rational` maintains canonical form internally, so this is a
    /// semantic no-op that provides an explicit API boundary.
    pub fn normalize(&self) -> Self {
        Self { value: self.value.clone() }
    }

    pub fn sign(&self) -> RuntimeSign {
        if self.value > 0 {
            RuntimeSign::Positive
        } else if self.value < 0 {
            RuntimeSign::Negative
        } else {
            RuntimeSign::Zero
        }
    }

    pub fn signum_i8(&self) -> i8 {
        match self.sign() {
            RuntimeSign::Positive => 1,
            RuntimeSign::Negative => -1,
            RuntimeSign::Zero => 0,
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
impl RuntimeScalar {
    pub open spec fn sign_neg_spec(sign: RuntimeSign) -> RuntimeSign {
        match sign {
            RuntimeSign::Negative => RuntimeSign::Positive,
            RuntimeSign::Zero => RuntimeSign::Zero,
            RuntimeSign::Positive => RuntimeSign::Negative,
        }
    }

    pub open spec fn sign_mul_spec(lhs: RuntimeSign, rhs: RuntimeSign) -> RuntimeSign {
        match (lhs, rhs) {
            (RuntimeSign::Zero, _) | (_, RuntimeSign::Zero) => RuntimeSign::Zero,
            (RuntimeSign::Positive, RuntimeSign::Positive)
            | (RuntimeSign::Negative, RuntimeSign::Negative) => RuntimeSign::Positive,
            (RuntimeSign::Positive, RuntimeSign::Negative)
            | (RuntimeSign::Negative, RuntimeSign::Positive) => RuntimeSign::Negative,
        }
    }

    pub open spec fn signed_from_parts_spec(sign: RuntimeSign, abs: nat) -> int {
        match sign {
            RuntimeSign::Negative => -(abs as int),
            RuntimeSign::Zero => 0,
            RuntimeSign::Positive => abs as int,
        }
    }

    pub open spec fn sign_parts_wf_spec(sign: RuntimeSign, abs: nat) -> bool {
        match sign {
            RuntimeSign::Negative => Self::signed_from_parts_spec(sign, abs) < 0,
            RuntimeSign::Zero => Self::signed_from_parts_spec(sign, abs) == 0,
            RuntimeSign::Positive => Self::signed_from_parts_spec(sign, abs) > 0,
        }
    }

    fn sign_neg_witness(sign: RuntimeSign) -> (out: RuntimeSign)
        ensures
            out == Self::sign_neg_spec(sign),
            (sign is Negative) ==> (out is Positive),
            (sign is Zero) ==> (out is Zero),
            (sign is Positive) ==> (out is Negative),
    {
        match sign {
            RuntimeSign::Negative => RuntimeSign::Positive,
            RuntimeSign::Zero => RuntimeSign::Zero,
            RuntimeSign::Positive => RuntimeSign::Negative,
        }
    }

    fn sign_mul_witness(lhs: RuntimeSign, rhs: RuntimeSign) -> (out: RuntimeSign)
        ensures
            out == Self::sign_mul_spec(lhs, rhs),
            (out is Zero) == ((lhs is Zero) || (rhs is Zero)),
            (out is Positive) == ((lhs is Positive && rhs is Positive)
                || (lhs is Negative && rhs is Negative)),
            (out is Negative) == ((lhs is Positive && rhs is Negative)
                || (lhs is Negative && rhs is Positive)),
    {
        match (lhs, rhs) {
            (RuntimeSign::Zero, _) | (_, RuntimeSign::Zero) => RuntimeSign::Zero,
            (RuntimeSign::Positive, RuntimeSign::Positive)
            | (RuntimeSign::Negative, RuntimeSign::Negative) => RuntimeSign::Positive,
            (RuntimeSign::Positive, RuntimeSign::Negative)
            | (RuntimeSign::Negative, RuntimeSign::Positive) => RuntimeSign::Negative,
        }
    }

    pub open spec fn signed_num_witness_spec(&self) -> int {
        Self::signed_from_parts_spec(self.sign_witness, self.num_abs_witness.model@)
    }

    pub open spec fn witness_wf_spec(&self) -> bool {
        &&& self.num_abs_witness.wf_spec()
        &&& self.den_witness.wf_spec()
        &&& self.den_witness.model@ > 0
        &&& match self.sign_witness {
            RuntimeSign::Negative => self.signed_num_witness_spec() < 0,
            RuntimeSign::Zero => self.signed_num_witness_spec() == 0,
            RuntimeSign::Positive => self.signed_num_witness_spec() > 0,
        }
        &&& self.signed_num_witness_spec() * self@.denom()
                == self@.num * (self.den_witness.model@ as int)
    }

    proof fn lemma_nat_product_positive(a: nat, b: nat)
        requires
            a > 0,
            b > 0,
        ensures
            a * b > 0,
    {
        assert(0 < a as int);
        assert(0 < b as int);
        lemma_mul_strict_inequality(0, a as int, b as int);
        lemma_mul_basics(b as int);
        assert(0 * (b as int) == 0);
        assert(0 < (a as int) * (b as int));
        assert((a * b) as int == (a as int) * (b as int)) by (nonlinear_arith);
        assert((a * b) as int > 0);
        assert(a * b > 0);
    }

    proof fn lemma_sign_parts_wf_from_witness_wf(&self)
        requires
            self.witness_wf_spec(),
        ensures
            Self::sign_parts_wf_spec(self.sign_witness, self.num_abs_witness.model@),
    {
        assert(Self::signed_from_parts_spec(self.sign_witness, self.num_abs_witness.model@)
            == self.signed_num_witness_spec());
        match self.sign_witness {
            RuntimeSign::Positive => {
                assert(self.signed_num_witness_spec() > 0);
                assert(Self::sign_parts_wf_spec(self.sign_witness, self.num_abs_witness.model@));
            }
            RuntimeSign::Negative => {
                assert(self.signed_num_witness_spec() < 0);
                assert(Self::sign_parts_wf_spec(self.sign_witness, self.num_abs_witness.model@));
            }
            RuntimeSign::Zero => {
                assert(self.signed_num_witness_spec() == 0);
                assert(Self::sign_parts_wf_spec(self.sign_witness, self.num_abs_witness.model@));
            }
        }
    }

    proof fn lemma_abs_positive_from_sign_parts(sign: RuntimeSign, abs: nat)
        requires
            Self::sign_parts_wf_spec(sign, abs),
            !(sign is Zero),
        ensures
            abs > 0,
    {
        match sign {
            RuntimeSign::Positive => {
                assert(Self::signed_from_parts_spec(sign, abs) == abs as int);
                assert(abs as int > 0);
                assert(abs > 0);
            }
            RuntimeSign::Negative => {
                assert(Self::signed_from_parts_spec(sign, abs) == -(abs as int));
                assert(-(abs as int) < 0);
                assert((-(abs as int) < 0) ==> abs as int > 0) by (nonlinear_arith);
                assert(abs as int > 0);
                assert(abs > 0);
            }
            RuntimeSign::Zero => {
                assert(false);
            }
        }
    }

    pub proof fn lemma_witness_sign_matches_model(&self)
        requires
            self.witness_wf_spec(),
        ensures
            (self.sign_witness is Positive) == (self@.signum() == 1),
            (self.sign_witness is Negative) == (self@.signum() == -1),
            (self.sign_witness is Zero) == (self@.signum() == 0),
    {
        ScalarModel::lemma_denom_positive(self@);
        ScalarModel::lemma_signum_positive_iff(self@);
        ScalarModel::lemma_signum_negative_iff(self@);
        ScalarModel::lemma_signum_zero_iff(self@);
        if self.sign_witness is Positive {
            assert(self.signed_num_witness_spec() > 0);
            assert(self@.denom() > 0);
            assert(self.den_witness.model@ as int > 0);
            assert((self.signed_num_witness_spec() > 0 && self@.denom() > 0)
                ==> self.signed_num_witness_spec() * self@.denom() > 0) by (nonlinear_arith);
            assert(self.signed_num_witness_spec() * self@.denom() > 0);
            assert(self.signed_num_witness_spec() * self@.denom()
                == self@.num * (self.den_witness.model@ as int));
            assert(self@.num * (self.den_witness.model@ as int) > 0);
            assert((self.den_witness.model@ as int > 0
                && self@.num * (self.den_witness.model@ as int) > 0) ==> self@.num > 0) by (nonlinear_arith);
            assert(self@.num > 0);
            assert(self@.signum() == 1);
            assert(!(self.sign_witness is Negative));
            assert(!(self.sign_witness is Zero));
            assert(self@.signum() != -1);
            assert(self@.signum() != 0);
        } else if self.sign_witness is Negative {
            assert(self.signed_num_witness_spec() < 0);
            assert(self@.denom() > 0);
            assert(self.den_witness.model@ as int > 0);
            assert((self.signed_num_witness_spec() < 0 && self@.denom() > 0)
                ==> self.signed_num_witness_spec() * self@.denom() < 0) by (nonlinear_arith);
            assert(self.signed_num_witness_spec() * self@.denom() < 0);
            assert(self.signed_num_witness_spec() * self@.denom()
                == self@.num * (self.den_witness.model@ as int));
            assert(self@.num * (self.den_witness.model@ as int) < 0);
            assert((self.den_witness.model@ as int > 0
                && self@.num * (self.den_witness.model@ as int) < 0) ==> self@.num < 0) by (nonlinear_arith);
            assert(self@.num < 0);
            assert(self@.signum() == -1);
            assert(!(self.sign_witness is Positive));
            assert(!(self.sign_witness is Zero));
            assert(self@.signum() != 1);
            assert(self@.signum() != 0);
        } else {
            assert(self.sign_witness is Zero);
            assert(self.signed_num_witness_spec() == 0);
            assert(self.signed_num_witness_spec() * self@.denom() == 0);
            assert(self.signed_num_witness_spec() * self@.denom()
                == self@.num * (self.den_witness.model@ as int));
            assert(self@.num * (self.den_witness.model@ as int) == 0);
            assert(self.den_witness.model@ as int > 0);
            assert((self.den_witness.model@ as int > 0
                && self@.num * (self.den_witness.model@ as int) == 0) ==> self@.num == 0) by (nonlinear_arith);
            assert(self@.num == 0);
            assert(self@.signum() == 0);
            assert(!(self.sign_witness is Positive));
            assert(!(self.sign_witness is Negative));
            assert(self@.signum() != 1);
            assert(self@.signum() != -1);
        }
    }

    proof fn lemma_int_pos_negates_to_neg(x: int)
        requires
            x > 0,
        ensures
            -x < 0,
    {
        assert((x > 0) ==> 0 - x < 0) by (nonlinear_arith);
        assert(0 - x < 0);
        assert(-x == 0 - x);
        assert(-x < 0);
    }

    proof fn lemma_int_neg_negates_to_pos(x: int)
        requires
            x < 0,
        ensures
            -x > 0,
    {
        assert((x < 0) ==> 0 - x > 0) by (nonlinear_arith);
        assert(0 - x > 0);
        assert(-x == 0 - x);
        assert(-x > 0);
    }

    proof fn lemma_signed_from_parts_mul(
        lhs_sign: RuntimeSign,
        lhs_abs: nat,
        rhs_sign: RuntimeSign,
        rhs_abs: nat,
    )
        ensures
            Self::signed_from_parts_spec(
                Self::sign_mul_spec(lhs_sign, rhs_sign),
                lhs_abs * rhs_abs,
            ) == Self::signed_from_parts_spec(lhs_sign, lhs_abs)
                * Self::signed_from_parts_spec(rhs_sign, rhs_abs),
    {
        match lhs_sign {
            RuntimeSign::Zero => {
                assert(Self::sign_mul_spec(lhs_sign, rhs_sign) is Zero);
                assert(Self::signed_from_parts_spec(Self::sign_mul_spec(lhs_sign, rhs_sign), lhs_abs * rhs_abs) == 0);
                assert(Self::signed_from_parts_spec(lhs_sign, lhs_abs) == 0);
                assert(
                    Self::signed_from_parts_spec(lhs_sign, lhs_abs)
                        * Self::signed_from_parts_spec(rhs_sign, rhs_abs)
                        == 0
                );
            }
            RuntimeSign::Positive => {
                match rhs_sign {
                    RuntimeSign::Zero => {
                        assert(Self::sign_mul_spec(lhs_sign, rhs_sign) is Zero);
                        assert(Self::signed_from_parts_spec(Self::sign_mul_spec(lhs_sign, rhs_sign), lhs_abs * rhs_abs) == 0);
                        assert(Self::signed_from_parts_spec(rhs_sign, rhs_abs) == 0);
                        assert(
                            Self::signed_from_parts_spec(lhs_sign, lhs_abs)
                                * Self::signed_from_parts_spec(rhs_sign, rhs_abs)
                                == 0
                        );
                    }
                    RuntimeSign::Positive => {
                        assert(Self::sign_mul_spec(lhs_sign, rhs_sign) is Positive);
                        assert(Self::signed_from_parts_spec(Self::sign_mul_spec(lhs_sign, rhs_sign), lhs_abs * rhs_abs)
                            == (lhs_abs * rhs_abs) as int);
                        assert(Self::signed_from_parts_spec(lhs_sign, lhs_abs) == lhs_abs as int);
                        assert(Self::signed_from_parts_spec(rhs_sign, rhs_abs) == rhs_abs as int);
                        assert((lhs_abs * rhs_abs) as int
                            == (lhs_abs as int) * (rhs_abs as int)) by (nonlinear_arith);
                    }
                    RuntimeSign::Negative => {
                        assert(Self::sign_mul_spec(lhs_sign, rhs_sign) is Negative);
                        assert(Self::signed_from_parts_spec(Self::sign_mul_spec(lhs_sign, rhs_sign), lhs_abs * rhs_abs)
                            == -((lhs_abs * rhs_abs) as int));
                        assert(Self::signed_from_parts_spec(lhs_sign, lhs_abs) == lhs_abs as int);
                        assert(Self::signed_from_parts_spec(rhs_sign, rhs_abs) == -(rhs_abs as int));
                        assert((lhs_abs * rhs_abs) as int
                            == (lhs_abs as int) * (rhs_abs as int)) by (nonlinear_arith);
                        assert((lhs_abs as int) * (-(rhs_abs as int))
                            == -((lhs_abs as int) * (rhs_abs as int))) by (nonlinear_arith);
                    }
                }
            }
            RuntimeSign::Negative => {
                match rhs_sign {
                    RuntimeSign::Zero => {
                        assert(Self::sign_mul_spec(lhs_sign, rhs_sign) is Zero);
                        assert(Self::signed_from_parts_spec(Self::sign_mul_spec(lhs_sign, rhs_sign), lhs_abs * rhs_abs) == 0);
                        assert(Self::signed_from_parts_spec(rhs_sign, rhs_abs) == 0);
                        assert(
                            Self::signed_from_parts_spec(lhs_sign, lhs_abs)
                                * Self::signed_from_parts_spec(rhs_sign, rhs_abs)
                                == 0
                        );
                    }
                    RuntimeSign::Positive => {
                        assert(Self::sign_mul_spec(lhs_sign, rhs_sign) is Negative);
                        assert(Self::signed_from_parts_spec(Self::sign_mul_spec(lhs_sign, rhs_sign), lhs_abs * rhs_abs)
                            == -((lhs_abs * rhs_abs) as int));
                        assert(Self::signed_from_parts_spec(lhs_sign, lhs_abs) == -(lhs_abs as int));
                        assert(Self::signed_from_parts_spec(rhs_sign, rhs_abs) == rhs_abs as int);
                        assert((lhs_abs * rhs_abs) as int
                            == (lhs_abs as int) * (rhs_abs as int)) by (nonlinear_arith);
                        assert((-(lhs_abs as int)) * (rhs_abs as int)
                            == -((lhs_abs as int) * (rhs_abs as int))) by (nonlinear_arith);
                    }
                    RuntimeSign::Negative => {
                        assert(Self::sign_mul_spec(lhs_sign, rhs_sign) is Positive);
                        assert(Self::signed_from_parts_spec(Self::sign_mul_spec(lhs_sign, rhs_sign), lhs_abs * rhs_abs)
                            == (lhs_abs * rhs_abs) as int);
                        assert(Self::signed_from_parts_spec(lhs_sign, lhs_abs) == -(lhs_abs as int));
                        assert(Self::signed_from_parts_spec(rhs_sign, rhs_abs) == -(rhs_abs as int));
                        assert((lhs_abs * rhs_abs) as int
                            == (lhs_abs as int) * (rhs_abs as int)) by (nonlinear_arith);
                        assert((-(lhs_abs as int)) * (-(rhs_abs as int))
                            == (lhs_abs as int) * (rhs_abs as int)) by (nonlinear_arith);
                    }
                }
            }
        }
    }

    fn add_signed_witness(
        lhs_sign: RuntimeSign,
        lhs_num_abs: &RuntimeBigNatWitness,
        lhs_den: &RuntimeBigNatWitness,
        rhs_sign: RuntimeSign,
        rhs_num_abs: &RuntimeBigNatWitness,
        rhs_den: &RuntimeBigNatWitness,
    ) -> (out: (RuntimeSign, RuntimeBigNatWitness))
    {
        let lhs_scaled = lhs_num_abs.mul_limbwise_small_total(rhs_den);
        let rhs_scaled = rhs_num_abs.mul_limbwise_small_total(lhs_den);
        match (lhs_sign, rhs_sign) {
            (RuntimeSign::Zero, _) => (rhs_sign, rhs_scaled),
            (_, RuntimeSign::Zero) => (lhs_sign, lhs_scaled),
            (RuntimeSign::Positive, RuntimeSign::Positive)
            | (RuntimeSign::Negative, RuntimeSign::Negative) => {
                (lhs_sign, lhs_scaled.add_limbwise_small_total(&rhs_scaled))
            }
            (RuntimeSign::Positive, RuntimeSign::Negative) => {
                let cmp = lhs_scaled.cmp_limbwise_small_total(&rhs_scaled);
                if cmp == 1 {
                    (RuntimeSign::Positive, lhs_scaled.sub_limbwise_small_total(&rhs_scaled))
                } else if cmp == -1 {
                    (RuntimeSign::Negative, rhs_scaled.sub_limbwise_small_total(&lhs_scaled))
                } else {
                    (RuntimeSign::Zero, RuntimeBigNatWitness::zero())
                }
            }
            (RuntimeSign::Negative, RuntimeSign::Positive) => {
                let cmp = lhs_scaled.cmp_limbwise_small_total(&rhs_scaled);
                if cmp == 1 {
                    (RuntimeSign::Negative, lhs_scaled.sub_limbwise_small_total(&rhs_scaled))
                } else if cmp == -1 {
                    (RuntimeSign::Positive, rhs_scaled.sub_limbwise_small_total(&lhs_scaled))
                } else {
                    (RuntimeSign::Zero, RuntimeBigNatWitness::zero())
                }
            }
        }
    }

    fn from_model(Ghost(model): Ghost<ScalarModel>) -> (out: Self)
        ensures
            out@ == model,
    {
        // Phase-2 scaffold: explicit exec-visible bigint witnesses are now
        // carried on the verus runtime scalar object. Arithmetic constructors
        // still route through this placeholder until each operation is migrated
        // to witness-preserving updates.
        RuntimeScalar {
            sign_witness: RuntimeSign::Zero,
            num_abs_witness: RuntimeBigNatWitness::zero(),
            den_witness: RuntimeBigNatWitness::from_u32(1),
            model: Ghost(model),
        }
    }

    pub fn from_int(value: i64) -> (out: Self)
        ensures
            out@ == ScalarModel::from_int_spec(value as int),
            out.witness_wf_spec(),
    {
        let sign_witness = if value > 0 {
            RuntimeSign::Positive
        } else if value < 0 {
            RuntimeSign::Negative
        } else {
            RuntimeSign::Zero
        };
        let abs_u64 = if value == -9_223_372_036_854_775_808i64 {
            9_223_372_036_854_775_808u64
        } else if value < 0 {
            (-value) as u64
        } else {
            value as u64
        };
        let out = RuntimeScalar {
            sign_witness,
            num_abs_witness: RuntimeBigNatWitness::from_u64(abs_u64),
            den_witness: RuntimeBigNatWitness::from_u32(1),
            model: Ghost(ScalarModel::from_int_spec(value as int)),
        };
        proof {
            assert(out@ == ScalarModel::from_int_spec(value as int));
            assert(out.num_abs_witness.model@ == abs_u64 as nat);
            assert(out.den_witness.model@ == 1);
            assert(out@.denom() == 1);
            assert(out.den_witness.model@ > 0);
            if value > 0 {
                assert(sign_witness is Positive);
                assert(abs_u64 == value as u64);
                assert(abs_u64 as int == value as int);
                assert(out.signed_num_witness_spec() == out.num_abs_witness.model@ as int);
                assert(out.signed_num_witness_spec() == value as int);
                assert(out.signed_num_witness_spec() > 0);
                assert(out@.num == value as int);
                assert(out.signed_num_witness_spec() * out@.denom()
                    == value as int * 1);
                assert(out@.num * (out.den_witness.model@ as int)
                    == value as int * 1);
            } else if value < 0 {
                assert(sign_witness is Negative);
                if value == -9_223_372_036_854_775_808i64 {
                    assert(abs_u64 == 9_223_372_036_854_775_808u64);
                    assert(value as int == -9_223_372_036_854_775_808int);
                    assert(abs_u64 as int == 9_223_372_036_854_775_808int);
                    assert(value as int == -(abs_u64 as int));
                } else {
                    assert(abs_u64 == (-value) as u64);
                    assert((-value) as int == abs_u64 as int);
                    assert(value as int == -(abs_u64 as int));
                }
                assert(out.signed_num_witness_spec() == -(out.num_abs_witness.model@ as int));
                assert(out.signed_num_witness_spec() == -(abs_u64 as int));
                assert(out.signed_num_witness_spec() == value as int);
                assert(out.signed_num_witness_spec() < 0);
                assert(out@.num == value as int);
                assert(out.signed_num_witness_spec() * out@.denom()
                    == value as int * 1);
                assert(out@.num * (out.den_witness.model@ as int)
                    == value as int * 1);
            } else {
                assert(sign_witness is Zero);
                assert(abs_u64 == 0u64);
                assert(out.signed_num_witness_spec() == 0);
                assert(out.signed_num_witness_spec() * out@.denom() == 0);
                assert(out@.num == 0);
                assert(out@.num * (out.den_witness.model@ as int) == 0);
            }
            assert(out.signed_num_witness_spec() * out@.denom()
                == out@.num * (out.den_witness.model@ as int));
            assert(out.witness_wf_spec());
        }
        out
    }

    pub fn add(&self, rhs: &Self) -> (out: Self)
        ensures
            out@ == self@.add_spec(rhs@),
    {
        let ghost model = self@.add_spec(rhs@);
        let (sign_witness, num_abs_witness) = Self::add_signed_witness(
            self.sign_witness,
            &self.num_abs_witness,
            &self.den_witness,
            rhs.sign_witness,
            &rhs.num_abs_witness,
            &rhs.den_witness,
        );
        let den_witness = self.den_witness.mul_limbwise_small_total(&rhs.den_witness);
        let out = RuntimeScalar {
            sign_witness,
            num_abs_witness,
            den_witness,
            model: Ghost(model),
        };
        proof {
            assert(out@ == self@.add_spec(rhs@));
        }
        out
    }

    pub fn sub(&self, rhs: &Self) -> (out: Self)
        ensures
            out@ == self@.sub_spec(rhs@),
    {
        let ghost model = self@.sub_spec(rhs@);
        let rhs_neg_sign = Self::sign_neg_witness(rhs.sign_witness);
        let (sign_witness, num_abs_witness) = Self::add_signed_witness(
            self.sign_witness,
            &self.num_abs_witness,
            &self.den_witness,
            rhs_neg_sign,
            &rhs.num_abs_witness,
            &rhs.den_witness,
        );
        let den_witness = self.den_witness.mul_limbwise_small_total(&rhs.den_witness);
        let out = RuntimeScalar {
            sign_witness,
            num_abs_witness,
            den_witness,
            model: Ghost(model),
        };
        proof {
            assert(out@ == self@.sub_spec(rhs@));
        }
        out
    }

    pub fn mul(&self, rhs: &Self) -> (out: Self)
        ensures
            out@ == self@.mul_spec(rhs@),
    {
        let ghost model = self@.mul_spec(rhs@);
        let num_abs_witness = self.num_abs_witness.mul_limbwise_small_total(&rhs.num_abs_witness);
        let den_witness = self.den_witness.mul_limbwise_small_total(&rhs.den_witness);
        let out = RuntimeScalar {
            sign_witness: Self::sign_mul_witness(self.sign_witness, rhs.sign_witness),
            num_abs_witness,
            den_witness,
            model: Ghost(model),
        };
        proof {
            assert(out@ == self@.mul_spec(rhs@));
        }
        out
    }

    pub fn mul_wf(&self, rhs: &Self) -> (out: Self)
        requires
            self.witness_wf_spec(),
            rhs.witness_wf_spec(),
        ensures
            out@ == self@.mul_spec(rhs@),
            out.witness_wf_spec(),
    {
        let ghost model = self@.mul_spec(rhs@);
        let num_abs_witness = self.num_abs_witness.mul_limbwise_small_total(&rhs.num_abs_witness);
        let den_witness = self.den_witness.mul_limbwise_small_total(&rhs.den_witness);
        let sign_witness = Self::sign_mul_witness(self.sign_witness, rhs.sign_witness);
        let out = RuntimeScalar {
            sign_witness,
            num_abs_witness,
            den_witness,
            model: Ghost(model),
        };
        proof {
            assert(out@ == self@.mul_spec(rhs@));
            assert(out.num_abs_witness.wf_spec());
            assert(out.den_witness.wf_spec());
            assert(out.num_abs_witness.model@ == self.num_abs_witness.model@ * rhs.num_abs_witness.model@);
            assert(out.den_witness.model@ == self.den_witness.model@ * rhs.den_witness.model@);
            assert(self.den_witness.model@ > 0);
            assert(rhs.den_witness.model@ > 0);
            Self::lemma_nat_product_positive(self.den_witness.model@, rhs.den_witness.model@);
            assert(out.den_witness.model@ == self.den_witness.model@ * rhs.den_witness.model@);
            assert(out.den_witness.model@ > 0);

            let ghost s1 = self.signed_num_witness_spec();
            let ghost s2 = rhs.signed_num_witness_spec();
            let ghost so = out.signed_num_witness_spec();
            self.lemma_sign_parts_wf_from_witness_wf();
            rhs.lemma_sign_parts_wf_from_witness_wf();
            Self::lemma_signed_from_parts_mul(
                self.sign_witness,
                self.num_abs_witness.model@,
                rhs.sign_witness,
                rhs.num_abs_witness.model@,
            );
            assert(
                so
                    == Self::signed_from_parts_spec(
                        Self::sign_mul_spec(self.sign_witness, rhs.sign_witness),
                        self.num_abs_witness.model@ * rhs.num_abs_witness.model@,
                    )
            );
            assert(sign_witness == Self::sign_mul_spec(self.sign_witness, rhs.sign_witness));
            assert(so == s1 * s2);

            if sign_witness is Zero {
                assert(
                    (sign_witness is Zero)
                        == ((self.sign_witness is Zero) || (rhs.sign_witness is Zero))
                );
                assert((self.sign_witness is Zero) || (rhs.sign_witness is Zero));
                if self.sign_witness is Zero {
                    assert(s1 == 0);
                } else {
                    assert(rhs.sign_witness is Zero);
                    assert(s2 == 0);
                }
                assert(so == s1 * s2);
                assert(so == 0);
                assert(Self::sign_parts_wf_spec(sign_witness, out.num_abs_witness.model@));
            } else if sign_witness is Positive {
                assert(
                    (sign_witness is Positive)
                        == ((self.sign_witness is Positive && rhs.sign_witness is Positive)
                            || (self.sign_witness is Negative && rhs.sign_witness is Negative))
                );
                assert(
                    (self.sign_witness is Positive && rhs.sign_witness is Positive)
                        || (self.sign_witness is Negative && rhs.sign_witness is Negative)
                );
                if self.sign_witness is Positive && rhs.sign_witness is Positive {
                    Self::lemma_abs_positive_from_sign_parts(
                        self.sign_witness,
                        self.num_abs_witness.model@,
                    );
                    Self::lemma_abs_positive_from_sign_parts(
                        rhs.sign_witness,
                        rhs.num_abs_witness.model@,
                    );
                } else {
                    assert(self.sign_witness is Negative && rhs.sign_witness is Negative);
                    Self::lemma_abs_positive_from_sign_parts(
                        self.sign_witness,
                        self.num_abs_witness.model@,
                    );
                    Self::lemma_abs_positive_from_sign_parts(
                        rhs.sign_witness,
                        rhs.num_abs_witness.model@,
                    );
                }
                Self::lemma_nat_product_positive(self.num_abs_witness.model@, rhs.num_abs_witness.model@);
                assert(out.num_abs_witness.model@ > 0);
                assert(so == out.num_abs_witness.model@ as int);
                assert(so > 0);
                assert(Self::sign_parts_wf_spec(sign_witness, out.num_abs_witness.model@));
            } else {
                assert(sign_witness is Negative);
                assert(
                    (sign_witness is Negative)
                        == ((self.sign_witness is Positive && rhs.sign_witness is Negative)
                            || (self.sign_witness is Negative && rhs.sign_witness is Positive))
                );
                if self.sign_witness is Positive && rhs.sign_witness is Negative {
                    Self::lemma_abs_positive_from_sign_parts(
                        self.sign_witness,
                        self.num_abs_witness.model@,
                    );
                    Self::lemma_abs_positive_from_sign_parts(
                        rhs.sign_witness,
                        rhs.num_abs_witness.model@,
                    );
                } else {
                    assert(self.sign_witness is Negative && rhs.sign_witness is Positive);
                    Self::lemma_abs_positive_from_sign_parts(
                        self.sign_witness,
                        self.num_abs_witness.model@,
                    );
                    Self::lemma_abs_positive_from_sign_parts(
                        rhs.sign_witness,
                        rhs.num_abs_witness.model@,
                    );
                }
                Self::lemma_nat_product_positive(self.num_abs_witness.model@, rhs.num_abs_witness.model@);
                assert(out.num_abs_witness.model@ > 0);
                assert(so == -(out.num_abs_witness.model@ as int));
                assert(so < 0);
                assert(Self::sign_parts_wf_spec(sign_witness, out.num_abs_witness.model@));
            }

            ScalarModel::lemma_mul_denom_product_int(self@, rhs@);
            assert(out@.denom() == self@.denom() * rhs@.denom());
            assert(out@.num == self@.num * rhs@.num);
            assert(s1 * self@.denom() == self@.num * (self.den_witness.model@ as int));
            assert(s2 * rhs@.denom() == rhs@.num * (rhs.den_witness.model@ as int));
            assert(
                (s1 * self@.denom()) * (s2 * rhs@.denom())
                    == (self@.num * (self.den_witness.model@ as int))
                        * (rhs@.num * (rhs.den_witness.model@ as int))
            );
            assert(
                (s1 * self@.denom()) * (s2 * rhs@.denom())
                    == (s1 * s2) * (self@.denom() * rhs@.denom())
            ) by (nonlinear_arith);
            assert(
                (self@.num * (self.den_witness.model@ as int))
                    * (rhs@.num * (rhs.den_witness.model@ as int))
                    == (self@.num * rhs@.num)
                        * ((self.den_witness.model@ as int) * (rhs.den_witness.model@ as int))
            ) by (nonlinear_arith);
            assert(
                (s1 * s2) * (self@.denom() * rhs@.denom())
                    == (self@.num * rhs@.num)
                        * ((self.den_witness.model@ as int) * (rhs.den_witness.model@ as int))
            );
            assert(
                so * out@.denom()
                    == (self@.num * rhs@.num)
                        * ((self.den_witness.model@ as int) * (rhs.den_witness.model@ as int))
            );
            assert(
                (self.den_witness.model@ * rhs.den_witness.model@) as int
                    == (self.den_witness.model@ as int) * (rhs.den_witness.model@ as int)
            ) by (nonlinear_arith);
            assert(out.den_witness.model@ as int
                == (self.den_witness.model@ as int) * (rhs.den_witness.model@ as int));
            assert(
                out@.num * (out.den_witness.model@ as int)
                    == (self@.num * rhs@.num)
                        * ((self.den_witness.model@ as int) * (rhs.den_witness.model@ as int))
            );
            assert(so * out@.denom() == out@.num * (out.den_witness.model@ as int));
            assert(out.witness_wf_spec());
        }
        out
    }

    pub fn sign(&self) -> (out: RuntimeSign)
        ensures
            (out is Positive) == (self@.signum() == 1),
            (out is Negative) == (self@.signum() == -1),
            (out is Zero) == (self@.signum() == 0),
    {
        let s = self.signum_i8();
        if s == 1 {
            RuntimeSign::Positive
        } else if s == -1 {
            RuntimeSign::Negative
        } else {
            RuntimeSign::Zero
        }
    }

    pub fn sign_from_witness(&self) -> (out: RuntimeSign)
        requires
            self.witness_wf_spec(),
        ensures
            (out is Positive) == (self@.signum() == 1),
            (out is Negative) == (self@.signum() == -1),
            (out is Zero) == (self@.signum() == 0),
    {
        proof {
            self.lemma_witness_sign_matches_model();
        }
        self.sign_witness
    }

    pub fn recip(&self) -> (out: Option<Self>)
        ensures
            out.is_none() == self@.eqv_spec(ScalarModel::from_int_spec(0)),
            match out {
                Option::None => true,
                Option::Some(r) => {
                    &&& !self@.eqv_spec(ScalarModel::from_int_spec(0))
                    &&& self@.mul_spec(r@).eqv_spec(ScalarModel::from_int_spec(1))
                    &&& r@.mul_spec(self@).eqv_spec(ScalarModel::from_int_spec(1))
                },
            },
    {
        let sign = self.sign();
        match sign {
            RuntimeSign::Zero => {
                proof {
                    assert((sign is Zero) == (self@.signum() == 0));
                    assert(self@.signum() == 0);
                    ScalarModel::lemma_signum_zero_iff(self@);
                    assert(self@.num == 0);
                    ScalarModel::lemma_eqv_zero_iff_num_zero(self@);
                    assert(self@.eqv_spec(ScalarModel::from_int_spec(0)));
                }
                Option::None
            }
            RuntimeSign::Negative | RuntimeSign::Positive => {
                let ghost one = ScalarModel::from_int_spec(1);
                proof {
                    assert((sign is Zero) == (self@.signum() == 0));
                    assert(!(sign is Zero));
                    assert(self@.signum() != 0);
                    ScalarModel::lemma_signum_zero_iff(self@);
                    assert(self@.num != 0);
                    ScalarModel::lemma_eqv_zero_iff_num_zero(self@);
                    assert(!self@.eqv_spec(ScalarModel::from_int_spec(0)));
                }
                let ghost inv = ScalarModel::reciprocal_constructive(self@);
                let r = RuntimeScalar {
                    sign_witness: self.sign_witness,
                    num_abs_witness: self.den_witness.copy_small_total(),
                    den_witness: self.num_abs_witness.copy_small_total(),
                    model: Ghost(inv),
                };
                proof {
                    assert(inv == r@);
                    assert(self@.mul_spec(inv).eqv_spec(one));
                    assert(inv.mul_spec(self@).eqv_spec(one));
                    assert(self@.mul_spec(r@).eqv_spec(one));
                    assert(r@.mul_spec(self@).eqv_spec(one));
                }
                Option::Some(r)
            }
        }
    }

    pub fn neg(&self) -> (out: Self)
        ensures
            out@ == self@.neg_spec(),
    {
        let out = RuntimeScalar {
            sign_witness: Self::sign_neg_witness(self.sign_witness),
            num_abs_witness: self.num_abs_witness.copy_small_total(),
            den_witness: self.den_witness.copy_small_total(),
            model: Ghost(self@.neg_spec()),
        };
        proof {
            assert(out@ == self@.neg_spec());
        }
        out
    }

    pub fn neg_wf(&self) -> (out: Self)
        requires
            self.witness_wf_spec(),
        ensures
            out@ == self@.neg_spec(),
            out.witness_wf_spec(),
    {
        let sign_witness = Self::sign_neg_witness(self.sign_witness);
        let num_abs_witness = self.num_abs_witness.copy_small_total();
        let den_witness = self.den_witness.copy_small_total();
        let out = RuntimeScalar {
            sign_witness,
            num_abs_witness,
            den_witness,
            model: Ghost(self@.neg_spec()),
        };
        proof {
            assert(out@ == self@.neg_spec());
            assert(out.num_abs_witness.wf_spec());
            assert(out.den_witness.wf_spec());
            assert(out.num_abs_witness.model@ == self.num_abs_witness.model@);
            assert(out.den_witness.model@ == self.den_witness.model@);
            assert(out.den_witness.model@ > 0);
            let ghost s = self.signed_num_witness_spec();
            let ghost os = out.signed_num_witness_spec();
            match self.sign_witness {
                RuntimeSign::Positive => {
                    assert(sign_witness is Negative);
                    assert(s > 0);
                    assert(s == self.num_abs_witness.model@ as int);
                    assert(os == -(out.num_abs_witness.model@ as int));
                    assert(out.num_abs_witness.model@ == self.num_abs_witness.model@);
                    assert(os == -s);
                    Self::lemma_int_pos_negates_to_neg(s);
                    assert(-s < 0);
                    assert(os < 0);
                }
                RuntimeSign::Negative => {
                    assert(sign_witness is Positive);
                    assert(s < 0);
                    assert(s == -(self.num_abs_witness.model@ as int));
                    assert(os == out.num_abs_witness.model@ as int);
                    assert(out.num_abs_witness.model@ == self.num_abs_witness.model@);
                    assert(os == -s);
                    Self::lemma_int_neg_negates_to_pos(s);
                    assert(-s > 0);
                    assert(os > 0);
                }
                RuntimeSign::Zero => {
                    assert(sign_witness is Zero);
                    assert(s == 0);
                    assert(os == 0);
                    assert(os == -s);
                }
            }
            assert(out@.denom() == self@.denom());
            assert(out@.num == -self@.num);
            assert(s * self@.denom() == self@.num * (self.den_witness.model@ as int));
            assert(os * out@.denom() == (-s) * self@.denom());
            assert((-s) * self@.denom() == -(s * self@.denom())) by (nonlinear_arith);
            assert((-self@.num) * (self.den_witness.model@ as int)
                == -(self@.num * (self.den_witness.model@ as int))) by (nonlinear_arith);
            assert((-s) * self@.denom() == (-self@.num) * (self.den_witness.model@ as int));
            assert(out@.num * (out.den_witness.model@ as int)
                == (-self@.num) * (self.den_witness.model@ as int));
            assert(os * out@.denom() == out@.num * (out.den_witness.model@ as int));
            assert(out.witness_wf_spec());
        }
        out
    }

    pub fn normalize(&self) -> (out: Self)
        ensures
            out@.eqv_spec(self@),
            out@.canonical_sign_spec(),
    {
        let ghost m = ScalarModel::normalize_constructive(self@);
        let out = RuntimeScalar {
            sign_witness: self.sign_witness,
            num_abs_witness: self.num_abs_witness.copy_small_total(),
            den_witness: self.den_witness.copy_small_total(),
            model: Ghost(m),
        };
        proof {
            assert(out@ == m);
            assert(out@.eqv_spec(self@));
            assert(out@.canonical_sign_spec());
        }
        out
    }

    /// Proof-only sign extraction from the scalar model.
    ///
    /// This is the migration target for verus-mode callers that currently
    /// depend on the trusted exec `signum_i8` bridge.
    pub proof fn signum_i8_proof(&self) -> (out: i8)
        ensures
            (out == 1) == (self@.signum() == 1),
            (out == -1) == (self@.signum() == -1),
            (out == 0) == (self@.signum() == 0),
    {
        if self@.signum() == 1 {
            1i8
        } else if self@.signum() == -1 {
            -1i8
        } else {
            ScalarModel::lemma_signum_cases(self@);
            assert(self@.signum() == 0);
            0i8
        }
    }

    /// Canonical bridge lemma from the exec signum contract to the proof signum witness.
    pub proof fn lemma_signum_i8_matches_proof(&self, s: i8) -> (sp: i8)
        requires
            (s == 1) == (self@.signum() == 1),
            (s == -1) == (self@.signum() == -1),
            (s == 0) == (self@.signum() == 0),
        ensures
            (sp == 1) == (self@.signum() == 1),
            (sp == -1) == (self@.signum() == -1),
            (sp == 0) == (self@.signum() == 0),
            s == sp,
    {
        let sp = self.signum_i8_proof();
        ScalarModel::lemma_signum_cases(self@);
        if self@.signum() == 1 {
            assert((s == 1) == (self@.signum() == 1));
            assert((sp == 1) == (self@.signum() == 1));
            assert(s == 1);
            assert(sp == 1);
        } else if self@.signum() == -1 {
            assert((s == -1) == (self@.signum() == -1));
            assert((sp == -1) == (self@.signum() == -1));
            assert(s == -1);
            assert(sp == -1);
        } else {
            assert(self@.signum() == 0);
            assert((s == 0) == (self@.signum() == 0));
            assert((sp == 0) == (self@.signum() == 0));
            assert(s == 0);
            assert(sp == 0);
        }
        sp
    }

    #[verifier::external_body]
    pub fn signum_i8(&self) -> (out: i8)
        ensures
            (out == 1) == (self@.signum() == 1),
            (out == -1) == (self@.signum() == -1),
            (out == 0) == (self@.signum() == 0),
    {
        0
    }
}
}

#[cfg(not(verus_keep_ghost))]
impl Hash for RuntimeScalar {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Canonical textual form is stable for equivalent rationals under rug.
        self.value.to_string().hash(state);
    }
}

#[cfg(test)]
mod tests {
    use super::RuntimeScalar;
    use core::hash::{Hash, Hasher};
    use rug::Integer;
    use std::collections::hash_map::DefaultHasher;

    fn hash_value(v: &RuntimeScalar) -> u64 {
        let mut h = DefaultHasher::new();
        v.hash(&mut h);
        h.finish()
    }

    #[test]
    fn equivalent_rationals_compare_equal_and_hash_equal() {
        let a = RuntimeScalar::from_fraction(Integer::from(1), Integer::from(2)).unwrap();
        let b = RuntimeScalar::from_fraction(Integer::from(2), Integer::from(4)).unwrap();
        assert_eq!(a, b);
        assert_eq!(hash_value(&a), hash_value(&b));
    }

    #[test]
    fn arithmetic_ops_work() {
        let a = RuntimeScalar::from_fraction(Integer::from(1), Integer::from(2)).unwrap();
        let b = RuntimeScalar::from_fraction(Integer::from(1), Integer::from(3)).unwrap();
        let sum = a.add(&b);
        let prod = a.mul(&b);

        assert_eq!(sum.value().to_string(), "5/6");
        assert_eq!(prod.value().to_string(), "1/6");
    }
}
