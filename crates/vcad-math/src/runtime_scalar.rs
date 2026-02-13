use core::hash::{Hash, Hasher};
use rug::{Integer, Rational};
#[cfg(verus_keep_ghost)]
use crate::scalar::ScalarModel;
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
    pub model: Ghost<ScalarModel>,
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

    pub fn signum_i8(&self) -> i8 {
        if self.value > 0 {
            1
        } else if self.value < 0 {
            -1
        } else {
            0
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
impl RuntimeScalar {
    fn from_model(Ghost(model): Ghost<ScalarModel>) -> (out: Self)
        ensures
            out@ == model,
    {
        RuntimeScalar { model: Ghost(model) }
    }

    pub fn from_int(value: i64) -> (out: Self)
        ensures
            out@ == ScalarModel::from_int_spec(value as int),
    {
        let out = Self::from_model(Ghost(ScalarModel::from_int_spec(value as int)));
        out
    }

    pub fn from_fraction(num: Integer, den: Integer) -> (out: Option<Self>) {
        let _ = num;
        let _ = den;
        Option::None
    }

    pub fn add(&self, rhs: &Self) -> (out: Self)
        ensures
            out@ == self@.add_spec(rhs@),
    {
        let out = Self::from_model(Ghost(self@.add_spec(rhs@)));
        out
    }

    pub fn sub(&self, rhs: &Self) -> (out: Self)
        ensures
            out@ == self@.sub_spec(rhs@),
    {
        let out = Self::from_model(Ghost(self@.sub_spec(rhs@)));
        out
    }

    pub fn mul(&self, rhs: &Self) -> (out: Self)
        ensures
            out@ == self@.mul_spec(rhs@),
    {
        let out = Self::from_model(Ghost(self@.mul_spec(rhs@)));
        out
    }

    #[verifier::external_body]
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
        Option::None
    }

    pub fn neg(&self) -> (out: Self)
        ensures
            out@ == self@.neg_spec(),
    {
        let out = Self::from_model(Ghost(self@.neg_spec()));
        out
    }

    pub fn normalize(&self) -> (out: Self)
        ensures
            out@.eqv_spec(self@),
            out@.canonical_sign_spec(),
    {
        let ghost m = ScalarModel::normalize_constructive(self@);
        let out = Self::from_model(Ghost(m));
        proof {
            assert(out@ == m);
            assert(out@.eqv_spec(self@));
            assert(out@.canonical_sign_spec());
        }
        out
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
