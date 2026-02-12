use core::hash::{Hash, Hasher};
use rug::{Integer, Rational};

/// Runtime rational scalar backed by `rug::Rational`.
///
/// This type is for executable paths. The proof model remains in `ScalarModel`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeScalar {
    value: Rational,
}

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

    pub fn neg(&self) -> Self {
        Self { value: -self.value.clone() }
    }
}

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
