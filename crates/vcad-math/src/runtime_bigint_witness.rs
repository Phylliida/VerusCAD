#[cfg(not(verus_keep_ghost))]
use rug::Integer;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::seq::Seq;

/// Exact runtime big-natural witness scaffold for future scalar de-trusting work.
///
/// Phase 2 intentionally starts with minimal verified constructors and representation
/// predicates. Arithmetic over limb vectors is added in subsequent steps.
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, Eq, PartialEq))]
#[cfg_attr(verus_keep_ghost, derive(Clone))]
pub struct RuntimeBigNatWitness {
    #[cfg(not(verus_keep_ghost))]
    value: Integer,
    #[cfg(verus_keep_ghost)]
    pub limbs_le: Vec<u32>,
    #[cfg(verus_keep_ghost)]
    pub model: Ghost<nat>,
}

#[cfg(not(verus_keep_ghost))]
impl RuntimeBigNatWitness {
    pub fn zero() -> Self {
        Self { value: Integer::from(0) }
    }

    pub fn from_u32(x: u32) -> Self {
        Self { value: Integer::from(x) }
    }

    pub fn from_u64(x: u64) -> Self {
        let lo = x as u32;
        let hi = (x >> 32) as u32;
        Self::from_two_limbs(lo, hi)
    }

    pub fn from_two_limbs(lo: u32, hi: u32) -> Self {
        if hi == 0 {
            return Self::from_u32(lo);
        }
        let mut out = Integer::from(hi);
        out <<= 32;
        out += Integer::from(lo);
        Self { value: out }
    }

    pub fn add(&self, rhs: &Self) -> Self {
        let mut out = self.value.clone();
        out += &rhs.value;
        Self { value: out }
    }

    pub fn add_limbwise_small(&self, rhs: &Self) -> Self {
        self.add(rhs)
    }

    pub fn mul(&self, rhs: &Self) -> Self {
        let mut out = self.value.clone();
        out *= &rhs.value;
        Self { value: out }
    }

    pub fn copy_small_total(&self) -> Self {
        Self { value: self.value.clone() }
    }

    pub fn is_zero(&self) -> bool {
        self.value == 0
    }

    pub fn value(&self) -> &Integer {
        &self.value
    }
}

#[cfg(verus_keep_ghost)]
impl core::fmt::Debug for RuntimeBigNatWitness {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("RuntimeBigNatWitness")
    }
}

#[cfg(verus_keep_ghost)]
impl PartialEq for RuntimeBigNatWitness {
    fn eq(&self, other: &Self) -> bool {
        core::ptr::eq(self, other)
    }
}

#[cfg(verus_keep_ghost)]
impl Eq for RuntimeBigNatWitness {}

#[cfg(verus_keep_ghost)]
verus! {
impl RuntimeBigNatWitness {
    pub open spec fn limb_base_spec() -> nat {
        4_294_967_296
    }

    pub open spec fn pow_base_spec(exp: nat) -> nat
        decreases exp
    {
        if exp == 0 {
            1
        } else {
            Self::limb_base_spec() * Self::pow_base_spec((exp - 1) as nat)
        }
    }

    pub open spec fn limbs_value_spec(limbs: Seq<u32>) -> nat
        decreases limbs.len()
    {
        if limbs.len() == 0 {
            0
        } else if limbs.len() == 1 {
            limbs[0] as nat
        } else {
            limbs[0] as nat + Self::limb_base_spec() * Self::limbs_value_spec(limbs.subrange(1, limbs.len() as int))
        }
    }

    pub open spec fn canonical_limbs_spec(limbs: Seq<u32>) -> bool {
        limbs.len() == 0 || limbs[(limbs.len() - 1) as int] != 0u32
    }

    pub open spec fn wf_spec(&self) -> bool {
        &&& self.model@ == Self::limbs_value_spec(self.limbs_le@)
        &&& Self::canonical_limbs_spec(self.limbs_le@)
    }

    proof fn lemma_pow_base_succ(exp: nat)
        ensures
            Self::pow_base_spec(exp + 1) == Self::limb_base_spec() * Self::pow_base_spec(exp),
    {
    }

    /// Value update law for appending a high limb in little-endian representation.
    proof fn lemma_limbs_value_push(limbs: Seq<u32>, digit: u32)
        ensures
            Self::limbs_value_spec(limbs.push(digit))
                == Self::limbs_value_spec(limbs) + digit as nat * Self::pow_base_spec(limbs.len()),
        decreases limbs.len()
    {
        if limbs.len() == 0 {
            assert(Self::limbs_value_spec(Seq::<u32>::empty()) == 0);
            assert(Self::pow_base_spec(0) == 1);
            assert(limbs.push(digit).len() == 1);
            assert(Self::limbs_value_spec(limbs.push(digit)) == digit as nat);
            assert(
                Self::limbs_value_spec(limbs.push(digit))
                    == Self::limbs_value_spec(limbs) + digit as nat * Self::pow_base_spec(limbs.len())
            );
        } else {
            let tail = limbs.subrange(1, limbs.len() as int);
            Self::lemma_limbs_value_push(tail, digit);
            assert(tail.len() + 1 == limbs.len());
            assert(limbs.push(digit).subrange(1, limbs.push(digit).len() as int) == tail.push(digit));
            assert(Self::limbs_value_spec(limbs.push(digit)) == limbs[0] as nat + Self::limb_base_spec() * Self::limbs_value_spec(tail.push(digit)));
            assert(Self::limbs_value_spec(limbs) == limbs[0] as nat + Self::limb_base_spec() * Self::limbs_value_spec(tail));
            assert(Self::limbs_value_spec(tail.push(digit)) == Self::limbs_value_spec(tail) + digit as nat * Self::pow_base_spec(tail.len()));
            assert(
                Self::limbs_value_spec(limbs.push(digit))
                    == Self::limbs_value_spec(limbs)
                        + Self::limb_base_spec() * (digit as nat * Self::pow_base_spec(tail.len()))
            );
            Self::lemma_pow_base_succ(tail.len() as nat);
            assert(Self::pow_base_spec(limbs.len()) == Self::limb_base_spec() * Self::pow_base_spec(tail.len() as nat));
            assert(
                Self::limb_base_spec() * (digit as nat * Self::pow_base_spec(tail.len()))
                    == digit as nat * (Self::limb_base_spec() * Self::pow_base_spec(tail.len()))
            ) by (nonlinear_arith)
            ;
            assert(
                digit as nat * (Self::limb_base_spec() * Self::pow_base_spec(tail.len()))
                    == digit as nat * Self::pow_base_spec(limbs.len())
            );
            assert(
                Self::limbs_value_spec(limbs.push(digit))
                    == Self::limbs_value_spec(limbs) + digit as nat * Self::pow_base_spec(limbs.len())
            );
        }
    }

    proof fn lemma_model_zero_or_single_limb(&self)
        requires
            self.wf_spec(),
            self.limbs_le@.len() <= 1,
        ensures
            self.limbs_le@.len() == 0 ==> self.model@ == 0,
            self.limbs_le@.len() == 1 ==> self.model@ == self.limbs_le@[0] as nat,
    {
        if self.limbs_le@.len() == 0 {
            assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
            assert(Self::limbs_value_spec(self.limbs_le@) == 0);
        } else {
            assert(self.limbs_le@.len() == 1);
            assert(self.model@ == Self::limbs_value_spec(self.limbs_le@));
            assert(Self::limbs_value_spec(self.limbs_le@) == self.limbs_le@[0] as nat);
        }
    }

    fn from_parts(limbs_le: Vec<u32>, Ghost(model): Ghost<nat>) -> (out: Self)
        requires
            model == Self::limbs_value_spec(limbs_le@),
            Self::canonical_limbs_spec(limbs_le@),
        ensures
            out.model@ == model,
            out.wf_spec(),
    {
        let out = RuntimeBigNatWitness { limbs_le, model: Ghost(model) };
        proof {
            assert(out.model@ == model);
            assert(out.wf_spec());
        }
        out
    }

    pub fn zero() -> (out: Self)
        ensures
            out.model@ == 0,
            out.wf_spec(),
    {
        let limbs_le: Vec<u32> = Vec::new();
        let out = Self::from_parts(limbs_le, Ghost(0));
        proof {
            assert(Self::limbs_value_spec(Seq::<u32>::empty()) == 0);
            assert(Self::canonical_limbs_spec(Seq::<u32>::empty()));
        }
        out
    }

    pub fn from_u32(x: u32) -> (out: Self)
        ensures
            out.model@ == x as nat,
            out.wf_spec(),
    {
        if x == 0 {
            Self::zero()
        } else {
            let mut limbs_le: Vec<u32> = Vec::new();
            limbs_le.push(x);
            proof {
                assert(limbs_le@.len() == 1);
                assert(limbs_le@[0] == x);
                assert(Self::limbs_value_spec(limbs_le@) == x as nat);
                assert(Self::canonical_limbs_spec(limbs_le@));
            }
            Self::from_parts(limbs_le, Ghost(x as nat))
        }
    }

    pub fn from_u64(x: u64) -> (out: Self)
        ensures
            out.wf_spec(),
    {
        let lo = x as u32;
        let hi = (x >> 32) as u32;
        let out = Self::from_two_limbs(lo, hi);
        out
    }

    pub fn from_two_limbs(lo: u32, hi: u32) -> (out: Self)
        ensures
            out.model@ == lo as nat + Self::limb_base_spec() * hi as nat,
            out.wf_spec(),
    {
        if hi == 0 {
            let out = Self::from_u32(lo);
            proof {
                assert(Self::limb_base_spec() * hi as nat == 0);
                assert(out.model@ == lo as nat);
                assert(out.model@ == lo as nat + Self::limb_base_spec() * hi as nat);
            }
            out
        } else {
            let mut limbs_le: Vec<u32> = Vec::new();
            limbs_le.push(lo);
            limbs_le.push(hi);
            proof {
                assert(limbs_le@.len() == 2);
                assert(limbs_le@[0] == lo);
                assert(limbs_le@[1] == hi);
                assert(limbs_le@.subrange(1, limbs_le@.len() as int).len() == 1);
                assert(limbs_le@.subrange(1, limbs_le@.len() as int)[0] == hi);
                assert(Self::limbs_value_spec(limbs_le@.subrange(1, limbs_le@.len() as int)) == hi as nat);
                assert(Self::limbs_value_spec(limbs_le@) == lo as nat + Self::limb_base_spec() * hi as nat);
                assert(Self::canonical_limbs_spec(limbs_le@));
            }
            Self::from_parts(limbs_le, Ghost(lo as nat + Self::limb_base_spec() * hi as nat))
        }
    }

    /// First constructive limb-wise addition milestone:
    /// supports operands represented by at most one limb each.
    pub fn add_limbwise_small(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
            self.limbs_le@.len() <= 1,
            rhs.limbs_le@.len() <= 1,
        ensures
            out.wf_spec(),
            out.model@ == self.model@ + rhs.model@,
    {
        let a0 = if self.limbs_le.len() == 0 { 0u32 } else { self.limbs_le[0] };
        let b0 = if rhs.limbs_le.len() == 0 { 0u32 } else { rhs.limbs_le[0] };

        let sum = a0 as u64 + b0 as u64;
        let base_u64 = 4_294_967_296u64;
        let (lo, hi) = if sum < base_u64 {
            (sum as u32, 0u32)
        } else {
            ((sum - base_u64) as u32, 1u32)
        };

        let out = Self::from_two_limbs(lo, hi);
        proof {
            self.lemma_model_zero_or_single_limb();
            rhs.lemma_model_zero_or_single_limb();

            if self.limbs_le@.len() == 0 {
                assert(a0 == 0u32);
                assert(self.model@ == 0);
                assert(self.model@ == a0 as nat);
            } else {
                assert(self.limbs_le@.len() == 1);
                assert(a0 == self.limbs_le@[0]);
                assert(self.model@ == self.limbs_le@[0] as nat);
                assert(self.model@ == a0 as nat);
            }

            if rhs.limbs_le@.len() == 0 {
                assert(b0 == 0u32);
                assert(rhs.model@ == 0);
                assert(rhs.model@ == b0 as nat);
            } else {
                assert(rhs.limbs_le@.len() == 1);
                assert(b0 == rhs.limbs_le@[0]);
                assert(rhs.model@ == rhs.limbs_le@[0] as nat);
                assert(rhs.model@ == b0 as nat);
            }

            assert(a0 as nat + rhs.model@ == a0 as nat + b0 as nat);
            assert(self.model@ + rhs.model@ == a0 as nat + b0 as nat);

            if sum < base_u64 {
                assert(hi == 0u32);
                assert(lo as u64 == sum);
                assert(lo as nat == sum as nat);
                assert(sum as nat == a0 as nat + b0 as nat);
                assert(out.model@ == lo as nat + Self::limb_base_spec() * hi as nat);
                assert(Self::limb_base_spec() * hi as nat == 0);
                assert(out.model@ == lo as nat);
                assert(out.model@ == sum as nat);
                assert(out.model@ == self.model@ + rhs.model@);
            } else {
                assert(hi == 1u32);
                assert(base_u64 <= sum);
                assert(sum < 2 * base_u64);
                assert((sum - base_u64) < base_u64);
                assert(lo as u64 == sum - base_u64);
                assert(lo as nat == (sum - base_u64) as nat);
                assert(sum as nat == a0 as nat + b0 as nat);
                assert(out.model@ == lo as nat + Self::limb_base_spec() * hi as nat);
                assert(Self::limb_base_spec() * hi as nat == Self::limb_base_spec());
                assert(out.model@ == (sum - base_u64) as nat + Self::limb_base_spec());
                assert(base_u64 as nat == Self::limb_base_spec());
                assert(out.model@ == sum as nat);
                assert(out.model@ == self.model@ + rhs.model@);
            }
        }
        out
    }

    /// Total small-limb add helper used by scalar witness plumbing.
    ///
    /// If both operands are represented in at most one limb, this computes
    /// exact limb-wise addition; otherwise it returns `0` as a conservative
    /// placeholder while preserving witness well-formedness.
    pub fn add_limbwise_small_total(&self, rhs: &Self) -> (out: Self)
        ensures
            out.wf_spec(),
    {
        if self.limbs_le.len() <= 1 && rhs.limbs_le.len() <= 1 {
            let a0 = if self.limbs_le.len() == 0 { 0u32 } else { self.limbs_le[0] };
            let b0 = if rhs.limbs_le.len() == 0 { 0u32 } else { rhs.limbs_le[0] };
            let sum = a0 as u64 + b0 as u64;
            let base_u64 = 4_294_967_296u64;
            let (lo, hi) = if sum < base_u64 {
                (sum as u32, 0u32)
            } else {
                ((sum - base_u64) as u32, 1u32)
            };
            Self::from_two_limbs(lo, hi)
        } else {
            Self::zero()
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn trimmed_len_exec(limbs: &Vec<u32>) -> (out: usize)
        ensures
            out <= limbs.len(),
    {
        let mut n = limbs.len();
        while n > 0 && limbs[n - 1] == 0u32
            invariant
                n <= limbs.len(),
        {
            n = n - 1;
        }
        assert(n <= limbs.len());
        n
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn trim_trailing_zero_limbs(mut limbs: Vec<u32>) -> (out: Vec<u32>)
        ensures
            Self::canonical_limbs_spec(out@),
    {
        while limbs.len() > 0 && limbs[limbs.len() - 1] == 0u32 {
            limbs.pop();
        }
        proof {
            if limbs@.len() == 0 {
                assert(Self::canonical_limbs_spec(limbs@));
            } else {
                assert(limbs.len() > 0);
                assert(!(limbs.len() > 0 && limbs[limbs.len() - 1] == 0u32));
                assert(limbs[limbs.len() - 1] != 0u32);
                assert(limbs@[(limbs@.len() - 1) as int] != 0u32);
                assert(Self::canonical_limbs_spec(limbs@));
            }
        }
        limbs
    }

    /// Total small-limb multiply helper used by scalar witness plumbing.
    ///
    /// If both operands are represented in at most one limb, this computes
    /// exact 32x32->64 multiplication; otherwise it returns `0` as a
    /// conservative placeholder while preserving witness well-formedness.
    pub fn mul_limbwise_small_total(&self, rhs: &Self) -> (out: Self)
        ensures
            out.wf_spec(),
    {
        if self.limbs_le.len() <= 1 && rhs.limbs_le.len() <= 1 {
            let a0 = if self.limbs_le.len() == 0 { 0u32 } else { self.limbs_le[0] };
            let b0 = if rhs.limbs_le.len() == 0 { 0u32 } else { rhs.limbs_le[0] };
            let prod = (a0 as u64).wrapping_mul(b0 as u64);
            #[verifier::truncate]
            let lo = prod as u32;
            #[verifier::truncate]
            let hi = (prod >> 32) as u32;
            Self::from_two_limbs(lo, hi)
        } else {
            Self::zero()
        }
    }

    /// Total small-limb compare helper used by scalar witness plumbing.
    ///
    /// Returns the exact sign of `(self - rhs)` as `-1/0/1` using full
    /// multi-limb comparison with trailing-zero normalization.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn cmp_limbwise_small_total(&self, rhs: &Self) -> (out: i8)
        ensures
            out == -1 || out == 0 || out == 1,
    {
        let alen = Self::trimmed_len_exec(&self.limbs_le);
        let blen = Self::trimmed_len_exec(&rhs.limbs_le);
        if alen > blen {
            1i8
        } else if alen < blen {
            -1i8
        } else {
            assert(alen == blen);
            assert(alen <= self.limbs_le.len());
            assert(blen <= rhs.limbs_le.len());
            let mut i = alen;
            while i > 0
                invariant
                    i <= alen,
                    alen == blen,
                    alen <= self.limbs_le.len(),
                    blen <= rhs.limbs_le.len(),
            {
                let idx = i - 1;
                assert(idx < self.limbs_le.len());
                assert(idx < rhs.limbs_le.len());
                let a = self.limbs_le[idx];
                let b = rhs.limbs_le[idx];
                if a > b {
                    return 1i8;
                } else if a < b {
                    return -1i8;
                }
                i = i - 1;
            }
            0i8
        }
    }

    /// Total small-limb subtraction helper used by scalar witness plumbing.
    ///
    /// Computes the exact nonnegative difference when `self >= rhs` using full
    /// multi-limb borrow propagation (with trailing-zero normalization).
    /// Returns `0` when `self < rhs`.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn sub_limbwise_small_total(&self, rhs: &Self) -> (out: Self)
        ensures
            out.wf_spec(),
    {
        if self.cmp_limbwise_small_total(rhs) == -1i8 {
            Self::zero()
        } else {
            let alen = Self::trimmed_len_exec(&self.limbs_le);
            let blen = Self::trimmed_len_exec(&rhs.limbs_le);
            assert(alen <= self.limbs_le.len());
            assert(blen <= rhs.limbs_le.len());
            let mut out_limbs: Vec<u32> = Vec::new();
            let mut i: usize = 0;
            let mut borrow: u64 = 0u64;

            while i < alen
                invariant
                    i <= alen,
                    alen <= self.limbs_le.len(),
                    blen <= rhs.limbs_le.len(),
            {
                assert(i < self.limbs_le.len());
                let a = self.limbs_le[i] as u64;
                let b = if i < blen {
                    assert(i < rhs.limbs_le.len());
                    rhs.limbs_le[i] as u64
                } else {
                    0u64
                };
                let need = b.wrapping_add(borrow);
                let digit64 = if a >= need {
                    borrow = 0u64;
                    a - need
                } else {
                    borrow = 1u64;
                    (4_294_967_296u64).wrapping_add(a).wrapping_sub(need)
                };
                #[verifier::truncate]
                let digit = digit64 as u32;
                out_limbs.push(digit);
                i = i + 1;
            }

            let out_limbs = Self::trim_trailing_zero_limbs(out_limbs);
            let ghost model = Self::limbs_value_spec(out_limbs@);
            Self::from_parts(out_limbs, Ghost(model))
        }
    }

    /// Total witness copy helper for scalar witness plumbing.
    ///
    /// Preserves all limbs exactly (after trailing-zero normalization).
    #[verifier::exec_allows_no_decreases_clause]
    pub fn copy_small_total(&self) -> (out: Self)
        ensures
            out.wf_spec(),
    {
        let n = Self::trimmed_len_exec(&self.limbs_le);
        assert(n <= self.limbs_le.len());
        let mut out_limbs: Vec<u32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n <= self.limbs_le.len(),
        {
            assert(i < self.limbs_le.len());
            out_limbs.push(self.limbs_le[i]);
            i = i + 1;
        }
        let out_limbs = Self::trim_trailing_zero_limbs(out_limbs);
        let ghost model = Self::limbs_value_spec(out_limbs@);
        Self::from_parts(out_limbs, Ghost(model))
    }
}
}

#[cfg(test)]
mod tests {
    use super::RuntimeBigNatWitness;

    #[test]
    fn basic_runtime_big_nat_ops() {
        let a = RuntimeBigNatWitness::from_u32(7);
        let b = RuntimeBigNatWitness::from_u32(9);
        let sum = a.add(&b);
        let prod = a.mul(&b);
        let small_sum = a.add_limbwise_small(&b);
        let two_limbs = RuntimeBigNatWitness::from_two_limbs(5, 3);
        assert_eq!(sum.value().to_string(), "16");
        assert_eq!(small_sum.value().to_string(), "16");
        assert_eq!(prod.value().to_string(), "63");
        assert_eq!(two_limbs.value().to_string(), "12884901893");
        assert!(!sum.is_zero());
        assert!(RuntimeBigNatWitness::zero().is_zero());
    }
}
