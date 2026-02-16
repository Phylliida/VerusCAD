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

    proof fn lemma_limbs_value_drop_last_zero(limbs: Seq<u32>)
        requires
            limbs.len() > 0,
            limbs[(limbs.len() - 1) as int] == 0u32,
        ensures
            Self::limbs_value_spec(limbs)
                == Self::limbs_value_spec(limbs.subrange(0, limbs.len() as int - 1)),
    {
        let prefix = limbs.subrange(0, limbs.len() as int - 1);
        assert(prefix.len() + 1 == limbs.len());
        assert(prefix.push(0u32).len() == limbs.len());
        assert forall|i: int| 0 <= i < limbs.len() implies #[trigger] prefix.push(0u32)[i] == limbs[i] by {
            if i < prefix.len() {
                assert(prefix.push(0u32)[i] == prefix[i]);
                assert(prefix[i] == limbs[i]);
            } else {
                assert(i == prefix.len());
                assert(i == limbs.len() - 1);
                assert(prefix.push(0u32)[i] == 0u32);
                assert(limbs[(limbs.len() - 1) as int] == 0u32);
                assert(limbs[i] == 0u32);
            }
        };
        assert(prefix.push(0u32) == limbs);
        Self::lemma_limbs_value_push(prefix, 0u32);
        assert(Self::pow_base_spec(prefix.len()) >= 0);
        assert(0u32 as nat * Self::pow_base_spec(prefix.len()) == 0);
        assert(
            Self::limbs_value_spec(prefix.push(0u32))
                == Self::limbs_value_spec(prefix) + 0
        );
        assert(
            Self::limbs_value_spec(prefix.push(0u32))
                == Self::limbs_value_spec(prefix)
        );
        assert(
            Self::limbs_value_spec(limbs)
                == Self::limbs_value_spec(limbs.subrange(0, limbs.len() as int - 1))
        );
    }

    proof fn lemma_limbs_value_trim_suffix_zeros(limbs: Seq<u32>, n: nat)
        requires
            n <= limbs.len(),
            forall|i: int| n <= i < limbs.len() ==> limbs[i] == 0u32,
        ensures
            Self::limbs_value_spec(limbs)
                == Self::limbs_value_spec(limbs.subrange(0, n as int)),
        decreases limbs.len() - n
    {
        if limbs.len() == n {
            assert(limbs.subrange(0, n as int) == limbs);
        } else {
            assert(limbs.len() > 0);
            assert(n < limbs.len());
            let last = limbs.len() - 1;
            assert(n <= last);
            assert(limbs[last as int] == 0u32);
            let prefix = limbs.subrange(0, limbs.len() as int - 1);
            Self::lemma_limbs_value_drop_last_zero(limbs);
            assert(
                Self::limbs_value_spec(limbs)
                    == Self::limbs_value_spec(prefix)
            );
            assert forall|i: int| n <= i < prefix.len() implies prefix[i] == 0u32 by {
                assert(i < prefix.len());
                assert(prefix.len() == limbs.len() - 1);
                assert(i < limbs.len());
                assert(limbs[i] == 0u32);
                assert(prefix[i] == limbs[i]);
            };
            Self::lemma_limbs_value_trim_suffix_zeros(prefix, n);
            assert(prefix.subrange(0, n as int) == limbs.subrange(0, n as int));
            assert(
                Self::limbs_value_spec(prefix)
                    == Self::limbs_value_spec(prefix.subrange(0, n as int))
            );
            assert(
                Self::limbs_value_spec(prefix.subrange(0, n as int))
                    == Self::limbs_value_spec(limbs.subrange(0, n as int))
            );
            assert(
                Self::limbs_value_spec(limbs)
                    == Self::limbs_value_spec(limbs.subrange(0, n as int))
            );
        }
    }

    pub open spec fn limb_or_zero_spec(limbs: Seq<u32>, logical_len: nat, idx: nat) -> nat {
        if idx < logical_len && idx < limbs.len() {
            limbs[idx as int] as nat
        } else {
            0
        }
    }

    pub open spec fn prefix_sum_spec(limbs: Seq<u32>, logical_len: nat, count: nat) -> nat
        decreases count
    {
        if count == 0 {
            0
        } else {
            let prev = (count - 1) as nat;
            Self::prefix_sum_spec(limbs, logical_len, prev)
                + Self::limb_or_zero_spec(limbs, logical_len, prev) * Self::pow_base_spec(prev)
        }
    }

    pub open spec fn add_sum_spec(a: nat, b: nat, carry_in: nat) -> nat {
        a + b + carry_in
    }

    pub open spec fn add_digit_spec(a: nat, b: nat, carry_in: nat) -> nat {
        if Self::add_sum_spec(a, b, carry_in) >= Self::limb_base_spec() {
            (Self::add_sum_spec(a, b, carry_in) - Self::limb_base_spec()) as nat
        } else {
            Self::add_sum_spec(a, b, carry_in)
        }
    }

    pub open spec fn add_carry_spec(a: nat, b: nat, carry_in: nat) -> nat {
        if Self::add_sum_spec(a, b, carry_in) >= Self::limb_base_spec() {
            1
        } else {
            0
        }
    }

    proof fn lemma_add_digit_carry_decompose(a: nat, b: nat, carry_in: nat)
        requires
            a < Self::limb_base_spec(),
            b < Self::limb_base_spec(),
            carry_in <= 1,
        ensures
            Self::add_carry_spec(a, b, carry_in) <= 1,
            Self::add_digit_spec(a, b, carry_in)
                + Self::add_carry_spec(a, b, carry_in) * Self::limb_base_spec()
                == Self::add_sum_spec(a, b, carry_in),
    {
        let sum = Self::add_sum_spec(a, b, carry_in);
        let base = Self::limb_base_spec();
        if sum >= base {
            assert(Self::add_digit_spec(a, b, carry_in) == (sum - base) as nat);
            assert(Self::add_carry_spec(a, b, carry_in) == 1);
            assert(Self::add_carry_spec(a, b, carry_in) <= 1);
            assert((sum - base) as nat + base == sum);
            assert(
                Self::add_digit_spec(a, b, carry_in)
                    + Self::add_carry_spec(a, b, carry_in) * base
                    == sum
            );
        } else {
            assert(Self::add_digit_spec(a, b, carry_in) == sum);
            assert(Self::add_carry_spec(a, b, carry_in) == 0);
            assert(Self::add_carry_spec(a, b, carry_in) <= 1);
            assert(
                Self::add_digit_spec(a, b, carry_in)
                    + Self::add_carry_spec(a, b, carry_in) * base
                    == sum
            );
        }
        assert(sum == Self::add_sum_spec(a, b, carry_in));
    }

    proof fn lemma_add_prefix_step(
        psr: nat,
        psa: nat,
        psb: nat,
        digit: nat,
        a: nat,
        b: nat,
        carry_in: nat,
        carry_out: nat,
        pow_i: nat,
        pow_next: nat,
    )
        requires
            psr + carry_in * pow_i == psa + psb,
            digit + carry_out * Self::limb_base_spec() == a + b + carry_in,
            pow_next == Self::limb_base_spec() * pow_i,
        ensures
            psr + digit * pow_i + carry_out * pow_next
                == psa + psb + a * pow_i + b * pow_i,
    {
        assert(carry_out * pow_next == carry_out * (Self::limb_base_spec() * pow_i));
        assert(carry_out * (Self::limb_base_spec() * pow_i) == carry_out * Self::limb_base_spec() * pow_i)
            by (nonlinear_arith);
        assert(
            digit * pow_i + carry_out * pow_next
                == digit * pow_i + carry_out * Self::limb_base_spec() * pow_i
        );
        assert(
            digit * pow_i + carry_out * Self::limb_base_spec() * pow_i
                == (digit + carry_out * Self::limb_base_spec()) * pow_i
        ) by (nonlinear_arith);
        assert((digit + carry_out * Self::limb_base_spec()) * pow_i == (a + b + carry_in) * pow_i);
        assert((a + b + carry_in) * pow_i == a * pow_i + b * pow_i + carry_in * pow_i)
            by (nonlinear_arith);
        assert(
            psr + digit * pow_i + carry_out * pow_next
                == psr + a * pow_i + b * pow_i + carry_in * pow_i
        );
        assert(
            psr + a * pow_i + b * pow_i + carry_in * pow_i
                == (psr + carry_in * pow_i) + a * pow_i + b * pow_i
        ) by (nonlinear_arith);
        assert((psr + carry_in * pow_i) + a * pow_i + b * pow_i == (psa + psb) + a * pow_i + b * pow_i);
        assert((psa + psb) + a * pow_i + b * pow_i == psa + psb + a * pow_i + b * pow_i)
            by (nonlinear_arith);
    }

    proof fn lemma_sub_prefix_step(
        psr: nat,
        psa: nat,
        psb: nat,
        digit: nat,
        a: nat,
        b: nat,
        borrow_in: nat,
        borrow_out: nat,
        pow_i: nat,
        pow_next: nat,
    )
        requires
            psr + psb == psa + borrow_in * pow_i,
            digit + b + borrow_in == a + borrow_out * Self::limb_base_spec(),
            pow_next == Self::limb_base_spec() * pow_i,
        ensures
            (psr + digit * pow_i) + (psb + b * pow_i)
                == (psa + a * pow_i) + borrow_out * pow_next,
    {
        assert((digit + b + borrow_in) * pow_i == (a + borrow_out * Self::limb_base_spec()) * pow_i);
        assert((digit + b + borrow_in) * pow_i == digit * pow_i + b * pow_i + borrow_in * pow_i)
            by (nonlinear_arith);
        assert((a + borrow_out * Self::limb_base_spec()) * pow_i == a * pow_i + borrow_out * Self::limb_base_spec() * pow_i)
            by (nonlinear_arith);
        assert(borrow_out * pow_next == borrow_out * (Self::limb_base_spec() * pow_i));
        assert(borrow_out * (Self::limb_base_spec() * pow_i) == borrow_out * Self::limb_base_spec() * pow_i)
            by (nonlinear_arith);
        assert(
            digit * pow_i + b * pow_i + borrow_in * pow_i
                == a * pow_i + borrow_out * pow_next
        );
        assert(
            (psr + digit * pow_i) + (psb + b * pow_i)
                == psr + psb + digit * pow_i + b * pow_i
        ) by (nonlinear_arith);
        assert(
            psr + psb + digit * pow_i + b * pow_i
                == psa + borrow_in * pow_i + digit * pow_i + b * pow_i
        );
        assert(
            psa + borrow_in * pow_i + digit * pow_i + b * pow_i
                == psa + (a * pow_i + borrow_out * pow_next)
        );
        assert(
            psa + (a * pow_i + borrow_out * pow_next)
                == (psa + a * pow_i) + borrow_out * pow_next
        ) by (nonlinear_arith);
        assert(
            (psr + digit * pow_i) + (psb + b * pow_i)
                == (psa + a * pow_i) + borrow_out * pow_next
        );
    }

    proof fn lemma_limb_or_zero_past_logical_len(limbs: Seq<u32>, logical_len: nat, idx: nat)
        requires
            logical_len <= idx,
        ensures
            Self::limb_or_zero_spec(limbs, logical_len, idx) == 0,
    {
        assert(!(idx < logical_len));
        assert(Self::limb_or_zero_spec(limbs, logical_len, idx) == 0);
    }

    proof fn lemma_prefix_sum_step(limbs: Seq<u32>, logical_len: nat, count: nat)
        ensures
            Self::prefix_sum_spec(limbs, logical_len, count + 1)
                == Self::prefix_sum_spec(limbs, logical_len, count)
                    + Self::limb_or_zero_spec(limbs, logical_len, count) * Self::pow_base_spec(count),
    {
        assert(
            Self::prefix_sum_spec(limbs, logical_len, count + 1)
                == Self::prefix_sum_spec(limbs, logical_len, count)
                    + Self::limb_or_zero_spec(limbs, logical_len, count) * Self::pow_base_spec(count)
        );
    }

    proof fn lemma_prefix_sum_constant_from_extra(limbs: Seq<u32>, logical_len: nat, extra: nat)
        ensures
            Self::prefix_sum_spec(limbs, logical_len, logical_len + extra)
                == Self::prefix_sum_spec(limbs, logical_len, logical_len),
        decreases extra
    {
        if extra == 0 {
            assert(logical_len + extra == logical_len);
        } else {
            let prev = (extra - 1) as nat;
            Self::lemma_prefix_sum_constant_from_extra(limbs, logical_len, prev);
            assert(extra == prev + 1);
            assert((logical_len + prev) + 1 == logical_len + extra);
            Self::lemma_prefix_sum_step(limbs, logical_len, logical_len + prev);
            Self::lemma_limb_or_zero_past_logical_len(limbs, logical_len, logical_len + prev);
            assert(
                Self::prefix_sum_spec(limbs, logical_len, logical_len + extra)
                    == Self::prefix_sum_spec(limbs, logical_len, logical_len + prev)
                        + Self::limb_or_zero_spec(limbs, logical_len, logical_len + prev)
                            * Self::pow_base_spec(logical_len + prev)
            );
            assert(
                Self::prefix_sum_spec(limbs, logical_len, logical_len + extra)
                    == Self::prefix_sum_spec(limbs, logical_len, logical_len + prev)
            );
            assert(
                Self::prefix_sum_spec(limbs, logical_len, logical_len + prev)
                    == Self::prefix_sum_spec(limbs, logical_len, logical_len)
            );
        }
    }

    proof fn lemma_prefix_sum_constant_past_logical_len(limbs: Seq<u32>, logical_len: nat, count: nat)
        requires
            logical_len <= count,
        ensures
            Self::prefix_sum_spec(limbs, logical_len, count)
                == Self::prefix_sum_spec(limbs, logical_len, logical_len),
    {
        let extra = (count - logical_len) as nat;
        assert(logical_len + extra == count);
        Self::lemma_prefix_sum_constant_from_extra(limbs, logical_len, extra);
        assert(
            Self::prefix_sum_spec(limbs, logical_len, count)
                == Self::prefix_sum_spec(limbs, logical_len, logical_len + extra)
        );
    }

    proof fn lemma_prefix_sum_matches_subrange(limbs: Seq<u32>, logical_len: nat, count: nat)
        requires
            count <= logical_len,
            count <= limbs.len(),
        ensures
            Self::prefix_sum_spec(limbs, logical_len, count)
                == Self::limbs_value_spec(limbs.subrange(0, count as int)),
        decreases count
    {
        if count == 0 {
            assert(limbs.subrange(0, 0) == Seq::<u32>::empty());
            assert(Self::prefix_sum_spec(limbs, logical_len, count) == 0);
            assert(Self::limbs_value_spec(limbs.subrange(0, count as int)) == 0);
        } else {
            let prev = (count - 1) as nat;
            Self::lemma_prefix_sum_matches_subrange(limbs, logical_len, prev);

            assert(prev < count);
            assert(prev < logical_len);
            assert(prev < limbs.len());
            assert(Self::limb_or_zero_spec(limbs, logical_len, prev) == limbs[prev as int] as nat);
            assert(
                Self::prefix_sum_spec(limbs, logical_len, count)
                    == Self::prefix_sum_spec(limbs, logical_len, prev)
                        + Self::limb_or_zero_spec(limbs, logical_len, prev) * Self::pow_base_spec(prev)
            );
            assert(
                Self::prefix_sum_spec(limbs, logical_len, count)
                    == Self::limbs_value_spec(limbs.subrange(0, prev as int))
                        + limbs[prev as int] as nat * Self::pow_base_spec(prev)
            );

            let prefix = limbs.subrange(0, prev as int);
            assert(prefix.push(limbs[prev as int]).len() == count);
            assert forall|i: int| 0 <= i < count implies #[trigger] prefix.push(limbs[prev as int])[i] == limbs.subrange(0, count as int)[i] by {
                if i < prev {
                    assert(prefix.push(limbs[prev as int])[i] == prefix[i]);
                    assert(prefix[i] == limbs[i]);
                    assert(limbs.subrange(0, count as int)[i] == limbs[i]);
                } else {
                    assert(i == prev);
                    assert(prefix.push(limbs[prev as int])[i] == limbs[prev as int]);
                    assert(limbs.subrange(0, count as int)[i] == limbs[prev as int]);
                }
            };
            assert(prefix.push(limbs[prev as int]) == limbs.subrange(0, count as int));
            Self::lemma_limbs_value_push(prefix, limbs[prev as int]);
            assert(
                Self::limbs_value_spec(limbs.subrange(0, count as int))
                    == Self::limbs_value_spec(prefix)
                        + limbs[prev as int] as nat * Self::pow_base_spec(prev)
            );
            assert(
                Self::prefix_sum_spec(limbs, logical_len, count)
                    == Self::limbs_value_spec(limbs.subrange(0, count as int))
            );
        }
    }

    proof fn lemma_prefix_sum_eq_subrange_value(limbs: Seq<u32>, logical_len: nat)
        requires
            logical_len <= limbs.len(),
        ensures
            Self::prefix_sum_spec(limbs, logical_len, logical_len)
                == Self::limbs_value_spec(limbs.subrange(0, logical_len as int)),
    {
        Self::lemma_prefix_sum_matches_subrange(limbs, logical_len, logical_len);
    }

    proof fn lemma_pow_ge_one(exp: nat)
        ensures
            Self::pow_base_spec(exp) >= 1,
        decreases exp
    {
        if exp == 0 {
            assert(Self::pow_base_spec(exp) == 1);
        } else {
            let prev = (exp - 1) as nat;
            Self::lemma_pow_ge_one(prev);
            Self::lemma_pow_base_succ(prev);
            assert(Self::limb_base_spec() == 4_294_967_296);
            assert(Self::limb_base_spec() >= 1);
            assert(Self::pow_base_spec(prev) >= 1);
            assert(Self::pow_base_spec(exp) == Self::limb_base_spec() * Self::pow_base_spec(prev));
            assert(Self::pow_base_spec(prev) <= Self::limb_base_spec() * Self::pow_base_spec(prev))
                by (nonlinear_arith);
            assert(Self::pow_base_spec(prev) <= Self::pow_base_spec(exp));
            assert(Self::pow_base_spec(exp) >= 1);
        }
    }

    proof fn lemma_pow_monotonic(lo: nat, hi: nat)
        requires
            lo <= hi,
        ensures
            Self::pow_base_spec(lo) <= Self::pow_base_spec(hi),
        decreases hi - lo
    {
        if lo == hi {
            assert(Self::pow_base_spec(lo) <= Self::pow_base_spec(hi));
        } else {
            assert(lo < hi);
            let prev = (hi - 1) as nat;
            assert(lo <= prev);
            Self::lemma_pow_monotonic(lo, prev);
            Self::lemma_pow_ge_one(prev);
            Self::lemma_pow_base_succ(prev);
            assert(Self::limb_base_spec() == 4_294_967_296);
            assert(Self::limb_base_spec() >= 1);
            assert(Self::pow_base_spec(prev) <= Self::limb_base_spec() * Self::pow_base_spec(prev))
                by (nonlinear_arith);
            assert(Self::pow_base_spec(hi) == Self::limb_base_spec() * Self::pow_base_spec(prev));
            assert(Self::pow_base_spec(prev) <= Self::pow_base_spec(hi));
            assert(Self::pow_base_spec(lo) <= Self::pow_base_spec(hi));
        }
    }

    proof fn lemma_limbs_value_unfold_nonempty(limbs: Seq<u32>)
        requires
            limbs.len() > 0,
        ensures
            Self::limbs_value_spec(limbs)
                == limbs[0] as nat
                    + Self::limb_base_spec() * Self::limbs_value_spec(limbs.subrange(1, limbs.len() as int)),
    {
        if limbs.len() == 1 {
            assert(Self::limbs_value_spec(limbs) == limbs[0] as nat);
            assert(limbs.subrange(1, limbs.len() as int) == Seq::<u32>::empty());
            assert(Self::limbs_value_spec(Seq::<u32>::empty()) == 0);
            assert(
                limbs[0] as nat
                    + Self::limb_base_spec() * Self::limbs_value_spec(limbs.subrange(1, limbs.len() as int))
                    == limbs[0] as nat
            );
        } else {
            assert(
                Self::limbs_value_spec(limbs)
                    == limbs[0] as nat
                        + Self::limb_base_spec()
                            * Self::limbs_value_spec(limbs.subrange(1, limbs.len() as int))
            );
        }
    }

    proof fn lemma_limbs_value_append(left: Seq<u32>, right: Seq<u32>)
        ensures
            Self::limbs_value_spec(left + right)
                == Self::limbs_value_spec(left)
                    + Self::pow_base_spec(left.len()) * Self::limbs_value_spec(right),
        decreases left.len()
    {
        if left.len() == 0 {
            assert(left + right == right);
            assert(Self::limbs_value_spec(left) == 0);
            assert(Self::pow_base_spec(left.len()) == 1);
            assert(
                Self::limbs_value_spec(left + right)
                    == Self::limbs_value_spec(left)
                        + Self::pow_base_spec(left.len()) * Self::limbs_value_spec(right)
            );
        } else {
            let tail = left.subrange(1, left.len() as int);
            let whole = left + right;
            let pow_tail = Self::pow_base_spec(tail.len());
            let right_val = Self::limbs_value_spec(right);
            Self::lemma_limbs_value_append(tail, right);
            Self::lemma_limbs_value_unfold_nonempty(left);
            Self::lemma_limbs_value_unfold_nonempty(whole);
            assert(whole.subrange(1, whole.len() as int) == tail + right);
            assert(
                Self::limbs_value_spec(whole)
                    == left[0] as nat
                        + Self::limb_base_spec() * Self::limbs_value_spec(tail + right)
            );
            assert(
                Self::limbs_value_spec(tail + right)
                    == Self::limbs_value_spec(tail)
                        + pow_tail * right_val
            );
            let right_shifted = pow_tail * right_val;
            assert(
                Self::limbs_value_spec(whole)
                    == left[0] as nat
                        + Self::limb_base_spec()
                            * (Self::limbs_value_spec(tail) + right_shifted)
            );
            assert(
                Self::limb_base_spec() * (Self::limbs_value_spec(tail) + right_shifted)
                    == Self::limb_base_spec() * Self::limbs_value_spec(tail)
                        + Self::limb_base_spec() * right_shifted
            ) by (nonlinear_arith);
            assert(
                Self::limb_base_spec() * right_shifted
                    == (Self::limb_base_spec() * pow_tail) * right_val
            ) by {
                assert(
                    Self::limb_base_spec() * right_shifted
                        == Self::limb_base_spec() * (pow_tail * right_val)
                );
                assert(
                    Self::limb_base_spec() * (pow_tail * right_val)
                        == (Self::limb_base_spec() * pow_tail) * right_val
                ) by (nonlinear_arith);
            };
            assert(
                Self::limbs_value_spec(whole)
                    == (left[0] as nat + Self::limb_base_spec() * Self::limbs_value_spec(tail))
                        + (Self::limb_base_spec() * pow_tail) * right_val
            );
            Self::lemma_pow_base_succ(tail.len() as nat);
            assert(Self::pow_base_spec(left.len()) == Self::limb_base_spec() * pow_tail);
            assert(Self::limbs_value_spec(left) == left[0] as nat + Self::limb_base_spec() * Self::limbs_value_spec(tail));
            assert(
                Self::limbs_value_spec(whole)
                    == Self::limbs_value_spec(left)
                        + Self::pow_base_spec(left.len()) * Self::limbs_value_spec(right)
            );
        }
    }

    proof fn lemma_limbs_value_lt_pow_len(limbs: Seq<u32>)
        ensures
            Self::limbs_value_spec(limbs) < Self::pow_base_spec(limbs.len()),
        decreases limbs.len()
    {
        if limbs.len() == 0 {
            assert(Self::limbs_value_spec(limbs) == 0);
            assert(Self::pow_base_spec(0) == 1);
        } else {
            let n = (limbs.len() - 1) as nat;
            let prefix = limbs.subrange(0, n as int);
            let last = limbs[n as int];
            let last_nat = last as nat;
            let pow_n = Self::pow_base_spec(n);
            Self::lemma_limbs_value_lt_pow_len(prefix);
            Self::lemma_limbs_value_push(prefix, last);
            assert(prefix.push(last).len() == limbs.len());
            assert forall|i: int| 0 <= i < limbs.len() implies #[trigger] prefix.push(last)[i] == limbs[i] by {
                if i < prefix.len() {
                    assert(prefix.push(last)[i] == prefix[i]);
                    assert(prefix[i] == limbs[i]);
                } else {
                    assert(i == prefix.len());
                    assert(i == n as int);
                    assert(prefix.push(last)[i] == last);
                    assert(last == limbs[i]);
                }
            };
            assert(prefix.push(last) == limbs);
            assert(Self::limbs_value_spec(limbs) == Self::limbs_value_spec(prefix) + last_nat * pow_n);
            assert(Self::limb_base_spec() == 4_294_967_296);
            assert(last_nat <= 4_294_967_295);
            assert(last_nat + 1 <= Self::limb_base_spec());
            assert(Self::limbs_value_spec(prefix) < pow_n);
            let shifted = last_nat * pow_n;
            assert(
                Self::limbs_value_spec(prefix) + shifted
                    < pow_n + shifted
            );
            assert(
                pow_n + shifted
                    == shifted + pow_n
            ) by (nonlinear_arith);
            assert(
                (last_nat + 1) * pow_n
                    == last_nat * pow_n + 1 * pow_n
            ) by (nonlinear_arith);
            assert(1 * pow_n == pow_n);
            assert(last_nat * pow_n == shifted);
            assert(
                (last_nat + 1) * pow_n
                    == shifted + pow_n
            );
            assert(
                pow_n + shifted
                    == (last_nat + 1) * pow_n
            );
            Self::lemma_pow_ge_one(n);
            let headroom = Self::limb_base_spec() - (last_nat + 1);
            assert(0 <= headroom);
            assert(Self::limb_base_spec() == (last_nat + 1) + headroom);
            assert(
                Self::limb_base_spec() * pow_n
                    == ((last_nat + 1) + headroom) * pow_n
            );
            assert(
                ((last_nat + 1) + headroom) * pow_n
                    == (last_nat + 1) * pow_n + headroom * pow_n
            ) by (nonlinear_arith);
            assert(0 <= headroom * pow_n);
            assert(
                (last_nat + 1) * pow_n
                    <= Self::limb_base_spec() * pow_n
            );
            Self::lemma_pow_base_succ(n);
            assert(Self::pow_base_spec(limbs.len()) == Self::limb_base_spec() * pow_n);
            assert(Self::limbs_value_spec(limbs) < Self::pow_base_spec(limbs.len()));
        }
    }

    proof fn lemma_limbs_value_ge_pow_last_nonzero(limbs: Seq<u32>)
        requires
            limbs.len() > 0,
            limbs[(limbs.len() - 1) as int] != 0u32,
        ensures
            Self::pow_base_spec((limbs.len() - 1) as nat) <= Self::limbs_value_spec(limbs),
    {
        let n = (limbs.len() - 1) as nat;
        let prefix = limbs.subrange(0, n as int);
        let last = limbs[n as int];
        Self::lemma_limbs_value_push(prefix, last);
        assert(prefix.push(last).len() == limbs.len());
        assert forall|i: int| 0 <= i < limbs.len() implies #[trigger] prefix.push(last)[i] == limbs[i] by {
            if i < prefix.len() {
                assert(prefix.push(last)[i] == prefix[i]);
                assert(prefix[i] == limbs[i]);
            } else {
                assert(i == prefix.len());
                assert(i == n as int);
                assert(prefix.push(last)[i] == last);
                assert(last == limbs[i]);
            }
        };
        assert(prefix.push(last) == limbs);
        assert(Self::limbs_value_spec(limbs) == Self::limbs_value_spec(prefix) + last as nat * Self::pow_base_spec(n));
        assert(last != 0u32);
        assert(1 <= last as nat);
        Self::lemma_pow_ge_one(n);
        assert(
            last as nat * Self::pow_base_spec(n)
                == Self::pow_base_spec(n) + (last as nat - 1) * Self::pow_base_spec(n)
        ) by (nonlinear_arith);
        assert(0 <= (last as nat - 1) * Self::pow_base_spec(n));
        assert(Self::pow_base_spec(n) <= last as nat * Self::pow_base_spec(n));
        assert(Self::limbs_value_spec(prefix) >= 0);
        assert(last as nat * Self::pow_base_spec(n) <= Self::limbs_value_spec(prefix) + last as nat * Self::pow_base_spec(n));
        assert(Self::pow_base_spec(n) <= Self::limbs_value_spec(prefix) + last as nat * Self::pow_base_spec(n));
        assert(Self::pow_base_spec(n) <= Self::limbs_value_spec(limbs));
    }

    proof fn lemma_cmp_prefix_last_digit_gt(a: Seq<u32>, b: Seq<u32>)
        requires
            a.len() == b.len(),
            a.len() > 0,
            a[(a.len() - 1) as int] > b[(b.len() - 1) as int],
        ensures
            Self::limbs_value_spec(a) > Self::limbs_value_spec(b),
    {
        let n = (a.len() - 1) as nat;
        let a_prefix = a.subrange(0, n as int);
        let b_prefix = b.subrange(0, n as int);
        let a_last = a[n as int];
        let b_last = b[n as int];
        let a_last_nat = a_last as nat;
        let b_last_nat = b_last as nat;
        let pow_n = Self::pow_base_spec(n);

        Self::lemma_limbs_value_push(a_prefix, a_last);
        Self::lemma_limbs_value_push(b_prefix, b_last);
        assert(a_prefix.push(a_last).len() == a.len());
        assert(b_prefix.push(b_last).len() == b.len());
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] a_prefix.push(a_last)[i] == a[i] by {
            if i < a_prefix.len() {
                assert(a_prefix.push(a_last)[i] == a_prefix[i]);
                assert(a_prefix[i] == a[i]);
            } else {
                assert(i == a_prefix.len());
                assert(i == n as int);
                assert(a_prefix.push(a_last)[i] == a_last);
                assert(a_last == a[i]);
            }
        };
        assert forall|i: int| 0 <= i < b.len() implies #[trigger] b_prefix.push(b_last)[i] == b[i] by {
            if i < b_prefix.len() {
                assert(b_prefix.push(b_last)[i] == b_prefix[i]);
                assert(b_prefix[i] == b[i]);
            } else {
                assert(i == b_prefix.len());
                assert(i == n as int);
                assert(b_prefix.push(b_last)[i] == b_last);
                assert(b_last == b[i]);
            }
        };
        assert(a_prefix.push(a_last) == a);
        assert(b_prefix.push(b_last) == b);
        assert(Self::limbs_value_spec(a) == Self::limbs_value_spec(a_prefix) + a_last_nat * pow_n);
        assert(Self::limbs_value_spec(b) == Self::limbs_value_spec(b_prefix) + b_last_nat * pow_n);
        Self::lemma_limbs_value_lt_pow_len(b_prefix);
        assert(Self::limbs_value_spec(b_prefix) < pow_n);
        let b_shifted = b_last_nat * pow_n;
        assert(
            Self::limbs_value_spec(b_prefix) + b_shifted
                < pow_n + b_shifted
        );
        assert(
            pow_n + b_shifted
                == b_shifted + pow_n
        ) by (nonlinear_arith);
        assert(
            (b_last_nat + 1) * pow_n
                == b_last_nat * pow_n + 1 * pow_n
        ) by (nonlinear_arith);
        assert(1 * pow_n == pow_n);
        assert(b_last_nat * pow_n == b_shifted);
        assert(
            (b_last_nat + 1) * pow_n
                == b_shifted + pow_n
        );
        assert(
            pow_n + b_shifted
                == (b_last_nat + 1) * pow_n
        );
        assert(a_last_nat > b_last_nat);
        assert(b_last_nat + 1 <= a_last_nat);
        assert(
            a_last_nat * pow_n
                == (b_last_nat + 1) * pow_n
                    + (a_last_nat - (b_last_nat + 1)) * pow_n
        ) by (nonlinear_arith);
        assert(0 <= (a_last_nat - (b_last_nat + 1)) * pow_n);
        assert(
            (b_last_nat + 1) * pow_n
                <= a_last_nat * pow_n
        );
        assert(
            Self::limbs_value_spec(b)
                < a_last_nat * pow_n
        );
        assert(Self::limbs_value_spec(a_prefix) >= 0);
        assert(
            a_last_nat * pow_n
                <= Self::limbs_value_spec(a_prefix) + a_last_nat * pow_n
        );
        assert(Self::limbs_value_spec(a) > Self::limbs_value_spec(b));
    }

    proof fn lemma_cmp_high_diff_gt(a: Seq<u32>, b: Seq<u32>, idx: nat)
        requires
            a.len() == b.len(),
            idx < a.len(),
            a[idx as int] > b[idx as int],
            forall|j: int| idx < j < a.len() ==> a[j] == b[j],
        ensures
            Self::limbs_value_spec(a) > Self::limbs_value_spec(b),
    {
        let split = idx + 1;
        let a_prefix = a.subrange(0, split as int);
        let b_prefix = b.subrange(0, split as int);
        let a_suffix = a.subrange(split as int, a.len() as int);
        let b_suffix = b.subrange(split as int, b.len() as int);

        assert(a == a_prefix + a_suffix);
        assert(b == b_prefix + b_suffix);
        assert(a_prefix.len() == split);
        assert(b_prefix.len() == split);
        assert(a_prefix[(a_prefix.len() - 1) as int] == a[idx as int]);
        assert(b_prefix[(b_prefix.len() - 1) as int] == b[idx as int]);
        assert(a_prefix[(a_prefix.len() - 1) as int] > b_prefix[(b_prefix.len() - 1) as int]);
        assert forall|j: int| 0 <= j < a_suffix.len() implies #[trigger] a_suffix[j] == b_suffix[j] by {
            assert(a_suffix[j] == a[(split + j) as int]);
            assert(b_suffix[j] == b[(split + j) as int]);
            assert(idx < split + j);
            assert(split + j < a.len());
            assert(a[(split + j) as int] == b[(split + j) as int]);
        };
        assert(a_suffix == b_suffix);

        Self::lemma_cmp_prefix_last_digit_gt(a_prefix, b_prefix);
        Self::lemma_limbs_value_append(a_prefix, a_suffix);
        Self::lemma_limbs_value_append(b_prefix, b_suffix);
        assert(
            Self::limbs_value_spec(a)
                == Self::limbs_value_spec(a_prefix)
                    + Self::pow_base_spec(a_prefix.len()) * Self::limbs_value_spec(a_suffix)
        );
        assert(
            Self::limbs_value_spec(b)
                == Self::limbs_value_spec(b_prefix)
                    + Self::pow_base_spec(b_prefix.len()) * Self::limbs_value_spec(b_suffix)
        );
        assert(
            Self::limbs_value_spec(b)
                == Self::limbs_value_spec(b_prefix)
                    + Self::pow_base_spec(b_prefix.len()) * Self::limbs_value_spec(a_suffix)
        );
        let suffix_shift = Self::pow_base_spec(a_prefix.len()) * Self::limbs_value_spec(a_suffix);
        assert(
            Self::limbs_value_spec(a)
                == Self::limbs_value_spec(a_prefix) + suffix_shift
        );
        assert(
            Self::limbs_value_spec(b)
                == Self::limbs_value_spec(b_prefix) + suffix_shift
        );
        assert(
            Self::limbs_value_spec(a_prefix) + suffix_shift
                > Self::limbs_value_spec(b_prefix) + suffix_shift
        );
        assert(Self::limbs_value_spec(a) > Self::limbs_value_spec(b));
    }

    proof fn lemma_trimmed_len_gt_implies_value_gt(a: Seq<u32>, alen: nat, b: Seq<u32>, blen: nat)
        requires
            alen <= a.len(),
            blen <= b.len(),
            forall|i: int| alen <= i < a.len() ==> a[i] == 0u32,
            forall|i: int| blen <= i < b.len() ==> b[i] == 0u32,
            blen < alen,
            alen > 0,
            a[(alen - 1) as int] != 0u32,
        ensures
            Self::limbs_value_spec(a) > Self::limbs_value_spec(b),
    {
        let a_trim = a.subrange(0, alen as int);
        let b_trim = b.subrange(0, blen as int);
        Self::lemma_limbs_value_trim_suffix_zeros(a, alen);
        Self::lemma_limbs_value_trim_suffix_zeros(b, blen);
        assert(Self::limbs_value_spec(a) == Self::limbs_value_spec(a_trim));
        assert(Self::limbs_value_spec(b) == Self::limbs_value_spec(b_trim));

        Self::lemma_limbs_value_lt_pow_len(b_trim);
        assert(Self::limbs_value_spec(b_trim) < Self::pow_base_spec(blen));
        assert(blen + 1 <= alen);
        assert((alen - 1) + 1 == alen);
        assert(blen <= (alen - 1) as nat);
        Self::lemma_pow_monotonic(blen, (alen - 1) as nat);
        assert(Self::pow_base_spec(blen) <= Self::pow_base_spec((alen - 1) as nat));
        assert(Self::limbs_value_spec(b_trim) < Self::pow_base_spec((alen - 1) as nat));

        assert(a_trim.len() == alen);
        assert(a_trim[(a_trim.len() - 1) as int] == a[(alen - 1) as int]);
        assert(a_trim[(a_trim.len() - 1) as int] != 0u32);
        Self::lemma_limbs_value_ge_pow_last_nonzero(a_trim);
        assert(Self::pow_base_spec((alen - 1) as nat) <= Self::limbs_value_spec(a_trim));
        assert(Self::limbs_value_spec(b_trim) < Self::limbs_value_spec(a_trim));
        assert(Self::limbs_value_spec(a) > Self::limbs_value_spec(b));
    }

    proof fn lemma_trimmed_high_diff_implies_value_gt(a: Seq<u32>, alen: nat, b: Seq<u32>, blen: nat, idx: nat)
        requires
            alen == blen,
            alen <= a.len(),
            blen <= b.len(),
            forall|i: int| alen <= i < a.len() ==> a[i] == 0u32,
            forall|i: int| blen <= i < b.len() ==> b[i] == 0u32,
            idx < alen,
            a[idx as int] > b[idx as int],
            forall|j: int| idx < j < alen ==> a[j] == b[j],
        ensures
            Self::limbs_value_spec(a) > Self::limbs_value_spec(b),
    {
        let a_trim = a.subrange(0, alen as int);
        let b_trim = b.subrange(0, blen as int);
        assert(a_trim.len() == alen);
        assert(b_trim.len() == blen);
        assert(a_trim.len() == b_trim.len());
        assert(a_trim[idx as int] == a[idx as int]);
        assert(b_trim[idx as int] == b[idx as int]);
        assert(a_trim[idx as int] > b_trim[idx as int]);
        assert forall|j: int| idx < j < a_trim.len() implies #[trigger] a_trim[j] == b_trim[j] by {
            assert(j < a_trim.len());
            assert(a_trim.len() == alen);
            assert(j < alen);
            assert(j < blen);
            assert(a_trim[j] == a[j]);
            assert(b_trim[j] == b[j]);
        };

        Self::lemma_cmp_high_diff_gt(a_trim, b_trim, idx);
        Self::lemma_limbs_value_trim_suffix_zeros(a, alen);
        Self::lemma_limbs_value_trim_suffix_zeros(b, blen);
        assert(Self::limbs_value_spec(a) == Self::limbs_value_spec(a_trim));
        assert(Self::limbs_value_spec(b) == Self::limbs_value_spec(b_trim));
        assert(Self::limbs_value_spec(a) > Self::limbs_value_spec(b));
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
            out.limbs_le@ == limbs_le@,
            out.model@ == model,
            out.wf_spec(),
    {
        let out = RuntimeBigNatWitness { limbs_le, model: Ghost(model) };
        proof {
            assert(out.limbs_le@ == limbs_le@);
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
            out.model@ == x as nat,
            out.wf_spec(),
    {
        let base_u64 = 4_294_967_296u64;
        let lo_u64 = x % base_u64;
        let hi_u64 = x / base_u64;
        let lo = #[verifier::truncate] (lo_u64 as u32);
        let hi = #[verifier::truncate] (hi_u64 as u32);
        let out = Self::from_two_limbs(lo, hi);
        proof {
            assert(x == hi_u64 * base_u64 + lo_u64);
            assert(lo_u64 < base_u64);
            assert(hi_u64 <= 4_294_967_295u64);
            assert(lo as u64 == lo_u64);
            assert(hi as u64 == hi_u64);
            assert(out.model@ == lo as nat + Self::limb_base_spec() * hi as nat);
            assert(Self::limb_base_spec() == 4_294_967_296);
            assert(x == hi as u64 * 4_294_967_296u64 + lo as u64);
            assert(x as nat == hi as nat * 4_294_967_296nat + lo as nat);
            assert(out.model@ == x as nat);
        }
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

    /// Total limb-wise addition helper used by scalar witness plumbing.
    ///
    /// Computes carry-propagating multi-limb addition over little-endian limbs,
    /// then canonicalizes the output by trimming trailing zero limbs.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn add_limbwise_small_total(&self, rhs: &Self) -> (out: Self)
        ensures
            out.wf_spec(),
            out.model@ == Self::limbs_value_spec(self.limbs_le@) + Self::limbs_value_spec(rhs.limbs_le@),
    {
        let alen = Self::trimmed_len_exec(&self.limbs_le);
        let blen = Self::trimmed_len_exec(&rhs.limbs_le);
        assert(alen <= self.limbs_le.len());
        assert(blen <= rhs.limbs_le.len());
        let ghost alen_nat = alen as nat;
        let ghost blen_nat = blen as nat;
        proof {
            assert(alen_nat == alen as nat);
            assert(blen_nat == blen as nat);
        }
        let n = if alen > blen { alen } else { blen };
        let mut out_limbs: Vec<u32> = Vec::new();
        let mut i: usize = 0;
        let mut carry: u64 = 0u64;
        while i < n
            invariant
                i <= n,
                alen <= self.limbs_le.len(),
                blen <= rhs.limbs_le.len(),
                out_limbs@.len() == i,
                carry == 0u64 || carry == 1u64,
                Self::limbs_value_spec(out_limbs@) + carry as nat * Self::pow_base_spec(i as nat)
                    == Self::prefix_sum_spec(self.limbs_le@, alen as nat, i as nat)
                        + Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i as nat),
        {
            let i_old = i;
            let carry_in = carry;
            let ghost i_nat = i_old as nat;
            let a = if i < alen {
                assert(i < self.limbs_le.len());
                self.limbs_le[i] as u64
            } else {
                0u64
            };
            let b = if i < blen {
                assert(i < rhs.limbs_le.len());
                rhs.limbs_le[i] as u64
            } else {
                0u64
            };
            let sum = a + b + carry_in;
            let (digit, next_carry) = if sum >= 4_294_967_296u64 {
                assert(sum == a + b + carry_in);
                assert(a <= 4_294_967_295u64);
                assert(b <= 4_294_967_295u64);
                assert(carry_in <= 1u64);
                assert(sum <= 8_589_934_591u64);
                assert(sum >= 4_294_967_296u64);
                assert(sum - 4_294_967_296u64 <= 4_294_967_295u64);
                let d = (sum - 4_294_967_296u64) as u32;
                (d, 1u64)
            } else {
                assert(sum == a + b + carry_in);
                assert(a <= 4_294_967_295u64);
                assert(b <= 4_294_967_295u64);
                assert(carry_in <= 1u64);
                assert(sum <= 8_589_934_591u64);
                assert(!(sum >= 4_294_967_296u64));
                assert(sum < 4_294_967_296u64);
                assert(sum <= 4_294_967_295u64);
                let d = sum as u32;
                (d, 0u64)
            };
            proof {
                let a_nat = a as nat;
                let b_nat = b as nat;
                let carry_nat = carry_in as nat;
                let digit_nat = digit as nat;
                let next_carry_nat = next_carry as nat;
                assert(i_nat == i_old as nat);
                if i_old < alen {
                    assert(i_old < self.limbs_le.len());
                    assert((i_old as int) < (alen as int));
                    assert(i_nat < alen as nat);
                    assert(i_nat < self.limbs_le@.len());
                    assert(a == self.limbs_le[i_old as int] as u64);
                    assert(a_nat == self.limbs_le@[i_old as int] as nat);
                    assert(a_nat < Self::limb_base_spec());
                    assert(
                        Self::limb_or_zero_spec(self.limbs_le@, alen as nat, i_nat)
                            == self.limbs_le@[i_old as int] as nat
                    );
                    assert(Self::limb_or_zero_spec(self.limbs_le@, alen as nat, i_nat) == a_nat);
                } else {
                    assert(a == 0u64);
                    assert(a_nat == 0);
                    assert(a_nat < Self::limb_base_spec());
                    assert((alen as int) <= (i_old as int));
                    assert(alen as nat <= i_nat);
                    Self::lemma_limb_or_zero_past_logical_len(self.limbs_le@, alen as nat, i_nat);
                    assert(Self::limb_or_zero_spec(self.limbs_le@, alen as nat, i_nat) == a_nat);
                }
                if i_old < blen {
                    assert(i_old < rhs.limbs_le.len());
                    assert((i_old as int) < (blen as int));
                    assert(i_nat < blen as nat);
                    assert(i_nat < rhs.limbs_le@.len());
                    assert(b == rhs.limbs_le[i_old as int] as u64);
                    assert(b_nat == rhs.limbs_le@[i_old as int] as nat);
                    assert(b_nat < Self::limb_base_spec());
                    assert(
                        Self::limb_or_zero_spec(rhs.limbs_le@, blen as nat, i_nat)
                            == rhs.limbs_le@[i_old as int] as nat
                    );
                    assert(Self::limb_or_zero_spec(rhs.limbs_le@, blen as nat, i_nat) == b_nat);
                } else {
                    assert(b == 0u64);
                    assert(b_nat == 0);
                    assert(b_nat < Self::limb_base_spec());
                    assert((blen as int) <= (i_old as int));
                    assert(blen as nat <= i_nat);
                    Self::lemma_limb_or_zero_past_logical_len(rhs.limbs_le@, blen as nat, i_nat);
                    assert(Self::limb_or_zero_spec(rhs.limbs_le@, blen as nat, i_nat) == b_nat);
                }
                assert(carry_in == 0u64 || carry_in == 1u64);
                assert(carry_nat <= 1);
                Self::lemma_add_digit_carry_decompose(a_nat, b_nat, carry_nat);

                assert(sum == a + b + carry_in);
                assert(sum as nat == a_nat + b_nat + carry_nat);
                if sum >= 4_294_967_296u64 {
                    assert(next_carry == 1u64);
                    assert(next_carry_nat == 1);
                    assert(digit as u64 == sum - 4_294_967_296u64);
                    assert(digit_nat == (sum - 4_294_967_296u64) as nat);
                    assert(Self::limb_base_spec() == 4_294_967_296);
                    assert((sum - 4_294_967_296u64) as nat + Self::limb_base_spec() == sum as nat);
                    assert(digit_nat + next_carry_nat * Self::limb_base_spec() == sum as nat);
                } else {
                    assert(next_carry == 0u64);
                    assert(next_carry_nat == 0);
                    assert(digit as u64 == sum);
                    assert(digit_nat == sum as nat);
                    assert(digit_nat + next_carry_nat * Self::limb_base_spec() == sum as nat);
                }
                assert(digit_nat + next_carry_nat * Self::limb_base_spec() == a_nat + b_nat + carry_nat);

                Self::lemma_prefix_sum_step(self.limbs_le@, alen as nat, i_nat);
                Self::lemma_prefix_sum_step(rhs.limbs_le@, blen as nat, i_nat);
                Self::lemma_pow_base_succ(i_nat);
                Self::lemma_add_prefix_step(
                    Self::limbs_value_spec(out_limbs@),
                    Self::prefix_sum_spec(self.limbs_le@, alen as nat, i_nat),
                    Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i_nat),
                    digit_nat,
                    a_nat,
                    b_nat,
                    carry_nat,
                    next_carry_nat,
                    Self::pow_base_spec(i_nat),
                    Self::pow_base_spec(i_nat + 1),
                );
                Self::lemma_limbs_value_push(out_limbs@, digit);
                assert(out_limbs@.push(digit).len() == i_nat + 1);
                assert(
                    Self::prefix_sum_spec(self.limbs_le@, alen as nat, i_nat + 1)
                        == Self::prefix_sum_spec(self.limbs_le@, alen as nat, i_nat)
                            + Self::limb_or_zero_spec(self.limbs_le@, alen as nat, i_nat)
                                * Self::pow_base_spec(i_nat)
                );
                assert(
                    Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i_nat + 1)
                        == Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i_nat)
                            + Self::limb_or_zero_spec(rhs.limbs_le@, blen as nat, i_nat)
                                * Self::pow_base_spec(i_nat)
                );
                assert(
                    Self::prefix_sum_spec(self.limbs_le@, alen as nat, i_nat + 1)
                        == Self::prefix_sum_spec(self.limbs_le@, alen as nat, i_nat)
                            + a_nat * Self::pow_base_spec(i_nat)
                );
                assert(
                    Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i_nat + 1)
                        == Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i_nat)
                            + b_nat * Self::pow_base_spec(i_nat)
                );
                assert(
                    Self::limbs_value_spec(out_limbs@.push(digit))
                        + next_carry_nat * Self::pow_base_spec(i_nat + 1)
                        == Self::prefix_sum_spec(self.limbs_le@, alen as nat, i_nat + 1)
                            + Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i_nat + 1)
                );
            }
            carry = next_carry;
            out_limbs.push(digit);
            i = i + 1;
        }
        assert(i == n);
        assert(out_limbs@.len() == n);
        let ghost n_nat = n as nat;
        let ghost pre_push = out_limbs@;
        proof {
            assert(
                Self::limbs_value_spec(pre_push) + carry as nat * Self::pow_base_spec(n_nat)
                    == Self::prefix_sum_spec(self.limbs_le@, alen_nat, n_nat)
                        + Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, n_nat)
            );
            if alen_nat <= n_nat {
                Self::lemma_prefix_sum_constant_past_logical_len(self.limbs_le@, alen_nat, n_nat);
            }
            if blen_nat <= n_nat {
                Self::lemma_prefix_sum_constant_past_logical_len(rhs.limbs_le@, blen_nat, n_nat);
            }
            Self::lemma_prefix_sum_eq_subrange_value(self.limbs_le@, alen_nat);
            Self::lemma_prefix_sum_eq_subrange_value(rhs.limbs_le@, blen_nat);
            assert(forall|j: int| alen_nat <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
            assert(forall|j: int| blen_nat <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32);
            Self::lemma_limbs_value_trim_suffix_zeros(self.limbs_le@, alen_nat);
            Self::lemma_limbs_value_trim_suffix_zeros(rhs.limbs_le@, blen_nat);
            assert(
                Self::prefix_sum_spec(self.limbs_le@, alen_nat, n_nat)
                    == Self::limbs_value_spec(self.limbs_le@)
            );
            assert(
                Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, n_nat)
                    == Self::limbs_value_spec(rhs.limbs_le@)
            );
        }
        if carry != 0u64 {
            out_limbs.push(1u32);
        }
        proof {
            if carry == 0u64 {
                assert(out_limbs@ == pre_push);
                assert(carry as nat == 0);
                assert(
                    Self::limbs_value_spec(out_limbs@)
                        == Self::limbs_value_spec(self.limbs_le@)
                            + Self::limbs_value_spec(rhs.limbs_le@)
                );
            } else {
                assert(carry == 1u64);
                assert(carry as nat == 1);
                Self::lemma_limbs_value_push(pre_push, 1u32);
                assert(out_limbs@ == pre_push.push(1u32));
                assert(
                    Self::limbs_value_spec(out_limbs@)
                        == Self::limbs_value_spec(pre_push) + Self::pow_base_spec(n_nat)
                );
                assert(
                    Self::limbs_value_spec(out_limbs@)
                        == Self::limbs_value_spec(self.limbs_le@)
                            + Self::limbs_value_spec(rhs.limbs_le@)
                );
            }
        }
        let out_limbs = Self::trim_trailing_zero_limbs(out_limbs);
        proof {
            assert(
                Self::limbs_value_spec(out_limbs@)
                    == Self::limbs_value_spec(self.limbs_le@)
                        + Self::limbs_value_spec(rhs.limbs_le@)
            );
        }
        let ghost model = Self::limbs_value_spec(out_limbs@);
        let out = Self::from_parts(out_limbs, Ghost(model));
        proof {
            assert(out.model@ == Self::limbs_value_spec(out.limbs_le@));
            assert(out.model@ == Self::limbs_value_spec(self.limbs_le@) + Self::limbs_value_spec(rhs.limbs_le@));
        }
        out
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn trimmed_len_exec(limbs: &Vec<u32>) -> (out: usize)
        ensures
            out <= limbs.len(),
            forall|i: int| out <= i < limbs.len() ==> limbs@[i] == 0u32,
            out > 0 ==> limbs@[(out - 1) as int] != 0u32,
    {
        let mut n = limbs.len();
        while n > 0 && limbs[n - 1] == 0u32
            invariant
                n <= limbs.len(),
                forall|i: int| n <= i < limbs.len() ==> limbs@[i] == 0u32,
        {
            assert(n > 0);
            assert(limbs[(n - 1) as int] == 0u32);
            n = n - 1;
        }
        assert(n <= limbs.len());
        if n > 0 {
            assert(!(n > 0 && limbs[n - 1] == 0u32));
            assert(limbs[n - 1] != 0u32);
            assert(limbs@[(n - 1) as int] != 0u32);
        }
        n
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn trim_trailing_zero_limbs(limbs: Vec<u32>) -> (out: Vec<u32>)
        ensures
            Self::canonical_limbs_spec(out@),
            Self::limbs_value_spec(out@) == Self::limbs_value_spec(limbs@),
    {
        let n = Self::trimmed_len_exec(&limbs);
        assert(n <= limbs.len());
        let mut out: Vec<u32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n <= limbs.len(),
                out@ == limbs@.subrange(0, i as int),
        {
            assert(i < limbs.len());
            out.push(limbs[i]);
            i = i + 1;
        }
        proof {
            assert(out@ == limbs@.subrange(0, n as int));
            if n == 0 {
                assert(out@.len() == 0);
                assert(Self::canonical_limbs_spec(out@));
            } else {
                assert(0 < n);
                assert(out@.len() == n);
                assert(limbs@[(n - 1) as int] != 0u32);
                assert(out@[(out@.len() - 1) as int] == limbs@[(n - 1) as int]);
                assert(out@[(out@.len() - 1) as int] != 0u32);
                assert(Self::canonical_limbs_spec(out@));
            }
        }
        proof {
            let ng: nat = n as nat;
            assert(ng <= limbs@.len());
            assert(forall|i: int| ng <= i < limbs@.len() ==> limbs@[i] == 0u32);
            Self::lemma_limbs_value_trim_suffix_zeros(limbs@, ng);
            assert(
                Self::limbs_value_spec(limbs@)
                    == Self::limbs_value_spec(limbs@.subrange(0, n as int))
            );
            assert(out@ == limbs@.subrange(0, n as int));
            assert(
                Self::limbs_value_spec(out@)
                    == Self::limbs_value_spec(limbs@.subrange(0, n as int))
            );
            assert(Self::limbs_value_spec(out@) == Self::limbs_value_spec(limbs@));
        }
        out
    }

    /// Total limb-wise multiplication helper used by scalar witness plumbing.
    ///
    /// Computes schoolbook multi-limb multiplication over little-endian limbs,
    /// with local carry propagation and canonical trailing-zero trim.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn mul_limbwise_small_total(&self, rhs: &Self) -> (out: Self)
        ensures
            out.wf_spec(),
    {
        let alen = Self::trimmed_len_exec(&self.limbs_le);
        let blen = Self::trimmed_len_exec(&rhs.limbs_le);
        assert(alen <= self.limbs_le.len());
        assert(blen <= rhs.limbs_le.len());
        if alen == 0 || blen == 0 {
            Self::zero()
        } else {
            let mut total_len = alen.wrapping_add(blen);
            total_len = total_len.wrapping_add(2usize);
            let mut out_limbs: Vec<u32> = Vec::new();
            while out_limbs.len() < total_len
                invariant
                    out_limbs.len() <= total_len,
            {
                out_limbs.push(0u32);
            }

            let mut i: usize = 0;
            while i < alen
                invariant
                    i <= alen,
                    alen <= self.limbs_le.len(),
                    blen <= rhs.limbs_le.len(),
                    out_limbs.len() == total_len,
            {
                assert(i < self.limbs_le.len());
                let ai = self.limbs_le[i] as u128;
                let mut carry: u128 = 0u128;
                let mut j: usize = 0;
                while j < blen
                    invariant
                        j <= blen,
                        i < alen,
                        alen <= self.limbs_le.len(),
                        blen <= rhs.limbs_le.len(),
                        out_limbs.len() == total_len,
                {
                    let idx = i.wrapping_add(j);
                    if idx >= out_limbs.len() {
                        break;
                    }
                    assert(j < rhs.limbs_le.len());
                    let bj = rhs.limbs_le[j] as u128;
                    let existing = out_limbs[idx] as u128;
                    let term = ai.wrapping_mul(bj);
                    let total = term.wrapping_add(existing).wrapping_add(carry);
                    #[verifier::truncate]
                    let digit = total as u32;
                    out_limbs[idx] = digit;
                    carry = total >> 32;
                    j = j + 1;
                }

                let mut k = i.wrapping_add(blen);
                while carry != 0u128
                    invariant
                        out_limbs.len() == total_len,
                {
                    if k >= out_limbs.len() {
                        break;
                    }
                    let existing = out_limbs[k] as u128;
                    let total = existing.wrapping_add(carry);
                    #[verifier::truncate]
                    let digit = total as u32;
                    out_limbs[k] = digit;
                    carry = total >> 32;
                    k = k + 1;
                }

                i = i + 1;
            }

            let out_limbs = Self::trim_trailing_zero_limbs(out_limbs);
            let ghost model = Self::limbs_value_spec(out_limbs@);
            Self::from_parts(out_limbs, Ghost(model))
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
            out == -1 ==> Self::limbs_value_spec(self.limbs_le@) < Self::limbs_value_spec(rhs.limbs_le@),
            out == 0 ==> Self::limbs_value_spec(self.limbs_le@) == Self::limbs_value_spec(rhs.limbs_le@),
            out == 1 ==> Self::limbs_value_spec(self.limbs_le@) > Self::limbs_value_spec(rhs.limbs_le@),
            self.limbs_le@ == rhs.limbs_le@ ==> out == 0,
    {
        let alen = Self::trimmed_len_exec(&self.limbs_le);
        let blen = Self::trimmed_len_exec(&rhs.limbs_le);
        if alen > blen {
            proof {
                let alen_nat = alen as nat;
                let blen_nat = blen as nat;
                assert(alen_nat <= self.limbs_le@.len());
                assert(blen_nat <= rhs.limbs_le@.len());
                assert(forall|j: int| alen_nat <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
                assert(forall|j: int| blen_nat <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32);
                assert(alen_nat > blen_nat);
                assert(alen_nat > 0);
                assert(self.limbs_le@[(alen - 1) as int] != 0u32);
                Self::lemma_trimmed_len_gt_implies_value_gt(
                    self.limbs_le@,
                    alen_nat,
                    rhs.limbs_le@,
                    blen_nat,
                );
            }
            1i8
        } else if alen < blen {
            proof {
                let alen_nat = alen as nat;
                let blen_nat = blen as nat;
                assert(alen_nat <= self.limbs_le@.len());
                assert(blen_nat <= rhs.limbs_le@.len());
                assert(forall|j: int| alen_nat <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
                assert(forall|j: int| blen_nat <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32);
                assert(blen_nat > alen_nat);
                assert(blen_nat > 0);
                assert(rhs.limbs_le@[(blen - 1) as int] != 0u32);
                Self::lemma_trimmed_len_gt_implies_value_gt(
                    rhs.limbs_le@,
                    blen_nat,
                    self.limbs_le@,
                    alen_nat,
                );
                assert(Self::limbs_value_spec(rhs.limbs_le@) > Self::limbs_value_spec(self.limbs_le@));
                assert(Self::limbs_value_spec(self.limbs_le@) < Self::limbs_value_spec(rhs.limbs_le@));
            }
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
                    forall|j: int| alen <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32,
                    forall|j: int| blen <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32,
                    forall|j: int| i <= j < alen ==> self.limbs_le@[j] == rhs.limbs_le@[j],
            {
                let idx = i - 1;
                assert(idx < self.limbs_le.len());
                assert(idx < rhs.limbs_le.len());
                let a = self.limbs_le[idx];
                let b = rhs.limbs_le[idx];
                if a > b {
                    proof {
                        let alen_nat = alen as nat;
                        let blen_nat = blen as nat;
                        let idx_nat = idx as nat;
                        assert(alen_nat == blen_nat);
                        assert(alen_nat <= self.limbs_le@.len());
                        assert(blen_nat <= rhs.limbs_le@.len());
                        assert(forall|j: int| alen_nat <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
                        assert(forall|j: int| blen_nat <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32);
                        assert(idx_nat < alen_nat);
                        assert(self.limbs_le@[idx as int] > rhs.limbs_le@[idx as int]);
                        assert(i == idx + 1);
                        assert forall|j: int| idx_nat < j < alen_nat
                            implies self.limbs_le@[j] == rhs.limbs_le@[j] by {
                            assert(idx as int + 1 <= j);
                            assert(i as int == idx as int + 1);
                            assert(i <= j);
                            assert(j < alen);
                            assert(self.limbs_le@[j] == rhs.limbs_le@[j]);
                        };
                        Self::lemma_trimmed_high_diff_implies_value_gt(
                            self.limbs_le@,
                            alen_nat,
                            rhs.limbs_le@,
                            blen_nat,
                            idx_nat,
                        );
                    }
                    return 1i8;
                } else if a < b {
                    proof {
                        let alen_nat = alen as nat;
                        let blen_nat = blen as nat;
                        let idx_nat = idx as nat;
                        assert(alen_nat == blen_nat);
                        assert(alen_nat <= self.limbs_le@.len());
                        assert(blen_nat <= rhs.limbs_le@.len());
                        assert(forall|j: int| alen_nat <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
                        assert(forall|j: int| blen_nat <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32);
                        assert(idx_nat < alen_nat);
                        assert(rhs.limbs_le@[idx as int] > self.limbs_le@[idx as int]);
                        assert(i == idx + 1);
                        assert forall|j: int| idx_nat < j < alen_nat
                            implies rhs.limbs_le@[j] == self.limbs_le@[j] by {
                            assert(idx as int + 1 <= j);
                            assert(i as int == idx as int + 1);
                            assert(i <= j);
                            assert(j < alen);
                            assert(self.limbs_le@[j] == rhs.limbs_le@[j]);
                        };
                        Self::lemma_trimmed_high_diff_implies_value_gt(
                            rhs.limbs_le@,
                            blen_nat,
                            self.limbs_le@,
                            alen_nat,
                            idx_nat,
                        );
                        assert(Self::limbs_value_spec(rhs.limbs_le@) > Self::limbs_value_spec(self.limbs_le@));
                        assert(Self::limbs_value_spec(self.limbs_le@) < Self::limbs_value_spec(rhs.limbs_le@));
                    }
                    return -1i8;
                }
                assert(a == b);
                assert(self.limbs_le@[idx as int] == rhs.limbs_le@[idx as int]);
                i = i - 1;
            }
            proof {
                let alen_nat = alen as nat;
                let blen_nat = blen as nat;
                assert(i == 0);
                assert(alen == blen);
                assert(forall|j: int| 0 <= j < alen ==> self.limbs_le@[j] == rhs.limbs_le@[j]);
                assert forall|j: int| (0 <= j && j < alen) implies
                    #[trigger] self.limbs_le@.subrange(0, alen as int)[j]
                        == rhs.limbs_le@.subrange(0, blen as int)[j] by {
                    if 0 <= j && j < alen {
                        assert(self.limbs_le@.subrange(0, alen as int)[j] == self.limbs_le@[j]);
                        assert(rhs.limbs_le@.subrange(0, blen as int)[j] == rhs.limbs_le@[j]);
                    }
                };
                assert(self.limbs_le@.subrange(0, alen as int) == rhs.limbs_le@.subrange(0, blen as int));
                assert(alen_nat <= self.limbs_le@.len());
                assert(blen_nat <= rhs.limbs_le@.len());
                assert(forall|j: int| alen_nat <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
                assert(forall|j: int| blen_nat <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32);
                Self::lemma_limbs_value_trim_suffix_zeros(self.limbs_le@, alen_nat);
                Self::lemma_limbs_value_trim_suffix_zeros(rhs.limbs_le@, blen_nat);
                assert(
                    Self::limbs_value_spec(self.limbs_le@)
                        == Self::limbs_value_spec(self.limbs_le@.subrange(0, alen as int))
                );
                assert(
                    Self::limbs_value_spec(rhs.limbs_le@)
                        == Self::limbs_value_spec(rhs.limbs_le@.subrange(0, blen as int))
                );
                assert(
                    Self::limbs_value_spec(self.limbs_le@.subrange(0, alen as int))
                        == Self::limbs_value_spec(rhs.limbs_le@.subrange(0, blen as int))
                );
                assert(
                    Self::limbs_value_spec(self.limbs_le@)
                        == Self::limbs_value_spec(rhs.limbs_le@)
                );
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
            Self::limbs_value_spec(self.limbs_le@) <= Self::limbs_value_spec(rhs.limbs_le@) ==> out.model@ == 0,
            Self::limbs_value_spec(rhs.limbs_le@) < Self::limbs_value_spec(self.limbs_le@)
                ==> out.model@ == Self::limbs_value_spec(self.limbs_le@) - Self::limbs_value_spec(rhs.limbs_le@),
    {
        let cmp = self.cmp_limbwise_small_total(rhs);
        if cmp == -1i8 {
            let out = Self::zero();
            proof {
                assert(Self::limbs_value_spec(self.limbs_le@) < Self::limbs_value_spec(rhs.limbs_le@));
                assert(Self::limbs_value_spec(self.limbs_le@) <= Self::limbs_value_spec(rhs.limbs_le@));
                assert(out.model@ == 0);
            }
            out
        } else if cmp == 0i8 {
            let out = Self::zero();
            proof {
                assert(Self::limbs_value_spec(self.limbs_le@) == Self::limbs_value_spec(rhs.limbs_le@));
                assert(Self::limbs_value_spec(self.limbs_le@) <= Self::limbs_value_spec(rhs.limbs_le@));
                assert(out.model@ == 0);
            }
            out
        } else {
            proof {
                assert(cmp == -1 || cmp == 0 || cmp == 1);
                assert(cmp != -1i8);
                assert(cmp != 0i8);
                assert(cmp == 1i8);
                assert(Self::limbs_value_spec(self.limbs_le@) > Self::limbs_value_spec(rhs.limbs_le@));
                assert(!(Self::limbs_value_spec(self.limbs_le@) <= Self::limbs_value_spec(rhs.limbs_le@)));
            }
            let alen = Self::trimmed_len_exec(&self.limbs_le);
            let blen = Self::trimmed_len_exec(&rhs.limbs_le);
            assert(alen <= self.limbs_le.len());
            assert(blen <= rhs.limbs_le.len());
            proof {
                if blen > alen {
                    let alen_nat = alen as nat;
                    let blen_nat = blen as nat;
                    assert(alen_nat <= self.limbs_le@.len());
                    assert(blen_nat <= rhs.limbs_le@.len());
                    assert(forall|j: int| alen_nat <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
                    assert(forall|j: int| blen_nat <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32);
                    assert(blen_nat > alen_nat);
                    assert(blen_nat > 0);
                    assert(rhs.limbs_le@[(blen - 1) as int] != 0u32);
                    Self::lemma_trimmed_len_gt_implies_value_gt(
                        rhs.limbs_le@,
                        blen_nat,
                        self.limbs_le@,
                        alen_nat,
                    );
                    assert(Self::limbs_value_spec(rhs.limbs_le@) > Self::limbs_value_spec(self.limbs_le@));
                    assert(Self::limbs_value_spec(self.limbs_le@) > Self::limbs_value_spec(rhs.limbs_le@));
                }
                assert(blen <= alen);
            }
            let mut out_limbs: Vec<u32> = Vec::new();
            let mut i: usize = 0;
            let mut borrow: u64 = 0u64;

            while i < alen
                invariant
                    i <= alen,
                    alen <= self.limbs_le.len(),
                    blen <= rhs.limbs_le.len(),
                    out_limbs@.len() == i,
                    borrow == 0u64 || borrow == 1u64,
                    Self::limbs_value_spec(out_limbs@)
                        + Self::prefix_sum_spec(rhs.limbs_le@, blen as nat, i as nat)
                        == Self::prefix_sum_spec(self.limbs_le@, alen as nat, i as nat)
                            + borrow as nat * Self::pow_base_spec(i as nat),
            {
                assert(i < self.limbs_le.len());
                let a = self.limbs_le[i] as u64;
                let b = if i < blen {
                    assert(i < rhs.limbs_le.len());
                    rhs.limbs_le[i] as u64
                } else {
                    0u64
                };
                let borrow_in = borrow;
                assert(a <= 4_294_967_295u64);
                assert(b <= 4_294_967_295u64);
                assert(borrow_in <= 1u64);
                let need = b + borrow_in;
                let digit64: u64;
                let next_borrow: u64;
                if a >= need {
                    next_borrow = 0u64;
                    digit64 = a - need;
                } else {
                    let a_plus_base = 4_294_967_296u64.wrapping_add(a);
                    next_borrow = 1u64;
                    digit64 = a_plus_base.wrapping_sub(need);
                }
                #[verifier::truncate]
                let digit = digit64 as u32;
                proof {
                    let i_nat = i as nat;
                    let alen_nat = alen as nat;
                    let blen_nat = blen as nat;
                    let a_nat = a as nat;
                    let b_nat = b as nat;
                    let borrow_nat = borrow_in as nat;
                    let next_borrow_nat = next_borrow as nat;
                    let digit_nat = digit as nat;

                    assert(a <= 4_294_967_295u64);
                    assert(a < 4_294_967_296u64);
                    assert(b <= 4_294_967_295u64);
                    assert(b < 4_294_967_296u64);
                    assert(a_nat < Self::limb_base_spec());
                    assert(b_nat < Self::limb_base_spec());
                    assert(Self::limb_base_spec() == 4_294_967_296);
                    assert(borrow_in == 0u64 || borrow_in == 1u64);
                    assert(borrow_nat <= 1);
                    assert(next_borrow == 0u64 || next_borrow == 1u64);
                    assert(next_borrow_nat <= 1);
                    assert(need == b + borrow_in);
                    assert(need as nat == b_nat + borrow_nat);

                    if a >= need {
                        assert(next_borrow == 0u64);
                        assert(next_borrow_nat == 0);
                        assert(digit64 == a - need);
                        assert(digit64 < 4_294_967_296u64);
                        assert(digit as u64 == digit64);
                        assert(digit_nat == digit64 as nat);
                        assert(digit_nat + b_nat + borrow_nat == a_nat);
                        assert(digit_nat + b_nat + borrow_nat == a_nat + next_borrow_nat * Self::limb_base_spec());
                    } else {
                        assert(next_borrow == 1u64);
                        assert(next_borrow_nat == 1);
                        assert(a < need);
                        assert(borrow_in <= 1u64);
                        assert(b + borrow_in <= 4_294_967_295u64 + 1u64);
                        assert(need <= 4_294_967_295u64 + 1u64);
                        assert(need <= 4_294_967_296u64);
                        assert(digit64 == 4_294_967_296u64.wrapping_add(a).wrapping_sub(need));
                        assert(4_294_967_296u64 + a <= 8_589_934_591u64);
                        assert(4_294_967_296u64.wrapping_add(a) == 4_294_967_296u64 + a);
                        assert(need <= 4_294_967_296u64 + a);
                        assert(4_294_967_296u64.wrapping_add(a).wrapping_sub(need) == 4_294_967_296u64 + a - need);
                        assert(digit64 == 4_294_967_296u64 + a - need);
                        assert(digit64 < 4_294_967_296u64);
                        assert(digit as u64 == digit64);
                        assert(digit_nat == digit64 as nat);
                        assert(
                            digit_nat
                                == a_nat + 4_294_967_296nat - (b_nat + borrow_nat)
                        );
                        assert(digit_nat + b_nat + borrow_nat == a_nat + 4_294_967_296nat);
                        assert(digit_nat + b_nat + borrow_nat == a_nat + next_borrow_nat * Self::limb_base_spec());
                    }

                    assert(i_nat < alen_nat);
                    assert(Self::limb_or_zero_spec(self.limbs_le@, alen_nat, i_nat) == a_nat);
                    if i < blen {
                        assert(i_nat < blen_nat);
                        assert(Self::limb_or_zero_spec(rhs.limbs_le@, blen_nat, i_nat) == b_nat);
                    } else {
                        assert(blen_nat <= i_nat);
                        Self::lemma_limb_or_zero_past_logical_len(rhs.limbs_le@, blen_nat, i_nat);
                        assert(Self::limb_or_zero_spec(rhs.limbs_le@, blen_nat, i_nat) == 0);
                        assert(b_nat == 0);
                    }

                    Self::lemma_prefix_sum_step(self.limbs_le@, alen_nat, i_nat);
                    Self::lemma_prefix_sum_step(rhs.limbs_le@, blen_nat, i_nat);
                    assert(
                        Self::prefix_sum_spec(self.limbs_le@, alen_nat, i_nat + 1)
                            == Self::prefix_sum_spec(self.limbs_le@, alen_nat, i_nat)
                                + a_nat * Self::pow_base_spec(i_nat)
                    );
                    assert(
                        Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, i_nat + 1)
                            == Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, i_nat)
                                + b_nat * Self::pow_base_spec(i_nat)
                    );

                    Self::lemma_pow_base_succ(i_nat);
                    Self::lemma_sub_prefix_step(
                        Self::limbs_value_spec(out_limbs@),
                        Self::prefix_sum_spec(self.limbs_le@, alen_nat, i_nat),
                        Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, i_nat),
                        digit_nat,
                        a_nat,
                        b_nat,
                        borrow_nat,
                        next_borrow_nat,
                        Self::pow_base_spec(i_nat),
                        Self::pow_base_spec(i_nat + 1),
                    );
                    Self::lemma_limbs_value_push(out_limbs@, digit);
                    assert(
                        Self::limbs_value_spec(out_limbs@.push(digit))
                            + Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, i_nat + 1)
                            == Self::prefix_sum_spec(self.limbs_le@, alen_nat, i_nat + 1)
                                + next_borrow_nat * Self::pow_base_spec(i_nat + 1)
                    );
                }
                borrow = next_borrow;
                out_limbs.push(digit);
                i = i + 1;
            }
            assert(i == alen);
            assert(out_limbs@.len() == alen);
            let ghost alen_nat = alen as nat;
            let ghost blen_nat = blen as nat;
            let ghost pre_trim = out_limbs@;
            proof {
                assert(
                    Self::limbs_value_spec(pre_trim)
                        + Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, alen_nat)
                        == Self::prefix_sum_spec(self.limbs_le@, alen_nat, alen_nat)
                            + borrow as nat * Self::pow_base_spec(alen_nat)
                );

                assert(blen_nat <= alen_nat);
                Self::lemma_prefix_sum_constant_past_logical_len(rhs.limbs_le@, blen_nat, alen_nat);
                Self::lemma_prefix_sum_eq_subrange_value(rhs.limbs_le@, blen_nat);
                assert(forall|j: int| blen_nat <= j < rhs.limbs_le@.len() ==> rhs.limbs_le@[j] == 0u32);
                Self::lemma_limbs_value_trim_suffix_zeros(rhs.limbs_le@, blen_nat);
                assert(
                    Self::prefix_sum_spec(rhs.limbs_le@, blen_nat, alen_nat)
                        == Self::limbs_value_spec(rhs.limbs_le@)
                );

                Self::lemma_prefix_sum_eq_subrange_value(self.limbs_le@, alen_nat);
                assert(forall|j: int| alen_nat <= j < self.limbs_le@.len() ==> self.limbs_le@[j] == 0u32);
                Self::lemma_limbs_value_trim_suffix_zeros(self.limbs_le@, alen_nat);
                assert(
                    Self::prefix_sum_spec(self.limbs_le@, alen_nat, alen_nat)
                        == Self::limbs_value_spec(self.limbs_le@)
                );
                assert(
                    Self::limbs_value_spec(pre_trim)
                        + Self::limbs_value_spec(rhs.limbs_le@)
                        == Self::limbs_value_spec(self.limbs_le@)
                            + borrow as nat * Self::pow_base_spec(alen_nat)
                );

                let self_trim = self.limbs_le@.subrange(0, alen as int);
                assert(self_trim.len() == alen_nat);
                Self::lemma_limbs_value_lt_pow_len(self_trim);
                assert(Self::limbs_value_spec(self_trim) < Self::pow_base_spec(alen_nat));
                assert(Self::limbs_value_spec(self.limbs_le@) == Self::limbs_value_spec(self_trim));
                assert(Self::limbs_value_spec(self.limbs_le@) < Self::pow_base_spec(alen_nat));

                Self::lemma_limbs_value_lt_pow_len(pre_trim);
                assert(Self::limbs_value_spec(pre_trim) < Self::pow_base_spec(alen_nat));
                assert(borrow == 0u64 || borrow == 1u64);
                assert(Self::limbs_value_spec(self.limbs_le@) > Self::limbs_value_spec(rhs.limbs_le@));
                if borrow == 1u64 {
                    let pre_val = Self::limbs_value_spec(pre_trim);
                    let rhs_val = Self::limbs_value_spec(rhs.limbs_le@);
                    let self_val = Self::limbs_value_spec(self.limbs_le@);
                    let pow_n = Self::pow_base_spec(alen_nat);
                    assert(borrow as nat == 1);
                    assert(
                        pre_val + rhs_val
                            == self_val + pow_n
                    );
                    assert(pre_val < pow_n);
                    assert(pre_val <= pow_n);
                    assert(pre_val + rhs_val <= pow_n + rhs_val);
                    assert(self_val + pow_n <= pow_n + rhs_val);
                    let d = self_val - rhs_val;
                    assert(self_val == rhs_val + d);
                    assert(rhs_val + 1 <= self_val);
                    assert(1 <= d);
                    assert(rhs_val + 1 <= rhs_val + d);
                    assert(rhs_val + 1 + pow_n <= rhs_val + d + pow_n);
                    assert(rhs_val + d + pow_n == self_val + pow_n);
                    assert(rhs_val + 1 + pow_n <= self_val + pow_n);
                    assert(rhs_val + 1 + pow_n <= pow_n + rhs_val);
                    assert(false);
                }
                assert(borrow != 1u64);
                assert(borrow == 0u64);
                assert(
                    Self::limbs_value_spec(pre_trim) + Self::limbs_value_spec(rhs.limbs_le@)
                        == Self::limbs_value_spec(self.limbs_le@)
                );
                assert(
                    Self::limbs_value_spec(pre_trim)
                        == Self::limbs_value_spec(self.limbs_le@) - Self::limbs_value_spec(rhs.limbs_le@)
                );
            }

            let out_limbs = Self::trim_trailing_zero_limbs(out_limbs);
            proof {
                assert(Self::limbs_value_spec(out_limbs@) == Self::limbs_value_spec(pre_trim));
                assert(
                    Self::limbs_value_spec(out_limbs@)
                        == Self::limbs_value_spec(self.limbs_le@) - Self::limbs_value_spec(rhs.limbs_le@)
                );
            }
            let ghost model = Self::limbs_value_spec(out_limbs@);
            let out = Self::from_parts(out_limbs, Ghost(model));
            proof {
                assert(
                    out.model@
                        == Self::limbs_value_spec(self.limbs_le@) - Self::limbs_value_spec(rhs.limbs_le@)
                );
            }
            out
        }
    }

    /// Total witness copy helper for scalar witness plumbing.
    ///
    /// Preserves all limbs exactly (after trailing-zero normalization).
    #[verifier::exec_allows_no_decreases_clause]
    pub fn copy_small_total(&self) -> (out: Self)
        ensures
            out.wf_spec(),
            out.model@ == Self::limbs_value_spec(self.limbs_le@),
    {
        let n = Self::trimmed_len_exec(&self.limbs_le);
        assert(n <= self.limbs_le.len());
        let mut out_limbs: Vec<u32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n <= self.limbs_le.len(),
                out_limbs@ == self.limbs_le@.subrange(0, i as int),
        {
            assert(i < self.limbs_le.len());
            out_limbs.push(self.limbs_le[i]);
            i = i + 1;
        }
        proof {
            assert(out_limbs@ == self.limbs_le@.subrange(0, n as int));
        }
        proof {
            if n == 0 {
                assert(out_limbs@.len() == 0);
                assert(Self::canonical_limbs_spec(out_limbs@));
            } else {
                assert(0 < n);
                assert(out_limbs@.len() == n);
                assert(self.limbs_le@[(n - 1) as int] != 0u32);
                assert(out_limbs@[(out_limbs@.len() - 1) as int] == self.limbs_le@[(n - 1) as int]);
                assert(out_limbs@[(out_limbs@.len() - 1) as int] != 0u32);
                assert(Self::canonical_limbs_spec(out_limbs@));
            }
        }
        proof {
            let ng: nat = n as nat;
            assert(ng <= self.limbs_le@.len());
            assert(forall|i: int| ng <= i < self.limbs_le@.len() ==> self.limbs_le@[i] == 0u32);
            Self::lemma_limbs_value_trim_suffix_zeros(self.limbs_le@, ng);
            assert(
                Self::limbs_value_spec(self.limbs_le@)
                    == Self::limbs_value_spec(self.limbs_le@.subrange(0, n as int))
            );
            assert(out_limbs@ == self.limbs_le@.subrange(0, n as int));
            assert(
                Self::limbs_value_spec(self.limbs_le@)
                    == Self::limbs_value_spec(out_limbs@)
            );
        }
        let ghost model = Self::limbs_value_spec(out_limbs@);
        let out = Self::from_parts(out_limbs, Ghost(model));
        proof {
            assert(out.model@ == Self::limbs_value_spec(out.limbs_le@));
            assert(out.limbs_le@ == self.limbs_le@.subrange(0, n as int));
            assert(
                Self::limbs_value_spec(self.limbs_le@)
                    == Self::limbs_value_spec(out.limbs_le@)
            );
            assert(out.model@ == Self::limbs_value_spec(self.limbs_le@));
        }
        out
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
