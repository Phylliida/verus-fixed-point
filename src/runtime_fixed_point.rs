use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::fixed_point::FixedPoint;
#[cfg(verus_keep_ghost)]
use crate::fixed_point::limbs::*;
#[cfg(verus_keep_ghost)]
use crate::fixed_point::pow2::*;

verus! {

// ── RuntimeFixedPoint struct ───────────────────────────

/// Exec-level fixed-point number.
pub struct RuntimeFixedPoint {
    pub limbs: Vec<u32>,
    pub sign: bool,
    pub n: Ghost<nat>,
    pub frac: Ghost<nat>,
    pub model: Ghost<FixedPoint>,
}

impl RuntimeFixedPoint {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.limbs@.len() == self.model@.n
        &&& self.limbs@ == self.model@.limbs
        &&& self.sign == self.model@.sign
        &&& self.n@ == self.model@.n
        &&& self.frac@ == self.model@.frac
        &&& self.model@.wf_spec()
    }
}

impl View for RuntimeFixedPoint {
    type V = FixedPoint;

    open spec fn view(&self) -> FixedPoint {
        self.model@
    }
}

// ── Unsigned limb operations ───────────────────────────

/// Unsigned carry-chain addition of two n-limb arrays.
/// Returns (result, carry_out) where carry_out is 0 or 1.
pub fn add_limbs(a: &Vec<u32>, b: &Vec<u32>, n: usize) -> (result: (Vec<u32>, u32))
    requires
        a@.len() == n,
        b@.len() == n,
    ensures
        result.0@.len() == n,
        limbs_to_nat(result.0@) + (result.1 as nat) * pow2((n * 32) as nat)
            == limbs_to_nat(a@) + limbs_to_nat(b@),
        result.1 <= 1,
{
    let mut out: Vec<u32> = Vec::new();
    let mut carry: u64 = 0;
    let mut i: usize = 0;

    proof {
        lemma_limbs_to_nat_subrange_zero(a@);
        lemma_limbs_to_nat_subrange_zero(b@);
    }

    while i < n
        invariant
            i <= n,
            a@.len() == n,
            b@.len() == n,
            out@.len() == i as int,
            carry <= 1,
            limbs_to_nat(out@) + carry as nat * pow2((i * 32) as nat)
                == limbs_to_nat(a@.subrange(0, i as int))
                    + limbs_to_nat(b@.subrange(0, i as int)),
        decreases n - i,
    {
        let ai = a[i] as u64;
        let bi = b[i] as u64;
        let sum: u64 = ai + bi + carry;

        let digit: u32 = (sum % 4_294_967_296u64) as u32;
        let next_carry: u64 = sum / 4_294_967_296u64;

        proof {
            assert(digit as nat + next_carry as nat * limb_base()
                == ai as nat + bi as nat + carry as nat) by (nonlinear_arith)
                requires
                    digit == (sum % 4_294_967_296u64) as u32,
                    next_carry == sum / 4_294_967_296u64,
                    sum == ai + bi + carry,
            {}

            assert(next_carry <= 1) by (nonlinear_arith)
                requires
                    next_carry == sum / 4_294_967_296u64,
                    sum <= 2 * 4_294_967_296u64 - 1,
            {}

            let p = pow2((i * 32) as nat);
            let p_next = pow2(((i + 1) * 32) as nat);
            lemma_pow2_add(32, (i * 32) as nat);
            assert(32 + i * 32 == (i + 1) * 32);
            lemma_limb_base_is_pow2_32();
            assert(p_next == limb_base() * p) by (nonlinear_arith)
                requires
                    p_next == pow2(((i + 1) * 32) as nat),
                    p == pow2((i * 32) as nat),
                    pow2(((i + 1) * 32) as nat) == pow2(32nat) * pow2((i * 32) as nat),
                    pow2(32nat) == limb_base(),
            {}

            lemma_limbs_to_nat_push(out@, digit);
            lemma_limbs_to_nat_subrange_extend(a@, i as nat);
            lemma_limbs_to_nat_subrange_extend(b@, i as nat);

            assert(
                limbs_to_nat(out@) + (digit as nat) * p + (next_carry as nat) * p_next
                == limbs_to_nat(a@.subrange(0, i as int)) + (ai as nat) * p
                    + limbs_to_nat(b@.subrange(0, i as int)) + (bi as nat) * p
            ) by (nonlinear_arith)
                requires
                    limbs_to_nat(out@) + (carry as nat) * p
                        == limbs_to_nat(a@.subrange(0, i as int))
                            + limbs_to_nat(b@.subrange(0, i as int)),
                    (digit as nat) + (next_carry as nat) * limb_base()
                        == (ai as nat) + (bi as nat) + (carry as nat),
                    p_next == limb_base() * p,
            {}
        }

        out.push(digit);
        carry = next_carry;
        i = i + 1;
    }

    proof {
        lemma_limbs_to_nat_subrange_full(a@);
        lemma_limbs_to_nat_subrange_full(b@);
    }

    (out, carry as u32)
}

/// Unsigned borrow-chain subtraction of two n-limb arrays.
/// Returns (result, borrow_out) where borrow_out is 0 or 1.
pub fn sub_limbs(a: &Vec<u32>, b: &Vec<u32>, n: usize) -> (result: (Vec<u32>, u32))
    requires
        a@.len() == n,
        b@.len() == n,
    ensures
        result.0@.len() == n,
        limbs_to_nat(result.0@) + limbs_to_nat(b@)
            == limbs_to_nat(a@) + (result.1 as nat) * pow2((n * 32) as nat),
        result.1 <= 1,
{
    let mut out: Vec<u32> = Vec::new();
    let mut borrow: u64 = 0;
    let mut i: usize = 0;

    proof {
        lemma_limbs_to_nat_subrange_zero(a@);
        lemma_limbs_to_nat_subrange_zero(b@);
    }

    while i < n
        invariant
            i <= n,
            a@.len() == n,
            b@.len() == n,
            out@.len() == i as int,
            borrow <= 1,
            limbs_to_nat(out@) + limbs_to_nat(b@.subrange(0, i as int))
                == limbs_to_nat(a@.subrange(0, i as int))
                    + borrow as nat * pow2((i * 32) as nat),
        decreases n - i,
    {
        let ai = a[i] as u64;
        let bi = b[i] as u64;
        let need = bi + borrow;

        let (digit, next_borrow): (u32, u64) = if ai >= need {
            ((ai - need) as u32, 0u64)
        } else {
            ((ai + 4_294_967_296u64 - need) as u32, 1u64)
        };

        proof {
            if ai >= need {
                assert(next_borrow == 0u64);
                let diff = ai - need;
                assert(diff < 4_294_967_296u64);
                assert(digit as nat == diff as nat);
                assert(diff as nat + need as nat == ai as nat);
                assert(need as nat == bi as nat + borrow as nat);
            } else {
                assert(next_borrow == 1u64);
                let sum_with_base = ai + 4_294_967_296u64 - need;
                assert(sum_with_base < 4_294_967_296u64);
                assert(digit as nat == sum_with_base as nat);
                assert(digit as nat + need as nat == ai as nat + 4_294_967_296u64 as nat);
                assert(need as nat == bi as nat + borrow as nat);
            }

            assert(next_borrow <= 1);

            let p = pow2((i * 32) as nat);
            let p_next = pow2(((i + 1) * 32) as nat);
            lemma_pow2_add(32, (i * 32) as nat);
            assert(32 + i * 32 == (i + 1) * 32);
            lemma_limb_base_is_pow2_32();
            assert(p_next == limb_base() * p) by (nonlinear_arith)
                requires
                    p_next == pow2(((i + 1) * 32) as nat),
                    p == pow2((i * 32) as nat),
                    pow2(((i + 1) * 32) as nat) == pow2(32nat) * pow2((i * 32) as nat),
                    pow2(32nat) == limb_base(),
            {}

            lemma_limbs_to_nat_push(out@, digit);
            lemma_limbs_to_nat_subrange_extend(a@, i as nat);
            lemma_limbs_to_nat_subrange_extend(b@, i as nat);

            assert(
                limbs_to_nat(out@) + (digit as nat) * p
                    + limbs_to_nat(b@.subrange(0, i as int)) + (bi as nat) * p
                == limbs_to_nat(a@.subrange(0, i as int)) + (ai as nat) * p
                    + (next_borrow as nat) * p_next
            ) by (nonlinear_arith)
                requires
                    limbs_to_nat(out@) + limbs_to_nat(b@.subrange(0, i as int))
                        == limbs_to_nat(a@.subrange(0, i as int))
                            + (borrow as nat) * p,
                    (digit as nat) + (bi as nat) + (borrow as nat)
                        == (ai as nat) + (next_borrow as nat) * limb_base(),
                    p_next == limb_base() * p,
            {}
        }

        out.push(digit);
        borrow = next_borrow;
        i = i + 1;
    }

    proof {
        lemma_limbs_to_nat_subrange_full(a@);
        lemma_limbs_to_nat_subrange_full(b@);
    }

    (out, borrow as u32)
}

/// Check if all limbs are zero.
pub fn is_all_zero(limbs: &Vec<u32>) -> (result: bool)
    ensures result == (limbs_to_nat(limbs@) == 0),
{
    let mut i: usize = 0;
    let n = limbs.len();
    while i < n
        invariant
            i <= n,
            n == limbs@.len(),
            forall|j: int| 0 <= j < i as int ==> limbs@[j] == 0u32,
        decreases n - i,
    {
        if limbs[i] != 0 {
            proof {
                // We found a nonzero limb. Need: limbs_to_nat(limbs@) != 0.
                // Use subrange: ltn(limbs[..i+1]) = ltn(limbs[..i]) + limbs[i] * pow2(i*32)
                // Since limbs[i] > 0 and pow2(i*32) > 0, this term is positive.
                // And ltn(limbs[..i]) >= 0.
                // So ltn(limbs[..i+1]) > 0.
                // And ltn(limbs) >= ltn(limbs[..i+1]) (since remaining terms are non-negative).
                // Therefore ltn(limbs) > 0.
                lemma_limbs_to_nat_subrange_extend(limbs@, i as nat);
                lemma_pow2_positive((i * 32) as nat);
                let prefix_val = limbs_to_nat(limbs@.subrange(0, i as int));
                let extended_val = limbs_to_nat(limbs@.subrange(0, (i + 1) as int));
                assert(extended_val == prefix_val + limbs@[i as int] as nat * pow2((i * 32) as nat));
                assert(extended_val > 0) by (nonlinear_arith)
                    requires
                        extended_val == prefix_val + limbs@[i as int] as nat * pow2((i * 32) as nat),
                        limbs@[i as int] as nat > 0,
                        pow2((i * 32) as nat) > 0,
                        prefix_val >= 0,
                {}
                // Now show ltn(limbs) >= extended_val.
                // limbs_to_nat(limbs) = ltn(limbs[..n]) and extended_val = ltn(limbs[..i+1])
                // Since i+1 <= n, remaining terms are non-negative, so ltn(limbs) >= extended_val
                // Use upper bound on the subrange to show the relationship
                lemma_limbs_to_nat_subrange_full(limbs@);
                // Actually, we can show this more directly: add remaining terms.
                // For now, use a loop-like argument or just assert it with help.
                // ltn(limbs[..n]) >= ltn(limbs[..i+1]) because remaining elements only add.
                // This follows from: ltn(s.push(x)) = ltn(s) + x * pow2(len*32) >= ltn(s)
                // Applied repeatedly from i+1 to n.
                // Simplest: ltn(limbs) >= extended_val > 0
                // We can show ltn(limbs) >= ltn(limbs[..i+1]) by induction via subrange_extend:
                // Each extension adds a non-negative term.
                // For now, assert this fact about non-negative accumulation:
                lemma_limbs_to_nat_prefix_le_full(limbs@, (i + 1) as nat);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        // All limbs are 0
        assert(limbs@ =~= Seq::new(n as nat, |_j: int| 0u32));
        lemma_limbs_to_nat_all_zeros(n as nat);
    }
    true
}

/// Compare two n-limb unsigned arrays using subtraction.
/// Returns ordering of limbs_to_nat(a) vs limbs_to_nat(b).
pub fn cmp_limbs(a: &Vec<u32>, b: &Vec<u32>, n: usize) -> (result: std::cmp::Ordering)
    requires
        a@.len() == n,
        b@.len() == n,
    ensures
        result == std::cmp::Ordering::Less ==> limbs_to_nat(a@) < limbs_to_nat(b@),
        result == std::cmp::Ordering::Equal ==> limbs_to_nat(a@) == limbs_to_nat(b@),
        result == std::cmp::Ordering::Greater ==> limbs_to_nat(a@) > limbs_to_nat(b@),
{
    let result = sub_limbs(a, b, n);
    let diff = &result.0;
    let borrow = result.1;

    if borrow > 0 {
        proof {
            // sub_limbs: ltn(diff) + ltn(b) == ltn(a) + borrow * pow2(n*32)
            // borrow >= 1, ltn(diff) < pow2(n*32)
            lemma_limbs_to_nat_upper_bound(diff@);
            let ltn_d = limbs_to_nat(diff@);
            let ltn_a = limbs_to_nat(a@);
            let ltn_b = limbs_to_nat(b@);
            let p = pow2((n * 32) as nat);
            assert(ltn_d + ltn_b == ltn_a + borrow as nat * p);
            assert(ltn_d < p);
            assert(ltn_a < ltn_b) by (nonlinear_arith)
                requires ltn_d + ltn_b == ltn_a + borrow as nat * p,
                         borrow >= 1,
                         ltn_d < p;
        }
        std::cmp::Ordering::Less
    } else {
        proof {
            let ltn_d = limbs_to_nat(result.0@);
            let ltn_a = limbs_to_nat(a@);
            let ltn_b = limbs_to_nat(b@);
            assert(borrow == 0u32);
            assert(ltn_d + ltn_b == ltn_a + 0nat * pow2((n * 32) as nat));
            assert(ltn_d + ltn_b == ltn_a);
        }
        let is_zero = is_all_zero(diff);
        if is_zero {
            std::cmp::Ordering::Equal
        } else {
            std::cmp::Ordering::Greater
        }
    }
}

} // verus!
