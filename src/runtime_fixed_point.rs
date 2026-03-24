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

/// Create a zero-filled Vec of length n.
pub fn zero_vec(n: usize) -> (result: Vec<u32>)
    ensures
        result@.len() == n,
        limbs_to_nat(result@) == 0,
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            out@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> out@[j] == 0u32,
        decreases n - i,
    {
        out.push(0u32);
        i = i + 1;
    }
    proof {
        assert(out@ =~= Seq::new(n as nat, |_j: int| 0u32));
        lemma_limbs_to_nat_all_zeros(n as nat);
    }
    out
}

/// Multiply an n-limb array by a single u32 scalar, producing an (n+1)-limb result.
/// Ensures: limbs_to_nat(result) == limbs_to_nat(a) * scalar
pub fn mul_by_u32(a: &Vec<u32>, scalar: u32, n: usize) -> (result: Vec<u32>)
    requires
        a@.len() == n,
    ensures
        result@.len() == n + 1,
        limbs_to_nat(result@) == limbs_to_nat(a@) * (scalar as nat),
{
    let mut out: Vec<u32> = Vec::new();
    let mut carry: u64 = 0;
    let mut i: usize = 0;
    let s = scalar as u64;

    proof {
        lemma_limbs_to_nat_subrange_zero(a@);
        lemma_pow2_zero();
        // Establish invariant at i=0:
        // ltn(empty) + 0 * pow2(0*32) == ltn(a[..0]) * scalar
        // = 0 + 0 == 0 * scalar = 0
        assert(limbs_to_nat(a@.subrange(0, 0int)) == 0nat);
        assert(0nat * (scalar as nat) == 0nat);
        assert(pow2((0 * 32) as nat) == 1nat);
    }

    while i < n
        invariant
            i <= n,
            a@.len() == n,
            s == scalar as u64,
            out@.len() == i as int,
            carry <= 0xFFFF_FFFFu64,
            limbs_to_nat(out@) + carry as nat * pow2((i * 32) as nat)
                == limbs_to_nat(a@.subrange(0, i as int)) * (scalar as nat),
        decreases n - i,
    {
        let ai = a[i] as u64;
        proof {
            assert(ai <= 0xFFFF_FFFFu64);
            assert(s <= 0xFFFF_FFFFu64);
            assert(carry <= 0xFFFF_FFFFu64);
            assert(ai * s <= 0xFFFF_FFFE_0000_0001u64) by (nonlinear_arith)
                requires ai <= 0xFFFF_FFFFu64, s <= 0xFFFF_FFFFu64;
        }
        let product: u64 = ai * s + carry;

        let digit: u32 = (product % 4_294_967_296u64) as u32;
        let next_carry: u64 = product / 4_294_967_296u64;

        proof {
            // digit + next_carry * BASE == ai * s + carry
            assert(digit as nat + next_carry as nat * limb_base()
                == ai as nat * s as nat + carry as nat) by (nonlinear_arith)
                requires
                    digit == (product % 4_294_967_296u64) as u32,
                    next_carry == product / 4_294_967_296u64,
                    product == ai * s + carry,
            {}

            // next_carry < BASE
            assert(next_carry < 0x1_0000_0000u64) by (nonlinear_arith)
                requires
                    next_carry == product / 0x1_0000_0000u64,
                    product <= 0xFFFF_FFFE_0000_0001u64 + 0xFFFF_FFFFu64,
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

            // Update invariant:
            // ltn(out.push(digit)) + next_carry * p_next
            //   == ltn(a[..i+1]) * scalar
            //
            // ltn(a[..i+1]) = ltn(a[..i]) + a[i] * p
            // ltn(a[..i+1]) * scalar = ltn(a[..i]) * scalar + a[i] * scalar * p
            //
            // LHS = ltn(out) + digit * p + next_carry * p_next
            //     = ltn(out) + digit * p + next_carry * BASE * p
            // From invariant: ltn(out) + carry * p == ltn(a[..i]) * scalar
            // So ltn(out) = ltn(a[..i]) * scalar - carry * p
            // LHS = ltn(a[..i]) * scalar - carry * p + digit * p + next_carry * BASE * p
            //     = ltn(a[..i]) * scalar + (digit - carry + next_carry * BASE) * p
            //     = ltn(a[..i]) * scalar + (ai * s) * p  [since digit + next_carry*BASE == ai*s + carry]
            //     = ltn(a[..i]) * scalar + a[i] * scalar * p
            //     = ltn(a[..i+1]) * scalar  ✓

            assert(
                limbs_to_nat(out@) + (digit as nat) * p + (next_carry as nat) * p_next
                == limbs_to_nat(a@.subrange(0, (i + 1) as int)) * (scalar as nat)
            ) by (nonlinear_arith)
                requires
                    limbs_to_nat(out@) + carry as nat * p
                        == limbs_to_nat(a@.subrange(0, i as int)) * (scalar as nat),
                    (digit as nat) + (next_carry as nat) * limb_base()
                        == (ai as nat) * (s as nat) + carry as nat,
                    limbs_to_nat(a@.subrange(0, (i + 1) as int))
                        == limbs_to_nat(a@.subrange(0, i as int)) + a@[i as int] as nat * p,
                    ai == a@[i as int] as u64,
                    s == scalar as u64,
                    p_next == limb_base() * p,
            {}
        }

        out.push(digit);
        carry = next_carry;
        i = i + 1;
    }

    proof {
        lemma_limbs_to_nat_subrange_full(a@);
        // At loop exit: ltn(out@) + carry * pow2(n*32) == ltn(a@) * scalar
        // out@.len() == n
    }

    // Save the pre-push sequence for the proof
    let ghost pre_push = out@;
    out.push(carry as u32);

    proof {
        // out@ == pre_push.push(carry as u32)
        assert(out@ =~= pre_push.push(carry as u32));
        lemma_limbs_to_nat_push(pre_push, carry as u32);
        // ltn(out@) == ltn(pre_push) + (carry as u32) as nat * pow2(n*32)
        // From invariant: ltn(pre_push) + carry as nat * pow2(n*32) == ltn(a@) * scalar
        // So: ltn(pre_push) == ltn(a@) * scalar - carry as nat * pow2(n*32)
        // ltn(out@) = ltn(a@) * scalar - carry * pow2(n*32) + carry * pow2(n*32)
        //           = ltn(a@) * scalar
        assert((carry as u32) as nat == carry as nat);
    }

    out
}

/// Pad a Vec<u32> with zeros to reach target length.
pub fn pad_to_length(a: &Vec<u32>, target: usize) -> (result: Vec<u32>)
    requires target >= a@.len(),
    ensures
        result@.len() == target,
        limbs_to_nat(result@) == limbs_to_nat(a@),
{
    let mut out: Vec<u32> = Vec::new();
    let a_len = a.len();
    let mut i: usize = 0;
    while i < a_len
        invariant
            i <= a_len,
            a_len == a@.len(),
            out@.len() == i as int,
            out@ =~= a@.subrange(0, i as int),
        decreases a_len - i,
    {
        out.push(a[i]);
        i = i + 1;
    }

    proof {
        // After copying, out == a
        assert(out@ =~= a@);
    }

    while i < target
        invariant
            a_len <= i,
            i <= target,
            a_len == a@.len(),
            out@.len() == i as int,
            limbs_to_nat(out@) == limbs_to_nat(a@),
        decreases target - i,
    {
        proof {
            lemma_limbs_to_nat_push_zero(out@);
        }
        out.push(0u32);
        i = i + 1;
    }

    out
}

/// Shift a limb array left by `offset` positions (prepend `offset` zero limbs).
/// Equivalent to multiplying by pow2(offset * 32).
pub fn shift_left(a: &Vec<u32>, offset: usize) -> (result: Vec<u32>)
    ensures
        result@.len() == a@.len() + offset,
        limbs_to_nat(result@) == limbs_to_nat(a@) * pow2((offset * 32) as nat),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;

    // Prepend offset zeros
    while i < offset
        invariant
            i <= offset,
            out@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> out@[j] == 0u32,
        decreases offset - i,
    {
        out.push(0u32);
        i = i + 1;
    }

    proof {
        assert(out@ =~= Seq::new(offset as nat, |_j: int| 0u32));
    }

    // Append a's limbs
    let a_len = a.len();
    let mut k: usize = 0;
    while k < a_len
        invariant
            k <= a_len,
            a_len == a@.len(),
            out@.len() == offset + k,
            out@.subrange(0, offset as int) =~= Seq::new(offset as nat, |_j: int| 0u32),
            forall|j: int| 0 <= j < k as int ==> out@[offset as int + j] == a@[j],
        decreases a_len - k,
    {
        out.push(a[k]);
        k = k + 1;
    }

    proof {
        // out == zeros(offset) ++ a
        // limbs_to_nat(out) = limbs_to_nat(zeros(offset) ++ a)
        // By the append_zeros lemma in reverse:
        // zeros(offset) ++ a has ltn == ltn(zeros(offset)) + ltn(a) * pow2(offset*32)
        //                         == 0 + ltn(a) * pow2(offset*32)

        // Show out@ == Seq::new(offset, |_| 0u32).add(a@)
        let zeros = Seq::new(offset as nat, |_j: int| 0u32);
        assert(out@ =~= zeros.add(a@));

        // ltn(zeros.add(a)) == ltn(zeros) + ltn(a) * pow2(offset*32)
        // We need a lemma: ltn(prefix ++ suffix) == ltn(prefix) + ltn(suffix) * pow2(prefix.len() * 32)
        // This follows from append_zeros (for zero prefix) + push lemma
        // Actually: ltn(zeros ++ a) = ltn(a pushed onto zeros one by one)
        // For zero prefix: ltn(zeros) == 0, so ltn(zeros ++ a) == ltn(a) * pow2(offset*32)
        lemma_limbs_to_nat_all_zeros(offset as nat);
        lemma_limbs_to_nat_prepend_zeros(a@, offset as nat);
    }

    out
}

} // verus!
