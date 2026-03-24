use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_rational::Rational;
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
/// Compare two n-limb unsigned arrays using subtraction.
/// Returns -1 if a < b, 0 if a == b, 1 if a > b.
pub fn cmp_limbs(a: &Vec<u32>, b: &Vec<u32>, n: usize) -> (result: i8)
    requires
        a@.len() == n,
        b@.len() == n,
    ensures
        result < 0i8 ==> limbs_to_nat(a@) < limbs_to_nat(b@),
        result == 0i8 ==> limbs_to_nat(a@) == limbs_to_nat(b@),
        result > 0i8 ==> limbs_to_nat(a@) > limbs_to_nat(b@),
        -1i8 <= result <= 1i8,
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
        -1i8
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
            0i8
        } else {
            1i8
        }
    }
}

/// Create a zero-filled Vec of length n.
pub fn zero_vec(n: usize) -> (result: Vec<u32>)
    ensures
        result@.len() == n,
        result@ =~= Seq::new(n as nat, |_i: int| 0u32),
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

/// Schoolbook multiplication: a * b -> 2n-limb result. O(n^2).
/// Used as the base case for Karatsuba.
pub fn mul_schoolbook(a: &Vec<u32>, b: &Vec<u32>, n: usize) -> (result: Vec<u32>)
    requires
        a@.len() == n,
        b@.len() == n,
        n <= 0x7FFF_FFFF, // ensure 2*n doesn't overflow usize
    ensures
        result@.len() == 2 * n,
        limbs_to_nat(result@) == limbs_to_nat(a@) * limbs_to_nat(b@),
{
    // Strategy: accumulate partial products.
    // result = sum over i: a * b[i] * BASE^i
    //        = a * (b[0] + b[1]*BASE + ... + b[n-1]*BASE^(n-1))
    //        = a * b

    let nn: usize = 2 * n; // precompute, overflow checked by precondition
    let mut acc = zero_vec(nn);
    let mut i: usize = 0;

    proof {
        lemma_limbs_to_nat_subrange_zero(b@);
        // At entry: ltn(acc) == 0 == ltn(a) * 0 == ltn(a) * ltn(b[..0])
        assert(limbs_to_nat(b@.subrange(0, 0int)) == 0nat);
        assert(limbs_to_nat(a@) * 0nat == 0nat) by (nonlinear_arith);
    }

    while i < n
        invariant
            i <= n,
            a@.len() == n,
            b@.len() == n,
            nn == 2 * n,
            acc@.len() == nn,
            limbs_to_nat(acc@) == limbs_to_nat(a@) * limbs_to_nat(b@.subrange(0, i as int)),
        decreases n - i,
    {
        // Compute partial product: a * b[i]
        let partial = mul_by_u32(a, b[i], n);
        // partial has n+1 limbs, ltn(partial) == ltn(a) * b[i]

        // Shift left by i positions: a * b[i] * BASE^i
        let shifted = shift_left(&partial, i);
        // shifted has n+1+i limbs, ltn(shifted) == ltn(a) * b[i] * pow2(i*32)

        // Add to accumulator
        // Need: shifted.len() <= acc.len()
        // shifted.len() == n + 1 + i <= n + 1 + (n-1) = 2n. Since i < n.
        proof {
            assert(shifted@.len() == n + 1 + i);
            assert(n + 1 + i <= nn) by (nonlinear_arith)
                requires i < n, nn == 2 * n;
        }
        let padded_shifted = pad_to_length(&shifted, nn);
        let (new_acc, carry) = add_limbs(&acc, &padded_shifted, nn);

        proof {
            // Update invariant:
            // ltn(new_acc) + carry * pow2(2n*32) == ltn(acc) + ltn(padded_shifted)
            //   == ltn(a) * ltn(b[..i]) + ltn(a) * b[i] * pow2(i*32)
            //   == ltn(a) * (ltn(b[..i]) + b[i] * pow2(i*32))
            //   == ltn(a) * ltn(b[..i+1])

            lemma_limbs_to_nat_subrange_extend(b@, i as nat);
            // ltn(b[..i+1]) == ltn(b[..i]) + b[i] * pow2(i*32)

            // ltn(padded_shifted) == ltn(shifted) == ltn(partial) * pow2(i*32)
            //   == ltn(a) * b[i] * pow2(i*32)

            assert(limbs_to_nat(padded_shifted@) == limbs_to_nat(a@) * (b@[i as int] as nat) * pow2((i * 32) as nat)) by (nonlinear_arith)
                requires
                    limbs_to_nat(padded_shifted@) == limbs_to_nat(shifted@),
                    limbs_to_nat(shifted@) == limbs_to_nat(partial@) * pow2((i * 32) as nat),
                    limbs_to_nat(partial@) == limbs_to_nat(a@) * (b@[i as int] as nat),
            {}

            // new_acc_value == ltn(a) * ltn(b[..i]) + ltn(a) * b[i] * pow2(i*32)
            //               == ltn(a) * (ltn(b[..i]) + b[i] * pow2(i*32))
            //               == ltn(a) * ltn(b[..i+1])

            assert(limbs_to_nat(a@) * limbs_to_nat(b@.subrange(0, i as int))
                + limbs_to_nat(a@) * (b@[i as int] as nat) * pow2((i * 32) as nat)
                == limbs_to_nat(a@) * limbs_to_nat(b@.subrange(0, (i + 1) as int))) by (nonlinear_arith)
                requires
                    limbs_to_nat(b@.subrange(0, (i + 1) as int))
                        == limbs_to_nat(b@.subrange(0, i as int)) + b@[i as int] as nat * pow2((i * 32) as nat),
            {}

            // carry must be 0: the sum fits in 2n limbs
            // ltn(a) < pow2(n*32), ltn(b[..i+1]) <= ltn(b) < pow2(n*32)
            // product < pow2(n*32) * pow2(n*32) = pow2(2n*32)
            // So new_acc == product < pow2(2n*32), meaning carry == 0
            lemma_limbs_to_nat_upper_bound(a@);
            lemma_limbs_to_nat_upper_bound(b@);
            lemma_limbs_to_nat_prefix_le_full(b@, (i + 1) as nat);
            lemma_pow2_double((n * 32) as nat);
            let bound = pow2((n * 32) as nat);
            assert(limbs_to_nat(a@) * limbs_to_nat(b@.subrange(0, (i + 1) as int))
                < bound * bound) by (nonlinear_arith)
                requires
                    limbs_to_nat(a@) < bound,
                    limbs_to_nat(b@.subrange(0, (i + 1) as int)) <= limbs_to_nat(b@),
                    limbs_to_nat(b@) < bound,
                    bound > 0,
            {}
            lemma_pow2_double((n * 32) as nat);
            assert(2 * (n * 32) == nn * 32) by (nonlinear_arith)
                requires nn == 2 * n;
            assert(bound * bound == pow2((nn * 32) as nat));

            // Chain: add_limbs postcondition + invariant + partial product
            assert(limbs_to_nat(new_acc@) + (carry as nat) * pow2((nn * 32) as nat)
                == limbs_to_nat(acc@) + limbs_to_nat(padded_shifted@));

            assert(limbs_to_nat(acc@) + limbs_to_nat(padded_shifted@)
                == limbs_to_nat(a@) * limbs_to_nat(b@.subrange(0, (i + 1) as int)));

            // So the value < pow2(nn*32), carry must be 0
            assert(limbs_to_nat(new_acc@) + (carry as nat) * pow2((nn * 32) as nat)
                == limbs_to_nat(a@) * limbs_to_nat(b@.subrange(0, (i + 1) as int)));
            assert(limbs_to_nat(a@) * limbs_to_nat(b@.subrange(0, (i + 1) as int))
                < pow2((nn * 32) as nat));
            lemma_limbs_to_nat_upper_bound(new_acc@);
            assert(carry == 0) by (nonlinear_arith)
                requires
                    limbs_to_nat(new_acc@) + (carry as nat) * pow2((nn * 32) as nat)
                        < pow2((nn * 32) as nat),
                    limbs_to_nat(new_acc@) < pow2((nn * 32) as nat),
                    carry <= 1,
            {}

            // Now chain: carry==0, so ltn(new_acc) == ltn(acc) + ltn(padded_shifted)
            assert(limbs_to_nat(new_acc@) == limbs_to_nat(acc@) + limbs_to_nat(padded_shifted@)) by (nonlinear_arith)
                requires
                    limbs_to_nat(new_acc@) + (carry as nat) * pow2((nn * 32) as nat)
                        == limbs_to_nat(acc@) + limbs_to_nat(padded_shifted@),
                    carry == 0u32,
            {}

            // And ltn(acc) + ltn(padded) == ltn(a) * ltn(b[..i+1])
            assert(limbs_to_nat(acc@) + limbs_to_nat(padded_shifted@)
                == limbs_to_nat(a@) * limbs_to_nat(b@.subrange(0, (i + 1) as int)));

            assert(limbs_to_nat(new_acc@) == limbs_to_nat(a@) * limbs_to_nat(b@.subrange(0, (i + 1) as int)));
        }

        acc = new_acc;
        i = i + 1;
    }

    proof {
        lemma_limbs_to_nat_subrange_full(b@);
    }

    acc
}

/// Extract a subrange of a Vec as a new Vec.
pub fn slice_vec(a: &Vec<u32>, start: usize, end: usize) -> (result: Vec<u32>)
    requires start <= end, end <= a@.len(),
    ensures result@ == a@.subrange(start as int, end as int),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = start;
    while i < end
        invariant
            start <= i, i <= end, end <= a@.len(),
            out@.len() == i - start,
            out@ =~= a@.subrange(start as int, i as int),
        decreases end - i,
    {
        out.push(a[i]);
        i = i + 1;
    }
    out
}

/// Karatsuba multiplication: a * b -> 2n-limb result. O(n^1.585).
/// Falls back to schoolbook for small n.
pub fn mul_karatsuba(a: &Vec<u32>, b: &Vec<u32>, n: usize) -> (result: Vec<u32>)
    requires
        a@.len() == n,
        b@.len() == n,
        n > 0,
        n <= 0x1FFF_FFFF,
    ensures
        result@.len() == 2 * n,
        limbs_to_nat(result@) == limbs_to_nat(a@) * limbs_to_nat(b@),
    decreases n,
{
    if n <= 4 {
        return mul_schoolbook(a, b, n);
    }

    let half: usize = n / 2;
    let upper: usize = n - half;

    // Split inputs
    let a_lo = slice_vec(a, 0, half);
    let a_hi = slice_vec(a, half, n);
    let b_lo = slice_vec(b, 0, half);
    let b_hi = slice_vec(b, half, n);

    // Pad a_lo, b_lo to `upper` limbs (they have `half` limbs, upper >= half)
    let a_lo_p = pad_to_length(&a_lo, upper);
    let b_lo_p = pad_to_length(&b_lo, upper);

    // z0 = a_lo * b_lo
    let z0 = mul_karatsuba(&a_lo_p, &b_lo_p, upper);

    // z2 = a_hi * b_hi
    let z2 = mul_karatsuba(&a_hi, &b_hi, upper);

    // Sums for z1: (a_lo + a_hi), (b_lo + b_hi)
    // These may have a carry, making them upper+1 limbs
    let (a_sum_body, a_carry) = add_limbs(&a_lo_p, &a_hi, upper);
    let (b_sum_body, b_carry) = add_limbs(&b_lo_p, &b_hi, upper);

    // Build (upper+1)-limb sums by copying body + pushing carry
    let ghost a_sum_pre = a_sum_body@;
    let mut a_sum = a_sum_body;
    a_sum.push(a_carry);
    let ghost b_sum_pre = b_sum_body@;
    let mut b_sum = b_sum_body;
    b_sum.push(b_carry);

    proof {
        assert(a_sum@ =~= a_sum_pre.push(a_carry));
        lemma_limbs_to_nat_push(a_sum_pre, a_carry);
        // ltn(a_sum) == ltn(a_sum_pre) + a_carry * pow2(upper*32)
        //            == ltn(a_lo_p) + ltn(a_hi) == ltn(a_lo) + ltn(a_hi)

        assert(b_sum@ =~= b_sum_pre.push(b_carry));
        lemma_limbs_to_nat_push(b_sum_pre, b_carry);
    }

    // z1_full = (a_lo + a_hi) * (b_lo + b_hi)
    let z1_full = mul_karatsuba(&a_sum, &b_sum, upper + 1);

    // z1 = z1_full - z0 - z2
    let tgt = 2 * (upper + 1);
    let z0_p = pad_to_length(&z0, tgt);
    let z2_p = pad_to_length(&z2, tgt);
    let (z1_tmp, bw1) = sub_limbs(&z1_full, &z0_p, tgt);
    let (z1, bw2) = sub_limbs(&z1_tmp, &z2_p, tgt);

    // Combine: result = z0 + z1 * B^half + z2 * B^(2*half)
    let z1_shifted = shift_left(&z1, half);
    let z2_shifted = shift_left(&z2, 2 * half);

    let rlen = 2 * n;
    let z0_f = pad_to_length(&z0, rlen);
    let z1_f = pad_to_length(&z1_shifted, rlen);
    let z2_f = pad_to_length(&z2_shifted, rlen);

    let (s1, c1) = add_limbs(&z0_f, &z1_f, rlen);
    let (s2, c2) = add_limbs(&s1, &z2_f, rlen);

    proof {
        // ── Connect everything to the Karatsuba identity ──

        let la = limbs_to_nat(a@) as int;
        let lb = limbs_to_nat(b@) as int;
        let la_lo = limbs_to_nat(a_lo@) as int;
        let la_hi = limbs_to_nat(a_hi@) as int;
        let lb_lo = limbs_to_nat(b_lo@) as int;
        let lb_hi = limbs_to_nat(b_hi@) as int;
        let B = pow2((half * 32) as nat) as int;

        // 1. Split correctness: a == a_hi * B + a_lo, b == b_hi * B + b_lo
        lemma_limbs_to_nat_split(a@, half as nat);
        lemma_limbs_to_nat_split(b@, half as nat);
        assert(la == la_lo + la_hi * B);
        assert(lb == lb_lo + lb_hi * B);
        // Rewrite as a_hi * B + a_lo form
        assert(la == la_hi * B + la_lo) by (nonlinear_arith)
            requires la == la_lo + la_hi * B;
        assert(lb == lb_hi * B + lb_lo) by (nonlinear_arith)
            requires lb == lb_lo + lb_hi * B;

        // 2. z0, z2, z1_full values
        let vz0 = limbs_to_nat(z0@) as int;
        let vz2 = limbs_to_nat(z2@) as int;
        assert(vz0 == la_lo * lb_lo);
        assert(vz2 == la_hi * lb_hi);

        let va_sum = limbs_to_nat(a_sum@) as int;
        let vb_sum = limbs_to_nat(b_sum@) as int;
        assert(va_sum == la_lo + la_hi);
        assert(vb_sum == lb_lo + lb_hi);

        let vz1_full = limbs_to_nat(z1_full@) as int;
        assert(vz1_full == va_sum * vb_sum);
        assert(vz1_full == (la_lo + la_hi) * (lb_lo + lb_hi)) by (nonlinear_arith)
            requires vz1_full == va_sum * vb_sum, va_sum == la_lo + la_hi, vb_sum == lb_lo + lb_hi;

        // 3. Subtractions for z1 don't underflow + 4. Final combines don't overflow
        // Use extracted helper lemmas for clean proof

        // 3. z1_full >= z0 + z2 (cross terms non-negative for nat)
        // (la_lo+la_hi)*(lb_lo+lb_hi) >= la_lo*lb_lo + la_hi*lb_hi
        // because expanding gives + la_lo*lb_hi + la_hi*lb_lo which are >= 0
        let nz0 = limbs_to_nat(z0@);
        let nz2 = limbs_to_nat(z2@);
        let nz1f = limbs_to_nat(z1_full@);
        let nalo = limbs_to_nat(a_lo@);
        let nahi = limbs_to_nat(a_hi@);
        let nblo = limbs_to_nat(b_lo@);
        let nbhi = limbs_to_nat(b_hi@);
        assert(nz0 == nalo * nblo);
        assert(nz2 == nahi * nbhi);
        assert(nz1f == (nalo + nahi) * (nblo + nbhi)) by (nonlinear_arith)
            requires
                nz1f == limbs_to_nat(a_sum@) * limbs_to_nat(b_sum@),
                limbs_to_nat(a_sum@) == nalo + nahi,
                limbs_to_nat(b_sum@) == nblo + nbhi,
        {}
        // (a+b)(c+d) = ac + ad + bc + bd >= ac + bd = z0 + z2
        lemma_mul_distribute(nalo as int, nahi as int, (nblo + nbhi) as int);
        lemma_mul_distribute(nblo as int, nbhi as int, nalo as int);
        lemma_mul_distribute(nblo as int, nbhi as int, nahi as int);
        assert(nz1f >= nz0 + nz2);

        // Connect padded values and sub_limbs postconditions
        assert(limbs_to_nat(z0_p@) == nz0);
        assert(limbs_to_nat(z2_p@) == nz2);
        assert(limbs_to_nat(z1_tmp@) + nz0 == nz1f + (bw1 as nat) * pow2((tgt * 32) as nat));
        assert(limbs_to_nat(z1@) + nz2 == limbs_to_nat(z1_tmp@) + (bw2 as nat) * pow2((tgt * 32) as nat));

        lemma_limbs_to_nat_upper_bound(a@);
        lemma_limbs_to_nat_upper_bound(b@);
        lemma_limbs_to_nat_upper_bound(z1_tmp@);
        lemma_limbs_to_nat_upper_bound(z1@);

        lemma_karatsuba_no_overflow(
            limbs_to_nat(a@), limbs_to_nat(b@), pow2((n * 32) as nat),
            nz0, nz2, nz1f,
            limbs_to_nat(z1_tmp@), bw1 as nat,
            limbs_to_nat(z1@), bw2 as nat,
            pow2((tgt * 32) as nat),
        );

        // 4. Karatsuba identity in nat form for combine
        lemma_karatsuba_identity(nalo as int, nahi as int, nblo as int, nbhi as int, pow2((half * 32) as nat) as int);
        // Gives: (nahi*B + nalo) * (nbhi*B + nblo) == z0 + z1*B + z2*B*B (in int)
        // where z0=nalo*nblo, z2=nahi*nbhi, z1 = (nalo+nahi)*(nblo+nbhi) - z0 - z2

        // la = nahi*B + nalo, lb = nbhi*B + nblo (from split)
        lemma_limbs_to_nat_split(a@, half as nat);
        lemma_limbs_to_nat_split(b@, half as nat);
        let nB = pow2((half * 32) as nat);
        assert(limbs_to_nat(a@) == nalo + nahi * nB);
        assert(limbs_to_nat(b@) == nblo + nbhi * nB);

        // Combine
        assert(limbs_to_nat(z0_f@) == nz0);
        assert(limbs_to_nat(z1_f@) == limbs_to_nat(z1_shifted@));
        assert(limbs_to_nat(z2_f@) == limbs_to_nat(z2_shifted@));

        lemma_pow2_double((half * 32) as nat);
        assert(2 * (half * 32) == 2 * half * 32) by (nonlinear_arith);
        lemma_pow2_double((n * 32) as nat);
        assert(2 * (n * 32) == 2 * n * 32) by (nonlinear_arith);
        assert(rlen == 2 * n);

        lemma_limbs_to_nat_upper_bound(s1@);
        lemma_limbs_to_nat_upper_bound(s2@);

        lemma_karatsuba_combine(
            limbs_to_nat(a@), limbs_to_nat(b@), n as nat, half as nat,
            nz0, nz2, limbs_to_nat(z1@),
            limbs_to_nat(z1_shifted@), limbs_to_nat(z2_shifted@),
            limbs_to_nat(s1@), c1 as nat,
            limbs_to_nat(s2@), c2 as nat,
            pow2((rlen * 32) as nat),
        );
    }

    s2
}

// ── RuntimeFixedPointInterval ──────────────────────────

/// Exec-level interval backed by RuntimeFixedPoint endpoints + ghost exact Rational.
/// The ghost exact tracks the true mathematical value. lo and hi are exec-level bounds.
pub struct RuntimeFixedPointInterval {
    pub lo: RuntimeFixedPoint,
    pub hi: RuntimeFixedPoint,
    pub exact: Ghost<Rational>,
}

impl RuntimeFixedPointInterval {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.lo.wf_spec()
        &&& self.hi.wf_spec()
        &&& self.lo@.same_format(self.hi@)
        &&& self.lo@.view().le_spec(self.exact@)
        &&& self.exact@.le_spec(self.hi@.view())
    }

    /// The ghost exact Rational value.
    pub open spec fn exact_view(&self) -> Rational {
        self.exact@
    }

    /// Format accessors.
    pub open spec fn n_spec(&self) -> nat { self.lo@.n }
    pub open spec fn frac_spec(&self) -> nat { self.lo@.frac }

    /// Construct a point interval at zero.
    pub fn zero_interval(n: usize, frac: usize) -> (result: Self)
        requires n > 0, frac <= n * 32,
        ensures result.wf_spec(),
    {
        let ghost fp_model = FixedPoint {
            limbs: Seq::new(n as nat, |_i: int| 0u32),
            sign: false,
            n: n as nat,
            frac: frac as nat,
        };

        let lo_limbs = zero_vec(n);
        let lo = RuntimeFixedPoint {
            limbs: lo_limbs, sign: false,
            n: Ghost(n as nat), frac: Ghost(frac as nat),
            model: Ghost(fp_model),
        };

        let hi_limbs = zero_vec(n);
        let hi = RuntimeFixedPoint {
            limbs: hi_limbs, sign: false,
            n: Ghost(n as nat), frac: Ghost(frac as nat),
            model: Ghost(fp_model),
        };

        let ghost exact = fp_model.view();

        proof {
            lemma_limbs_to_nat_all_zeros(n as nat);
            assert(fp_model.wf_spec());
            lemma_pow2_positive(frac as nat);
            Rational::lemma_eqv_reflexive(fp_model.view());
            Rational::lemma_le_iff_lt_or_eqv(fp_model.view(), fp_model.view());
        }

        RuntimeFixedPointInterval { lo, hi, exact: Ghost(exact) }
    }

    /// Deep copy.
    pub fn copy_interval(&self) -> (result: Self)
        requires self.wf_spec(),
        ensures result.wf_spec(), result.exact@ == self.exact@,
    {
        // Copy lo limbs
        let mut lo_limbs: Vec<u32> = Vec::new();
        let lo_n = self.lo.limbs.len();
        let mut i: usize = 0;
        while i < lo_n
            invariant
                i <= lo_n, lo_n == self.lo.limbs@.len(),
                lo_limbs@.len() == i,
                lo_limbs@ =~= self.lo.limbs@.subrange(0, i as int),
            decreases lo_n - i,
        {
            lo_limbs.push(self.lo.limbs[i]);
            i = i + 1;
        }

        proof { assert(lo_limbs@ =~= self.lo.limbs@); }

        let lo = RuntimeFixedPoint {
            limbs: lo_limbs, sign: self.lo.sign,
            n: Ghost(self.lo.n@), frac: Ghost(self.lo.frac@),
            model: Ghost(self.lo@),
        };

        let mut hi_limbs: Vec<u32> = Vec::new();
        let hi_n = self.hi.limbs.len();
        let mut j: usize = 0;
        while j < hi_n
            invariant
                j <= hi_n, hi_n == self.hi.limbs@.len(),
                hi_limbs@.len() == j,
                hi_limbs@ =~= self.hi.limbs@.subrange(0, j as int),
            decreases hi_n - j,
        {
            hi_limbs.push(self.hi.limbs[j]);
            j = j + 1;
        }

        proof { assert(hi_limbs@ =~= self.hi.limbs@); }

        let hi = RuntimeFixedPoint {
            limbs: hi_limbs, sign: self.hi.sign,
            n: Ghost(self.hi.n@), frac: Ghost(self.hi.frac@),
            model: Ghost(self.hi@),
        };

        RuntimeFixedPointInterval { lo, hi, exact: Ghost(self.exact@) }
    }

    /// Negation: swap lo/hi, negate both, exact = -exact.
    pub fn neg_interval(&self) -> (result: Self)
        requires self.wf_spec(),
        ensures
            result.wf_spec(),
            result.exact@ == self.exact@.neg_spec(),
    {
        // -[lo, hi] = [-hi, -lo]
        // Negate hi (becomes new lo) and lo (becomes new hi)
        let n = self.lo.limbs.len();

        // Copy hi's limbs for new lo (negated)
        let mut new_lo_limbs: Vec<u32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n, n == self.hi.limbs@.len(),
                new_lo_limbs@.len() == i,
                new_lo_limbs@ =~= self.hi.limbs@.subrange(0, i as int),
            decreases n - i,
        {
            new_lo_limbs.push(self.hi.limbs[i]);
            i = i + 1;
        }

        proof { assert(new_lo_limbs@ =~= self.hi.limbs@); }
        let hi_mag_zero = is_all_zero(&new_lo_limbs);
        let new_lo = RuntimeFixedPoint {
            limbs: new_lo_limbs,
            sign: if hi_mag_zero { false } else { !self.hi.sign },
            n: Ghost(self.hi.n@),
            frac: Ghost(self.hi.frac@),
            model: Ghost(self.hi@.neg_spec()),
        };

        // Copy lo's limbs for new hi (negated)
        let mut new_hi_limbs: Vec<u32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n, n == self.lo.limbs@.len(),
                new_hi_limbs@.len() == j,
                new_hi_limbs@ =~= self.lo.limbs@.subrange(0, j as int),
            decreases n - j,
        {
            new_hi_limbs.push(self.lo.limbs[j]);
            j = j + 1;
        }

        proof { assert(new_hi_limbs@ =~= self.lo.limbs@); }
        let lo_mag_zero = is_all_zero(&new_hi_limbs);
        let new_hi = RuntimeFixedPoint {
            limbs: new_hi_limbs,
            sign: if lo_mag_zero { false } else { !self.lo.sign },
            n: Ghost(self.lo.n@),
            frac: Ghost(self.lo.frac@),
            model: Ghost(self.lo@.neg_spec()),
        };

        let ghost new_exact = self.exact@.neg_spec();

        proof {
            FixedPoint::lemma_neg_wf(self.hi@);
            FixedPoint::lemma_neg_wf(self.lo@);
            FixedPoint::lemma_neg_view(self.hi@);
            FixedPoint::lemma_neg_view(self.lo@);

            // Need: -hi.view() <= -exact <= -lo.view()
            Rational::lemma_neg_reverses_le(self.exact@, self.hi@.view());
            Rational::lemma_neg_reverses_le(self.lo@.view(), self.exact@);

            // Connect through eqv
            Rational::lemma_eqv_implies_le(self.hi@.neg_spec().view(), self.hi@.view().neg_spec());
            Rational::lemma_le_transitive(
                self.hi@.neg_spec().view(),
                self.hi@.view().neg_spec(),
                new_exact,
            );
            Rational::lemma_eqv_implies_le(self.lo@.neg_spec().view(), self.lo@.view().neg_spec());
            Rational::lemma_eqv_symmetric(self.lo@.neg_spec().view(), self.lo@.view().neg_spec());
            Rational::lemma_eqv_implies_le(self.lo@.view().neg_spec(), self.lo@.neg_spec().view());
            Rational::lemma_le_transitive(
                new_exact,
                self.lo@.view().neg_spec(),
                self.lo@.neg_spec().view(),
            );
        }

        RuntimeFixedPointInterval { lo: new_lo, hi: new_hi, exact: Ghost(new_exact) }
    }

    /// Signed addition of two RuntimeFixedPoints with same format.
    /// Implements: same sign → add magnitudes, different sign → compare then subtract.
    pub fn add_rfp(a: &RuntimeFixedPoint, b: &RuntimeFixedPoint) -> (result: RuntimeFixedPoint)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a@.same_format(b@),
            FixedPoint::add_no_overflow(a@, b@),
        ensures
            result.wf_spec(),
            result@.n == a@.n,
            result@.frac == a@.frac,
            result@ == a@.add_spec(b@),
    {
        let n = a.limbs.len();

        // Helper: build a RuntimeFixedPoint from exec limbs + sign, constructing
        // the model from the exec data (avoids limb uniqueness issues).
        // Then prove the view matches the spec-level add result.

        if a.sign == b.sign {
            // Same sign: add magnitudes, keep sign
            let (sum_limbs, carry) = add_limbs(&a.limbs, &b.limbs, n);
            let result_sign = if carry == 0 && is_all_zero(&sum_limbs) { false } else { a.sign };

            let ghost model = FixedPoint { limbs: sum_limbs@, sign: result_sign, n: a.n@, frac: a.frac@ };
            proof {
                // Prove carry == 0 from add_no_overflow:
                // Same sign: magnitude = ltn(a) + ltn(b) < pow2(n*32) (from overflow cond)
                // add_limbs: ltn(sum) + carry * pow2(n*32) == ltn(a) + ltn(b)
                // Since ltn(a) + ltn(b) < pow2(n*32) and ltn(sum) >= 0: carry == 0
                // Derive: ltn(a) + ltn(b) < pow2(n*32) from add_no_overflow
                // When same sign, signed sum magnitude == ltn(a) + ltn(b)
                let la = limbs_to_nat(a@.limbs);
                let lb = limbs_to_nat(b@.limbs);
                let p = pow2((a.n@ * 32) as nat);
                assert(la + lb < p) by {
                    // From add_no_overflow: the magnitude of signed sum < pow2(n*32)
                    // For same sign: magnitude = ltn(a) + ltn(b)
                    let sv_a = a@.signed_value();
                    let sv_b = b@.signed_value();
                    if a.sign {
                        assert(sv_a == -(la as int));
                        assert(sv_b == -(lb as int));
                        assert(sv_a + sv_b == -((la + lb) as int));
                    } else {
                        assert(sv_a == la as int);
                        assert(sv_b == lb as int);
                    }
                }

                lemma_limbs_to_nat_upper_bound(sum_limbs@);
                assert(carry == 0) by (nonlinear_arith)
                    requires
                        limbs_to_nat(sum_limbs@) + (carry as nat) * p == la + lb,
                        la + lb < p,
                        limbs_to_nat(sum_limbs@) < p,
                        carry <= 1,
                {}
                assert(model.wf_spec());

                // Uniqueness: model == a@.add_spec(b@)
                // add_spec result has limbs = nat_to_limbs(magnitude, n)
                // For same sign: magnitude = la + lb = ltn(sum_limbs@)
                // By uniqueness: sum_limbs@ == nat_to_limbs(la + lb, n)
                // Connect exec limbs to spec model limbs (from wf_spec)
                assert(a.limbs@ == a@.limbs);
                assert(b.limbs@ == b@.limbs);
                assert((carry as nat) * p == 0nat) by (nonlinear_arith) requires carry == 0u32;
                assert(limbs_to_nat(sum_limbs@) == la + lb);
                lemma_limbs_nat_to_limbs_identity(sum_limbs@, a.n@);
                assert(sum_limbs@ =~= nat_to_limbs(la + lb, a.n@));
            }

            RuntimeFixedPoint {
                limbs: sum_limbs, sign: result_sign,
                n: Ghost(a.n@), frac: Ghost(a.frac@),
                model: Ghost(model),
            }
        } else {
            // Different sign: compare magnitudes, subtract smaller from larger
            let ord = cmp_limbs(&a.limbs, &b.limbs, n);
            if ord == 0i8 {
                // |a| == |b| with opposite signs: result is zero
                let z = zero_vec(n);
                let ghost model = FixedPoint { limbs: z@, sign: false, n: a.n@, frac: a.frac@ };
                proof {
                    assert(model.wf_spec());
                    // Uniqueness: add_spec magnitude = |sv_a + sv_b| = |±la ∓ la| = 0
                    assert(a.limbs@ == a@.limbs);
                    assert(b.limbs@ == b@.limbs);
                    let la = limbs_to_nat(a@.limbs);
                    let lb = limbs_to_nat(b@.limbs);
                    assert(la == lb);
                    // nat_to_limbs(0, n) == z@ (all zeros)
                    lemma_nat_to_limbs_zero(a.n@);
                    lemma_limbs_to_nat_all_zeros(a.n@);
                }
                RuntimeFixedPoint {
                    limbs: z, sign: false,
                    n: Ghost(a.n@), frac: Ghost(a.frac@),
                    model: Ghost(model),
                }
            } else if ord > 0i8 {
                // |a| > |b|: magnitude = |a| - |b|
                let (diff, borrow) = sub_limbs(&a.limbs, &b.limbs, n);
                let result_sign = if is_all_zero(&diff) { false } else { a.sign };
                let ghost model = FixedPoint { limbs: diff@, sign: result_sign, n: a.n@, frac: a.frac@ };
                proof {
                    assert(model.wf_spec());
                    assert(a.limbs@ == a@.limbs);
                    assert(b.limbs@ == b@.limbs);
                    let la = limbs_to_nat(a@.limbs);
                    let lb = limbs_to_nat(b@.limbs);
                    // borrow == 0 since |a| > |b|
                    lemma_limbs_to_nat_upper_bound(diff@);
                    assert(borrow == 0) by (nonlinear_arith)
                        requires
                            limbs_to_nat(diff@) + lb == la + (borrow as nat) * pow2((n * 32) as nat),
                            la > lb,
                            limbs_to_nat(diff@) < pow2((n * 32) as nat),
                            borrow <= 1,
                    {}
                    assert((borrow as nat) * pow2((a.n@ * 32) as nat) == 0nat) by (nonlinear_arith) requires borrow == 0u32;
                    assert(limbs_to_nat(diff@) == la - lb);
                    lemma_limbs_nat_to_limbs_identity(diff@, a.n@);
                }
                RuntimeFixedPoint {
                    limbs: diff, sign: result_sign,
                    n: Ghost(a.n@), frac: Ghost(a.frac@),
                    model: Ghost(model),
                }
            } else {
                // |a| < |b|: magnitude = |b| - |a|
                let (diff, borrow) = sub_limbs(&b.limbs, &a.limbs, n);
                let result_sign = if is_all_zero(&diff) { false } else { b.sign };
                let ghost model = FixedPoint { limbs: diff@, sign: result_sign, n: a.n@, frac: a.frac@ };
                proof {
                    assert(model.wf_spec());
                    assert(a.limbs@ == a@.limbs);
                    assert(b.limbs@ == b@.limbs);
                    let la = limbs_to_nat(a@.limbs);
                    let lb = limbs_to_nat(b@.limbs);
                    lemma_limbs_to_nat_upper_bound(diff@);
                    assert(borrow == 0) by (nonlinear_arith)
                        requires
                            limbs_to_nat(diff@) + la == lb + (borrow as nat) * pow2((n * 32) as nat),
                            lb > la,
                            limbs_to_nat(diff@) < pow2((n * 32) as nat),
                            borrow <= 1,
                    {}
                    assert((borrow as nat) * pow2((a.n@ * 32) as nat) == 0nat) by (nonlinear_arith) requires borrow == 0u32;
                    assert(limbs_to_nat(diff@) == lb - la);
                    lemma_limbs_nat_to_limbs_identity(diff@, a.n@);
                }
                RuntimeFixedPoint {
                    limbs: diff, sign: result_sign,
                    n: Ghost(a.n@), frac: Ghost(a.frac@),
                    model: Ghost(model),
                }
            }
        }
    }

    /// Negation of a single RuntimeFixedPoint: flip sign, copy limbs.
    pub fn neg_rfp(a: &RuntimeFixedPoint) -> (result: RuntimeFixedPoint)
        requires a.wf_spec(),
        ensures
            result.wf_spec(),
            result@.n == a@.n,
            result@.frac == a@.frac,
            result@ == a@.neg_spec(),
    {
        let n = a.limbs.len();
        let mut out_limbs: Vec<u32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n, n == a.limbs@.len(),
                out_limbs@.len() == i,
                out_limbs@ =~= a.limbs@.subrange(0, i as int),
            decreases n - i,
        {
            out_limbs.push(a.limbs[i]);
            i = i + 1;
        }
        proof { assert(out_limbs@ =~= a.limbs@); }

        let mag_zero = is_all_zero(&out_limbs);
        let new_sign = if mag_zero { false } else { !a.sign };
        let ghost model = FixedPoint { limbs: out_limbs@, sign: new_sign, n: a.n@, frac: a.frac@ };

        proof {
            // model == a@.neg_spec() (same limbs, flipped sign with canonical zero)
            assert(model == a@.neg_spec());
            FixedPoint::lemma_neg_wf(a@);
            FixedPoint::lemma_neg_view(a@);
        }

        RuntimeFixedPoint {
            limbs: out_limbs, sign: new_sign,
            n: Ghost(a.n@), frac: Ghost(a.frac@),
            model: Ghost(model),
        }
    }

    /// Signed multiplication of two RuntimeFixedPoints (widening).
    /// Result has 2*n limbs and 2*frac fractional bits.
    pub fn mul_rfp(a: &RuntimeFixedPoint, b: &RuntimeFixedPoint) -> (result: RuntimeFixedPoint)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a@.same_format(b@),
            a@.n <= 0x1FFF_FFFF,
        ensures
            result.wf_spec(),
            result@.n == 2 * a@.n,
            result@.frac == 2 * a@.frac,
    {
        let n = a.limbs.len();
        // Multiply magnitudes using Karatsuba
        let product_limbs = mul_karatsuba(&a.limbs, &b.limbs, n);
        // product has 2n limbs, ltn(product) == ltn(a.limbs) * ltn(b.limbs)

        // Sign: XOR of input signs (positive if same sign, negative if different)
        let product_zero = is_all_zero(&product_limbs);
        let result_sign = if product_zero { false } else { a.sign != b.sign };

        let ghost model = FixedPoint {
            limbs: product_limbs@,
            sign: result_sign,
            n: 2 * a.n@,
            frac: 2 * a.frac@,
        };

        proof {
            // wf: limbs.len() == 2*n ✓ (from mul_karatsuba ensures)
            // n > 0: 2 * a.n@ > 0 since a.n@ > 0
            assert(2 * a.n@ > 0) by (nonlinear_arith) requires a.n@ > 0;
            // frac <= n*32: 2*frac <= 2*n*32 since frac <= n*32
            assert(2 * a.frac@ <= 2 * a.n@ * 32) by (nonlinear_arith)
                requires a.frac@ <= a.n@ * 32;
            // canonical zero: result_sign is false when product is zero
            assert(model.wf_spec());
        }

        RuntimeFixedPoint {
            limbs: product_limbs,
            sign: result_sign,
            n: Ghost(2 * a.n@),
            frac: Ghost(2 * a.frac@),
            model: Ghost(model),
        }
    }
    /// Interval addition: [lo_a + lo_b, hi_a + hi_b], exact = exact_a + exact_b.
    pub fn add_interval(&self, rhs: &Self) -> (result: Self)
        requires
            self.wf_spec(), rhs.wf_spec(),
            self.lo@.same_format(rhs.lo@),
            FixedPoint::add_no_overflow(self.lo@, rhs.lo@),
            FixedPoint::add_no_overflow(self.hi@, rhs.hi@),
        ensures
            result.wf_spec(),
            result.exact@ == self.exact@.add_spec(rhs.exact@),
    {
        let new_lo = Self::add_rfp(&self.lo, &rhs.lo);
        let new_hi = Self::add_rfp(&self.hi, &rhs.hi);
        let ghost new_exact = self.exact@.add_spec(rhs.exact@);

        proof {
            // add_rfp ensures: new_lo@ == self.lo@.add_spec(rhs.lo@)
            //                  new_hi@ == self.hi@.add_spec(rhs.hi@)
            // Need: new_lo@.view() <= new_exact <= new_hi@.view()

            // From add_spec view correspondence:
            FixedPoint::lemma_add_view(self.lo@, rhs.lo@);
            FixedPoint::lemma_add_view(self.hi@, rhs.hi@);
            // new_lo@.view() eqv lo.view() + rhs_lo.view()
            // new_hi@.view() eqv hi.view() + rhs_hi.view()

            // From wf: lo.view() <= exact <= hi.view() for both self and rhs
            Rational::lemma_le_add_both(self.lo@.view(), self.exact@, rhs.lo@.view(), rhs.exact@);
            // lo.view() + rhs_lo.view() <= exact + rhs_exact
            Rational::lemma_le_add_both(self.exact@, self.hi@.view(), rhs.exact@, rhs.hi@.view());
            // exact + rhs_exact <= hi.view() + rhs_hi.view()

            // Chain through eqv: new_lo@.view() eqv lo+rhs_lo <= exact+rhs_exact
            Rational::lemma_eqv_implies_le(new_lo@.view(), self.lo@.view().add_spec(rhs.lo@.view()));
            Rational::lemma_le_transitive(new_lo@.view(), self.lo@.view().add_spec(rhs.lo@.view()), new_exact);

            // exact+rhs_exact <= hi+rhs_hi eqv new_hi@.view()
            Rational::lemma_eqv_symmetric(new_hi@.view(), self.hi@.view().add_spec(rhs.hi@.view()));
            Rational::lemma_eqv_implies_le(self.hi@.view().add_spec(rhs.hi@.view()), new_hi@.view());
            Rational::lemma_le_transitive(new_exact, self.hi@.view().add_spec(rhs.hi@.view()), new_hi@.view());
        }

        RuntimeFixedPointInterval { lo: new_lo, hi: new_hi, exact: Ghost(new_exact) }
    }
}

} // verus!
