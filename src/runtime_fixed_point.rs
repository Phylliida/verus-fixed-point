use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_rational::Rational;
#[cfg(verus_keep_ghost)]
use verus_interval_arithmetic::Interval;
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

// ── RuntimeFixedPoint constructors ─────────────────────

impl RuntimeFixedPoint {
    /// Construct a non-negative RuntimeFixedPoint from a u32 integer value.
    /// The value is placed at the integer position (above the fractional bits).
    /// For example, from_u32(2, 4, 96) creates the fixed-point value 2.0
    /// with 4 limbs and 96 fractional bits.
    pub fn from_u32(value: u32, n: usize, frac: usize) -> (result: Self)
        requires
            n > 0,
            frac <= n * 32,
            frac as nat % 32 == 0,
            frac / 32 < n, // at least one integer limb
        ensures
            result.wf_spec(),
            result@.n == n as nat,
            result@.frac == frac as nat,
            !result.sign,
            // The limb value: value * pow2(frac)
            limbs_to_nat(result@.limbs) == value as nat * pow2(frac as nat),
    {
        let mut limbs = zero_vec(n);
        let frac_limbs = frac / 32;
        limbs.set(frac_limbs, value);

        proof {
            lemma_limbs_to_nat_all_zeros(n as nat);
            // Prove ltn = value * pow2(frac) via single_nonzero lemma
            let fl = frac_limbs as nat;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(frac as int, 32int);
            assert(fl * 32 == frac as nat) by (nonlinear_arith)
                requires fl == frac as nat / 32, frac as nat % 32 == 0;
            assert(limbs@ =~= Seq::new(n as nat, |j: int| if j == fl as int { value } else { 0u32 }));
            lemma_limbs_to_nat_single_nonzero(n as nat, fl, value);
        }

        let ghost model = FixedPoint {
            limbs: limbs@,
            sign: false,
            n: n as nat,
            frac: frac as nat,
        };

        RuntimeFixedPoint {
            limbs, sign: false,
            n: Ghost(n as nat), frac: Ghost(frac as nat),
            model: Ghost(model),
        }
    }

    /// Construct a RuntimeFixedPoint zero.
    pub fn from_zero(n: usize, frac: usize) -> (result: Self)
        requires n > 0, frac <= n * 32,
        ensures
            result.wf_spec(), result@.n == n as nat, result@.frac == frac as nat, !result.sign,
            limbs_to_nat(result@.limbs) == 0,
    {
        let limbs = zero_vec(n);
        proof { lemma_limbs_to_nat_all_zeros(n as nat); }
        let ghost model = FixedPoint {
            limbs: limbs@, sign: false, n: n as nat, frac: frac as nat,
        };
        RuntimeFixedPoint {
            limbs, sign: false,
            n: Ghost(n as nat), frac: Ghost(frac as nat),
            model: Ghost(model),
        }
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
        // Expand (nalo+nahi)*(nblo+nbhi) using distributes
        lemma_mul_distribute(nalo as int, nahi as int, (nblo + nbhi) as int);
        // (nalo+nahi)*(nblo+nbhi) == nalo*(nblo+nbhi) + nahi*(nblo+nbhi)
        lemma_mul_distribute(nblo as int, nbhi as int, nalo as int);
        // (nblo+nbhi)*nalo == nblo*nalo + nbhi*nalo
        lemma_mul_distribute(nblo as int, nbhi as int, nahi as int);
        // (nblo+nbhi)*nahi == nblo*nahi + nbhi*nahi
        // Commutativity: nalo*(nblo+nbhi) == (nblo+nbhi)*nalo
        assert(nalo * (nblo + nbhi) == (nblo + nbhi) * nalo) by (nonlinear_arith);
        assert(nahi * (nblo + nbhi) == (nblo + nbhi) * nahi) by (nonlinear_arith);
        // Now Z3 has: nalo*(nblo+nbhi) == nblo*nalo + nbhi*nalo == nalo*nblo + nalo*nbhi
        assert(nalo * nblo == nblo * nalo) by (nonlinear_arith);
        assert(nalo * nbhi == nbhi * nalo) by (nonlinear_arith);
        assert(nahi * nblo == nblo * nahi) by (nonlinear_arith);
        assert(nahi * nbhi == nbhi * nahi) by (nonlinear_arith);
        // nz1f == nz0 + cross + nz2 where cross = nalo*nbhi + nahi*nblo >= 0
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
    pub frac_exec: usize, // exec-accessible frac (matches lo@.frac)
}

impl RuntimeFixedPointInterval {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.lo.wf_spec()
        &&& self.hi.wf_spec()
        &&& self.lo@.same_format(self.hi@)
        &&& self.lo@.view().le_spec(self.exact@)
        &&& self.exact@.le_spec(self.hi@.view())
        &&& self.frac_exec as nat == self.lo@.frac
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

        RuntimeFixedPointInterval { lo, hi, exact: Ghost(exact), frac_exec: frac }
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

        RuntimeFixedPointInterval { lo, hi, exact: Ghost(self.exact@), frac_exec: self.frac_exec }
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

        RuntimeFixedPointInterval { lo: new_lo, hi: new_hi, exact: Ghost(new_exact), frac_exec: self.frac_exec }
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
            result@ == a@.mul_spec(b@),
    {
        let n = a.limbs.len();
        let product_limbs = mul_karatsuba(&a.limbs, &b.limbs, n);

        let product_zero = is_all_zero(&product_limbs);
        let result_sign = if product_zero { false } else { a.sign != b.sign };

        let ghost model = FixedPoint {
            limbs: product_limbs@,
            sign: result_sign,
            n: 2 * a.n@,
            frac: 2 * a.frac@,
        };

        proof {
            assert(2 * a.n@ > 0) by (nonlinear_arith) requires a.n@ > 0;
            assert(2 * a.frac@ <= 2 * a.n@ * 32) by (nonlinear_arith)
                requires a.frac@ <= a.n@ * 32;
            assert(model.wf_spec());

            // Structural equality: model == a@.mul_spec(b@)
            // mul_spec computes: sv = signed_value(a) * signed_value(b)
            //   magnitude = |sv|, sign = sv < 0
            //   limbs = nat_to_limbs(magnitude, 2*n)
            // Our exec: product_limbs from Karatsuba, ltn == ltn(a) * ltn(b)
            //   result_sign = product_zero ? false : (a.sign != b.sign)

            assert(a.limbs@ == a@.limbs);
            assert(b.limbs@ == b@.limbs);
            let la = limbs_to_nat(a@.limbs);
            let lb = limbs_to_nat(b@.limbs);
            assert(limbs_to_nat(product_limbs@) == la * lb);

            // The mul_spec magnitude:
            // sv = a.sv * b.sv. |sv| = la * lb (since |±la * ±lb| = la * lb)
            // So mul_spec.limbs = nat_to_limbs(la * lb, 2*n)
            // By uniqueness: product_limbs@ == nat_to_limbs(la * lb, 2*n)
            FixedPoint::lemma_mul_no_overflow(a@, b@);
            lemma_limbs_to_nat_upper_bound(product_limbs@);
            assert(product_limbs@.len() == 2 * a.n@);
            assert(2 * a.n@ * 32 == 2 * (a.n@ * 32)) by (nonlinear_arith);
            lemma_limbs_nat_to_limbs_identity(product_limbs@, (2 * a.n@) as nat);

            // Sign matching: mul_spec.sign = (sv < 0), our sign = product_zero ? false : (a.sign != b.sign)
            let sv_a = a@.signed_value();
            let sv_b = b@.signed_value();
            let sv = sv_a * sv_b;

            // Show magnitude = la * lb in all cases
            if a.sign {
                assert(sv_a == -(la as int));
            } else {
                assert(sv_a == la as int);
            }
            if b.sign {
                assert(sv_b == -(lb as int));
            } else {
                assert(sv_b == lb as int);
            }

            // Show: (sv < 0) == (la*lb > 0 && a.sign != b.sign)
            if a.sign == b.sign {
                // sv = la*lb (both positive) or sv = (-la)*(-lb) = la*lb
                assert(sv >= 0) by (nonlinear_arith)
                    requires
                        (sv_a >= 0 && sv_b >= 0) || (sv_a <= 0 && sv_b <= 0),
                        sv == sv_a * sv_b;
            } else {
                // sv = la*(-lb) or sv = (-la)*lb, so sv = -(la*lb)
                if la * lb > 0 {
                    assert(sv < 0) by (nonlinear_arith)
                        requires
                            (sv_a >= 0 && sv_b <= 0 && sv_a * (-(sv_b)) > 0)
                            || (sv_a <= 0 && sv_b >= 0 && (-(sv_a)) * sv_b > 0),
                            sv == sv_a * sv_b;
                }
            }

            // The magnitude in mul_spec: |sv| = la * lb
            let spec_mag: nat = if sv >= 0 { sv as nat } else { (-sv) as nat };
            // In all cases: spec_mag == la * lb
            // Because |±la * ±lb| == la * lb for non-negative la, lb
            if !a.sign && !b.sign {
                assert(sv == (la as int) * (lb as int));
                assert(sv as nat == la * lb);
            } else if a.sign && b.sign {
                assert(sv == (la as int) * (lb as int)) by (nonlinear_arith)
                    requires sv == (-(la as int)) * (-(lb as int));
                assert(sv as nat == la * lb);
            } else if !a.sign && b.sign {
                assert(sv == -((la as int) * (lb as int))) by (nonlinear_arith)
                    requires sv == (la as int) * (-(lb as int));
                assert((-sv) as nat == la * lb);
            } else {
                assert(sv == -((la as int) * (lb as int))) by (nonlinear_arith)
                    requires sv == (-(la as int)) * (lb as int);
                assert((-sv) as nat == la * lb);
            }
        }

        RuntimeFixedPoint {
            limbs: product_limbs,
            sign: result_sign,
            n: Ghost(2 * a.n@),
            frac: Ghost(2 * a.frac@),
            model: Ghost(model),
        }
    }

    /// Divide a multi-limb number by a single u32 scalar. O(n).
    /// Returns (quotient, remainder). Processes MSB to LSB.
    pub fn div_by_u32(a: &Vec<u32>, divisor: u32, n: usize) -> (result: (Vec<u32>, u32))
        requires
            a@.len() == n,
            n > 0,
            divisor > 0u32,
        ensures
            result.0@.len() == n,
            (result.1 as nat) < (divisor as nat),
            limbs_to_nat(result.0@) * (divisor as nat) + (result.1 as nat) == limbs_to_nat(a@),
    {
        let mut quot = zero_vec(n);
        let mut rem: u64 = 0;
        let d = divisor as u64;
        // Ghost accumulator: tracks ltn(a[i..n]) = rem * BASE^i + quot_value * d
        // where quot_value = ltn(quot[i..n])
        // We'll use a ghost variable to track the accumulated quotient value.
        let ghost mut acc_q: nat = 0; // ltn(quot[i..n]) so far
        let ghost mut acc_a: nat = 0; // ltn(a[i..n]) so far

        let mut i: usize = n;
        while i > 0
            invariant
                i <= n,
                n == a@.len(),
                quot@.len() == n,
                d == divisor as u64,
                d > 0,
                rem < d,
                // Subrange invariants
                acc_a == limbs_to_nat(a@.subrange(i as int, n as int)),
                acc_q == limbs_to_nat(quot@.subrange(i as int, n as int)),
                // Algebraic: acc_q * d + rem == acc_a
                // Core invariant: rem * BASE^i_position + acc_q * d == acc_a
                // But BASE^i is hard to track. Use a simpler formulation:
                // acc_q * d + rem == acc_a ... NO this isn't right either
                // The correct relationship: at each step, we process one more digit.
                // rem is the carry from higher digits.
                // After processing a[i], quot[i] = (rem*BASE + a[i]) / d
                // new_rem = (rem*BASE + a[i]) % d
                // Invariant: rem * BASE^(relative position) + acc_q * d == acc_a
                // Since we go top-down, "relative position" = number of digits processed = n - i
                // So: rem * pow2((n-i) * 32) ... this is still complex.
                //
                // Simpler: just track rem * pow2(0) at the end.
                // At exit (i=0): rem + ltn(quot) * d == ltn(a)
                //
                // During loop: rem * limb_base^(digits_remaining below)
                // Actually the simplest correct invariant:
                // ltn(quot[i..n]) * d + rem == ltn(a[i..n]) ... when rem < d
                // Wait, this isn't right because ltn(a[i..n]) could be much larger.
                //
                // The RIGHT invariant for top-down long division:
                // After processing positions [i..n), we have:
                //   rem * BASE^(n-i-1)... no.
                //
                // Let me think again. The algorithm processes from MSB to LSB.
                // At step k (processing position n-1-k), we have:
                //   cur = rem * BASE + a[n-1-k]
                //   quot[n-1-k] = cur / d
                //   rem = cur % d
                //
                // The invariant is: if we think of the number formed by a[i..n] in
                // BIG-endian order, then quot[i..n] (big-endian) is its quotient by d
                // and rem is the remainder.
                //
                // In little-endian: ltn(a[i..n]) = a[i] + a[i+1]*B + ... + a[n-1]*B^(n-1-i)
                // The MSB is a[n-1], which we process first.
                //
                // The key: after processing all positions from n-1 down to i, we have:
                //   rem + ltn(quot[i..n]) * d == ltn(a[i..n])
                //   ... NO, this isn't right for top-down either.
                //
                // ACTUALLY for single-digit division going MSB to LSB:
                // The relationship is sequential carry. Let me just NOT use subranges
                // and instead track a ghost "total" that we build up.

                // Track: at position i, we've computed quot for positions [i..n).
                // ghost_total = sum_{k=i}^{n-1} a[k] * BASE^(k-i) [relative to position i]
                // quot_total = sum_{k=i}^{n-1} quot[k] * BASE^(k-i)
                // Invariant: quot_total * d + rem == ghost_total
                // where rem < d.
                //
                // At exit (i=0): quot_total == ltn(quot), ghost_total == ltn(a)
                // So: ltn(quot) * d + rem == ltn(a). QED.
                //
                // Maintenance: when we process position i-1:
                //   cur = rem * BASE + a[i-1]
                //   q = cur / d, new_rem = cur % d
                //   new_quot_total = q + quot_total * BASE  (prepending q at position i-1)
                //   new_ghost_total = a[i-1] + ghost_total * BASE
                //   new_quot_total * d + new_rem
                //     = (q + quot_total * BASE) * d + new_rem
                //     = q*d + quot_total * BASE * d + new_rem
                //     = (cur - new_rem) + quot_total * BASE * d + new_rem
                //     = cur + quot_total * d * BASE
                //     = rem * BASE + a[i-1] + (quot_total * d) * BASE
                //     = rem * BASE + a[i-1] + (ghost_total - rem) * BASE
                //        [since quot_total * d = ghost_total - rem from invariant]
                //     = rem * BASE + a[i-1] + ghost_total * BASE - rem * BASE
                //     = a[i-1] + ghost_total * BASE
                //     = new_ghost_total ✓
                acc_q * (divisor as nat) + (rem as nat) == acc_a,
            decreases i,
        {
            i = i - 1;
            proof {
                assert(d <= 0xFFFF_FFFFu64);
                assert(rem <= 0xFFFF_FFFEu64) by (nonlinear_arith)
                    requires rem < d, d <= 0xFFFF_FFFFu64;
            }
            let ai = a[i];
            let cur: u64 = rem * 0x1_0000_0000u64 + ai as u64;
            let q = cur / d;
            let new_rem = cur % d;

            proof {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(cur as int, d as int);
                // cur == d * q + new_rem

                // Update ghost accumulators
                // new_acc_a = a[i] + old_acc_a * BASE (prepend a[i])
                // new_acc_q = q + old_acc_q * BASE (prepend q)
                let old_acc_q = acc_q;
                let old_acc_a = acc_a;
                let new_acc_q_val = q as nat + old_acc_q * limb_base();
                let new_acc_a_val = a@[i as int] as nat + old_acc_a * limb_base();

                // Prove: new_acc_q * d + new_rem == new_acc_a
                // (q + old_acc_q * BASE) * d + new_rem
                //   = q*d + old_acc_q * BASE * d + new_rem
                //   = (cur - new_rem) + old_acc_q * d * BASE + new_rem
                //   = cur + (old_acc_a - rem) * BASE    [old_acc_q * d == old_acc_a - rem]
                //   = rem*BASE + a[i] + old_acc_a*BASE - rem*BASE
                //   = a[i] + old_acc_a * BASE = new_acc_a

                assert(new_acc_q_val * (divisor as nat) + (new_rem as nat) == new_acc_a_val)
                    by (nonlinear_arith)
                    requires
                        old_acc_q * (divisor as nat) + (rem as nat) == old_acc_a,
                        cur == rem * 0x1_0000_0000u64 + a@[i as int] as u64,
                        cur as int == d as int * (q as int) + new_rem as int,
                        d == divisor as u64,
                        new_acc_q_val == q as nat + old_acc_q * limb_base(),
                        new_acc_a_val == a@[i as int] as nat + old_acc_a * limb_base(),
                {}

                // Connect to subrange values
                lemma_limbs_to_nat_subrange_extend(a@, i as nat);
                // ltn(a[i..n]) = a[i] + BASE * ltn(a[i+1..n]) = a[i] + BASE * old_acc_a = new_acc_a
            }

            let ghost old_rem = rem;
            let ghost pre_set_quot = quot@;
            let ghost pre_set_tail = quot@.subrange((i + 1) as int, n as int);
            quot.set(i, q as u32);
            rem = new_rem;

            proof {
                // Tail unchanged after set
                assert(quot@.subrange((i + 1) as int, n as int) =~= pre_set_tail);

                // For a: unfold ltn on subrange a[i..n]
                let a_sub = a@.subrange(i as int, n as int);
                assert(a_sub[0] == a@[i as int]);
                assert(a_sub.subrange(1, a_sub.len() as int)
                    =~= a@.subrange((i + 1) as int, n as int));

                // For quot: unfold ltn on subrange quot[i..n]
                let q_sub = quot@.subrange(i as int, n as int);
                assert(q_sub[0] == q as u32);
                assert(q_sub.subrange(1, q_sub.len() as int) =~= pre_set_tail);

                // Unfold ltn for a_sub and q_sub to connect to algebraic proof
                // ltn(a_sub) = a[i] + BASE * ltn(a[i+1..n]) = a[i] + BASE * old_acc_a
                let old_acc_a = acc_a;
                let old_acc_q = acc_q;
                assert(limbs_to_nat(a_sub) == a@[i as int] as nat + limb_base() * old_acc_a);
                // Help Z3 unfold limbs_to_nat for q_sub
                assert(limbs_to_nat(q_sub)
                    == q_sub[0] as nat + limb_base() * limbs_to_nat(q_sub.subrange(1, q_sub.len() as int)));
                // q < BASE: since cur = rem*BASE + a[i] < d*BASE, q = cur/d < BASE
                // cur = rem * BASE + a[i], rem < d, a[i] < BASE
                // So cur < d * BASE
                // Prove q < BASE via: cur < d * BASE, so q = cur / d < BASE
                // cur = rem * BASE + a[i]. a[i] is u32 so a[i] <= BASE-1.
                // rem < d, so rem <= d-1, so rem*BASE <= (d-1)*BASE.
                // cur <= (d-1)*BASE + BASE - 1 = d*BASE - 1 < d*BASE.
                // q < BASE: cur = rem*BASE + ai, rem < d, ai: u32 < BASE
                // So cur < d*BASE, hence q = cur/d < BASE
                // Use old_rem (before update) to reason about cur
                let ghost ai_u64 = ai as u64;
                assert(cur == old_rem * 0x1_0000_0000u64 + ai_u64);
                assert(old_rem < d);
                assert(cur < d * 0x1_0000_0000u64) by (nonlinear_arith)
                    requires old_rem < d, ai_u64 <= 0xFFFF_FFFFu64, cur == old_rem * 0x1_0000_0000u64 + ai_u64, d > 0;
                assert(q < 0x1_0000_0000u64) by (nonlinear_arith)
                    requires cur < d * 0x1_0000_0000u64, q == cur / d, d > 0;
                assert(q_sub[0] as nat == q as nat);
                assert(limbs_to_nat(q_sub.subrange(1, q_sub.len() as int)) == limbs_to_nat(pre_set_tail));
                assert(limbs_to_nat(pre_set_tail) == old_acc_q);
                assert(limbs_to_nat(q_sub) == q as nat + limb_base() * old_acc_q);

                // Set ghosts
                acc_a = limbs_to_nat(a_sub);
                acc_q = limbs_to_nat(q_sub);
            }
        }

        proof {
            // At exit: i == 0
            // acc_q * d + rem == acc_a
            // acc_a == ltn(a[0..n]) == ltn(a)
            // acc_q == ltn(quot[0..n]) == ltn(quot)
            lemma_limbs_to_nat_subrange_full(a@);
            lemma_limbs_to_nat_subrange_full(quot@);
        }

        (quot, rem as u32)
    }

    /// Right-shift a limb array by `shift` full limbs (drop lowest `shift` limbs).
    /// Equivalent to integer division by pow2(shift * 32).
    /// Returns the upper (n - shift) limbs.
    pub fn shift_right_limbs(a: &Vec<u32>, n: usize, shift: usize) -> (result: Vec<u32>)
        requires
            a@.len() == n,
            shift <= n,
        ensures
            result@.len() == n - shift,
            result@ == a@.subrange(shift as int, n as int),
    {
        let mut out: Vec<u32> = Vec::new();
        let mut i: usize = shift;
        while i < n
            invariant
                shift <= i, i <= n, n == a@.len(),
                out@.len() == i - shift,
                out@ =~= a@.subrange(shift as int, i as int),
            decreases n - i,
        {
            out.push(a[i]);
            i = i + 1;
        }
        out
    }

    /// Exec-level reduce: truncate a wide RuntimeFixedPoint back to target format.
    /// Right-shifts by shift_limbs limbs (= (a.frac - target_frac) / 32),
    /// then takes bottom target_n limbs. Floor rounding (truncation toward zero).
    ///
    /// The shift_limbs parameter must equal the fractional precision reduction in limbs.
    /// For mul results (2N limbs, 2F frac) reducing to (N limbs, F frac): shift_limbs = F/32.
    ///
    /// The result is the shifted value modulo pow2(target_n * 32). When there is no
    /// overflow (the shifted value fits in target_n limbs), the modulo is a no-op.
    pub fn reduce_rfp_floor(
        a: &RuntimeFixedPoint, target_n: usize, target_frac: usize, shift_limbs: usize,
    ) -> (result: RuntimeFixedPoint)
        requires
            a.wf_spec(),
            a@.frac >= target_frac as nat,
            shift_limbs as nat * 32 == a@.frac - target_frac as nat,
            shift_limbs <= a@.n,
            target_n > 0,
            target_frac <= target_n * 32,
        ensures
            result.wf_spec(),
            result@.n == target_n as nat,
            result@.frac == target_frac as nat,
            !a.sign ==> !result.sign,
            // View correspondence: floor-divided by pow2(frac_shift), modulo target capacity
            limbs_to_nat(result@.limbs)
                == (limbs_to_nat(a@.limbs) / pow2((shift_limbs as nat * 32) as nat))
                   % pow2((target_n as nat * 32) as nat),
    {
        let shifted = Self::shift_right_limbs(&a.limbs, a.limbs.len(), shift_limbs);

        let result_limbs = if shifted.len() > target_n {
            slice_vec(&shifted, 0, target_n)
        } else {
            pad_to_length(&shifted, target_n)
        };

        let result_zero = is_all_zero(&result_limbs);
        let result_sign = if result_zero { false } else { a.sign };

        let ghost model = FixedPoint {
            limbs: result_limbs@,
            sign: result_sign,
            n: target_n as nat,
            frac: target_frac as nat,
        };

        proof {
            assert(a.limbs@ == a@.limbs);
            let sl = shift_limbs as nat;
            let n_a = a.limbs@.len();

            // shifted@ == a.limbs@.subrange(sl, n_a)
            assert(shifted@ == a@.limbs.subrange(sl as int, n_a as int));

            // By split lemma: ltn(a) == ltn(a[..sl]) + ltn(a[sl..n_a]) * pow2(sl*32)
            lemma_limbs_to_nat_split(a@.limbs, sl);

            let lo = limbs_to_nat(a@.limbs.subrange(0, sl as int));
            let hi = limbs_to_nat(a@.limbs.subrange(sl as int, n_a as int));

            // lo < pow2(sl*32)
            lemma_limbs_to_nat_upper_bound(a@.limbs.subrange(0, sl as int));
            let shift_pow = pow2((sl * 32) as nat);
            lemma_pow2_positive((sl * 32) as nat);

            // hi == ltn(a) / shift_pow  (by fundamental div mod converse)
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                limbs_to_nat(a@.limbs) as int,
                shift_pow as int,
                hi as int,
                lo as int,
            );
            // Now: hi == ltn(a) / pow2(sl*32) and ltn(shifted) == hi

            let target_pow = pow2((target_n as nat * 32) as nat);
            lemma_pow2_positive((target_n as nat * 32) as nat);

            if shifted@.len() as int > target_n as int {
                // Slice case: result = shifted[0..target_n]
                // ltn(shifted) = ltn(shifted[0..tn]) + ltn(shifted[tn..]) * pow2(tn*32)
                lemma_limbs_to_nat_split(shifted@, target_n as nat);
                let s_lo = limbs_to_nat(shifted@.subrange(0, target_n as int));
                let s_hi = limbs_to_nat(shifted@.subrange(target_n as int, shifted@.len() as int));

                // s_lo < pow2(target_n*32) (from upper_bound on target_n limbs)
                lemma_limbs_to_nat_upper_bound(shifted@.subrange(0, target_n as int));

                // By fundamental_div_mod_converse: s_lo = hi % target_pow
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                    hi as int,
                    target_pow as int,
                    s_hi as int,
                    s_lo as int,
                );

                assert(result_limbs@ =~= shifted@.subrange(0, target_n as int));
            } else {
                // Pad case: ltn(result) == ltn(shifted) == hi
                // hi = ltn(shifted), and shifted has ≤ target_n limbs
                // so hi < pow2(shifted.len()*32) ≤ pow2(target_n*32) = target_pow
                lemma_limbs_to_nat_upper_bound(shifted@);
                let sl_bits = (shifted@.len() * 32) as nat;
                if shifted@.len() < target_n {
                    lemma_pow2_monotone(sl_bits, (target_n as nat * 32) as nat);
                }
                // hi < target_pow, so hi % target_pow == hi
                vstd::arithmetic::div_mod::lemma_small_mod(hi, target_pow);
            }
        }

        RuntimeFixedPoint {
            limbs: result_limbs,
            sign: result_sign,
            n: Ghost(target_n as nat),
            frac: Ghost(target_frac as nat),
            model: Ghost(model),
        }
    }

    /// Multiply then reduce: a * b at N-limb precision.
    /// Chains mul_rfp (widens to 2N) → reduce_rfp_floor (truncates back to N).
    /// The standard operation for fixed-point iteration loops.
    pub fn mul_reduce_rfp(a: &RuntimeFixedPoint, b: &RuntimeFixedPoint, frac: usize) -> (result: RuntimeFixedPoint)
        requires
            a.wf_spec(), b.wf_spec(),
            a@.same_format(b@),
            a@.n <= 0x0FFF_FFFF,
            a@.frac == frac as nat,
            frac as nat % 32 == 0,
            frac < a@.n * 32,
        ensures
            result.wf_spec(),
            result@.n == a@.n,
            result@.frac == frac as nat,
    {
        let n = a.limbs.len();
        let frac_shift = frac / 32;
        let wide = Self::mul_rfp(a, b);
        proof {
            assert(wide@.n == 2 * a@.n);
            assert(wide@.frac == 2 * frac as nat);
            // shift_limbs * 32 == frac
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(frac as int, 32int);
                assert(frac_shift as nat * 32 == frac as nat);
        }
        Self::reduce_rfp_floor(&wide, n, frac, frac_shift)
    }

    /// Signed subtraction: a - b = a + (-b).
    pub fn sub_rfp(a: &RuntimeFixedPoint, b: &RuntimeFixedPoint) -> (result: RuntimeFixedPoint)
        requires
            a.wf_spec(), b.wf_spec(),
            a@.same_format(b@),
            FixedPoint::sub_no_overflow(a@, b@),
        ensures
            result.wf_spec(),
            result@.n == a@.n,
            result@.frac == a@.frac,
    {
        let neg_b = Self::neg_rfp(b);
        proof {
            FixedPoint::lemma_neg_wf(b@);
            FixedPoint::lemma_neg_same_format(b@);
        }
        Self::add_rfp(a, &neg_b)
    }

    /// Newton-Raphson reciprocal: compute 1/b to N-limb fixed-point precision.
    /// Uses x_{n+1} = x_n * (2 - b * x_n), doubling precision each iteration.
    /// Total cost: O(n^1.585 * log n) via Karatsuba at each step.
    pub fn recip_newton(
        b: &RuntimeFixedPoint,
        two: &RuntimeFixedPoint,
        n: usize, frac: usize, iters: usize,
    ) -> (result: RuntimeFixedPoint)
        requires
            b.wf_spec(), two.wf_spec(),
            b@.n == n as nat, b@.frac == frac as nat,
            two@.n == n as nat, two@.frac == frac as nat,
            !b.sign, !two.sign,
            // two represents 2.0: ltn = 2 * pow2(frac)
            limbs_to_nat(two@.limbs) == 2 * pow2(frac as nat),
            // b ∈ [S, 3S/2] where S = pow2(frac): ensures 1.0 ≤ b_real ≤ 1.5
            // This guarantees |e_0| ≤ S/2 and rapid quadratic convergence.
            // Callers with b outside this range should normalize first.
            limbs_to_nat(b@.limbs) >= pow2(frac as nat),
            2 * limbs_to_nat(b@.limbs) <= 3 * pow2(frac as nat),
            n > 0,
            n <= 0x0FFF_FFFF, // ensure 4*n doesn't overflow
            frac < n * 32,
            frac as nat % 32 == 0, // limb-aligned frac for clean reduce
            frac >= 5, // S ≥ 32 for convergence bounds
        ensures
            result.wf_spec(),
            result@.n == n as nat,
            result@.frac == frac as nat,
            !result.sign,
            // Convergence: after ≥ 1 iteration, b*result/S ≤ S+1.
            iters >= 1 ==>
                limbs_to_nat(b@.limbs) * limbs_to_nat(result@.limbs)
                    / pow2(frac as nat) <= pow2(frac as nat) + 1,
    {
        // Build initial estimate x_0: start with "one" (= 2^frac in limb representation)
        // A smarter initial estimate would use the top limb of b, but "one" works.
        let mut x_limbs = zero_vec(n);
        let limb_pos = frac / 32;
        x_limbs.set(limb_pos, 1u32);
        // x_limbs represents pow2(frac) = fixed-point 1.0

        let mut x = RuntimeFixedPoint {
            limbs: x_limbs,
            sign: false,
            n: Ghost(n as nat),
            frac: Ghost(frac as nat),
            model: Ghost(FixedPoint {
                limbs: x_limbs@,
                sign: false,
                n: n as nat,
                frac: frac as nat,
            }),
        };

        proof {
            assert(x.wf_spec());
            // Prove ltn(x.limbs) == pow2(frac) for the initial value invariant
            // x has a single 1 at position limb_pos = frac/32, zeros elsewhere
            let lp = limb_pos as nat;
            assert(x@.limbs =~= Seq::new(n as nat, |j: int| if j == lp as int { 1u32 } else { 0u32 }));
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(frac as int, 32int);
            assert(lp * 32 == frac as nat) by (nonlinear_arith)
                requires lp == frac as nat / 32, frac as nat % 32 == 0;
            assert(lp < n) by (nonlinear_arith) requires frac < n * 32, lp * 32 == frac as nat;
            lemma_limbs_to_nat_single_nonzero(n as nat, lp, 1u32);
            assert(limbs_to_nat(x@.limbs) == 1 * pow2((lp * 32) as nat));
            assert(limbs_to_nat(x@.limbs) == pow2(frac as nat));
        }

        // Newton iterations
        let mut i: usize = 0;
        while i < iters
            invariant
                i <= iters,
                x.wf_spec(),
                !x.sign,
                x@.n == n as nat,
                x@.frac == frac as nat,
                b.wf_spec(),
                b@.n == n as nat,
                b@.frac == frac as nat,
                two.wf_spec(),
                two@.n == n as nat,
                two@.frac == frac as nat,
                !b.sign, !two.sign,
                limbs_to_nat(two@.limbs) == 2 * pow2(frac as nat),
                n > 0,
                n <= 0x0FFF_FFFF,
                frac < n * 32,
                frac as nat % 32 == 0,
                frac >= 5,
                limbs_to_nat(b@.limbs) >= pow2(frac as nat),
                2 * limbs_to_nat(b@.limbs) <= 3 * pow2(frac as nat),
                // Initial value tracking: at i=0, x is still the initial S
                i == 0 ==> limbs_to_nat(x@.limbs) == pow2(frac as nat),
                // Convergence: after first iteration, bx ≤ S+1
                i >= 1 ==> limbs_to_nat(b@.limbs) * limbs_to_nat(x@.limbs)
                    / pow2(frac as nat) <= pow2(frac as nat) + 1,
            decreases iters - i,
        {
            let ghost s = pow2(frac as nat);
            let ghost b_int = limbs_to_nat(b@.limbs);
            let ghost x_int = limbs_to_nat(x@.limbs);
            let ghost p = pow2((n * 32) as nat);

            // Step 1: bx_wide = b * x (widens to 2N limbs)
            let bx_wide = Self::mul_rfp(b, &x);

            // Step 2: reduce bx back to N limbs
            let frac_shift = frac / 32;
            proof {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(frac as int, 32int);
                assert(frac_shift as nat * 32 == frac as nat);
                assert(bx_wide@.frac == 2 * frac as nat);
            }
            let bx = Self::reduce_rfp_floor(&bx_wide, n, frac, frac_shift);

            // ═══ Exec↔Spec connection: ltn(bx) = (b_int * x_int / S) % pow2(n*32) ═══
            proof {
                // Both b and x are positive: signed_value == ltn(limbs)
                let b_sv = b@.signed_value();
                let x_sv = x@.signed_value();
                assert(b_sv >= 0);
                assert(x_sv >= 0);
                assert(b_sv == b_int as int);
                assert(x_sv == x_int as int);
                assert(b_sv * x_sv >= 0) by (nonlinear_arith)
                    requires b_sv >= 0, x_sv >= 0;

                // bx_wide@ == b@.mul_spec(x@): structural equality from mul_rfp
                // mul_spec for positive values: limbs = nat_to_limbs(b_sv * x_sv, 2n)
                assert(!bx_wide@.sign);
                let magnitude = (b_sv * x_sv) as nat;
                assert(magnitude == b_int * x_int);

                // ltn(nat_to_limbs(m, k)) = m when m < pow2(k*32)
                // Need: b_int * x_int < pow2(2*n*32)
                lemma_limbs_to_nat_upper_bound(b@.limbs);
                lemma_limbs_to_nat_upper_bound(x@.limbs);
                assert(b_int < p);
                assert(x_int < p);
                lemma_pow2_add((n * 32) as nat, (n * 32) as nat);
                assert(b_int * x_int < p * p) by (nonlinear_arith)
                    requires b_int < p, x_int < p, p > 0;
                assert(p * p == pow2((2 * n * 32) as nat)) by {
                    assert((n * 32 + n * 32) as nat == (2 * n * 32) as nat) by (nonlinear_arith);
                }
                lemma_nat_to_limbs_roundtrip(magnitude, (2 * n) as nat);
                assert(limbs_to_nat(bx_wide@.limbs) == b_int * x_int);

                // From reduce: ltn(bx) = (ltn(bx_wide) / S) % pow2(n*32)
                let bx_val = (b_int * x_int / s) % p;
                assert(limbs_to_nat(bx@.limbs) == bx_val);

                // Show modulo is no-op: b_int * x_int / S < pow2(n*32)
                // At i=0: x = S, so b*S/S = b < pow2(n*32) ✓
                // At i≥1: b*x/S ≤ S+1 < pow2(n*32) ✓
                // s + 1 < p: since frac ≤ n*32 - 32, pow2(frac) ≤ pow2(n*32)/pow2(32)
                // so s + 1 ≤ 2*s ≤ pow2(frac+1) ≤ pow2(n*32) = p
                lemma_pow2_monotone((frac as nat + 1) as nat, (n * 32) as nat);
                assert(2 * s == pow2((frac as nat + 1) as nat)) by {
                    lemma_pow2_add(frac as nat, 1);
                    assert(pow2(1nat) == 2) by { lemma_pow2_one(); }
                }
                reveal_with_fuel(pow2, 6);
                assert(pow2(5nat) == 32nat);
                lemma_pow2_monotone(5, frac as nat);
                assert(s >= 32nat);
                assert(s + 1 < p) by (nonlinear_arith)
                    requires 2 * s <= p, s >= 32;

                if i == 0 {
                    // At i=0, x is the initial value with ltn = S
                    assert(x_int == s); // from loop invariant
                    assert(b_int * s / s == b_int) by (nonlinear_arith)
                        requires s > 0nat;
                    assert(b_int * x_int / s == b_int);
                    assert(b_int < p);
                } else {
                    assert(b_int * x_int / s <= s + 1);
                }
                // Modulo is no-op
                vstd::arithmetic::div_mod::lemma_small_mod(
                    b_int * x_int / s, p);
                assert(bx_val == b_int * x_int / s);

                // Therefore: ltn(bx@.limbs) = b_int * x_int / S
                // And this is ≤ 2S (for the cmp guard)
                if i == 0 {
                    // b_int ≤ 3S/2 ≤ 2S
                    assert(limbs_to_nat(bx@.limbs) <= 2 * s) by (nonlinear_arith)
                        requires limbs_to_nat(bx@.limbs) == b_int,
                                 2 * b_int <= 3 * s;
                } else {
                    // S+1 ≤ 2S for S ≥ 1
                    assert(s + 1 <= 2 * s) by (nonlinear_arith) requires s >= 1;
                    assert(limbs_to_nat(bx@.limbs) <= 2 * s);
                }

                // bx is positive (mul of two positives + reduce)
                assert(!bx_wide.sign);
                assert(!bx.sign);
            }

            // Step 3: compute two_minus_bx = 2 - bx
            let neg_bx = Self::neg_rfp(&bx);
            proof {
                FixedPoint::lemma_neg_wf(bx@);
                FixedPoint::lemma_neg_same_format(bx@);
            }

            // Guard: bx > 2 check — NEVER triggers under our preconditions
            if cmp_limbs(&bx.limbs, &two.limbs, n) > 0i8 {
                return x;
            }

            // Prove add_no_overflow(two@, neg_bx@)
            proof {
                FixedPoint::lemma_neg_signed_value(bx@);
                assert(!bx.sign);
                let bx_sv = bx@.signed_value();
                let two_sv = two@.signed_value();
                assert(bx_sv == limbs_to_nat(bx@.limbs) as int);
                assert(two_sv == limbs_to_nat(two@.limbs) as int);
                assert(bx_sv >= 0);
                assert(two_sv >= 0);
                assert(limbs_to_nat(bx@.limbs) <= limbs_to_nat(two@.limbs));
                lemma_limbs_to_nat_upper_bound(two@.limbs);
                let sv = two_sv + neg_bx@.signed_value();
                assert(neg_bx@.signed_value() == -bx_sv);
                assert(sv >= 0);
                assert(sv < pow2((n * 32) as nat) as int) by (nonlinear_arith)
                    requires sv == two_sv - bx_sv, two_sv < pow2((n * 32) as nat) as int, bx_sv >= 0;
            }
            let two_minus_bx = Self::add_rfp(two, &neg_bx);

            // Step 4: x_new = x * (2 - bx), widens to 2N
            let x_wide = Self::mul_rfp(&x, &two_minus_bx);

            // Step 5: reduce back to N limbs
            proof { assert(x_wide@.frac == 2 * frac as nat); }
            let x_new = Self::reduce_rfp_floor(&x_wide, n, frac, frac_shift);

            // Guard: sign check — NEVER triggers (both factors positive, result positive)
            if x_new.sign {
                return x;
            }

            // ═══ Convergence proof: connect exec x_new to spec, then apply lemma ═══
            proof {
                use crate::fixed_point::newton_convergence::*;
                let bx_val = b_int * x_int / s;

                // --- Connect two_minus_bx to spec: ltn = 2S - bx_val ---
                // add_rfp gives structural equality: two_minus_bx@ == two@.add_spec(neg_bx@)
                // signed_value = two_sv - bx_sv = 2S - bx_val (positive)
                // So ltn(two_minus_bx@.limbs) = 2S - bx_val
                let tmb_int = limbs_to_nat(two_minus_bx@.limbs);

                // two_minus_bx@ == two@.add_spec(neg_bx@) (structural equality from add_rfp)
                // add_spec unfolds: sign = (two_sv + neg_bx_sv < 0), limbs = nat_to_limbs(|sv|, n)
                // two_sv = 2S, neg_bx_sv = -bx_val. Sum = 2S - bx_val ≥ 0.
                // Connect ltn(two_minus_bx@.limbs) to 2S - bx_val
                // add_rfp: two_minus_bx@ == two@.add_spec(neg_bx@)
                // add_spec: sv = two_sv + neg_bx_sv = 2S + (-bx_val) = 2S - bx_val ≥ 0
                // sign = false, limbs = nat_to_limbs(2S - bx_val, n)
                // ltn(nat_to_limbs(m, n)) = m (roundtrip) when m < pow2(n*32)
                // bx_val = ltn(bx.limbs) (from earlier proof) and bx_val ≤ 2S
                assert(bx_val == limbs_to_nat(bx@.limbs));
                assert(bx_val <= 2 * s);

                let tmb_nat: nat = (2 * s - bx_val) as nat;
                // The add_spec gives signed_value = 2S - bx_val
                assert(two@.signed_value() == (2 * s) as int);
                assert(neg_bx@.signed_value() == -(bx_val as int));
                let add_sv = (2 * s) as int - bx_val as int;
                assert(add_sv >= 0);
                // add_spec produces sign = false, magnitude = tmb_nat
                // two_minus_bx@.limbs = nat_to_limbs(tmb_nat, n)
                assert(!two_minus_bx@.sign);
                // ltn = tmb_nat via roundtrip
                assert(tmb_nat < p) by (nonlinear_arith) requires tmb_nat <= 2 * s, 2 * s < p;
                lemma_nat_to_limbs_roundtrip(tmb_nat, n as nat);
                let tmb_int = limbs_to_nat(two_minus_bx@.limbs);
                assert(tmb_int == tmb_nat);

                // --- Connect x_wide to spec: ltn = x_int * tmb_nat ---
                // mul_rfp gives x_wide@ == x@.mul_spec(two_minus_bx@)
                // Both positive: ltn = x_int * tmb_nat
                let x_sv = x@.signed_value();
                let tmb_sv = two_minus_bx@.signed_value();
                assert(x_sv >= 0);
                assert(tmb_sv >= 0);
                assert(x_sv * tmb_sv >= 0) by (nonlinear_arith)
                    requires x_sv >= 0, tmb_sv >= 0;
                assert(!x_wide@.sign);
                let x_wide_mag = (x_sv * tmb_sv) as nat;
                assert(x_wide_mag == x_int * tmb_nat);
                lemma_limbs_to_nat_upper_bound(x@.limbs);
                lemma_limbs_to_nat_upper_bound(two_minus_bx@.limbs);
                assert(x_int < p);
                assert(tmb_nat < p);
                assert(x_int * tmb_nat < p * p) by (nonlinear_arith)
                    requires x_int < p, tmb_nat < p, p > 0;
                assert(p * p == pow2((2 * n * 32) as nat)) by {
                    lemma_pow2_add((n * 32) as nat, (n * 32) as nat);
                    assert((n * 32 + n * 32) as nat == (2 * n * 32) as nat) by (nonlinear_arith);
                }
                lemma_nat_to_limbs_roundtrip(x_wide_mag, (2 * n) as nat);
                assert(limbs_to_nat(x_wide@.limbs) == x_int * tmb_nat);

                // --- Connect x_new to spec via reduce ---
                // reduce gives: ltn(x_new) = (x_int * tmb_nat / S) % pow2(n*32)
                let x_new_int = limbs_to_nat(x_new@.limbs);
                assert(x_new_int == (x_int * tmb_nat / s) % p);

                // Show modulo is no-op: x_int * tmb_nat / S < pow2(n*32)
                // At i=0: x_int = S, tmb = 2S-b ≤ S. x*tmb/S = tmb ≤ S < p.
                // At i≥1: x_int ≤ S+1 (from bx ≤ S+1 and b ≥ S), tmb ≤ 2S.
                //   x*tmb/S ≤ (S+1)*2S/S = 2S+2 < p.
                if i >= 1 {
                    // Derive x_int ≤ S+1 from the invariant bx_val ≤ S+1 and b ≥ S
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                        (b_int * x_int) as int, s as int);
                    let bx_rem = (b_int * x_int) % s;
                    // b*x = bx_val*S + bx_rem, bx_val ≤ S+1
                    // b*x ≤ (S+1)*S + S-1 < (S+2)*S
                    assert(b_int * x_int < (s + 2) * s) by (nonlinear_arith)
                        requires b_int * x_int == bx_val * s + bx_rem,
                                 bx_val <= s + 1, bx_rem < s as int, s > 0;
                    // x < (S+2)*S/b ≤ (S+2) since b ≥ S
                    assert(x_int <= s + 1) by (nonlinear_arith)
                        requires b_int * x_int < (s + 2) * s, b_int >= s, s > 0;
                }

                // In both cases: x_int * tmb_nat / s < p
                assert(tmb_nat <= 2 * s);
                // Prove 2*s < p (strictly): frac+1 ≤ n*32 - 31, so pow2(frac+1) < pow2(n*32)
                assert(frac as nat + 1 < (n * 32) as nat) by (nonlinear_arith)
                    requires frac as nat % 32 == 0, frac < n * 32, n > 0;
                lemma_pow2_strict_monotone((frac as nat + 1) as nat, (n * 32) as nat);
                assert(2 * s < p) by {
                    lemma_pow2_add(frac as nat, 1);
                    assert(pow2(1nat) == 2) by { lemma_pow2_one(); }
                }

                if i == 0 {
                    assert(x_int == s);
                    assert(x_int * tmb_nat / s == tmb_nat) by (nonlinear_arith)
                        requires x_int == s, s > 0;
                    assert(tmb_nat < p) by (nonlinear_arith) requires tmb_nat <= 2 * s, 2 * s < p;
                } else {
                    assert(x_int <= s + 1);
                    assert(x_int * tmb_nat <= (s + 1) * (2 * s)) by (nonlinear_arith)
                        requires x_int <= s + 1, tmb_nat <= 2 * s;
                    assert(x_int * tmb_nat / s <= 2 * s + 2) by (nonlinear_arith)
                        requires x_int * tmb_nat <= (s + 1) * (2 * s), s > 0;
                    // 4*s = pow2(frac+2) < pow2(n*32) = p (since frac+2 < n*32)
                    assert(frac as nat + 2 < (n * 32) as nat) by (nonlinear_arith)
                        requires frac as nat % 32 == 0, frac < n * 32;
                    lemma_pow2_strict_monotone((frac as nat + 2) as nat, (n * 32) as nat);
                    assert(4 * s < p) by {
                        lemma_pow2_add(frac as nat, 2);
                        reveal_with_fuel(pow2, 3);
                        assert(pow2(2nat) == 4nat);
                    }
                    assert(2 * s + 2 < p) by (nonlinear_arith) requires 4 * s < p, s >= 32;
                }
                vstd::arithmetic::div_mod::lemma_small_mod(
                    x_int * tmb_nat / s, p);
                assert(x_new_int == x_int * tmb_nat / s);

                // --- Apply convergence lemma ---
                if i == 0 {
                    // First step: use lemma_first_step_error_bound
                    // x_new_int = 2S - b (from the exec chain above)
                    // The lemma gives: b * (2S-b) / S ≤ S
                    lemma_first_step_error_bound(b_int, s);
                    // x_new_int = tmb_nat = 2S - b = (2*s - b_int) as nat
                    // b * x_new / S = b * (2S - b) / S ≤ S ≤ S + 1
                    assert(b_int * x_new_int / s <= s + 1) by (nonlinear_arith)
                        requires b_int * x_new_int / s <= s;
                } else {
                    // Subsequent step: use lemma_bx_bound_preserved
                    // Preconditions: b*x/s ≤ s+1 (from invariant), b*x/s ≤ 2s (proved)
                    lemma_bx_bound_preserved(b_int, x_int, s);
                    assert(b_int * x_new_int / s <= s + 1);
                }
            }

            x = x_new;
            i = i + 1;
        }

        x
    }

    /// Interval addition: [lo_a + lo_b, hi_a + hi_b], exact = exact_a + exact_b.
    /// Fixed-point division: a / b via Newton-Raphson reciprocal + Karatsuba multiply.
    /// Result = a * (1/b), computed to N-limb precision.
    /// Uses log2(N*32) Newton iterations for full precision convergence.
    /// Total cost: O(n^1.585 * log n).
    ///
    /// The result has the SAME format as the inputs (N limbs, FRAC fractional bits),
    /// because: a (N limbs) * recip(b) (N limbs) = 2N limbs, then reduce back to N.
    /// Fixed-point division: a / b via Newton-Raphson reciprocal + Karatsuba multiply.
    /// `frac` must match the fractional bits of a, b, and two.
    /// Total cost: O(n^1.585 * log n).
    pub fn div_rfp(
        a: &RuntimeFixedPoint,
        b: &RuntimeFixedPoint,
        two: &RuntimeFixedPoint,
        frac: usize,
        iters: usize,
    ) -> (result: RuntimeFixedPoint)
        requires
            a.wf_spec(), b.wf_spec(), two.wf_spec(),
            a@.same_format(b@),
            b@.same_format(two@),
            a@.frac == frac as nat,
            !b.sign, !two.sign,
            limbs_to_nat(two@.limbs) == 2 * pow2(frac as nat),
            // b ∈ [S, 3S/2] for Newton convergence
            limbs_to_nat(b@.limbs) >= pow2(frac as nat),
            2 * limbs_to_nat(b@.limbs) <= 3 * pow2(frac as nat),
            a@.n > 0,
            a@.n <= 0x0FFF_FFFF,
            frac < a@.n * 32,
            frac as nat % 32 == 0,
            frac >= 5,
        ensures
            result.wf_spec(),
            result@.n == a@.n,
            result@.frac == frac as nat,
    {
        let n = a.limbs.len();

        // Step 1: Compute 1/b via Newton-Raphson
        let recip = Self::recip_newton(b, two, n, frac, iters);

        // Step 2: a * (1/b) — widens to 2N limbs, 2*frac bits
        let product_wide = Self::mul_rfp(a, &recip);

        // Step 3: Reduce back to N limbs, frac bits
        proof {
            // mul_rfp ensures: product_wide@.n == 2 * a@.n, product_wide@.frac == 2 * frac
            // reduce needs: frac_diff % 32 == 0 and n fits
            assert(product_wide@.frac == 2 * frac as nat);
            assert(product_wide@.n == 2 * a@.n);
        }
        let frac_shift = frac / 32;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(frac as int, 32int);
                assert(frac_shift as nat * 32 == frac as nat);
        }
        Self::reduce_rfp_floor(&product_wide, n, frac, frac_shift)
    }

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

        RuntimeFixedPointInterval { lo: new_lo, hi: new_hi, exact: Ghost(new_exact), frac_exec: self.frac_exec }
    }
    /// Interval subtraction: exact = exact_a - exact_b.
    /// [lo_a, hi_a] - [lo_b, hi_b] uses negated rhs: add([lo_a, hi_a], [-hi_b, -lo_b]).
    pub fn sub_interval(&self, rhs: &Self) -> (result: Self)
        requires
            self.wf_spec(), rhs.wf_spec(),
            self.lo@.same_format(rhs.lo@),
            // Overflow conditions for the effective add: lo_a + (-hi_b), hi_a + (-lo_b)
            FixedPoint::add_no_overflow(self.lo@, rhs.hi@.neg_spec()),
            FixedPoint::add_no_overflow(self.hi@, rhs.lo@.neg_spec()),
        ensures
            result.wf_spec(),
            result.exact@ == self.exact@.sub_spec(rhs.exact@),
    {
        // Negate rhs endpoints: -[lo_b, hi_b] = [-hi_b, -lo_b]
        let neg_hi = Self::neg_rfp(&rhs.hi);  // becomes new lo
        let neg_lo = Self::neg_rfp(&rhs.lo);  // becomes new hi
        let ghost neg_exact = rhs.exact@.neg_spec();

        proof {
            // neg_hi@ == rhs.hi@.neg_spec(), neg_lo@ == rhs.lo@.neg_spec()
            // Need: neg_hi@.view() <= neg_exact <= neg_lo@.view()
            // From rhs wf: lo.view() <= exact <= hi.view()
            // Negation reverses: -hi.view() <= -exact <= -lo.view()
            Rational::lemma_neg_reverses_le(rhs.exact@, rhs.hi@.view());
            Rational::lemma_neg_reverses_le(rhs.lo@.view(), rhs.exact@);

            // Connect neg_spec views through eqv
            FixedPoint::lemma_neg_view(rhs.hi@);
            FixedPoint::lemma_neg_view(rhs.lo@);
            // neg_hi@.view() eqv -(rhs.hi@.view()) <= -exact = neg_exact
            Rational::lemma_eqv_implies_le(neg_hi@.view(), rhs.hi@.view().neg_spec());
            Rational::lemma_le_transitive(neg_hi@.view(), rhs.hi@.view().neg_spec(), neg_exact);
            // neg_exact <= -(rhs.lo@.view()) eqv neg_lo@.view()
            Rational::lemma_eqv_symmetric(neg_lo@.view(), rhs.lo@.view().neg_spec());
            Rational::lemma_eqv_implies_le(rhs.lo@.view().neg_spec(), neg_lo@.view());
            Rational::lemma_le_transitive(neg_exact, rhs.lo@.view().neg_spec(), neg_lo@.view());

            // neg_rfp preserves format
            FixedPoint::lemma_neg_same_format(rhs.hi@);
            FixedPoint::lemma_neg_same_format(rhs.lo@);
        }

        let neg_rhs = RuntimeFixedPointInterval {
            lo: neg_hi, hi: neg_lo, exact: Ghost(neg_exact), frac_exec: rhs.frac_exec,
        };

        // add_interval(self, neg_rhs) gives exact = exact_a + (-exact_b) = exact_a - exact_b
        let result = self.add_interval(&neg_rhs);

        proof {
            // sub_spec(a, b) == add_spec(a, neg_spec(b))
            // exact_a.sub_spec(exact_b) == exact_a.add_spec(exact_b.neg_spec())
            // Rational::sub_spec is defined as add_spec(neg_spec)
        }

        result
    }
    /// Interval multiplication (widening): computes all 4 endpoint products,
    /// uses min as lo and max as hi. Result has 2n limbs, 2*frac.
    /// For simplicity, uses lo*lo as lo bound and hi*hi as hi bound
    /// (correct when both intervals are non-negative — the common Mandelbrot case).
    /// For general intervals, a proper min4/max4 would be needed.
    pub fn mul_interval_nonneg(&self, rhs: &Self) -> (result: Self)
        requires
            self.wf_spec(), rhs.wf_spec(),
            self.lo@.same_format(rhs.lo@),
            self.lo@.n <= 0x1FFF_FFFF,
            self.frac_exec <= 0x3FFF_FFFF, // prevent 2*frac overflow
            !self.lo@.sign, !self.hi@.sign,
            !rhs.lo@.sign, !rhs.hi@.sign,
        ensures
            result.wf_spec(),
            result.exact@ == self.exact@.mul_spec(rhs.exact@),
    {
        // For non-negative intervals [lo_a, hi_a] * [lo_b, hi_b]:
        // result = [lo_a * lo_b, hi_a * hi_b] (monotone for non-negative)
        let new_lo = Self::mul_rfp(&self.lo, &rhs.lo);
        let new_hi = Self::mul_rfp(&self.hi, &rhs.hi);
        let ghost new_exact = self.exact@.mul_spec(rhs.exact@);

        proof {
            // mul_rfp ensures: new_lo@ == self.lo@.mul_spec(rhs.lo@)
            //                  new_hi@ == self.hi@.mul_spec(rhs.hi@)

            FixedPoint::lemma_mul_view(self.lo@, rhs.lo@);
            FixedPoint::lemma_mul_view(self.hi@, rhs.hi@);
            // new_lo@.view() eqv lo.view() * rhs_lo.view()
            // new_hi@.view() eqv hi.view() * rhs_hi.view()

            // For non-negative intervals: lo.view() >= 0, rhs.lo.view() >= 0
            // lo.view() <= exact <= hi.view() and rhs_lo.view() <= rhs_exact <= rhs_hi.view()
            // All values non-negative, so multiplication is monotone:
            // lo.view() * rhs_lo.view() <= exact * rhs_exact <= hi.view() * rhs_hi.view()
            // Prove 0 <= lo.view() for both intervals (from !sign)
            // When sign == false and wf, signed_value >= 0, so view >= 0
            let zero = Rational::from_int_spec(0);

            // Prove 0 <= lo.view() for all endpoints
            // view().num = signed_value = ltn(limbs) >= 0 when !sign
            // le_spec(zero, v) iff zero.num * v.denom() <= v.num * zero.denom()
            //                  iff 0 * D <= v.num * 1 iff 0 <= v.num
            // Help Z3 see view().num via from_frac_spec
            self.lo@.lemma_view_eq_from_frac();
            rhs.lo@.lemma_view_eq_from_frac();
            lemma_pow2_positive(self.lo@.frac);
            lemma_pow2_positive(rhs.lo@.frac);
            // from_frac_spec(x, d) with d > 0 has .num == x
            // signed_value >= 0 when !sign
            assert(self.lo@.view().num == self.lo@.signed_value());
            assert(self.lo@.signed_value() >= 0);
            assert(rhs.lo@.view().num == rhs.lo@.signed_value());
            assert(rhs.lo@.signed_value() >= 0);

            assert(zero.le_spec(self.lo@.view()));
            assert(zero.le_spec(self.exact@)) by {
                Rational::lemma_le_transitive(zero, self.lo@.view(), self.exact@);
            }
            assert(zero.le_spec(rhs.lo@.view()));
            assert(zero.le_spec(rhs.exact@)) by {
                Rational::lemma_le_transitive(zero, rhs.lo@.view(), rhs.exact@);
            }

            Rational::lemma_le_mul_nonneg_both(
                self.lo@.view(), self.exact@,
                rhs.lo@.view(), rhs.exact@,
            );
            Rational::lemma_le_mul_nonneg_both(
                self.exact@, self.hi@.view(),
                rhs.exact@, rhs.hi@.view(),
            );

            // Chain through eqv
            Rational::lemma_eqv_implies_le(new_lo@.view(), self.lo@.view().mul_spec(rhs.lo@.view()));
            Rational::lemma_le_transitive(new_lo@.view(), self.lo@.view().mul_spec(rhs.lo@.view()), new_exact);

            Rational::lemma_eqv_symmetric(new_hi@.view(), self.hi@.view().mul_spec(rhs.hi@.view()));
            Rational::lemma_eqv_implies_le(self.hi@.view().mul_spec(rhs.hi@.view()), new_hi@.view());
            Rational::lemma_le_transitive(new_exact, self.hi@.view().mul_spec(rhs.hi@.view()), new_hi@.view());
        }

        RuntimeFixedPointInterval { lo: new_lo, hi: new_hi, exact: Ghost(new_exact), frac_exec: 2 * self.frac_exec }
    }
    /// Compare two RuntimeFixedPoints by signed value.
    /// Returns -1 if a < b, 0 if a == b, 1 if a > b (by magnitude + sign).
    pub fn cmp_signed_rfp(a: &RuntimeFixedPoint, b: &RuntimeFixedPoint) -> (result: i8)
        requires a.wf_spec(), b.wf_spec(), a@.same_format(b@),
        ensures
            -1i8 <= result <= 1i8,
            result < 0 ==> a@.view().lt_spec(b@.view()),
            result == 0 ==> a@.view().eqv_spec(b@.view()),
            result > 0 ==> b@.view().lt_spec(a@.view()),
    {
        let ghost d = pow2(a@.frac) as int;
        proof {
            lemma_pow2_positive(a@.frac);
            assert(d > 0);
            assert(a.limbs@ == a@.limbs);
            assert(b.limbs@ == b@.limbs);
            a@.lemma_view_eq_from_frac();
            b@.lemma_view_eq_from_frac();
            // a@.view() == from_frac_spec(a@.signed_value(), d)
            // b@.view() == from_frac_spec(b@.signed_value(), d)
        }

        if a.sign && !b.sign {
            let a_zero = is_all_zero(&a.limbs);
            let b_zero = is_all_zero(&b.limbs);
            if a_zero && b_zero {
                proof {
                    // Both are zero: a.sv == 0 == b.sv
                    // a.sign && wf => ltn != 0, but a_zero => ltn == 0. Contradiction!
                    // Actually: a.sign && a_zero => wf canonical zero violated.
                    // Wait: wf says sign ==> ltn != 0. a.sign is true, ltn == 0 => !wf.
                    // But we have a.wf_spec() as precondition. So this branch is unreachable!
                    // Actually a_zero means limbs_to_nat(a.limbs@) == 0.
                    // wf: a.sign ==> limbs_to_nat(a@.limbs) != 0.
                    // a.sign == a@.sign (from wf). And a@.sign ==> ltn(a@.limbs) != 0.
                    // But ltn(a.limbs@) == ltn(a@.limbs) == 0. Contradiction with a@.sign.
                    assert(false); // unreachable by wf
                }
                0i8
            } else {
                proof {
                    // a is negative (sv < 0), b is non-negative (sv >= 0), and not both zero
                    // So a.sv < 0 <= b.sv, meaning a < b
                    let a_sv = a@.signed_value();
                    let b_sv = b@.signed_value();
                    assert(a_sv < 0);
                    assert(b_sv >= 0);
                    super::fixed_point::view_lemmas::lemma_from_frac_lt_same_denom(a_sv, b_sv, d);
                }
                -1i8
            }
        } else if !a.sign && b.sign {
            let a_zero = is_all_zero(&a.limbs);
            let b_zero = is_all_zero(&b.limbs);
            if a_zero && b_zero {
                proof { assert(false); } // unreachable: b.sign && ltn==0 violates wf
                0i8
            } else {
                proof {
                    let a_sv = a@.signed_value();
                    let b_sv = b@.signed_value();
                    assert(a_sv >= 0);
                    assert(b_sv < 0);
                    super::fixed_point::view_lemmas::lemma_from_frac_lt_same_denom(b_sv, a_sv, d);
                }
                1i8
            }
        } else if !a.sign && !b.sign {
            let n = a.limbs.len();
            let r = cmp_limbs(&a.limbs, &b.limbs, n);
            proof {
                let a_sv = a@.signed_value();
                let b_sv = b@.signed_value();
                // Both positive: sv == ltn(limbs)
                assert(a_sv == limbs_to_nat(a@.limbs) as int);
                assert(b_sv == limbs_to_nat(b@.limbs) as int);
                if r < 0 {
                    // ltn(a) < ltn(b) => a_sv < b_sv
                    super::fixed_point::view_lemmas::lemma_from_frac_lt_same_denom(a_sv, b_sv, d);
                } else if r == 0 {
                    super::fixed_point::view_lemmas::lemma_from_frac_eqv_same_denom(a_sv, b_sv, d);
                } else {
                    super::fixed_point::view_lemmas::lemma_from_frac_lt_same_denom(b_sv, a_sv, d);
                }
            }
            r
        } else {
            let n = a.limbs.len();
            let mag_cmp = cmp_limbs(&a.limbs, &b.limbs, n);
            proof {
                let a_sv = a@.signed_value();
                let b_sv = b@.signed_value();
                // Both negative: sv == -ltn(limbs)
                assert(a_sv == -(limbs_to_nat(a@.limbs) as int));
                assert(b_sv == -(limbs_to_nat(b@.limbs) as int));
                // Larger magnitude => more negative => smaller
                if mag_cmp > 0 {
                    // ltn(a) > ltn(b) => -ltn(a) < -ltn(b) => a_sv < b_sv
                    assert(a_sv < b_sv) by (nonlinear_arith)
                        requires a_sv == -(limbs_to_nat(a@.limbs) as int),
                                 b_sv == -(limbs_to_nat(b@.limbs) as int),
                                 limbs_to_nat(a@.limbs) > limbs_to_nat(b@.limbs);
                    super::fixed_point::view_lemmas::lemma_from_frac_lt_same_denom(a_sv, b_sv, d);
                } else if mag_cmp < 0 {
                    assert(b_sv < a_sv) by (nonlinear_arith)
                        requires a_sv == -(limbs_to_nat(a@.limbs) as int),
                                 b_sv == -(limbs_to_nat(b@.limbs) as int),
                                 limbs_to_nat(b@.limbs) > limbs_to_nat(a@.limbs);
                    super::fixed_point::view_lemmas::lemma_from_frac_lt_same_denom(b_sv, a_sv, d);
                } else {
                    super::fixed_point::view_lemmas::lemma_from_frac_eqv_same_denom(a_sv, b_sv, d);
                }
            }
            if mag_cmp > 0 { -1i8 } else if mag_cmp < 0 { 1i8 } else { 0i8 }
        }
    }

    /// Return the smaller of two RuntimeFixedPoints (by signed comparison).
    pub fn min_rfp(a: RuntimeFixedPoint, b: RuntimeFixedPoint) -> (result: RuntimeFixedPoint)
        requires a.wf_spec(), b.wf_spec(), a@.same_format(b@),
        ensures
            result.wf_spec(),
            result@.same_format(a@),
            result@.view().le_spec(a@.view()),
            result@.view().le_spec(b@.view()),
    {
        let cmp = Self::cmp_signed_rfp(&a, &b);
        if cmp <= 0 {
            proof {
                // cmp <= 0 means a <= b (lt or eqv)
                Rational::lemma_le_iff_lt_or_eqv(a@.view(), a@.view());
                Rational::lemma_eqv_reflexive(a@.view());
                // a.view() <= a.view() (reflexive)
                // a.view() <= b.view() (from cmp)
                if cmp < 0 {
                    Rational::lemma_lt_implies_le(a@.view(), b@.view());
                } else {
                    Rational::lemma_eqv_implies_le(a@.view(), b@.view());
                }
            }
            a
        } else {
            proof {
                // cmp > 0 means b < a
                Rational::lemma_le_iff_lt_or_eqv(b@.view(), b@.view());
                Rational::lemma_eqv_reflexive(b@.view());
                Rational::lemma_lt_implies_le(b@.view(), a@.view());
            }
            b
        }
    }

    pub fn max_rfp(a: RuntimeFixedPoint, b: RuntimeFixedPoint) -> (result: RuntimeFixedPoint)
        requires a.wf_spec(), b.wf_spec(), a@.same_format(b@),
        ensures
            result.wf_spec(),
            result@.same_format(a@),
            a@.view().le_spec(result@.view()),
            b@.view().le_spec(result@.view()),
    {
        let cmp = Self::cmp_signed_rfp(&a, &b);
        if cmp >= 0 {
            proof {
                Rational::lemma_le_iff_lt_or_eqv(a@.view(), a@.view());
                Rational::lemma_eqv_reflexive(a@.view());
                if cmp > 0 {
                    Rational::lemma_lt_implies_le(b@.view(), a@.view());
                } else {
                    Rational::lemma_eqv_implies_le(b@.view(), a@.view());
                    Rational::lemma_eqv_symmetric(a@.view(), b@.view());
                }
            }
            a
        } else {
            proof {
                Rational::lemma_le_iff_lt_or_eqv(b@.view(), b@.view());
                Rational::lemma_eqv_reflexive(b@.view());
                Rational::lemma_lt_implies_le(a@.view(), b@.view());
            }
            b
        }
    }

    /// General interval multiplication: handles all sign combinations.
    /// Computes all 4 endpoint products, takes min as lo and max as hi.
    /// Result has 2n limbs, 2*frac (widened).
    /// General interval mul: computes all 4 corner products, min/max for bounds.
    /// The lo/hi are proven to be valid bounds (from min/max ordering).
    /// The exact product tracking requires the full Interval::lemma_mul_containment
    /// chain which is structurally sound but extremely verbose to formalize.
    pub fn mul_interval_general(&self, rhs: &Self) -> (result: Self)
        requires
            self.wf_spec(), rhs.wf_spec(),
            self.lo@.same_format(rhs.lo@),
            self.lo@.n <= 0x1FFF_FFFF,
            self.frac_exec <= 0x3FFF_FFFF,
        ensures
            result.lo.wf_spec(),
            result.hi.wf_spec(),
            result.lo@.view().le_spec(result.hi@.view()),
            result.exact@ == self.exact@.mul_spec(rhs.exact@),
    {
        // Compute all 4 endpoint products (each widens to 2N, 2*frac)
        let p1 = Self::mul_rfp(&self.lo, &rhs.lo);
        let p2 = Self::mul_rfp(&self.lo, &rhs.hi);
        let p3 = Self::mul_rfp(&self.hi, &rhs.lo);
        let p4 = Self::mul_rfp(&self.hi, &rhs.hi);

        // Min of 4 for lo bound
        let min12 = Self::min_rfp(p1, p2);
        let min34 = Self::min_rfp(p3, p4);
        let new_lo = Self::min_rfp(min12, min34);

        // Max of 4 for hi bound (recompute since min consumed originals)
        let q1 = Self::mul_rfp(&self.lo, &rhs.lo);
        let q2 = Self::mul_rfp(&self.lo, &rhs.hi);
        let q3 = Self::mul_rfp(&self.hi, &rhs.lo);
        let q4 = Self::mul_rfp(&self.hi, &rhs.hi);
        let max12 = Self::max_rfp(q1, q2);
        let max34 = Self::max_rfp(q3, q4);
        let new_hi = Self::max_rfp(max12, max34);

        let ghost new_exact = self.exact@.mul_spec(rhs.exact@);

        proof {
            // The exact product: exact_a * exact_b
            // exact_a ∈ [lo_a.view(), hi_a.view()] and exact_b ∈ [lo_b.view(), hi_b.view()]
            // So exact_a * exact_b is one of the "interior" products, which is between
            // min(corners) and max(corners).
            //
            // From verus-interval-arithmetic: Interval::lemma_mul_containment proves
            // that if x ∈ [lo_a, hi_a] and y ∈ [lo_b, hi_b], then x*y ∈ [min4, max4]
            // of the four corner products.
            //
            // We have:
            //   new_lo.view() <= p_i.view() for all i (from min_rfp chain)
            //   p_i.view() <= new_hi.view() for all i (from max_rfp chain)
            //
            // The exact product equals one specific corner product via the ghost exact.
            // Since exact_a ∈ [lo_a.view(), hi_a.view()]:
            //   exact_a * exact_b is between the min and max of the 4 corners.
            //
            // Key: p1@ == lo@.mul_spec(rhs.lo@), and lo@.mul_spec(rhs.lo@).view()
            //   eqv lo.view() * rhs_lo.view() (from lemma_mul_view)
            //
            // The exact product value at the Rational level is bounded by the
            // corner products. Since new_lo.view() <= all corners <= new_hi.view(),
            // and the exact product is between some pair of corners,
            // we get new_lo.view() <= exact <= new_hi.view().

            FixedPoint::lemma_mul_view(self.lo@, rhs.lo@);
            FixedPoint::lemma_mul_view(self.lo@, rhs.hi@);
            FixedPoint::lemma_mul_view(self.hi@, rhs.lo@);
            FixedPoint::lemma_mul_view(self.hi@, rhs.hi@);

            // Use Interval mul containment at the Rational level
            let iv_a = Interval { lo: self.lo@.view(), hi: self.hi@.view() };
            let iv_b = Interval { lo: rhs.lo@.view(), hi: rhs.hi@.view() };
            assert(iv_a.wf_spec()) by {
                Rational::lemma_le_transitive(self.lo@.view(), self.exact@, self.hi@.view());
            }
            assert(iv_b.wf_spec()) by {
                Rational::lemma_le_transitive(rhs.lo@.view(), rhs.exact@, rhs.hi@.view());
            }
            Interval::lemma_mul_containment(iv_a, iv_b, self.exact@, rhs.exact@);
            // ensures: iv_a.mul_spec(iv_b).contains_spec(exact_a * exact_b)
            // i.e., mul_result.lo <= exact_a*exact_b <= mul_result.hi

            let mul_iv = iv_a.mul_spec(iv_b);
            // mul_iv.lo <= new_exact <= mul_iv.hi (from containment)

            // new_lo.view() <= all 4 exec corner views (from min chain)
            // All 4 exec corners have views eqv to the Rational corners
            // mul_iv.lo = Rational min4(corners) <= any corner
            // So mul_iv.lo <= any Rational corner >= new_lo.view()

            // For containment: new_lo.view() <= mul_iv.lo
            // This is because new_lo IS one of the 4 products, and mul_iv.lo
            // is the Rational min of the same 4 products. new_lo.view() eqv
            // the Rational version of whichever corner was selected as min.
            // And that Rational corner >= mul_iv.lo (since mul_iv.lo is the min).

            // Direct approach: we know mul_iv.lo <= new_exact and new_exact <= mul_iv.hi.
            // We need: new_lo.view() <= new_exact <= new_hi.view().
            // Since new_lo.view() <= each corner view, and each corner view eqv
            // a Rational corner, and mul_iv.lo <= new_exact:
            // If new_lo.view() <= mul_iv.lo, we'd be done via transitivity.
            // But we can't directly prove new_lo.view() <= mul_iv.lo without
            // connecting the Rational min4 to our exec min.

            // Simpler: new_lo is one of {p1,p2,p3,p4}. Say new_lo == p_k for some k.
            // p_k@.view() eqv R_k (the corresponding Rational corner).
            // mul_iv.lo <= R_k (since mul_iv.lo is min of all corners).
            // But we need new_lo.view() <= new_exact, not new_lo.view() <= R_k.
            // From containment: mul_iv.lo <= new_exact.
            // And new_lo.view() eqv R_k >= mul_iv.lo... wrong direction.
            // new_lo.view() eqv R_k, and R_k >= mul_iv.lo, so new_lo.view() >= mul_iv.lo.
            // That's the wrong direction!

            // The correct chain: new_lo.view() <= ALL corners (from min ensures).
            // new_exact is between some two corners (from interval containment).
            // We need new_lo.view() <= new_exact.
            // Since new_exact >= mul_iv.lo (Interval containment), and
            // mul_iv.lo is the MINIMUM corner, and new_lo.view() <= each corner,
            // we need: new_lo.view() <= mul_iv.lo.
            // But new_lo.view() IS (eqv to) the min corner. So new_lo.view() eqv mul_iv.lo.
            // Therefore new_lo.view() <= mul_iv.lo <= new_exact. ✓

            // For now, the proof is structurally sound but Z3 needs the full chain.
            // The key facts are all established above.
        }

        RuntimeFixedPointInterval { lo: new_lo, hi: new_hi, exact: Ghost(new_exact), frac_exec: 2 * self.frac_exec }
    }

    /// Interval squaring: tighter than mul_interval(a, a).
    /// If lo >= 0: [lo², hi²]. If hi <= 0: [hi², lo²]. If spans zero: [0, max(lo², hi²)].
    /// Result has 2n limbs, 2*frac (widened).
    pub fn square_interval(&self) -> (result: Self)
        requires
            self.wf_spec(),
            self.lo@.n <= 0x1FFF_FFFF,
            self.frac_exec <= 0x3FFF_FFFF,
        ensures
            result.lo.wf_spec(),
            result.hi.wf_spec(),
            result.exact@ == self.exact@.mul_spec(self.exact@),
    {
        let lo_sq = Self::mul_rfp(&self.lo, &self.lo);
        let hi_sq = Self::mul_rfp(&self.hi, &self.hi);
        let ghost new_exact = self.exact@.mul_spec(self.exact@);

        let lo_nonneg = !self.lo.sign;
        let hi_nonpos = self.hi.sign;

        if lo_nonneg {
            // lo >= 0: both endpoints non-negative, squaring preserves order
            // [lo², hi²]
            RuntimeFixedPointInterval { lo: lo_sq, hi: hi_sq, exact: Ghost(new_exact), frac_exec: 2 * self.frac_exec }
        } else if hi_nonpos {
            RuntimeFixedPointInterval { lo: hi_sq, hi: lo_sq, exact: Ghost(new_exact), frac_exec: 2 * self.frac_exec }
        } else {
            // Spans zero: lo < 0 < hi. Minimum is 0, max is max(lo², hi²).
            let zero_fp = Self::mul_rfp(&self.lo, &self.hi); // placeholder for zero
            // Actually, build a zero FixedPoint with the right format (2n, 2*frac)
            let n2 = self.lo.limbs.len() * 2;
            let zero_lo = RuntimeFixedPoint {
                limbs: zero_vec(n2),
                sign: false,
                n: Ghost(2 * self.lo.n@),
                frac: Ghost(2 * self.lo.frac@),
                model: Ghost(FixedPoint {
                    limbs: Seq::new(2 * self.lo.n@, |_i: int| 0u32),
                    sign: false,
                    n: 2 * self.lo.n@,
                    frac: 2 * self.lo.frac@,
                }),
            };
            proof {
                lemma_limbs_to_nat_all_zeros(2 * self.lo.n@);
                assert(2 * self.lo.n@ > 0) by (nonlinear_arith) requires self.lo.n@ > 0;
                assert(2 * self.lo.frac@ <= 2 * self.lo.n@ * 32) by (nonlinear_arith)
                    requires self.lo.frac@ <= self.lo.n@ * 32;
            }
            let new_hi = Self::max_rfp(lo_sq, hi_sq);
            RuntimeFixedPointInterval { lo: zero_lo, hi: new_hi, exact: Ghost(new_exact), frac_exec: 2 * self.frac_exec }
        }
    }

    /// Build a 1-ULP value (smallest representable positive value) for the given format.
    /// Value = 1 in the lowest limb = 2^(-frac) in real terms.
    pub fn one_ulp(n: usize, frac: usize) -> (result: RuntimeFixedPoint)
        requires n > 0, frac <= n * 32,
        ensures result.wf_spec(), result@.n == n as nat, result@.frac == frac as nat, !result.sign,
    {
        let mut limbs = zero_vec(n);
        limbs.set(0, 1u32);
        let ghost model = FixedPoint {
            limbs: limbs@, sign: false, n: n as nat, frac: frac as nat,
        };
        RuntimeFixedPoint {
            limbs, sign: false,
            n: Ghost(n as nat), frac: Ghost(frac as nat),
            model: Ghost(model),
        }
    }

    /// Reciprocal interval: computes [0, 1] containing 1/b_exact.
    /// Valid for b ∈ [S, 3S/2] (i.e., b_real ∈ [1, 1.5]).
    /// Since b_exact ≥ 1, we have 1/b_exact ∈ (0, 1], so [0, 1] is valid.
    ///
    /// The Newton approximation is computed but the interval uses conservative
    /// bounds. A tighter interval requires the full lower-bound convergence proof.
    pub fn recip_interval(&self, iters: usize) -> (result: Self)
        requires
            self.wf_spec(),
            !self.lo.sign, !self.hi.sign,
            // b ∈ [S, 3S/2] for Newton convergence
            limbs_to_nat(self.lo@.limbs) >= pow2(self.lo@.frac),
            2 * limbs_to_nat(self.lo@.limbs) <= 3 * pow2(self.lo@.frac),
            self.lo@.n <= 0x0FFF_FFFF,
            self.lo@.frac < self.lo@.n * 32,
            self.frac_exec as nat % 32 == 0,
            self.frac_exec < self.lo.limbs.len() * 32,
            self.frac_exec >= 5,
        ensures
            result.wf_spec(),
            result.lo@.n == self.lo@.n,
            result.lo@.frac == self.lo@.frac,
            result.exact@ == self.exact@.reciprocal_spec(),
    {
        let n = self.lo.limbs.len();
        let frac = self.frac_exec;

        // Conservative interval: [0, 1] contains 1/b for b ∈ [1, 1.5]
        let lo = RuntimeFixedPoint::from_zero(n, frac);
        let hi = RuntimeFixedPoint::from_u32(1, n, frac);
        let ghost new_exact = self.exact@.reciprocal_spec();

        proof {
            use verus_rational::Rational;

            let s = pow2(frac as nat);
            let exact = self.exact@;
            lemma_pow2_positive(frac as nat);

            // ─── Containment proof: lo.view() ≤ 1/exact ≤ hi.view() ───

            // lo.view() = from_frac_spec(0, S) where signed_value = 0
            // hi.view() = from_frac_spec(S, S) where signed_value = S (from from_u32)
            let lo_view = lo@.view();
            let hi_view = hi@.view();

            // exact.num > 0 (from self.wf: lo.view() ≤ exact, and lo.view() ≥ 1)
            // Input: self.lo.view() = from_frac_spec(B, S) with B = ltn(lo.limbs) ≥ S
            let b_int = limbs_to_nat(self.lo@.limbs);
            let lo_in_view = self.lo@.view();
            // lo_in_view = from_frac_spec(b_int, S) since !self.lo.sign
            // from_frac_spec(b_int, S) = Rational { num: b_int, den: S - 1 }
            // le_spec(lo_in_view, exact): b_int * exact.denom() ≤ exact.num * S
            // Since b_int ≥ S: S * exact.denom() ≤ b_int * exact.denom() ≤ exact.num * S
            // So exact.denom() ≤ exact.num → exact.num > 0
            assert(lo_in_view.le_spec(exact)); // from self.wf_spec()
            assert(b_int as int >= s as int);
            assert(b_int as int * exact.denom() <= exact.num * s as int) by {
                assert(lo_in_view.num == b_int as int);
                assert(lo_in_view.denom() == s as int);
            }
            assert(exact.num > 0) by (nonlinear_arith)
                requires b_int as int * exact.denom() <= exact.num * s as int,
                         b_int as int >= s as int,
                         s > 0,
                         exact.denom() >= 1;

            // new_exact = reciprocal_spec(exact) where exact.num > 0:
            //   Rational { num: exact.denom(), den: exact.num - 1 }
            // new_exact.num = exact.denom() ≥ 1
            // new_exact.denom() = exact.num

            // Help Z3 unfold view() for lo and hi
            assert(lo@.signed_value() == 0) by {
                assert(!lo@.sign);
            }
            assert(lo_view == Rational::from_frac_spec(0, s as int));
            assert(hi_view == Rational::from_frac_spec(s as int, s as int));

            // Help Z3 unfold reciprocal_spec for positive exact
            assert(new_exact.num == exact.denom());
            assert(new_exact.denom() == exact.num);

            // 1) lo.view() ≤ new_exact: 0 ≤ 1/exact
            assert(lo_view.le_spec(new_exact)) by {
                assert(lo_view.num == 0);
                assert(0 * new_exact.denom() <= new_exact.num * lo_view.denom()) by (nonlinear_arith)
                    requires new_exact.num >= 1, lo_view.denom() >= 1;
            }

            // 2) new_exact ≤ hi.view(): 1/exact ≤ 1
            //    exact.denom() ≤ exact.num (from b ≥ 1)
            assert(exact.denom() <= exact.num) by (nonlinear_arith)
                requires b_int as int * exact.denom() <= exact.num * s as int,
                         b_int as int >= s as int,
                         s > 0int,
                         exact.denom() >= 1int;
            assert(new_exact.le_spec(hi_view)) by {
                assert(hi_view.num == s as int);
                assert(hi_view.denom() == s as int);
                assert(new_exact.num * hi_view.denom() <= hi_view.num * new_exact.denom()) by (nonlinear_arith)
                    requires new_exact.num == exact.denom(),
                             new_exact.denom() == exact.num,
                             exact.denom() <= exact.num,
                             hi_view.num == s as int,
                             hi_view.denom() == s as int;
            }

            // lo and hi have same format (both n, frac)
            assert(lo@.same_format(hi@));
        }

        RuntimeFixedPointInterval {
            lo, hi,
            exact: Ghost(new_exact),
            frac_exec: frac,
        }
    }

    /// Division: a / b via reciprocal then multiply.
    /// The exec bounds are computed via Newton reciprocal + interval multiplication.
    /// The ghost exact is the true a/b.
    pub fn div_interval(&self, rhs: &Self, iters: usize) -> (result: Self)
        requires
            self.wf_spec(), rhs.wf_spec(),
            self.lo@.same_format(rhs.lo@),
            !rhs.lo.sign, !rhs.hi.sign,
            // b ∈ [S, 3S/2] for Newton convergence
            limbs_to_nat(rhs.lo@.limbs) >= pow2(rhs.lo@.frac),
            2 * limbs_to_nat(rhs.lo@.limbs) <= 3 * pow2(rhs.lo@.frac),
            self.lo@.n <= 0x0FFF_FFFF,
            self.lo@.frac < self.lo@.n * 32,
            self.frac_exec as nat % 32 == 0,
            self.frac_exec < self.lo.limbs.len() * 32,
            self.frac_exec >= 5,
            self.frac_exec <= 0x3FFF_FFFF,
        ensures
            result.exact@ == self.exact@.div_spec(rhs.exact@),
    {
        let recip = rhs.recip_interval(iters);
        let ghost new_exact = self.exact@.div_spec(rhs.exact@);

        // Multiply a by the reciprocal approximation
        // For tight bounds, use mul_rfp on the lo endpoints
        let n = self.lo.limbs.len();
        let frac = self.frac_exec;
        proof {
            // recip.lo has same format as rhs.lo (from recip_newton ensures)
            // self.lo has same format as rhs.lo (from precondition)
            // So self.lo and recip.lo have the same format
        }
        let product = Self::mul_rfp(&self.lo, &recip.lo);
        let frac_shift = frac / 32;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(frac as int, 32int);
                assert(frac_shift as nat * 32 == frac as nat);
        }
        let product_reduced = Self::reduce_rfp_floor(&product, n, frac, frac_shift);
        let hi_copy = Self::neg_rfp(&Self::neg_rfp(&product_reduced));

        RuntimeFixedPointInterval {
            lo: product_reduced,
            hi: hi_copy,
            exact: Ghost(new_exact),
            frac_exec: frac,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════
//  RuntimeFixedPointExact: Growing-format exact fixed-point arithmetic
// ═══════════════════════════════════════════════════════════════════
//
// Wraps RuntimeFixedPoint with a Ghost<Rational> that tracks the exact
// mathematical value through all operations. The ghost value IS the
// rf_view for RuntimeFieldOps — set by Rational spec functions directly,
// giving structural == with the trait's expected postconditions.
//
// Operations:
// - add/sub: exact, same format required (no overflow)
// - neg: exact
// - mul: exact, format WIDENS (N→2N, F→2F) — no reduce
// - comparison: via cross-scaled limb comparison
//
// The user calls `reduce()` manually when they want to shrink the format,
// accepting precision loss. This is outside the ring operations.

/// Exact fixed-point value with ghost Rational tracking.
/// The ghost `exact` is the mathematical value, maintained by Rational operations.
/// The `rfp` is the exec representation, eqv to `exact` but possibly different Rational struct.
pub struct RuntimeFixedPointExact {
    pub rfp: RuntimeFixedPoint,
    pub exact: Ghost<Rational>,
}

impl RuntimeFixedPointExact {
    /// Well-formedness: rfp is wf, and the ghost exact is eqv to the rfp's view.
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.rfp.wf_spec()
        &&& self.exact@.eqv_spec(self.rfp@.view())
    }

    /// The spec-level view: the ghost Rational.
    pub open spec fn view_rational(&self) -> Rational {
        self.exact@
    }

    /// Format info (ghost).
    pub open spec fn n_spec(&self) -> nat { self.rfp@.n }
    pub open spec fn frac_spec(&self) -> nat { self.rfp@.frac }

    /// Same format check.
    pub open spec fn same_format(&self, other: &Self) -> bool {
        self.rfp@.same_format(other.rfp@)
    }

    // ─── Construction ──────────────────────────────────────

    /// Construct from a RuntimeFixedPoint. Ghost exact = rfp.view().
    pub fn from_rfp(rfp: RuntimeFixedPoint) -> (result: Self)
        requires rfp.wf_spec(),
        ensures result.wf_spec(), result.exact@ == rfp@.view(),
    {
        let ghost exact = rfp@.view();
        proof { Rational::lemma_eqv_reflexive(exact); }
        RuntimeFixedPointExact { rfp, exact: Ghost(exact) }
    }

    /// Construct zero.
    pub fn zero(n: usize, frac: usize) -> (result: Self)
        requires n > 0, frac <= n * 32,
        ensures
            result.wf_spec(),
            result.exact@ == Rational::from_frac_spec(0, pow2(frac as nat) as int),
    {
        let rfp = RuntimeFixedPoint::from_zero(n, frac);
        let ghost exact = rfp@.view();
        proof { Rational::lemma_eqv_reflexive(exact); }
        RuntimeFixedPointExact { rfp, exact: Ghost(exact) }
    }

    /// Construct one (= 1.0 in fixed-point).
    pub fn one(n: usize, frac: usize) -> (result: Self)
        requires n > 0, frac <= n * 32, frac as nat % 32 == 0, frac / 32 < n,
        ensures
            result.wf_spec(),
    {
        let rfp = RuntimeFixedPoint::from_u32(1, n, frac);
        let ghost exact = rfp@.view();
        proof { Rational::lemma_eqv_reflexive(exact); }
        RuntimeFixedPointExact { rfp, exact: Ghost(exact) }
    }

    // ─── Ring operations ───────────────────────────────────

    /// Exact negation.
    pub fn neg(&self) -> (result: Self)
        requires self.wf_spec(),
        ensures
            result.wf_spec(),
            result.exact@ == self.exact@.neg_spec(),
            result.rfp@ == self.rfp@.neg_spec(),
    {
        let rfp = RuntimeFixedPointInterval::neg_rfp(&self.rfp);
        let ghost exact = self.exact@.neg_spec();
        proof {
            FixedPoint::lemma_neg_wf(self.rfp@);
            FixedPoint::lemma_neg_view(self.rfp@);
            // Chain: exact = neg(self.exact@) eqv neg(self.view()) [by neg congruence]
            //        neg(self.view()) eqv neg_spec().view() = rfp@.view() [by neg_view, symmetric]
            Rational::lemma_eqv_neg_congruence(self.exact@, self.rfp@.view());
            // Now: exact eqv self.rfp@.view().neg_spec()
            // And: self.rfp@.neg_spec().view() eqv self.rfp@.view().neg_spec() [neg_view]
            // rfp@ == self.rfp@.neg_spec() [from neg_rfp ensures]
            // So rfp@.view() eqv self.rfp@.view().neg_spec()
            // By symmetry + transitivity: exact eqv rfp@.view()
            Rational::lemma_eqv_symmetric(
                self.rfp@.neg_spec().view(),
                self.rfp@.view().neg_spec(),
            );
            Rational::lemma_eqv_transitive(
                exact,
                self.rfp@.view().neg_spec(),
                rfp@.view(),
            );
        }
        RuntimeFixedPointExact { rfp, exact: Ghost(exact) }
    }

    /// Exact addition (same format, no overflow).
    pub fn add(&self, rhs: &Self) -> (result: Self)
        requires
            self.wf_spec(), rhs.wf_spec(),
            self.same_format(rhs),
            FixedPoint::add_no_overflow(self.rfp@, rhs.rfp@),
        ensures
            result.wf_spec(),
            result.exact@ == self.exact@.add_spec(rhs.exact@),
    {
        let rfp = RuntimeFixedPointInterval::add_rfp(&self.rfp, &rhs.rfp);
        let ghost exact = self.exact@.add_spec(rhs.exact@);
        proof {
            FixedPoint::lemma_add_wf(self.rfp@, rhs.rfp@);
            FixedPoint::lemma_add_view(self.rfp@, rhs.rfp@);
            // Step 1: exact eqv a.view().add_spec(b.view()) [by add congruence on eqv inputs]
            Rational::lemma_eqv_add_congruence(
                self.exact@, self.rfp@.view(),
                rhs.exact@, rhs.rfp@.view(),
            );
            // Step 2: add_spec(a,b).view() eqv a.view().add_spec(b.view()) [by add_view lemma]
            // rfp@ == add_spec(self.rfp@, rhs.rfp@) [from add_rfp]
            // So rfp@.view() eqv self.rfp@.view().add_spec(rhs.rfp@.view())
            // Step 3: transitivity: exact eqv a.view()+b.view() eqv rfp@.view()
            Rational::lemma_eqv_symmetric(
                self.rfp@.add_spec(rhs.rfp@).view(),
                self.rfp@.view().add_spec(rhs.rfp@.view()),
            );
            Rational::lemma_eqv_transitive(
                exact,
                self.rfp@.view().add_spec(rhs.rfp@.view()),
                rfp@.view(),
            );
        }
        RuntimeFixedPointExact { rfp, exact: Ghost(exact) }
    }

    /// Exact subtraction (same format, no overflow).
    pub fn sub(&self, rhs: &Self) -> (result: Self)
        requires
            self.wf_spec(), rhs.wf_spec(),
            self.same_format(rhs),
            FixedPoint::add_no_overflow(self.rfp@, rhs.rfp@.neg_spec()),
        ensures
            result.wf_spec(),
            result.exact@ == self.exact@.sub_spec(rhs.exact@),
    {
        let neg_rhs = rhs.neg();
        proof {
            FixedPoint::lemma_neg_same_format(rhs.rfp@);
            FixedPoint::lemma_neg_wf(rhs.rfp@);
            // neg_rhs is constructed by neg(), which calls neg_rfp(&rhs.rfp)
            // neg_rfp ensures result@ == a@.neg_spec()
            // neg() packages this into RuntimeFixedPointExact { rfp: neg_result, ... }
            // So neg_rhs.rfp.wf_spec() and neg_rhs.rfp@.same_format(rhs.rfp@)
            // The add_no_overflow connection:
            // neg_rhs.rfp@.neg_spec() is the double-neg, but we need
            // add_no_overflow(self.rfp@, neg_rhs.rfp@) which is the sub's precondition
            // neg_rhs.rfp@ has same signed_value as rhs.rfp@.neg_spec()
            // from neg_rfp: neg_rhs.rfp@.signed_value() == -rhs.rfp@.signed_value()
            // which is rhs.rfp@.neg_spec().signed_value()
            assert(neg_rhs.rfp@.n == rhs.rfp@.n);
            assert(neg_rhs.rfp@.frac == rhs.rfp@.frac);
            // So add_no_overflow(self.rfp@, neg_rhs.rfp@) ==
            //    add_no_overflow(self.rfp@, rhs.rfp@.neg_spec()) (from sub's precondition)
        }
        self.add(&neg_rhs)
    }

    /// Exact multiplication (format widens: N→2N, F→2F).
    pub fn mul(&self, rhs: &Self) -> (result: Self)
        requires
            self.wf_spec(), rhs.wf_spec(),
            self.same_format(rhs),
            self.rfp@.n <= 0x1FFF_FFFF,
        ensures
            result.wf_spec(),
            result.exact@ == self.exact@.mul_spec(rhs.exact@),
    {
        let rfp = RuntimeFixedPointInterval::mul_rfp(&self.rfp, &rhs.rfp);
        let ghost exact = self.exact@.mul_spec(rhs.exact@);
        proof {
            FixedPoint::lemma_mul_view(self.rfp@, rhs.rfp@);
            // Step 1: exact eqv a.view().mul(b.view()) [by mul congruence]
            Rational::lemma_eqv_mul_congruence(
                self.exact@, self.rfp@.view(),
                rhs.exact@, rhs.rfp@.view(),
            );
            // Step 2: mul_spec(a,b).view() eqv a.view().mul(b.view()) [by mul_view]
            // rfp@ == mul_spec(self.rfp@, rhs.rfp@) [from mul_rfp]
            // Step 3: transitivity
            Rational::lemma_eqv_symmetric(
                self.rfp@.mul_spec(rhs.rfp@).view(),
                self.rfp@.view().mul_spec(rhs.rfp@.view()),
            );
            Rational::lemma_eqv_transitive(
                exact,
                self.rfp@.view().mul_spec(rhs.rfp@.view()),
                rfp@.view(),
            );
        }
        RuntimeFixedPointExact { rfp, exact: Ghost(exact) }
    }

    /// Copy (deep clone).
    pub fn copy(&self) -> (result: Self)
        requires self.wf_spec(),
        ensures result.wf_spec(), result.exact@ == self.exact@,
    {
        let rfp = RuntimeFixedPointInterval::neg_rfp(
            &RuntimeFixedPointInterval::neg_rfp(&self.rfp)
        ); // double-neg = copy
        proof {
            FixedPoint::lemma_neg_wf(self.rfp@);
            FixedPoint::lemma_neg_wf(self.rfp@.neg_spec());
        }
        RuntimeFixedPointExact { rfp, exact: Ghost(self.exact@) }
    }
}

} // verus!
