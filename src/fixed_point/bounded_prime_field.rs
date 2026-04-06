///  Bounded prime field: RuntimePrimeField wrapper with centered ordering.
///
///  Uses modular arithmetic internally (reusing all verified RuntimePrimeField ops)
///  but presents an integer-ordered view via centered representation:
///    values in [0, (p-1)/2] are positive, [(p+1)/2, p-1] are negative.
///
///  Each value carries a ghost bound: |centered_value| <= bound.
///  Operations track bounds dynamically:
///    add: output.bound = a.bound + b.bound
///    mul: output.bound = a.bound * b.bound
///  The add_wf/mul_wf preconditions ensure bounds stay < p/2 (no wrap).

use vstd::prelude::*;
use crate::fixed_point::prime_field::*;
use crate::fixed_point::limb_ops::*;
#[allow(unused_imports)]
use crate::fixed_point::modular::*;

verus! {

//  ══════════════════════════════════════════════════════════════
//  Centered representation
//  ══════════════════════════════════════════════════════════════

///  Map a reduced value in [0, p) to the centered range [-(p-1)/2, (p-1)/2].
///  Values <= (p-1)/2 stay as-is; values > (p-1)/2 map to value - p.
pub open spec fn centered(value: nat, p: nat) -> int {
    if value as int <= (p as int - 1) / 2 {
        value as int
    } else {
        value as int - p as int
    }
}

///  Map a centered value back to [0, p).
pub open spec fn uncentered(value: int, p: nat) -> nat {
    if value >= 0 {
        value as nat
    } else {
        (value + p as int) as nat
    }
}

///  Core lemma: when |a + b| < p/2, centered modular add equals integer add.
pub proof fn lemma_centered_add(a: nat, b: nat, p: nat)
    requires
        p > 2, p % 2 == 1,
        a < p, b < p,
        -((p as int - 1) / 2) <= centered(a, p) + centered(b, p),
        centered(a, p) + centered(b, p) <= (p as int - 1) / 2,
    ensures
        centered(((a + b) % p) as nat, p) == centered(a, p) + centered(b, p),
{
    let ca = centered(a, p);
    let cb = centered(b, p);
    let sum = ca + cb;
    let half = (p as int - 1) / 2;
    lemma_odd_half(p);
    //  The proof strategy: sum is in [-half, half].
    //  Its unique representative mod p is sum (if >= 0) or sum + p (if < 0).
    //  We show (a + b) % p equals this representative, then centering gives sum.
    if sum >= 0 {
        //  sum in [0, half]. Representative = sum.
        //  Need: (a + b) % p == sum, and sum <= half so centered = sum.
        //  Case split on a, b relative to half:
        if a as int <= half && b as int <= half {
            //  ca = a, cb = b. sum = a + b.
            //  a + b <= half < p, so (a+b)%p = a+b = sum, centered = sum. ✓
            assert((a + b) % p == a + b) by(nonlinear_arith)
                requires a + b <= half, half < p, p > 0;
        } else if a as int <= half {
            //  ca = a, cb = b - p. sum = a + b - p.
            //  sum >= 0 means a + b >= p. sum <= half means a + b - p <= half.
            //  (a+b) % p = a + b - p = sum. sum <= half so centered = sum. ✓
            assert(a + b >= p) by(nonlinear_arith)
                requires sum >= 0, sum == a as int + b as int - p as int;
            assert((a + b) % p == (a + b - p) as nat) by(nonlinear_arith)
                requires a + b >= p, a + b < 2 * p, p > 0;
        } else if b as int <= half {
            //  ca = a - p, cb = b. sum = a - p + b. Same as above, symmetric.
            assert(a + b >= p) by(nonlinear_arith)
                requires sum >= 0, sum == a as int - p as int + b as int;
            assert((a + b) % p == (a + b - p) as nat) by(nonlinear_arith)
                requires a + b >= p, a + b < 2 * p, p > 0;
        } else {
            //  ca = a - p, cb = b - p. sum = a + b - 2p.
            //  sum >= 0 means a + b >= 2p. But a < p, b < p, so a+b < 2p. Contradiction.
            assert(false) by(nonlinear_arith)
                requires sum >= 0, sum == a as int + b as int - 2 * p as int, a < p, b < p;
        }
    } else {
        //  sum in [-half, 0). Representative = sum + p, in (p - half, p).
        //  p - half > half (since p > 2*half), so centering gives (sum+p) - p = sum.
        if a as int <= half && b as int <= half {
            //  ca = a, cb = b, sum = a + b. But sum < 0 and a,b >= 0. Contradiction.
            assert(false) by(nonlinear_arith)
                requires sum < 0, sum == a as int + b as int, a >= 0, b >= 0;
        } else if a as int <= half {
            //  ca = a, cb = b - p. sum = a + b - p < 0, so a + b < p.
            //  (a+b)%p = a+b. centered(a+b, p): is a+b <= half?
            //  sum = a+b-p, and sum in [-half, 0), so a+b in [p-half, p).
            //  p - half > half, so a+b > half. centered = a+b-p = sum. ✓
            assert(a + b < p) by(nonlinear_arith)
                requires sum < 0, sum == a as int + b as int - p as int;
            assert((a + b) % p == a + b) by(nonlinear_arith)
                requires a + b < p, a + b >= 0, p > 0;
            assert(a + b > half) by(nonlinear_arith)
                requires sum == a as int + b as int - p as int, sum >= -half, p > 2 * half;
        } else if b as int <= half {
            //  Symmetric case
            assert(a + b < p) by(nonlinear_arith)
                requires sum < 0, sum == a as int - p as int + b as int;
            assert((a + b) % p == a + b) by(nonlinear_arith)
                requires a + b < p, a + b >= 0, p > 0;
            assert(a + b > half) by(nonlinear_arith)
                requires sum == a as int - p as int + b as int, sum >= -half, p > 2 * half;
        } else {
            //  ca = a-p, cb = b-p. sum = a+b-2p. sum < 0: a+b < 2p (always).
            //  sum >= -half: a+b >= 2p-half. So a+b >= p (since p > half).
            //  (a+b)%p = a+b-p. Is a+b-p <= half? sum+p = a+b-p, sum < 0, so a+b-p < p.
            //  a+b-p = sum + p. sum in [-half, 0), so a+b-p in [p-half, p). > half.
            //  centered = a+b-p-p = sum. ✓
            assert(a + b >= p) by(nonlinear_arith)
                requires sum >= -half, sum == a as int + b as int - 2 * p as int, p > 2 * half;
            assert((a + b) % p == (a + b - p) as nat) by(nonlinear_arith)
                requires a + b >= p, a + b < 2 * p, p > 0;
            assert((a + b - p) as int > half) by(nonlinear_arith)
                requires sum == a as int + b as int - 2 * p as int, sum >= -half, p > 2 * half;
        }
    }
}

///  Helper: for odd p > 2, establish p == 2*half + 1.
proof fn lemma_odd_half(p: nat)
    requires p > 2, p % 2 == 1,
    ensures (p as int - 1) / 2 >= 1, p as int == 2 * ((p as int - 1) / 2) + 1,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p as int - 1, 2);
    assert((p as int - 1) % 2 == 0) by(nonlinear_arith) requires p as int % 2 == 1, p > 2;
}

///  Centered negation: centered(p - a, p) == -centered(a, p) when a > 0.
pub proof fn lemma_centered_neg(a: nat, p: nat)
    requires p > 2, p % 2 == 1, a < p, a > 0,
    ensures centered((p - a) as nat, p) == -centered(a, p),
{
    let half = (p as int - 1) / 2;
    let neg_val = (p - a) as nat;
    lemma_odd_half(p);
    //  Now Z3 knows: p == 2*half + 1
    if a as int <= half {
        assert(centered(a, p) == a as int);
        assert(neg_val as int > half) by(nonlinear_arith)
            requires neg_val as int == p as int - a as int,
                a as int <= half, a > 0, p as int == 2 * half + 1;
        assert(centered(neg_val, p) == neg_val as int - p as int);
    } else {
        assert(centered(a, p) == a as int - p as int);
        assert(neg_val as int <= half) by(nonlinear_arith)
            requires neg_val as int == p as int - a as int,
                a as int > half, a < p, p as int == 2 * half + 1;
        assert(centered(neg_val, p) == neg_val as int);
    }
}

///  Centered zero is zero.
pub proof fn lemma_centered_zero(p: nat)
    requires p > 2,
    ensures centered(0nat, p) == 0int,
{
    assert((p as int - 1) / 2 >= 0) by(nonlinear_arith) requires p > 2;
}

///  Core lemma: when |a * b| < p/2, centered modular mul equals integer mul.
pub proof fn lemma_centered_mul(a: nat, b: nat, p: nat)
    requires
        p > 2, p % 2 == 1,
        a < p, b < p,
        -((p as int - 1) / 2) <= centered(a, p) * centered(b, p),
        centered(a, p) * centered(b, p) <= (p as int - 1) / 2,
    ensures
        centered(((a * b) % p) as nat, p) == centered(a, p) * centered(b, p),
{
    let ca = centered(a, p);
    let cb = centered(b, p);
    let prod = ca * cb;
    let half = (p as int - 1) / 2;
    //  Key: a ≡ ca (mod p), b ≡ cb (mod p), so a*b ≡ ca*cb (mod p).
    //  Since |prod| <= half, centered(prod mod p, p) == prod.
    //  Strategy: show a*b == prod + q*p for some integer q, then
    //  (a*b) % p == prod % p, and centering a value in [-half, half] gives itself.
    let ka: int = if a as int <= half { 0 } else { 1 };
    let kb: int = if b as int <= half { 0 } else { 1 };
    assert(a as int == ca + ka * (p as int)) by(nonlinear_arith)
        requires a < p, half == (p as int - 1) / 2,
            ca == if a as int <= half { a as int } else { a as int - p as int },
            ka == if a as int <= half { 0int } else { 1int };
    assert(b as int == cb + kb * (p as int)) by(nonlinear_arith)
        requires b < p, half == (p as int - 1) / 2,
            cb == if b as int <= half { b as int } else { b as int - p as int },
            kb == if b as int <= half { 0int } else { 1int };
    //  Case split on ka/kb (0 or 1) — each case is simple for nonlinear_arith
    let q: int = ka * cb + kb * ca + ka * kb * (p as int);
    if ka == 0 && kb == 0 {
        assert(a as int * b as int == prod + q * (p as int)) by(nonlinear_arith)
            requires a as int == ca, b as int == cb, prod == ca * cb, q == 0;
    } else if ka == 1 && kb == 0 {
        assert(a as int * b as int == prod + q * (p as int)) by(nonlinear_arith)
            requires a as int == ca + p as int, b as int == cb,
                prod == ca * cb, q == cb;
    } else if ka == 0 && kb == 1 {
        assert(a as int * b as int == prod + q * (p as int)) by(nonlinear_arith)
            requires a as int == ca, b as int == cb + p as int,
                prod == ca * cb, q == ca;
    } else {
        assert(a as int * b as int == prod + q * (p as int)) by(nonlinear_arith)
            requires a as int == ca + p as int, b as int == cb + p as int,
                prod == ca * cb, q == ca + cb + p as int;
    }
    //  (a*b) % p is the unique value in [0, p) congruent to a*b ≡ prod (mod p).
    //  Since |prod| <= half: representative is prod (if >= 0) or prod + p (if < 0).
    if prod >= 0 {
        //  prod in [0, half]. (a*b) % p == prod. centered(prod, p) = prod.
        assert((a * b) % p == prod as nat) by(nonlinear_arith)
            requires a as int * b as int == prod + q * (p as int), p > 0,
                0 <= prod, prod <= half, half < p;
    } else {
        //  prod in [-half, 0). (a*b) % p == prod + p. centered(prod+p, p) = prod.
        assert((a * b) % p == (prod + p as int) as nat) by(nonlinear_arith)
            requires a as int * b as int == prod + q * (p as int), p > 0,
                -half <= prod, prod < 0, half < p;
        assert((prod + p as int) as int > half) by(nonlinear_arith)
            requires prod >= -half, prod < 0, p > 2 * half;
    }
}

///  |centered(a, p)| <= (p-1)/2 always holds for a < p (odd p).
pub proof fn lemma_centered_bounded(a: nat, p: nat)
    requires p > 2, p % 2 == 1, a < p,
    ensures
        centered(a, p) >= -((p as int - 1) / 2),
        centered(a, p) <= (p as int - 1) / 2,
{
    let half = (p as int - 1) / 2;
    lemma_odd_half(p);
    if a as int <= half {
        assert(centered(a, p) == a as int);
    } else {
        assert(centered(a, p) == a as int - p as int);
        assert(a as int - p as int >= -half) by(nonlinear_arith)
            requires a as int > half, a < p, p as int == 2 * half + 1;
    }
}

//  ══════════════════════════════════════════════════════════════
//  BoundedPrimeField<N, C> — const-generic wrapper
//  ══════════════════════════════════════════════════════════════

///  RuntimePrimeField wrapper with centered integer view and dynamic bound tracking.
///  Const generics N (limbs) and C (Mersenne constant) fix the prime p = 2^(32*N) - C,
///  guaranteeing all wf values share the same field (critical for eq/le correctness).
pub struct BoundedPrimeField<const N: usize, const C: u32> {
    pub inner: RuntimePrimeField<u32>,
    pub bound: Ghost<nat>,
}

impl<const N: usize, const C: u32> BoundedPrimeField<N, C> {
    pub open spec fn prime_spec() -> nat {
        (limb_power(N as nat) - C as int) as nat
    }

    pub open spec fn half_prime() -> int {
        (Self::prime_spec() as int - 1) / 2
    }

    pub open spec fn centered_value(&self) -> int {
        centered(self.inner.model@, Self::prime_spec())
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.inner.wf()
        &&& self.inner.n_exec == N
        &&& self.inner.c_exec == C
        &&& N >= 2 && N <= 0x1FFF_FFFF
        &&& C > 0 && (C as int) < LIMB_BASE()
        &&& Self::prime_spec() > 2
        &&& Self::prime_spec() % 2 == 1
        &&& self.centered_value() >= -(self.bound@ as int)
        &&& self.centered_value() <= self.bound@ as int
        &&& (self.bound@ as int) <= Self::half_prime()
    }
}

impl<const N: usize, const C: u32> vstd::view::View for BoundedPrimeField<N, C> {
    type V = int;
    open spec fn view(&self) -> int {
        self.centered_value()
    }
}

//  ══════════════════════════════════════════════════════════════
//  Exec helpers
//  ══════════════════════════════════════════════════════════════

///  Compare two n-limb Vecs for equality. Returns true iff all limbs match.
fn limbs_equal(a: &Vec<u32>, b: &Vec<u32>, n: usize) -> (out: bool)
    requires a@.len() == n, b@.len() == n,
    ensures out == (forall|j: int| 0 <= j < n ==> a@[j] == b@[j]),
{
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            a@.len() == n, b@.len() == n,
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases n - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    true
}

///  Check if a value's model is > half = (p-1)/2, meaning centered value is negative.
///  We compare the raw model against half by checking: sub from p_half rounds.
///  Simpler approach: compare raw model against threshold using limb comparison.
///  For now: just check if the first n limbs represent a value > (p-1)/2.
///  We use: a > (p-1)/2 iff 2*a > p - 1 iff 2*a >= p (since p odd).
///  Equivalently: a + a >= p, which we can check via generic_add + carry.
fn is_negative_centered(val: &RuntimePrimeField<u32>) -> (out: bool)
    requires val.wf(), val.n_exec >= 2, val.prime_spec() > 2, val.prime_spec() % 2 == 1,
    ensures out == (centered(val.model@, val.prime_spec()) < 0),
{
    //  centered(a, p) < 0 iff a > (p-1)/2 iff a as int > (p as int - 1) / 2
    //  Since p = 2*half + 1 (odd), a > half iff 2*a > 2*half = p - 1 iff 2*a >= p.
    //  2*a >= p iff a + a overflows p, i.e., add_mod(a, a) has a "carry" from the addition.
    //  But add_mod reduces, so we can't check carry. Instead: a > half iff p - a <= half.
    //  Or: a > half iff a >= half + 1 iff 2*a >= 2*half + 2 = p + 1 > p.
    //  Actually simplest: val.model@ == 0 → not negative. Otherwise check if val > p/2.
    //  Use: add val to itself via generic_add_limbs. If carry = 1, then 2*val >= BASE^n > p,
    //  so val > p/2. If carry = 0, compare the sum against p_limbs.
    //  Actually even simpler: val.model@ > (p-1)/2 iff val.model@ >= (p+1)/2.
    //  And (p+1)/2 = half + 1. We can construct this and compare.
    //  But constructing (p+1)/2 as limbs is complex.
    //
    //  Simplest correct approach: add val to itself using generic_add_limbs.
    //  sum + carry*BASE^n == 2*val.model@. Since val.model@ < p:
    //  2*val < 2*p. And if 2*val >= p (i.e., val > (p-1)/2), then carry could be 0 or 1.
    //
    //  Actually, the very simplest: compare val against p_limbs using subtraction.
    //  val > half iff val >= half+1 iff val + val >= p (since p = 2*half+1).
    //  val + val: use generic_add_limbs.
    let n = val.n_exec;
    let (sum, carry) = generic_add_limbs(&val.limbs, &val.limbs, n);
    //  sum + carry * limb_power(n) == 2 * vec_val(val.limbs@)
    //  i.e. sum + carry * lp_full == 2 * val.model@ (where lp_full is the limb space, not p)
    //  If carry == 1: 2*val >= BASE^n >= p (since p < BASE^n), so val >= p/2 > half. Negative.
    //  If carry == 0: sum == 2*val. Compare sum >= p: use generic_sub_limbs(sum, p_limbs).
    if carry > 0u32 {
        proof {
            let lp = limb_power(n as nat);
            let p = val.prime_spec();
            let half = (p as int - 1) / 2;
            lemma_vec_val_bounded(val.limbs@);
            lemma_vec_val_bounded(sum@);
            lemma_odd_half(p);
            //  carry > 0 → carry.sem() >= 1 → 2*val >= lp >= p → val > half
            assert(2 * val.model@ as int >= lp) by(nonlinear_arith)
                requires vec_val(sum@) + carry.sem() * lp == vec_val(val.limbs@) + vec_val(val.limbs@),
                    val.model@ == vec_val(val.limbs@) as nat,
                    vec_val(sum@) >= 0, carry.sem() >= 1, lp > 0;
            assert(val.model@ as int > half) by(nonlinear_arith)
                requires 2 * val.model@ as int >= lp,
                    (p as int) < lp, p as int == 2 * half + 1;
        }
        true
    } else {
        let p_limbs: Vec<u32> = make_p_limbs(n, val.c_exec);
        let (_diff, borrow) = generic_sub_limbs(&sum, &p_limbs, n);
        let result = borrow == 0u32;
        proof {
            let lp = limb_power(n as nat);
            let p = val.prime_spec();
            let half = (p as int - 1) / 2;
            let pv = lp - val.c_exec as int;
            lemma_vec_val_bounded(val.limbs@);
            lemma_vec_val_bounded(sum@);
            lemma_vec_val_bounded(_diff@);
            lemma_odd_half(p);
            //  carry == 0u32 → carry.sem()*lp == 0 → sum == 2*val
            assert(carry.sem() == 0int);
            assert(carry.sem() * lp == 0int) by(nonlinear_arith) requires carry.sem() == 0int;
            //  Now Z3 can derive: sum + 0 == val_limbs + val_limbs → sum == 2*val
            assert(vec_val(sum@) == 2 * val.model@ as int) by(nonlinear_arith)
                requires vec_val(sum@) + 0 == vec_val(val.limbs@) + vec_val(val.limbs@),
                    val.model@ == vec_val(val.limbs@) as nat, vec_val(val.limbs@) >= 0;
            assert(vec_val(p_limbs@) == pv);
            if borrow.sem() == 0 {
                assert(vec_val(_diff@) + pv == vec_val(sum@));
                assert(vec_val(sum@) >= pv) by(nonlinear_arith)
                    requires vec_val(_diff@) + pv == vec_val(sum@), vec_val(_diff@) >= 0;
                assert(val.model@ as int > half) by(nonlinear_arith)
                    requires vec_val(sum@) >= pv, vec_val(sum@) == 2 * val.model@ as int,
                        pv == p as int, p as int == 2 * half + 1;
            } else {
                assert(borrow.sem() == 1);
                assert(vec_val(_diff@) + pv == vec_val(sum@) + lp);
                assert(vec_val(sum@) < pv) by(nonlinear_arith)
                    requires vec_val(_diff@) + pv == vec_val(sum@) + lp,
                        vec_val(_diff@) < lp, pv > 0, pv < lp;
                assert(val.model@ as int <= half) by(nonlinear_arith)
                    requires vec_val(sum@) < pv, vec_val(sum@) == 2 * val.model@ as int,
                        pv == p as int, p as int == 2 * half + 1;
            }
        }
        result
    }
}

//  ══════════════════════════════════════════════════════════════
//  RuntimeOrderedRingOps<int> for BoundedPrimeField<N, C>
//  ══════════════════════════════════════════════════════════════

impl<const N: usize, const C: u32> verus_algebra::traits::runtime::RuntimeOrderedRingOps<int>
    for BoundedPrimeField<N, C>
{
    open spec fn wf_spec(&self) -> bool { self.wf() }

    open spec fn add_wf(&self, rhs: &Self) -> bool {
        (self.bound@ as int + rhs.bound@ as int) <= Self::half_prime()
    }

    open spec fn mul_wf(&self, rhs: &Self) -> bool {
        (self.bound@ as int * rhs.bound@ as int) <= Self::half_prime()
    }

    fn add(&self, rhs: &Self) -> (out: Self)
    {
        let result_inner = self.inner.add_mod(&rhs.inner);
        proof {
            let p = Self::prime_spec();
            assert(self.centered_value() + rhs.centered_value() >= -Self::half_prime())
                by(nonlinear_arith)
                requires self.centered_value() >= -(self.bound@ as int),
                    rhs.centered_value() >= -(rhs.bound@ as int),
                    self.bound@ as int + rhs.bound@ as int <= Self::half_prime();
            assert(self.centered_value() + rhs.centered_value() <= Self::half_prime())
                by(nonlinear_arith)
                requires self.centered_value() <= self.bound@ as int,
                    rhs.centered_value() <= rhs.bound@ as int,
                    self.bound@ as int + rhs.bound@ as int <= Self::half_prime();
            lemma_centered_add(self.inner.model@, rhs.inner.model@, p);
        }
        BoundedPrimeField { inner: result_inner, bound: Ghost(self.bound@ + rhs.bound@) }
    }

    fn sub(&self, rhs: &Self) -> (out: Self)
    {
        let neg_inner = rhs.inner.neg_mod();
        let result_inner = self.inner.add_mod(&neg_inner);
        proof {
            let p = Self::prime_spec();
            let a = self.inner.model@;
            let b = rhs.inner.model@;
            //  neg_inner has same n_exec/c_exec (from neg_mod same_field)
            assert(neg_inner.n_exec == N && neg_inner.c_exec == C);
            if b == 0 {
                lemma_centered_zero(p);
                assert(neg_inner.model@ == 0nat);
                assert((a + 0nat) % p == a) by(nonlinear_arith) requires a < p, p > 0;
                assert(rhs.centered_value() == 0int);
            } else {
                //  centered(neg_inner) == -centered(b) == -rhs.cv
                lemma_centered_neg(b, p);
                assert(centered(neg_inner.model@, p) == -rhs.centered_value());
                //  Bound check for centered_add
                assert(self.centered_value() + centered(neg_inner.model@, p) >= -Self::half_prime())
                    by(nonlinear_arith)
                    requires self.centered_value() >= -(self.bound@ as int),
                        centered(neg_inner.model@, p) >= -(rhs.bound@ as int),
                        self.bound@ as int + rhs.bound@ as int <= Self::half_prime();
                assert(self.centered_value() + centered(neg_inner.model@, p) <= Self::half_prime())
                    by(nonlinear_arith)
                    requires self.centered_value() <= self.bound@ as int,
                        centered(neg_inner.model@, p) <= rhs.bound@ as int,
                        self.bound@ as int + rhs.bound@ as int <= Self::half_prime();
                lemma_centered_add(a, neg_inner.model@, p);
                //  centered(result) == self.cv + centered(neg) == self.cv - rhs.cv
                assert(centered(result_inner.model@, p) == self.centered_value() - rhs.centered_value());
            }
            //  Output bound
            assert(self.centered_value() - rhs.centered_value()
                >= -(self.bound@ as int + rhs.bound@ as int)) by(nonlinear_arith)
                requires self.centered_value() >= -(self.bound@ as int),
                    rhs.centered_value() <= rhs.bound@ as int;
            assert(self.centered_value() - rhs.centered_value()
                <= self.bound@ as int + rhs.bound@ as int) by(nonlinear_arith)
                requires self.centered_value() <= self.bound@ as int,
                    rhs.centered_value() >= -(rhs.bound@ as int);
        }
        BoundedPrimeField { inner: result_inner, bound: Ghost(self.bound@ + rhs.bound@) }
    }

    fn neg(&self) -> (out: Self)
    {
        let result_inner = self.inner.neg_mod();
        proof {
            let p = Self::prime_spec();
            let a = self.inner.model@;
            if a == 0 { lemma_centered_zero(p); }
            else { lemma_centered_neg(a, p); }
        }
        BoundedPrimeField { inner: result_inner, bound: Ghost(self.bound@) }
    }

    fn mul(&self, rhs: &Self) -> (out: Self)
    {
        let result_inner = self.inner.mul_mod(&rhs.inner);
        proof {
            let p = Self::prime_spec();
            assert(self.centered_value() * rhs.centered_value() >= -Self::half_prime())
                by(nonlinear_arith)
                requires self.centered_value() >= -(self.bound@ as int),
                    self.centered_value() <= self.bound@ as int,
                    rhs.centered_value() >= -(rhs.bound@ as int),
                    rhs.centered_value() <= rhs.bound@ as int,
                    self.bound@ as int * rhs.bound@ as int <= Self::half_prime();
            assert(self.centered_value() * rhs.centered_value() <= Self::half_prime())
                by(nonlinear_arith)
                requires self.centered_value() >= -(self.bound@ as int),
                    self.centered_value() <= self.bound@ as int,
                    rhs.centered_value() >= -(rhs.bound@ as int),
                    rhs.centered_value() <= rhs.bound@ as int,
                    self.bound@ as int * rhs.bound@ as int <= Self::half_prime();
            lemma_centered_mul(self.inner.model@, rhs.inner.model@, p);
            //  Output bound: |ca * cb| <= bound_a * bound_b
            let ca = self.centered_value();
            let cb = rhs.centered_value();
            assert(ca * cb >= -(self.bound@ as int * rhs.bound@ as int)) by(nonlinear_arith)
                requires ca >= -(self.bound@ as int), ca <= self.bound@ as int,
                    cb >= -(rhs.bound@ as int), cb <= rhs.bound@ as int;
            assert(ca * cb <= self.bound@ as int * rhs.bound@ as int) by(nonlinear_arith)
                requires ca >= -(self.bound@ as int), ca <= self.bound@ as int,
                    cb >= -(rhs.bound@ as int), cb <= rhs.bound@ as int;
        }
        BoundedPrimeField { inner: result_inner, bound: Ghost((self.bound@ * rhs.bound@) as nat) }
    }

    fn eq(&self, rhs: &Self) -> (out: bool)
    {
        //  a == b iff a <= b && b <= a. Avoids positional uniqueness proof.
        let ab = <Self as verus_algebra::traits::runtime::RuntimeOrderedRingOps<int>>::le(self, rhs);
        let ba = <Self as verus_algebra::traits::runtime::RuntimeOrderedRingOps<int>>::le(rhs, self);
        ab && ba
    }

    fn copy(&self) -> (out: Self)
    {
        let copied_limbs = generic_slice_vec(&self.inner.limbs, 0, N);
        proof {
            assert(sem_seq(copied_limbs@) =~= sem_seq(self.inner.limbs@)) by {
                assert forall|j: int| 0 <= j < N
                    implies sem_seq(copied_limbs@)[j] == sem_seq(self.inner.limbs@)[j] by {
                    assert(copied_limbs@[j].sem() == self.inner.limbs@[(0 + j) as int].sem());
                };
            };
        }
        BoundedPrimeField {
            inner: RuntimePrimeField {
                limbs: copied_limbs, n_exec: N, c_exec: C,
                model: Ghost(self.inner.model@),
            },
            bound: Ghost(self.bound@),
        }
    }

    fn zero_like(&self) -> (out: Self)
    {
        let limbs: Vec<u32> = generic_zero_vec(N);
        proof {
            lemma_vec_val_zeros(limbs@);
            lemma_centered_zero(Self::prime_spec());
        }
        BoundedPrimeField {
            inner: RuntimePrimeField {
                limbs: limbs, n_exec: N, c_exec: C, model: Ghost(0nat),
            },
            bound: Ghost(0nat),
        }
    }

    fn one_like(&self) -> (out: Self)
    {
        let limbs: Vec<u32> = scalar_to_padded_vec(1u32, N);
        proof {
            //  scalar_to_padded_vec ensures vec_val == 1, valid_limbs, len == N
            //  centered(1, p) == 1 since 1 <= half (half >= 1 for p > 2)
            lemma_odd_half(Self::prime_spec());
        }
        BoundedPrimeField {
            inner: RuntimePrimeField {
                limbs: limbs, n_exec: N, c_exec: C, model: Ghost(1nat),
            },
            bound: Ghost(1nat),
        }
    }

    fn le(&self, rhs: &Self) -> (out: bool)
    {
        let a_neg = is_negative_centered(&self.inner);
        let b_neg = is_negative_centered(&rhs.inner);
        if a_neg && !b_neg {
            proof { assert(self.centered_value() < 0); assert(rhs.centered_value() >= 0); }
            true
        } else if !a_neg && b_neg {
            proof { assert(self.centered_value() >= 0); assert(rhs.centered_value() < 0); }
            false
        } else {
            //  Same sign: centered ordering == raw ordering (both shifted by same -p or 0).
            let (_diff, borrow) = generic_sub_limbs(&rhs.inner.limbs, &self.inner.limbs, N);
            let result = borrow == 0u32;
            proof {
                let p = Self::prime_spec();
                let a = self.inner.model@;
                let b = rhs.inner.model@;
                let lp = limb_power(N as nat);
                lemma_vec_val_bounded(self.inner.limbs@);
                lemma_vec_val_bounded(rhs.inner.limbs@);
                lemma_vec_val_bounded(_diff@);
                if borrow.sem() == 0 {
                    assert(borrow.sem() * lp == 0int) by(nonlinear_arith) requires borrow.sem() == 0;
                    assert(a as int <= b as int) by(nonlinear_arith)
                        requires vec_val(_diff@) + a as int == b as int,
                            vec_val(_diff@) >= 0;
                } else {
                    assert(a as int > b as int) by(nonlinear_arith)
                        requires vec_val(_diff@) + a as int == b as int + borrow.sem() * lp,
                            vec_val(_diff@) < lp, lp > 0, borrow.sem() >= 1;
                }
                //  Same sign → same centered branch → ordering preserved
                lemma_odd_half(p);
                if !a_neg && !b_neg {
                    assert(centered(a, p) == a as int);
                    assert(centered(b, p) == b as int);
                } else {
                    //  Both negative: a > half, b > half
                    assert(a as int > Self::half_prime());
                    assert(b as int > Self::half_prime());
                    assert(centered(a, p) == a as int - p as int);
                    assert(centered(b, p) == b as int - p as int);
                }
            }
            result
        }
    }

    fn lt(&self, rhs: &Self) -> (out: bool)
    {
        let is_le = <Self as verus_algebra::traits::runtime::RuntimeOrderedRingOps<int>>::le(self, rhs);
        let is_eq = <Self as verus_algebra::traits::runtime::RuntimeOrderedRingOps<int>>::eq(self, rhs);
        is_le && !is_eq
    }
}

} // verus!
