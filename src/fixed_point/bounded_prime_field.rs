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
    let q: int = ka * cb + kb * ca + ka * kb * (p as int);
    assert(a as int * b as int == prod + q * (p as int)) by(nonlinear_arith)
        requires a as int == ca + ka * (p as int), b as int == cb + kb * (p as int),
            prod == ca * cb, q == ka * cb + kb * ca + ka * kb * (p as int);
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
//  BoundedPrimeField type
//  ══════════════════════════════════════════════════════════════

///  RuntimePrimeField wrapper with centered integer view and dynamic bound tracking.
///
///  View type is `int` (the centered value). Implements RuntimeOrderedRingOps<int>.
///  The ghost `bound` tracks |centered_value| <= bound, and add_wf/mul_wf ensure
///  operations don't wrap around the modular boundary.
pub struct BoundedPrimeField {
    pub inner: RuntimePrimeField,
    pub bound: Ghost<nat>,
}

impl BoundedPrimeField {
    pub open spec fn prime_spec(&self) -> nat {
        self.inner.prime_spec()
    }

    pub open spec fn half_prime(&self) -> int {
        (self.prime_spec() as int - 1) / 2
    }

    pub open spec fn centered_value(&self) -> int {
        centered(self.inner.model@, self.prime_spec())
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.inner.wf()
        &&& self.inner.n_exec >= 2
        &&& self.prime_spec() > 2
        &&& self.centered_value() >= -(self.bound@ as int)
        &&& self.centered_value() <= self.bound@ as int
        &&& (self.bound@ as int) <= self.half_prime()
    }

    pub open spec fn same_field(&self, other: &Self) -> bool {
        self.inner.same_field(&other.inner)
    }
}

} // verus!
