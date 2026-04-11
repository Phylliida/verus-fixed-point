use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse, lemma_small_mod};

verus! {

// ============================================================
// Number theory foundations for field axioms
// ============================================================

// ── Primality ──────────────────────────────────────────

pub open spec fn is_prime(p: nat) -> bool {
    p >= 2 && forall|d: nat| 1 < d < p ==> #[trigger] (p % d) != 0
}

// ── GCD (Euclidean algorithm) ──────────────────────────

pub open spec fn gcd(a: nat, b: nat) -> nat
    decreases b,
{
    if b == 0 { a }
    else { gcd(b, a % b) }
}

// ── Extended Euclidean — Bezout coefficients ───────────
// Returns (s, t) such that gcd(a, b) = s*a + t*b.

pub open spec fn ext_gcd(a: nat, b: nat) -> (int, int)
    decreases b,
{
    if b == 0 {
        (1int, 0int)
    } else {
        let r = ext_gcd(b, a % b);
        let s1 = r.0;
        let t1 = r.1;
        let q = (a / b) as int;
        (t1, s1 - q * t1)
    }
}

// ── Helper: if d divides both b and r, it divides q*b+r ──

pub proof fn lemma_divides_linear_combination(d: int, b: int, r: int, q: int)
    requires
        d > 0,
        b % d == 0,
        r % d == 0,
    ensures
        (q * b + r) % d == 0,
{
    lemma_fundamental_div_mod(b, d);
    lemma_fundamental_div_mod(r, d);
    let kb = b / d;
    let kr = r / d;
    let total = q * b + r;
    let qtotal = q * kb + kr;
    assert(total == d * qtotal) by (nonlinear_arith)
        requires
            b == d * kb + b % d, b % d == 0,
            r == d * kr + r % d, r % d == 0,
            total == q * b + r, qtotal == q * kb + kr;
    lemma_fundamental_div_mod_converse(total, d, qtotal, 0);
}

// ── GCD divides both arguments ─────────────────────────

pub proof fn lemma_gcd_divides(a: nat, b: nat)
    requires a > 0 || b > 0,
    ensures
        a % gcd(a, b) == 0,
        b % gcd(a, b) == 0,
    decreases b,
{
    if b == 0 {
        assert(gcd(a, b) == a);
        assert(a > 0nat);
        //  a % a = 0: a = 1*a + 0, by div_mod_converse
        lemma_fundamental_div_mod_converse(a as int, a as int, 1, 0);
        //  0 % a = 0: 0 = 0*a + 0, by div_mod_converse
        lemma_fundamental_div_mod_converse(0int, a as int, 0, 0);
    } else {
        //  b > 0, so b > 0 || a%b > 0, satisfying IH precondition.
        lemma_gcd_divides(b, a % b);
        let d = gcd(a, b);
        //  IH: b % d == 0 and (a%b) % d == 0.
        assert(b % d == 0nat);
        assert((a % b) % d == 0nat);

        //  a = b*(a/b) + a%b. Since d | b and d | (a%b), d | a.
        lemma_fundamental_div_mod(a as int, b as int);
        let q = (a as int) / (b as int);
        let r = (a as int) % (b as int);
        lemma_gcd_positive(b, a % b);
        //  Use int mod directly so Z3 connects the linear combination to a
        lemma_divides_linear_combination(d as int, b as int, r, q);
        //  Now Z3 knows (q * b + r) % d == 0 where q*b+r == a
        assert(a as int == (b as int) * q + r);
        assert((b as int) * q + r == q * (b as int) + r) by (nonlinear_arith);
        assert((a as int) % (d as int) == 0);
    }
}

// ── GCD is positive when inputs are ────────────────────

pub proof fn lemma_gcd_positive(a: nat, b: nat)
    requires a > 0 || b > 0,
    ensures gcd(a, b) > 0,
    decreases b,
{
    if b == 0 {
        assert(gcd(a, b) == a);
    } else {
        if a % b > 0 {
            lemma_gcd_positive(b, a % b);
        } else {
            assert(a % b == 0nat);
            assert(gcd(b, 0nat) == b);
        }
    }
}

// ── GCD bounded by first argument ──────────────────────

pub proof fn lemma_gcd_le_args(a: nat, b: nat)
    requires a > 0,
    ensures gcd(a, b) <= a,
{
    lemma_gcd_divides(a, b);
    lemma_gcd_positive(a, b);
    let d = gcd(a, b);
    assert(d > 0nat);

    if b == 0 {
        assert(d == a);
    } else {
        assert(a % d == 0nat);
        //  d | a means a = d * (a/d), so d <= a.
        lemma_fundamental_div_mod(a as int, d as int);
        let qd = (a as int) / (d as int);
        assert(a as int == d as int * qd + (a as int) % (d as int));
        assert((a as int) % (d as int) == 0) by (nonlinear_arith)
            requires a % d == 0nat, a >= 0nat, d > 0nat;
        assert(a as int == d as int * qd) by (nonlinear_arith)
            requires a as int == d as int * qd + (a as int) % (d as int), (a as int) % (d as int) == 0;
        assert(qd >= 1) by (nonlinear_arith)
            requires a as int == d as int * qd, a > 0nat, d > 0nat;
        assert(d <= a) by (nonlinear_arith)
            requires a as int == d as int * qd, qd >= 1, d > 0nat;
    }
}

// ── Bezout's Identity ──────────────────────────────────

pub proof fn lemma_bezout(a: nat, b: nat)
    ensures
        gcd(a, b) as int == ext_gcd(a, b).0 * (a as int) + ext_gcd(a, b).1 * (b as int),
    decreases b,
{
    if b == 0 {
    } else {
        lemma_bezout(b, a % b);
        let s1 = ext_gcd(b, a % b).0;
        let t1 = ext_gcd(b, a % b).1;
        let q = (a / b) as int;
        let r = (a % b) as int;
        let ai = a as int;
        let bi = b as int;

        lemma_fundamental_div_mod(ai, bi);

        assert(s1 * bi + t1 * r == t1 * ai + (s1 - q * t1) * bi)
            by (nonlinear_arith)
            requires ai == bi * q + r;
    }
}

// ── Prime implies coprime ──────────────────────────────

pub proof fn lemma_prime_coprime(a: nat, p: nat)
    requires
        is_prime(p),
        0 < a,
        a < p,
    ensures
        gcd(a, p) == 1,
{
    let d = gcd(a, p);
    lemma_gcd_divides(a, p);
    lemma_gcd_positive(a, p);
    lemma_gcd_le_args(a, p);
    assert(d > 0nat);
    assert(d <= a);
    assert(p > 0nat);
    //  d | p (from gcd_divides, since p > 0 so the b==0 case doesn't apply)
    assert(p % d == 0nat);
    //  d < p (since d <= a < p)
    //  If d > 1 then is_prime says p % d != 0, contradiction.
    if d > 1 {
        assert(1 < d);
        assert(d < p) by (nonlinear_arith) requires d <= a, a < p;
        assert(false);
    }
}

// ── Bezout gives modular inverse ───────────────────────

pub proof fn lemma_bezout_inverse(a: nat, p: nat)
    requires
        is_prime(p),
        0 < a,
        a < p,
    ensures ({
        let s = ext_gcd(a, p).0;
        (s * a as int) % p as int == 1
    }),
{
    lemma_prime_coprime(a, p);
    lemma_bezout(a, p);
    let s = ext_gcd(a, p).0;
    let t = ext_gcd(a, p).1;
    let ai = a as int;
    let pi = p as int;
    let sa = s * ai;
    //  Bezout: 1 = s*a + t*p, so s*a = 1 - t*p = (-t)*p + 1.
    assert(sa == (-t) * pi + 1) by (nonlinear_arith)
        requires s * ai + t * pi == 1, sa == s * ai;
    //  0 <= 1 < p, so (s*a) % p = 1.
    lemma_fundamental_div_mod_converse(sa, pi, -t, 1);
}

// ── Euclid's Lemma ─────────────────────────────────────

///  If p is prime, 0 < a < p, and p divides a*b, then p divides b.
pub proof fn lemma_euclid(a: nat, b: int, p: nat)
    requires
        is_prime(p),
        0 < a, a < p,
        ((a as int) * b) % (p as int) == 0,
    ensures
        b % (p as int) == 0,
{
    let ai = a as int;
    let pi = p as int;
    lemma_prime_coprime(a, p);
    lemma_bezout(a, p);
    let s = ext_gcd(a, p).0;
    let t = ext_gcd(a, p).1;
    //  s*a + t*p = 1. Multiply by b: s*a*b + t*p*b = b.
    //  p | a*b, so a*b = k*p for some k.
    lemma_fundamental_div_mod(ai * b, pi);
    let k = (ai * b) / pi;
    assert(ai * b == pi * k) by (nonlinear_arith)
        requires ai * b == pi * k + (ai * b) % pi, (ai * b) % pi == 0;
    //  b = s*a*b + t*p*b = s*(k*p) + t*p*b = p*(s*k + t*b)
    assert(s * ai + t * pi == 1);
    assert(s * (ai * b) + t * pi * b == b) by (nonlinear_arith)
        requires s * ai + t * pi == 1;
    assert(b == pi * (s * k + t * b)) by (nonlinear_arith)
        requires s * (ai * b) + t * pi * b == b, ai * b == pi * k;
    lemma_fundamental_div_mod_converse(b, pi, s * k + t * b, 0);
}

// ── Modular inverse uniqueness ─────────────────────────

///  The modular inverse is unique in [0, p).
pub proof fn lemma_mod_inverse_unique(a: nat, x: nat, y: nat, p: nat)
    requires
        is_prime(p),
        0 < a, a < p,
        x < p, y < p,
        (x * a) % p == 1,
        (y * a) % p == 1,
    ensures
        x == y,
{
    let ai = a as int;
    let pi = p as int;
    let xi = x as int;
    let yi = y as int;
    //  x*a = q1*p + 1, y*a = q2*p + 1
    lemma_fundamental_div_mod(xi * ai, pi);
    lemma_fundamental_div_mod(yi * ai, pi);
    let q1 = (xi * ai) / pi;
    let q2 = (yi * ai) / pi;
    assert(xi * ai == pi * q1 + 1) by (nonlinear_arith)
        requires xi * ai == pi * q1 + (xi * ai) % pi, (xi * ai) % pi == 1;
    assert(yi * ai == pi * q2 + 1) by (nonlinear_arith)
        requires yi * ai == pi * q2 + (yi * ai) % pi, (yi * ai) % pi == 1;
    //  (x - y) * a = (q1 - q2) * p
    assert((xi - yi) * ai == (q1 - q2) * pi) by (nonlinear_arith)
        requires xi * ai == pi * q1 + 1, yi * ai == pi * q2 + 1;
    //  p | (x - y) * a
    lemma_fundamental_div_mod_converse((xi - yi) * ai, pi, q1 - q2, 0);
    //  Commutativity: ((xi - yi) * ai) % pi == (ai * (xi - yi)) % pi
    assert((xi - yi) * ai == ai * (xi - yi)) by (nonlinear_arith);
    assert((ai * (xi - yi)) % pi == 0);
    //  By Euclid: p | (x - y)
    lemma_euclid(a, xi - yi, p);
    //  |x - y| < p and p | (x - y), so x - y == 0
    assert(-(pi - 1) <= xi - yi && xi - yi <= pi - 1) by (nonlinear_arith)
        requires 0 <= xi, xi < pi, 0 <= yi, yi < pi;
    //  If x != y, then 0 < |x - y| < p, contradicting p | (x - y)
    if xi != yi {
        lemma_fundamental_div_mod(xi - yi, pi);
        assert((xi - yi) == pi * ((xi - yi) / pi)) by (nonlinear_arith)
            requires (xi - yi) == pi * ((xi - yi) / pi) + (xi - yi) % pi, (xi - yi) % pi == 0;
        assert(false) by (nonlinear_arith)
            requires (xi - yi) == pi * ((xi - yi) / pi),
                     -(pi - 1) <= xi - yi, xi - yi <= pi - 1,
                     xi != yi, pi > 1;
    }
}

} //  verus!
