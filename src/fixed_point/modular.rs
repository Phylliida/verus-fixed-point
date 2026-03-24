use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse};

verus! {

/// Element of Z/pZ — a natural number modulo a given modulus.
pub struct ModularInt {
    pub value: nat,
    pub modulus: nat,
}

impl ModularInt {
    pub open spec fn wf_spec(self) -> bool {
        self.value < self.modulus && self.modulus > 1
    }

    pub open spec fn same_modulus(self, other: ModularInt) -> bool {
        self.modulus == other.modulus
    }

    pub open spec fn zero(p: nat) -> ModularInt {
        ModularInt { value: 0, modulus: p }
    }

    pub open spec fn one(p: nat) -> ModularInt {
        ModularInt { value: 1, modulus: p }
    }

    pub open spec fn add_mod(self, rhs: ModularInt) -> ModularInt {
        ModularInt { value: (self.value + rhs.value) % self.modulus, modulus: self.modulus }
    }

    pub open spec fn neg_mod(self) -> ModularInt {
        ModularInt {
            value: if self.value == 0 { 0 } else { (self.modulus - self.value) as nat },
            modulus: self.modulus,
        }
    }

    pub open spec fn sub_mod(self, rhs: ModularInt) -> ModularInt {
        self.add_mod(rhs.neg_mod())
    }

    pub open spec fn mul_mod(self, rhs: ModularInt) -> ModularInt {
        ModularInt { value: (self.value * rhs.value) % self.modulus, modulus: self.modulus }
    }

    pub open spec fn eqv(self, rhs: ModularInt) -> bool {
        self.value == rhs.value && self.modulus == rhs.modulus
    }

    pub open spec fn pow_mod(self, exp: nat) -> ModularInt
        decreases exp,
    {
        if exp == 0 { Self::one(self.modulus) }
        else if exp % 2 == 0 { let half = self.pow_mod(exp / 2); half.mul_mod(half) }
        else { self.mul_mod(self.pow_mod((exp - 1) as nat)) }
    }
}

// ── Modular arithmetic core lemma ──────────────────────
// Proved using vstd's lemma_fundamental_div_mod_converse.

/// (a%p + b)%p == (a+b)%p
pub proof fn lemma_mod_add_left(a: nat, b: nat, p: nat)
    requires p > 0,
    ensures (a % p + b) % p == (a + b) % p,
{
    // a = (a/p)*p + a%p, so a+b = (a/p)*p + (a%p + b)
    // Let q2 = (a%p+b)/p, r2 = (a%p+b)%p.
    // Then a%p+b = q2*p + r2, so a+b = (a/p)*p + q2*p + r2 = (a/p + q2)*p + r2.
    // By converse: (a+b)%p == r2 == (a%p+b)%p.
    let pi = p as int;
    let ai = a as int;
    let bi = b as int;
    let q1 = ai / pi;
    let r1 = ai % pi;

    // Fundamental division identity
    lemma_fundamental_div_mod(ai, pi);
    // ensures: ai == pi * (ai / pi) + (ai % pi) == pi * q1 + r1

    let r1_plus_b = r1 + bi;
    let q2 = r1_plus_b / pi;
    let r2 = r1_plus_b % pi;

    lemma_fundamental_div_mod(r1_plus_b, pi);
    // r1_plus_b == pi * q2 + r2

    // ai + bi = pi*q1 + r1 + bi = pi*q1 + r1_plus_b = pi*q1 + pi*q2 + r2 = pi*(q1+q2) + r2
    assert(ai + bi == pi * q1 + r1_plus_b) by (nonlinear_arith)
        requires ai == pi * q1 + r1, r1_plus_b == r1 + bi;
    assert(pi * q1 + pi * q2 + r2 == pi * (q1 + q2) + r2) by (nonlinear_arith);
    assert(ai + bi == pi * q1 + pi * q2 + r2);
    assert((a + b) as int == pi * (q1 + q2) + r2);

    lemma_fundamental_div_mod_converse((a + b) as int, pi, q1 + q2, r2);
    // r2 == (a+b) % p == (a%p + b) % p
}

/// (a + b%p)%p == (a+b)%p
pub proof fn lemma_mod_add_right(a: nat, b: nat, p: nat)
    requires p > 0,
    ensures (a + b % p) % p == (a + b) % p,
{
    lemma_mod_add_left(b, a, p);
    // (b%p + a)%p == (b+a)%p == (a+b)%p
}

/// (a%p * b)%p == (a*b)%p
pub proof fn lemma_mod_mul_left(a: nat, b: nat, p: nat)
    requires p > 0,
    ensures (a % p * b) % p == (a * b) % p,
{
    // a = q*p + r, so a*b = q*p*b + r*b = (q*b)*p + r*b
    // (a%p * b) == r*b
    // Let q2 = (r*b)/p, r2 = (r*b)%p. Then r*b = q2*p + r2.
    // a*b = (q*b)*p + q2*p + r2 = (q*b + q2)*p + r2.
    // By converse: (a*b)%p == r2 == (r*b)%p == (a%p * b)%p.
    let pi = p as int;
    let ai = a as int;
    let bi = b as int;
    let q1 = ai / pi;
    let r1 = ai % pi;
    let r1b = r1 * bi;
    let q2 = r1b / pi;
    let r2 = r1b % pi;

    lemma_fundamental_div_mod(ai, pi);
    // ai == pi * q1 + r1
    lemma_fundamental_div_mod(r1b, pi);
    // r1b == pi * q2 + r2

    // ai*bi = (pi*q1+r1)*bi = pi*q1*bi + r1*bi = pi*q1*bi + r1b = pi*q1*bi + pi*q2 + r2
    assert(ai * bi == pi * q1 * bi + r1 * bi) by (nonlinear_arith)
        requires ai == pi * q1 + r1;
    assert(ai * bi == pi * q1 * bi + pi * q2 + r2) by (nonlinear_arith)
        requires ai * bi == pi * q1 * bi + r1 * bi, r1b == pi * q2 + r2, r1b == r1 * bi;
    assert(pi * q1 * bi + pi * q2 == pi * (q1 * bi + q2)) by (nonlinear_arith);
    assert((a * b) as int == pi * (q1 * bi + q2) + r2);

    lemma_fundamental_div_mod_converse((a * b) as int, pi, q1 * bi + q2, r2);
}

/// (a * b%p)%p == (a*b)%p
pub proof fn lemma_mod_mul_right(a: nat, b: nat, p: nat)
    requires p > 0,
    ensures (a * (b % p)) % p == (a * b) % p,
{
    lemma_mod_mul_left(b, a, p);
    assert(a * b == b * a) by (nonlinear_arith);
    assert(b % p * a == a * (b % p)) by (nonlinear_arith);
}

// ── Well-formedness ────────────────────────────────────

pub proof fn lemma_zero_wf(p: nat)
    requires p > 1, ensures ModularInt::zero(p).wf_spec(),
{}

pub proof fn lemma_one_wf(p: nat)
    requires p > 1, ensures ModularInt::one(p).wf_spec(),
{}

pub proof fn lemma_add_mod_wf(a: ModularInt, b: ModularInt)
    requires a.wf_spec(), b.wf_spec(), a.same_modulus(b),
    ensures a.add_mod(b).wf_spec(),
{
    assert((a.value + b.value) % a.modulus < a.modulus) by (nonlinear_arith) requires a.modulus > 1;
}

pub proof fn lemma_neg_mod_wf(a: ModularInt)
    requires a.wf_spec(),
    ensures a.neg_mod().wf_spec(), a.neg_mod().same_modulus(a),
{}

pub proof fn lemma_mul_mod_wf(a: ModularInt, b: ModularInt)
    requires a.wf_spec(), b.wf_spec(), a.same_modulus(b),
    ensures a.mul_mod(b).wf_spec(),
{
    assert((a.value * b.value) % a.modulus < a.modulus) by (nonlinear_arith) requires a.modulus > 1;
}

// ── Ring axioms (all fully proved) ─────────────────────

pub proof fn lemma_add_commutative(a: ModularInt, b: ModularInt)
    requires a.wf_spec(), b.wf_spec(), a.same_modulus(b),
    ensures a.add_mod(b).eqv(b.add_mod(a)),
{}

pub proof fn lemma_add_associative(a: ModularInt, b: ModularInt, c: ModularInt)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(),
             a.same_modulus(b), b.same_modulus(c),
    ensures a.add_mod(b).add_mod(c).eqv(a.add_mod(b.add_mod(c))),
{
    let p = a.modulus;
    lemma_mod_add_left(a.value + b.value, c.value, p);
    lemma_mod_add_right(a.value, b.value + c.value, p);
}

pub proof fn lemma_add_zero_right(a: ModularInt)
    requires a.wf_spec(),
    ensures a.add_mod(ModularInt::zero(a.modulus)).eqv(a),
{
    assert((a.value + 0) % a.modulus == a.value) by (nonlinear_arith)
        requires a.value < a.modulus, a.modulus > 1;
}

pub proof fn lemma_add_neg_right(a: ModularInt)
    requires a.wf_spec(),
    ensures a.add_mod(a.neg_mod()).eqv(ModularInt::zero(a.modulus)),
{
    let p = a.modulus;
    if a.value == 0 {
        assert((0 + 0) % p == 0) by (nonlinear_arith) requires p > 1;
    } else {
        let neg_val = (p - a.value) as nat;
        assert((a.value + neg_val) % p == 0) by (nonlinear_arith)
            requires a.value < p, a.value > 0, neg_val == (p - a.value) as nat, p > 1;
    }
}

pub proof fn lemma_mul_commutative(a: ModularInt, b: ModularInt)
    requires a.wf_spec(), b.wf_spec(), a.same_modulus(b),
    ensures a.mul_mod(b).eqv(b.mul_mod(a)),
{
    assert(a.value * b.value == b.value * a.value) by (nonlinear_arith);
}

pub proof fn lemma_mul_associative(a: ModularInt, b: ModularInt, c: ModularInt)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(),
             a.same_modulus(b), b.same_modulus(c),
    ensures a.mul_mod(b).mul_mod(c).eqv(a.mul_mod(b.mul_mod(c))),
{
    let p = a.modulus;
    lemma_mod_mul_left(a.value * b.value, c.value, p);
    lemma_mod_mul_right(a.value, b.value * c.value, p);
    assert(a.value * b.value * c.value == a.value * (b.value * c.value)) by (nonlinear_arith);
}

pub proof fn lemma_mul_one_right(a: ModularInt)
    requires a.wf_spec(),
    ensures a.mul_mod(ModularInt::one(a.modulus)).eqv(a),
{
    assert((a.value * 1) % a.modulus == a.value) by (nonlinear_arith)
        requires a.value < a.modulus, a.modulus > 1;
}

pub proof fn lemma_mul_zero_right(a: ModularInt)
    requires a.wf_spec(),
    ensures a.mul_mod(ModularInt::zero(a.modulus)).eqv(ModularInt::zero(a.modulus)),
{
    assert((a.value * 0) % a.modulus == 0) by (nonlinear_arith) requires a.modulus > 1;
}

pub proof fn lemma_mul_distributes_left(a: ModularInt, b: ModularInt, c: ModularInt)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(),
             a.same_modulus(b), b.same_modulus(c),
    ensures a.mul_mod(b.add_mod(c)).eqv(a.mul_mod(b).add_mod(a.mul_mod(c))),
{
    let p = a.modulus;
    let av = a.value; let bv = b.value; let cv = c.value;
    // LHS: (av * ((bv+cv)%p)) % p == (av * (bv+cv)) % p [by mod_mul_right]
    lemma_mod_mul_right(av, bv + cv, p);
    // RHS: ((av*bv)%p + (av*cv)%p) % p == (av*bv + av*cv) % p [by mod_add_left + mod_add_right]
    lemma_mod_add_left(av * bv, av * cv, p);
    lemma_mod_add_right(av * bv % p, av * cv, p);
    // av*(bv+cv) == av*bv + av*cv
    assert(av * (bv + cv) == av * bv + av * cv) by (nonlinear_arith);
}

pub proof fn lemma_one_ne_zero(p: nat)
    requires p > 1,
    ensures !ModularInt::one(p).eqv(ModularInt::zero(p)),
{}

// ── Exec-level modular arithmetic ──────────────────────

/// Runtime modular integer: value mod p, stored as u32.
/// Uses u64 for intermediate computations to avoid overflow.
pub struct RuntimeModularInt {
    pub val: u32,
    pub p: u32, // modulus (prime), stored at exec level for computation
    pub model: Ghost<ModularInt>,
}

impl RuntimeModularInt {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.model@.wf_spec()
        &&& self.model@.value == self.val as nat
        &&& self.model@.modulus == self.p as nat
        &&& self.p > 1
    }
}

impl View for RuntimeModularInt {
    type V = ModularInt;
    open spec fn view(&self) -> ModularInt { self.model@ }
}

impl RuntimeModularInt {
    /// Construct from value (must be < p).
    pub fn new(val: u32, p: u32) -> (result: Self)
        requires val < p, p > 1,
        ensures result.wf_spec(), result@.value == val as nat, result@.modulus == p as nat,
    {
        RuntimeModularInt {
            val, p,
            model: Ghost(ModularInt { value: val as nat, modulus: p as nat }),
        }
    }

    /// Modular addition.
    pub fn add_exec(&self, rhs: &Self) -> (result: Self)
        requires self.wf_spec(), rhs.wf_spec(), self.p == rhs.p,
        ensures result.wf_spec(), result@ == self@.add_mod(rhs@),
    {
        let sum: u64 = self.val as u64 + rhs.val as u64;
        let p64 = self.p as u64;
        let r = (sum % p64) as u32;
        RuntimeModularInt {
            val: r, p: self.p,
            model: Ghost(self@.add_mod(rhs@)),
        }
    }

    /// Modular subtraction.
    pub fn sub_exec(&self, rhs: &Self) -> (result: Self)
        requires self.wf_spec(), rhs.wf_spec(), self.p == rhs.p,
        ensures result.wf_spec(), result@ == self@.sub_mod(rhs@),
    {
        // a - b mod p = a + (p - b) mod p
        let neg_rhs = self.neg_of(rhs);
        self.add_exec(&neg_rhs)
    }

    /// Modular negation of rhs (using self just for the modulus).
    fn neg_of(&self, rhs: &Self) -> (result: Self)
        requires self.wf_spec(), rhs.wf_spec(), self.p == rhs.p,
        ensures result.wf_spec(), result@ == rhs@.neg_mod(),
    {
        let val = if rhs.val == 0 { 0u32 } else { self.p - rhs.val };
        RuntimeModularInt {
            val, p: self.p,
            model: Ghost(rhs@.neg_mod()),
        }
    }

    /// Modular multiplication.
    pub fn mul_exec(&self, rhs: &Self) -> (result: Self)
        requires self.wf_spec(), rhs.wf_spec(), self.p == rhs.p,
        ensures result.wf_spec(), result@ == self@.mul_mod(rhs@),
    {
        proof {
            let a = self.val as u64;
            let b = rhs.val as u64;
            assert(a <= 0xFFFF_FFFFu64);
            assert(b <= 0xFFFF_FFFFu64);
            assert(a * b <= 0xFFFF_FFFE_0000_0001u64) by (nonlinear_arith)
                requires a <= 0xFFFF_FFFFu64, b <= 0xFFFF_FFFFu64;
        }
        let prod: u64 = self.val as u64 * rhs.val as u64;
        let p64 = self.p as u64;
        let r = (prod % p64) as u32;
        RuntimeModularInt {
            val: r, p: self.p,
            model: Ghost(self@.mul_mod(rhs@)),
        }
    }

    /// Copy.
    pub fn copy_exec(&self) -> (result: Self)
        requires self.wf_spec(),
        ensures result.wf_spec(), result@ == self@,
    {
        RuntimeModularInt { val: self.val, p: self.p, model: Ghost(self@) }
    }
}

} // verus!
