use vstd::prelude::*;

verus! {

/// Element of Z/pZ — a natural number modulo a given modulus.
pub struct ModularInt {
    pub value: nat,
    pub modulus: nat,
}

impl ModularInt {
    /// Well-formedness: value < modulus and modulus > 1.
    pub open spec fn wf_spec(self) -> bool {
        self.value < self.modulus && self.modulus > 1
    }

    /// Same modulus check.
    pub open spec fn same_modulus(self, other: ModularInt) -> bool {
        self.modulus == other.modulus
    }

    /// Zero element.
    pub open spec fn zero(p: nat) -> ModularInt {
        ModularInt { value: 0, modulus: p }
    }

    /// One element.
    pub open spec fn one(p: nat) -> ModularInt {
        ModularInt { value: 1, modulus: p }
    }

    /// Addition mod p.
    pub open spec fn add_mod(self, rhs: ModularInt) -> ModularInt {
        ModularInt {
            value: (self.value + rhs.value) % self.modulus,
            modulus: self.modulus,
        }
    }

    /// Negation mod p: p - value (or 0 if value == 0).
    pub open spec fn neg_mod(self) -> ModularInt {
        ModularInt {
            value: if self.value == 0 { 0 } else { (self.modulus - self.value) as nat },
            modulus: self.modulus,
        }
    }

    /// Subtraction mod p.
    pub open spec fn sub_mod(self, rhs: ModularInt) -> ModularInt {
        self.add_mod(rhs.neg_mod())
    }

    /// Multiplication mod p.
    pub open spec fn mul_mod(self, rhs: ModularInt) -> ModularInt {
        ModularInt {
            value: (self.value * rhs.value) % self.modulus,
            modulus: self.modulus,
        }
    }

    /// Equivalence (same value mod p).
    pub open spec fn eqv(self, rhs: ModularInt) -> bool {
        self.value == rhs.value && self.modulus == rhs.modulus
    }

    /// Exponentiation by squaring (spec level).
    pub open spec fn pow_mod(self, exp: nat) -> ModularInt
        decreases exp,
    {
        if exp == 0 {
            Self::one(self.modulus)
        } else if exp % 2 == 0 {
            let half = self.pow_mod(exp / 2);
            half.mul_mod(half)
        } else {
            self.mul_mod(self.pow_mod((exp - 1) as nat))
        }
    }
}

// ── Well-formedness preservation ───────────────────────

/// Zero is well-formed for p > 1.
pub proof fn lemma_zero_wf(p: nat)
    requires p > 1,
    ensures ModularInt::zero(p).wf_spec(),
{}

/// One is well-formed for p > 1.
pub proof fn lemma_one_wf(p: nat)
    requires p > 1,
    ensures ModularInt::one(p).wf_spec(),
{}

/// Addition preserves well-formedness.
pub proof fn lemma_add_mod_wf(a: ModularInt, b: ModularInt)
    requires a.wf_spec(), b.wf_spec(), a.same_modulus(b),
    ensures a.add_mod(b).wf_spec(),
{
    assert((a.value + b.value) % a.modulus < a.modulus) by (nonlinear_arith)
        requires a.modulus > 1;
}

/// Negation preserves well-formedness.
pub proof fn lemma_neg_mod_wf(a: ModularInt)
    requires a.wf_spec(),
    ensures a.neg_mod().wf_spec(), a.neg_mod().same_modulus(a),
{
    if a.value > 0 {
        let neg = (a.modulus - a.value) as nat;
        assert(neg < a.modulus);
    }
}

/// Multiplication preserves well-formedness.
pub proof fn lemma_mul_mod_wf(a: ModularInt, b: ModularInt)
    requires a.wf_spec(), b.wf_spec(), a.same_modulus(b),
    ensures a.mul_mod(b).wf_spec(),
{
    assert((a.value * b.value) % a.modulus < a.modulus) by (nonlinear_arith)
        requires a.modulus > 1;
}

// ── Modular arithmetic helpers ─────────────────────────

/// (a % p + b) % p == (a + b) % p
pub proof fn lemma_mod_add_left(a: nat, b: nat, p: nat)
    requires p > 0,
    ensures (a % p + b) % p == (a + b) % p,
{
    assert((a % p + b) % p == (a + b) % p) by (nonlinear_arith)
        requires p > 0;
}

/// (a + b % p) % p == (a + b) % p
pub proof fn lemma_mod_add_right(a: nat, b: nat, p: nat)
    requires p > 0,
    ensures (a + b % p) % p == (a + b) % p,
{
    assert((a + b % p) % p == (a + b) % p) by (nonlinear_arith)
        requires p > 0;
}

/// (a % p * b) % p == (a * b) % p
pub proof fn lemma_mod_mul_left(a: nat, b: nat, p: nat)
    requires p > 0,
    ensures (a % p * b) % p == (a * b) % p,
{
    assert((a % p * b) % p == (a * b) % p) by (nonlinear_arith)
        requires p > 0;
}

/// (a * b % p) % p == (a * b) % p
pub proof fn lemma_mod_mul_right(a: nat, b: nat, p: nat)
    requires p > 0,
    ensures (a * (b % p)) % p == (a * b) % p,
{
    assert((a * (b % p)) % p == (a * b) % p) by (nonlinear_arith)
        requires p > 0;
}

// ── Ring axioms ────────────────────────────────────────

/// Addition is commutative: a + b == b + a (mod p).
pub proof fn lemma_add_commutative(a: ModularInt, b: ModularInt)
    requires a.wf_spec(), b.wf_spec(), a.same_modulus(b),
    ensures a.add_mod(b).eqv(b.add_mod(a)),
{}

/// Addition is associative: (a + b) + c == a + (b + c) (mod p).
pub proof fn lemma_add_associative(a: ModularInt, b: ModularInt, c: ModularInt)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(),
             a.same_modulus(b), b.same_modulus(c),
    ensures a.add_mod(b).add_mod(c).eqv(a.add_mod(b.add_mod(c))),
{
    let p = a.modulus;
    let av = a.value; let bv = b.value; let cv = c.value;
    lemma_mod_add_left(av + bv, cv, p);
    lemma_mod_add_right(av, bv + cv, p);
}

/// Zero is additive identity: a + 0 == a (mod p).
pub proof fn lemma_add_zero_right(a: ModularInt)
    requires a.wf_spec(),
    ensures a.add_mod(ModularInt::zero(a.modulus)).eqv(a),
{
    let p = a.modulus;
    assert((a.value + 0) % p == a.value) by (nonlinear_arith)
        requires a.value < p, p > 1;
}

/// Negation is additive inverse: a + (-a) == 0 (mod p).
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

/// Multiplication is commutative: a * b == b * a (mod p).
pub proof fn lemma_mul_commutative(a: ModularInt, b: ModularInt)
    requires a.wf_spec(), b.wf_spec(), a.same_modulus(b),
    ensures a.mul_mod(b).eqv(b.mul_mod(a)),
{
    assert(a.value * b.value == b.value * a.value) by (nonlinear_arith);
}

/// Multiplication is associative: (a * b) * c == a * (b * c) (mod p).
pub proof fn lemma_mul_associative(a: ModularInt, b: ModularInt, c: ModularInt)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(),
             a.same_modulus(b), b.same_modulus(c),
    ensures a.mul_mod(b).mul_mod(c).eqv(a.mul_mod(b.mul_mod(c))),
{
    let p = a.modulus;
    let av = a.value; let bv = b.value; let cv = c.value;
    lemma_mod_mul_left(av * bv, cv, p);
    lemma_mod_mul_right(av, bv * cv, p);
    assert(av * bv * cv == av * (bv * cv)) by (nonlinear_arith);
}

/// One is multiplicative identity: a * 1 == a (mod p).
pub proof fn lemma_mul_one_right(a: ModularInt)
    requires a.wf_spec(),
    ensures a.mul_mod(ModularInt::one(a.modulus)).eqv(a),
{
    let p = a.modulus;
    assert((a.value * 1) % p == a.value) by (nonlinear_arith)
        requires a.value < p, p > 1;
}

/// Zero annihilates: a * 0 == 0 (mod p).
pub proof fn lemma_mul_zero_right(a: ModularInt)
    requires a.wf_spec(),
    ensures a.mul_mod(ModularInt::zero(a.modulus)).eqv(ModularInt::zero(a.modulus)),
{
    let p = a.modulus;
    assert((a.value * 0) % p == 0) by (nonlinear_arith)
        requires p > 1;
}

/// Distributive law: a * (b + c) == a*b + a*c (mod p).
pub proof fn lemma_mul_distributes_left(a: ModularInt, b: ModularInt, c: ModularInt)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(),
             a.same_modulus(b), b.same_modulus(c),
    ensures a.mul_mod(b.add_mod(c)).eqv(a.mul_mod(b).add_mod(a.mul_mod(c))),
{
    let p = a.modulus;
    let av = a.value; let bv = b.value; let cv = c.value;
    lemma_mod_mul_right(av, bv + cv, p);
    // (av * (bv+cv)) % p
    lemma_mul_distribute(av as int, 0, (bv + cv) as int);
    // av * (bv + cv) == av * bv + av * cv
    assert(av * (bv + cv) == av * bv + av * cv) by (nonlinear_arith);
    // (av*bv + av*cv) % p == ((av*bv)%p + (av*cv)%p) % p
    lemma_mod_add_left(av * bv, av * cv, p);
    lemma_mod_add_right(av * bv % p, av * cv, p);
}

/// One != Zero (for ring with unity).
pub proof fn lemma_one_ne_zero(p: nat)
    requires p > 1,
    ensures !ModularInt::one(p).eqv(ModularInt::zero(p)),
{}

} // verus!
