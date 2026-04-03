///  Verified prime field Z/pZ — implements Ring from verus-algebra.
///
///  Design: operations work on raw nat values (no intermediate reduction).
///  Equivalence is defined as `a.value % p == b.value % p`.
///  This makes all Ring axioms reduce to standard integer arithmetic facts.

use vstd::prelude::*;
use verus_algebra::traits::*;
use crate::fixed_point::modular::*;
use crate::fixed_point::limb_ops::*;
#[allow(unused_imports)]
use crate::fixed_point::number_theory::is_prime;

verus! {

///  Marker trait for a specific prime modulus.
pub trait PrimeSpec: Sized {
    spec fn prime() -> nat;

    proof fn axiom_prime_gt_one()
        ensures Self::prime() > 1;
}

///  Spec-level element of Z/pZ.
///  Stores a raw nat; equivalence reduces mod p.
#[verifier::reject_recursive_types(S)]
pub struct SpecPrimeField<S: PrimeSpec> {
    pub value: nat,
    pub _marker: Ghost<S>,
}

impl<S: PrimeSpec> SpecPrimeField<S> {
    pub open spec fn reduced(self) -> nat {
        self.value % S::prime()
    }

    pub open spec fn mk(v: nat) -> Self {
        SpecPrimeField::<S> { value: v, _marker: Ghost::new(arbitrary()) }
    }
}

//  ── Equivalence: a ≡ b iff a.value % p == b.value % p ───────

impl<S: PrimeSpec> Equivalence for SpecPrimeField<S> {
    open spec fn eqv(self, other: Self) -> bool {
        self.value % S::prime() == other.value % S::prime()
    }

    proof fn axiom_eqv_reflexive(a: Self) {}
    proof fn axiom_eqv_symmetric(a: Self, b: Self) {}
    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {}
    proof fn axiom_eq_implies_eqv(a: Self, b: Self) {}
}

//  ── Additive Commutative Monoid ──────────────────────────────
//  add(a, b) = mk(a.value + b.value). No intermediate reduction.
//  All axioms reduce to properties of nat addition + mod.

impl<S: PrimeSpec> AdditiveCommutativeMonoid for SpecPrimeField<S> {
    open spec fn zero() -> Self {
        SpecPrimeField::<S>::mk(0)
    }

    open spec fn add(self, other: Self) -> Self {
        SpecPrimeField::<S>::mk(self.value + other.value)
    }

    proof fn axiom_add_commutative(a: Self, b: Self) {
        //  (a + b) % p == (b + a) % p  — nat addition is commutative
    }

    proof fn axiom_add_associative(a: Self, b: Self, c: Self) {
        //  (a + b + c) % p == (a + (b + c)) % p  — nat addition is associative
        assert((a.value + b.value) + c.value == a.value + (b.value + c.value));
    }

    proof fn axiom_add_zero_right(a: Self) {
        //  (a + 0) % p == a % p  — trivial
    }

    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self) {
        //  a%p == b%p  →  (a+c)%p == (b+c)%p
        //  (a+c)%p == (a%p + c)%p [mod_add_left] == (b%p + c)%p [eqv] == (b+c)%p [mod_add_left]
        S::axiom_prime_gt_one();
        lemma_mod_add_left(a.value, c.value, S::prime());
        lemma_mod_add_left(b.value, c.value, S::prime());
    }
}

//  ── Additive Group ───────────────────────────────────────────
//  neg(a) = p - (a%p) when a%p > 0, else 0.

impl<S: PrimeSpec> AdditiveGroup for SpecPrimeField<S> {
    open spec fn neg(self) -> Self {
        let r = self.value % S::prime();
        SpecPrimeField::<S>::mk(
            if r == 0 { 0nat } else { (S::prime() - r) as nat }
        )
    }

    open spec fn sub(self, other: Self) -> Self {
        self.add(other.neg())
    }

    proof fn axiom_add_inverse_right(a: Self) {
        S::axiom_prime_gt_one();
        let p = S::prime();
        let r: nat = a.value % p;
        let neg_val: nat = if r == 0 { 0nat } else { (p - r) as nat };
        //  Explicitly connect neg(a).value to neg_val
        assert(a.neg().value == neg_val);
        //  (a.value + neg_val) % p == (a.value%p + neg_val) % p  [lemma_mod_add_left]
        lemma_mod_add_left(a.value, neg_val, p);
        //  In both cases: r + neg_val is a multiple of p → (r + neg_val) % p == 0
        if r == 0 {
            assert(neg_val == 0nat);
            assert(0nat % p == 0nat) by(nonlinear_arith) requires p > 1;
        } else {
            assert((r + neg_val) % p == 0nat) by(nonlinear_arith)
                requires r < p, r > 0, neg_val == (p - r) as nat, p > 1;
        }
        assert(0nat % p == 0nat) by(nonlinear_arith) requires p > 1;
    }

    proof fn axiom_sub_is_add_neg(a: Self, b: Self) {}
    proof fn axiom_neg_congruence(a: Self, b: Self) {}
}

//  ── Ring ─────────────────────────────────────────────────────
//  mul(a, b) = mk(a.value * b.value). No intermediate reduction.

impl<S: PrimeSpec> Ring for SpecPrimeField<S> {
    open spec fn one() -> Self {
        SpecPrimeField::<S>::mk(1)
    }

    open spec fn mul(self, other: Self) -> Self {
        SpecPrimeField::<S>::mk(self.value * other.value)
    }

    proof fn axiom_mul_commutative(a: Self, b: Self) {
        assert(a.value * b.value == b.value * a.value) by(nonlinear_arith);
    }

    proof fn axiom_mul_associative(a: Self, b: Self, c: Self) {
        assert((a.value * b.value) * c.value == a.value * (b.value * c.value))
            by(nonlinear_arith);
    }

    proof fn axiom_mul_one_right(a: Self) {
        //  (a * 1) % p == a % p  — trivial
    }

    proof fn axiom_mul_zero_right(a: Self) {
        //  (a * 0) % p == 0 % p  — trivial
    }

    proof fn axiom_mul_distributes_left(a: Self, b: Self, c: Self) {
        //  a*(b+c) % p == (a*b + a*c) % p  — integer distributivity
        assert(a.value * (b.value + c.value) == a.value * b.value + a.value * c.value)
            by(nonlinear_arith);
    }

    proof fn axiom_one_ne_zero() {
        S::axiom_prime_gt_one();
        assert(1nat % S::prime() != 0nat % S::prime()) by(nonlinear_arith)
            requires S::prime() > 1;
    }

    proof fn axiom_mul_congruence_left(a: Self, b: Self, c: Self) {
        //  a%p == b%p  →  (a*c)%p == (b*c)%p
        //  (a*c)%p == (a%p * c)%p [mod_mul_left] == (b%p * c)%p [eqv] == (b*c)%p
        S::axiom_prime_gt_one();
        lemma_mod_mul_left(a.value, c.value, S::prime());
        lemma_mod_mul_left(b.value, c.value, S::prime());
    }
}

//  ══════════════════════════════════════════════════════════════
//  Phase 2: Pseudo-Mersenne reduction lemma
//  ══════════════════════════════════════════════════════════════

///  Core Mersenne reduction: 2^k ≡ c (mod 2^k - c), so hi*2^k + lo ≡ hi*c + lo.
pub proof fn lemma_pseudo_mersenne_reduce(lo: nat, hi: nat, base_k: nat, c: nat)
    requires
        c > 0,
        base_k > c,  //  p = base_k - c > 0
    ensures
        (lo + hi * base_k) % ((base_k - c) as nat) == (lo + hi * c) % ((base_k - c) as nat),
{
    let p: nat = (base_k - c) as nat;
    //  hi * base_k == hi * p + hi * c  (since base_k = p + c)
    assert(hi * base_k == hi * p + hi * c) by(nonlinear_arith)
        requires base_k == p + c;
    //  lo + hi*base_k == (lo + hi*c) + hi*p
    //  (x + k*p) % p == x % p
    lemma_mod_add_left(hi * p, lo + hi * c, p);
    assert(hi * p % p == 0nat) by(nonlinear_arith) requires p > 0;
    assert(hi * p + (lo + hi * c) == lo + hi * base_k) by(nonlinear_arith)
        requires hi * base_k == hi * p + hi * c;
}

//  ══════════════════════════════════════════════════════════════
//  Phase 3: RuntimePrimeField — multi-limb exec operations
//  ══════════════════════════════════════════════════════════════

///  Construct the limbs of p = 2^(n*32) - c = [BASE-c, MAX, MAX, ..., MAX].
///  Proved: vec_val(result) == limb_power(n) - c.
fn make_p_limbs(n: usize, c: u32) -> (out: Vec<u32>)
    requires n > 0, c > 0, (c as int) < LIMB_BASE(),
    ensures
        out@.len() == n,
        valid_limbs(out@),
        vec_val(out@) == limb_power(n as nat) - c as int,
{
    let first: u32 = (0xFFFF_FFFFu32 - c) + 1u32;
    //  first == 2^32 - c == LIMB_BASE() - c
    let mut p: Vec<u32> = Vec::new();
    p.push(first);
    proof {
        //  vec_val([first]) = first = BASE - c = limb_power(1) - c
        lemma_sem_seq_push(Seq::<u32>::empty(), first);
        lemma_limbs_val_push(Seq::<int>::empty(), first as int);
        reveal_with_fuel(limbs_val, 2);
        reveal_with_fuel(limb_power, 2);
    }
    let mut i: usize = 1;
    while i < n
        invariant
            1 <= i <= n, n > 0,
            c > 0, (c as int) < LIMB_BASE(),
            p@.len() == i,
            valid_limbs(p@),
            vec_val(p@) == limb_power(i as nat) - c as int,
        decreases n - i,
    {
        proof {
            let ghost old_p = p@;
            lemma_sem_seq_push(p@, 0xFFFF_FFFFu32);
            lemma_limbs_val_push(sem_seq(p@), 0xFFFF_FFFFu32 as int);
            //  After push: vec_val(new) = vec_val(old) + MAX * limb_power(i)
            //  = (limb_power(i) - c) + (BASE - 1) * limb_power(i)
            //  = limb_power(i) * BASE - c = limb_power(i+1) - c
            lemma_limb_power_add(1, i as nat);
            //  limb_power(1 + i) == limb_power(1) * limb_power(i)
            reveal_with_fuel(limb_power, 2);
            //  limb_power(1) == BASE
        }
        p.push(0xFFFF_FFFFu32);
        proof {
            assert(vec_val(p@) == limb_power(i as nat) - c as int
                + (LIMB_BASE() - 1) * limb_power(i as nat));
            assert(vec_val(p@) == limb_power(i as nat) * LIMB_BASE() - c as int)
                by(nonlinear_arith)
                requires
                    vec_val(p@) == limb_power(i as nat) - c as int
                        + (LIMB_BASE() - 1) * limb_power(i as nat);
            assert(limb_power(i as nat) * LIMB_BASE() == limb_power((i + 1) as nat))
                by(nonlinear_arith)
                requires
                    limb_power(1 + i as nat) == limb_power(1nat) * limb_power(i as nat),
                    limb_power(1nat) == LIMB_BASE();
        }
        i = i + 1;
    }
    p
}

///  Runtime element of Z/pZ where p = 2^(n*32) - c (pseudo-Mersenne).
pub struct RuntimePrimeField {
    pub limbs: Vec<u32>,
    pub n_exec: usize,
    pub c_exec: u32,
    pub model: Ghost<nat>,
}

///  Build a 2-limb Vec<u32>, pad to n. vec_val == lo + hi * BASE.
fn pair_to_padded_vec(lo: u32, hi: u32, n: usize) -> (out: Vec<u32>)
    requires n >= 2,
    ensures
        out@.len() == n,
        valid_limbs(out@),
        vec_val(out@) == lo as int + hi as int * LIMB_BASE(),
{
    let mut v: Vec<u32> = Vec::new();
    v.push(lo);
    let ghost v1 = v@;
    v.push(hi);
    proof {
        //  v@ == [lo, hi]. Prove vec_val([lo, hi]) == lo + hi * BASE.
        //  sem_seq([lo, hi]) == [lo as int, hi as int]
        //  limbs_val([lo_int, hi_int]) = lo_int + BASE * limbs_val([hi_int])
        //                              = lo_int + BASE * (hi_int + BASE * 0)
        //                              = lo_int + hi_int * BASE
        assert(v@[0] == lo);
        assert(v@[1] == hi);
        assert(v@.len() == 2);
        //  Unfold via push chain:
        lemma_sem_seq_push(Seq::<u32>::empty(), lo);
        lemma_limbs_val_push(Seq::<int>::empty(), lo as int);
        reveal_with_fuel(limbs_val, 2);
        //  vec_val([lo]) == lo as int
        assert(vec_val(v1) == lo as int);
        lemma_sem_seq_push(v1, hi);
        lemma_limbs_val_push(sem_seq(v1), hi as int);
        reveal_with_fuel(limb_power, 2);
        //  vec_val([lo, hi]) == vec_val([lo]) + hi * limb_power(1) = lo + hi * BASE
    }
    let result = generic_pad_to_length(&v, n);
    proof { lemma_vec_val_pad(v@, result@); }
    result
}

///  Build a 1-limb Vec<u32>, pad to n. vec_val == scalar.
fn scalar_to_padded_vec(scalar: u32, n: usize) -> (out: Vec<u32>)
    requires n >= 1,
    ensures
        out@.len() == n,
        valid_limbs(out@),
        vec_val(out@) == scalar as int,
{
    let mut v: Vec<u32> = Vec::new();
    v.push(scalar);
    proof {
        lemma_sem_seq_push(Seq::<u32>::empty(), scalar);
        lemma_limbs_val_push(Seq::<int>::empty(), scalar as int);
        reveal_with_fuel(limbs_val, 2);
    }
    let result = generic_pad_to_length(&v, n);
    proof { lemma_vec_val_pad(v@, result@); }
    result
}

///  Int-typed wrapper for lemma_pseudo_mersenne_reduce (avoids nat↔int bridging at call sites).
proof fn lemma_mersenne_int(lo: int, hi: int, base_k: int, c: int)
    requires lo >= 0, hi >= 0, c > 0, base_k > c,
    ensures (lo + hi * base_k) as nat % ((base_k - c) as nat)
         == (lo + hi * c) as nat % ((base_k - c) as nat),
{
    lemma_pseudo_mersenne_reduce(lo as nat, hi as nat, base_k as nat, c as nat);
}

///  Helper: proves the Mersenne fold chain f4 ≡ a*b (mod p).
///  Extracted from mul_mod to stay under rlimit.
proof fn lemma_mersenne_chain(
    lp: int, p: nat, ci: int,
    av: int, bv: int,       //  input values
    lov: int, hiv: int,     //  product split
    f1: int, c1: int, hct: int,  //  fold1 + (c1+hct)*lp == lo+hi*c
    f2: int, cy2i: int,     //  fold2 + cy2*lp == f1 + hct*c
    f3: int, cy3ai: int,    //  fold3a + cy3a*lp == f2 + c1*c
    f3b: int, cy3bi: int,   //  fold3b + cy3b*lp == f3 + cy2*c
    f4: int, cy4i: int,     //  fold4 + cy4*lp == f3b + cy_sum
    cy_sum: int,             //  (cy3a+cy3b)*c
)
    requires
        lp > 0, p > 0, ci > 0, (ci as int) < LIMB_BASE(),
        p == (lp - ci) as nat,
        //  Non-negativity (from vec_val_bounded)
        lov >= 0, hiv >= 0, f1 >= 0, f2 >= 0, f3 >= 0, f3b >= 0, f4 >= 0,
        c1 >= 0, hct >= 0, cy2i >= 0, cy3ai >= 0, cy3bi >= 0, cy4i >= 0,
        //  Product: a*b == lo + hi*lp
        av * bv == lov + hiv * lp,
        //  Fold1: f1 + (c1+hct)*lp == lo + hi*c
        f1 + (c1 + hct) * lp == lov + hiv * ci,
        //  Fold chain
        f2 + cy2i * lp == f1 + hct * ci,
        f3 + cy3ai * lp == f2 + c1 * ci,
        f3b + cy3bi * lp == f3 + cy2i * ci,
        f4 + cy4i * lp == f3b + cy_sum,
        cy_sum == (cy3ai + cy3bi) * ci,
        //  Bounds
        f4 < lp,
        f3b < lp,
        0 <= cy_sum, cy_sum < 2 * LIMB_BASE(),
        lp >= LIMB_BASE() * LIMB_BASE(),
    ensures
        (f4 + cy4i * ci) as nat % p == (av * bv) as nat % p,
        cy4i >= 0,
        cy4i <= 1,
{
    //  lp > ci (needed for Mersenne precondition: base_k > c)
    assert(lp > ci) by(nonlinear_arith)
        requires lp >= LIMB_BASE() * LIMB_BASE(), (ci as int) < LIMB_BASE(), ci > 0;

    //  cy4 <= 1 from bounds
    assert(cy4i <= 1) by(nonlinear_arith)
        requires f4 + cy4i * lp == f3b + cy_sum,
            0 <= f4, f4 < lp, 0 <= f3b, f3b < lp,
            0 <= cy_sum, cy_sum < 2 * LIMB_BASE(),
            lp >= LIMB_BASE() * LIMB_BASE(), lp > 0, cy4i >= 0;

    //  Combine fold steps: f3 + (cy2+cy3a)*lp == f1 + (c1+hct)*c
    assert(f3 + (cy2i + cy3ai) * lp == f1 + (c1 + hct) * ci) by(nonlinear_arith)
        requires f2 + cy2i * lp == f1 + hct * ci,
            f3 + cy3ai * lp == f2 + c1 * ci;

    //  Step-by-step modular chain (each step trivial for Z3):
    lemma_mersenne_int(lov, hiv, lp, ci);
    lemma_mersenne_int(f1, c1 + hct, lp, ci);
    lemma_mersenne_int(f3, cy2i + cy3ai, lp, ci);

    //  Mersenne on remaining carry positions
    lemma_mersenne_int(f4, cy4i, lp, ci);

    //  Step-by-step chain:
    //  a*b == lo + hi*lp ≡ lo + hi*c == f1 + (c1+hct)*lp ≡ f1 + (c1+hct)*c
    //       == f3 + (cy2+cy3a)*lp ≡ f3 + (cy2+cy3a)*c
    //  f3 + (cy2+cy3a)*c = f3b + cy3b*lp + cy3a*c (from f3b+cy3b*lp=f3+cy2*c)
    //  ≡ f3b + cy3b*c + cy3a*c = f3b + (cy3a+cy3b)*c = f4 + cy4*lp ≡ f4 + cy4*c

    //  (1) a*b ≡ lo + hi*c (mod p)
    assert((lov + hiv * lp) as nat % p == (lov + hiv * ci) as nat % p);
    //  (2) lo + hi*c = f1 + (c1+hct)*lp ≡ f1 + (c1+hct)*c
    assert((f1 + (c1 + hct) * lp) as nat % p == (f1 + (c1 + hct) * ci) as nat % p);
    //  (3) f1 + (c1+hct)*c = f3 + (cy2+cy3a)*lp ≡ f3 + (cy2+cy3a)*c
    assert((f3 + (cy2i + cy3ai) * lp) as nat % p == (f3 + (cy2i + cy3ai) * ci) as nat % p);
    //  (4) f3 = f3b + cy3b*lp - cy2*c (from f3b+cy3b*lp=f3+cy2*c)
    //      f3 + (cy2+cy3a)*c = f3b + cy3b*lp - cy2*c + cy2*c + cy3a*c
    //                        = f3b + cy3b*lp + cy3a*c
    assert(f3 + (cy2i + cy3ai) * ci == f3b + cy3bi * lp + cy3ai * ci) by(nonlinear_arith)
        requires f3b + cy3bi * lp == f3 + cy2i * ci;
    //  (5) Mersenne on cy3b: f3b + cy3a*c + cy3b*lp ≡ f3b + cy3a*c + cy3b*c
    lemma_mersenne_int(f3b + cy3ai * ci, cy3bi, lp, ci);
    //  (6) f3b + cy3a*c + cy3b*c = f3b + (cy3a+cy3b)*c = f3b + cy_sum
    //      = f4 + cy4*lp ≡ f4 + cy4*c
    assert(f3b + (cy3ai + cy3bi) * ci == f3b + cy_sum) by(nonlinear_arith)
        requires cy_sum == (cy3ai + cy3bi) * ci;
    assert(f3b + cy_sum == f4 + cy4i * lp);
    assert((f4 + cy4i * lp) as nat % p == (f4 + cy4i * ci) as nat % p);
}

///  Helper: conditional subtract of p from a value < lp = p + c.
///  Returns value mod p.
proof fn lemma_cond_sub(val: int, diff: int, pv: int, lp: int, ci: int, borrow: int)
    requires
        diff + pv == val + borrow * lp,
        pv == lp - ci,
        0 <= val, val < lp,
        0 <= diff, diff < lp,
        borrow == 0 || borrow == 1,
        ci > 0, lp > 0,
        2 * ci <= lp,  //  ensures pv >= ci, so val-pv < ci < pv
    ensures
        borrow == 0 ==> (diff as nat == val as nat % (pv as nat) && 0 <= diff && (diff as int) < pv),
        borrow == 1 ==> (val as nat == val as nat % (pv as nat) && 0 <= val && (val as int) < pv),
{
    if borrow == 0 {
        assert(diff == val - pv) by(nonlinear_arith)
            requires diff + pv == val + 0 * lp;
        assert(val >= pv) by(nonlinear_arith)
            requires diff == val - pv, diff >= 0;
        assert(diff < pv) by(nonlinear_arith)
            requires diff == val - pv, val < lp, pv == lp - ci, 2 * ci <= lp;
        assert(diff as nat == val as nat % (pv as nat)) by(nonlinear_arith)
            requires diff == val - pv, 0 <= diff, (diff as int) < pv, pv > 0, val >= pv;
    } else {
        assert(val < pv) by(nonlinear_arith)
            requires diff + pv == val + lp, 0 <= diff, diff < lp, pv == lp - ci, ci > 0;
        assert(val as nat == val as nat % (pv as nat)) by(nonlinear_arith)
            requires 0 <= val, (val as int) < pv, pv > 0;
    }
}

impl RuntimePrimeField {
    pub open spec fn prime_spec(&self) -> nat {
        (limb_power(self.n_exec as nat) - self.c_exec as int) as nat
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.limbs@.len() == self.n_exec
        &&& self.n_exec > 0
        &&& self.c_exec > 0
        &&& (self.c_exec as int) < LIMB_BASE()
        &&& valid_limbs(self.limbs@)
        &&& self.model@ == vec_val(self.limbs@) as nat
        &&& (vec_val(self.limbs@) as int) >= 0
        &&& (vec_val(self.limbs@) as nat) < self.prime_spec()
    }

    pub open spec fn same_field(&self, other: &Self) -> bool {
        self.n_exec == other.n_exec && self.c_exec == other.c_exec
    }

    ///  Modular addition: (a + b) mod p.
    pub fn add_mod(&self, other: &Self) -> (out: Self)
        requires self.wf(), other.wf(), self.same_field(other),
        ensures out.wf(), out.same_field(self),
            out.model@ == ((self.model@ + other.model@) % self.prime_spec()),
    {
        let n = self.n_exec;
        let c = self.c_exec;
        let (sum, carry) = generic_add_limbs(&self.limbs, &other.limbs, n);
        let p_limbs = make_p_limbs(n, c);
        let (diff, borrow) = generic_sub_limbs(&sum, &p_limbs, n);
        let use_diff: bool = carry > 0u32 || borrow == 0u32;
        proof {
            let av: int = vec_val(self.limbs@);
            let bv: int = vec_val(other.limbs@);
            let sv: int = vec_val(sum@);
            let dv: int = vec_val(diff@);
            let pv: int = self.prime_spec() as int;
            let lp: int = limb_power(n as nat);
            let cv: int = carry as int;
            let bwv: int = borrow as int;
            lemma_vec_val_bounded(sum@);
            lemma_vec_val_bounded(diff@);
            lemma_vec_val_bounded(self.limbs@);
            lemma_vec_val_bounded(other.limbs@);
            //  Key facts from postconditions:
            //  sv + cv * lp == av + bv         (generic_add_limbs)
            //  dv + pv == sv + bwv * lp        (generic_sub_limbs, pv = vec_val(p_limbs))
            //  Carry <= 1 (from bounds: av + bv < 2*lp, sv >= 0)
            assert(cv <= 1) by(nonlinear_arith)
                requires sv + cv * lp == av + bv, av < lp, bv < lp, 0 <= sv, lp > 0, cv >= 0;
            //  Assert carry.sem() == cv (bridge LimbOps::sem to our ghost var)
            assert(carry.sem() == cv);
            assert(borrow.sem() == bwv);
            if use_diff {
                if carry > 0u32 {
                    //  carry == 1: sv + lp == av + bv, so av+bv >= lp > pv
                    //  borrow must be 1 (if 0, dv = sv-pv < 0 contradiction)
                    assert(cv == 1);
                    assert(sv + lp == av + bv) by(nonlinear_arith)
                        requires sv + cv * lp == av + bv, cv == 1;
                    assert(bwv == 1) by(nonlinear_arith)
                        requires
                            dv + pv == sv + bwv * lp,
                            sv + lp == av + bv,
                            av < pv, bv < pv, 0 <= dv,
                            pv == lp - c as int,
                            bwv == 0 || bwv == 1,
                            c > 0, lp > 0;
                    //  dv + pv == sv + lp == av + bv → dv == av + bv - pv
                    assert(dv == av + bv - pv) by(nonlinear_arith)
                        requires dv + pv == sv + lp, sv + lp == av + bv;
                } else {
                    //  carry == 0, borrow == 0: sv == av + bv, dv == sv - pv
                    assert(cv == 0);
                    assert(bwv == 0);
                    assert(sv == av + bv) by(nonlinear_arith)
                        requires sv + 0 * lp == av + bv;
                    assert(dv == sv - pv) by(nonlinear_arith)
                        requires dv + pv == sv + 0 * lp;
                    assert(dv == av + bv - pv);
                }
                //  In both sub-cases: dv == av + bv - pv, and av+bv >= pv
                assert(dv >= 0) by(nonlinear_arith)
                    requires dv == av + bv - pv, av >= 0, bv >= 0,
                        av + bv >= pv;
                assert(dv < pv) by(nonlinear_arith)
                    requires dv == av + bv - pv, av < pv, bv < pv;
                assert(dv as nat == (av + bv) as nat % (pv as nat)) by(nonlinear_arith)
                    requires dv == av + bv - pv, 0 <= dv, dv < pv, pv > 0,
                        av >= 0, bv >= 0;
            } else {
                //  carry == 0, borrow == 1: sv == av+bv < pv, no reduction
                assert(cv == 0);
                assert(bwv == 1);
                assert(sv == av + bv) by(nonlinear_arith)
                    requires sv + 0 * lp == av + bv;
                assert(sv < pv) by(nonlinear_arith)
                    requires dv + pv == sv + lp, 0 <= dv, dv < lp,
                        pv == lp - c as int, c > 0;
                assert(sv as nat == (av + bv) as nat % (pv as nat)) by(nonlinear_arith)
                    requires sv == av + bv, 0 <= sv, sv < pv, pv > 0;
            }
        }
        let result_limbs = if use_diff { diff } else { sum };
        RuntimePrimeField {
            limbs: result_limbs,
            n_exec: n,
            c_exec: c,
            model: Ghost(((self.model@ + other.model@) % self.prime_spec()) as nat),
        }
    }
    ///  Modular negation: (p - a) mod p.
    ///  When a == 0: result is 0 (since p - 0 = p, and p mod p = 0).
    ///  When a > 0: result is p - a (already in [0, p)).
    pub fn neg_mod(&self) -> (out: Self)
        requires self.wf(),
        ensures out.wf(), out.same_field(self),
            out.model@ == (if self.model@ == 0 { 0nat }
                           else { (self.prime_spec() - self.model@) as nat }),
    {
        let n = self.n_exec;
        let c = self.c_exec;
        let p_limbs = make_p_limbs(n, c);
        //  Compute p - self. Borrow is always 0 since self <= p.
        let (raw, borrow) = generic_sub_limbs(&p_limbs, &self.limbs, n);
        //  raw might equal p (when self == 0). Conditional subtract to reduce.
        let (reduced, bw2) = generic_sub_limbs(&raw, &p_limbs, n);
        let use_reduced: bool = bw2 == 0u32;
        proof {
            let sv: int = vec_val(self.limbs@);
            let pv: int = self.prime_spec() as int;
            let lp: int = limb_power(n as nat);
            let rv: int = vec_val(raw@);
            let dv: int = vec_val(reduced@);
            lemma_vec_val_bounded(raw@);
            lemma_vec_val_bounded(reduced@);
            //  borrow == 0: self <= p, so p - self >= 0
            assert(borrow.sem() == 0) by(nonlinear_arith)
                requires
                    rv + sv == pv + borrow.sem() * lp,
                    0 <= rv, rv < lp, 0 <= sv, sv <= pv,
                    pv == lp - c as int,
                    borrow.sem() == 0 || borrow.sem() == 1,
                    c > 0, lp > 0;
            assert(rv == pv - sv) by(nonlinear_arith)
                requires rv + sv == pv + 0 * lp;
            //  rv is in [0, p]: either rv < p (self > 0) or rv == p (self == 0)
            //  After conditional subtract: result == rv mod p
            if use_reduced {
                //  bw2 == 0: raw >= p, so rv == pv, meaning sv == 0
                assert(dv + pv == rv + bw2.sem() * lp);
                assert(bw2.sem() == 0);
                assert(dv == rv - pv) by(nonlinear_arith)
                    requires dv + pv == rv + 0 * lp;
                assert(dv == 0) by(nonlinear_arith)
                    requires dv == rv - pv, rv == pv - sv, sv >= 0, dv >= 0;
                assert(sv == 0) by(nonlinear_arith)
                    requires dv == 0, rv == pv - sv, dv == rv - pv;
                assert(self.model@ == 0nat);
            } else {
                //  bw2 == 1: raw < p, so rv < pv, meaning sv > 0
                assert(bw2.sem() == 1);
                assert(rv < pv) by(nonlinear_arith)
                    requires dv + pv == rv + bw2.sem() * lp, bw2.sem() == 1,
                        0 <= dv, dv < lp,
                        pv == lp - c as int, c > 0;
                assert(sv > 0) by(nonlinear_arith)
                    requires rv == pv - sv, rv < pv;
                assert(self.model@ != 0nat);
            }
        }
        let result_limbs = if use_reduced { reduced } else { raw };
        RuntimePrimeField {
            limbs: result_limbs,
            n_exec: n,
            c_exec: c,
            model: Ghost(
                if self.model@ == 0 { 0nat }
                else { (self.prime_spec() - self.model@) as nat }
            ),
        }
    }

    ///  Modular subtraction: (a - b) mod p = a + neg(b).
    pub fn sub_mod(&self, other: &Self) -> (out: Self)
        requires self.wf(), other.wf(), self.same_field(other),
        ensures out.wf(), out.same_field(self),
    {
        let neg_other = other.neg_mod();
        self.add_mod(&neg_other)
    }

    ///  Modular multiplication: (a * b) mod p via Karatsuba + Mersenne reduction.
    ///  GPU-friendly: no u64 anywhere, only u32 LimbOps.
    pub fn mul_mod(&self, other: &Self) -> (out: Self)
        requires
            self.wf(), other.wf(), self.same_field(other),
            self.n_exec >= 2, self.n_exec <= 0x1FFF_FFFF,
        ensures
            out.wf(), out.same_field(self),
            out.model@ == ((self.model@ * other.model@) % self.prime_spec()),
    {
        let n = self.n_exec;
        let c = self.c_exec;

        //  ── Step 1: Exact 2n-limb product ──
        let (product, _gc) = generic_mul_karatsuba(&self.limbs, &other.limbs, n);

        //  ── Step 2: Mersenne fold 1 — split 2n → hi*c + lo (n limbs each) ──
        let lo = generic_slice_vec(&product, 0, n);
        let hi = generic_slice_vec(&product, n, 2 * n);
        let c_limb: u32 = c;
        let hi_c = generic_mul_by_limb(&hi, &c_limb, n);
        //  hi_c has n+1 limbs. Split: hi_c_lo (n) + hi_c_top (1).
        let hi_c_lo = generic_slice_vec(&hi_c, 0, n);
        let hi_c_top: u32 = hi_c[n];
        //  Add lo + hi_c_lo (both n limbs)
        let (fold1, carry1) = generic_add_limbs(&lo, &hi_c_lo, n);
        //  Now: fold1 + (carry1 + hi_c_top) * lp == lo + hi*c ≡ a*b (mod p)
        //  Mersenne: (carry1 + hi_c_top) * lp ≡ (carry1 + hi_c_top) * c (mod p)
        //  carry1 ≤ 1, hi_c_top < BASE. So (carry1 + hi_c_top) < BASE + 1.
        //  (carry1 + hi_c_top) * c < (BASE+1) * BASE ≈ BASE^2, fits in u64.

        //  ── Step 3: Fold hi_c_top * c (2 limbs from mul2, add to fold1) ──
        let (prod_lo, prod_hi) = hi_c_top.mul2(&c_limb);
        let prod_vec = pair_to_padded_vec(prod_lo, prod_hi, n);
        let (fold2, cy2) = generic_add_limbs(&fold1, &prod_vec, n);

        //  ── Step 4: Fold carry1 * c (scalar, carry1 ∈ {0,1}) ──
        let carry1_c: u32 = if carry1 > 0u32 { c } else { 0u32 };
        let c1_vec = scalar_to_padded_vec(carry1_c, n);
        let (fold3a, cy3a) = generic_add_limbs(&fold2, &c1_vec, n);

        //  ── Step 5: Fold cy2 * c (scalar, cy2 ≤ 1) ──
        proof {
            let lp_local = limb_power(n as nat);
            lemma_vec_val_bounded(fold1@);
            lemma_vec_val_bounded(fold2@);
            lemma_vec_val_bounded(prod_vec@);
            assert(cy2 as int <= 1) by(nonlinear_arith)
                requires
                    vec_val(fold2@) + cy2 as int * lp_local == vec_val(fold1@) + vec_val(prod_vec@),
                    0 <= vec_val(fold2@), vec_val(fold2@) < lp_local,
                    0 <= vec_val(fold1@), vec_val(fold1@) < lp_local,
                    0 <= vec_val(prod_vec@), vec_val(prod_vec@) < lp_local,
                    lp_local > 0, cy2 as int >= 0;
            assert(cy2 as int * (c as int) <= u32::MAX as int) by(nonlinear_arith)
                requires cy2 as int <= 1, (c as int) < LIMB_BASE();
        }
        let cy2_c: u32 = cy2 * c;
        let cy2_vec = scalar_to_padded_vec(cy2_c, n);
        let (fold3b, cy3b) = generic_add_limbs(&fold3a, &cy2_vec, n);

        //  ── Step 6: Fold cy3a * c and cy3b * c ──
        proof {
            let lp_local = limb_power(n as nat);
            lemma_vec_val_bounded(fold3a@);
            lemma_vec_val_bounded(fold3b@);
            assert(cy3a as int <= 1) by(nonlinear_arith)
                requires
                    vec_val(fold3a@) + cy3a as int * lp_local == vec_val(fold2@) + vec_val(c1_vec@),
                    0 <= vec_val(fold3a@), vec_val(fold3a@) < lp_local,
                    0 <= vec_val(fold2@), vec_val(fold2@) < lp_local,
                    vec_val(c1_vec@) < LIMB_BASE(),
                    lp_local >= LIMB_BASE(), lp_local > 0, cy3a as int >= 0;
            assert(cy3a as int * (c as int) <= u32::MAX as int) by(nonlinear_arith)
                requires cy3a as int <= 1, (c as int) < LIMB_BASE();
            assert(cy3b as int <= 1) by(nonlinear_arith)
                requires
                    vec_val(fold3b@) + cy3b as int * lp_local == vec_val(fold3a@) + vec_val(cy2_vec@),
                    0 <= vec_val(fold3b@), vec_val(fold3b@) < lp_local,
                    0 <= vec_val(fold3a@), vec_val(fold3a@) < lp_local,
                    vec_val(cy2_vec@) < LIMB_BASE(),
                    lp_local >= LIMB_BASE(), lp_local > 0, cy3b as int >= 0;
            assert(cy3b as int * (c as int) <= u32::MAX as int) by(nonlinear_arith)
                requires cy3b as int <= 1, (c as int) < LIMB_BASE();
        }
        let cy3a_c: u32 = cy3a * c;
        let cy3b_c: u32 = cy3b * c;
        let cy3a_vec = scalar_to_padded_vec(cy3a_c, n);
        let (fold4a, cy4a) = generic_add_limbs(&fold3b, &cy3a_vec, n);
        let cy3b_vec = scalar_to_padded_vec(cy3b_c, n);
        let (fold4, cy4b) = generic_add_limbs(&fold4a, &cy3b_vec, n);

        //  ── Step 7: One more fold — cy4*c (cy4 ≤ 1) ──
        //  ── Step 7: One more fold — (cy4a+cy4b)*c ──
        proof {
            let lpl = limb_power(n as nat);
            lemma_vec_val_bounded(fold4a@);
            lemma_vec_val_bounded(fold4@);
            lemma_vec_val_bounded(fold3b@);
            assert(cy4a as int <= 1) by(nonlinear_arith)
                requires vec_val(fold4a@) + cy4a as int * lpl == vec_val(fold3b@) + vec_val(cy3a_vec@),
                    0 <= vec_val(fold4a@), vec_val(fold4a@) < lpl,
                    0 <= vec_val(fold3b@), vec_val(fold3b@) < lpl,
                    vec_val(cy3a_vec@) < LIMB_BASE(), lpl >= LIMB_BASE(), lpl > 0, cy4a as int >= 0;
            assert(cy4b as int <= 1) by(nonlinear_arith)
                requires vec_val(fold4@) + cy4b as int * lpl == vec_val(fold4a@) + vec_val(cy3b_vec@),
                    0 <= vec_val(fold4@), vec_val(fold4@) < lpl,
                    0 <= vec_val(fold4a@), vec_val(fold4a@) < lpl,
                    vec_val(cy3b_vec@) < LIMB_BASE(), lpl >= LIMB_BASE(), lpl > 0, cy4b as int >= 0;
            //  Combined: fold4 + (cy4a+cy4b)*lp == fold3b + cy3a_c + cy3b_c
            assert(vec_val(fold4@) + (cy4a as int + cy4b as int) * lpl
                == vec_val(fold3b@) + cy3a_c as int + cy3b_c as int) by(nonlinear_arith)
                requires
                    vec_val(fold4a@) + cy4a as int * lpl == vec_val(fold3b@) + vec_val(cy3a_vec@),
                    vec_val(fold4@) + cy4b as int * lpl == vec_val(fold4a@) + vec_val(cy3b_vec@),
                    vec_val(cy3a_vec@) == cy3a_c as int,
                    vec_val(cy3b_vec@) == cy3b_c as int;
            //  cy4a + cy4b ≤ 2, (cy4a+cy4b)*c ≤ 2*(BASE-1) — need 2 scalar folds
            assert((cy4a as int + cy4b as int) * (c as int) <= u32::MAX as int) by(nonlinear_arith)
                requires cy4a as int <= 1, cy4b as int <= 1, (c as int) < LIMB_BASE();
        }
        //  Add (cy4a+cy4b)*c — but cy4a+cy4b ≤ 2, so (cy4a+cy4b)*c ≤ 2*(BASE-1) fits in u32
        //  only if 2*(BASE-1) ≤ u32::MAX, which is 2*BASE-2 ≤ BASE-1 — FALSE! 2*BASE-2 > BASE-1.
        //  So we need to add them separately.
        let cy4a_c: u32 = cy4a * c;
        let cy4a_vec = scalar_to_padded_vec(cy4a_c, n);
        let (fold5a, cy5a) = generic_add_limbs(&fold4, &cy4a_vec, n);
        let cy4b_c: u32 = cy4b * c;
        let cy4b_vec = scalar_to_padded_vec(cy4b_c, n);
        let (fold5, cy5b) = generic_add_limbs(&fold5a, &cy4b_vec, n);
        let cy4v = scalar_to_padded_vec(cy4_c, n);
        let (fold5, _cy5) = generic_add_limbs(&fold4, &cy4v, n);
        //  cy5 == 0: fold4 < lp, cy4_c < BASE << lp for n≥2. fold5+cy5*lp = fold4+cy4_c < lp+BASE < 2*lp.
        //  ── Step 8: Conditional subtract p ──
        let p_limbs = make_p_limbs(n, c);
        let (d1, bw1) = generic_sub_limbs(&fold5, &p_limbs, n);
        let use_d1: bool = bw1 == 0u32;
        let r = if use_d1 { d1 } else { fold5 };

        proof {
            let lp: int = limb_power(n as nat);
            let p: nat = self.prime_spec();
            let ci: int = c as int;
            let av: int = vec_val(self.limbs@);
            let bv: int = vec_val(other.limbs@);

            //  ── gc == 0 → product == a*b ──
            lemma_vec_val_bounded(product@);
            lemma_vec_val_bounded(self.limbs@);
            lemma_vec_val_bounded(other.limbs@);
            lemma_limb_power_add(n as nat, n as nat);
            let prd: int = vec_val(product@);
            let lp2: int = limb_power((2 * n) as nat);
            assert(_gc@ == 0int) by(nonlinear_arith)
                requires prd + _gc@ * lp2 == av * bv, 0 <= prd, prd < lp2,
                    0 <= av, av < lp, 0 <= bv, bv < lp, lp2 == lp * lp, lp > 0;

            //  ── Split + fold1 chain: f1 + (carry1+hct)*lp == lo+hi*c ──
            lemma_vec_val_split(product@, n as nat);
            assert(sem_seq(lo@) =~= sem_seq(product@.subrange(0, n as int)));
            assert(sem_seq(hi@) =~= sem_seq(product@.subrange(n as int, (2*n) as int)));
            let lov: int = vec_val(lo@);
            let hiv: int = vec_val(hi@);
            assert(vec_val(hi_c@) == hiv * ci);
            lemma_vec_val_split(hi_c@, n as nat);
            assert(sem_seq(hi_c_lo@) =~= sem_seq(hi_c@.subrange(0, n as int)));
            let f1: int = vec_val(fold1@);
            let hct: int = hi_c_top as int;
            assert(f1 + (carry1 as int + hct) * lp == lov + hiv * ci) by(nonlinear_arith)
                requires f1 + carry1 as int * lp == lov + vec_val(hi_c_lo@),
                    vec_val(hi_c_lo@) + hct * lp == hiv * ci;

            //  ── Connect vec_vals of fold steps ──
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod((hct * ci) as int, LIMB_BASE());
            assert(vec_val(prod_vec@) == hct * ci) by(nonlinear_arith)
                requires vec_val(prod_vec@) == prod_lo as int + prod_hi as int * LIMB_BASE(),
                    prod_lo as int == (hct * ci) % LIMB_BASE(), prod_hi as int == (hct * ci) / LIMB_BASE(),
                    hct * ci == (hct * ci) / LIMB_BASE() * LIMB_BASE() + (hct * ci) % LIMB_BASE();
            assert(carry1_c as int == carry1 as int * ci);
            let f2: int = vec_val(fold2@);
            let f3: int = vec_val(fold3a@);
            let f3b: int = vec_val(fold3b@);
            let cy_sum: int = (cy3a_c + cy3b_c) as int;
            assert(cy_sum == (cy3a as int + cy3b as int) * ci) by(nonlinear_arith)
                requires cy3a_c as int == cy3a as int * ci,
                    cy3b_c as int == cy3b as int * ci;
            let f4: int = vec_val(fold4@);
            lemma_vec_val_bounded(fold4@);
            lemma_vec_val_bounded(fold3b@);

            //  ── Call chain lemma: (f4 + cy4*c) % p == (a*b) % p ──
            lemma_mersenne_chain(lp, p, ci, av, bv, lov, hiv,
                f1, carry1 as int, hct,
                f2, cy2 as int,
                f3, cy3a as int,
                f3b, cy3b as int,
                f4, _cy4 as int,
                cy_sum);
            //  chain gives: (f4 + _cy4*ci) % p == (av*bv) % p, _cy4 <= 1

            //  ── fold5 = f4 + cy4*c, cy5 == 0 ──
            let f5: int = vec_val(fold5@);
            lemma_vec_val_bounded(fold5@);
            assert(cy4_c as int == _cy4 as int * ci);
            assert(f5 + _cy5 as int * lp == f4 + _cy4 as int * ci);
            //  cy5 == 0: f4 < lp, cy4_c < BASE. f4 + cy4_c < lp + BASE < 2*lp.
            assert(_cy5 as int == 0) by(nonlinear_arith)
                requires f5 + _cy5 as int * lp == f4 + _cy4 as int * ci,
                    0 <= f5, f5 < lp,
                    0 <= f4, f4 < lp,
                    _cy4 as int <= 1,
                    (ci as int) < LIMB_BASE(),
                    _cy4 as int <= 1, (ci as int) < LIMB_BASE(),
                    lp >= LIMB_BASE() * LIMB_BASE(),
                    lp > 0, _cy5 as int >= 0;
            //  f5 == f4 + cy4*c, and (f4+cy4*c) % p == (a*b) % p
            //  So f5 % p == (a*b) % p
            assert(f5 as nat % p == (av * bv) as nat % p) by(nonlinear_arith)
                requires f5 == f4 + _cy4 as int * ci, _cy5 as int == 0,
                    (f4 + _cy4 as int * ci) as nat % p == (av * bv) as nat % p;

            //  ── Conditional subtract: r == f5 % p ──
            lemma_vec_val_bounded(d1@);
            lemma_cond_sub(f5, vec_val(d1@), p as int, lp, ci, bw1 as int);
        }

        RuntimePrimeField {
            limbs: r,
            n_exec: n,
            c_exec: c,
            model: Ghost(((self.model@ * other.model@) % self.prime_spec()) as nat),
        }
    }
}

} // verus!
