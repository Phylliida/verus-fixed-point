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
    //  cy4 <= 1 from bounds
    assert(cy4i <= 1) by(nonlinear_arith)
        requires f4 + cy4i * lp == f3b + cy_sum,
            0 <= f4, f4 < lp, 0 <= f3b, f3b < lp,
            0 <= cy_sum, cy_sum < 2 * LIMB_BASE(),
            lp >= LIMB_BASE() * LIMB_BASE(), lp > 0, cy4i >= 0;

    //  Key algebraic insight: substitute fold equations step by step to show
    //  f4 + cy4i*ci == av*bv - k*(lp-ci) where k = hiv+hct+c1+cy2i+cy3ai+cy3bi+cy4i.
    //  Then (f4+cy4i*ci) % p == (av*bv) % p since the difference is k*p.

    //  Step-by-step substitution (each step ≤ 2 equations):
    //  From eqs 5+6: f1 expressed in terms of av*bv
    assert(f1 == av * bv + hiv * ci - (hiv + c1 + hct) * lp) by(nonlinear_arith)
        requires f1 + (c1 + hct) * lp == lov + hiv * ci, lov + hiv * lp == av * bv;
    //  From eq 4: f2
    assert(f2 == av * bv + (hiv + hct) * ci - (hiv + c1 + hct + cy2i) * lp) by(nonlinear_arith)
        requires f2 + cy2i * lp == f1 + hct * ci,
            f1 == av * bv + hiv * ci - (hiv + c1 + hct) * lp;
    //  From eq 3: f3
    assert(f3 == av * bv + (hiv + hct + c1) * ci - (hiv + c1 + hct + cy2i + cy3ai) * lp) by(nonlinear_arith)
        requires f3 + cy3ai * lp == f2 + c1 * ci,
            f2 == av * bv + (hiv + hct) * ci - (hiv + c1 + hct + cy2i) * lp;
    //  From eq 2: f3b — use intermediate vars to keep nonlinear_arith simple
    let s_val: int = hiv + hct + c1 + cy2i;
    let s1_val: int = s_val + cy3ai + cy3bi;
    let k: int = s1_val + cy4i;
    //  Restate f3 in s_val terms (split (hiv+hct+c1) = s_val - cy2i)
    assert(f3 == av * bv + (s_val - cy2i) * ci - (s_val + cy3ai) * lp) by(nonlinear_arith)
        requires f3 == av * bv + (hiv + hct + c1) * ci - (hiv + c1 + hct + cy2i + cy3ai) * lp,
            s_val == hiv + hct + c1 + cy2i;
    //  Now derive f3b
    assert(f3b == av * bv + s_val * ci - s1_val * lp) by(nonlinear_arith)
        requires f3b + cy3bi * lp == f3 + cy2i * ci,
            f3 == av * bv + (s_val - cy2i) * ci - (s_val + cy3ai) * lp,
            s1_val == s_val + cy3ai + cy3bi;
    //  From eq 1: f4
    //  Sub-step: f4 = f3b + (cy3ai+cy3bi)*ci - cy4i*lp = av*bv + s1*ci - k*lp
    assert(f4 == av * bv + s1_val * ci - k * lp) by(nonlinear_arith)
        requires f4 + cy4i * lp == f3b + (cy3ai + cy3bi) * ci,
            f3b == av * bv + s_val * ci - s1_val * lp,
            s1_val == s_val + cy3ai + cy3bi,
            k == s1_val + cy4i;
    //  Therefore: f4 + cy4i*ci == av*bv - k*(lp-ci) == av*bv - k*p
    assert(f4 + cy4i * ci == av * bv - k * (lp - ci)) by(nonlinear_arith)
        requires f4 == av * bv + s1_val * ci - k * lp, k == s1_val + cy4i;

    //  Modular conclusion: (f4+cy4i*ci) % p == (av*bv) % p
    assert(f4 + cy4i * ci >= 0) by(nonlinear_arith) requires f4 >= 0, cy4i >= 0, ci >= 0;
    assert(lp > ci) by(nonlinear_arith)
        requires lp >= LIMB_BASE() * LIMB_BASE(), (ci as int) < LIMB_BASE(), ci > 0;
    assert(k >= 0) by(nonlinear_arith)
        requires s_val >= 0, s1_val >= 0, cy4i >= 0,
            s_val == hiv + hct + c1 + cy2i, s1_val == s_val + cy3ai + cy3bi, k == s1_val + cy4i;
    lemma_mod_add_left((k * (lp - ci)) as nat, (f4 + cy4i * ci) as nat, (lp - ci) as nat);
    assert(((k * (lp - ci)) as nat) % ((lp - ci) as nat) == 0nat) by(nonlinear_arith)
        requires lp > ci, k >= 0;
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

///  Carry from adding two n-limb values is ≤ 1.
proof fn lemma_carry_le_1(fv: int, cy: int, lp: int, av: int, bv: int)
    requires fv + cy * lp == av + bv,
        0 <= fv, fv < lp, 0 <= av, av < lp, 0 <= bv, bv < lp, lp > 0, cy >= 0,
    ensures cy <= 1,
{
    assert(cy <= 1) by(nonlinear_arith)
        requires fv + cy * lp == av + bv, 0 <= fv, av < lp, bv < lp, lp > 0, cy >= 0;
}

///  Carry from adding an n-limb value and a scalar < BASE is ≤ 1.
proof fn lemma_scalar_carry_le_1(fv: int, cy: int, lp: int, av: int, sv: int)
    requires fv + cy * lp == av + sv,
        0 <= fv, fv < lp, 0 <= av, av < lp,
        0 <= sv, sv < lp,
        lp > 0, cy >= 0,
    ensures cy <= 1,
{
    assert(cy <= 1) by(nonlinear_arith)
        requires fv + cy * lp == av + sv, 0 <= fv, av < lp, sv < lp, lp > 0, cy >= 0;
}

///  carry * c fits in u32 when carry ≤ 1 and c < BASE.
proof fn lemma_carry_mul_fits(cy: int, ci: int)
    requires cy <= 1, cy >= 0, 0 < ci, (ci) < LIMB_BASE(),
    ensures cy * ci <= u32::MAX as int,
{}

///  Chain proof for mersenne_reduce_exec: fold8 + k*p == product.
///  Uses step-by-step substitution to stay under nonlinear_arith limits.
proof fn lemma_reduce_chain(
    lp: int, ci: int,
    prd: int, lov: int, hiv: int,
    wlo: int, wt: int, wcy: int,
    f2: int, c2: int, f3: int, c3: int,
    f4: int, c4: int, f5: int, c5: int,
    f6: int, c6: int, f7: int, c7: int,
    f8: int, c8: int, fc: int,
)
    requires
        lp > 0, ci > 0, (ci) < LIMB_BASE(), lp >= LIMB_BASE() * LIMB_BASE(),
        //  All values non-negative
        lov >= 0, hiv >= 0, wlo >= 0, wt >= 0, wcy >= 0,
        f2 >= 0, f3 >= 0, f4 >= 0, f5 >= 0, f6 >= 0, f7 >= 0, f8 >= 0,
        c2 >= 0, c3 >= 0, c4 >= 0, c5 >= 0, c6 >= 0, c7 >= 0, c8 >= 0, fc >= 0,
        //  Fold equations
        prd == lov + hiv * lp,
        wlo + (wt + wcy * LIMB_BASE()) * lp == lov + hiv * ci,
        f2 + c2 * lp == wlo + wt * ci,
        f3 + c3 * lp == f2 + wcy * ci * LIMB_BASE(),
        f4 + c4 * lp == f3 + c2 * ci,
        f5 + c5 * lp == f4 + c3 * ci,
        f6 + c6 * lp == f5 + c4 * ci,
        f7 + c7 * lp == f6 + c5 * ci,
        f8 + c8 * lp == f7 + fc,
        fc == (c6 + c7) * ci,
        c8 == 0,
    ensures
        f8 as nat % ((lp - ci) as nat) == prd as nat % ((lp - ci) as nat),
{
    //  Step-by-step substitution (each ≤ 2 equations, manageable for nonlinear_arith):
    let s0: int = hiv;
    assert(wlo == lov + hiv * ci - (wt + wcy * LIMB_BASE()) * lp);
    //  f2 in terms of lov
    let s1: int = wt + wcy * LIMB_BASE();
    assert(f2 == lov + s0 * ci - (s1 + c2) * lp + wt * ci) by(nonlinear_arith)
        requires f2 + c2 * lp == wlo + wt * ci,
            wlo == lov + hiv * ci - s1 * lp, s0 == hiv;
    //  Simplify: f2 == lov + (s0 + wt)*ci - (s1 + c2)*lp
    let a2: int = s0 + wt;
    let b2: int = s1 + c2;
    assert(f2 == lov + a2 * ci - b2 * lp) by(nonlinear_arith)
        requires f2 == lov + s0 * ci - (s1 + c2) * lp + wt * ci, a2 == s0 + wt, b2 == s1 + c2;
    //  f3
    let a3: int = a2 + wcy * LIMB_BASE();
    let b3: int = b2 + c3;
    assert(f3 == lov + a3 * ci - b3 * lp) by(nonlinear_arith)
        requires f3 + c3 * lp == f2 + wcy * ci * LIMB_BASE(),
            f2 == lov + a2 * ci - b2 * lp, a3 == a2 + wcy * LIMB_BASE(), b3 == b2 + c3;
    //  f4
    assert(f4 == lov + (a3 + c2) * ci - (b3 + c4) * lp) by(nonlinear_arith)
        requires f4 + c4 * lp == f3 + c2 * ci, f3 == lov + a3 * ci - b3 * lp;
    //  f5
    assert(f5 == lov + (a3+c2+c3) * ci - (b3+c4+c5) * lp) by(nonlinear_arith)
        requires f5 + c5 * lp == f4 + c3 * ci, f4 == lov + (a3+c2) * ci - (b3+c4) * lp;
    //  f6
    assert(f6 == lov + (a3+c2+c3+c4) * ci - (b3+c4+c5+c6) * lp) by(nonlinear_arith)
        requires f6 + c6 * lp == f5 + c4 * ci, f5 == lov + (a3+c2+c3) * ci - (b3+c4+c5) * lp;
    //  f7
    assert(f7 == lov + (a3+c2+c3+c4+c5) * ci - (b3+c4+c5+c6+c7) * lp) by(nonlinear_arith)
        requires f7 + c7 * lp == f6 + c5 * ci, f6 == lov + (a3+c2+c3+c4) * ci - (b3+c4+c5+c6) * lp;
    //  f8 = f7 + (c6+c7)*ci (since c8 == 0)
    assert(f8 == lov + (a3+c2+c3+c4+c5+c6+c7) * ci - (b3+c4+c5+c6+c7) * lp) by(nonlinear_arith)
        requires f8 + c8 * lp == f7 + fc, fc == (c6+c7) * ci, c8 == 0,
            f7 == lov + (a3+c2+c3+c4+c5) * ci - (b3+c4+c5+c6+c7) * lp;
    //  Now: f8 = lov + A*ci - B*lp where A,B are sums.
    //  product = lov + hiv*lp. So lov = prd - hiv*lp.
    //  f8 = prd - hiv*lp + A*ci - B*lp = prd + A*ci - (hiv+B)*lp
    //     = prd + A*ci - (hiv+B)*(ci + (lp-ci))
    //     = prd + A*ci - (hiv+B)*ci - (hiv+B)*(lp-ci)
    //     = prd + (A - hiv - B)*ci - (hiv+B)*(lp-ci)
    //  Now A = a3+c2+c3+c4+c5+c6+c7 = s0+wt+wcy*BASE+c2+c3+c4+c5+c6+c7 = hiv+wt+wcy*BASE+c2+c3+c4+c5+c6+c7
    //  B = b3+c4+c5+c6+c7 = s1+c2+c3+c4+c5+c6+c7 = wt+wcy*BASE+c2+c3+c4+c5+c6+c7
    //  A - hiv - B = (hiv+wt+wcy*BASE+...) - hiv - (wt+wcy*BASE+...) = 0
    //  So f8 = prd - (hiv+B)*(lp-ci) = prd - K*p where K = hiv+B ≥ 0.
    //  Compute A = a3+c2+c3+c4+c5+c6+c7 and B = b3+c4+c5+c6+c7 explicitly
    let a_total: int = a3 + c2 + c3 + c4 + c5 + c6 + c7;
    let b_total: int = b3 + c4 + c5 + c6 + c7;
    //  A = hiv + wt + wcy*BASE + c2 + c3 + c4 + c5 + c6 + c7
    assert(a3 == hiv + wt + wcy * LIMB_BASE()) by(nonlinear_arith)
        requires a3 == a2 + wcy * LIMB_BASE(), a2 == s0 + wt, s0 == hiv;
    assert(b3 == wt + wcy * LIMB_BASE() + c2 + c3) by(nonlinear_arith)
        requires b3 == b2 + c3, b2 == s1 + c2, s1 == wt + wcy * LIMB_BASE();
    //  a_total = a3 + c2..c7 = hiv + wt + wcy*BASE + c2..c7
    //  b_total = b3 + c4..c7 = wt + wcy*BASE + c2 + c3 + c4..c7
    //  a_total - hiv == b_total (both equal wt + wcy*BASE + c2 + c3 + c4 + c5 + c6 + c7)
    assert(a_total == hiv + b_total) by(nonlinear_arith)
        requires a_total == a3 + c2 + c3 + c4 + c5 + c6 + c7,
            a3 == hiv + wt + wcy * LIMB_BASE(),
            b_total == b3 + c4 + c5 + c6 + c7,
            b3 == wt + wcy * LIMB_BASE() + c2 + c3;
    //  f8 = lov + A*ci - B*lp. prd = lov + hiv*lp.
    //  f8 + (hiv+B)*(lp-ci) = lov + A*ci - B*lp + (hiv+B)*lp - (hiv+B)*ci
    //                        = lov + (A - hiv - B)*ci + hiv*lp = lov + hiv*lp = prd  (since A = hiv+B)
    let k: int = hiv + b_total;
    assert(f8 + k * (lp - ci) == prd) by(nonlinear_arith)
        requires f8 == lov + a_total * ci - b_total * lp,
            prd == lov + hiv * lp,
            a_total == hiv + b_total,
            k == hiv + b_total;
    assert(b_total >= 0) by(nonlinear_arith)
        requires b_total == b3 + c4 + c5 + c6 + c7,
            b3 == wt + wcy * LIMB_BASE() + c2 + c3,
            wt >= 0, wcy >= 0, c2 >= 0, c3 >= 0, c4 >= 0, c5 >= 0, c6 >= 0, c7 >= 0;
    assert(k >= 0) by(nonlinear_arith) requires hiv >= 0, b_total >= 0, k == hiv + b_total;
    assert(lp > ci) by(nonlinear_arith)
        requires lp >= LIMB_BASE() * LIMB_BASE(), (ci) < LIMB_BASE(), ci > 0;
    assert(f8 >= 0);
    lemma_mod_add_left((k * (lp - ci)) as nat, f8 as nat, (lp - ci) as nat);
    assert(((k * (lp - ci)) as nat) % ((lp - ci) as nat) == 0nat) by(nonlinear_arith)
        requires lp > ci, k >= 0;
}

///  Mersenne reduction: reduce a 2n-limb product mod p = limb_power(n) - c.
///  Returns n-limb result with value ≡ vec_val(product) (mod p).
///  Extracted from mul_mod to stay under rlimit.
fn mersenne_reduce_exec(product: &Vec<u32>, n: usize, c: u32) -> (out: Vec<u32>)
    requires
        product@.len() == 2 * n,
        valid_limbs(product@),
        n >= 2, n <= 0x1FFF_FFFF,
        c > 0, (c as int) < LIMB_BASE(),
    ensures
        out@.len() == n,
        valid_limbs(out@),
        vec_val(out@) as nat % ((limb_power(n as nat) - c as int) as nat)
            == vec_val(product@) as nat % ((limb_power(n as nat) - c as int) as nat),
        (vec_val(out@) as nat) < ((limb_power(n as nat) - c as int) as nat),
{
    let c_limb: u32 = c;
    //  Split + first fold
    let lo = generic_slice_vec(product, 0, n);
    let hi = generic_slice_vec(product, n, 2 * n);
    let hi_c = generic_mul_by_limb(&hi, &c_limb, n);
    let lo_pad = generic_pad_to_length(&lo, n + 1);
    let (wide, wide_cy) = generic_add_limbs(&lo_pad, &hi_c, n + 1);
    //  Second fold: wide[n]*c + wide_cy*BASE*c
    let wide_lo = generic_slice_vec(&wide, 0, n);
    let wide_top: u32 = wide[n];
    let (wt_lo, wt_hi) = wide_top.mul2(&c_limb);
    let wt_vec = pair_to_padded_vec(wt_lo, wt_hi, n);
    let (fold2, cy2) = generic_add_limbs(&wide_lo, &wt_vec, n);
    proof {
        assert(wide_cy as int <= 1 && cy2 as int <= 1) by {
            let lpl = limb_power(n as nat);
            let lpl1 = limb_power((n + 1) as nat);
            lemma_vec_val_pad(lo@, lo_pad@);
            lemma_vec_val_bounded(lo@);
            lemma_vec_val_bounded(hi_c@);
            lemma_vec_val_bounded(wide@);
            lemma_limb_power_add(1, n as nat);
            reveal_with_fuel(limb_power, 2);
            lemma_carry_le_1(vec_val(wide@), wide_cy as int, lpl1,
                vec_val(lo_pad@), vec_val(hi_c@));
            lemma_vec_val_bounded(wide_lo@);
            lemma_vec_val_bounded(fold2@);
            lemma_carry_le_1(vec_val(fold2@), cy2 as int, lpl,
                vec_val(wide_lo@), vec_val(wt_vec@));
        };
        lemma_carry_mul_fits(wide_cy as int, c as int);
        lemma_carry_mul_fits(cy2 as int, c as int);
    }
    let wcy_c: u32 = wide_cy * c;
    let wcy_vec = pair_to_padded_vec(0u32, wcy_c, n);
    let (fold3, cy3) = generic_add_limbs(&fold2, &wcy_vec, n);
    let cy2_c: u32 = cy2 * c;
    let cy2_vec = scalar_to_padded_vec(cy2_c, n);
    let (fold4, cy4) = generic_add_limbs(&fold3, &cy2_vec, n);
    proof {
        assert(cy3 as int <= 1 && cy4 as int <= 1) by {
            let lpl = limb_power(n as nat);
            lemma_vec_val_bounded(fold2@);
            lemma_vec_val_bounded(fold3@);
            lemma_vec_val_bounded(fold4@);
            lemma_vec_val_bounded(wcy_vec@);
            lemma_vec_val_bounded(cy2_vec@);
            lemma_scalar_carry_le_1(vec_val(fold3@), cy3 as int, lpl, vec_val(fold2@), vec_val(wcy_vec@));
            lemma_scalar_carry_le_1(vec_val(fold4@), cy4 as int, lpl, vec_val(fold3@), vec_val(cy2_vec@));
        };
        lemma_carry_mul_fits(cy3 as int, c as int);
        lemma_carry_mul_fits(cy4 as int, c as int);
    }
    let cy3_c: u32 = cy3 * c;
    let cy3_vec = scalar_to_padded_vec(cy3_c, n);
    let (fold5, cy5) = generic_add_limbs(&fold4, &cy3_vec, n);
    proof {
        assert(cy5 as int <= 1) by {
            let lpl = limb_power(n as nat);
            lemma_vec_val_bounded(fold4@);
            lemma_vec_val_bounded(fold5@);
            lemma_vec_val_bounded(cy3_vec@);
            lemma_scalar_carry_le_1(vec_val(fold5@), cy5 as int, lpl, vec_val(fold4@), vec_val(cy3_vec@));
        };
        lemma_carry_mul_fits(cy5 as int, c as int);
        lemma_carry_mul_fits(cy4 as int, c as int);
    }
    let cy4_c: u32 = cy4 * c;
    let cy4_vec = scalar_to_padded_vec(cy4_c, n);
    let (fold6, _cy6) = generic_add_limbs(&fold5, &cy4_vec, n);
    let cy5_c: u32 = cy5 * c;
    let cy5_vec = scalar_to_padded_vec(cy5_c, n);
    let (fold7, cy7) = generic_add_limbs(&fold6, &cy5_vec, n);
    //  Final fold: (cy6+cy7)*c. cy6+cy7 ≤ 1 (proved from decreasing fold values).
    proof {
        assert(_cy6 as int <= 1 && cy7 as int <= 1) by {
            let lpl = limb_power(n as nat);
            lemma_vec_val_bounded(fold5@); lemma_vec_val_bounded(fold6@); lemma_vec_val_bounded(fold7@);
            lemma_vec_val_bounded(cy4_vec@); lemma_vec_val_bounded(cy5_vec@);
            lemma_scalar_carry_le_1(vec_val(fold6@), _cy6 as int, lpl, vec_val(fold5@), vec_val(cy4_vec@));
            lemma_scalar_carry_le_1(vec_val(fold7@), cy7 as int, lpl, vec_val(fold6@), vec_val(cy5_vec@));
        };
        //  cy6+cy7 ≤ 1: if cy6==1, fold6 < BASE, so fold7 = fold6+cy5_c < 2*BASE < lp, cy7=0.
        assert((_cy6 as int + cy7 as int) <= 1) by {
            let lpl = limb_power(n as nat);
            lemma_vec_val_bounded(fold5@); lemma_vec_val_bounded(fold6@); lemma_vec_val_bounded(fold7@);
            lemma_vec_val_bounded(cy4_vec@); lemma_vec_val_bounded(cy5_vec@);
            lemma_limb_power_add(1, 1);
            reveal_with_fuel(limb_power, 2);
            if _cy6 as int == 1 {
                assert(vec_val(fold6@) < LIMB_BASE()) by(nonlinear_arith)
                    requires vec_val(fold6@) + _cy6 as int * lpl == vec_val(fold5@) + vec_val(cy4_vec@),
                        vec_val(fold5@) < lpl, vec_val(cy4_vec@) < LIMB_BASE(), _cy6 as int == 1, lpl > 0;
                assert(cy7 as int == 0) by(nonlinear_arith)
                    requires vec_val(fold7@) + cy7 as int * lpl == vec_val(fold6@) + vec_val(cy5_vec@),
                        vec_val(fold6@) < LIMB_BASE(), vec_val(cy5_vec@) < LIMB_BASE(),
                        lpl >= limb_power(2nat), limb_power(2nat) == LIMB_BASE() * LIMB_BASE(),
                        lpl > 0, cy7 as int >= 0, 0 <= vec_val(fold7@);
            }
        };
        assert((_cy6 as int + cy7 as int) * (c as int) <= u32::MAX as int) by(nonlinear_arith)
            requires (_cy6 as int + cy7 as int) <= 1, (c as int) < LIMB_BASE();
    }
    let final_c: u32 = _cy6 * c + cy7 * c;
    let final_vec = scalar_to_padded_vec(final_c, n);
    let (fold8, _cy8) = generic_add_limbs(&fold7, &final_vec, n);
    //  cy8 == 0: fold7 < lp, final_c ≤ c < BASE << lp.
    //  Conditional subtract p (twice)
    let p_limbs = make_p_limbs(n, c);
    let (d1, bw1) = generic_sub_limbs(&fold8, &p_limbs, n);
    let r1 = if bw1 == 0u32 { d1 } else { fold8 };
    let (d2, bw2) = generic_sub_limbs(&r1, &p_limbs, n);
    let r = if bw2 == 0u32 { d2 } else { r1 };
    proof {
        let lp: int = limb_power(n as nat);
        let ci: int = c as int;
        let p: nat = ((lp - ci) as nat);

        //  cy8 == 0
        lemma_vec_val_bounded(fold7@);
        lemma_vec_val_bounded(fold8@);
        assert(final_c as int <= ci) by(nonlinear_arith)
            requires final_c == _cy6 * c + cy7 * c,
                (_cy6 as int + cy7 as int) <= 1,
                (ci) == c as int;
        lemma_limb_power_add(1, 1);
        reveal_with_fuel(limb_power, 2);
        assert(lp >= LIMB_BASE() * LIMB_BASE()) by {
            lemma_limb_power_add(1, 1);
            reveal_with_fuel(limb_power, 2);
        };
        assert(_cy8 as int == 0) by(nonlinear_arith)
            requires vec_val(fold8@) + _cy8 as int * lp == vec_val(fold7@) + final_c as int,
                0 <= vec_val(fold8@), vec_val(fold8@) < lp, 0 <= vec_val(fold7@), vec_val(fold7@) < lp,
                0 <= final_c as int, final_c as int <= ci, (ci) < LIMB_BASE(),
                lp >= LIMB_BASE() * LIMB_BASE(),
                lp > 0, _cy8 as int >= 0;

        //  Connect vec_vals for chain lemma call
        lemma_vec_val_split(product@, n as nat);
        assert(sem_seq(lo@) =~= sem_seq(product@.subrange(0, n as int)));
        assert(sem_seq(hi@) =~= sem_seq(product@.subrange(n as int, (2*n) as int)));
        lemma_vec_val_pad(lo@, lo_pad@);
        lemma_vec_val_split(wide@, n as nat);
        assert(sem_seq(wide_lo@) =~= sem_seq(wide@.subrange(0, n as int)));
        lemma_limb_power_add(1, n as nat);
        reveal_with_fuel(limb_power, 2);
        assert(vec_val(wt_vec@) == wide_top as int * ci) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod((wide_top as int * ci) as int, LIMB_BASE());
        };
        //  Establish wide_lo + (wt+wcy*BASE)*lp == lo+hi*c
        let wlo: int = vec_val(wide_lo@);
        let wt: int = wide_top as int;
        let wcy: int = wide_cy as int;
        assert(wlo + (wt + wcy * LIMB_BASE()) * lp == vec_val(lo@) + vec_val(hi@) * ci) by(nonlinear_arith)
            requires wlo + wt * lp + wcy * (LIMB_BASE() * lp)
                == vec_val(lo_pad@) + vec_val(hi_c@),
                vec_val(lo_pad@) == vec_val(lo@),
                vec_val(hi_c@) == vec_val(hi@) * ci,
                wlo + wt * lp == vec_val(wide@);
        //  Call chain lemma
        lemma_reduce_chain(lp, ci,
            vec_val(product@), vec_val(lo@), vec_val(hi@),
            wlo, wt, wcy,
            vec_val(fold2@), cy2 as int,
            vec_val(fold3@), cy3 as int,
            vec_val(fold4@), cy4 as int,
            vec_val(fold5@), cy5 as int,
            vec_val(fold6@), _cy6 as int,
            vec_val(fold7@), cy7 as int,
            vec_val(fold8@), _cy8 as int,
            final_c as int);
        //  Conditional subtract
        lemma_vec_val_bounded(d1@);
        lemma_cond_sub(vec_val(fold8@), vec_val(d1@), p as int, lp, ci, bw1 as int);
        if bw2 == 0u32 { lemma_vec_val_bounded(d2@); }
    }
    r
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
    ///  GPU-friendly: no u64, only u32 LimbOps.
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
        let (product, _gc) = generic_mul_karatsuba(&self.limbs, &other.limbs, n);
        let r = mersenne_reduce_exec(&product, n, c);
        proof {
            lemma_vec_val_bounded(product@);
            lemma_vec_val_bounded(self.limbs@);
            lemma_vec_val_bounded(other.limbs@);
            lemma_limb_power_add(n as nat, n as nat);
            let lp = limb_power(n as nat);
            assert(_gc@ == 0int) by(nonlinear_arith)
                requires vec_val(product@) + _gc@ * limb_power((2*n) as nat) == vec_val(self.limbs@) * vec_val(other.limbs@),
                    0 <= vec_val(product@), vec_val(product@) < limb_power((2*n) as nat),
                    0 <= vec_val(self.limbs@), vec_val(self.limbs@) < lp,
                    0 <= vec_val(other.limbs@), vec_val(other.limbs@) < lp,
                    limb_power((2*n) as nat) == lp * lp, lp > 0;
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

