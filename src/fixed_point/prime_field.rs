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
}

} // verus!
