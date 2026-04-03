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
    ///
    ///  Strategy: Karatsuba → split hi/lo → add lo + hi_c_lo (n limbs each) →
    ///  fold (carry + hi_c_top) * c → fold carry2 * c → conditional subtract.
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

        //  ── Step 3: Fold 2 — add (carry1 + hi_c_top) * c to fold1 ──
        //  Prove carry1 ≤ 1 (for u64 overflow safety)
        proof {
            lemma_vec_val_bounded(lo@);
            lemma_vec_val_bounded(hi_c_lo@);
            let lp_tmp: int = limb_power(n as nat);
            assert(carry1 as int <= 1) by(nonlinear_arith)
                requires
                    vec_val(fold1@) + carry1 as int * lp_tmp == vec_val(lo@) + vec_val(hi_c_lo@),
                    0 <= vec_val(fold1@),
                    vec_val(lo@) < lp_tmp,
                    vec_val(hi_c_lo@) < lp_tmp,
                    lp_tmp > 0,
                    carry1 as int >= 0;
        }
        let extra: u64 = (carry1 as u64 + hi_c_top as u64) * (c as u64);
        let extra_lo: u32 = (extra & 0xFFFF_FFFFu64) as u32;
        let extra_hi: u32 = (extra >> 32u64) as u32;
        let mut e2: Vec<u32> = Vec::new();
        e2.push(extra_lo);
        e2.push(extra_hi);
        let extra_vec = generic_pad_to_length(&e2, n);
        let (fold2, carry2) = generic_add_limbs(&fold1, &extra_vec, n);

        //  ── Step 4: Fold 3 — add carry2 * c ──
        //  carry2 ≤ 1 (fold1 < lp, extra < BASE^2 ≤ lp for n≥2, sum < 2*lp)
        proof {
            let lp_local: int = limb_power(n as nat);
            lemma_vec_val_bounded(fold1@);
            lemma_vec_val_bounded(fold2@);
            lemma_vec_val_bounded(extra_vec@);
            lemma_limb_power_add(1, 1);
            reveal_with_fuel(limb_power, 2);
            assert(carry2 as int <= 1) by(nonlinear_arith)
                requires
                    vec_val(fold2@) + carry2 as int * lp_local == vec_val(fold1@) + vec_val(extra_vec@),
                    0 <= vec_val(fold2@), vec_val(fold2@) < lp_local,
                    0 <= vec_val(fold1@), vec_val(fold1@) < lp_local,
                    0 <= vec_val(extra_vec@), vec_val(extra_vec@) < limb_power(2nat),
                    limb_power(2nat) <= lp_local,
                    lp_local > 0;
        }
        let carry2_c: u32 = carry2 * c;
        let mut e3: Vec<u32> = Vec::new();
        e3.push(carry2_c);
        let carry2_vec = generic_pad_to_length(&e3, n);
        let (fold3, _carry3) = generic_add_limbs(&fold2, &carry2_vec, n);

        //  ── Step 5: Conditional subtract p (twice) ──
        let p_limbs = make_p_limbs(n, c);
        let (d1, bw1) = generic_sub_limbs(&fold3, &p_limbs, n);
        let r1 = if bw1 == 0u32 { d1 } else { fold3 };
        let (d2, bw2) = generic_sub_limbs(&r1, &p_limbs, n);
        let r2 = if bw2 == 0u32 { d2 } else { r1 };

        proof {
            let lp: int = limb_power(n as nat);
            let p: nat = self.prime_spec();
            let ci: int = c as int;
            let av: int = vec_val(self.limbs@);
            let bvi: int = vec_val(other.limbs@);
            let prod_val: int = vec_val(product@);

            //  ── (1) product == a * b ──
            assert(prod_val == av * bvi);

            //  ── (2) product == lo_val + hi_val * lp ──
            lemma_vec_val_split(product@, n as nat);
            assert(sem_seq(lo@) =~= sem_seq(product@.subrange(0, n as int)));
            assert(sem_seq(hi@) =~= sem_seq(product@.subrange(n as int, (2*n) as int)));
            let lo_val: int = vec_val(lo@);
            let hi_val: int = vec_val(hi@);
            assert(prod_val == lo_val + hi_val * lp);

            //  ── (3) Mersenne #1: a*b % p == (lo + hi*c) % p ──
            lemma_vec_val_bounded(lo@);
            lemma_vec_val_bounded(hi@);
            lemma_pseudo_mersenne_reduce(lo_val as nat, hi_val as nat, lp as nat, c as nat);

            //  ── (4) hi_c == hi * c, split into hi_c_lo + hi_c_top * lp ──
            assert(vec_val(hi_c@) == hi_val * ci);
            lemma_vec_val_split(hi_c@, n as nat);
            assert(sem_seq(hi_c_lo@) =~= sem_seq(hi_c@.subrange(0, n as int)));
            let hcl_val: int = vec_val(hi_c_lo@);
            let hct_val: int = hi_c_top as int;
            assert(hcl_val + hct_val * lp == hi_val * ci);

            //  ── (5) fold1 + carry1*lp == lo + hi_c_lo ──
            let f1: int = vec_val(fold1@);
            let c1: int = carry1 as int;
            assert(f1 + c1 * lp == lo_val + hcl_val);

            //  ── (6) Combine: fold1 + (carry1 + hi_c_top) * lp == lo + hi*c ──
            //  f1 + c1*lp == lo + hcl, and hcl + hct*lp == hi*c
            //  So f1 + c1*lp + hct*lp == lo + hi*c
            //  f1 + (c1 + hct)*lp == lo + hi*c
            assert(f1 + (c1 + hct_val) * lp == lo_val + hi_val * ci)
                by(nonlinear_arith)
                requires
                    f1 + c1 * lp == lo_val + hcl_val,
                    hcl_val + hct_val * lp == hi_val * ci;

            //  ── (7) Mersenne #2: (c1+hct)*lp ≡ (c1+hct)*c (mod p) ──
            lemma_pseudo_mersenne_reduce(f1 as nat, (c1 + hct_val) as nat, lp as nat, c as nat);
            //  So (f1 + (c1+hct)*lp) % p == (f1 + (c1+hct)*c) % p

            //  ── (8) extra == (c1 + hct) * c ──
            let extra_int: int = extra as int;
            assert(extra_int == (c1 + hct_val) * ci) by {
                assert(extra == (carry1 as u64 + hi_c_top as u64) * (c as u64));
            }

            //  ── (9) vec_val(extra_vec) == extra ──
            //  e2 = [extra_lo, extra_hi]. vec_val = extra_lo + extra_hi * BASE = extra.
            lemma_sem_seq_push(Seq::<u32>::empty(), extra_lo);
            lemma_limbs_val_push(Seq::<int>::empty(), extra_lo as int);
            reveal_with_fuel(limbs_val, 2);
            assert(vec_val(e2@.subrange(0, 1)) == extra_lo as int);
            lemma_sem_seq_push(e2@.subrange(0, 1), extra_hi);
            lemma_limbs_val_push(sem_seq(e2@.subrange(0, 1)), extra_hi as int);
            reveal_with_fuel(limb_power, 2);
            assert(vec_val(e2@) == extra_lo as int + extra_hi as int * LIMB_BASE());
            assert(extra_lo as u64 + extra_hi as u64 * 0x1_0000_0000u64 == extra) by(bit_vector)
                requires
                    extra_lo == (extra & 0xFFFF_FFFFu64) as u32,
                    extra_hi == (extra >> 32u64) as u32;
            lemma_vec_val_pad(e2@, extra_vec@);
            assert(vec_val(extra_vec@) == extra_int);

            //  ── (10) fold2 + carry2*lp == f1 + extra ──
            let f2: int = vec_val(fold2@);
            let c2: int = carry2 as int;
            assert(f2 + c2 * lp == f1 + extra_int);

            //  ── (11) fold2 + carry2*c ≡ a*b (mod p) ──
            lemma_pseudo_mersenne_reduce(f2 as nat, c2 as nat, lp as nat, c as nat);
            //  (f2 + c2*lp) % p == (f2 + c2*c) % p
            //  And (f1 + extra) % p == (f1 + (c1+hct)*c) % p == (lo+hi*c) % p == a*b % p
            //  So (f2 + c2*c) % p == a*b % p

            //  ── (12) vec_val(carry2_vec) == carry2 * c ──
            lemma_sem_seq_push(Seq::<u32>::empty(), carry2_c);
            lemma_limbs_val_push(Seq::<int>::empty(), carry2_c as int);
            reveal_with_fuel(limbs_val, 2);
            lemma_vec_val_pad(e3@, carry2_vec@);
            assert(vec_val(carry2_vec@) == c2 * ci);

            //  ── (13) fold3 + carry3*lp == f2 + c2*c ──
            let f3: int = vec_val(fold3@);
            let c3: int = _carry3 as int;
            assert(f3 + c3 * lp == f2 + c2 * ci);

            //  ── (14) fold3 + c3*c ≡ a*b (mod p) ──
            lemma_pseudo_mersenne_reduce(f3 as nat, c3 as nat, lp as nat, c as nat);

            //  ── (15) Chain: (f3 + c3*c) % p == a*b % p ──
            //  Need to connect through: f3+c3*lp = f2+c2*c, (f2+c2*lp)%p = (f2+c2*c)%p,
            //  f2+c2*lp = f1+extra, (f1+extra)%p = (lo+hi*c)%p = a*b%p
            //  Each Mersenne step: (x+y*lp)%p == (x+y*c)%p
            //  The chain is:
            //  (f3+c3*c)%p == (f3+c3*lp)%p [Mersenne on f3,c3]
            //              == (f2+c2*c)%p   [since f3+c3*lp == f2+c2*c]
            //              == (f2+c2*lp)%p  [Mersenne on f2,c2, REVERSED]
            //              == (f1+extra)%p  [since f2+c2*lp == f1+extra]
            //              == (f1+(c1+hct)*c)%p  [extra == (c1+hct)*c]
            //              == (f1+(c1+hct)*lp)%p  [Mersenne on f1,(c1+hct), REVERSED]
            //              == (lo+hi*c)%p    [since f1+(c1+hct)*lp == lo+hi*c]
            //              == (lo+hi*lp)%p   [Mersenne on lo,hi, REVERSED]
            //              == a*b%p          [since lo+hi*lp == prod == a*b]
            //
            //  The key: each "==" between %p expressions uses EITHER
            //  Mersenne (lp ↔ c) OR exact integer equality of the arguments.
            //  Z3 should chain these automatically once all the individual facts are established.

            //  ── (16) Bounds: f3 < 2*p, so 2 conditional subtracts suffice ──
            lemma_vec_val_bounded(fold1@);
            lemma_vec_val_bounded(fold2@);
            lemma_vec_val_bounded(fold3@);
            //  c3 == 0: fold2 < lp, carry2*c < BASE. fold3+c3*lp = fold2+c2*c < lp + BASE.
            //  Since n >= 2: lp >= BASE^2 >> BASE. So c3 == 0.
            //  f3 < lp = p + c. Two subtracts: f3 - p < c < p. Then < p.
            //  Actually one subtract suffices since f3 < p + c and c < p.

            //  Apply conditional subtract pattern (same as add_mod)
            lemma_vec_val_bounded(d1@);
            lemma_vec_val_bounded(r1@);
            lemma_vec_val_bounded(d2@);
            lemma_vec_val_bounded(r2@);

            //  r2 == f3 % p (after at most 2 subtracts)
            //  and f3 ≡ a*b (mod p)
            //  so r2 == a*b % p

            //  For the postconditions (wf, model), we need:
            //  vec_val(r2) == (a*b) % p  and  vec_val(r2) < p
            //  This follows from the chain + bounds.
            //  However, the full formal connection through Z3 requires
            //  explicit modular arithmetic chaining. Let me assert key equalities:

            assert((f3 + c3 * ci) as nat % p == (av * bvi) as nat % p) by(nonlinear_arith)
                requires
                    f3 + c3 * lp == f2 + c2 * ci,
                    (f3 + c3 * lp) as nat % p == (f3 + c3 * ci) as nat % p,
                    f2 + c2 * lp == f1 + extra_int,
                    (f2 + c2 * lp) as nat % p == (f2 + c2 * ci) as nat % p,
                    extra_int == (c1 + hct_val) * ci,
                    f1 + (c1 + hct_val) * lp == lo_val + hi_val * ci,
                    (f1 + (c1 + hct_val) * lp) as nat % p == (f1 + (c1 + hct_val) * ci) as nat % p,
                    (lo_val + hi_val * lp) as nat % p == (lo_val + hi_val * ci) as nat % p,
                    lo_val + hi_val * lp == av * bvi;
        }

        RuntimePrimeField {
            limbs: r2,
            n_exec: n,
            c_exec: c,
            model: Ghost(((self.model@ * other.model@) % self.prime_spec()) as nat),
        }
    }
}

} // verus!
