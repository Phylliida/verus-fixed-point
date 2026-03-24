use vstd::prelude::*;
use verus_rational::Rational;
use super::FixedPoint;
use super::limbs::*;
use super::pow2::*;

verus! {

impl FixedPoint {
    /// Semantic equality: views represent the same rational.
    pub open spec fn eqv_spec(self, other: FixedPoint) -> bool {
        self.view().eqv_spec(other.view())
    }

    /// Less-than-or-equal via view.
    pub open spec fn le_spec(self, other: FixedPoint) -> bool {
        self.view().le_spec(other.view())
    }

    /// Strict less-than via view.
    pub open spec fn lt_spec(self, other: FixedPoint) -> bool {
        self.view().lt_spec(other.view())
    }

    // ── Equivalence ────────────────────────────────────

    /// Equivalence is reflexive.
    pub proof fn lemma_eqv_reflexive(a: FixedPoint)
        ensures a.eqv_spec(a),
    {
        Rational::lemma_eqv_reflexive(a.view());
    }

    /// Equivalence is symmetric.
    pub proof fn lemma_eqv_symmetric(a: FixedPoint, b: FixedPoint)
        ensures a.eqv_spec(b) == b.eqv_spec(a),
    {
        Rational::lemma_eqv_symmetric(a.view(), b.view());
    }

    /// Equivalence is transitive.
    pub proof fn lemma_eqv_transitive(a: FixedPoint, b: FixedPoint, c: FixedPoint)
        requires a.eqv_spec(b), b.eqv_spec(c),
        ensures a.eqv_spec(c),
    {
        Rational::lemma_eqv_transitive(a.view(), b.view(), c.view());
    }

    // ── Ordering ───────────────────────────────────────

    /// lt is irreflexive.
    pub proof fn lemma_lt_irreflexive(a: FixedPoint)
        ensures !a.lt_spec(a),
    {
        Rational::lemma_lt_irreflexive(a.view());
    }

    /// lt is asymmetric.
    pub proof fn lemma_lt_asymmetric(a: FixedPoint, b: FixedPoint)
        requires a.lt_spec(b),
        ensures !b.lt_spec(a),
    {
        Rational::lemma_lt_asymmetric(a.view(), b.view());
    }

    /// lt is transitive.
    pub proof fn lemma_lt_transitive(a: FixedPoint, b: FixedPoint, c: FixedPoint)
        requires a.lt_spec(b), b.lt_spec(c),
        ensures a.lt_spec(c),
    {
        Rational::lemma_lt_transitive(a.view(), b.view(), c.view());
    }

    /// Trichotomy: exactly one of lt, eqv, gt holds.
    pub proof fn lemma_trichotomy(a: FixedPoint, b: FixedPoint)
        ensures
            a.lt_spec(b) || a.eqv_spec(b) || b.lt_spec(a),
            !(a.lt_spec(b) && a.eqv_spec(b)),
            !(a.lt_spec(b) && b.lt_spec(a)),
            !(a.eqv_spec(b) && b.lt_spec(a)),
    {
        Rational::lemma_trichotomy(a.view(), b.view());
    }

    /// le is equivalent to lt or eqv.
    pub proof fn lemma_le_iff_lt_or_eqv(a: FixedPoint, b: FixedPoint)
        ensures a.le_spec(b) == (a.lt_spec(b) || a.eqv_spec(b)),
    {
        Rational::lemma_le_iff_lt_or_eqv(a.view(), b.view());
    }

    /// le is antisymmetric (yields eqv).
    pub proof fn lemma_le_antisymmetric(a: FixedPoint, b: FixedPoint)
        requires a.le_spec(b), b.le_spec(a),
        ensures a.eqv_spec(b),
    {
        Rational::lemma_le_antisymmetric(a.view(), b.view());
    }

    /// le is transitive.
    pub proof fn lemma_le_transitive(a: FixedPoint, b: FixedPoint, c: FixedPoint)
        requires a.le_spec(b), b.le_spec(c),
        ensures a.le_spec(c),
    {
        Rational::lemma_le_transitive(a.view(), b.view(), c.view());
    }

    // ── Structural / zero / one properties ─────────────

    /// Structural equality implies semantic equivalence for well-formed values.
    pub proof fn lemma_structural_eq_implies_eqv(a: FixedPoint, b: FixedPoint)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.sign == b.sign,
            a.limbs =~= b.limbs,
            a.n == b.n,
            a.frac == b.frac,
        ensures
            a.eqv_spec(b),
    {
        // Same limbs => same view => eqv by reflexivity
        assert(a.view() == b.view());
        Rational::lemma_eqv_reflexive(a.view());
    }

    /// The canonical zero invariant payoff: eqv to zero implies structural zero.
    pub proof fn lemma_eqv_zero_implies_structural_zero(a: FixedPoint, z: FixedPoint)
        requires
            a.wf_spec(),
            z.wf_spec(),
            a.same_format(z),
            limbs_to_nat(z.limbs) == 0,
            z.sign == false,
            a.eqv_spec(z),
        ensures
            a.sign == false,
            limbs_to_nat(a.limbs) == 0,
    {
        // z.view() == from_frac_spec(0, pow2(frac))
        lemma_pow2_positive(z.frac);
        let z_view = z.view();
        assert(z_view == Rational::from_frac_spec(0int, pow2(z.frac) as int));
        assert(z_view.num == 0);

        // a.eqv_spec(z) means a.view().eqv_spec(z.view())
        // z.view().num == 0, so z.view() eqv from_int_spec(0)
        Rational::lemma_eqv_zero_iff_num_zero(z_view);
        // z_view eqv from_int_spec(0)

        // a.view() eqv z.view() and z.view() eqv from_int_spec(0)
        // => a.view() eqv from_int_spec(0)
        Rational::lemma_eqv_transitive(a.view(), z_view, Rational::from_int_spec(0));

        // a.view() eqv from_int_spec(0) => a.view().num == 0
        Rational::lemma_eqv_zero_iff_num_zero(a.view());
        // a.view().num == sign_factor * limbs_to_nat(a.limbs) where sign_factor is 1 or -1
        // a.view() == from_frac_spec(sign_factor * magnitude, pow2(frac))
        // from_frac_spec(x, pow2(frac)) with pow2(frac) > 0 gives .num == x
        lemma_pow2_positive(a.frac);
        let magnitude = limbs_to_nat(a.limbs) as int;
        let sign_factor: int = if a.sign { -1 } else { 1 };
        assert(a.view().num == sign_factor * magnitude);
        assert(sign_factor * magnitude == 0);
        // sign_factor is 1 or -1, so magnitude == 0
        assert(magnitude == 0);
        assert(limbs_to_nat(a.limbs) == 0);
        // wf canonical zero: sign==true ==> magnitude != 0
        // magnitude == 0 ==> sign == false (contrapositive)
    }

    /// The zero FixedPoint is le every well-formed non-negative FixedPoint.
    pub proof fn lemma_zero_le_nonneg(z: FixedPoint, a: FixedPoint)
        requires
            z.wf_spec(),
            a.wf_spec(),
            z.same_format(a),
            z.sign == false,
            limbs_to_nat(z.limbs) == 0,
            a.sign == false,
        ensures
            z.le_spec(a),
    {
        // z.view() == from_frac_spec(0, pow2(frac))
        // a.view() == from_frac_spec(magnitude, pow2(frac))
        // 0 <= magnitude, and same positive denominator, so z <= a
        lemma_pow2_positive(z.frac);
        let z_view = z.view();
        let a_view = a.view();
        // le_spec is cross-multiplication: z.num * a.denom() <= a.num * z.denom()
        // z.num == 0, so LHS == 0
        // a.num == limbs_to_nat(a.limbs) >= 0, a.denom() > 0, z.denom() > 0
        // RHS == limbs_to_nat(a.limbs) * pow2(frac) >= 0
        assert(z_view.num == 0);
    }
}

} // verus!
