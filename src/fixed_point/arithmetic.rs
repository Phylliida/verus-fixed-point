use vstd::prelude::*;
use verus_rational::Rational;
use super::FixedPoint;
use super::limbs::*;
use super::pow2::*;
use super::view_lemmas::*;

verus! {

impl FixedPoint {
    // ── Negation ───────────────────────────────────────

    /// Negate a FixedPoint. Same limbs, flipped sign (with canonical zero handling).
    pub open spec fn neg_spec(self) -> FixedPoint {
        FixedPoint {
            limbs: self.limbs,
            sign: if limbs_to_nat(self.limbs) == 0 { false } else { !self.sign },
            n: self.n,
            frac: self.frac,
        }
    }

    /// Negation preserves well-formedness.
    pub proof fn lemma_neg_wf(a: FixedPoint)
        requires a.wf_spec(),
        ensures a.neg_spec().wf_spec(),
    {
        let result = a.neg_spec();
        // limbs unchanged, n unchanged, frac unchanged
        // canonical zero: if result.sign == true, then limbs_to_nat != 0
        // (we only set sign to !a.sign when magnitude != 0)
    }

    /// Negation preserves format.
    pub proof fn lemma_neg_same_format(a: FixedPoint)
        ensures a.neg_spec().same_format(a),
    {}

    /// signed_value of negation is negated.
    pub proof fn lemma_neg_signed_value(a: FixedPoint)
        requires a.wf_spec(),
        ensures a.neg_spec().signed_value() == -a.signed_value(),
    {
        let mag = limbs_to_nat(a.limbs);
        if mag == 0 {
            // Both sides are 0
            assert(a.signed_value() == 0);
            assert(a.neg_spec().signed_value() == 0);
        } else {
            // Sign flips
            if a.sign {
                assert(a.signed_value() == -(mag as int));
                assert(a.neg_spec().sign == false);
                assert(a.neg_spec().signed_value() == mag as int);
            } else {
                assert(a.signed_value() == mag as int);
                assert(a.neg_spec().sign == true);
                assert(a.neg_spec().signed_value() == -(mag as int));
            }
        }
    }

    /// Negation view corresponds to Rational negation.
    pub proof fn lemma_neg_view(a: FixedPoint)
        requires a.wf_spec(),
        ensures a.neg_spec().view().eqv_spec(a.view().neg_spec()),
    {
        Self::lemma_neg_wf(a);
        a.lemma_view_eq_from_frac();
        a.neg_spec().lemma_view_eq_from_frac();
        Self::lemma_neg_signed_value(a);

        let d = pow2(a.frac) as int;
        lemma_pow2_positive(a.frac);
        assert(d > 0);

        // a.neg_spec().view() == from_frac_spec(-a.signed_value(), d)
        // a.view().neg_spec() == from_frac_spec(a.signed_value(), d).neg_spec()
        //                     == from_frac_spec(-a.signed_value(), d)  [by lemma_from_frac_neg]
        lemma_from_frac_neg(a.signed_value(), d);
        Rational::lemma_eqv_reflexive(a.neg_spec().view());
    }

    /// Double negation roundtrip.
    pub proof fn lemma_neg_involution(a: FixedPoint)
        requires a.wf_spec(),
        ensures a.neg_spec().neg_spec() == a,
    {
        let mag = limbs_to_nat(a.limbs);
        if mag == 0 {
            // Both neg_specs leave sign as false, limbs unchanged
        } else {
            // First neg flips sign, second flips back
        }
    }

    // ── Addition ───────────────────────────────────────

    /// No-overflow condition for addition.
    pub open spec fn add_no_overflow(a: FixedPoint, b: FixedPoint) -> bool {
        let sv = a.signed_value() + b.signed_value();
        let mag: nat = if sv >= 0 { sv as nat } else { (-sv) as nat };
        mag < pow2((a.n * 32) as nat)
    }

    /// Addition of two same-format FixedPoints.
    pub open spec fn add_spec(self, rhs: FixedPoint) -> FixedPoint {
        let sv = self.signed_value() + rhs.signed_value();
        let magnitude: nat = if sv >= 0 { sv as nat } else { (-sv) as nat };
        FixedPoint {
            limbs: nat_to_limbs(magnitude, self.n),
            sign: sv < 0,
            n: self.n,
            frac: self.frac,
        }
    }

    /// Addition preserves well-formedness (when no overflow).
    pub proof fn lemma_add_wf(a: FixedPoint, b: FixedPoint)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.same_format(b),
            Self::add_no_overflow(a, b),
        ensures
            a.add_spec(b).wf_spec(),
            a.add_spec(b).same_format(a),
    {
        let sv = a.signed_value() + b.signed_value();
        let magnitude: nat = if sv >= 0 { sv as nat } else { (-sv) as nat };
        let result = a.add_spec(b);

        // limbs.len() == n
        lemma_nat_to_limbs_len(magnitude, a.n);
        assert(result.limbs.len() == a.n);

        // n > 0 and frac <= n * 32 inherited from a
        assert(result.n == a.n);
        assert(result.frac == a.frac);

        // canonical zero: sign == true ==> magnitude != 0
        // sign == (sv < 0). If sv < 0, then magnitude = (-sv) > 0.
        // limbs_to_nat(nat_to_limbs(magnitude, n)) == magnitude [by roundtrip]
        lemma_nat_to_limbs_roundtrip(magnitude, a.n);
    }

    /// signed_value of the sum equals the sum of signed_values.
    pub proof fn lemma_add_signed_value(a: FixedPoint, b: FixedPoint)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.same_format(b),
            Self::add_no_overflow(a, b),
        ensures
            a.add_spec(b).signed_value() == a.signed_value() + b.signed_value(),
    {
        let sv = a.signed_value() + b.signed_value();
        let magnitude: nat = if sv >= 0 { sv as nat } else { (-sv) as nat };

        // limbs_to_nat(nat_to_limbs(magnitude, n)) == magnitude
        lemma_nat_to_limbs_roundtrip(magnitude, a.n);
        let result = a.add_spec(b);

        if sv >= 0 {
            assert(!result.sign);
            assert(result.signed_value() == magnitude as int);
            assert(magnitude as int == sv);
        } else {
            assert(result.sign);
            assert(result.signed_value() == -(magnitude as int));
            assert(-(magnitude as int) == sv);
        }
    }

    /// Addition view corresponds to Rational addition.
    pub proof fn lemma_add_view(a: FixedPoint, b: FixedPoint)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.same_format(b),
            Self::add_no_overflow(a, b),
        ensures
            a.add_spec(b).view().eqv_spec(a.view().add_spec(b.view())),
    {
        Self::lemma_add_wf(a, b);
        Self::lemma_add_signed_value(a, b);
        a.lemma_view_eq_from_frac();
        b.lemma_view_eq_from_frac();
        a.add_spec(b).lemma_view_eq_from_frac();

        let d = pow2(a.frac) as int;
        lemma_pow2_positive(a.frac);

        // result.view() == from_frac_spec(sv_a + sv_b, d)
        // a.view().add_spec(b.view()) == from_frac_spec(sv_a, d).add_spec(from_frac_spec(sv_b, d))
        // By lemma_from_frac_add_same_denom: eqv to from_frac_spec(sv_a + sv_b, d)
        lemma_from_frac_add_same_denom(a.signed_value(), b.signed_value(), d);
        Rational::lemma_eqv_reflexive(a.add_spec(b).view());

        // result.view() == from_frac_spec(sv_a + sv_b, d)
        // from_frac_spec(sv_a, d).add_spec(from_frac_spec(sv_b, d)) eqv from_frac_spec(sv_a + sv_b, d)
        // So result.view() eqv from_frac_spec(sv_a, d).add_spec(from_frac_spec(sv_b, d))
        // == a.view().add_spec(b.view())
        Rational::lemma_eqv_symmetric(
            Rational::from_frac_spec(a.signed_value(), d).add_spec(Rational::from_frac_spec(b.signed_value(), d)),
            Rational::from_frac_spec(a.signed_value() + b.signed_value(), d)
        );
        Rational::lemma_eqv_transitive(
            a.add_spec(b).view(),
            Rational::from_frac_spec(a.signed_value() + b.signed_value(), d),
            a.view().add_spec(b.view()),
        );
    }

    /// Addition is commutative.
    pub proof fn lemma_add_commutative(a: FixedPoint, b: FixedPoint)
        requires a.wf_spec(), b.wf_spec(), a.same_format(b),
        ensures a.add_spec(b) == b.add_spec(a),
    {
        // signed_value addition is commutative over int
        assert(a.signed_value() + b.signed_value() == b.signed_value() + a.signed_value());
    }

    // ── Subtraction ────────────────────────────────────

    /// No-overflow condition for subtraction.
    pub open spec fn sub_no_overflow(a: FixedPoint, b: FixedPoint) -> bool {
        Self::add_no_overflow(a, b.neg_spec())
    }

    /// Subtraction: a - b == a + (-b).
    pub open spec fn sub_spec(self, rhs: FixedPoint) -> FixedPoint {
        self.add_spec(rhs.neg_spec())
    }

    /// Subtraction preserves well-formedness.
    pub proof fn lemma_sub_wf(a: FixedPoint, b: FixedPoint)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.same_format(b),
            Self::sub_no_overflow(a, b),
        ensures
            a.sub_spec(b).wf_spec(),
            a.sub_spec(b).same_format(a),
    {
        Self::lemma_neg_wf(b);
        Self::lemma_neg_same_format(b);
        Self::lemma_add_wf(a, b.neg_spec());
    }

    /// signed_value of difference equals the difference of signed_values.
    pub proof fn lemma_sub_signed_value(a: FixedPoint, b: FixedPoint)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.same_format(b),
            Self::sub_no_overflow(a, b),
        ensures
            a.sub_spec(b).signed_value() == a.signed_value() - b.signed_value(),
    {
        Self::lemma_neg_wf(b);
        Self::lemma_neg_same_format(b);
        Self::lemma_neg_signed_value(b);
        Self::lemma_add_signed_value(a, b.neg_spec());
    }

    /// Subtraction view corresponds to Rational subtraction.
    pub proof fn lemma_sub_view(a: FixedPoint, b: FixedPoint)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.same_format(b),
            Self::sub_no_overflow(a, b),
        ensures
            a.sub_spec(b).view().eqv_spec(a.view().sub_spec(b.view())),
    {
        Self::lemma_neg_wf(b);
        Self::lemma_neg_same_format(b);
        Self::lemma_sub_wf(a, b);
        Self::lemma_sub_signed_value(a, b);
        a.lemma_view_eq_from_frac();
        b.lemma_view_eq_from_frac();
        a.sub_spec(b).lemma_view_eq_from_frac();

        let d = pow2(a.frac) as int;
        lemma_pow2_positive(a.frac);

        let sv_a = a.signed_value();
        let sv_b = b.signed_value();

        // result.view() == from_frac_spec(sv_a - sv_b, d)
        // a.view().sub_spec(b.view()) == from_frac_spec(sv_a, d).sub_spec(from_frac_spec(sv_b, d))
        lemma_from_frac_sub_same_denom(sv_a, sv_b, d);
        Rational::lemma_eqv_symmetric(
            Rational::from_frac_spec(sv_a, d).sub_spec(Rational::from_frac_spec(sv_b, d)),
            Rational::from_frac_spec(sv_a - sv_b, d)
        );
        Rational::lemma_eqv_transitive(
            a.sub_spec(b).view(),
            Rational::from_frac_spec(sv_a - sv_b, d),
            a.view().sub_spec(b.view()),
        );
    }

    // ── Multiplication ─────────────────────────────────

    /// Multiplication with widening: result has 2n limbs and 2*frac fractional bits.
    pub open spec fn mul_spec(self, rhs: FixedPoint) -> FixedPoint {
        let sv = self.signed_value() * rhs.signed_value();
        let magnitude: nat = if sv >= 0 { sv as nat } else { (-sv) as nat };
        FixedPoint {
            limbs: nat_to_limbs(magnitude, 2 * self.n),
            sign: sv < 0,
            n: 2 * self.n,
            frac: 2 * self.frac,
        }
    }

    /// Product magnitude always fits in 2n limbs (no overflow possible).
    pub proof fn lemma_mul_no_overflow(a: FixedPoint, b: FixedPoint)
        requires a.wf_spec(), b.wf_spec(), a.same_format(b),
        ensures
            ({
                let sv = a.signed_value() * b.signed_value();
                let mag: nat = if sv >= 0 { sv as nat } else { (-sv) as nat };
                mag < pow2((2 * a.n * 32) as nat)
            }),
    {
        let mag_a = limbs_to_nat(a.limbs);
        let mag_b = limbs_to_nat(b.limbs);
        lemma_limbs_to_nat_upper_bound(a.limbs);
        lemma_limbs_to_nat_upper_bound(b.limbs);
        // mag_a < pow2(n*32), mag_b < pow2(n*32)
        let bound = pow2((a.n * 32) as nat);
        assert(mag_a < bound);
        assert(mag_b < bound);

        // |sv_a * sv_b| == mag_a * mag_b < bound * bound
        assert(mag_a * mag_b < bound * bound) by (nonlinear_arith)
            requires mag_a < bound, mag_b < bound, bound > 0,
        {
        }
        lemma_pow2_positive((a.n * 32) as nat);

        // bound * bound == pow2(2 * n * 32)
        lemma_pow2_double((a.n * 32) as nat);
        assert(2 * (a.n * 32) == 2 * a.n * 32);

        // |signed_value product| == mag_a * mag_b
        let sv = a.signed_value() * b.signed_value();
        let product_mag: nat = if sv >= 0 { sv as nat } else { (-sv) as nat };
        // Need: product_mag == mag_a * mag_b
        // Show |sv| == mag_a * mag_b
        let sv_a = a.signed_value();
        let sv_b = b.signed_value();
        assert(sv == sv_a * sv_b);

        if a.sign == b.sign {
            if a.sign {
                assert(sv_a == -(mag_a as int));
                assert(sv_b == -(mag_b as int));
                assert(sv == (-(mag_a as int)) * (-(mag_b as int)));
                assert(sv == (mag_a as int) * (mag_b as int)) by (nonlinear_arith)
                    requires sv == (-(mag_a as int)) * (-(mag_b as int));
            } else {
                assert(sv_a == mag_a as int);
                assert(sv_b == mag_b as int);
            }
        } else {
            if a.sign {
                assert(sv_a == -(mag_a as int));
                assert(sv_b == mag_b as int);
                assert(sv == (-(mag_a as int)) * (mag_b as int));
                assert(-sv == (mag_a as int) * (mag_b as int)) by (nonlinear_arith)
                    requires sv == (-(mag_a as int)) * (mag_b as int);
            } else {
                assert(sv_a == mag_a as int);
                assert(sv_b == -(mag_b as int));
                assert(sv == (mag_a as int) * (-(mag_b as int)));
                assert(-sv == (mag_a as int) * (mag_b as int)) by (nonlinear_arith)
                    requires sv == (mag_a as int) * (-(mag_b as int));
            }
        }
    }

    /// Multiplication preserves well-formedness.
    pub proof fn lemma_mul_wf(a: FixedPoint, b: FixedPoint)
        requires a.wf_spec(), b.wf_spec(), a.same_format(b),
        ensures
            a.mul_spec(b).wf_spec(),
            a.mul_spec(b).n == 2 * a.n,
            a.mul_spec(b).frac == 2 * a.frac,
    {
        Self::lemma_mul_no_overflow(a, b);
        let sv = a.signed_value() * b.signed_value();
        let magnitude: nat = if sv >= 0 { sv as nat } else { (-sv) as nat };

        lemma_nat_to_limbs_len(magnitude, 2 * a.n);
        lemma_nat_to_limbs_roundtrip(magnitude, 2 * a.n);

        // 2 * n > 0 since n > 0
        assert(2 * a.n > 0);
        // 2 * frac <= 2 * n * 32 since frac <= n * 32
        assert(2 * a.frac <= 2 * a.n * 32);
    }

    /// signed_value of product equals product of signed_values.
    pub proof fn lemma_mul_signed_value(a: FixedPoint, b: FixedPoint)
        requires a.wf_spec(), b.wf_spec(), a.same_format(b),
        ensures a.mul_spec(b).signed_value() == a.signed_value() * b.signed_value(),
    {
        Self::lemma_mul_no_overflow(a, b);
        let sv = a.signed_value() * b.signed_value();
        let magnitude: nat = if sv >= 0 { sv as nat } else { (-sv) as nat };

        lemma_nat_to_limbs_roundtrip(magnitude, 2 * a.n);

        if sv >= 0 {
            assert(!a.mul_spec(b).sign);
        } else {
            assert(a.mul_spec(b).sign);
        }
    }

    /// Multiplication view corresponds to Rational multiplication.
    pub proof fn lemma_mul_view(a: FixedPoint, b: FixedPoint)
        requires a.wf_spec(), b.wf_spec(), a.same_format(b),
        ensures a.mul_spec(b).view().eqv_spec(a.view().mul_spec(b.view())),
    {
        Self::lemma_mul_wf(a, b);
        Self::lemma_mul_signed_value(a, b);
        a.lemma_view_eq_from_frac();
        b.lemma_view_eq_from_frac();
        a.mul_spec(b).lemma_view_eq_from_frac();

        let d_a = pow2(a.frac) as int;
        let d_b = pow2(b.frac) as int;
        let d_prod = pow2(2 * a.frac) as int;
        lemma_pow2_positive(a.frac);
        lemma_pow2_positive(b.frac);
        lemma_pow2_positive(2 * a.frac);

        let sv_a = a.signed_value();
        let sv_b = b.signed_value();

        // result.view() == from_frac_spec(sv_a * sv_b, d_prod)
        // a.view().mul_spec(b.view()) == from_frac_spec(sv_a, d_a).mul_spec(from_frac_spec(sv_b, d_b))
        // == from_frac_spec(sv_a * sv_b, d_a * d_b)  [by lemma_from_frac_mul]
        // d_a * d_b == pow2(frac) * pow2(frac) == pow2(2*frac) == d_prod
        lemma_from_frac_mul(sv_a, sv_b, d_a, d_b);
        lemma_pow2_double(a.frac);
        assert(d_a * d_b == d_prod) by (nonlinear_arith)
            requires
                d_a == pow2(a.frac) as int,
                d_b == pow2(b.frac) as int,
                d_prod == pow2(2 * a.frac) as int,
                pow2(2 * a.frac) == pow2(a.frac) * pow2(a.frac),
                a.frac == b.frac,
        {
        }

        // So a.view().mul_spec(b.view()) == from_frac_spec(sv_a * sv_b, d_prod) == result.view()
        Rational::lemma_eqv_reflexive(a.mul_spec(b).view());
    }

    /// Multiplication is commutative.
    pub proof fn lemma_mul_commutative(a: FixedPoint, b: FixedPoint)
        requires a.wf_spec(), b.wf_spec(), a.same_format(b),
        ensures a.mul_spec(b) == b.mul_spec(a),
    {
        assert(a.signed_value() * b.signed_value() == b.signed_value() * a.signed_value()) by (nonlinear_arith);
    }
}

} // verus!
