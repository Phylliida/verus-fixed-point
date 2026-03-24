use vstd::prelude::*;
use verus_rational::Rational;
use super::FixedPoint;
use super::limbs::*;
use super::pow2::*;
use super::view_lemmas::*;

verus! {

impl FixedPoint {
    /// Widen limb count, keeping frac the same. Appends zero limbs at the high end.
    /// This is the common case: making two FixedPoints the same size before add/sub.
    pub open spec fn promote_n_spec(self, new_n: nat) -> FixedPoint {
        FixedPoint {
            limbs: self.limbs.add(Seq::new((new_n - self.n) as nat, |_i: int| 0u32)),
            sign: self.sign,
            n: new_n,
            frac: self.frac,
        }
    }

    /// promote_n preserves well-formedness.
    pub proof fn lemma_promote_n_wf(a: FixedPoint, new_n: nat)
        requires
            a.wf_spec(),
            new_n >= a.n,
            a.frac <= new_n * 32,
        ensures
            a.promote_n_spec(new_n).wf_spec(),
            a.promote_n_spec(new_n).n == new_n,
            a.promote_n_spec(new_n).frac == a.frac,
    {
        let extra = (new_n - a.n) as nat;
        let result = a.promote_n_spec(new_n);

        // limbs.len() == a.n + extra == new_n
        assert(result.limbs.len() == a.n + extra);
        assert(a.n + extra == new_n);

        // new_n > 0 since a.n > 0 and new_n >= a.n
        assert(new_n > 0);

        // canonical zero: sign preserved, magnitude preserved
        lemma_limbs_to_nat_append_zeros(a.limbs, extra);
        // limbs_to_nat(result.limbs) == limbs_to_nat(a.limbs)
    }

    /// promote_n preserves the view (structural equality of the Rational).
    pub proof fn lemma_promote_n_view(a: FixedPoint, new_n: nat)
        requires
            a.wf_spec(),
            new_n >= a.n,
            a.frac <= new_n * 32,
        ensures
            a.promote_n_spec(new_n).view() == a.view(),
    {
        let extra = (new_n - a.n) as nat;
        lemma_limbs_to_nat_append_zeros(a.limbs, extra);
        // limbs_to_nat is unchanged, sign is unchanged, frac is unchanged
        // so signed_value is unchanged, and view() uses the same from_frac_spec call
    }

    /// Full promotion: widen both limb count and fractional bits.
    /// Multiplies magnitude by pow2(new_frac - frac) to maintain the same value.
    /// Requires the integer bits don't decrease: (new_n*32 - new_frac) >= (n*32 - frac).
    pub open spec fn promote_spec(self, new_n: nat, new_frac: nat) -> FixedPoint {
        let shift = (new_frac - self.frac) as nat;
        let shifted_magnitude = limbs_to_nat(self.limbs) * pow2(shift);
        FixedPoint {
            limbs: nat_to_limbs(shifted_magnitude, new_n),
            sign: self.sign,
            n: new_n,
            frac: new_frac,
        }
    }

    /// Overflow condition for full promotion: shifted magnitude fits in new_n limbs.
    pub open spec fn promote_no_overflow(a: FixedPoint, new_n: nat, new_frac: nat) -> bool {
        let shift = (new_frac - a.frac) as nat;
        limbs_to_nat(a.limbs) * pow2(shift) < pow2((new_n * 32) as nat)
    }

    /// Full promotion preserves well-formedness.
    pub proof fn lemma_promote_wf(a: FixedPoint, new_n: nat, new_frac: nat)
        requires
            a.wf_spec(),
            new_n >= a.n,
            new_frac >= a.frac,
            new_frac <= new_n * 32,
            Self::promote_no_overflow(a, new_n, new_frac),
        ensures
            a.promote_spec(new_n, new_frac).wf_spec(),
            a.promote_spec(new_n, new_frac).n == new_n,
            a.promote_spec(new_n, new_frac).frac == new_frac,
    {
        let shift = (new_frac - a.frac) as nat;
        let shifted_magnitude = limbs_to_nat(a.limbs) * pow2(shift);

        lemma_nat_to_limbs_len(shifted_magnitude, new_n);
        lemma_nat_to_limbs_roundtrip(shifted_magnitude, new_n);

        // new_n > 0 since a.n > 0 and new_n >= a.n
        assert(new_n > 0);

        // canonical zero: if sign == true, original magnitude != 0, and pow2(shift) > 0,
        // so shifted_magnitude != 0
        lemma_pow2_positive(shift);
        if a.sign {
            assert(limbs_to_nat(a.limbs) != 0);
            let m = limbs_to_nat(a.limbs);
            let p = pow2(shift);
            assert(m > 0);
            assert(p > 0);
            assert(m * p > 0) by (nonlinear_arith)
                requires m > 0nat, p > 0nat;
            assert(limbs_to_nat(nat_to_limbs(shifted_magnitude, new_n)) == shifted_magnitude);
        }
    }

    /// Full promotion preserves the view (eqv).
    pub proof fn lemma_promote_view(a: FixedPoint, new_n: nat, new_frac: nat)
        requires
            a.wf_spec(),
            new_n >= a.n,
            new_frac >= a.frac,
            new_frac <= new_n * 32,
            Self::promote_no_overflow(a, new_n, new_frac),
        ensures
            a.promote_spec(new_n, new_frac).view().eqv_spec(a.view()),
    {
        Self::lemma_promote_wf(a, new_n, new_frac);
        a.lemma_view_eq_from_frac();
        a.promote_spec(new_n, new_frac).lemma_view_eq_from_frac();

        let shift = (new_frac - a.frac) as nat;
        let mag_a = limbs_to_nat(a.limbs);
        let shifted_mag = mag_a * pow2(shift);

        lemma_nat_to_limbs_roundtrip(shifted_mag, new_n);
        lemma_pow2_positive(a.frac);
        lemma_pow2_positive(new_frac);
        lemma_pow2_positive(shift);

        // promoted.signed_value() = sign_factor * shifted_mag
        //                         = sign_factor * mag_a * pow2(shift)
        // promoted.view() = from_frac_spec(sign_factor * shifted_mag, pow2(new_frac))

        // a.view() = from_frac_spec(sign_factor * mag_a, pow2(a.frac))

        // Need: from_frac_spec(sv * pow2(shift), pow2(new_frac))
        //   eqv from_frac_spec(sv, pow2(a.frac))
        // where new_frac = a.frac + shift, so pow2(new_frac) = pow2(a.frac) * pow2(shift)

        lemma_pow2_add(a.frac, shift);
        assert(a.frac + shift == new_frac);
        let d_old = pow2(a.frac) as int;
        let d_new = pow2(new_frac) as int;
        let p = pow2(shift) as int;

        assert(d_new == d_old * p) by (nonlinear_arith)
            requires
                d_new == pow2(new_frac) as int,
                d_old == pow2(a.frac) as int,
                p == pow2(shift) as int,
                pow2(new_frac) == pow2(a.frac) * pow2(shift);

        let sv_a = a.signed_value();

        // promoted.signed_value() == sv_a * p  (if sign is same)
        let promoted = a.promote_spec(new_n, new_frac);
        if a.sign {
            assert(promoted.signed_value() == -(shifted_mag as int));
            assert(sv_a == -(mag_a as int));
            assert(promoted.signed_value() == sv_a * p) by (nonlinear_arith)
                requires
                    promoted.signed_value() == -(shifted_mag as int),
                    shifted_mag == mag_a * pow2(shift),
                    sv_a == -(mag_a as int),
                    p == pow2(shift) as int;
        } else {
            assert(promoted.signed_value() == shifted_mag as int);
            assert(sv_a == mag_a as int);
            assert(promoted.signed_value() == sv_a * p) by (nonlinear_arith)
                requires
                    promoted.signed_value() == shifted_mag as int,
                    shifted_mag == mag_a * pow2(shift),
                    sv_a == mag_a as int,
                    p == pow2(shift) as int;
        }

        // promoted.view() = from_frac_spec(sv_a * p, d_old * p)
        // a.view()         = from_frac_spec(sv_a, d_old)
        // eqv: (sv_a * p) * d_old == sv_a * (d_old * p)  -- trivially true
        let prom_view = promoted.view();
        let a_view = a.view();

        assert(prom_view == Rational::from_frac_spec(sv_a * p, d_new));
        assert(a_view == Rational::from_frac_spec(sv_a, d_old));

        // eqv_spec: prom_view.num * a_view.denom() == a_view.num * prom_view.denom()
        // (sv_a * p) * d_old == sv_a * (d_old * p) == sv_a * d_new
        assert(prom_view.num == sv_a * p);
        assert(a_view.num == sv_a);
        assert(a_view.denom() == d_old);
        assert(prom_view.denom() == d_new);

        assert(prom_view.num * a_view.denom() == a_view.num * prom_view.denom()) by (nonlinear_arith)
            requires
                prom_view.num == sv_a * p,
                a_view.num == sv_a,
                a_view.denom() == d_old,
                prom_view.denom() == d_new,
                d_new == d_old * p;
    }
}

} // verus!
