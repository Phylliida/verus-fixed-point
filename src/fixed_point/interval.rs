use vstd::prelude::*;
use verus_rational::Rational;
use verus_interval_arithmetic::Interval;
use super::FixedPoint;
use super::limbs::*;
use super::pow2::*;

verus! {

/// Spec-level interval backed by fixed-point endpoints, with a ghost exact value.
/// The ghost `exact` tracks the true mathematical value being computed on.
/// lo and hi are fixed-point bounds: lo.view() <= exact <= hi.view().
/// Field axioms hold at the ghost level (exact is a Rational).
pub struct FixedPointInterval {
    pub lo: FixedPoint,
    pub hi: FixedPoint,
    pub exact: Rational,
}

impl FixedPointInterval {
    /// The spec-level Interval [lo, hi].
    pub open spec fn interval_view(self) -> Interval {
        Interval { lo: self.lo.view(), hi: self.hi.view() }
    }

    /// The ghost exact value (for field algebra).
    pub open spec fn exact_view(self) -> Rational {
        self.exact
    }

    /// Well-formedness: both endpoints wf, same format, lo <= exact <= hi.
    pub open spec fn wf_spec(self) -> bool {
        &&& self.lo.wf_spec()
        &&& self.hi.wf_spec()
        &&& self.lo.same_format(self.hi)
        &&& self.lo.view().le_spec(self.exact)
        &&& self.exact.le_spec(self.hi.view())
    }

    /// Format accessors.
    pub open spec fn n(self) -> nat { self.lo.n }
    pub open spec fn frac(self) -> nat { self.lo.frac }

    /// Two FPIs have the same format.
    pub open spec fn same_format(self, other: FixedPointInterval) -> bool {
        self.lo.same_format(other.lo)
    }

    /// The interval view is well-formed when self is wf.
    pub proof fn lemma_interval_view_wf(self)
        requires self.wf_spec(),
        ensures self.interval_view().wf_spec(),
    {
        Rational::lemma_le_transitive(self.lo.view(), self.exact, self.hi.view());
    }

    /// The exact value is contained in the interval.
    pub proof fn lemma_exact_in_interval(self)
        requires self.wf_spec(),
        ensures self.interval_view().contains_spec(self.exact),
    {}

    /// Helper: if a eqv a' and b eqv b' and a' <= b', then a <= b.
    proof fn lemma_le_via_eqv(a: Rational, a_prime: Rational, b: Rational, b_prime: Rational)
        requires a.eqv_spec(a_prime), b.eqv_spec(b_prime), a_prime.le_spec(b_prime),
        ensures a.le_spec(b),
    {
        Rational::lemma_eqv_implies_le(a, a_prime);
        Rational::lemma_le_transitive(a, a_prime, b_prime);
        Rational::lemma_eqv_symmetric(b, b_prime);
        Rational::lemma_eqv_implies_le(b_prime, b);
        Rational::lemma_le_transitive(a, b_prime, b);
    }

    // ── Constructors ───────────────────────────────────

    /// Construct a point interval [fp, fp] with exact == fp.view().
    pub proof fn from_point(fp: FixedPoint) -> (result: FixedPointInterval)
        requires fp.wf_spec(),
        ensures
            result.wf_spec(),
            result.lo == fp,
            result.hi == fp,
            result.exact == fp.view(),
    {
        Rational::lemma_eqv_reflexive(fp.view());
        Rational::lemma_le_iff_lt_or_eqv(fp.view(), fp.view());
        FixedPointInterval { lo: fp, hi: fp, exact: fp.view() }
    }

    /// Construct from two endpoints with a given exact value.
    pub proof fn from_endpoints(lo: FixedPoint, hi: FixedPoint, exact: Rational) -> (result: FixedPointInterval)
        requires
            lo.wf_spec(),
            hi.wf_spec(),
            lo.same_format(hi),
            lo.view().le_spec(exact),
            exact.le_spec(hi.view()),
        ensures
            result.wf_spec(),
            result.lo == lo,
            result.hi == hi,
            result.exact == exact,
    {
        FixedPointInterval { lo, hi, exact }
    }

    // ── Negation ───────────────────────────────────────

    /// Negate: -[lo, hi] = [-hi, -lo], exact = -exact.
    pub open spec fn neg_spec(self) -> FixedPointInterval {
        FixedPointInterval {
            lo: self.hi.neg_spec(),
            hi: self.lo.neg_spec(),
            exact: self.exact.neg_spec(),
        }
    }

    /// Negation preserves well-formedness.
    pub proof fn lemma_neg_wf(a: FixedPointInterval)
        requires a.wf_spec(),
        ensures a.neg_spec().wf_spec(),
    {
        FixedPoint::lemma_neg_wf(a.lo);
        FixedPoint::lemma_neg_wf(a.hi);
        FixedPoint::lemma_neg_same_format(a.lo);
        FixedPoint::lemma_neg_same_format(a.hi);
        FixedPoint::lemma_neg_view(a.lo);
        FixedPoint::lemma_neg_view(a.hi);

        // Need: -hi.view() <= -exact <= -lo.view()
        // From exact <= hi.view(): -hi.view() <= -exact
        Rational::lemma_neg_reverses_le(a.exact, a.hi.view());
        // From lo.view() <= exact: -exact <= -lo.view()
        Rational::lemma_neg_reverses_le(a.lo.view(), a.exact);

        // Connect through eqv for the FixedPoint neg
        Self::lemma_le_via_eqv(
            a.hi.neg_spec().view(), a.hi.view().neg_spec(),
            a.neg_spec().exact, a.neg_spec().exact,
        );
        Rational::lemma_eqv_reflexive(a.neg_spec().exact);
        Self::lemma_le_via_eqv(
            a.neg_spec().exact, a.neg_spec().exact,
            a.lo.neg_spec().view(), a.lo.view().neg_spec(),
        );
    }

    // ── Addition ───────────────────────────────────────

    /// No-overflow for interval addition.
    pub open spec fn add_no_overflow(a: FixedPointInterval, b: FixedPointInterval) -> bool {
        &&& FixedPoint::add_no_overflow(a.lo, b.lo)
        &&& FixedPoint::add_no_overflow(a.hi, b.hi)
    }

    /// Add: [lo_a + lo_b, hi_a + hi_b], exact = exact_a + exact_b.
    pub open spec fn add_spec(self, rhs: FixedPointInterval) -> FixedPointInterval {
        FixedPointInterval {
            lo: self.lo.add_spec(rhs.lo),
            hi: self.hi.add_spec(rhs.hi),
            exact: self.exact.add_spec(rhs.exact),
        }
    }

    /// Addition preserves well-formedness.
    pub proof fn lemma_add_wf(a: FixedPointInterval, b: FixedPointInterval)
        requires
            a.wf_spec(), b.wf_spec(),
            a.same_format(b),
            Self::add_no_overflow(a, b),
        ensures a.add_spec(b).wf_spec(),
    {
        FixedPoint::lemma_add_wf(a.lo, b.lo);
        FixedPoint::lemma_add_wf(a.hi, b.hi);
        FixedPoint::lemma_add_view(a.lo, b.lo);
        FixedPoint::lemma_add_view(a.hi, b.hi);

        // Need: add(lo_a, lo_b).view() <= exact_a + exact_b <= add(hi_a, hi_b).view()
        // lo_a.view() <= exact_a and lo_b.view() <= exact_b
        // => lo_a.view() + lo_b.view() <= exact_a + exact_b (by add monotone)
        Rational::lemma_le_add_both(a.lo.view(), a.exact, b.lo.view(), b.exact);
        Rational::lemma_le_add_both(a.exact, a.hi.view(), b.exact, b.hi.view());

        // Connect FP add view (eqv) to Rational add
        Self::lemma_le_via_eqv(
            a.lo.add_spec(b.lo).view(), a.lo.view().add_spec(b.lo.view()),
            a.add_spec(b).exact, a.add_spec(b).exact,
        );
        Rational::lemma_eqv_reflexive(a.add_spec(b).exact);
        Self::lemma_le_via_eqv(
            a.add_spec(b).exact, a.add_spec(b).exact,
            a.hi.add_spec(b.hi).view(), a.hi.view().add_spec(b.hi.view()),
        );
    }

    // ── Subtraction ────────────────────────────────────

    /// No-overflow for interval subtraction.
    pub open spec fn sub_no_overflow(a: FixedPointInterval, b: FixedPointInterval) -> bool {
        &&& FixedPoint::sub_no_overflow(a.lo, b.hi)
        &&& FixedPoint::sub_no_overflow(a.hi, b.lo)
    }

    /// Subtract: [lo_a - hi_b, hi_a - lo_b], exact = exact_a - exact_b.
    pub open spec fn sub_spec(self, rhs: FixedPointInterval) -> FixedPointInterval {
        FixedPointInterval {
            lo: self.lo.sub_spec(rhs.hi),
            hi: self.hi.sub_spec(rhs.lo),
            exact: self.exact.sub_spec(rhs.exact),
        }
    }

    /// Subtraction preserves well-formedness.
    pub proof fn lemma_sub_wf(a: FixedPointInterval, b: FixedPointInterval)
        requires
            a.wf_spec(), b.wf_spec(),
            a.same_format(b),
            Self::sub_no_overflow(a, b),
        ensures a.sub_spec(b).wf_spec(),
    {
        FixedPoint::lemma_sub_wf(a.lo, b.hi);
        FixedPoint::lemma_sub_wf(a.hi, b.lo);
        FixedPoint::lemma_sub_view(a.lo, b.hi);
        FixedPoint::lemma_sub_view(a.hi, b.lo);

        // lo_a - hi_b <= exact_a - exact_b <= hi_a - lo_b
        // Left: lo_a <= exact_a ==> lo_a - hi_b <= exact_a - hi_b (monotone left)
        //        exact_b <= hi_b ==> exact_a - hi_b <= exact_a - exact_b (monotone right, reversed)
        Rational::lemma_sub_le_monotone_left(a.lo.view(), a.exact, b.hi.view());
        // lo_a - hi_b <= exact_a - hi_b
        Rational::lemma_sub_le_monotone_right(b.exact, b.hi.view(), a.exact);
        // exact_b <= hi_b ==> exact_a - hi_b <= exact_a - exact_b
        Rational::lemma_le_transitive(
            a.lo.view().sub_spec(b.hi.view()),
            a.exact.sub_spec(b.hi.view()),
            a.exact.sub_spec(b.exact),
        );
        // Right: exact_a <= hi_a ==> exact_a - lo_b <= hi_a - lo_b (monotone left)
        //        lo_b <= exact_b ==> exact_a - exact_b <= exact_a - lo_b (monotone right, reversed)
        Rational::lemma_sub_le_monotone_right(b.lo.view(), b.exact, a.exact);
        // lo_b <= exact_b ==> exact_a - exact_b <= exact_a - lo_b
        Rational::lemma_sub_le_monotone_left(a.exact, a.hi.view(), b.lo.view());
        // exact_a <= hi_a ==> exact_a - lo_b <= hi_a - lo_b
        Rational::lemma_le_transitive(
            a.exact.sub_spec(b.exact),
            a.exact.sub_spec(b.lo.view()),
            a.hi.view().sub_spec(b.lo.view()),
        );

        // Connect FP sub view (eqv) to Rational sub
        Self::lemma_le_via_eqv(
            a.lo.sub_spec(b.hi).view(), a.lo.view().sub_spec(b.hi.view()),
            a.sub_spec(b).exact, a.sub_spec(b).exact,
        );
        Rational::lemma_eqv_reflexive(a.sub_spec(b).exact);
        Self::lemma_le_via_eqv(
            a.sub_spec(b).exact, a.sub_spec(b).exact,
            a.hi.sub_spec(b.lo).view(), a.hi.view().sub_spec(b.lo.view()),
        );
    }

    // ── Reduce ─────────────────────────────────────────

    /// No-overflow for reduce.
    pub open spec fn reduce_no_overflow(a: FixedPointInterval, target_n: nat, target_frac: nat) -> bool {
        &&& FixedPoint::reduce_down_no_overflow(a.lo, target_n, target_frac)
        &&& FixedPoint::reduce_up_no_overflow(a.hi, target_n, target_frac)
    }

    /// Reduce: narrow precision. exact stays the same (still contained).
    pub open spec fn reduce_spec(self, target_n: nat, target_frac: nat) -> FixedPointInterval {
        FixedPointInterval {
            lo: self.lo.reduce_down_spec(target_n, target_frac),
            hi: self.hi.reduce_up_spec(target_n, target_frac),
            exact: self.exact,
        }
    }

    /// Reduce preserves well-formedness.
    pub proof fn lemma_reduce_wf(a: FixedPointInterval, target_n: nat, target_frac: nat)
        requires
            a.wf_spec(),
            a.frac() >= target_frac,
            target_n > 0,
            target_frac <= target_n * 32,
            Self::reduce_no_overflow(a, target_n, target_frac),
        ensures
            a.reduce_spec(target_n, target_frac).wf_spec(),
    {
        FixedPoint::lemma_reduce_down_wf(a.lo, target_n, target_frac);
        FixedPoint::lemma_reduce_up_wf(a.hi, target_n, target_frac);

        // reduce_down(lo) <= lo <= exact <= hi <= reduce_up(hi)
        FixedPoint::lemma_reduce_down_le(a.lo, target_n, target_frac);
        FixedPoint::lemma_reduce_up_ge(a.hi, target_n, target_frac);

        Rational::lemma_le_transitive(
            a.lo.reduce_down_spec(target_n, target_frac).view(),
            a.lo.view(),
            a.exact,
        );
        Rational::lemma_le_transitive(
            a.exact,
            a.hi.view(),
            a.hi.reduce_up_spec(target_n, target_frac).view(),
        );
    }

    // ── Promote ────────────────────────────────────────

    /// Promote both endpoints. exact stays the same.
    pub open spec fn promote_n_spec(self, new_n: nat) -> FixedPointInterval {
        FixedPointInterval {
            lo: self.lo.promote_n_spec(new_n),
            hi: self.hi.promote_n_spec(new_n),
            exact: self.exact,
        }
    }

    /// Promote preserves well-formedness.
    pub proof fn lemma_promote_n_wf(a: FixedPointInterval, new_n: nat)
        requires
            a.wf_spec(),
            new_n >= a.n(),
            a.frac() <= new_n * 32,
        ensures
            a.promote_n_spec(new_n).wf_spec(),
    {
        FixedPoint::lemma_promote_n_wf(a.lo, new_n);
        FixedPoint::lemma_promote_n_wf(a.hi, new_n);
        FixedPoint::lemma_promote_n_view(a.lo, new_n);
        FixedPoint::lemma_promote_n_view(a.hi, new_n);
    }

    // ── Width tracking ─────────────────────────────────

    /// The width of the interval (hi - lo).
    pub open spec fn width_spec(self) -> Rational {
        self.hi.view().sub_spec(self.lo.view())
    }
}

} // verus!
