use vstd::prelude::*;
use verus_rational::Rational;
use verus_interval_arithmetic::Interval;
use super::FixedPoint;
use super::limbs::*;
use super::pow2::*;

verus! {

/// Spec-level interval backed by fixed-point endpoints.
/// Represents a closed interval [lo, hi] where both endpoints are FixedPoints
/// with the same format (n, frac).
pub struct FixedPointInterval {
    pub lo: FixedPoint,
    pub hi: FixedPoint,
}

impl FixedPointInterval {
    /// The spec-level Interval corresponding to this FixedPointInterval.
    pub open spec fn view(self) -> Interval {
        Interval { lo: self.lo.view(), hi: self.hi.view() }
    }

    /// Well-formedness: both endpoints are wf, same format, and lo <= hi.
    pub open spec fn wf_spec(self) -> bool {
        &&& self.lo.wf_spec()
        &&& self.hi.wf_spec()
        &&& self.lo.same_format(self.hi)
        &&& self.lo.view().le_spec(self.hi.view())
    }

    /// Format accessors.
    pub open spec fn n(self) -> nat { self.lo.n }
    pub open spec fn frac(self) -> nat { self.lo.frac }

    /// Two FPIs have the same format.
    pub open spec fn same_format(self, other: FixedPointInterval) -> bool {
        self.lo.same_format(other.lo)
    }

    /// The view is a well-formed Interval when self is wf.
    pub proof fn lemma_view_wf(self)
        requires self.wf_spec(),
        ensures self.view().wf_spec(),
    {
        // Interval::wf_spec() is lo.le_spec(hi), which is our invariant.
    }

    /// Helper: if a eqv a' and b eqv b' and a' <= b', then a <= b.
    /// Used to transfer le_spec through eqv relationships.
    proof fn lemma_le_via_eqv(a: Rational, a_prime: Rational, b: Rational, b_prime: Rational)
        requires
            a.eqv_spec(a_prime),
            b.eqv_spec(b_prime),
            a_prime.le_spec(b_prime),
        ensures
            a.le_spec(b),
    {
        // a eqv a' => a <= a'
        Rational::lemma_eqv_implies_le(a, a_prime);
        // a <= a' and a' <= b' => a <= b'
        Rational::lemma_le_transitive(a, a_prime, b_prime);
        // b eqv b' => b' <= b
        Rational::lemma_eqv_implies_le(b, b_prime);
        Rational::lemma_eqv_symmetric(b, b_prime);
        Rational::lemma_eqv_implies_le(b_prime, b);
        // a <= b' and b' <= b => a <= b
        Rational::lemma_le_transitive(a, b_prime, b);
    }

    // ── Constructors ───────────────────────────────────

    /// Construct a point interval [fp, fp].
    pub proof fn from_point(fp: FixedPoint) -> (result: FixedPointInterval)
        requires fp.wf_spec(),
        ensures
            result.wf_spec(),
            result.lo == fp,
            result.hi == fp,
    {
        Rational::lemma_eqv_reflexive(fp.view());
        // le_spec from eqv: x eqv y ==> x le y
        Rational::lemma_le_iff_lt_or_eqv(fp.view(), fp.view());
        FixedPointInterval { lo: fp, hi: fp }
    }

    /// Construct from two endpoints.
    pub proof fn from_endpoints(lo: FixedPoint, hi: FixedPoint) -> (result: FixedPointInterval)
        requires
            lo.wf_spec(),
            hi.wf_spec(),
            lo.same_format(hi),
            lo.view().le_spec(hi.view()),
        ensures
            result.wf_spec(),
            result.lo == lo,
            result.hi == hi,
    {
        FixedPointInterval { lo, hi }
    }

    // ── Negation ───────────────────────────────────────

    /// Negate: -[lo, hi] = [-hi, -lo] (swap and negate).
    pub open spec fn neg_spec(self) -> FixedPointInterval {
        FixedPointInterval {
            lo: self.hi.neg_spec(),
            hi: self.lo.neg_spec(),
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

        // Need: -hi.view() <= -lo.view()
        // From lo.view() <= hi.view(), negation reverses order.
        FixedPoint::lemma_neg_view(a.lo);
        FixedPoint::lemma_neg_view(a.hi);
        // a.lo.neg_spec().view() eqv -(a.lo.view())
        // a.hi.neg_spec().view() eqv -(a.hi.view())
        // From lo <= hi: -hi <= -lo (by Rational::lemma_neg_reverses_le)
        Rational::lemma_neg_reverses_le(a.lo.view(), a.hi.view());
        // -(a.hi.view()) <= -(a.lo.view())

        // Connect through eqv: neg_spec().view() eqv neg of view
        // Need le_spec to respect eqv on both sides
        Self::lemma_le_via_eqv(
            a.hi.neg_spec().view(), a.hi.view().neg_spec(),
            a.lo.neg_spec().view(), a.lo.view().neg_spec(),
        );
    }

    // ── Addition ───────────────────────────────────────

    /// No-overflow for interval addition.
    pub open spec fn add_no_overflow(a: FixedPointInterval, b: FixedPointInterval) -> bool {
        &&& FixedPoint::add_no_overflow(a.lo, b.lo)
        &&& FixedPoint::add_no_overflow(a.hi, b.hi)
    }

    /// Add: [lo_a + lo_b, hi_a + hi_b].
    pub open spec fn add_spec(self, rhs: FixedPointInterval) -> FixedPointInterval {
        FixedPointInterval {
            lo: self.lo.add_spec(rhs.lo),
            hi: self.hi.add_spec(rhs.hi),
        }
    }

    /// Addition preserves well-formedness.
    pub proof fn lemma_add_wf(a: FixedPointInterval, b: FixedPointInterval)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.same_format(b),
            Self::add_no_overflow(a, b),
        ensures
            a.add_spec(b).wf_spec(),
    {
        FixedPoint::lemma_add_wf(a.lo, b.lo);
        FixedPoint::lemma_add_wf(a.hi, b.hi);

        // Need: add(lo_a, lo_b).view() <= add(hi_a, hi_b).view()
        // By lemma_add_view: add(x,y).view() eqv x.view() + y.view()
        FixedPoint::lemma_add_view(a.lo, b.lo);
        FixedPoint::lemma_add_view(a.hi, b.hi);

        // Interval::lemma_add_wf tells us: lo_a+lo_b <= hi_a+hi_b when lo_a<=hi_a and lo_b<=hi_b
        let iv_a = a.view();
        let iv_b = b.view();
        Interval::lemma_add_wf(iv_a, iv_b);
        // iv_a.add_spec(iv_b).wf_spec(), meaning (lo_a+lo_b).le_spec(hi_a+hi_b)
        // at the Rational level

        // Connect through eqv
        Self::lemma_le_via_eqv(
            a.lo.add_spec(b.lo).view(), iv_a.lo.add_spec(iv_b.lo),
            a.hi.add_spec(b.hi).view(), iv_a.hi.add_spec(iv_b.hi),
        );
    }

    // ── Subtraction ────────────────────────────────────

    /// No-overflow for interval subtraction.
    /// sub [lo_a, hi_a] - [lo_b, hi_b] = [lo_a - hi_b, hi_a - lo_b]
    pub open spec fn sub_no_overflow(a: FixedPointInterval, b: FixedPointInterval) -> bool {
        &&& FixedPoint::sub_no_overflow(a.lo, b.hi)
        &&& FixedPoint::sub_no_overflow(a.hi, b.lo)
    }

    /// Subtract: [lo_a - hi_b, hi_a - lo_b].
    pub open spec fn sub_spec(self, rhs: FixedPointInterval) -> FixedPointInterval {
        FixedPointInterval {
            lo: self.lo.sub_spec(rhs.hi),
            hi: self.hi.sub_spec(rhs.lo),
        }
    }

    /// Subtraction preserves well-formedness.
    pub proof fn lemma_sub_wf(a: FixedPointInterval, b: FixedPointInterval)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.same_format(b),
            Self::sub_no_overflow(a, b),
        ensures
            a.sub_spec(b).wf_spec(),
    {
        FixedPoint::lemma_sub_wf(a.lo, b.hi);
        FixedPoint::lemma_sub_wf(a.hi, b.lo);

        FixedPoint::lemma_sub_view(a.lo, b.hi);
        FixedPoint::lemma_sub_view(a.hi, b.lo);

        let iv_a = a.view();
        let iv_b = b.view();
        Interval::lemma_sub_wf(iv_a, iv_b);

        Self::lemma_le_via_eqv(
            a.lo.sub_spec(b.hi).view(), iv_a.lo.sub_spec(iv_b.hi),
            a.hi.sub_spec(b.lo).view(), iv_a.hi.sub_spec(iv_b.lo),
        );
    }

    // ── Reduce ─────────────────────────────────────────

    /// No-overflow for reduce.
    pub open spec fn reduce_no_overflow(a: FixedPointInterval, target_n: nat, target_frac: nat) -> bool {
        &&& FixedPoint::reduce_down_no_overflow(a.lo, target_n, target_frac)
        &&& FixedPoint::reduce_up_no_overflow(a.hi, target_n, target_frac)
    }

    /// Reduce: narrow precision. lo rounds toward -∞, hi rounds toward +∞.
    /// This is the ONLY operation that loses precision.
    pub open spec fn reduce_spec(self, target_n: nat, target_frac: nat) -> FixedPointInterval {
        FixedPointInterval {
            lo: self.lo.reduce_down_spec(target_n, target_frac),
            hi: self.hi.reduce_up_spec(target_n, target_frac),
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

        // Need: reduce_down(lo).view() <= reduce_up(hi).view()
        // Chain: reduce_down(lo).view() <= lo.view() <= hi.view() <= reduce_up(hi).view()
        FixedPoint::lemma_reduce_down_le(a.lo, target_n, target_frac);
        FixedPoint::lemma_reduce_up_ge(a.hi, target_n, target_frac);

        Rational::lemma_le_transitive(
            a.lo.reduce_down_spec(target_n, target_frac).view(),
            a.lo.view(),
            a.hi.view(),
        );
        Rational::lemma_le_transitive(
            a.lo.reduce_down_spec(target_n, target_frac).view(),
            a.hi.view(),
            a.hi.reduce_up_spec(target_n, target_frac).view(),
        );
    }

    /// Reduce preserves containment: if x is in the interval, x stays in the reduced interval.
    pub proof fn lemma_reduce_containment(a: FixedPointInterval, target_n: nat, target_frac: nat, x: Rational)
        requires
            a.wf_spec(),
            a.frac() >= target_frac,
            target_n > 0,
            target_frac <= target_n * 32,
            Self::reduce_no_overflow(a, target_n, target_frac),
            a.view().contains_spec(x),
        ensures
            a.reduce_spec(target_n, target_frac).view().contains_spec(x),
    {
        // x is in [lo.view(), hi.view()]
        // reduce_down(lo).view() <= lo.view() <= x  (by reduce_down_le + containment)
        // x <= hi.view() <= reduce_up(hi).view()  (by containment + reduce_up_ge)
        FixedPoint::lemma_reduce_down_le(a.lo, target_n, target_frac);
        FixedPoint::lemma_reduce_up_ge(a.hi, target_n, target_frac);

        // lo.view() <= x (from containment)
        // reduce_down(lo).view() <= lo.view() (from reduce_down_le)
        Rational::lemma_le_transitive(
            a.lo.reduce_down_spec(target_n, target_frac).view(),
            a.lo.view(),
            x,
        );

        // x <= hi.view() (from containment)
        // hi.view() <= reduce_up(hi).view() (from reduce_up_ge)
        Rational::lemma_le_transitive(
            x,
            a.hi.view(),
            a.hi.reduce_up_spec(target_n, target_frac).view(),
        );
    }

    // ── Promote ────────────────────────────────────────

    /// Promote both endpoints to wider limb count.
    pub open spec fn promote_n_spec(self, new_n: nat) -> FixedPointInterval {
        FixedPointInterval {
            lo: self.lo.promote_n_spec(new_n),
            hi: self.hi.promote_n_spec(new_n),
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

        // promote_n preserves view structurally
        FixedPoint::lemma_promote_n_view(a.lo, new_n);
        FixedPoint::lemma_promote_n_view(a.hi, new_n);
        // lo.promote_n.view() == lo.view(), hi.promote_n.view() == hi.view()
        // So the ordering is preserved.
    }

    /// Promote preserves the view (structural equality of the Interval).
    pub proof fn lemma_promote_n_view(a: FixedPointInterval, new_n: nat)
        requires
            a.wf_spec(),
            new_n >= a.n(),
            a.frac() <= new_n * 32,
        ensures
            a.promote_n_spec(new_n).view() == a.view(),
    {
        FixedPoint::lemma_promote_n_view(a.lo, new_n);
        FixedPoint::lemma_promote_n_view(a.hi, new_n);
    }

    // ── Width tracking ─────────────────────────────────

    /// The width of the interval (hi - lo) as a Rational.
    /// Tracks how much precision has been lost.
    pub open spec fn width_spec(self) -> Rational {
        self.hi.view().sub_spec(self.lo.view())
    }
}

} // verus!
