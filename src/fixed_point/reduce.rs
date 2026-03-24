use vstd::prelude::*;
use verus_rational::Rational;
use super::FixedPoint;
use super::limbs::*;
use super::pow2::*;

verus! {

// ── Ceiling division ───────────────────────────────────

/// Ceiling division of naturals: ceil(a / b).
pub open spec fn ceil_div(a: nat, b: nat) -> nat
    recommends b > 0,
{
    if a == 0 { 0nat }
    else { (a - 1) as nat / b + 1 }
}

/// Floor division: (a / b) * b <= a.
pub proof fn lemma_floor_div_mul_le(a: nat, b: nat)
    requires b > 0,
    ensures (a / b) * b <= a,
{
    assert((a / b) * b <= a) by (nonlinear_arith)
        requires b > 0nat;
}

/// Remainder is less than divisor.
pub proof fn lemma_mod_lt(a: nat, b: nat)
    requires b > 0,
    ensures a % b < b,
{
    assert(a % b < b) by (nonlinear_arith)
        requires b > 0nat;
}

/// ceil_div(a, b) * b >= a.
pub proof fn lemma_ceil_div_mul_ge(a: nat, b: nat)
    requires b > 0,
    ensures ceil_div(a, b) * b >= a,
{
    if a > 0 {
        let am1 = (a - 1) as nat;
        let q = am1 / b;
        let r = am1 % b;
        lemma_floor_div_mul_le(am1, b);
        lemma_mod_lt(am1, b);
        // q * b + r == am1 by definition of / and %
        assert(q * b + r == am1) by (nonlinear_arith)
            requires q == am1 / b, r == am1 % b, b > 0nat;
        assert((q + 1) * b >= a) by (nonlinear_arith)
            requires
                q * b <= am1,
                r < b,
                q * b + r == am1,
                am1 == (a - 1) as nat,
        {}
        assert(ceil_div(a, b) == q + 1);
    }
}

// ── Reduce operations ──────────────────────────────────

impl FixedPoint {
    /// Reduce toward -∞: for interval lo endpoints.
    pub open spec fn reduce_down_spec(self, target_n: nat, target_frac: nat) -> FixedPoint {
        let shift = (self.frac - target_frac) as nat;
        let mag = limbs_to_nat(self.limbs);
        let divisor = pow2(shift);
        let new_mag: nat = if self.sign { ceil_div(mag, divisor) } else { mag / divisor };
        FixedPoint {
            limbs: nat_to_limbs(new_mag, target_n),
            sign: if new_mag == 0 { false } else { self.sign },
            n: target_n,
            frac: target_frac,
        }
    }

    /// Reduce toward +∞: for interval hi endpoints.
    pub open spec fn reduce_up_spec(self, target_n: nat, target_frac: nat) -> FixedPoint {
        let shift = (self.frac - target_frac) as nat;
        let mag = limbs_to_nat(self.limbs);
        let divisor = pow2(shift);
        let new_mag: nat = if self.sign { mag / divisor } else { ceil_div(mag, divisor) };
        FixedPoint {
            limbs: nat_to_limbs(new_mag, target_n),
            sign: if new_mag == 0 { false } else { self.sign },
            n: target_n,
            frac: target_frac,
        }
    }

    /// No-overflow for reduce_down.
    pub open spec fn reduce_down_no_overflow(a: FixedPoint, target_n: nat, target_frac: nat) -> bool {
        let shift = (a.frac - target_frac) as nat;
        let mag = limbs_to_nat(a.limbs);
        let divisor = pow2(shift);
        let new_mag: nat = if a.sign { ceil_div(mag, divisor) } else { mag / divisor };
        new_mag < pow2((target_n * 32) as nat)
    }

    /// No-overflow for reduce_up.
    pub open spec fn reduce_up_no_overflow(a: FixedPoint, target_n: nat, target_frac: nat) -> bool {
        let shift = (a.frac - target_frac) as nat;
        let mag = limbs_to_nat(a.limbs);
        let divisor = pow2(shift);
        let new_mag: nat = if a.sign { mag / divisor } else { ceil_div(mag, divisor) };
        new_mag < pow2((target_n * 32) as nat)
    }

    /// reduce_down preserves well-formedness.
    pub proof fn lemma_reduce_down_wf(a: FixedPoint, target_n: nat, target_frac: nat)
        requires
            a.wf_spec(),
            a.frac >= target_frac,
            target_n > 0,
            target_frac <= target_n * 32,
            Self::reduce_down_no_overflow(a, target_n, target_frac),
        ensures
            a.reduce_down_spec(target_n, target_frac).wf_spec(),
            a.reduce_down_spec(target_n, target_frac).n == target_n,
            a.reduce_down_spec(target_n, target_frac).frac == target_frac,
    {
        let shift = (a.frac - target_frac) as nat;
        let mag = limbs_to_nat(a.limbs);
        let divisor = pow2(shift);
        let new_mag: nat = if a.sign { ceil_div(mag, divisor) } else { mag / divisor };
        lemma_nat_to_limbs_len(new_mag, target_n);
        lemma_nat_to_limbs_roundtrip(new_mag, target_n);
    }

    /// reduce_up preserves well-formedness.
    pub proof fn lemma_reduce_up_wf(a: FixedPoint, target_n: nat, target_frac: nat)
        requires
            a.wf_spec(),
            a.frac >= target_frac,
            target_n > 0,
            target_frac <= target_n * 32,
            Self::reduce_up_no_overflow(a, target_n, target_frac),
        ensures
            a.reduce_up_spec(target_n, target_frac).wf_spec(),
            a.reduce_up_spec(target_n, target_frac).n == target_n,
            a.reduce_up_spec(target_n, target_frac).frac == target_frac,
    {
        let shift = (a.frac - target_frac) as nat;
        let mag = limbs_to_nat(a.limbs);
        let divisor = pow2(shift);
        let new_mag: nat = if a.sign { mag / divisor } else { ceil_div(mag, divisor) };
        lemma_nat_to_limbs_len(new_mag, target_n);
        lemma_nat_to_limbs_roundtrip(new_mag, target_n);
    }

    /// Helper: prove the le_spec cross-multiplication for the positive-floor case.
    /// (mag / divisor) * d_a <= mag * d_t, where d_a == d_t * divisor.
    proof fn lemma_reduce_le_positive_case(mag: nat, divisor: nat, d_t: int, d_a: int)
        requires
            divisor > 0,
            d_t > 0,
            d_a == d_t * (divisor as int),
            (mag / divisor) * divisor <= mag,
        ensures
            (mag / divisor) as int * d_a <= (mag as int) * d_t,
    {
        // (mag/div) * d_t * div <= mag * d_t
        // because (mag/div) * div <= mag, and d_t > 0
        let q = mag / divisor;
        assert(q * divisor <= mag);
        assert((q as int) * d_a == (q as int) * d_t * (divisor as int)) by (nonlinear_arith)
            requires d_a == d_t * (divisor as int);
        assert((q as int) * d_t * (divisor as int) <= (mag as int) * d_t) by (nonlinear_arith)
            requires q * divisor <= mag, d_t > 0;
    }

    /// Helper: prove the le_spec cross-multiplication for the negative-ceil case.
    /// -(ceil_div(mag, divisor)) * d_a <= -(mag) * d_t, where d_a == d_t * divisor.
    proof fn lemma_reduce_le_negative_case(mag: nat, divisor: nat, new_mag: nat, d_t: int, d_a: int)
        requires
            divisor > 0,
            d_t > 0,
            d_a == d_t * (divisor as int),
            new_mag * divisor >= mag,
            new_mag > 0,
        ensures
            -(new_mag as int) * d_a <= -(mag as int) * d_t,
    {
        // Need: -new_mag * d_t * div <= -mag * d_t
        //     = mag * d_t <= new_mag * d_t * div
        // From new_mag * div >= mag and d_t > 0:
        assert((mag as int) * d_t <= (new_mag as int) * d_a) by (nonlinear_arith)
            requires
                new_mag * divisor >= mag,
                d_a == d_t * (divisor as int),
                d_t > 0,
                divisor > 0,
        {}
        assert(-(new_mag as int) * d_a <= -(mag as int) * d_t) by (nonlinear_arith)
            requires (mag as int) * d_t <= (new_mag as int) * d_a;
    }

    /// reduce_down rounds toward -∞: result.view() <= a.view().
    pub proof fn lemma_reduce_down_le(a: FixedPoint, target_n: nat, target_frac: nat)
        requires
            a.wf_spec(),
            a.frac >= target_frac,
            target_n > 0,
            target_frac <= target_n * 32,
            Self::reduce_down_no_overflow(a, target_n, target_frac),
        ensures
            a.reduce_down_spec(target_n, target_frac).view().le_spec(a.view()),
    {
        Self::lemma_reduce_down_wf(a, target_n, target_frac);

        let shift = (a.frac - target_frac) as nat;
        let mag = limbs_to_nat(a.limbs);
        let divisor = pow2(shift);
        lemma_pow2_positive(shift);
        lemma_pow2_positive(a.frac);
        lemma_pow2_positive(target_frac);

        let new_mag: nat = if a.sign { ceil_div(mag, divisor) } else { mag / divisor };
        lemma_nat_to_limbs_roundtrip(new_mag, target_n);

        lemma_pow2_add(target_frac, shift);
        assert(target_frac + shift == a.frac);

        let d_t = pow2(target_frac) as int;
        let d_a = pow2(a.frac) as int;
        assert(d_a == d_t * (divisor as int)) by (nonlinear_arith)
            requires
                d_a == pow2(a.frac) as int,
                d_t == pow2(target_frac) as int,
                pow2(a.frac) == pow2(target_frac) * pow2(shift),
                divisor == pow2(shift);

        let result = a.reduce_down_spec(target_n, target_frac);

        // Connect view fields to our variables
        assert(result.view().num == if new_mag == 0 { 0int } else if result.sign { -(new_mag as int) } else { new_mag as int });
        assert(result.view().denom() == d_t);
        assert(a.view().num == if a.sign { -(mag as int) } else { mag as int });
        assert(a.view().denom() == d_a);

        if !a.sign {
            lemma_floor_div_mul_le(mag, divisor);
            Self::lemma_reduce_le_positive_case(mag, divisor, d_t, d_a);
            // result.view().num == new_mag as int == (mag / divisor) as int
            // We proved: (mag / divisor) as int * d_a <= mag as int * d_t
        } else {
            lemma_ceil_div_mul_ge(mag, divisor);
            if new_mag == 0 {
                assert(mag > 0);
                assert(ceil_div(mag, divisor) * divisor >= mag);
                assert(false) by (nonlinear_arith)
                    requires
                        ceil_div(mag, divisor) == 0nat,
                        ceil_div(mag, divisor) * divisor >= mag,
                        mag > 0nat;
            }
            Self::lemma_reduce_le_negative_case(mag, divisor, new_mag, d_t, d_a);
            // We proved: -(new_mag as int) * d_a <= -(mag as int) * d_t
        }
    }

    /// reduce_up rounds toward +∞: a.view() <= result.view().
    pub proof fn lemma_reduce_up_ge(a: FixedPoint, target_n: nat, target_frac: nat)
        requires
            a.wf_spec(),
            a.frac >= target_frac,
            target_n > 0,
            target_frac <= target_n * 32,
            Self::reduce_up_no_overflow(a, target_n, target_frac),
        ensures
            a.view().le_spec(a.reduce_up_spec(target_n, target_frac).view()),
    {
        Self::lemma_reduce_up_wf(a, target_n, target_frac);

        let shift = (a.frac - target_frac) as nat;
        let mag = limbs_to_nat(a.limbs);
        let divisor = pow2(shift);
        lemma_pow2_positive(shift);
        lemma_pow2_positive(a.frac);
        lemma_pow2_positive(target_frac);

        let new_mag: nat = if a.sign { mag / divisor } else { ceil_div(mag, divisor) };
        lemma_nat_to_limbs_roundtrip(new_mag, target_n);

        lemma_pow2_add(target_frac, shift);
        assert(target_frac + shift == a.frac);

        let d_t = pow2(target_frac) as int;
        let d_a = pow2(a.frac) as int;
        assert(d_a == d_t * (divisor as int)) by (nonlinear_arith)
            requires
                d_a == pow2(a.frac) as int,
                d_t == pow2(target_frac) as int,
                pow2(a.frac) == pow2(target_frac) * pow2(shift),
                divisor == pow2(shift);

        let result = a.reduce_up_spec(target_n, target_frac);

        // Need: a_sv * d_t <= result_sv * d_a
        // This is the mirror of reduce_down: positive uses ceil, negative uses floor

        if !a.sign {
            // Positive: new_mag = ceil_div(mag, divisor)
            // Need: mag * d_t <= new_mag * d_a (= new_mag * d_t * divisor)
            //     = mag <= new_mag * divisor
            lemma_ceil_div_mul_ge(mag, divisor);
            if new_mag == 0 {
                assert(ceil_div(mag, divisor) * divisor >= mag);
                assert(mag == 0) by (nonlinear_arith)
                    requires ceil_div(mag, divisor) == 0nat, ceil_div(mag, divisor) * divisor >= mag;
                // mag == 0, a_sv == 0, trivially holds
            }
            assert((mag as int) * d_t <= (new_mag as int) * d_a) by (nonlinear_arith)
                requires
                    d_a == d_t * (divisor as int),
                    new_mag * divisor >= mag,
                    d_t > 0,
                    divisor > 0,
                    new_mag == 0nat ==> mag == 0nat,
            {}
        } else {
            // Negative: new_mag = mag / divisor
            // a_sv = -mag, result_sv = -new_mag (or 0 if new_mag == 0)
            // Need: (-mag) * d_t <= result_sv * d_a
            // If new_mag == 0: result_sv = 0, (-mag)*d_t <= 0 since mag >= 0 and d_t > 0
            //   But a.sign && wf => mag > 0, so (-mag)*d_t < 0 <= 0 ✓
            // If new_mag > 0: result_sv = -new_mag
            //   (-mag) * d_t <= (-new_mag) * d_a = (-new_mag) * d_t * divisor
            //   mag >= new_mag * divisor  ← floor property: (mag/div)*div <= mag
            lemma_floor_div_mul_le(mag, divisor);
            let a_sv = -(mag as int);
            let r_sv: int = if new_mag == 0 { 0 } else { -(new_mag as int) };
            if new_mag == 0 {
                assert(a_sv * d_t <= 0) by (nonlinear_arith)
                    requires a_sv <= 0, d_t > 0;
                assert(r_sv * d_a >= 0) by (nonlinear_arith)
                    requires r_sv == 0;
            } else {
                assert((mag as int) * d_t >= (new_mag as int) * d_a) by (nonlinear_arith)
                    requires
                        d_a == d_t * (divisor as int),
                        (mag / divisor) * divisor <= mag,
                        new_mag == mag / divisor,
                        d_t > 0,
                        divisor > 0,
                {}
                assert(a_sv * d_t <= r_sv * d_a) by (nonlinear_arith)
                    requires
                        a_sv == -(mag as int),
                        r_sv == -(new_mag as int),
                        (mag as int) * d_t >= (new_mag as int) * d_a,
                {}
            }
        }
    }
}

} // verus!
