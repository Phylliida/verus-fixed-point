use vstd::prelude::*;
use verus_rational::Rational;
use super::FixedPoint;
use super::limbs::*;
use super::pow2::*;

verus! {

// ── Ceiling division ───────────────────────────────────

/// Ceiling division of naturals: ceil(a / b).
/// When a == 0, returns 0. Otherwise (a-1)/b + 1.
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
    assert(a == (a / b) * b + a % b);
}

/// ceil_div(a, b) >= a / b.
pub proof fn lemma_ceil_div_ge(a: nat, b: nat)
    requires b > 0,
    ensures ceil_div(a, b) >= a / b,
{
    if a > 0 {
        let am1 = (a - 1) as nat;
        assert(am1 / b + 1 >= a / b) by (nonlinear_arith)
            requires a > 0nat, b > 0nat, am1 == (a - 1) as nat;
    }
}

/// ceil_div(a, b) * b >= a.
pub proof fn lemma_ceil_div_mul_ge(a: nat, b: nat)
    requires b > 0,
    ensures ceil_div(a, b) * b >= a,
{
    if a > 0 {
        let am1 = (a - 1) as nat;
        let q = am1 / b;
        // am1 == q * b + am1 % b, and am1 % b < b
        assert(am1 == q * b + am1 % b);
        assert(am1 % b < b);
        // So am1 < (q + 1) * b, i.e., a - 1 < (q+1)*b, i.e., a <= (q+1)*b
        assert(a <= (q + 1) * b) by (nonlinear_arith)
            requires am1 == q * b + am1 % b, am1 % b < b, am1 == (a - 1) as nat;
        assert(ceil_div(a, b) == q + 1);
    }
}

/// ceil_div upper bound: ceil_div(a, b) <= a / b + 1.
pub proof fn lemma_ceil_div_upper_bound(a: nat, b: nat)
    requires b > 0,
    ensures ceil_div(a, b) <= a / b + 1,
{
    if a > 0 {
        let am1 = (a - 1) as nat;
        assert(am1 / b <= a / b) by (nonlinear_arith)
            requires a > 0nat, b > 0nat, am1 == (a - 1) as nat;
    }
}

// ── Reduce operations ──────────────────────────────────

impl FixedPoint {
    /// Reduce toward -∞: for interval lo endpoints.
    /// Positive values: floor magnitude. Negative values: ceil magnitude (more negative).
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
    /// Positive values: ceil magnitude. Negative values: floor magnitude (less negative).
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
        let result = a.reduce_down_spec(target_n, target_frac);

        let shift = (a.frac - target_frac) as nat;
        let mag = limbs_to_nat(a.limbs);
        let divisor = pow2(shift);
        lemma_pow2_positive(shift);
        lemma_pow2_positive(a.frac);
        lemma_pow2_positive(target_frac);

        let new_mag: nat = if a.sign { ceil_div(mag, divisor) } else { mag / divisor };
        lemma_nat_to_limbs_roundtrip(new_mag, target_n);

        // pow2(a.frac) = pow2(target_frac) * pow2(shift)
        lemma_pow2_add(target_frac, shift);
        assert(target_frac + shift == a.frac);

        let d_target = pow2(target_frac) as int;
        let d_a = pow2(a.frac) as int;
        let div_int = divisor as int;
        assert(d_a == d_target * div_int) by (nonlinear_arith)
            requires
                d_a == pow2(a.frac) as int,
                d_target == pow2(target_frac) as int,
                div_int == pow2(shift) as int,
                pow2(a.frac) == pow2(target_frac) * pow2(shift);

        // le_spec: result.view().num * a.view().denom() <= a.view().num * result.view().denom()
        if !a.sign {
            // Positive: new_mag = mag / divisor
            // result.num = new_mag, a.num = mag
            // result.denom() = d_target, a.denom() = d_a = d_target * divisor
            // Need: new_mag * d_a <= mag * d_target
            //     = (mag / divisor) * d_target * divisor <= mag * d_target
            //     = (mag / divisor) * divisor <= mag
            lemma_floor_div_mul_le(mag, divisor);
            assert(result.view().num * a.view().denom() <= a.view().num * result.view().denom()) by (nonlinear_arith)
                requires
                    result.view().num == (mag / divisor) as int,
                    a.view().num == mag as int,
                    result.view().denom() == d_target,
                    a.view().denom() == d_a,
                    d_a == d_target * div_int,
                    (mag / divisor) * divisor <= mag,
                    d_target > 0,
            {}
        } else {
            // Negative: new_mag = ceil_div(mag, divisor)
            // a_sv = -mag, result_sv = -new_mag (or 0 if new_mag == 0)
            // Need: result.num * d_a <= a.num * d_target
            //   i.e. -(new_mag) * d_a <= -(mag) * d_target
            //   i.e. mag * d_target <= new_mag * d_a = new_mag * d_target * divisor
            //   i.e. mag <= new_mag * divisor = ceil_div(mag, divisor) * divisor
            lemma_ceil_div_mul_ge(mag, divisor);

            if new_mag == 0 {
                // ceil_div(mag, divisor) == 0, but ceil_div * divisor >= mag > 0 (wf), contradiction
                assert(mag != 0);
                assert(ceil_div(mag, divisor) * divisor > 0) by (nonlinear_arith)
                    requires ceil_div(mag, divisor) * divisor >= mag, mag > 0nat;
                assert(ceil_div(mag, divisor) > 0) by (nonlinear_arith)
                    requires ceil_div(mag, divisor) * divisor > 0nat, divisor > 0nat;
                assert(false); // unreachable
            }

            assert(result.view().num == -(new_mag as int));
            assert(a.view().num == -(mag as int));
            assert(result.view().num * a.view().denom() <= a.view().num * result.view().denom()) by (nonlinear_arith)
                requires
                    result.view().num == -(new_mag as int),
                    a.view().num == -(mag as int),
                    result.view().denom() == d_target,
                    a.view().denom() == d_a,
                    d_a == d_target * div_int,
                    new_mag * divisor >= mag,
                    d_target > 0,
                    div_int > 0,
            {}
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
        let result = a.reduce_up_spec(target_n, target_frac);

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

        let d_target = pow2(target_frac) as int;
        let d_a = pow2(a.frac) as int;
        let div_int = divisor as int;
        assert(d_a == d_target * div_int) by (nonlinear_arith)
            requires
                d_a == pow2(a.frac) as int,
                d_target == pow2(target_frac) as int,
                div_int == pow2(shift) as int,
                pow2(a.frac) == pow2(target_frac) * pow2(shift);

        // Need: a.view().num * result.view().denom() <= result.view().num * a.view().denom()
        if !a.sign {
            // Positive: new_mag = ceil_div(mag, divisor)
            // a.num = mag, result.num = new_mag (or 0 if new_mag == 0)
            // Need: mag * d_target <= new_mag * d_a = new_mag * d_target * divisor
            //     = mag <= new_mag * divisor
            lemma_ceil_div_mul_ge(mag, divisor);

            if new_mag == 0 {
                // ceil_div == 0, means mag == 0 (since ceil * divisor >= mag)
                assert(ceil_div(mag, divisor) * divisor >= mag);
                assert(mag == 0) by (nonlinear_arith)
                    requires ceil_div(mag, divisor) == 0nat, ceil_div(mag, divisor) * divisor >= mag;
            }

            assert(a.view().num * result.view().denom() <= result.view().num * a.view().denom()) by (nonlinear_arith)
                requires
                    a.view().num == mag as int,
                    result.view().num == if new_mag == 0 { 0int } else { new_mag as int },
                    result.view().denom() == d_target,
                    a.view().denom() == d_a,
                    d_a == d_target * div_int,
                    new_mag * divisor >= mag,
                    d_target > 0,
                    div_int > 0,
                    new_mag == 0nat ==> mag == 0nat,
            {}
        } else {
            // Negative: new_mag = mag / divisor
            // a.num = -mag, result.num = -new_mag (or 0 if new_mag == 0)
            // Need: (-mag) * d_target <= result.num * d_a
            // If new_mag > 0: result.num = -new_mag
            //   (-mag) * d_target <= (-new_mag) * d_a = (-new_mag) * d_target * divisor
            //   -mag <= -new_mag * divisor = -(mag / divisor) * divisor
            //   (mag / divisor) * divisor <= mag
            // If new_mag == 0: result.num = 0, a.num = -mag <= 0
            //   (-mag) * d_target <= 0 * d_a = 0, since mag > 0 (wf) and d_target > 0
            //   Wait, -mag * d_target < 0 <= 0. That works.
            lemma_floor_div_mul_le(mag, divisor);

            assert(a.view().num * result.view().denom() <= result.view().num * a.view().denom()) by (nonlinear_arith)
                requires
                    a.view().num == -(mag as int),
                    result.view().num == if new_mag == 0 { 0int } else { -(new_mag as int) },
                    result.view().denom() == d_target,
                    a.view().denom() == d_a,
                    d_a == d_target * div_int,
                    (mag / divisor) * divisor <= mag,
                    new_mag == mag / divisor,
                    d_target > 0,
                    div_int > 0,
            {}
        }
    }

    /// Helper: if val < bound * divisor, then val / divisor < bound.
    pub proof fn lemma_div_bounded(val: nat, divisor: nat, bound: nat)
        requires
            divisor > 0,
            val < bound * divisor,
        ensures
            val / divisor < bound,
    {
        assert(val / divisor < bound) by (nonlinear_arith)
            requires divisor > 0nat, val < bound * divisor;
    }
}

} // verus!
