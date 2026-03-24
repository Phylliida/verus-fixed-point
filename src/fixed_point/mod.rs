use vstd::prelude::*;
use verus_rational::Rational;

pub mod pow2;
pub mod limbs;
pub mod constructors;
pub mod comparison;
pub mod view_lemmas;
pub mod arithmetic;
pub mod promotion;
pub mod reduce;
pub mod interval;
pub mod modular;
pub mod ntt;
pub mod newton_convergence;

verus! {

/// Spec-level fixed-point number.
///
/// Represents: (-1)^sign * limbs_to_nat(limbs) * 2^(-frac)
///
/// - `limbs`: Seq<u32> in little-endian order (limbs[0] is least significant)
/// - `sign`: true = negative, false = non-negative
/// - `n`: number of limbs (limbs.len() must equal n)
/// - `frac`: number of fractional bits (must satisfy frac <= n * 32)
pub struct FixedPoint {
    pub limbs: Seq<u32>,
    pub sign: bool,
    pub n: nat,
    pub frac: nat,
}

impl FixedPoint {
    /// The exact rational value this fixed-point number represents.
    pub open spec fn view(self) -> Rational {
        let magnitude = limbs::limbs_to_nat(self.limbs);
        let sign_factor: int = if self.sign { -1 } else { 1 };
        Rational::from_frac_spec(sign_factor * (magnitude as int), pow2::pow2(self.frac) as int)
    }

    /// Well-formedness predicate.
    ///
    /// 1. limbs.len() == n           (fixed width)
    /// 2. n > 0                      (at least one limb)
    /// 3. frac <= n * 32             (fractional bits fit within total bits)
    /// 4. sign ==> magnitude != 0    (canonical zero: no -0)
    pub open spec fn wf_spec(self) -> bool {
        &&& self.limbs.len() == self.n
        &&& self.n > 0
        &&& self.frac <= self.n * 32
        &&& (self.sign ==> limbs::limbs_to_nat(self.limbs) != 0)
    }

    /// Two FixedPoints have the same format (same number of limbs and fractional bits).
    pub open spec fn same_format(self, other: FixedPoint) -> bool {
        self.n == other.n && self.frac == other.frac
    }

    /// The signed integer magnitude: (-1)^sign * limbs_to_nat(limbs).
    /// This is the numerator of the rational before dividing by 2^frac.
    pub open spec fn signed_value(self) -> int {
        if self.sign { -(limbs::limbs_to_nat(self.limbs) as int) } else { limbs::limbs_to_nat(self.limbs) as int }
    }

    /// view() == from_frac_spec(signed_value(), pow2(frac)).
    pub proof fn lemma_view_eq_from_frac(self)
        requires self.wf_spec(),
        ensures self.view() == Rational::from_frac_spec(self.signed_value(), pow2::pow2(self.frac) as int),
    {
        let magnitude = limbs::limbs_to_nat(self.limbs);
        if self.sign {
            assert(self.signed_value() == -(magnitude as int));
            assert(self.view() == Rational::from_frac_spec(-1int * (magnitude as int), pow2::pow2(self.frac) as int));
        } else {
            assert(self.signed_value() == magnitude as int);
            assert(self.view() == Rational::from_frac_spec(1int * (magnitude as int), pow2::pow2(self.frac) as int));
        }
    }
}

} // verus!
