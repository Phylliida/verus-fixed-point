use vstd::prelude::*;
use verus_rational::Rational;
use super::FixedPoint;
use super::limbs::*;
use super::pow2::*;

verus! {

impl FixedPoint {
    /// Construct the zero FixedPoint with given format.
    pub proof fn zero(n: nat, frac: nat) -> (result: FixedPoint)
        requires
            n > 0,
            frac <= n * 32,
        ensures
            result.wf_spec(),
            result.n == n,
            result.frac == frac,
            result.sign == false,
            limbs_to_nat(result.limbs) == 0,
            result.view().eqv_spec(Rational::from_int_spec(0)),
    {
        let limbs = Seq::new(n as int, |_i: int| 0u32);
        let fp = FixedPoint { limbs, sign: false, n, frac };
        // wf: limbs.len() == n, n > 0, frac <= n*32, sign==false (canonical zero trivial)
        assert(limbs.len() == n);

        // limbs_to_nat(all zeros) == 0
        lemma_limbs_to_nat_all_zeros(n);

        // view == from_frac_spec(1 * 0, pow2(frac)) == from_frac_spec(0, pow2(frac))
        // from_frac_spec(0, pow2(frac)).num == 0
        // by lemma_eqv_zero_iff_num_zero: eqv to from_int_spec(0)
        lemma_pow2_positive(frac);
        assert(pow2(frac) > 0);
        let view = Rational::from_frac_spec(0int, pow2(frac) as int);
        assert(fp.view() == view);
        assert(view.num == 0);
        Rational::lemma_eqv_zero_iff_num_zero(view);

        fp
    }

    /// Construct the one FixedPoint with given format.
    /// Requires strict inequality: frac < n * 32 to ensure pow2(frac) fits in n limbs.
    pub proof fn one(n: nat, frac: nat) -> (result: FixedPoint)
        requires
            n > 0,
            frac < n * 32,
        ensures
            result.wf_spec(),
            result.n == n,
            result.frac == frac,
            result.sign == false,
            result.view().eqv_spec(Rational::from_int_spec(1)),
    {
        // We need limbs whose value == pow2(frac).
        // Place the appropriate value at limb position (frac / 32),
        // with bit (frac % 32) set.
        let k: nat = frac / 32;
        let r: nat = frac % 32;

        // pow2(r) < pow2(32) since r < 32
        lemma_pow2_strict_monotone(r, 32);
        lemma_pow2_32();
        // so pow2(r) fits in a u32
        let limb_val: u32 = pow2(r) as u32;

        // k < n since frac < n * 32
        assert(k < n) by {
            assert(frac < n * 32);
            assert(k == frac / 32);
            // frac / 32 < n when frac < n * 32
        }

        let limbs = Seq::new(n as int, |i: int| if i == k as int { limb_val } else { 0u32 });

        // Prove limbs_to_nat(limbs) == pow2(frac)
        lemma_limbs_to_nat_single_nonzero(n, k, limb_val);
        // limbs_to_nat(limbs) == limb_val * pow2(k * 32) == pow2(r) * pow2(k * 32) == pow2(r + k * 32) == pow2(frac)
        lemma_pow2_add(r, (k * 32) as nat);
        assert(r + k * 32 == frac) by {
            assert(frac == k * 32 + r);
        }

        let magnitude = pow2(frac);
        assert(limbs_to_nat(limbs) == magnitude);

        // magnitude > 0 (so wf canonical zero is satisfied even though sign==false, and also useful for view)
        lemma_pow2_positive(frac);

        let fp = FixedPoint { limbs, sign: false, n, frac };
        assert(fp.wf_spec());

        // view == from_frac_spec(pow2(frac), pow2(frac))
        // This should be eqv to from_int_spec(1) since pow2(frac) / pow2(frac) == 1
        let view = Rational::from_frac_spec(magnitude as int, pow2(frac) as int);
        assert(fp.view() == view);
        // from_frac_spec with positive den: view.num == magnitude, view.denom() == pow2(frac)
        // from_int_spec(1).num == 1, from_int_spec(1).denom() == 1
        // eqv: view.num * from_int_spec(1).denom() == from_int_spec(1).num * view.denom()
        //       pow2(frac) * 1 == 1 * pow2(frac)
        let one_rat = Rational::from_int_spec(1);
        assert(view.eqv_spec(one_rat)) by {
            // eqv is cross-multiplication: view.num * one_rat.denom() == one_rat.num * view.denom()
            assert(view.num == magnitude as int);
            assert(one_rat.num == 1);
            assert(one_rat.denom() == 1);
        }

        fp
    }
}

} // verus!
