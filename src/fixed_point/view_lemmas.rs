use vstd::prelude::*;
use verus_rational::Rational;

verus! {

/// Negation of from_frac_spec: structural equality.
/// from_frac_spec(a, d).neg_spec() == from_frac_spec(-a, d)
pub proof fn lemma_from_frac_neg(a: int, d: int)
    requires d > 0,
    ensures
        Rational::from_frac_spec(a, d).neg_spec() == Rational::from_frac_spec(-a, d),
{
    // from_frac_spec(a, d) with d > 0 gives Rational { num: a, den: (d-1) as nat }
    // neg_spec gives Rational { num: -a, den: (d-1) as nat }
    // from_frac_spec(-a, d) with d > 0 gives Rational { num: -a, den: (d-1) as nat }
    let r = Rational::from_frac_spec(a, d);
    assert(r.num == a);
    assert(r.neg_spec() == Rational { num: -a, den: r.den });
    assert(Rational::from_frac_spec(-a, d) == Rational { num: -a, den: (d - 1) as nat });
}

/// Multiplication of from_frac_spec: structural equality.
/// from_frac_spec(a, d1).mul_spec(from_frac_spec(b, d2)) == from_frac_spec(a*b, d1*d2)
pub proof fn lemma_from_frac_mul(a: int, b: int, d1: int, d2: int)
    requires d1 > 0, d2 > 0,
    ensures
        Rational::from_frac_spec(a, d1).mul_spec(Rational::from_frac_spec(b, d2))
            == Rational::from_frac_spec(a * b, d1 * d2),
{
    // from_frac_spec(a, d1): Rational { num: a, den: (d1-1) as nat }
    // from_frac_spec(b, d2): Rational { num: b, den: (d2-1) as nat }
    // mul_spec: Rational { num: a*b, den: (d1-1)*(d2-1) + (d1-1) + (d2-1) }
    // from_frac_spec(a*b, d1*d2): Rational { num: a*b, den: (d1*d2 - 1) as nat }
    // Need: (d1-1)*(d2-1) + (d1-1) + (d2-1) == d1*d2 - 1
    let r1 = Rational::from_frac_spec(a, d1);
    let r2 = Rational::from_frac_spec(b, d2);
    let product = r1.mul_spec(r2);
    assert(d1 * d2 > 0) by (nonlinear_arith) requires d1 > 0, d2 > 0;
    let expected = Rational::from_frac_spec(a * b, d1 * d2);
    assert(product.num == a * b);
    assert(expected.num == a * b);
    // den equality
    let d1n = (d1 - 1) as nat;
    let d2n = (d2 - 1) as nat;
    assert(product.den == d1n * d2n + d1n + d2n);
    assert(expected.den == (d1 * d2 - 1) as nat);
    assert(d1n * d2n + d1n + d2n == (d1 * d2 - 1) as nat) by (nonlinear_arith)
        requires d1 > 0, d2 > 0, d1n == (d1 - 1) as nat, d2n == (d2 - 1) as nat;
}

/// Same-denominator addition: eqv (not structural equality).
/// from_frac_spec(a, d).add_spec(from_frac_spec(b, d)).eqv_spec(from_frac_spec(a+b, d))
pub proof fn lemma_from_frac_add_same_denom(a: int, b: int, d: int)
    requires d > 0,
    ensures
        Rational::from_frac_spec(a, d).add_spec(Rational::from_frac_spec(b, d))
            .eqv_spec(Rational::from_frac_spec(a + b, d)),
{
    // LHS: add_spec gives Rational { num: a*d + b*d, den: (d-1)*(d-1) + (d-1) + (d-1) }
    //   = Rational { num: (a+b)*d, den: d²-1 }
    //   denom_nat = d²
    // RHS: from_frac_spec(a+b, d) = Rational { num: a+b, den: d-1 }
    //   denom_nat = d
    // eqv: LHS.num * RHS.denom_nat() == RHS.num * LHS.denom_nat()
    //   (a+b)*d * d == (a+b) * d*d
    let lhs = Rational::from_frac_spec(a, d).add_spec(Rational::from_frac_spec(b, d));
    let rhs = Rational::from_frac_spec(a + b, d);

    assert(lhs.num == a * d + b * d);
    assert(rhs.num == a + b);
    assert(rhs.denom_nat() == d as nat);

    // lhs.den = (d-1)*(d-1) + (d-1) + (d-1) = d²-1
    let dn = (d - 1) as nat;
    assert(lhs.den == dn * dn + dn + dn);
    assert(lhs.denom_nat() == dn * dn + dn + dn + 1);
    // d² = (d-1)² + 2(d-1) + 1 = dn*dn + 2*dn + 1
    // dn*dn + dn + dn + 1 == d*d
    // (d-1)^2 + 2(d-1) + 1 = d^2 - 2d + 1 + 2d - 2 + 1 = d^2
    assert(dn * dn + dn + dn + 1 == (d * d) as nat) by (nonlinear_arith)
        requires dn == (d - 1) as nat, d > 0;
    assert(lhs.denom_nat() == (d * d) as nat);

    // eqv_spec: lhs.num * rhs.denom() == rhs.num * lhs.denom()
    // (a*d + b*d) * d == (a+b) * d²
    assert(lhs.num * rhs.denom() == rhs.num * lhs.denom()) by (nonlinear_arith)
        requires
            lhs.num == a * d + b * d,
            rhs.num == a + b,
            rhs.denom() == d,
            lhs.denom() == (d * d) as int,
    {
    }
}

/// Same-denominator subtraction: eqv.
pub proof fn lemma_from_frac_sub_same_denom(a: int, b: int, d: int)
    requires d > 0,
    ensures
        Rational::from_frac_spec(a, d).sub_spec(Rational::from_frac_spec(b, d))
            .eqv_spec(Rational::from_frac_spec(a - b, d)),
{
    // sub_spec(x, y) = x.add_spec(y.neg_spec())
    // y.neg_spec() = from_frac_spec(-b, d)  [by lemma_from_frac_neg]
    // x.add_spec(from_frac_spec(-b, d)) eqv from_frac_spec(a + (-b), d) = from_frac_spec(a - b, d)
    lemma_from_frac_neg(b, d);
    lemma_from_frac_add_same_denom(a, -b, d);
    // from_frac_spec(a, d).add_spec(from_frac_spec(-b, d)) eqv from_frac_spec(a + (-b), d)
    // = from_frac_spec(a - b, d)
    assert(a + (-b) == a - b);
    // sub_spec == add_spec(neg_spec)
    assert(Rational::from_frac_spec(a, d).sub_spec(Rational::from_frac_spec(b, d))
        == Rational::from_frac_spec(a, d).add_spec(Rational::from_frac_spec(b, d).neg_spec()));
    assert(Rational::from_frac_spec(b, d).neg_spec() == Rational::from_frac_spec(-b, d));
}

} // verus!
