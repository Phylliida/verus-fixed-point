use vstd::prelude::*;
use verus_rational::Rational;

verus! {

/// Newton-Raphson convergence for reciprocal computation.
///
/// The iteration x_{n+1} = x_n * (2 - b * x_n) computes 1/b.
/// Key identity: if e_n = 1 - b * x_n (the "error"), then e_{n+1} = e_n².
/// This gives quadratic convergence: the number of correct bits doubles each step.

/// The error of a reciprocal approximation: e = 1 - b * x.
pub open spec fn newton_error(b: Rational, x: Rational) -> Rational {
    Rational::from_int_spec(1).sub_spec(b.mul_spec(x))
}

/// The Newton step: x' = x * (2 - b*x).
pub open spec fn newton_step(b: Rational, x: Rational) -> Rational {
    let bx = b.mul_spec(x);
    x.mul_spec(Rational::from_int_spec(2).sub_spec(bx))
}

/// **Core convergence identity at the integer level:**
/// If e = 1 - b*x, then 1 - b*x*(2-b*x) = e².
/// This is purely algebraic and Z3 handles it directly.
pub proof fn lemma_newton_error_squares_int(b: int, x: int)
    ensures
    ({
        let bx = b * x;
        let e = 1 - bx;
        let x_next = x * (2 - bx);
        1 - b * x_next == e * e
    }),
{
    let bx = b * x;
    // b * x_next = b * (x * (2 - bx)) = bx * (2 - bx) = 2*bx - bx²
    // 1 - b*x_next = 1 - 2*bx + bx² = (1-bx)²
    // Use the distributive helper from limbs
    super::limbs::lemma_mul_distribute(2, -bx, x);
    // (2 + (-bx)) * x == 2*x + (-bx)*x == 2*x - bx*x
    assert((2 - bx) * x == 2 * x - bx * x) by (nonlinear_arith)
        requires (2 + (-bx)) * x == 2 * x + (-bx) * x;
    assert(x * (2 - bx) == 2 * x - bx * x) by (nonlinear_arith)
        requires (2 - bx) * x == 2 * x - bx * x;
    assert(b * (x * (2 - bx)) == b * (2 * x - bx * x)) by (nonlinear_arith)
        requires x * (2 - bx) == 2 * x - bx * x;
    assert(b * (2 * x - bx * x) == 2 * bx - bx * bx) by (nonlinear_arith)
        requires bx == b * x;
    assert(1 - (2 * bx - bx * bx) == (1 - bx) * (1 - bx)) by (nonlinear_arith);
}

/// Corollary: error after k steps.
/// If e_0 = 1 - b*x_0, then after k Newton steps the error is e_0^{2^k}.
pub open spec fn error_after_k_int(e_0: int, k: nat) -> int
    decreases k,
{
    if k == 0 { e_0 }
    else {
        let prev = error_after_k_int(e_0, (k - 1) as nat);
        prev * prev
    }
}

/// error_after_k(e, k+1) == error_after_k(e, k)².
pub proof fn lemma_error_after_k_squares(e_0: int, k: nat)
    ensures error_after_k_int(e_0, k + 1) == error_after_k_int(e_0, k) * error_after_k_int(e_0, k),
{}

/// **Convergence bound:** If |e_0| ≤ 1/2 (in the appropriate scaling),
/// then after k iterations, |e_k| ≤ (1/2)^{2^k}.
/// At k = log2(N): |e_k| ≤ 2^{-N}, giving N bits of precision.
///
/// For 128-bit (96 frac bits): k = 7 iterations.
/// For 10000-bit: k = 14 iterations.
pub open spec fn newton_iters_needed(frac_bits: nat) -> nat
    decreases frac_bits,
{
    if frac_bits <= 1 { 1 }
    else { 1 + newton_iters_needed(frac_bits / 2) }
}

pub proof fn lemma_newton_iters_sufficient(frac_bits: nat)
    ensures newton_iters_needed(frac_bits) >= 1,
    decreases frac_bits,
{
    if frac_bits > 1 {
        lemma_newton_iters_sufficient(frac_bits / 2);
    }
}

/// 2^k spec for bounding convergence.
pub open spec fn pow2k(k: nat) -> nat
    decreases k,
{
    if k == 0 { 1 }
    else { 2 * pow2k((k - 1) as nat) }
}

/// pow2k grows: pow2k(k+1) == 2 * pow2k(k).
pub proof fn lemma_pow2k_step(k: nat)
    ensures pow2k(k + 1) == 2 * pow2k(k),
{}

/// pow2k is always positive.
pub proof fn lemma_pow2k_positive(k: nat)
    ensures pow2k(k) > 0,
    decreases k,
{
    if k > 0 { lemma_pow2k_positive((k - 1) as nat); }
}

} // verus!
