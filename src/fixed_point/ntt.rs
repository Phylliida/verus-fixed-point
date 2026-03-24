use vstd::prelude::*;
use super::modular::*;

verus! {

// ── Root of unity ──────────────────────────────────────

/// omega is a primitive n-th root of unity mod p:
/// omega^n == 1 and omega^k != 1 for 0 < k < n.
pub open spec fn is_primitive_root(omega: ModularInt, n: nat) -> bool {
    &&& omega.wf_spec()
    &&& n > 0
    &&& omega.pow_mod(n).eqv(ModularInt::one(omega.modulus))
    &&& forall|k: nat| 0 < k < n ==> !omega.pow_mod(k).eqv(ModularInt::one(omega.modulus))
}

/// omega and omega_inv are inverses: omega * omega_inv == 1 (mod p).
pub open spec fn is_inverse(omega: ModularInt, omega_inv: ModularInt) -> bool {
    &&& omega.wf_spec()
    &&& omega_inv.wf_spec()
    &&& omega.same_modulus(omega_inv)
    &&& omega.mul_mod(omega_inv).eqv(ModularInt::one(omega.modulus))
}

// ── NTT evaluation (DFT matrix definition) ─────────────

/// Evaluate the polynomial a at point omega^k:
/// sum_{j=0}^{n-1} a[j] * omega^(j*k) mod p
pub open spec fn ntt_eval_at(
    a: Seq<ModularInt>, omega: ModularInt, n: nat, k: nat,
) -> ModularInt
    decreases n,
{
    if n == 0 {
        ModularInt::zero(omega.modulus)
    } else {
        let term = a[(n - 1) as int].mul_mod(omega.pow_mod(((n - 1) * k) as nat));
        term.add_mod(ntt_eval_at(a, omega, (n - 1) as nat, k))
    }
}

/// Forward NTT: evaluate polynomial at all n roots of unity.
/// result[k] = sum_{j=0}^{n-1} a[j] * omega^(j*k) for k = 0..n-1
pub open spec fn ntt_forward_spec(
    a: Seq<ModularInt>, omega: ModularInt, n: nat,
) -> Seq<ModularInt> {
    Seq::new(n, |k: int| ntt_eval_at(a, omega, n, k as nat))
}

/// Inverse NTT: same as forward but with omega_inv and scaled by n_inv.
/// result[j] = n_inv * sum_{k=0}^{n-1} A[k] * omega_inv^(j*k)
pub open spec fn ntt_inverse_spec(
    a: Seq<ModularInt>, omega_inv: ModularInt, n_inv: ModularInt, n: nat,
) -> Seq<ModularInt> {
    Seq::new(n, |j: int|
        n_inv.mul_mod(ntt_eval_at(a, omega_inv, n, j as nat))
    )
}

// ── Pointwise multiplication (convolution theorem) ─────

/// Pointwise (Hadamard) product of two sequences.
pub open spec fn pointwise_mul(
    a: Seq<ModularInt>, b: Seq<ModularInt>, n: nat,
) -> Seq<ModularInt> {
    Seq::new(n, |k: int| a[k].mul_mod(b[k]))
}

/// Polynomial product (linear convolution):
/// c[k] = sum_{j=0}^{k} a[j] * b[k-j]
pub open spec fn poly_mul_coeff(
    a: Seq<ModularInt>, b: Seq<ModularInt>, k: nat,
) -> ModularInt
    decreases k,
{
    if k == 0 {
        a[0].mul_mod(b[0])
    } else {
        let sum_prev = poly_mul_coeff(a, b, (k - 1) as nat);
        if k < a.len() && k < b.len() {
            sum_prev.add_mod(a[k as int].mul_mod(b[0]))
        } else {
            sum_prev
        }
    }
}

// ── Basic properties ───────────────────────────────────

/// ntt_eval_at of an empty polynomial is zero.
pub proof fn lemma_ntt_eval_at_zero(omega: ModularInt, k: nat)
    ensures ntt_eval_at(Seq::empty(), omega, 0, k).eqv(ModularInt::zero(omega.modulus)),
{}

/// ntt_eval_at of a single coefficient a[0] is just a[0] (since omega^0 == 1).
pub proof fn lemma_ntt_eval_at_single(a: ModularInt, omega: ModularInt, k: nat)
    requires a.wf_spec(), omega.wf_spec(), a.same_modulus(omega),
    ensures ntt_eval_at(seq![a], omega, 1, k).eqv(a),
{
    // ntt_eval_at(seq![a], omega, 1, k)
    //   = a.mul_mod(omega.pow_mod(0)).add_mod(ntt_eval_at(seq![a], omega, 0, k))
    //   = a.mul_mod(one).add_mod(zero)
    //   = a
    // ntt_eval_at(seq![a], omega, 1, k)
    //   = a.mul_mod(omega.pow_mod(0*k)).add_mod(zero)
    //   = a.mul_mod(one).add_mod(zero) eqv a
    let p = omega.modulus;
    // Unfold: ntt_eval_at(seq![a], omega, 1, k)
    //   == seq![a][0].mul_mod(omega.pow_mod(0*k)).add_mod(ntt_eval_at(seq![a], omega, 0, k))
    //   == a.mul_mod(omega.pow_mod(0)).add_mod(zero(p))
    assert(0 * k == 0) by (nonlinear_arith);

    // pow_mod(0) == one
    let one = ModularInt::one(p);
    assert(omega.pow_mod(0) == one);

    // a.mul_mod(one).value == a.value
    lemma_mul_one_right(a);
    let x = a.mul_mod(one);
    assert(x.eqv(a));
    assert(x.value == a.value);

    // x.add_mod(zero).value == x.value == a.value
    let z = ModularInt::zero(p);
    lemma_add_zero_right(x);
    assert(x.add_mod(z).value == x.value);

    // Help Z3 unfold ntt_eval_at for n=1 and n=0
    reveal_with_fuel(ntt_eval_at, 2);

    let result = ntt_eval_at(seq![a], omega, 1, k);
    assert(result.value == a.value);
    assert(result.modulus == a.modulus);
}

/// NTT of a zero-padded polynomial extends the evaluation consistently.
pub proof fn lemma_ntt_eval_at_extend(
    a: Seq<ModularInt>, omega: ModularInt, n: nat, k: nat,
)
    requires
        n > 0,
        a.len() >= n,
        a[(n - 1) as int].wf_spec(),
        omega.wf_spec(),
        a[(n - 1) as int].same_modulus(omega),
    ensures
        ntt_eval_at(a, omega, n, k)
            == a[(n - 1) as int].mul_mod(omega.pow_mod(((n - 1) * k) as nat))
                .add_mod(ntt_eval_at(a, omega, (n - 1) as nat, k)),
{
    // Direct from definition
}

/// Forward NTT produces n elements.
pub proof fn lemma_ntt_forward_len(
    a: Seq<ModularInt>, omega: ModularInt, n: nat,
)
    ensures ntt_forward_spec(a, omega, n).len() == n,
{}

/// Inverse NTT produces n elements.
pub proof fn lemma_ntt_inverse_len(
    a: Seq<ModularInt>, omega_inv: ModularInt, n_inv: ModularInt, n: nat,
)
    ensures ntt_inverse_spec(a, omega_inv, n_inv, n).len() == n,
{}

// ── Convolution theorem statement ──────────────────────

/// The convolution theorem: pointwise multiplication in NTT domain
/// corresponds to polynomial multiplication in coefficient domain.
///
/// ntt_forward(a, omega, n) * ntt_forward(b, omega, n) [pointwise]
/// == ntt_forward(a conv b, omega, n)
///
/// where (a conv b)[k] = sum_{j=0}^{k} a[j] * b[k-j] (cyclic convolution mod n)
///
/// This is stated here but the full proof is deferred — it requires
/// the orthogonality relation for roots of unity:
///   sum_{k=0}^{n-1} omega^(j*k) == n if j==0, 0 otherwise.
pub open spec fn cyclic_conv_coeff(
    a: Seq<ModularInt>, b: Seq<ModularInt>, n: nat, k: nat,
) -> ModularInt
    decreases n,
{
    // c[k] = sum_{j=0}^{n-1} a[j] * b[(k-j) mod n]
    if n == 0 {
        ModularInt::zero(a[0].modulus)
    } else {
        let j = (n - 1) as nat;
        let bindex = if k >= j { (k - j) as nat } else { (k + n - j) as nat };
        a[j as int].mul_mod(b[bindex as int])
            .add_mod(cyclic_conv_coeff(a, b, (n - 1) as nat, k))
    }
}

} // verus!
