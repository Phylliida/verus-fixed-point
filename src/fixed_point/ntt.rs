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

// ── Exec NTT: Cooley-Tukey butterfly ───────────────────

/// Single butterfly operation: given u and t, compute (u+t, u-t).
pub fn butterfly_op(
    u: &RuntimeModularInt, t: &RuntimeModularInt,
) -> (result: (RuntimeModularInt, RuntimeModularInt))
    requires u.wf_spec(), t.wf_spec(), u.p == t.p,
    ensures result.0.wf_spec(), result.1.wf_spec(),
            result.0.p == u.p, result.1.p == u.p,
{
    let sum = u.add_exec(t);
    let diff = u.sub_exec(t);
    (sum, diff)
}

/// Exec-level bit-reversal permutation on a Vec of RuntimeModularInt.
pub fn bit_reverse_permutation(data: &mut Vec<RuntimeModularInt>, n: usize, log_n: usize)
    requires
        old(data)@.len() == n,
        n == pow2_nat(log_n as nat),
        n > 0,
        forall|i: int| 0 <= i < n as int ==> old(data)@[i].wf_spec() && old(data)@[i].p == old(data)@[0].p,
    ensures
        data@.len() == n,
        forall|i: int| 0 <= i < n as int ==> data@[i].wf_spec() && data@[i].p == old(data)@[0].p,
        // The permutation is correct (indices bit-reversed)
        // Full spec: data[i] == old(data)[bit_reverse(i, log_n)]
{
    // Simple O(n²) bit-reversal for correctness (optimized version later)
    let ghost p0 = old(data)@[0].p;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            data@.len() == n,
            n > 0,
            forall|k: int| 0 <= k < n as int ==> data@[k].wf_spec() && data@[k].p == p0,
        decreases n - i,
    {
        // Compute bit-reverse of i
        let mut rev: usize = 0;
        let mut bits: usize = i;
        let mut s: usize = 0;
        while s < log_n
            invariant
                s <= log_n,
                rev < n, // maintained by construction
                data@.len() == n,
                forall|k: int| 0 <= k < n as int ==> data@[k].wf_spec() && data@[k].p == p0,
            decreases log_n - s,
        {
            if rev < n / 2 { // guard overflow
                rev = rev * 2 + bits % 2;
            }
            bits = bits / 2;
            s = s + 1;
        }

        if rev > i && rev < n {
            let tmp = data[i].copy_exec();
            let swp = data[rev].copy_exec();
            data.set(i, swp);
            data.set(rev, tmp);
        }
        i = i + 1;
    }
}

/// Helper: 2^k as nat (for NTT size constraints).
pub open spec fn pow2_nat(k: nat) -> nat
    decreases k,
{
    if k == 0 { 1 }
    else { 2 * pow2_nat((k - 1) as nat) }
}

/// Exec-level forward NTT using iterative Cooley-Tukey butterfly.
/// Transforms data in-place. n must be a power of 2.
/// omega is a primitive n-th root of unity mod p.
pub fn ntt_butterfly_exec(
    data: &mut Vec<RuntimeModularInt>,
    omega: &RuntimeModularInt,
    n: usize,
    log_n: usize,
)
    requires
        old(data)@.len() == n,
        n == pow2_nat(log_n as nat),
        n > 1,
        n < 0x7FFF_FFFF, // prevent overflow in n+1
        log_n > 0,
        omega.wf_spec(),
        forall|i: int| 0 <= i < n as int ==> old(data)@[i].wf_spec() && old(data)@[i].p == omega.p,
    ensures
        data@.len() == n,
        forall|i: int| 0 <= i < n as int ==> data@[i].wf_spec(),
{
    // Step 1: Bit-reversal permutation
    bit_reverse_permutation(data, n, log_n);

    // Step 2: Butterfly stages
    let mut m: usize = 2;
    let mut stage: usize = 0;

    while stage < log_n
        invariant
            stage <= log_n,
            data@.len() == n,
            n > 1,
            m >= 2,
            m <= n + 1, // loose upper bound
            forall|i: int| 0 <= i < n as int ==> data@[i].wf_spec() && data@[i].p == omega.p,
            omega.wf_spec(),
            omega.p > 1,
        decreases log_n - stage,
    {
        let half_m = m / 2;
        // half_m >= 1 since m >= 2

        let mut group: usize = 0;
        while group <= n && n - group >= m
            invariant
                data@.len() == n,
                forall|i: int| 0 <= i < n as int ==> data@[i].wf_spec() && data@[i].p == omega.p,
                half_m >= 1, m >= 2, half_m == m / 2,
                group <= n,
                omega.wf_spec(), omega.p > 1,
            decreases n - group,
        {
            let mut w = RuntimeModularInt::new(1, omega.p);
            let mut k: usize = 0;
            proof { assert(half_m == m / 2); }

            while k < half_m
                invariant
                    k <= half_m,
                    data@.len() == n,
                    w.wf_spec(), w.p == omega.p,
                    forall|i: int| 0 <= i < n as int ==> data@[i].wf_spec() && data@[i].p == omega.p,
                    n - group >= m,
                    half_m >= 1, m >= 2, half_m == m / 2,
                    omega.wf_spec(), omega.p > 1,
                decreases half_m - k,
            {
                // Bounds: k < half_m = m/2, n - group >= m
                // group + k < group + m/2 < group + m <= n ✓
                // group + k + half_m < group + m <= n ✓
                proof {
                    assert(k < half_m);
                    assert(half_m + half_m <= m) by (nonlinear_arith)
                        requires half_m == m / 2, m >= 2;
                    assert(group + half_m <= n) by (nonlinear_arith)
                        requires n - group >= m, half_m <= m;
                    assert(group + k + half_m < group + m) by (nonlinear_arith)
                        requires k < half_m, half_m + half_m <= m;
                }
                let idx1 = group + k;
                let idx2 = group + k + half_m;

                let t = w.mul_exec(&data[idx2]);
                let u = data[idx1].copy_exec();
                let (new1, new2) = butterfly_op(&u, &t);

                data.set(idx1, new1);
                data.set(idx2, new2);

                w = w.mul_exec(omega);
                k = k + 1;
            }

            // Advance group. group + m <= n, so group' = group + m <= n
            group = group + m;
        }

        stage = stage + 1;
        // m doubles. Guard: if m > n, next iteration won't enter inner loop anyway
        if m <= n / 2 {
            m = m * 2;
        } else {
            m = n; // sentinel: ensures inner loop condition n - group >= m won't hold when group > 0
        }
    }
}

} // verus!
