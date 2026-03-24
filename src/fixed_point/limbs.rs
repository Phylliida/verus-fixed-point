use vstd::prelude::*;
use super::pow2::*;

verus! {

/// The radix base for a single limb (2^32 = 4294967296).
pub open spec fn limb_base() -> nat {
    4_294_967_296
}

/// Interpret a little-endian Seq<u32> as a natural number.
///
/// limbs_to_nat([a, b, c]) = a + b * 2^32 + c * 2^64
pub open spec fn limbs_to_nat(limbs: Seq<u32>) -> nat
    decreases limbs.len(),
{
    if limbs.len() == 0 {
        0
    } else {
        limbs[0] as nat + limb_base() * limbs_to_nat(limbs.subrange(1, limbs.len() as int))
    }
}

/// limb_base() == pow2(32).
pub proof fn lemma_limb_base_is_pow2_32()
    ensures limb_base() == pow2(32nat),
{
    lemma_pow2_32();
}

/// Empty sequence has value 0.
pub proof fn lemma_limbs_to_nat_empty()
    ensures limbs_to_nat(Seq::<u32>::empty()) == 0nat,
{}

/// Single-element sequence equals the element.
pub proof fn lemma_limbs_to_nat_single(v: u32)
    ensures limbs_to_nat(seq![v]) == v as nat,
{
    let s = seq![v];
    let tail = s.subrange(1, s.len() as int);
    assert(tail =~= Seq::<u32>::empty());
    assert(limbs_to_nat(tail) == 0);
    assert(limbs_to_nat(s) == v as nat + limb_base() * 0nat);
}

/// Recursive step: value = head + base * tail_value.
pub proof fn lemma_limbs_to_nat_cons(limbs: Seq<u32>)
    requires limbs.len() > 0,
    ensures
        limbs_to_nat(limbs) == limbs[0] as nat
            + limb_base() * limbs_to_nat(limbs.subrange(1, limbs.len() as int)),
{}

/// All-zero limbs have value 0.
pub proof fn lemma_limbs_to_nat_all_zeros(n: nat)
    ensures limbs_to_nat(Seq::new(n, |_i: int| 0u32)) == 0nat,
    decreases n,
{
    let limbs = Seq::new(n, |_i: int| 0u32);
    if n > 0 {
        let tail = limbs.subrange(1, n as int);
        assert(tail =~= Seq::new((n - 1) as nat, |_i: int| 0u32));
        lemma_limbs_to_nat_all_zeros((n - 1) as nat);
        assert(limbs_to_nat(tail) == 0);
        assert(limbs[0] == 0u32);
        assert(limbs_to_nat(limbs) == 0u32 as nat + limb_base() * 0nat);
    }
}

/// Upper bound: limbs_to_nat(limbs) < pow2(limbs.len() * 32).
pub proof fn lemma_limbs_to_nat_upper_bound(limbs: Seq<u32>)
    ensures limbs_to_nat(limbs) < pow2((limbs.len() * 32) as nat),
    decreases limbs.len(),
{
    if limbs.len() == 0 {
        lemma_pow2_positive(0);
    } else {
        let tail = limbs.subrange(1, limbs.len() as int);
        lemma_limbs_to_nat_upper_bound(tail);
        // tail.len() == limbs.len() - 1
        // IH: limbs_to_nat(tail) < pow2((limbs.len() - 1) * 32)
        // limbs[0] <= 2^32 - 1 = limb_base() - 1
        // limbs_to_nat(limbs) = limbs[0] + limb_base() * limbs_to_nat(tail)
        //   <= (limb_base() - 1) + limb_base() * (pow2((len-1)*32) - 1)
        //   = limb_base() - 1 + limb_base() * pow2((len-1)*32) - limb_base()
        //   = limb_base() * pow2((len-1)*32) - 1
        //   = pow2(32) * pow2((len-1)*32) - 1
        //   = pow2(len*32) - 1
        //   < pow2(len*32)
        lemma_limb_base_is_pow2_32();
        let len_minus_1 = (limbs.len() - 1) as nat;
        lemma_pow2_add(32, (len_minus_1 * 32) as nat);
        assert(pow2(32) * pow2((len_minus_1 * 32) as nat) == pow2((32 + len_minus_1 * 32) as nat));
        assert(32 + len_minus_1 * 32 == limbs.len() * 32);
        // Now bound: limbs[0] as nat + limb_base() * limbs_to_nat(tail)
        //   < limb_base() + limb_base() * pow2((len_minus_1 * 32) as nat)
        //   = limb_base() * (1 + pow2((len_minus_1 * 32) as nat))
        //   <= limb_base() * pow2((len_minus_1 * 32) as nat + 1)  ... not quite right
        // Simpler bound:
        //   limbs[0] as nat <= limb_base() - 1
        //   limbs_to_nat(tail) <= pow2((len_minus_1 * 32) as nat) - 1
        //   total <= (limb_base() - 1) + limb_base() * (pow2((len_minus_1 * 32) as nat) - 1)
        //         = limb_base() * pow2((len_minus_1 * 32) as nat) - 1
        //         = pow2((limbs.len() * 32) as nat) - 1
        //         < pow2((limbs.len() * 32) as nat)
        assert(limbs[0] as nat <= limb_base() - 1);
        assert(limbs_to_nat(tail) <= pow2((len_minus_1 * 32) as nat) - 1);
        assert(limbs_to_nat(limbs) <= (limb_base() - 1) + limb_base() * (pow2((len_minus_1 * 32) as nat) - 1));
        assert((limb_base() - 1) + limb_base() * (pow2((len_minus_1 * 32) as nat) - 1)
            == limb_base() * pow2((len_minus_1 * 32) as nat) - 1) by (nonlinear_arith)
            requires
                limb_base() > 0,
                pow2((len_minus_1 * 32) as nat) > 0,
        {
        }
        lemma_pow2_positive((len_minus_1 * 32) as nat);
    }
}

/// Appending a zero limb at the high end doesn't change the value.
pub proof fn lemma_limbs_to_nat_push_zero(limbs: Seq<u32>)
    ensures limbs_to_nat(limbs.push(0u32)) == limbs_to_nat(limbs),
    decreases limbs.len(),
{
    let extended = limbs.push(0u32);
    if limbs.len() == 0 {
        assert(extended =~= seq![0u32]);
        lemma_limbs_to_nat_single(0u32);
    } else {
        let tail = limbs.subrange(1, limbs.len() as int);
        let ext_tail = extended.subrange(1, extended.len() as int);
        assert(ext_tail =~= tail.push(0u32));
        lemma_limbs_to_nat_push_zero(tail);
        assert(limbs_to_nat(ext_tail) == limbs_to_nat(tail));
        assert(extended[0] == limbs[0]);
    }
}

/// Value of pushing a high limb:
/// limbs_to_nat(limbs.push(d)) == limbs_to_nat(limbs) + d * pow2(limbs.len() * 32)
pub proof fn lemma_limbs_to_nat_push(limbs: Seq<u32>, d: u32)
    ensures
        limbs_to_nat(limbs.push(d))
            == limbs_to_nat(limbs) + d as nat * pow2((limbs.len() * 32) as nat),
    decreases limbs.len(),
{
    let extended = limbs.push(d);
    if limbs.len() == 0 {
        assert(extended =~= seq![d]);
        lemma_limbs_to_nat_single(d);
        lemma_pow2_zero();
        assert(limbs_to_nat(limbs) == 0nat);
        assert(pow2(0nat) == 1nat);
        assert(d as nat * 1nat == d as nat);
    } else {
        let tail = limbs.subrange(1, limbs.len() as int);
        let ext_tail = extended.subrange(1, extended.len() as int);
        assert(ext_tail =~= tail.push(d));
        lemma_limbs_to_nat_push(tail, d);
        assert(extended[0] == limbs[0]);
        // IH: limbs_to_nat(ext_tail) == limbs_to_nat(tail) + d * pow2(tail.len() * 32)
        let tail_val = limbs_to_nat(tail);
        let d_nat = d as nat;
        let tail_pow = pow2((tail.len() * 32) as nat);

        // limbs_to_nat(extended) = extended[0] + base * limbs_to_nat(ext_tail)
        //   = limbs[0] + base * (tail_val + d * tail_pow)
        //   = limbs[0] + base * tail_val + base * d * tail_pow
        //   = limbs_to_nat(limbs) + base * d * tail_pow
        assert(limbs_to_nat(extended) == limbs[0] as nat + limb_base() * (tail_val + d_nat * tail_pow));
        assert(limb_base() * (tail_val + d_nat * tail_pow)
            == limb_base() * tail_val + limb_base() * d_nat * tail_pow) by (nonlinear_arith);
        assert(limbs_to_nat(limbs) == limbs[0] as nat + limb_base() * tail_val);

        // base * d * tail_pow == d * (base * tail_pow) == d * pow2(32 + tail.len() * 32)
        lemma_limb_base_is_pow2_32();
        lemma_pow2_add(32, (tail.len() * 32) as nat);
        assert(32 + tail.len() * 32 == limbs.len() * 32);
        assert(limb_base() * tail_pow == pow2((limbs.len() * 32) as nat));
        assert(limb_base() * d_nat * tail_pow == d_nat * (limb_base() * tail_pow)) by (nonlinear_arith);
    }
}

/// If limbs_to_nat != 0, at least one limb is nonzero.
pub proof fn lemma_limbs_to_nat_nonzero_means_nonzero_limb(limbs: Seq<u32>)
    requires limbs_to_nat(limbs) != 0,
    ensures exists|i: int| 0 <= i < limbs.len() && limbs[i] != 0u32,
    decreases limbs.len(),
{
    if limbs.len() == 0 {
        // contradiction: limbs_to_nat(empty) == 0
    } else if limbs[0] != 0u32 {
        assert(0int >= 0 && 0int < limbs.len() && limbs[0int] != 0u32);
    } else {
        // limbs[0] == 0, so limbs_to_nat(limbs) = limb_base() * limbs_to_nat(tail)
        let tail = limbs.subrange(1, limbs.len() as int);
        assert(limbs_to_nat(limbs) == limb_base() * limbs_to_nat(tail));
        // limb_base() > 0, and total != 0, so tail value != 0
        assert(limbs_to_nat(tail) != 0);
        lemma_limbs_to_nat_nonzero_means_nonzero_limb(tail);
        let i_tail = choose|i: int| 0 <= i < tail.len() && tail[i] != 0u32;
        assert(limbs[i_tail + 1] == tail[i_tail]);
        assert(0 <= i_tail + 1 && i_tail + 1 < limbs.len() && limbs[i_tail + 1] != 0u32);
    }
}

/// A sequence with a single nonzero limb at position k:
/// value == v * pow2(k * 32)
pub proof fn lemma_limbs_to_nat_single_nonzero(n: nat, k: nat, v: u32)
    requires k < n,
    ensures
        limbs_to_nat(Seq::new(n, |i: int| if i == k as int { v } else { 0u32 }))
            == v as nat * pow2((k * 32) as nat),
    decreases n,
{
    let limbs = Seq::new(n, |i: int| if i == k as int { v } else { 0u32 });
    if n == 1 {
        // k must be 0
        assert(k == 0);
        assert(limbs =~= seq![v]);
        lemma_limbs_to_nat_single(v);
        lemma_pow2_zero();
    } else {
        let tail = limbs.subrange(1, n as int);
        if k == 0 {
            // limbs[0] == v, tail is all zeros
            assert(tail =~= Seq::new((n - 1) as nat, |_i: int| 0u32));
            lemma_limbs_to_nat_all_zeros((n - 1) as nat);
            assert(limbs_to_nat(limbs) == v as nat + limb_base() * 0);
            lemma_pow2_zero();
        } else {
            // limbs[0] == 0, recurse on tail with k-1
            assert(tail =~= Seq::new((n - 1) as nat, |i: int| if i == (k - 1) as int { v } else { 0u32 }));
            lemma_limbs_to_nat_single_nonzero((n - 1) as nat, (k - 1) as nat, v);
            // IH: limbs_to_nat(tail) == v * pow2((k-1) * 32)
            assert(limbs[0] == 0u32);
            // limbs_to_nat(limbs) = 0 + limb_base() * v * pow2((k-1) * 32)
            //                     = pow2(32) * v * pow2((k-1) * 32)
            //                     = v * pow2(32 + (k-1) * 32)
            //                     = v * pow2(k * 32)
            lemma_limb_base_is_pow2_32();
            lemma_pow2_add(32, ((k - 1) * 32) as nat);
            assert(32 + (k - 1) * 32 == k * 32);
            assert(limbs_to_nat(limbs) == limb_base() * (v as nat * pow2(((k - 1) * 32) as nat)));
            assert(limb_base() * (v as nat * pow2(((k - 1) * 32) as nat))
                == v as nat * (limb_base() * pow2(((k - 1) * 32) as nat))) by (nonlinear_arith);
        }
    }
}

// ── nat_to_limbs: inverse of limbs_to_nat ──────────────────────

/// Construct n little-endian u32 limbs from a natural number.
/// Standard base-2^32 decomposition.
pub open spec fn nat_to_limbs(val: nat, n: nat) -> Seq<u32>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        seq![(val % limb_base()) as u32].add(
            nat_to_limbs(val / limb_base(), (n - 1) as nat))
    }
}

/// nat_to_limbs produces a sequence of exactly n elements.
pub proof fn lemma_nat_to_limbs_len(val: nat, n: nat)
    ensures nat_to_limbs(val, n).len() == n,
    decreases n,
{
    if n > 0 {
        lemma_nat_to_limbs_len(val / limb_base(), (n - 1) as nat);
    }
}

/// nat_to_limbs(0, n) produces all zeros.
pub proof fn lemma_nat_to_limbs_zero(n: nat)
    ensures nat_to_limbs(0nat, n) =~= Seq::new(n, |_i: int| 0u32),
    decreases n,
{
    if n > 0 {
        lemma_nat_to_limbs_zero((n - 1) as nat);
        // 0 % B == 0, 0 / B == 0
        assert(0nat % limb_base() == 0nat);
        assert(0nat / limb_base() == 0nat);
        // nat_to_limbs(0, n) == seq![0u32].add(nat_to_limbs(0, n-1))
        // IH: nat_to_limbs(0, n-1) =~= Seq::new(n-1, |_| 0u32)
        // seq![0u32].add(Seq::new(n-1, |_| 0u32)) =~= Seq::new(n, |_| 0u32)
        let result = seq![0u32].add(nat_to_limbs(0nat, (n - 1) as nat));
        let expected = Seq::new(n, |_i: int| 0u32);
        assert(result.len() == n) by {
            lemma_nat_to_limbs_len(0nat, (n - 1) as nat);
        }
        assert forall|i: int| 0 <= i < n as int implies result[i] == expected[i] by {
            if i == 0 {
                assert(result[0] == 0u32);
            } else {
                assert(result[i] == nat_to_limbs(0nat, (n - 1) as nat)[i - 1]);
            }
        }
    }
}

/// Roundtrip: limbs_to_nat(nat_to_limbs(v, n)) == v, when v fits in n limbs.
pub proof fn lemma_nat_to_limbs_roundtrip(val: nat, n: nat)
    requires val < pow2((n * 32) as nat),
    ensures limbs_to_nat(nat_to_limbs(val, n)) == val,
    decreases n,
{
    if n == 0 {
        // val < pow2(0) = 1, so val == 0
        lemma_pow2_zero();
    } else {
        let lo = (val % limb_base()) as u32;
        let hi = val / limb_base();
        let result = nat_to_limbs(val, n);
        let tail = nat_to_limbs(hi, (n - 1) as nat);

        // result == seq![lo].add(tail), so result[0] == lo
        // result.subrange(1, result.len()) =~= tail
        lemma_nat_to_limbs_len(val, n);
        lemma_nat_to_limbs_len(hi, (n - 1) as nat);
        assert(result.subrange(1, result.len() as int) =~= tail);

        // Need: hi < pow2((n-1) * 32)
        // val < pow2(n * 32) = limb_base() * pow2((n-1) * 32)  [by pow2_add(32, (n-1)*32)]
        // hi = val / limb_base() < pow2((n-1) * 32)
        lemma_limb_base_is_pow2_32();
        lemma_pow2_add(32, ((n - 1) * 32) as nat);
        assert(32 + (n - 1) * 32 == n * 32);
        assert(pow2((n * 32) as nat) == limb_base() * pow2(((n - 1) * 32) as nat));

        // IH: limbs_to_nat(tail) == hi
        lemma_nat_to_limbs_roundtrip(hi, (n - 1) as nat);

        // limbs_to_nat(result) = lo + limb_base() * limbs_to_nat(tail)
        //                      = lo + limb_base() * hi
        //                      = (val % B) + B * (val / B) = val
        assert(limbs_to_nat(result) == lo as nat + limb_base() * hi);
        assert(lo as nat + limb_base() * hi == val) by (nonlinear_arith)
            requires
                lo as nat == val % limb_base(),
                hi == val / limb_base(),
                limb_base() > 0,
        {
        }
    }
}

/// Appending extra zero limbs to a sequence preserves its value.
pub proof fn lemma_limbs_to_nat_append_zeros(limbs: Seq<u32>, extra: nat)
    ensures limbs_to_nat(limbs.add(Seq::new(extra, |_i: int| 0u32))) == limbs_to_nat(limbs),
    decreases extra,
{
    if extra == 0 {
        assert(Seq::new(0nat, |_i: int| 0u32) =~= Seq::<u32>::empty());
        assert(limbs.add(Seq::<u32>::empty()) =~= limbs);
    } else {
        // limbs ++ zeros(extra) == (limbs ++ zeros(extra-1)).push(0)
        let zeros_prev = Seq::new((extra - 1) as nat, |_i: int| 0u32);
        let zeros_full = Seq::new(extra, |_i: int| 0u32);

        // zeros_full == zeros_prev.push(0u32)
        assert(zeros_full =~= zeros_prev.push(0u32));

        // limbs.add(zeros_full) == limbs.add(zeros_prev).push(0u32)
        // This is sequence associativity + push == add(seq![x])
        let mid = limbs.add(zeros_prev);
        assert(limbs.add(zeros_full) =~= mid.push(0u32));

        // By IH: limbs_to_nat(mid) == limbs_to_nat(limbs)
        lemma_limbs_to_nat_append_zeros(limbs, (extra - 1) as nat);

        // By push_zero: limbs_to_nat(mid.push(0)) == limbs_to_nat(mid)
        lemma_limbs_to_nat_push_zero(mid);
    }
}

/// Subrange growth: extending a subrange by one element equals pushing that element.
/// limbs_to_nat(limbs.subrange(0, i+1)) == limbs_to_nat(limbs.subrange(0, i)) + limbs[i] * pow2(i * 32)
pub proof fn lemma_limbs_to_nat_subrange_extend(limbs: Seq<u32>, i: nat)
    requires i < limbs.len(),
    ensures
        limbs_to_nat(limbs.subrange(0, (i + 1) as int))
            == limbs_to_nat(limbs.subrange(0, i as int)) + limbs[i as int] as nat * pow2((i * 32) as nat),
{
    let prefix = limbs.subrange(0, i as int);
    let extended = limbs.subrange(0, (i + 1) as int);
    // extended == prefix.push(limbs[i])
    assert(extended =~= prefix.push(limbs[i as int]));
    lemma_limbs_to_nat_push(prefix, limbs[i as int]);
}

/// Subrange of length 0 has value 0.
pub proof fn lemma_limbs_to_nat_subrange_zero(limbs: Seq<u32>)
    ensures limbs_to_nat(limbs.subrange(0, 0int)) == 0nat,
{
    assert(limbs.subrange(0, 0int) =~= Seq::<u32>::empty());
}

/// Full subrange equals the original sequence.
pub proof fn lemma_limbs_to_nat_subrange_full(limbs: Seq<u32>)
    ensures limbs_to_nat(limbs.subrange(0, limbs.len() as int)) == limbs_to_nat(limbs),
{
    assert(limbs.subrange(0, limbs.len() as int) =~= limbs);
}

/// A prefix of a limb sequence has a value <= the full sequence.
pub proof fn lemma_limbs_to_nat_prefix_le_full(limbs: Seq<u32>, prefix_len: nat)
    requires prefix_len <= limbs.len(),
    ensures limbs_to_nat(limbs.subrange(0, prefix_len as int)) <= limbs_to_nat(limbs),
    decreases limbs.len() - prefix_len,
{
    if prefix_len == limbs.len() {
        lemma_limbs_to_nat_subrange_full(limbs);
    } else {
        // Extend by one: ltn(limbs[..prefix_len+1]) = ltn(limbs[..prefix_len]) + limbs[prefix_len] * pow2(...)
        lemma_limbs_to_nat_subrange_extend(limbs, prefix_len);
        // ltn(limbs[..prefix_len]) <= ltn(limbs[..prefix_len+1])
        lemma_pow2_positive((prefix_len * 32) as nat);
        // By IH: ltn(limbs[..prefix_len+1]) <= ltn(limbs)
        lemma_limbs_to_nat_prefix_le_full(limbs, prefix_len + 1);
    }
}

/// If two same-length sequences are equal element-wise, their limbs_to_nat values are equal.
pub proof fn lemma_limbs_to_nat_eq(a: Seq<u32>, b: Seq<u32>)
    requires a =~= b,
    ensures limbs_to_nat(a) == limbs_to_nat(b),
{}

/// Prepending n zero limbs scales the value by pow2(n * 32).
/// limbs_to_nat(zeros(n) ++ a) == limbs_to_nat(a) * pow2(n * 32)
pub proof fn lemma_limbs_to_nat_prepend_zeros(a: Seq<u32>, n: nat)
    ensures
        limbs_to_nat(Seq::new(n, |_j: int| 0u32).add(a))
            == limbs_to_nat(a) * pow2((n * 32) as nat),
    decreases n,
{
    let zeros = Seq::new(n, |_j: int| 0u32);
    if n == 0 {
        assert(zeros.add(a) =~= a);
        lemma_pow2_zero();
    } else {
        // zeros(n) ++ a == [0] ++ (zeros(n-1) ++ a)
        let inner = Seq::new((n - 1) as nat, |_j: int| 0u32).add(a);
        let full = zeros.add(a);
        assert(full[0] == 0u32);
        assert(full.subrange(1, full.len() as int) =~= inner);

        // ltn(full) = full[0] + BASE * ltn(full[1..]) = 0 + BASE * ltn(inner)
        // By IH: ltn(inner) == ltn(a) * pow2((n-1)*32)
        lemma_limbs_to_nat_prepend_zeros(a, (n - 1) as nat);

        // ltn(full) = BASE * ltn(a) * pow2((n-1)*32) = ltn(a) * BASE * pow2((n-1)*32)
        //           = ltn(a) * pow2(32) * pow2((n-1)*32) = ltn(a) * pow2(n*32)
        lemma_limb_base_is_pow2_32();
        lemma_pow2_add(32, ((n - 1) * 32) as nat);
        assert(32 + (n - 1) * 32 == n * 32);
        assert(limbs_to_nat(full) == limb_base() * (limbs_to_nat(a) * pow2(((n - 1) * 32) as nat)));
        assert(limb_base() * (limbs_to_nat(a) * pow2(((n - 1) * 32) as nat))
            == limbs_to_nat(a) * (limb_base() * pow2(((n - 1) * 32) as nat))) by (nonlinear_arith);
    }
}

/// Split a limb sequence at position `mid`:
/// limbs_to_nat(limbs) == limbs_to_nat(limbs[..mid]) + limbs_to_nat(limbs[mid..]) * pow2(mid * 32)
pub proof fn lemma_limbs_to_nat_split(limbs: Seq<u32>, mid: nat)
    requires mid <= limbs.len(),
    ensures
        limbs_to_nat(limbs) == limbs_to_nat(limbs.subrange(0, mid as int))
            + limbs_to_nat(limbs.subrange(mid as int, limbs.len() as int)) * pow2((mid * 32) as nat),
    decreases mid,
{
    if mid == 0 {
        assert(limbs.subrange(0, 0int) =~= Seq::<u32>::empty());
        assert(limbs.subrange(0, limbs.len() as int) =~= limbs);
        lemma_pow2_zero();
    } else {
        // Induction: split off the first element
        // limbs = [limbs[0]] ++ limbs[1..]
        // ltn(limbs) = limbs[0] + BASE * ltn(limbs[1..])
        let tail = limbs.subrange(1, limbs.len() as int);
        // IH on tail at mid-1:
        // ltn(tail) = ltn(tail[..mid-1]) + ltn(tail[mid-1..]) * pow2((mid-1)*32)
        lemma_limbs_to_nat_split(tail, (mid - 1) as nat);

        // tail[..mid-1] == limbs[1..mid]
        let tail_lo = tail.subrange(0, (mid - 1) as int);
        let limbs_lo = limbs.subrange(0, mid as int);
        let limbs_1_to_mid = limbs.subrange(1, mid as int);
        assert(tail_lo =~= limbs_1_to_mid);

        // tail[mid-1..] == limbs[mid..]
        let tail_hi = tail.subrange((mid - 1) as int, tail.len() as int);
        let limbs_hi = limbs.subrange(mid as int, limbs.len() as int);
        assert(tail_hi =~= limbs_hi);

        // ltn(limbs) = limbs[0] + BASE * ltn(tail)
        //            = limbs[0] + BASE * (ltn(tail_lo) + ltn(tail_hi) * pow2((mid-1)*32))
        //            = limbs[0] + BASE * ltn(limbs[1..mid]) + BASE * ltn(limbs[mid..]) * pow2((mid-1)*32)
        //
        // ltn(limbs[..mid]) = limbs[0] + BASE * ltn(limbs[1..mid])
        //   (by the recursive definition applied to limbs[..mid])
        let lo = limbs.subrange(0, mid as int);
        assert(lo[0] == limbs[0]);
        assert(lo.subrange(1, lo.len() as int) =~= limbs_1_to_mid);

        // ltn(limbs[mid..]) * pow2(mid*32) = ltn(limbs_hi) * BASE * pow2((mid-1)*32)
        //                                  = ltn(limbs_hi) * pow2(32) * pow2((mid-1)*32)
        //                                  = ltn(limbs_hi) * pow2(mid*32)
        lemma_limb_base_is_pow2_32();
        lemma_pow2_add(32, ((mid - 1) * 32) as nat);
        assert(32 + (mid - 1) * 32 == mid * 32);

        // Chain the algebra
        assert(limbs_to_nat(limbs) == limbs[0] as nat + limb_base() * limbs_to_nat(tail));
        assert(limbs_to_nat(tail) == limbs_to_nat(tail_lo) + limbs_to_nat(tail_hi) * pow2(((mid - 1) * 32) as nat));
        assert(limbs_to_nat(lo) == limbs[0] as nat + limb_base() * limbs_to_nat(limbs_1_to_mid));

        assert(limbs_to_nat(limbs)
            == limbs_to_nat(lo) + limb_base() * limbs_to_nat(limbs_hi) * pow2(((mid - 1) * 32) as nat))
            by (nonlinear_arith)
            requires
                limbs_to_nat(limbs) == limbs[0] as nat + limb_base() * limbs_to_nat(tail),
                limbs_to_nat(tail) == limbs_to_nat(limbs_1_to_mid) + limbs_to_nat(limbs_hi) * pow2(((mid - 1) * 32) as nat),
                limbs_to_nat(lo) == limbs[0] as nat + limb_base() * limbs_to_nat(limbs_1_to_mid),
        {}

        assert(limb_base() * limbs_to_nat(limbs_hi) * pow2(((mid - 1) * 32) as nat)
            == limbs_to_nat(limbs_hi) * pow2((mid * 32) as nat)) by (nonlinear_arith)
            requires
                limb_base() * pow2(((mid - 1) * 32) as nat) == pow2((mid * 32) as nat),
        {}
    }
}

/// Distributive law: (a + b) * c == a * c + b * c.
/// Verus's Z3 needs this as an explicit lemma for int multiplication.
pub proof fn lemma_mul_distribute(a: int, b: int, c: int)
    ensures (a + b) * c == a * c + b * c,
{
    // This should follow from Verus's built-in int arithmetic axioms
    // If Z3 can't prove it directly, we can try nonlinear_arith
    assert((a + b) * c == a * c + b * c) by (nonlinear_arith);
}

/// Karatsuba algebraic identity (using int to avoid nat subtraction issues):
/// (a_hi * B + a_lo) * (b_hi * B + b_lo)
///   == z0 + z1 * B + z2 * B^2
/// where z0 = a_lo*b_lo, z2 = a_hi*b_hi, z1 = (a_lo+a_hi)*(b_lo+b_hi) - z0 - z2
pub proof fn lemma_karatsuba_identity(a_lo: int, a_hi: int, b_lo: int, b_hi: int, base: int)
    ensures
    ({
        let z0 = a_lo * b_lo;
        let z2 = a_hi * b_hi;
        let z1 = (a_lo + a_hi) * (b_lo + b_hi) - z0 - z2;
        (a_hi * base + a_lo) * (b_hi * base + b_lo) == z0 + z1 * base + z2 * base * base
    }),
{
    // Expand LHS:
    // (a_hi * B + a_lo)(b_hi * B + b_lo)
    // = a_hi * b_hi * B^2 + a_hi * b_lo * B + a_lo * b_hi * B + a_lo * b_lo
    //
    // RHS z1 term:
    // (a_lo + a_hi)(b_lo + b_hi) - a_lo*b_lo - a_hi*b_hi
    // = a_lo*b_lo + a_lo*b_hi + a_hi*b_lo + a_hi*b_hi - a_lo*b_lo - a_hi*b_hi
    // = a_lo*b_hi + a_hi*b_lo
    //
    // RHS = a_lo*b_lo + (a_lo*b_hi + a_hi*b_lo)*B + a_hi*b_hi*B^2
    // = LHS ✓

    // We prove the identity by introducing intermediate product terms
    // and using distributive lemmas.

    let z0 = a_lo * b_lo;
    let z2 = a_hi * b_hi;

    // Step 1: (a_lo + a_hi) * (b_lo + b_hi) == z0 + (a_lo*b_hi + a_hi*b_lo) + z2
    lemma_mul_distribute(a_lo, a_hi, b_lo + b_hi);
    lemma_mul_distribute(a_lo, a_hi, b_lo);
    lemma_mul_distribute(a_lo, a_hi, b_hi);
    // -> (a_lo + a_hi) * X = a_lo * X + a_hi * X, for X = b_lo+b_hi, b_lo, b_hi

    lemma_mul_distribute(b_lo, b_hi, a_lo);
    lemma_mul_distribute(b_lo, b_hi, a_hi);
    // -> a_lo * (b_lo + b_hi) = a_lo * b_lo + a_lo * b_hi, etc.

    let cross = a_lo * b_hi + a_hi * b_lo;
    let z1 = (a_lo + a_hi) * (b_lo + b_hi) - z0 - z2;
    assert(z1 == cross);

    // Step 2: Expand LHS
    let lhs = (a_hi * base + a_lo) * (b_hi * base + b_lo);

    // (a_hi*B + a_lo) * (b_hi*B + b_lo) = (a_hi*B)*(b_hi*B+b_lo) + a_lo*(b_hi*B+b_lo)
    lemma_mul_distribute(a_hi * base, a_lo, b_hi * base + b_lo);
    let t1 = (a_hi * base) * (b_hi * base + b_lo);
    let t2 = a_lo * (b_hi * base + b_lo);
    assert(lhs == t1 + t2);

    // t1 = (a_hi*B)*(b_hi*B) + (a_hi*B)*b_lo
    lemma_mul_distribute(b_hi * base, b_lo, a_hi * base);
    assert(t1 == (a_hi * base) * (b_hi * base) + (a_hi * base) * b_lo);

    // t2 = a_lo*(b_hi*B) + a_lo*b_lo
    lemma_mul_distribute(b_hi * base, b_lo, a_lo);
    assert(t2 == a_lo * (b_hi * base) + z0);

    // (a_hi*B)*(b_hi*B) = a_hi*b_hi*B*B = z2*B*B
    // Break into two steps: first rearrange, then substitute z2
    assert((a_hi * base) * (b_hi * base) == a_hi * b_hi * (base * base)) by (nonlinear_arith);
    assert(a_hi * b_hi * (base * base) == z2 * base * base) by (nonlinear_arith)
        requires z2 == a_hi * b_hi;

    // (a_hi*B)*b_lo = a_hi*b_lo*B
    assert((a_hi * base) * b_lo == a_hi * b_lo * base) by (nonlinear_arith);

    // a_lo*(b_hi*B) = a_lo*b_hi*B
    assert(a_lo * (b_hi * base) == a_lo * b_hi * base) by (nonlinear_arith);

    // lhs = z2*B*B + a_hi*b_lo*B + a_lo*b_hi*B + z0
    assert(lhs == z2 * base * base + a_hi * b_lo * base + a_lo * b_hi * base + z0);

    // cross*B = (a_lo*b_hi + a_hi*b_lo)*B = a_lo*b_hi*B + a_hi*b_lo*B
    lemma_mul_distribute(a_lo * b_hi, a_hi * b_lo, base);
    assert(cross * base == a_lo * b_hi * base + a_hi * b_lo * base);

    // lhs = z0 + cross*B + z2*B*B
    assert(lhs == z0 + cross * base + z2 * base * base);

    // z1 == cross, so z0 + z1*B + z2*B*B == lhs
}

/// Helper for Karatsuba: if the full product is correct and fits,
/// then the subtraction borrows and addition carries are all zero.
pub proof fn lemma_karatsuba_no_overflow(
    ltn_a: nat, ltn_b: nat, bound: nat,
    z0: nat, z2: nat, z1_full: nat,
    ltn_z1_tmp: nat, bw1: nat,
    ltn_z1: nat, bw2: nat,
    P_sub: nat,
)
    requires
        z1_full >= z0 + z2,
        // sub_limbs #1: ltn_z1_tmp + z0 == z1_full + bw1 * P_sub
        ltn_z1_tmp + z0 == z1_full + bw1 * P_sub,
        ltn_z1_tmp < P_sub,
        bw1 <= 1,
        // sub_limbs #2: ltn_z1 + z2 == ltn_z1_tmp + bw2 * P_sub
        ltn_z1 + z2 == ltn_z1_tmp + bw2 * P_sub,
        ltn_z1 < P_sub,
        bw2 <= 1,
    ensures
        bw1 == 0,
        bw2 == 0,
        ltn_z1_tmp == z1_full - z0,
        ltn_z1 == z1_full - z0 - z2,
{
    // bw1 == 0: if bw1 == 1, then ltn_z1_tmp + z0 == z1_full + P_sub
    // => ltn_z1_tmp = z1_full - z0 + P_sub >= P_sub (since z1_full >= z0)
    // But ltn_z1_tmp < P_sub. Contradiction.
    assert(bw1 == 0) by (nonlinear_arith)
        requires
            ltn_z1_tmp + z0 == z1_full + bw1 * P_sub,
            z1_full >= z0,
            ltn_z1_tmp < P_sub,
            bw1 <= 1,
    {}
    assert(ltn_z1_tmp == z1_full - z0);

    // bw2 == 0: similarly, ltn_z1_tmp >= z2 (since z1_full - z0 >= z2)
    assert(ltn_z1_tmp >= z2) by (nonlinear_arith)
        requires ltn_z1_tmp == z1_full - z0, z1_full >= z0 + z2;
    assert(bw2 == 0) by (nonlinear_arith)
        requires
            ltn_z1 + z2 == ltn_z1_tmp + bw2 * P_sub,
            ltn_z1_tmp >= z2,
            ltn_z1 < P_sub,
            bw2 <= 1,
    {}
}

/// Helper for Karatsuba: the final adds don't overflow and produce the correct product.
pub proof fn lemma_karatsuba_combine(
    ltn_a: nat, ltn_b: nat, n: nat, half: nat,
    z0: nat, z2: nat, z1: nat,
    ltn_z1_shifted: nat, ltn_z2_shifted: nat,
    ltn_s1: nat, c1: nat,
    ltn_s2: nat, c2: nat,
    Rn: nat,
)
    requires
        ltn_a < pow2((n * 32) as nat),
        ltn_b < pow2((n * 32) as nat),
        half <= n,
        Rn == pow2((2 * n * 32) as nat),
        // Karatsuba identity (from lemma_karatsuba_identity)
        (ltn_a as int) * (ltn_b as int) == (z0 as int) + (z1 as int) * (pow2((half * 32) as nat) as int) + (z2 as int) * (pow2((half * 32) as nat) as int) * (pow2((half * 32) as nat) as int),
        // Shifted values
        ltn_z1_shifted == z1 * pow2((half * 32) as nat),
        ltn_z2_shifted == z2 * pow2((2 * half * 32) as nat),
        pow2((2 * half * 32) as nat) == pow2((half * 32) as nat) * pow2((half * 32) as nat),
        // add_limbs #1
        ltn_s1 + c1 * Rn == z0 + ltn_z1_shifted,
        ltn_s1 < Rn,
        c1 <= 1,
        // add_limbs #2
        ltn_s2 + c2 * Rn == ltn_s1 + ltn_z2_shifted,
        ltn_s2 < Rn,
        c2 <= 1,
    ensures
        c1 == 0,
        c2 == 0,
        ltn_s2 == ltn_a * ltn_b,
{
    lemma_pow2_positive((n * 32) as nat);
    let bound = pow2((n * 32) as nat);

    // Product < bound^2 = Rn
    assert(ltn_a * ltn_b < bound * bound) by (nonlinear_arith)
        requires ltn_a < bound, ltn_b < bound, bound > 0;
    lemma_pow2_double((n * 32) as nat);
    assert(2 * (n * 32) == 2 * n * 32) by (nonlinear_arith);
    assert(bound * bound == Rn);
    let product = ltn_a * ltn_b;
    assert(product < Rn);

    // z0 + z1_shifted == z0 + z1 * B^half
    // z0 + z1*B^half + z2*B^(2*half) == product < Rn
    // So z0 + z1_shifted <= product < Rn => c1 == 0
    let B = pow2((half * 32) as nat);
    // z0 + z1*B + z2*B*B == product (from Karatsuba identity)
    // z1_shifted == z1*B, z2_shifted == z2*B*B
    assert(ltn_z2_shifted == z2 * B * B) by (nonlinear_arith)
        requires
            ltn_z2_shifted == z2 * pow2((2 * half * 32) as nat),
            pow2((2 * half * 32) as nat) == B * B,
    {}
    assert(z0 + ltn_z1_shifted + ltn_z2_shifted == product) by (nonlinear_arith)
        requires
            product as int == (z0 as int) + (z1 as int) * (B as int) + (z2 as int) * (B as int) * (B as int),
            ltn_z1_shifted == z1 * B,
            ltn_z2_shifted == z2 * B * B,
    {}

    assert(z0 + ltn_z1_shifted <= product) by (nonlinear_arith)
        requires z0 + ltn_z1_shifted + ltn_z2_shifted == product;
    assert(z0 + ltn_z1_shifted < Rn) by (nonlinear_arith)
        requires z0 + ltn_z1_shifted <= product, product < Rn;

    assert(c1 == 0) by (nonlinear_arith)
        requires
            ltn_s1 + c1 * Rn == z0 + ltn_z1_shifted,
            z0 + ltn_z1_shifted < Rn,
            ltn_s1 < Rn,
            c1 <= 1,
    {}

    assert(ltn_s1 == z0 + ltn_z1_shifted);
    assert(ltn_s1 + ltn_z2_shifted == product);

    assert(c2 == 0) by (nonlinear_arith)
        requires
            ltn_s2 + c2 * Rn == ltn_s1 + ltn_z2_shifted,
            ltn_s1 + ltn_z2_shifted == product,
            product < Rn,
            ltn_s2 < Rn,
            c2 <= 1,
    {}

    assert(ltn_s2 == product);
}

// ── Base-2^32 representation uniqueness ────────────────

/// The lowest limb of a sequence is value % limb_base.
pub proof fn lemma_limbs_to_nat_lowest(limbs: Seq<u32>)
    requires limbs.len() > 0,
    ensures limbs[0] as nat == limbs_to_nat(limbs) % limb_base(),
{
    // ltn(limbs) = limbs[0] + BASE * ltn(tail)
    // ltn(limbs) % BASE = (limbs[0] + BASE * ltn(tail)) % BASE
    //                   = limbs[0] % BASE (since BASE * ltn(tail) is divisible by BASE)
    //                   = limbs[0] (since limbs[0] < BASE as it's a u32)
    let tail = limbs.subrange(1, limbs.len() as int);
    assert(limbs_to_nat(limbs) == limbs[0] as nat + limb_base() * limbs_to_nat(tail));
    // limbs[0] < limb_base (since it's a u32 and limb_base = 2^32)
    let lo = limbs[0] as nat;
    assert(lo < limb_base());
    assert((lo + limb_base() * limbs_to_nat(tail)) % limb_base() == lo) by (nonlinear_arith)
        requires lo < limb_base(), limb_base() > 0;
}

/// The value without the lowest limb is value / limb_base.
pub proof fn lemma_limbs_to_nat_shift(limbs: Seq<u32>)
    requires limbs.len() > 0,
    ensures
        limbs_to_nat(limbs.subrange(1, limbs.len() as int))
            == limbs_to_nat(limbs) / limb_base(),
{
    let tail = limbs.subrange(1, limbs.len() as int);
    let lo = limbs[0] as nat;
    assert(limbs_to_nat(limbs) == lo + limb_base() * limbs_to_nat(tail));
    assert(lo < limb_base());
    assert((lo + limb_base() * limbs_to_nat(tail)) / limb_base()
        == limbs_to_nat(tail)) by (nonlinear_arith)
        requires lo < limb_base(), limb_base() > 0;
}

/// Base-2^32 representation uniqueness:
/// If two sequences of the same length have the same limbs_to_nat value,
/// they are element-wise equal.
pub proof fn lemma_limbs_to_nat_unique(a: Seq<u32>, b: Seq<u32>)
    requires
        a.len() == b.len(),
        limbs_to_nat(a) == limbs_to_nat(b),
    ensures
        a =~= b,
    decreases a.len(),
{
    if a.len() == 0 {
        // Both empty, trivially equal
    } else {
        // Lowest limb: a[0] == ltn(a) % BASE == ltn(b) % BASE == b[0]
        lemma_limbs_to_nat_lowest(a);
        lemma_limbs_to_nat_lowest(b);
        assert(a[0] == b[0]);

        // Tail: ltn(a_tail) == ltn(a) / BASE == ltn(b) / BASE == ltn(b_tail)
        let a_tail = a.subrange(1, a.len() as int);
        let b_tail = b.subrange(1, b.len() as int);
        lemma_limbs_to_nat_shift(a);
        lemma_limbs_to_nat_shift(b);
        assert(limbs_to_nat(a_tail) == limbs_to_nat(b_tail));

        // By induction: a_tail =~= b_tail
        lemma_limbs_to_nat_unique(a_tail, b_tail);

        // Combine: a[0] == b[0] and a[1..] =~= b[1..] => a =~= b
        assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
            if i == 0 {
                assert(a[0] == b[0]);
            } else {
                assert(a[i] == a_tail[i - 1]);
                assert(b[i] == b_tail[i - 1]);
            }
        }
    }
}

/// Corollary: nat_to_limbs and limbs_to_nat are inverses (the other direction).
/// If limbs_to_nat(a) == val and a.len() == n and val < pow2(n*32),
/// then a == nat_to_limbs(val, n).
pub proof fn lemma_limbs_nat_to_limbs_identity(a: Seq<u32>, n: nat)
    requires
        a.len() == n,
        limbs_to_nat(a) < pow2((n * 32) as nat),
    ensures
        a =~= nat_to_limbs(limbs_to_nat(a), n),
{
    let val = limbs_to_nat(a);
    lemma_nat_to_limbs_roundtrip(val, n);
    // limbs_to_nat(nat_to_limbs(val, n)) == val == limbs_to_nat(a)
    lemma_nat_to_limbs_len(val, n);
    // nat_to_limbs(val, n).len() == n == a.len()
    lemma_limbs_to_nat_unique(a, nat_to_limbs(val, n));
}

} // verus!
