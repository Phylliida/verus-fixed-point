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

} // verus!
