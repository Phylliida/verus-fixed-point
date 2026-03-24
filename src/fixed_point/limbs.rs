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
    assert(seq![v].subrange(1, 1int) =~= Seq::<u32>::empty());
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
    ensures limbs_to_nat(Seq::new(n as int, |_i: int| 0u32)) == 0nat,
    decreases n,
{
    let limbs = Seq::new(n as int, |_i: int| 0u32);
    if n > 0 {
        let tail = limbs.subrange(1, n as int);
        assert(tail =~= Seq::new((n - 1) as int, |_i: int| 0u32));
        lemma_limbs_to_nat_all_zeros((n - 1) as nat);
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
    } else {
        let tail = limbs.subrange(1, limbs.len() as int);
        let ext_tail = extended.subrange(1, extended.len() as int);
        assert(ext_tail =~= tail.push(d));
        lemma_limbs_to_nat_push(tail, d);
        assert(extended[0] == limbs[0]);
        // limbs_to_nat(ext) = limbs[0] + base * limbs_to_nat(ext_tail)
        //   = limbs[0] + base * (limbs_to_nat(tail) + d * pow2(tail.len() * 32))
        //   = (limbs[0] + base * limbs_to_nat(tail)) + base * d * pow2(tail.len() * 32)
        //   = limbs_to_nat(limbs) + d * base * pow2(tail.len() * 32)
        //   = limbs_to_nat(limbs) + d * pow2(32) * pow2(tail.len() * 32)
        //   = limbs_to_nat(limbs) + d * pow2(32 + tail.len() * 32)
        //   = limbs_to_nat(limbs) + d * pow2(limbs.len() * 32)
        lemma_limb_base_is_pow2_32();
        lemma_pow2_add(32, (tail.len() * 32) as nat);
        assert(32 + tail.len() * 32 == limbs.len() * 32);
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
        limbs_to_nat(Seq::new(n as int, |i: int| if i == k as int { v } else { 0u32 }))
            == v as nat * pow2((k * 32) as nat),
    decreases n,
{
    let limbs = Seq::new(n as int, |i: int| if i == k as int { v } else { 0u32 });
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
            assert(tail =~= Seq::new((n - 1) as int, |_i: int| 0u32));
            lemma_limbs_to_nat_all_zeros((n - 1) as nat);
            assert(limbs_to_nat(limbs) == v as nat + limb_base() * 0);
            lemma_pow2_zero();
        } else {
            // limbs[0] == 0, recurse on tail with k-1
            assert(tail =~= Seq::new((n - 1) as int, |i: int| if i == (k - 1) as int { v } else { 0u32 }));
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

} // verus!
