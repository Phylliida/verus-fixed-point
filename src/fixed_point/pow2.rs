use vstd::prelude::*;

verus! {

/// 2^n, defined recursively.
pub open spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 }
    else { 2 * pow2((n - 1) as nat) }
}

/// pow2 is always positive.
pub proof fn lemma_pow2_positive(n: nat)
    ensures pow2(n) > 0,
    decreases n,
{
    if n > 0 {
        lemma_pow2_positive((n - 1) as nat);
    }
}

/// pow2(0) == 1.
pub proof fn lemma_pow2_zero()
    ensures pow2(0nat) == 1nat,
{}

/// pow2(1) == 2.
pub proof fn lemma_pow2_one()
    ensures pow2(1nat) == 2nat,
{}

/// pow2(a + b) == pow2(a) * pow2(b).
pub proof fn lemma_pow2_add(a: nat, b: nat)
    ensures pow2(a + b) == pow2(a) * pow2(b),
    decreases a,
{
    if a == 0 {
        assert(pow2(0 + b) == pow2(b));
        assert(pow2(0nat) == 1nat);
    } else {
        lemma_pow2_add((a - 1) as nat, b);
        assert(pow2(a + b) == 2 * pow2(((a + b) - 1) as nat));
        assert(((a + b) - 1) as nat == ((a - 1) as nat + b));
    }
}

/// Monotonicity: a <= b ==> pow2(a) <= pow2(b).
pub proof fn lemma_pow2_monotone(a: nat, b: nat)
    requires a <= b,
    ensures pow2(a) <= pow2(b),
    decreases b,
{
    if a < b {
        lemma_pow2_monotone(a, (b - 1) as nat);
        lemma_pow2_positive((b - 1) as nat);
        assert(pow2(b) == 2 * pow2((b - 1) as nat));
        assert(pow2((b - 1) as nat) >= pow2(a));
        assert(2 * pow2((b - 1) as nat) >= pow2((b - 1) as nat));
    }
}

/// Strict monotonicity: a < b ==> pow2(a) < pow2(b).
pub proof fn lemma_pow2_strict_monotone(a: nat, b: nat)
    requires a < b,
    ensures pow2(a) < pow2(b),
    decreases b,
{
    if b == a + 1 {
        lemma_pow2_positive(a);
        assert(pow2(b) == 2 * pow2(a));
    } else {
        lemma_pow2_strict_monotone(a, (b - 1) as nat);
        lemma_pow2_positive((b - 1) as nat);
        assert(pow2(b) == 2 * pow2((b - 1) as nat));
    }
}

/// pow2(8) == 256.
pub proof fn lemma_pow2_8()
    ensures pow2(8nat) == 256nat,
{
    reveal_with_fuel(pow2, 9);
}

/// pow2(16) == 65536.
pub proof fn lemma_pow2_16()
    ensures pow2(16nat) == 65536nat,
{
    lemma_pow2_8();
    lemma_pow2_add(8, 8);
    assert(pow2(16) == pow2(8) * pow2(8));
}

/// pow2(32) == 4294967296 (the limb base).
pub proof fn lemma_pow2_32()
    ensures pow2(32nat) == 4294967296nat,
{
    lemma_pow2_16();
    lemma_pow2_add(16, 16);
    assert(pow2(32) == pow2(16) * pow2(16));
    assert(pow2(32) == 65536nat * 65536nat);
}

} // verus!
