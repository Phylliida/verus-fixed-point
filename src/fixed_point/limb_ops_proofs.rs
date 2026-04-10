///  Helper proof lemmas for limb_ops operations.
///
///  Extracted into its own module to keep these auxiliary lemmas out of
///  limb_ops::*'s Z3 context (which contains the heavy mul2 verification).

use vstd::prelude::*;
use super::limb_ops::{
    LIMB_BASE, LimbOps, limb_power, limbs_val, vec_val, sem_seq, valid_limbs,
    lemma_vec_val_split, lemma_vec_val_eq_from_sem_eq, lemma_vec_val_bounded,
};

verus! {

///  Updating one element of a Seq<T> changes vec_val by a multiple of limb_power(idx).
///  vec_val(s_post) == vec_val(s_pre) + (s_post[idx].sem() - s_pre[idx].sem()) * limb_power(idx).
pub proof fn lemma_vec_val_set_one<T: LimbOps>(
    s_pre: Seq<T>, s_post: Seq<T>, idx: int,
)
    requires
        s_pre.len() == s_post.len(),
        0 <= idx,
        idx < s_pre.len(),
        forall |k: int| 0 <= k < s_pre.len() && k != idx ==> s_pre[k] == s_post[k],
    ensures
        vec_val(s_post) == vec_val(s_pre)
            + (s_post[idx].sem() - s_pre[idx].sem()) * limb_power(idx as nat),
{
    lemma_vec_val_split::<T>(s_pre, idx as nat);
    lemma_vec_val_split::<T>(s_post, idx as nat);

    let lo_pre = s_pre.subrange(0, idx);
    let lo_post = s_post.subrange(0, idx);
    let hi_pre = s_pre.subrange(idx, s_pre.len() as int);
    let hi_post = s_post.subrange(idx, s_post.len() as int);

    // Lo parts are equal
    assert(lo_pre =~= lo_post);

    // Now split each hi part at index 1 to isolate s[idx]
    lemma_vec_val_split::<T>(hi_pre, 1);
    lemma_vec_val_split::<T>(hi_post, 1);

    let head_pre = hi_pre.subrange(0, 1);
    let head_post = hi_post.subrange(0, 1);
    let tail_pre = hi_pre.subrange(1, hi_pre.len() as int);
    let tail_post = hi_post.subrange(1, hi_post.len() as int);

    // Single-element vec_val
    reveal_with_fuel(limbs_val, 2);
    reveal_with_fuel(limb_power, 2);
    assert(head_pre.len() == 1);
    assert(head_post.len() == 1);
    assert(head_pre[0] == s_pre[idx]);
    assert(head_post[0] == s_post[idx]);
    assert(sem_seq(head_pre).len() == 1);
    assert(sem_seq(head_pre)[0] == s_pre[idx].sem());
    assert(sem_seq(head_pre).subrange(1, 1) =~= Seq::<int>::empty());
    assert(vec_val(head_pre) == s_pre[idx].sem());
    assert(sem_seq(head_post)[0] == s_post[idx].sem());
    assert(sem_seq(head_post).subrange(1, 1) =~= Seq::<int>::empty());
    assert(vec_val(head_post) == s_post[idx].sem());

    // Tail parts are equal
    assert forall |k: int| 0 <= k < tail_pre.len() implies tail_pre[k] == tail_post[k] by {
        assert(tail_pre[k] == hi_pre[k + 1]);
        assert(hi_pre[k + 1] == s_pre[idx + 1 + k]);
        assert(tail_post[k] == hi_post[k + 1]);
        assert(hi_post[k + 1] == s_post[idx + 1 + k]);
    }
    assert(tail_pre =~= tail_post);

    let p_idx = limb_power(idx as nat);
    let p_idx1 = limb_power((idx + 1) as nat);
    assert(p_idx1 == LIMB_BASE() * p_idx);
    assert(limb_power(1nat) == LIMB_BASE());

    assert(vec_val(s_post) == vec_val(s_pre)
        + (s_post[idx].sem() - s_pre[idx].sem()) * p_idx) by(nonlinear_arith)
        requires
            vec_val(s_pre) == vec_val(lo_pre) + vec_val(hi_pre) * p_idx,
            vec_val(s_post) == vec_val(lo_post) + vec_val(hi_post) * p_idx,
            vec_val(lo_pre) == vec_val(lo_post),
            vec_val(hi_pre) == vec_val(head_pre) + vec_val(tail_pre) * LIMB_BASE(),
            vec_val(hi_post) == vec_val(head_post) + vec_val(tail_post) * LIMB_BASE(),
            vec_val(head_pre) == s_pre[idx].sem(),
            vec_val(head_post) == s_post[idx].sem(),
            vec_val(tail_pre) == vec_val(tail_post);
}

///  Truncated product on Seq<T>: vec_val of the n-limb middle slice of the
///  2n-limb product equals ((a_val * b_val) / limb_power(frac_limbs)) % limb_power(n).
pub proof fn lemma_truncated_product_seq<T: LimbOps>(
    product: Seq<T>, truncated: Seq<T>,
    a_val: int, b_val: int,
    n: nat, frac_limbs: nat,
)
    requires
        product.len() == 2 * n,
        valid_limbs(product),
        vec_val(product) == a_val * b_val,
        truncated.len() == n,
        valid_limbs(truncated),
        forall |j: int| 0 <= j < n as int ==>
            (#[trigger] truncated[j]).sem() == product[(frac_limbs + j) as int].sem(),
        frac_limbs + n <= 2 * n,
        frac_limbs <= n,
        n > 0,
    ensures
        vec_val(truncated) == ((a_val * b_val) / limb_power(frac_limbs)) % limb_power(n),
{
    let scale = limb_power(frac_limbs);
    let P = limb_power(n);
    let ab = a_val * b_val;

    // Step 1: Split product at frac_limbs → lo + upper * scale
    lemma_vec_val_split::<T>(product, frac_limbs);
    let lo = vec_val(product.subrange(0, frac_limbs as int));
    let upper_seq = product.subrange(frac_limbs as int, product.len() as int);

    // Step 2: Split upper at n → mid + hi * P
    lemma_vec_val_split::<T>(upper_seq, n);
    let mid = vec_val(upper_seq.subrange(0, n as int));
    let hi = vec_val(upper_seq.subrange(n as int, upper_seq.len() as int));

    // Step 3: truncated == upper[0..n] semantically
    assert(truncated.len() == upper_seq.subrange(0, n as int).len());
    assert forall |j: int| 0 <= j < truncated.len()
        implies (#[trigger] truncated[j]).sem() == upper_seq.subrange(0, n as int)[j].sem() by {
        assert(upper_seq.subrange(0, n as int)[j] == upper_seq[j]);
        assert(upper_seq[j] == product[(frac_limbs as int) + j]);
    }
    lemma_vec_val_eq_from_sem_eq::<T>(truncated, upper_seq.subrange(0, n as int));
    assert(vec_val(truncated) == mid);

    // Step 4: Bounds on lo, mid, hi
    let lo_seq = product.subrange(0, frac_limbs as int);
    assert forall |j: int| 0 <= j < lo_seq.len()
        implies 0 <= (#[trigger] lo_seq[j]).sem() && lo_seq[j].sem() < LIMB_BASE() by {
        assert(lo_seq[j] == product[j]);
    }
    lemma_vec_val_bounded::<T>(lo_seq);
    assert(0 <= lo && lo < scale);
    lemma_vec_val_bounded::<T>(truncated);
    assert(0 <= mid && mid < P);
    let hi_seq = upper_seq.subrange(n as int, upper_seq.len() as int);
    assert forall |j: int| 0 <= j < hi_seq.len()
        implies 0 <= (#[trigger] hi_seq[j]).sem() && hi_seq[j].sem() < LIMB_BASE() by {
        assert(hi_seq[j] == upper_seq[j + n as int]);
        assert(upper_seq[j + n as int] == product[(frac_limbs as int) + j + n as int]);
    }
    lemma_vec_val_bounded::<T>(hi_seq);
    assert(hi >= 0);

    // Step 5: ab == lo + (mid + hi*P) * scale
    assert(ab == lo + vec_val(upper_seq) * scale);
    assert(vec_val(upper_seq) == mid + hi * P);
    assert(ab == lo + (mid + hi * P) * scale) by(nonlinear_arith)
        requires
            ab == lo + vec_val(upper_seq) * scale,
            vec_val(upper_seq) == mid + hi * P;

    // Step 6: ab % scale == lo
    assert(scale > 0) by {
        lemma_vec_val_bounded::<T>(lo_seq);
    }
    assert(ab % scale == lo) by {
        assert(ab == scale * (mid + hi * P) + lo) by(nonlinear_arith)
            requires ab == lo + (mid + hi * P) * scale;
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(mid + hi * P, lo, scale);
        vstd::arithmetic::div_mod::lemma_small_mod(lo as nat, scale as nat);
    };

    // Step 7: ab / scale == mid + hi * P
    assert(ab == scale * (mid + hi * P) + lo) by(nonlinear_arith)
        requires ab == lo + (mid + hi * P) * scale;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ab, scale);
    assert(ab / scale == mid + hi * P) by(nonlinear_arith)
        requires
            ab == scale * (ab / scale) + ab % scale,
            ab % scale == lo,
            ab == scale * (mid + hi * P) + lo,
            scale > 0;

    // Step 8: (mid + hi*P) % P == mid
    assert(P > 0);
    assert((mid + hi * P) % P == mid) by {
        assert(mid + hi * P == P * hi + mid) by(nonlinear_arith);
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(hi, mid, P);
        vstd::arithmetic::div_mod::lemma_small_mod(mid as nat, P as nat);
    };
}

///  Signed-magnitude value of a limb sequence with explicit sign.
pub open spec fn signed_val_of<T: LimbOps>(limbs: Seq<T>, sign_v: int) -> int {
    if sign_v == 0 { vec_val(limbs) } else { -vec_val(limbs) }
}

///  Seq-friendly correctness lemma for signed addition (mirrors
///  GenericFixedPoint::lemma_signed_add_correct, but operating on Seq<T>).
///  Given the intermediate values produced by add+sub+sub+select, proves
///  the 3-way modular disjunction connecting the result to the true sum.
pub proof fn lemma_signed_add_correct_seq<T: LimbOps>(
    a_seq: Seq<T>, a_sign_v: int,
    b_seq: Seq<T>, b_sign_v: int,
    sum: Seq<T>, carry_v: int,
    a_minus_b: Seq<T>, borrow_ab_v: int,
    b_minus_a: Seq<T>, borrow_ba_v: int,
    same_sign_v: int,
    out_seq: Seq<T>, out_sign_v: int,
    n: nat,
)
    requires
        a_seq.len() == n, b_seq.len() == n, sum.len() == n,
        a_minus_b.len() == n, b_minus_a.len() == n, out_seq.len() == n,
        valid_limbs(a_seq), valid_limbs(b_seq), valid_limbs(sum),
        valid_limbs(a_minus_b), valid_limbs(b_minus_a), valid_limbs(out_seq),
        a_sign_v == 0 || a_sign_v == 1,
        b_sign_v == 0 || b_sign_v == 1,
        carry_v == 0 || carry_v == 1,
        vec_val(sum) + carry_v * limb_power(n) == vec_val(a_seq) + vec_val(b_seq),
        borrow_ab_v == 0 || borrow_ab_v == 1,
        vec_val(a_minus_b) + vec_val(b_seq) == vec_val(a_seq) + borrow_ab_v * limb_power(n),
        borrow_ba_v == 0 || borrow_ba_v == 1,
        vec_val(b_minus_a) + vec_val(a_seq) == vec_val(b_seq) + borrow_ba_v * limb_power(n),
        same_sign_v == 0 || same_sign_v == 1,
        (a_sign_v == b_sign_v) <==> same_sign_v == 1,
        same_sign_v == 1 ==> vec_val(out_seq) == vec_val(sum),
        same_sign_v == 0 && borrow_ab_v == 0 ==> vec_val(out_seq) == vec_val(a_minus_b),
        same_sign_v == 0 && borrow_ab_v == 1 ==> vec_val(out_seq) == vec_val(b_minus_a),
        same_sign_v == 1 ==> out_sign_v == a_sign_v,
        same_sign_v == 0 && borrow_ab_v == 0 ==> out_sign_v == a_sign_v,
        same_sign_v == 0 && borrow_ab_v == 1 ==> out_sign_v == b_sign_v,
        out_sign_v == 0 || out_sign_v == 1,
    ensures
        signed_val_of(out_seq, out_sign_v)
            == signed_val_of(a_seq, a_sign_v) + signed_val_of(b_seq, b_sign_v)
        || (signed_val_of(out_seq, out_sign_v)
                == signed_val_of(a_seq, a_sign_v) + signed_val_of(b_seq, b_sign_v) - limb_power(n)
            && signed_val_of(a_seq, a_sign_v) + signed_val_of(b_seq, b_sign_v) >= limb_power(n))
        || (signed_val_of(out_seq, out_sign_v)
                == signed_val_of(a_seq, a_sign_v) + signed_val_of(b_seq, b_sign_v) + limb_power(n)
            && signed_val_of(a_seq, a_sign_v) + signed_val_of(b_seq, b_sign_v) <= -(limb_power(n) as int)),
{
    let va = vec_val(a_seq);
    let vb = vec_val(b_seq);
    let vo = vec_val(out_seq);
    let P = limb_power(n);
    let sa_signed = signed_val_of(a_seq, a_sign_v);
    let sb_signed = signed_val_of(b_seq, b_sign_v);
    let so_signed = signed_val_of(out_seq, out_sign_v);
    let true_sum = sa_signed + sb_signed;

    lemma_vec_val_bounded::<T>(a_seq);
    lemma_vec_val_bounded::<T>(b_seq);
    lemma_vec_val_bounded::<T>(sum);
    lemma_vec_val_bounded::<T>(a_minus_b);
    lemma_vec_val_bounded::<T>(b_minus_a);
    lemma_vec_val_bounded::<T>(out_seq);

    if same_sign_v == 1 {
        let sv = vec_val(sum);
        let cy = carry_v;
        assert(vo == sv);
        assert(out_sign_v == a_sign_v);
        if a_sign_v == 0 {
            assert(so_signed == sv);
            assert(true_sum == va + vb);
            if cy == 0 {
                assert(sv == va + vb);
                assert(so_signed == true_sum);
            } else {
                assert(sv + P == va + vb) by(nonlinear_arith)
                    requires sv + cy * P == va + vb, cy == 1;
                assert(so_signed == true_sum - P);
                assert(true_sum >= P);
            }
        } else {
            assert(so_signed == -sv);
            assert(true_sum == -va - vb);
            if cy == 0 {
                assert(sv == va + vb);
                assert(so_signed == true_sum);
            } else {
                assert(sv + P == va + vb) by(nonlinear_arith)
                    requires sv + cy * P == va + vb, cy == 1;
                assert(va + vb >= P) by(nonlinear_arith)
                    requires sv + P == va + vb, sv >= 0;
                assert(true_sum <= -P);
                assert(so_signed == true_sum + P);
            }
        }
    } else {
        let amv = vec_val(a_minus_b);
        let bmv = vec_val(b_minus_a);
        assert(a_sign_v != b_sign_v);

        if borrow_ab_v == 0 {
            assert(amv == va - vb) by(nonlinear_arith)
                requires
                    amv + vb == va + borrow_ab_v * P,
                    borrow_ab_v == 0;
            assert(vo == amv);
            assert(out_sign_v == a_sign_v);
            assert(va >= vb);
            if a_sign_v == 0 {
                assert(sa_signed == va);
                assert(sb_signed == -vb);
                assert(true_sum == va - vb);
                assert(so_signed == amv);
                assert(so_signed == true_sum);
            } else {
                assert(sa_signed == -va);
                assert(sb_signed == vb);
                assert(true_sum == -va + vb);
                assert(so_signed == -amv);
                assert(so_signed == -(va - vb));
                assert(so_signed == true_sum);
            }
        } else {
            assert(va < vb) by {
                assert(0 <= amv);
                assert(amv + vb == va + P);
                assert(amv < P);
            }
            assert(borrow_ba_v == 0) by {
                if borrow_ba_v == 1 {
                    assert(bmv + va == vb + P);
                    assert(bmv >= P) by(nonlinear_arith)
                        requires bmv + va == vb + P, va < vb;
                    assert(false);
                }
            }
            assert(bmv == vb - va) by(nonlinear_arith)
                requires
                    bmv + va == vb + borrow_ba_v * P,
                    borrow_ba_v == 0;
            assert(vo == bmv);
            assert(out_sign_v == b_sign_v);
            if b_sign_v == 0 {
                assert(sa_signed == -va);
                assert(sb_signed == vb);
                assert(true_sum == -va + vb);
                assert(so_signed == bmv);
                assert(so_signed == vb - va);
                assert(so_signed == true_sum);
            } else {
                assert(sa_signed == va);
                assert(sb_signed == -vb);
                assert(true_sum == va - vb);
                assert(so_signed == -bmv);
                assert(so_signed == -(vb - va));
                assert(so_signed == va - vb);
                assert(so_signed == true_sum);
            }
        }
    }
}

} //  verus!
