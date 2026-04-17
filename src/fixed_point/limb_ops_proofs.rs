///  Helper proof lemmas for limb_ops operations.
///
///  Extracted into its own module to keep these auxiliary lemmas out of
///  limb_ops::*'s Z3 context (which contains the heavy mul2 verification).

use vstd::prelude::*;
use super::limb_ops::{
    LIMB_BASE, LimbOps, limb_power, limbs_val, vec_val, sem_seq, valid_limbs,
    lemma_vec_val_split, lemma_vec_val_eq_from_sem_eq, lemma_vec_val_bounded,
    lemma_limb_power_add,
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

/// Prove that the Karatsuba z1 overflow is 0 or 1.
/// z1_full - z0 - z2 = cross terms (non-negative, < 2*P).
/// The n-limb sub_borrow gives z1_n + (z1_overflow - bw1 - bw2) * P = cross.
/// Since 0 <= cross < 2*P and 0 <= z1_n < P, the overflow is 0 or 1.
pub proof fn lemma_karatsuba_z1_overflow_bound(
    z1_full: int,
    z0: int, z2: int,
    z1_overflow: int, bw1: int, bw2: int,
    z1_n: int,
    P: int,
)
    requires
        P > 0,
        z1_full >= z0 + z2,  // from Karatsuba identity: cross terms >= 0
        z1_full < z0 + z2 + 2 * P,  // cross < 2*P (each half < P)
        0 <= z0, 0 <= z2,
        // sub_borrow step 1: z1_full_n - z0 = z1_tmp + (bw1) * P (mod P representation)
        // sub_borrow step 2: z1_tmp - z2 = z1_n + (bw2) * P
        // Combined: z1_full_n - z0 - z2 = z1_n + (bw1 + bw2) * P (mod)
        // True z1: z1_full - z0 - z2 = z1_n + (z1_overflow - bw1 - bw2) * P
        z1_n + (z1_overflow - bw1 - bw2) * P == z1_full - z0 - z2,
        0 <= z1_n, z1_n < P,
        bw1 == 0 || bw1 == 1,
        bw2 == 0 || bw2 == 1,
        z1_overflow >= 0, z1_overflow <= 3,
    ensures
        z1_overflow - bw1 - bw2 == 0 || z1_overflow - bw1 - bw2 == 1,
{
    let ov = z1_overflow - bw1 - bw2;
    let cross = z1_full - z0 - z2;
    // cross = z1_n + ov * P (from the combined sub_borrow equation)
    // 0 <= cross (from z1_full >= z0 + z2)
    // cross < 2*P (from z1_full < z0 + z2 + 2*P)
    // 0 <= z1_n < P
    // ov * P = cross - z1_n, with 0 <= cross < 2*P and 0 <= z1_n < P
    // => -(P-1) < ov*P < 2*P => 0 <= ov <= 1
    assert(ov >= 0 && ov < 2) by(nonlinear_arith)
        requires z1_n + ov * P == cross,
                 0 <= z1_n, z1_n < P,
                 cross >= 0, cross < 2 * P,
                 z1_full >= z0 + z2,
                 z1_full < z0 + z2 + 2 * P,
                 cross == z1_full - z0 - z2,
                 P > 0;
}

/// Establish that z1_full = (a_lo+a_hi)(b_lo+b_hi) from the step 3/4/4b value equations,
/// and derive the bounds needed for lemma_karatsuba_z1_overflow_bound.
pub proof fn lemma_karatsuba_z1_full_bounds(
    a_sum_val: int, b_sum_val: int,
    asum_carry: int, bsum_carry: int,
    a_lo_val: int, a_hi_val: int,
    b_lo_val: int, b_hi_val: int,
    schoolbook_val: int,
    z1_full_val: int,
    z0_val: int, z2_val: int,
    B: int, P: int,
)
    requires
        // Step 3: a_sum + carry*B = a_lo + a_hi
        a_sum_val + asum_carry * B == a_lo_val + a_hi_val,
        b_sum_val + bsum_carry * B == b_lo_val + b_hi_val,
        asum_carry == 0 || asum_carry == 1,
        bsum_carry == 0 || bsum_carry == 1,
        // Step 4: schoolbook = a_sum * b_sum
        schoolbook_val == a_sum_val * b_sum_val,
        // Step 4b: z1_full = (a_sum + ca*B)(b_sum + cb*B)
        // This is what the carry correction computes
        z1_full_val == schoolbook_val
            + asum_carry * B * b_sum_val
            + bsum_carry * B * a_sum_val
            + asum_carry * bsum_carry * B * B,
        // Input bounds
        0 <= a_lo_val, a_lo_val < B,
        0 <= a_hi_val, a_hi_val < B,
        0 <= b_lo_val, b_lo_val < B,
        0 <= b_hi_val, b_hi_val < B,
        0 <= a_sum_val, a_sum_val < B,
        0 <= b_sum_val, b_sum_val < B,
        // z0 = a_lo*b_lo, z2 = a_hi*b_hi
        z0_val == a_lo_val * b_lo_val,
        z2_val == a_hi_val * b_hi_val,
        // P = B^2
        P == B * B, B > 0,
    ensures
        z1_full_val == (a_lo_val + a_hi_val) * (b_lo_val + b_hi_val),
        z1_full_val >= z0_val + z2_val,
        z1_full_val < z0_val + z2_val + 2 * P,
{
    // z1_full = (a_sum + ca*B)(b_sum + cb*B) = (a_lo + a_hi)(b_lo + b_hi)
    let A = a_sum_val + asum_carry * B;
    let C = b_sum_val + bsum_carry * B;
    assert(A == a_lo_val + a_hi_val);
    assert(C == b_lo_val + b_hi_val);
    // Two-step distributive expansion: A*C = (a_sum + ca*B) * C
    //   = a_sum*C + ca*B*C
    assert(A * C == a_sum_val * C + asum_carry * B * C) by(nonlinear_arith)
        requires A == a_sum_val + asum_carry * B;
    // Now expand each: a_sum*C = a_sum*b_sum + a_sum*cb*B
    //                  ca*B*C = ca*B*b_sum + ca*cb*B*B
    assert(a_sum_val * C == a_sum_val * b_sum_val + a_sum_val * bsum_carry * B) by(nonlinear_arith)
        requires C == b_sum_val + bsum_carry * B;
    assert(asum_carry * B * C == asum_carry * B * b_sum_val + asum_carry * bsum_carry * B * B) by(nonlinear_arith)
        requires C == b_sum_val + bsum_carry * B;
    // z1_full_val = schoolbook + corrections = a_sum*b_sum + ca*B*b_sum + cb*B*a_sum + ca*cb*B²
    // = a_sum*C + ca*B*C = A*C (from above)
    assert(z1_full_val == a_sum_val * C + asum_carry * B * C) by(nonlinear_arith)
        requires
            z1_full_val == schoolbook_val
                + asum_carry * B * b_sum_val
                + bsum_carry * B * a_sum_val
                + asum_carry * bsum_carry * B * B,
            schoolbook_val == a_sum_val * b_sum_val,
            a_sum_val * C == a_sum_val * b_sum_val + a_sum_val * bsum_carry * B,
            asum_carry * B * C == asum_carry * B * b_sum_val + asum_carry * bsum_carry * B * B;
    assert(z1_full_val == A * C);
    assert(z1_full_val == (a_lo_val + a_hi_val) * (b_lo_val + b_hi_val));

    // z1_full - z0 - z2 = cross terms >= 0
    // (a_lo+a_hi)(b_lo+b_hi) - a_lo*b_lo - a_hi*b_hi = a_lo*b_hi + a_hi*b_lo >= 0
    assert(z1_full_val >= z0_val + z2_val) by(nonlinear_arith)
        requires
            z1_full_val == (a_lo_val + a_hi_val) * (b_lo_val + b_hi_val),
            z0_val == a_lo_val * b_lo_val,
            z2_val == a_hi_val * b_hi_val,
            a_lo_val >= 0, a_hi_val >= 0, b_lo_val >= 0, b_hi_val >= 0;

    // cross = a_lo*b_hi + a_hi*b_lo < 2*B^2 = 2*P
    // Break into: cross = z1_full - z0 - z2, each cross term < B²
    let cross = z1_full_val - z0_val - z2_val;
    // (a+c)(b+d) = ab + ad + cb + cd. So (a+c)(b+d) - ab - cd = ad + cb.
    assert((a_lo_val + a_hi_val) * (b_lo_val + b_hi_val)
        == a_lo_val * b_lo_val + a_lo_val * b_hi_val + a_hi_val * b_lo_val + a_hi_val * b_hi_val)
        by(nonlinear_arith);
    assert(cross == a_lo_val * b_hi_val + a_hi_val * b_lo_val);
    assert(a_lo_val * b_hi_val < B * B) by(nonlinear_arith)
        requires a_lo_val < B, b_hi_val < B, a_lo_val >= 0, b_hi_val >= 0, B > 0;
    assert(a_hi_val * b_lo_val < B * B) by(nonlinear_arith)
        requires a_hi_val < B, b_lo_val < B, a_hi_val >= 0, b_lo_val >= 0, B > 0;
    assert(cross < 2 * P) by(nonlinear_arith)
        requires cross == a_lo_val * b_hi_val + a_hi_val * b_lo_val,
                 a_lo_val * b_hi_val < B * B, a_hi_val * b_lo_val < B * B,
                 P == B * B;
}

/// Carry correction for Karatsuba: adds ca*b_sum + cb*a_sum at offset half,
/// returns z1_overflow = cc1 + cc2 + ca*cb.
///
/// Postcondition value equation (the key connection):
///   z1_full_n_new + z1_overflow * P == schoolbook_val + ca*B*b_sum_val + cb*B*a_sum_val + ca*cb*B²
pub fn karatsuba_carry_correct<T: LimbOps>(
    scratch: &mut Vec<T>,
    scratch_off: usize,
    a_sum_vec: &[T],
    a_sum_off: usize,
    b_sum_vec: &[T],
    b_sum_off: usize,
    asum_carry: &T,
    bsum_carry: &T,
    n: usize,
    half: usize,
) -> (z1_overflow: T)
    requires
        half == n / 2, n >= 4, n <= 0x1FFF_FFFF, n % 2 == 0,
        old(scratch)@.len() >= scratch_off + 2 * n,
        scratch_off + 2 * n < usize::MAX,
        a_sum_vec@.len() >= a_sum_off + half, b_sum_vec@.len() >= b_sum_off + half,
        a_sum_off + half < usize::MAX, b_sum_off + half < usize::MAX,
        valid_limbs(a_sum_vec@), valid_limbs(b_sum_vec@),
        asum_carry.sem() == 0 || asum_carry.sem() == 1,
        bsum_carry.sem() == 0 || bsum_carry.sem() == 1,
        forall |j: int| 0 <= j < n as int
            ==> 0 <= (#[trigger] old(scratch)@[(scratch_off as int + j)]).sem() < LIMB_BASE(),
    ensures
        scratch@.len() == old(scratch)@.len(),
        forall |j: int| 0 <= j < n as int
            ==> 0 <= (#[trigger] scratch@[(scratch_off as int + j)]).sem() < LIMB_BASE(),
        // Frame: only scratch[scratch_off..scratch_off+n] modified
        forall |j: int| 0 <= j < scratch@.len() && !(scratch_off as int <= j < (scratch_off + n) as int)
            ==> scratch@[j] == old(scratch)@[j],
        // z1_overflow bounds
        0 <= z1_overflow.sem(), z1_overflow.sem() <= 3,
        // Value equation: new = old + carry corrections, with overflow at position n
        vec_val(scratch@.subrange(scratch_off as int, (scratch_off + n) as int))
            + z1_overflow.sem() * limb_power(n as nat)
            == vec_val(old(scratch)@.subrange(scratch_off as int, (scratch_off + n) as int))
             + asum_carry.sem() * limb_power(half as nat) * vec_val(b_sum_vec@.subrange(b_sum_off as int, (b_sum_off + half) as int))
             + bsum_carry.sem() * limb_power(half as nat) * vec_val(a_sum_vec@.subrange(a_sum_off as int, (a_sum_off + half) as int))
             + asum_carry.sem() * bsum_carry.sem() * limb_power(n as nat),
{
    let ghost old_scratch = scratch@;
    let ghost S = scratch_off as int;

    // cc1 loop: add asum_carry * b_sum at offset half
    let mut cc1 = T::zero_val();
    for k in 0..half
        invariant half == n / 2, n >= 4, n <= 0x1FFF_FFFF,
            scratch@.len() == old_scratch.len(), old_scratch.len() >= scratch_off + 2 * n,
            scratch_off + 2 * n < usize::MAX, S == scratch_off as int,
            asum_carry.sem() == 0 || asum_carry.sem() == 1,
            cc1.sem() == 0 || cc1.sem() == 1,
            a_sum_vec@.len() >= a_sum_off + half, b_sum_vec@.len() >= b_sum_off + half,
            a_sum_off + half < usize::MAX, b_sum_off + half < usize::MAX,
            valid_limbs(a_sum_vec@), valid_limbs(b_sum_vec@),
            forall |j: int| 0 <= j < n as int
                ==> 0 <= (#[trigger] scratch@[(S + j)]).sem() < LIMB_BASE(),
            // Frame: only positions half..half+k modified
            forall |j: int| 0 <= j < old_scratch.len() && !(S + half as int <= j < S + half as int + k)
                ==> scratch@[j] == old_scratch[j],
            // Value equation for cc1 correction
            vec_val(scratch@.subrange(S, S + n as int))
                + cc1.sem() * limb_power((half + k) as nat)
                == vec_val(old_scratch.subrange(S, S + n as int))
                    + asum_carry.sem() * limb_power(half as nat) * vec_val(b_sum_vec@.subrange(b_sum_off as int, (b_sum_off + k) as int)),
    {
        let addend = T::select_limb(asum_carry, T::zero_val(), b_sum_vec[b_sum_off + k].clone_limb());
        let ghost hk = (half + k) as int;
        let ghost sv = scratch@[(S + hk)].sem();
        proof { assert(0 <= hk && hk < n as int); }
        let ghost region_pre = scratch@.subrange(S, S + n as int);
        let (s, nc) = scratch[scratch_off + half + k].add3(&addend, &cc1);
        proof {
            let x = sv + addend.sem() + cc1.sem();
            assert(x < 2 * LIMB_BASE());
            assert(nc.sem() <= 1) by(nonlinear_arith)
                requires nc.sem() == x / LIMB_BASE(), x >= 0,
                         x < 2 * LIMB_BASE(), LIMB_BASE() > 0;
        }
        scratch.set(scratch_off + half + k, s);
        proof {
            let region_post = scratch@.subrange(S, S + n as int);
            assert forall |j: int| 0 <= j < region_pre.len() && j != hk
                implies region_pre[j] == region_post[j]
            by { assert(region_post[j] == scratch@[(S + j)]); }
            lemma_vec_val_set_one::<T>(region_pre, region_post, hk);

            // Extend b_sum: vec_val(b[0..k+1]) = vec_val(b[0..k]) + b[k].sem() * P(k)
            lemma_vec_val_split::<T>(b_sum_vec@.subrange(b_sum_off as int, (b_sum_off + k + 1) as int), k as nat);
            let b_tail = b_sum_vec@.subrange((b_sum_off + k) as int, (b_sum_off + k) as int + 1);
            reveal_with_fuel(limbs_val, 2);
            assert(sem_seq(b_tail)[0] == b_sum_vec@[(b_sum_off + k) as int].sem());
            assert(sem_seq(b_tail).subrange(1, 1) =~= Seq::<int>::empty());
            assert(vec_val(b_tail) == b_sum_vec@[(b_sum_off + k) as int].sem());
            assert(b_sum_vec@.subrange(b_sum_off as int, (b_sum_off + k + 1) as int).subrange(0, k as int) =~= b_sum_vec@.subrange(b_sum_off as int, (b_sum_off + k) as int));

            // addend.sem() == asum_carry * b_sum_vec[k] (from select_limb)
            // s.sem() + nc.sem()*BASE = sv + addend + cc1
            // set_one: vec_val(post) = vec_val(pre) + (s - sv) * P(hk)
            let p_hk = limb_power(hk as nat);
            reveal_with_fuel(limb_power, 2);
            let p_hk1 = limb_power((hk + 1) as nat);
            assert(p_hk1 == LIMB_BASE() * p_hk);
            let p_k = limb_power(k as nat);
            lemma_limb_power_add(half as nat, k as nat);
            assert(p_hk == limb_power(half as nat) * p_k);

            let bv_k = vec_val(b_sum_vec@.subrange(b_sum_off as int, (b_sum_off + k) as int));
            let bv_k1 = vec_val(b_sum_vec@.subrange(b_sum_off as int, (b_sum_off + k + 1) as int));
            let bk = b_sum_vec@[(b_sum_off + k) as int].sem();
            let v_old = vec_val(old_scratch.subrange(S, S + n as int));
            let h = limb_power(half as nat);
            let ac = asum_carry.sem();
            assert(
                vec_val(region_post) + nc.sem() * p_hk1
                == v_old + ac * h * bv_k1
            ) by(nonlinear_arith)
                requires
                    vec_val(region_pre) + cc1.sem() * p_hk == v_old + ac * h * bv_k,
                    vec_val(region_post) == vec_val(region_pre) + (s.sem() - sv) * p_hk,
                    s.sem() + nc.sem() * LIMB_BASE() == sv + addend.sem() + cc1.sem(),
                    addend.sem() == if ac == 0 { 0int } else { bk },
                    bv_k1 == bv_k + bk * p_k,
                    p_hk == h * p_k,
                    p_hk1 == LIMB_BASE() * p_hk,
                    ac == 0 || ac == 1;
        }
        cc1 = nc;
    }

    let ghost scratch_post_cc1 = scratch@;

    // cc2 loop: add bsum_carry * a_sum at offset half
    let mut cc2 = T::zero_val();
    for k in 0..half
        invariant half == n / 2, n >= 4, n <= 0x1FFF_FFFF,
            scratch@.len() == old_scratch.len(), old_scratch.len() >= scratch_off + 2 * n,
            scratch_off + 2 * n < usize::MAX, S == scratch_off as int,
            bsum_carry.sem() == 0 || bsum_carry.sem() == 1,
            cc2.sem() == 0 || cc2.sem() == 1,
            a_sum_vec@.len() >= a_sum_off + half, b_sum_vec@.len() >= b_sum_off + half,
            a_sum_off + half < usize::MAX, b_sum_off + half < usize::MAX,
            valid_limbs(a_sum_vec@), valid_limbs(b_sum_vec@),
            forall |j: int| 0 <= j < n as int
                ==> 0 <= (#[trigger] scratch@[(S + j)]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < old_scratch.len() && !(S + half as int <= j < S + half as int + k)
                ==> scratch@[j] == scratch_post_cc1[j],
            vec_val(scratch@.subrange(S, S + n as int))
                + cc2.sem() * limb_power((half + k) as nat)
                == vec_val(scratch_post_cc1.subrange(S, S + n as int))
                    + bsum_carry.sem() * limb_power(half as nat) * vec_val(a_sum_vec@.subrange(a_sum_off as int, (a_sum_off + k) as int)),
    {
        let addend = T::select_limb(bsum_carry, T::zero_val(), a_sum_vec[a_sum_off + k].clone_limb());
        let ghost hk = (half + k) as int;
        let ghost sv = scratch@[(S + hk)].sem();
        proof { assert(0 <= hk && hk < n as int); }
        let ghost region_pre = scratch@.subrange(S, S + n as int);
        let (s, nc) = scratch[scratch_off + half + k].add3(&addend, &cc2);
        proof {
            let x = sv + addend.sem() + cc2.sem();
            assert(x < 2 * LIMB_BASE());
            assert(nc.sem() <= 1) by(nonlinear_arith)
                requires nc.sem() == x / LIMB_BASE(), x >= 0,
                         x < 2 * LIMB_BASE(), LIMB_BASE() > 0;
        }
        scratch.set(scratch_off + half + k, s);
        proof {
            let region_post = scratch@.subrange(S, S + n as int);
            assert forall |j: int| 0 <= j < region_pre.len() && j != hk
                implies region_pre[j] == region_post[j]
            by { assert(region_post[j] == scratch@[(S + j)]); }
            lemma_vec_val_set_one::<T>(region_pre, region_post, hk);

            lemma_vec_val_split::<T>(a_sum_vec@.subrange(a_sum_off as int, (a_sum_off + k + 1) as int), k as nat);
            let a_tail = a_sum_vec@.subrange((a_sum_off + k) as int, (a_sum_off + k) as int + 1);
            reveal_with_fuel(limbs_val, 2);
            assert(vec_val(a_tail) == a_sum_vec@[(a_sum_off + k) as int].sem());
            assert(a_sum_vec@.subrange(a_sum_off as int, (a_sum_off + k + 1) as int).subrange(0, k as int) =~= a_sum_vec@.subrange(a_sum_off as int, (a_sum_off + k) as int));

            let p_hk = limb_power(hk as nat);
            reveal_with_fuel(limb_power, 2);
            let p_hk1 = limb_power((hk + 1) as nat);
            assert(p_hk1 == LIMB_BASE() * p_hk);
            let p_k = limb_power(k as nat);
            lemma_limb_power_add(half as nat, k as nat);

            let av_k = vec_val(a_sum_vec@.subrange(a_sum_off as int, (a_sum_off + k) as int));
            let av_k1 = vec_val(a_sum_vec@.subrange(a_sum_off as int, (a_sum_off + k + 1) as int));
            let ak = a_sum_vec@[(a_sum_off + k) as int].sem();
            let v_old2 = vec_val(scratch_post_cc1.subrange(S, S + n as int));
            let h = limb_power(half as nat);
            let bc = bsum_carry.sem();
            assert(
                vec_val(region_post) + nc.sem() * p_hk1
                == v_old2 + bc * h * av_k1
            ) by(nonlinear_arith)
                requires
                    vec_val(region_pre) + cc2.sem() * p_hk == v_old2 + bc * h * av_k,
                    vec_val(region_post) == vec_val(region_pre) + (s.sem() - sv) * p_hk,
                    s.sem() + nc.sem() * LIMB_BASE() == sv + addend.sem() + cc2.sem(),
                    addend.sem() == if bc == 0 { 0int } else { ak },
                    av_k1 == av_k + ak * p_k,
                    p_hk == h * p_k,
                    p_hk1 == LIMB_BASE() * p_hk,
                    bc == 0 || bc == 1;
        }
        cc2 = nc;
    }

    // z1_overflow = cc1 + cc2 + ca*cb
    let (ca_cb, _) = asum_carry.mul2(bsum_carry);
    let (temp_ov, _) = cc1.add3(&cc2, &T::zero_val());
    let (z1_overflow, _) = temp_ov.add3(&ca_cb, &T::zero_val());

    proof {
        // Combine cc1 and cc2 value equations
        // cc1 at end: vec_val(post_cc1) + cc1*P(n) = vec_val(old) + ca*B*vec_val(b_sum)
        assert(b_sum_vec@.subrange(b_sum_off as int, (b_sum_off + half) as int).len() == half as int);
        assert(a_sum_vec@.subrange(a_sum_off as int, (a_sum_off + half) as int).len() == half as int);
        // cc2 at end: vec_val(final) + cc2*P(n) = vec_val(post_cc1) + cb*B*vec_val(a_sum)
        // Combined: vec_val(final) + (cc1+cc2)*P(n) = vec_val(old) + ca*B*b_sum + cb*B*a_sum
        // z1_overflow = cc1 + cc2 + ca*cb
        // vec_val(final) + z1_overflow*P = vec_val(old) + ca*B*b_sum + cb*B*a_sum + ca*cb*P

        // z1_overflow bounds
        assert(LIMB_BASE() > 3) by {
            reveal_with_fuel(limb_power, 2);
            use crate::fixed_point::limbs::limb_base;
        }
        let ghost ca_v = asum_carry.sem();
        let ghost cb_v = bsum_carry.sem();
        assert(ca_cb.sem() == ca_v * cb_v) by(nonlinear_arith)
            requires ca_cb.sem() == (ca_v * cb_v) % LIMB_BASE(),
                     ca_v <= 1, cb_v <= 1, ca_v >= 0, cb_v >= 0, LIMB_BASE() > 1;
        assert(temp_ov.sem() == cc1.sem() + cc2.sem()) by(nonlinear_arith)
            requires temp_ov.sem() == (cc1.sem() + cc2.sem() + 0) % LIMB_BASE(),
                     cc1.sem() <= 1, cc2.sem() <= 1, cc1.sem() >= 0, cc2.sem() >= 0, LIMB_BASE() > 3;
        assert(z1_overflow.sem() == cc1.sem() + cc2.sem() + ca_v * cb_v) by(nonlinear_arith)
            requires z1_overflow.sem() == (temp_ov.sem() + ca_cb.sem() + 0) % LIMB_BASE(),
                     temp_ov.sem() == cc1.sem() + cc2.sem(),
                     ca_cb.sem() == ca_v * cb_v,
                     cc1.sem() <= 1, cc2.sem() <= 1, ca_v * cb_v <= 1,
                     cc1.sem() >= 0, cc2.sem() >= 0, ca_v * cb_v >= 0, LIMB_BASE() > 3;
        assert(0 <= z1_overflow.sem() && z1_overflow.sem() <= 3);

        let P = limb_power(n as nat);
        assert(n == 2 * half);
        lemma_limb_power_add(half as nat, half as nat);
        // limb_power(half + half) == limb_power(half) * limb_power(half)
        // and half + half == n, so P == limb_power(n) == limb_power(half)²

        // Final value equation combining cc1 and cc2
        assert(
            vec_val(scratch@.subrange(S, S + n as int))
                + z1_overflow.sem() * P
            == vec_val(old_scratch.subrange(S, S + n as int))
                + asum_carry.sem() * limb_power(half as nat) * vec_val(b_sum_vec@.subrange(b_sum_off as int, (b_sum_off + half) as int))
                + bsum_carry.sem() * limb_power(half as nat) * vec_val(a_sum_vec@.subrange(a_sum_off as int, (a_sum_off + half) as int))
                + asum_carry.sem() * bsum_carry.sem() * P
        ) by(nonlinear_arith)
            requires
                // cc1 equation at k=half
                vec_val(scratch_post_cc1.subrange(S, S + n as int))
                    + cc1.sem() * P
                    == vec_val(old_scratch.subrange(S, S + n as int))
                        + asum_carry.sem() * limb_power(half as nat) * vec_val(b_sum_vec@.subrange(b_sum_off as int, (b_sum_off + half) as int)),
                // cc2 equation at k=half
                vec_val(scratch@.subrange(S, S + n as int))
                    + cc2.sem() * P
                    == vec_val(scratch_post_cc1.subrange(S, S + n as int))
                        + bsum_carry.sem() * limb_power(half as nat) * vec_val(a_sum_vec@.subrange(a_sum_off as int, (a_sum_off + half) as int)),
                // overflow decomposition
                z1_overflow.sem() == cc1.sem() + cc2.sem() + ca_cb.sem(),
                ca_cb.sem() == asum_carry.sem() * bsum_carry.sem(),
                P == limb_power(half as nat) * limb_power(half as nat);
    }
    z1_overflow
}

/// Combined helper: establish z1_final_overflow == 0 || 1 from all intermediate values.
/// Chains lemma_karatsuba_z1_full_bounds + lemma_karatsuba_z1_overflow_bound + sub_borrow unwrapping.
pub proof fn lemma_karatsuba_overflow_chain(
    // Step 3 value equations
    a_sum_val: int, b_sum_val: int,
    asum_carry_v: int, bsum_carry_v: int,
    a_lo_v: int, a_hi_v: int, b_lo_v: int, b_hi_v: int,
    // Step 4
    schoolbook_val: int,
    // Step 4b
    z1_full_val: int, z1_full_n_val: int, z1_overflow_v: int,
    // Step 5
    z0_val: int, z2_val: int,
    scratch_post_sub1_val: int,
    borrow1_v: int, borrow2_v: int,
    z1_n: int,
    // Sub_borrow results
    temp_ov2_v: int, z1_final_overflow_v: int,
    // Constants
    B: int, P: int,
)
    requires
        // Step 3
        a_sum_val + asum_carry_v * B == a_lo_v + a_hi_v,
        b_sum_val + bsum_carry_v * B == b_lo_v + b_hi_v,
        asum_carry_v == 0 || asum_carry_v == 1,
        bsum_carry_v == 0 || bsum_carry_v == 1,
        // Step 4
        schoolbook_val == a_sum_val * b_sum_val,
        // Step 4b
        z1_full_val == z1_full_n_val + z1_overflow_v * P,
        z1_full_n_val + z1_overflow_v * P == schoolbook_val
            + asum_carry_v * B * b_sum_val
            + bsum_carry_v * B * a_sum_val
            + asum_carry_v * bsum_carry_v * B * B,
        0 <= z1_overflow_v, z1_overflow_v <= 3,
        // Input bounds
        0 <= a_lo_v, a_lo_v < B, 0 <= a_hi_v, a_hi_v < B,
        0 <= b_lo_v, b_lo_v < B, 0 <= b_hi_v, b_hi_v < B,
        0 <= a_sum_val, a_sum_val < B, 0 <= b_sum_val, b_sum_val < B,
        // z0/z2
        z0_val == a_lo_v * b_lo_v, z2_val == a_hi_v * b_hi_v,
        // Sub_borrow value equations
        scratch_post_sub1_val == z1_full_n_val - z0_val + borrow1_v * P,
        z1_n == scratch_post_sub1_val - z2_val + borrow2_v * P,
        borrow1_v == 0 || borrow1_v == 1,
        borrow2_v == 0 || borrow2_v == 1,
        0 <= z1_n, z1_n < P,
        // Sub_borrow on overflow
        temp_ov2_v == (z1_overflow_v - borrow1_v - 0 + LIMB_BASE()) % LIMB_BASE(),
        z1_final_overflow_v == (temp_ov2_v - borrow2_v - 0 + LIMB_BASE()) % LIMB_BASE(),
        // Constants
        P == B * B, B > 0, LIMB_BASE() > 3,
    ensures
        z1_final_overflow_v == 0 || z1_final_overflow_v == 1,
        // Value equation: z1_n + z1_final_overflow * P = z1_full - z0 - z2
        z1_n + z1_final_overflow_v * P == z1_full_val - z0_val - z2_val,
        // z1_full = (a_lo+a_hi)(b_lo+b_hi)
        z1_full_val == (a_lo_v + a_hi_v) * (b_lo_v + b_hi_v),
{
    // Step A: z1_full bounds
    lemma_karatsuba_z1_full_bounds(
        a_sum_val, b_sum_val,
        asum_carry_v, bsum_carry_v,
        a_lo_v, a_hi_v, b_lo_v, b_hi_v,
        schoolbook_val, z1_full_val, z0_val, z2_val,
        B, P,
    );
    // → z1_full >= z0+z2, z1_full < z0+z2+2P

    // Step B: combined sub_borrow value equation
    assert(z1_n + (z1_overflow_v - borrow1_v - borrow2_v) * P
        == z1_full_val - z0_val - z2_val) by(nonlinear_arith)
        requires
            scratch_post_sub1_val == z1_full_n_val - z0_val + borrow1_v * P,
            z1_n == scratch_post_sub1_val - z2_val + borrow2_v * P,
            z1_full_val == z1_full_n_val + z1_overflow_v * P;

    // Step C: overflow bound
    lemma_karatsuba_z1_overflow_bound(
        z1_full_val, z0_val, z2_val,
        z1_overflow_v, borrow1_v, borrow2_v,
        z1_n, P,
    );
    // → ov_diff = z1_overflow_v - borrow1_v - borrow2_v is 0 or 1
    let ov_diff = z1_overflow_v - borrow1_v - borrow2_v;
    assert(ov_diff == 0 || ov_diff == 1);
    assert(ov_diff >= 0);

    // Step D: sub_borrow unwrapping
    assert(z1_overflow_v >= borrow1_v + borrow2_v);
    assert(z1_overflow_v - borrow1_v >= 0);
    assert(z1_overflow_v - borrow1_v <= 3);
    assert(temp_ov2_v == z1_overflow_v - borrow1_v) by(nonlinear_arith)
        requires
            temp_ov2_v == (z1_overflow_v - borrow1_v + LIMB_BASE()) % LIMB_BASE(),
            z1_overflow_v - borrow1_v >= 0,
            z1_overflow_v - borrow1_v <= 3, LIMB_BASE() > 3;
    assert(temp_ov2_v >= borrow2_v);
    assert(temp_ov2_v <= 3);
    assert(temp_ov2_v - borrow2_v >= 0);
    assert(temp_ov2_v - borrow2_v < LIMB_BASE()) by(nonlinear_arith)
        requires temp_ov2_v <= 3, borrow2_v >= 0, LIMB_BASE() > 3;
    assert(z1_final_overflow_v == temp_ov2_v - borrow2_v) by(nonlinear_arith)
        requires
            z1_final_overflow_v == (temp_ov2_v - borrow2_v + LIMB_BASE()) % LIMB_BASE(),
            temp_ov2_v - borrow2_v >= 0,
            temp_ov2_v - borrow2_v < LIMB_BASE(), LIMB_BASE() > 0;
    assert(z1_final_overflow_v == ov_diff);
}

/// Add b[b_off..b_off+n] to out[out_start..out_start+n] in-place,
/// then add `overflow` at position n, then propagate carry through
/// out[out_start+n..out_start+n+tail].
///
/// Postcondition value equation:
///   vec_val(new_region) + carry * P(n+tail)
///     == vec_val(old_region) + vec_val(b_sub) + overflow * P(n)
#[verifier::rlimit(120)]
pub fn add_inplace_propagate<T: LimbOps>(
    out: &mut Vec<T>,
    out_start: usize,
    b: &[T], b_off: usize,
    n: usize,
    overflow: &T,
    tail: usize,
) -> (carry: T)
    requires
        n > 0,
        old(out)@.len() >= out_start + n + tail,
        out_start + n + tail < usize::MAX,
        b@.len() >= b_off + n,
        b_off + n < usize::MAX,
        overflow.sem() == 0 || overflow.sem() == 1,
        forall |j: int| 0 <= j < (n + tail) as int
            ==> 0 <= (#[trigger] old(out)@[(out_start as int + j)]).sem() < LIMB_BASE(),
        forall |j: int| 0 <= j < n as int
            ==> 0 <= (#[trigger] b@[(b_off as int + j)]).sem() < LIMB_BASE(),
    ensures
        out@.len() == old(out)@.len(),
        0 <= carry.sem() < LIMB_BASE(),
        forall |j: int| 0 <= j < (n + tail) as int
            ==> 0 <= (#[trigger] out@[(out_start as int + j)]).sem() < LIMB_BASE(),
        forall |j: int| 0 <= j < out@.len() && !(out_start as int <= j < (out_start + n + tail) as int)
            ==> out@[j] == old(out)@[j],
        vec_val(out@.subrange(out_start as int, (out_start + n + tail) as int))
            + carry.sem() * limb_power((n + tail) as nat)
            == vec_val(old(out)@.subrange(out_start as int, (out_start + n + tail) as int))
             + vec_val(b@.subrange(b_off as int, (b_off + n) as int))
             + overflow.sem() * limb_power(n as nat),
{
    let ghost old_out = out@;
    let ghost S = out_start as int;
    let ghost N = (n + tail) as int;
    let ghost B = b_off as int;
    let total_len = n + tail;

    // Phase 1: add b[0..n] to out[out_start..out_start+n] using lemma_vec_val_set_one
    let mut add_carry: T = T::zero_val();
    for i in 0..n
        invariant
            n > 0, n + tail == total_len,
            b@.len() >= b_off + n, b_off + n < usize::MAX,
            out@.len() == old_out.len(), old_out.len() >= (out_start + total_len),
            out_start + total_len < usize::MAX,
            S == out_start as int, N == total_len as int, B == b_off as int,
            add_carry.sem() == 0 || add_carry.sem() == 1,
            forall |j: int| 0 <= j < N ==> 0 <= (#[trigger] old_out[(S + j)]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < n as int ==> 0 <= (#[trigger] b@[(B + j)]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < i ==> 0 <= (#[trigger] out@[(S + j)]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < old_out.len() && !(S <= j < S + i) ==> out@[j] == old_out[j],
            vec_val(out@.subrange(S, S + N)) + add_carry.sem() * limb_power(i as nat)
                == vec_val(old_out.subrange(S, S + N)) + vec_val(b@.subrange(B, B + i)),
    {
        let ghost oi_sem = old_out[(S + i as int)].sem();
        let ghost bi_sem = b@[(B + i as int)].sem();
        proof {
            // Position S+i is unmodified: frame says j >= S+i is outside [S, S+i)
            assert(out@[(S + i as int)] == old_out[(S + i as int)]);
        }
        let (digit, next_carry) = out[out_start + i].add3(&b[b_off + i], &add_carry);
        proof {
            let x = oi_sem + bi_sem + add_carry.sem();
            assert(digit.sem() + next_carry.sem() * LIMB_BASE() == x) by(nonlinear_arith)
                requires digit.sem() == x % LIMB_BASE(),
                         next_carry.sem() == x / LIMB_BASE(), LIMB_BASE() > 0;
            assert(x < 2 * LIMB_BASE());
            assert(next_carry.sem() <= 1) by(nonlinear_arith)
                requires next_carry.sem() == x / LIMB_BASE(), x >= 0,
                         x < 2 * LIMB_BASE(), LIMB_BASE() > 0;
        }
        let ghost region_pre = out@.subrange(S, S + N);
        out.set(out_start + i, digit);
        proof {
            let region_post = out@.subrange(S, S + N);
            // Only position i changed in the subrange
            assert forall |k: int| 0 <= k < region_pre.len() && k != i as int
                implies region_pre[k] == region_post[k]
            by {
                assert(region_pre[k] == out@[(S + k)]);   // pre-set, k != i
                assert(region_post[k] == out@[(S + k)]);  // post-set
            }
            lemma_vec_val_set_one::<T>(region_pre, region_post, i as int);
            // vec_val(post) == vec_val(pre) + (digit.sem() - oi_sem) * P(i)

            // Extend b: vec_val(b[B..B+i+1]) = vec_val(b[B..B+i]) + bi_sem * P(i)
            lemma_vec_val_split::<T>(b@.subrange(B, B + i as int + 1), i as nat);
            let b_tail = b@.subrange(B + i as int, B + i as int + 1);
            assert(b_tail[0] == b@[(B + i as int)]);
            reveal_with_fuel(limbs_val, 2);
            assert(sem_seq(b_tail).len() == 1);
            assert(sem_seq(b_tail)[0] == bi_sem);
            assert(sem_seq(b_tail).subrange(1, 1) =~= Seq::<int>::empty());
            assert(vec_val(b_tail) == bi_sem);
            assert(b@.subrange(B, B + i as int + 1).subrange(0, i as int) =~= b@.subrange(B, B + i as int));
            assert(b@.subrange(B, B + i as int + 1).subrange(i as int, i as int + 1) =~= b_tail);

            let p_i = limb_power(i as nat);
            reveal_with_fuel(limb_power, 2);
            let p_i1 = limb_power((i + 1) as nat);
            assert(p_i1 == LIMB_BASE() * p_i);

            // Combine: IH + set_one + b_extension + carry chain → new IH
            assert(
                vec_val(region_post) + next_carry.sem() * p_i1
                == vec_val(old_out.subrange(S, S + N))
                    + vec_val(b@.subrange(B, B + i as int + 1))
            ) by(nonlinear_arith)
                requires
                    vec_val(region_pre) + add_carry.sem() * p_i
                        == vec_val(old_out.subrange(S, S + N))
                            + vec_val(b@.subrange(B, B + i as int)),
                    vec_val(region_post) == vec_val(region_pre)
                        + (digit.sem() - oi_sem) * p_i,
                    digit.sem() + next_carry.sem() * LIMB_BASE() == oi_sem + bi_sem + add_carry.sem(),
                    vec_val(b@.subrange(B, B + i as int + 1))
                        == vec_val(b@.subrange(B, B + i as int)) + bi_sem * p_i,
                    p_i1 == LIMB_BASE() * p_i;
        }
        add_carry = next_carry;
    }

    // Phase 2: total = carry + overflow
    let (total, _tc_hi) = add_carry.add3(overflow, &T::zero_val());
    proof {
        let s = add_carry.sem() + overflow.sem() + 0;
        assert(s <= 2);
        // LIMB_BASE = 2^32 > 2, so s < LIMB_BASE: s % LIMB_BASE = s, s / LIMB_BASE = 0
        assert(s < LIMB_BASE()) by {
            reveal_with_fuel(limb_power, 2);
            use crate::fixed_point::limbs::limb_base;
        }
        assert(total.sem() == s) by(nonlinear_arith)
            requires s >= 0, s < LIMB_BASE(), total.sem() == s % LIMB_BASE(), LIMB_BASE() > 0;
        assert(_tc_hi.sem() == 0) by(nonlinear_arith)
            requires s >= 0, s < LIMB_BASE(), _tc_hi.sem() == s / LIMB_BASE(), LIMB_BASE() > 0;
    }

    // Phase 3: propagate total through tail positions
    let mut prop = total;
    for i in 0..tail
        invariant
            n > 0, n + tail == total_len,
            out@.len() == old_out.len(), old_out.len() >= (out_start + total_len),
            out_start + total_len < usize::MAX,
            S == out_start as int, N == total_len as int,
            0 <= prop.sem(), prop.sem() < LIMB_BASE(),
            total.sem() <= 2,
            forall |j: int| 0 <= j < N ==> 0 <= (#[trigger] old_out[(S + j)]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < n as int + i ==> 0 <= (#[trigger] out@[(S + j)]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < old_out.len() && !(S <= j < S + n as int + i) ==> out@[j] == old_out[j],
            // Value equation: carry from phase 1 at position n, prop at position n+i
            vec_val(out@.subrange(S, S + N))
                + add_carry.sem() * limb_power(n as nat)
                + prop.sem() * limb_power((n as int + i) as nat)
                == vec_val(old_out.subrange(S, S + N))
                    + vec_val(b@.subrange(B, B + n as int))
                    + total.sem() * limb_power(n as nat),
    {
        let ghost ni = n as int + i as int;
        let ghost oi_sem3 = old_out[(S + ni)].sem();
        proof {
            assert(out@[(S + ni)] == old_out[(S + ni)]);
        }
        let (s, nc) = out[out_start + n + i].add3(&prop, &T::zero_val());
        proof {
            let x3 = oi_sem3 + prop.sem() + 0;
            assert(s.sem() + nc.sem() * LIMB_BASE() == x3) by(nonlinear_arith)
                requires s.sem() == x3 % LIMB_BASE(),
                         nc.sem() == x3 / LIMB_BASE(), LIMB_BASE() > 0;
            assert(x3 < 2 * LIMB_BASE());
            assert(nc.sem() < LIMB_BASE()) by(nonlinear_arith)
                requires nc.sem() == x3 / LIMB_BASE(), x3 >= 0,
                         x3 < 2 * LIMB_BASE(), LIMB_BASE() > 0;
        }
        let ghost region_pre3 = out@.subrange(S, S + N);
        out.set(out_start + n + i, s);
        proof {
            let region_post3 = out@.subrange(S, S + N);
            assert forall |k: int| 0 <= k < region_pre3.len() && k != ni
                implies region_pre3[k] == region_post3[k]
            by {
                assert(region_post3[k] == out@[(S + k)]);
            }
            lemma_vec_val_set_one::<T>(region_pre3, region_post3, ni);

            let p_ni = limb_power(ni as nat);
            reveal_with_fuel(limb_power, 2);
            let p_ni1 = limb_power((ni + 1) as nat);
            assert(p_ni1 == LIMB_BASE() * p_ni);

            assert(
                vec_val(region_post3)
                    + add_carry.sem() * limb_power(n as nat)
                    + nc.sem() * p_ni1
                == vec_val(old_out.subrange(S, S + N))
                    + vec_val(b@.subrange(B, B + n as int))
                    + total.sem() * limb_power(n as nat)
            ) by(nonlinear_arith)
                requires
                    vec_val(region_pre3) + add_carry.sem() * limb_power(n as nat)
                        + prop.sem() * p_ni
                        == vec_val(old_out.subrange(S, S + N))
                            + vec_val(b@.subrange(B, B + n as int))
                            + total.sem() * limb_power(n as nat),
                    vec_val(region_post3) == vec_val(region_pre3)
                        + (s.sem() - oi_sem3) * p_ni,
                    s.sem() + nc.sem() * LIMB_BASE() == oi_sem3 + prop.sem(),
                    p_ni1 == LIMB_BASE() * p_ni;
        }
        prop = nc;
    }

    // Final: simplify value equation and bound carry
    proof {
        // From the loop: add_carry*P(n) + prop*P(n+tail) cancels with total*P(n)
        // since total = add_carry + overflow
        assert(
            vec_val(out@.subrange(S, S + N)) + prop.sem() * limb_power((n + tail) as nat)
            == vec_val(old_out.subrange(S, S + N))
                + vec_val(b@.subrange(B, B + n as int))
                + overflow.sem() * limb_power(n as nat)
        ) by(nonlinear_arith)
            requires
                vec_val(out@.subrange(S, S + N))
                    + add_carry.sem() * limb_power(n as nat)
                    + prop.sem() * limb_power((n + tail) as nat)
                == vec_val(old_out.subrange(S, S + N))
                    + vec_val(b@.subrange(B, B + n as int))
                    + total.sem() * limb_power(n as nat),
                total.sem() == add_carry.sem() + overflow.sem();

        // Carry bound: prop < LIMB_BASE from loop invariant (already established)
    }
    prop
}

/// Steps 5+6 of Karatsuba: subtract z0/z2 from z1_full, then add z1 to output at offset half.
/// Extracted from mul_karatsuba_one_level_to to keep Z3 context small.
///
/// Ghost values are passed via Ghost<int> wrappers. The caller establishes the
/// algebraic connections (step 3/4/4b value equations) in the requires.
#[verifier::rlimit(200)]
pub fn karatsuba_combine<T: LimbOps>(
    out: &mut Vec<T>, out_off: usize,
    scratch: &mut Vec<T>, scratch_off: usize,
    n: usize, half: usize,
    z1_overflow: &T,
    // Ghost values from steps 1-4b (packed as ints)
    z1_full_n_val_g: Ghost<int>,
    z0_val_g: Ghost<int>, z2_val_g: Ghost<int>,
    schoolbook_val_g: Ghost<int>,
    a_sum_val_g: Ghost<int>, b_sum_val_g: Ghost<int>,
    asum_carry_g: Ghost<int>, bsum_carry_g: Ghost<int>,
    a_lo_v_g: Ghost<int>, a_hi_v_g: Ghost<int>,
    b_lo_v_g: Ghost<int>, b_hi_v_g: Ghost<int>,
)
    requires
        half == n / 2, n >= 4, n <= 0x1FFF_FFFF, n % 2 == 0,
        old(out)@.len() >= out_off + 2 * n, out_off + 2 * n < usize::MAX,
        old(scratch)@.len() >= scratch_off + 2 * n, scratch_off + 2 * n < usize::MAX,
        // Valid limbs
        forall |j: int| 0 <= j < 2 * n ==> 0 <= (#[trigger] old(out)@[(out_off as int + j)]).sem() < LIMB_BASE(),
        forall |j: int| 0 <= j < n as int ==> 0 <= (#[trigger] old(scratch)@[(scratch_off as int + j)]).sem() < LIMB_BASE(),
        // z1_overflow bounds
        0 <= z1_overflow.sem(), z1_overflow.sem() <= 3,
        // Ghost values match exec state
        z1_full_n_val_g@ == vec_val(old(scratch)@.subrange(scratch_off as int, (scratch_off + n) as int)),
        z0_val_g@ == vec_val(old(out)@.subrange(out_off as int, (out_off + n) as int)),
        z2_val_g@ == vec_val(old(out)@.subrange((out_off + n) as int, (out_off + 2 * n) as int)),
        // Algebraic facts (established by caller from steps 1-4b)
        asum_carry_g@ == 0 || asum_carry_g@ == 1,
        bsum_carry_g@ == 0 || bsum_carry_g@ == 1,
        a_sum_val_g@ + asum_carry_g@ * limb_power(half as nat) == a_lo_v_g@ + a_hi_v_g@,
        b_sum_val_g@ + bsum_carry_g@ * limb_power(half as nat) == b_lo_v_g@ + b_hi_v_g@,
        schoolbook_val_g@ == a_sum_val_g@ * b_sum_val_g@,
        z1_full_n_val_g@ + z1_overflow.sem() * limb_power(n as nat) == schoolbook_val_g@
            + asum_carry_g@ * limb_power(half as nat) * b_sum_val_g@
            + bsum_carry_g@ * limb_power(half as nat) * a_sum_val_g@
            + asum_carry_g@ * bsum_carry_g@ * limb_power(n as nat),
        z0_val_g@ == a_lo_v_g@ * b_lo_v_g@,
        z2_val_g@ == a_hi_v_g@ * b_hi_v_g@,
        // Input bounds
        0 <= a_lo_v_g@, a_lo_v_g@ < limb_power(half as nat),
        0 <= a_hi_v_g@, a_hi_v_g@ < limb_power(half as nat),
        0 <= b_lo_v_g@, b_lo_v_g@ < limb_power(half as nat),
        0 <= b_hi_v_g@, b_hi_v_g@ < limb_power(half as nat),
        0 <= a_sum_val_g@, a_sum_val_g@ < limb_power(half as nat),
        0 <= b_sum_val_g@, b_sum_val_g@ < limb_power(half as nat),
    ensures
        out@.len() == old(out)@.len(),
        scratch@.len() == old(scratch)@.len(),
        forall |j: int| 0 <= j < 2 * n ==> 0 <= (#[trigger] out@[(out_off as int + j)]).sem() < LIMB_BASE(),
        forall |j: int| 0 <= j < out@.len() && !(out_off as int <= j < (out_off + 2 * n) as int)
            ==> out@[j] == old(out)@[j],
        // Value equation
        vec_val(out@.subrange(out_off as int, (out_off + 2 * n) as int))
            == (a_hi_v_g@ * limb_power(half as nat) + a_lo_v_g@)
             * (b_hi_v_g@ * limb_power(half as nat) + b_lo_v_g@),
{
    use vstd::slice::slice_subrange;

    let ghost old_out = out@;
    let ghost old_scratch = scratch@;
    let ghost z0_val = z0_val_g@;
    let ghost z2_val = z2_val_g@;
    let ghost z1_full_n_val = z1_full_n_val_g@;
    let ghost z1_full_val = z1_full_n_val + z1_overflow.sem() * limb_power(n as nat);

    // Step 5: z1 = z1_full - z0 - z2 (two sub_borrow loops)
    let ghost scratch_pre_sub = scratch@;
    let mut borrow1 = T::zero_val();
    for i in 0..n
        invariant n >= 4, n <= 0x1FFF_FFFF, half == n / 2,
            out@.len() >= out_off + 2 * n, out@.len() == old_out.len(),
            out_off + 2 * n < usize::MAX,
            scratch@.len() >= scratch_off + 2 * n, scratch@.len() == old_scratch.len(),
            scratch_off + 2 * n < usize::MAX,
            borrow1.sem() == 0 || borrow1.sem() == 1,
            z1_full_n_val == vec_val(scratch_pre_sub.subrange(scratch_off as int, (scratch_off + n) as int)),
            forall |j: int| 0 <= j < 2 * n
                ==> 0 <= (#[trigger] out@[(out_off as int + j) as int]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < n
                ==> 0 <= (#[trigger] scratch@[(scratch_off as int + j) as int]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < scratch@.len() && !(scratch_off as int <= j < scratch_off as int + i)
                ==> scratch@[j] == scratch_pre_sub[j],
            vec_val(scratch@.subrange(scratch_off as int, (scratch_off + n) as int))
                == z1_full_n_val
                    - vec_val(out@.subrange(out_off as int, out_off as int + i))
                    + borrow1.sem() * limb_power(i as nat),
    {
        let ghost si_sem = scratch@[(scratch_off as int + i as int)].sem();
        let ghost oi_sem = out@[(out_off as int + i as int)].sem();
        let ghost region_pre = scratch@.subrange(scratch_off as int, (scratch_off + n) as int);
        let (d, bw) = scratch[scratch_off + i].sub_borrow(&out[out_off + i], &borrow1);
        scratch.set(scratch_off + i, d);
        proof {
            let region_post = scratch@.subrange(scratch_off as int, (scratch_off + n) as int);
            assert forall |k: int| 0 <= k < region_pre.len() && k != i as int
                implies region_pre[k] == region_post[k]
            by { assert(region_post[k] == scratch@[(scratch_off as int + k)]); }
            lemma_vec_val_set_one::<T>(region_pre, region_post, i as int);

            lemma_vec_val_split::<T>(out@.subrange(out_off as int, out_off as int + i as int + 1), i as nat);
            let b_tail = out@.subrange(out_off as int + i as int, out_off as int + i as int + 1);
            reveal_with_fuel(limbs_val, 2);
            assert(sem_seq(b_tail)[0] == oi_sem);
            assert(sem_seq(b_tail).subrange(1, 1) =~= Seq::<int>::empty());
            assert(vec_val(b_tail) == oi_sem);
            assert(out@.subrange(out_off as int, out_off as int + i as int + 1).subrange(0, i as int)
                =~= out@.subrange(out_off as int, out_off as int + i as int));

            let p_i = limb_power(i as nat);
            reveal_with_fuel(limb_power, 2);
            let p_i1 = limb_power((i + 1) as nat);
            assert(p_i1 == LIMB_BASE() * p_i);

            assert(
                vec_val(region_post) == z1_full_n_val
                    - vec_val(out@.subrange(out_off as int, out_off as int + i as int + 1))
                    + bw.sem() * p_i1
            ) by(nonlinear_arith)
                requires
                    vec_val(region_pre) == z1_full_n_val
                        - vec_val(out@.subrange(out_off as int, out_off as int + i))
                        + borrow1.sem() * p_i,
                    vec_val(region_post) == vec_val(region_pre) + (d.sem() - si_sem) * p_i,
                    d.sem() + oi_sem + borrow1.sem() == si_sem + bw.sem() * LIMB_BASE(),
                    vec_val(out@.subrange(out_off as int, out_off as int + i as int + 1))
                        == vec_val(out@.subrange(out_off as int, out_off as int + i)) + oi_sem * p_i,
                    p_i1 == LIMB_BASE() * p_i;
        }
        borrow1 = bw;
    }
    let ghost scratch_post_sub1_val = vec_val(scratch@.subrange(scratch_off as int, (scratch_off + n) as int));

    let ghost scratch_post_sub1 = scratch@;
    let mut borrow2 = T::zero_val();
    for i in 0..n
        invariant n >= 4, n <= 0x1FFF_FFFF, half == n / 2,
            out@.len() >= out_off + 2 * n, out@.len() == old_out.len(),
            out_off + 2 * n < usize::MAX,
            scratch@.len() >= scratch_off + 2 * n, scratch@.len() == old_scratch.len(),
            scratch_off + 2 * n < usize::MAX,
            borrow2.sem() == 0 || borrow2.sem() == 1,
            scratch_post_sub1_val == vec_val(scratch_post_sub1.subrange(scratch_off as int, (scratch_off + n) as int)),
            forall |j: int| 0 <= j < 2 * n
                ==> 0 <= (#[trigger] out@[(out_off as int + j) as int]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < n
                ==> 0 <= (#[trigger] scratch@[(scratch_off as int + j) as int]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < scratch@.len() && !(scratch_off as int <= j < scratch_off as int + i)
                ==> scratch@[j] == scratch_post_sub1[j],
            vec_val(scratch@.subrange(scratch_off as int, (scratch_off + n) as int))
                == scratch_post_sub1_val
                    - vec_val(out@.subrange((out_off + n) as int, (out_off + n) as int + i))
                    + borrow2.sem() * limb_power(i as nat),
    {
        let ghost si_sem = scratch@[(scratch_off as int + i as int)].sem();
        let ghost j2 = (n as int + i as int);
        proof { assert(0 <= j2 && j2 < 2 * n as int); }
        let ghost oi_sem = out@[(out_off as int + j2) as int].sem();
        let ghost region_pre = scratch@.subrange(scratch_off as int, (scratch_off + n) as int);
        let (d, bw) = scratch[scratch_off + i].sub_borrow(&out[out_off + n + i], &borrow2);
        proof {
            let ghost diff2 = si_sem - oi_sem - borrow2.sem();
            assert(d.sem() + oi_sem + borrow2.sem() == si_sem + bw.sem() * LIMB_BASE()) by {
                if diff2 >= 0 {
                    assert(bw.sem() == 0);
                    assert(diff2 < LIMB_BASE()) by(nonlinear_arith)
                        requires diff2 >= 0, diff2 == si_sem - oi_sem - borrow2.sem(),
                                 si_sem < LIMB_BASE(), oi_sem >= 0, borrow2.sem() >= 0;
                    assert(d.sem() == diff2) by(nonlinear_arith)
                        requires d.sem() == (diff2 + LIMB_BASE()) % LIMB_BASE(),
                                 diff2 >= 0, diff2 < LIMB_BASE(), LIMB_BASE() > 0;
                } else {
                    assert(bw.sem() == 1);
                    assert(diff2 + LIMB_BASE() >= 0) by(nonlinear_arith)
                        requires diff2 == si_sem - oi_sem - borrow2.sem(),
                                 si_sem >= 0, oi_sem < LIMB_BASE(), borrow2.sem() <= 1;
                    assert(diff2 + LIMB_BASE() < LIMB_BASE()) by(nonlinear_arith)
                        requires diff2 < 0;
                    assert(d.sem() == diff2 + LIMB_BASE()) by(nonlinear_arith)
                        requires d.sem() == (diff2 + LIMB_BASE()) % LIMB_BASE(),
                                 diff2 + LIMB_BASE() >= 0, diff2 + LIMB_BASE() < LIMB_BASE(),
                                 LIMB_BASE() > 0;
                }
            }
        }
        scratch.set(scratch_off + i, d);
        proof {
            let region_post = scratch@.subrange(scratch_off as int, (scratch_off + n) as int);
            assert forall |k: int| 0 <= k < region_pre.len() && k != i as int
                implies region_pre[k] == region_post[k]
            by { assert(region_post[k] == scratch@[(scratch_off as int + k)]); }
            lemma_vec_val_set_one::<T>(region_pre, region_post, i as int);

            lemma_vec_val_split::<T>(out@.subrange((out_off + n) as int, (out_off + n) as int + i as int + 1), i as nat);
            let b_tail2 = out@.subrange((out_off + n) as int + i as int, (out_off + n) as int + i as int + 1);
            reveal_with_fuel(limbs_val, 2);
            assert(sem_seq(b_tail2)[0] == oi_sem);
            assert(sem_seq(b_tail2).subrange(1, 1) =~= Seq::<int>::empty());
            assert(vec_val(b_tail2) == oi_sem);
            assert(out@.subrange((out_off + n) as int, (out_off + n) as int + i as int + 1).subrange(0, i as int)
                =~= out@.subrange((out_off + n) as int, (out_off + n) as int + i as int));

            let p_i = limb_power(i as nat);
            reveal_with_fuel(limb_power, 2);
            let p_i1 = limb_power((i + 1) as nat);
            assert(p_i1 == LIMB_BASE() * p_i);

            assert(
                vec_val(region_post) == scratch_post_sub1_val
                    - vec_val(out@.subrange((out_off + n) as int, (out_off + n) as int + i as int + 1))
                    + bw.sem() * p_i1
            ) by(nonlinear_arith)
                requires
                    vec_val(region_pre) == scratch_post_sub1_val
                        - vec_val(out@.subrange((out_off + n) as int, (out_off + n) as int + i))
                        + borrow2.sem() * p_i,
                    vec_val(region_post) == vec_val(region_pre) + (d.sem() - si_sem) * p_i,
                    d.sem() + oi_sem + borrow2.sem() == si_sem + bw.sem() * LIMB_BASE(),
                    vec_val(out@.subrange((out_off + n) as int, (out_off + n) as int + i as int + 1))
                        == vec_val(out@.subrange((out_off + n) as int, (out_off + n) as int + i)) + oi_sem * p_i,
                    p_i1 == LIMB_BASE() * p_i;
        }
        borrow2 = bw;
    }

    // Step 5b: prove z1_final_overflow is 0 or 1
    let (temp_ov2, _) = z1_overflow.sub_borrow(&borrow1, &T::zero_val());
    let (z1_final_overflow, _) = temp_ov2.sub_borrow(&borrow2, &T::zero_val());
    proof {
        let P = limb_power(n as nat);
        let B = limb_power(half as nat);
        let z1_n = vec_val(scratch@.subrange(scratch_off as int, (scratch_off + n) as int));

        assert(valid_limbs(scratch@.subrange(scratch_off as int, (scratch_off + n) as int))) by {
            assert forall |j: int| 0 <= j < n as int
                implies 0 <= (#[trigger] scratch@.subrange(scratch_off as int, (scratch_off + n) as int)[j]).sem() < LIMB_BASE()
            by { assert(scratch@.subrange(scratch_off as int, (scratch_off + n) as int)[j] == scratch@[(scratch_off as int + j)]); }
        }
        lemma_vec_val_bounded::<T>(scratch@.subrange(scratch_off as int, (scratch_off + n) as int));
        assert(LIMB_BASE() > 3) by {
            reveal_with_fuel(limb_power, 2);
            use crate::fixed_point::limbs::limb_base;
        }
        lemma_limb_power_add(half as nat, half as nat);
        assert(n == 2 * half);
        assert(P == B * B);
        // Convert karatsuba_combine's precondition (using limb_power(n)) to
        // overflow_chain's format (using B*B)
        assert(z1_full_n_val + z1_overflow.sem() * P == schoolbook_val_g@
            + asum_carry_g@ * B * b_sum_val_g@
            + bsum_carry_g@ * B * a_sum_val_g@
            + asum_carry_g@ * bsum_carry_g@ * B * B) by(nonlinear_arith)
            requires
                z1_full_n_val + z1_overflow.sem() * P == schoolbook_val_g@
                    + asum_carry_g@ * B * b_sum_val_g@
                    + bsum_carry_g@ * B * a_sum_val_g@
                    + asum_carry_g@ * bsum_carry_g@ * P,
                P == B * B;

        lemma_karatsuba_overflow_chain(
            a_sum_val_g@, b_sum_val_g@,
            asum_carry_g@, bsum_carry_g@,
            a_lo_v_g@, a_hi_v_g@, b_lo_v_g@, b_hi_v_g@,
            schoolbook_val_g@,
            z1_full_val, z1_full_n_val, z1_overflow.sem(),
            z0_val, z2_val,
            scratch_post_sub1_val,
            borrow1.sem(), borrow2.sem(),
            z1_n,
            temp_ov2.sem(), z1_final_overflow.sem(),
            B, P,
        );
    }

    // Step 6: add z1 to output at offset half
    let scratch_slice = slice_subrange(&*scratch, scratch_off, scratch.len());
    proof {
        assert forall |j: int| 0 <= j < n as int
            implies 0 <= (#[trigger] scratch_slice@[(j as int)]).sem() < LIMB_BASE()
        by { assert(scratch_slice@[j] == scratch@[(scratch_off as int + j) as int]); }
        assert forall |j: int| 0 <= j < (n + half) as int
            implies 0 <= (#[trigger] out@[((out_off + half) as int + j)]).sem() < LIMB_BASE()
        by {
            let jj = (half as int + j);
            assert(0 <= jj && jj < 2 * n as int);
            assert(out@[(out_off as int + jj) as int].sem() < LIMB_BASE());
        }
    }
    let ghost out_pre_step6 = out@;
    let step6_carry = add_inplace_propagate(
        out, out_off + half,
        scratch_slice, 0,
        n,
        &z1_final_overflow,
        half,
    );
    // add_inplace_propagate postcondition:
    //   vec_val(out[half..2n]) + carry*P(n+half)
    //     == vec_val(old[half..2n]) + z1_n_limbs + overflow*P(n)

    // Postcondition: value equation
    proof {
        use crate::fixed_point::limbs::lemma_karatsuba_identity;

        let B = limb_power(half as nat);
        let P = limb_power(n as nat);
        lemma_limb_power_add(half as nat, half as nat);
        assert(P == B * B);
        let P2n = limb_power((2 * n) as nat);
        lemma_limb_power_add(n as nat, n as nat);
        assert(P2n == P * P);
        let Pnh = limb_power((n + half) as nat);
        lemma_limb_power_add(n as nat, half as nat);

        // Split output and old_out at half
        let out_region = out@.subrange(out_off as int, (out_off + 2 * n) as int);
        lemma_vec_val_split::<T>(out_region, half as nat);
        let out_lo = out_region.subrange(0, half as int);
        let out_hi = out_region.subrange(half as int, (2 * n) as int);
        assert(out_hi =~= out@.subrange((out_off + half) as int, (out_off + 2 * n) as int));

        let old_region = old_out.subrange(out_off as int, (out_off + 2 * n) as int);
        lemma_vec_val_split::<T>(old_region, half as nat);
        let old_lo = old_region.subrange(0, half as int);
        let old_hi = old_region.subrange(half as int, (2 * n) as int);
        assert(old_hi =~= old_out.subrange((out_off + half) as int, (out_off + 2 * n) as int));

        // out_lo unchanged: [0..half) wasn't modified by add_inplace_propagate (frame)
        assert(out_lo =~= old_lo);

        // old_out split at n: z0 + z2*P
        lemma_vec_val_split::<T>(old_region, n as nat);
        assert(old_region.subrange(0, n as int) =~= old_out.subrange(out_off as int, (out_off + n) as int));
        assert(old_region.subrange(n as int, (2 * n) as int) =~= old_out.subrange((out_off + n) as int, (out_off + 2 * n) as int));

        // out_pre_step6 == old_out (sub_borrow loops only modified scratch, not out)
        assert(out_pre_step6.subrange((out_off + half) as int, (out_off + 2 * n) as int)
            =~= old_hi);

        // Karatsuba identity
        lemma_karatsuba_identity(
            a_lo_v_g@ as int, a_hi_v_g@ as int,
            b_lo_v_g@ as int, b_hi_v_g@ as int,
            B as int,
        );

        // Product bound: a*b < P(2n) = P²
        let a_val = a_hi_v_g@ * B + a_lo_v_g@;
        let b_val = b_hi_v_g@ * B + b_lo_v_g@;
        assert(a_hi_v_g@ * B <= (B - 1) * B) by(nonlinear_arith)
            requires a_hi_v_g@ < B, a_hi_v_g@ >= 0, B > 0;
        assert(a_val < P) by(nonlinear_arith)
            requires a_val == a_hi_v_g@ * B + a_lo_v_g@,
                     a_hi_v_g@ * B <= (B - 1) * B, a_lo_v_g@ < B, a_lo_v_g@ >= 0, P == B * B;
        assert(b_hi_v_g@ * B <= (B - 1) * B) by(nonlinear_arith)
            requires b_hi_v_g@ < B, b_hi_v_g@ >= 0, B > 0;
        assert(b_val < P) by(nonlinear_arith)
            requires b_val == b_hi_v_g@ * B + b_lo_v_g@,
                     b_hi_v_g@ * B <= (B - 1) * B, b_lo_v_g@ < B, b_lo_v_g@ >= 0, P == B * B;
        assert(a_val * b_val < P2n) by(nonlinear_arith)
            requires a_val < P, b_val < P, a_val >= 0, b_val >= 0, P2n == P * P, P > 0;

        // Output bounded
        assert(valid_limbs(out_region)) by {
            assert forall |j: int| 0 <= j < out_region.len()
                implies 0 <= (#[trigger] out_region[j]).sem() < LIMB_BASE()
            by {
                assert(out_region[j] == out@[(out_off as int + j)]);
                if j >= half as int {
                    let jj = j - half as int;
                    assert(out@[((out_off + half) as int + jj)].sem() < LIMB_BASE());
                } else {
                    // Frame: unchanged from old_out
                    assert(out@[(out_off as int + j)] == old_out[(out_off as int + j)]);
                }
            }
        }
        lemma_vec_val_bounded::<T>(out_region);

        // Chain: vec_val(out) + carry*Pnh*B = vec_val(old) + z1_true*B
        // where z1_true is added via add_inplace_propagate
        // vec_val(out_region) = vec_val(out_lo) + vec_val(out_hi)*B
        //                     = vec_val(old_lo) + vec_val(out_hi)*B
        // From add_inplace: vec_val(out_hi) + carry*Pnh = vec_val(old_hi) + z1_val + ov*P
        // So: vec_val(out_region) = vec_val(old_lo) + (vec_val(old_hi) + z1_val + ov*P - carry*Pnh)*B
        //   = vec_val(old_region) + (z1_val + ov*P)*B - carry*Pnh*B
        // vec_val(old_region) = z0 + z2*P  (from precondition)
        // z1_val + ov*P = z1_true (from sub_borrow chain + overflow)
        // And z0 + z1_true*B + z2*P = z0 + z1*B + z2*B² = a*b  (Karatsuba identity)
        // So: vec_val(out_region) + carry*Pnh*B = a*b
        // Since a*b < P2n and vec_val >= 0, carry must be 0.
        // And Pnh*B = P*P = P2n, so vec_val(out_region) = a*b.

        assert(vec_val(out_region) + step6_carry.sem() * Pnh * B
            == vec_val(old_region) + (vec_val(scratch_slice@.subrange(0, n as int)) + z1_final_overflow.sem() * P) * B)
        by(nonlinear_arith)
            requires
                vec_val(out_region) == vec_val(out_lo) + vec_val(out_hi) * B,
                vec_val(old_region) == vec_val(old_lo) + vec_val(old_hi) * B,
                vec_val(out_lo) == vec_val(old_lo),
                vec_val(out_hi) + step6_carry.sem() * Pnh
                    == vec_val(old_hi) + vec_val(scratch_slice@.subrange(0, n as int))
                     + z1_final_overflow.sem() * P;

        // vec_val(old_region) = z0 + z2*P
        assert(vec_val(old_region) == z0_val + z2_val * P);

        // The product a_val * b_val = z0 + z1*B + z2*B² from Karatsuba identity
        // carry must be 0 because a*b < P2n and vec_val(out) < P2n
        assert(Pnh * B == P2n) by(nonlinear_arith)
            requires Pnh == P * B, P == B * B, P2n == P * P;

        // The key value equation:
        // vec_val(out_region) + carry*P2n = z0 + z1_true*B + z2*P
        //   where z1_true = (vec_val(z1_limbs) + overflow*P)
        // And by Karatsuba identity: z0 + z1*B + z2*B² = a*b
        // Since a*b < P2n and vec_val(out) >= 0, carry = 0.

        // Step 1: from add_inplace_propagate postcondition:
        // vec_val(out_hi) + carry*Pnh = vec_val(old_hi) + z1_n_val + overflow*P
        // (old_hi = out_pre_step6[half..2n] = old_out[half..2n])

        // Step 2: vec_val(out_region) = vec_val(out_lo) + vec_val(out_hi)*B
        //   = vec_val(old_lo) + (vec_val(old_hi) + z1_val + ov*P - carry*Pnh)*B
        //   = vec_val(old_region) + (z1_val + ov*P)*B - carry*Pnh*B
        //   = z0 + z2*P + z1_true*B - carry*P2n

        // Step 3: z0 + z1_true*B + z2*P = a*b (from Karatsuba identity + z1_full bounds)
        // So vec_val(out_region) + carry*P2n = a*b

        // Step 4: a*b < P2n, vec_val >= 0 → carry = 0

        // I need Z3 to see the intermediate: vec_val(out_hi) + carry*Pnh = vec_val(old_hi) + z1_n + ov*P
        // This IS add_inplace_propagate's postcondition. Let me just assert the final result:

        let z1_true = vec_val(scratch_slice@.subrange(0, n as int)) + z1_final_overflow.sem() * P;

        // From add_inplace_propagate: vec_val(out_hi) + carry*Pnh = vec_val(old_hi) + z1_n + ov*P
        // = vec_val(old_hi) + z1_true

        // vec_val(out_region) = vec_val(out_lo) + vec_val(out_hi) * B
        // vec_val(old_region) = vec_val(old_lo) + vec_val(old_hi) * B
        // out_lo == old_lo
        // So: vec_val(out_region) + carry * Pnh * B
        //   = vec_val(old_lo) + (vec_val(old_hi) + z1_true) * B
        //   = vec_val(old_region) + z1_true * B
        assert(vec_val(out_region) + step6_carry.sem() * P2n
            == vec_val(old_region) + z1_true * B) by(nonlinear_arith)
            requires
                vec_val(out_region) == vec_val(out_lo) + vec_val(out_hi) * B,
                vec_val(old_region) == vec_val(old_lo) + vec_val(old_hi) * B,
                vec_val(out_lo) == vec_val(old_lo),
                vec_val(out_hi) + step6_carry.sem() * Pnh
                    == vec_val(old_hi) + z1_true,
                Pnh * B == P2n;

        // old_region = z0 + z2*P
        // z1_true = z1 (the Karatsuba z1 cross term)
        // z0 + z1*B + z2*P = z0 + z1*B + z2*B² = a*b
        // Connect z1_true to Karatsuba z1 via the overflow chain's postcondition
        // The overflow chain proved:
        //   z1_n + z1_final_overflow * P == z1_full - z0 - z2
        //   z1_full == (a_lo+a_hi)(b_lo+b_hi)
        // where z1_n was the vec_val of scratch z1 limbs at that point.
        // After the sub loops, scratch z1 limbs weren't modified by add_inplace_propagate
        // (which only wrote to out). So scratch_slice@[0..n] still has the same values.
        // z1_true = vec_val(scratch_slice[0..n]) + z1_final_overflow * P = z1_n + z1_final_overflow * P
        // = z1_full - z0 - z2 = (a_lo+a_hi)(b_lo+b_hi) - z0 - z2

        // scratch_slice[0..n] has the same z1 limbs that overflow chain used
        let z1_n_check = vec_val(scratch@.subrange(scratch_off as int, (scratch_off + n) as int));
        assert(scratch_slice@.subrange(0, n as int) =~= scratch@.subrange(scratch_off as int, (scratch_off + n) as int));
        assert(z1_true == z1_n_check + z1_final_overflow.sem() * P);
        // overflow chain postcondition gives: z1_n_check + z1_final_overflow*P == z1_full - z0 - z2
        // and z1_full == (a_lo+a_hi)(b_lo+b_hi)

        assert(a_val * b_val == z0_val + z1_true * B + z2_val * P) by(nonlinear_arith)
            requires
                a_val * b_val == z0_val
                    + ((a_lo_v_g@ + a_hi_v_g@) * (b_lo_v_g@ + b_hi_v_g@) - z0_val - z2_val) * B
                    + z2_val * B * B,
                z1_true == (a_lo_v_g@ + a_hi_v_g@) * (b_lo_v_g@ + b_hi_v_g@) - z0_val - z2_val,
                P == B * B;

        // carry = 0 from bounds
        assert(step6_carry.sem() == 0) by(nonlinear_arith)
            requires
                vec_val(out_region) + step6_carry.sem() * P2n == a_val * b_val,
                0 <= vec_val(out_region), vec_val(out_region) < P2n,
                a_val * b_val < P2n, a_val * b_val >= 0,
                step6_carry.sem() >= 0, P2n > 0;

        assert(vec_val(out_region) == a_val * b_val);
    }

    // Postcondition: valid limbs on full 2n region
    // add_inplace_propagate guarantees valid limbs on [half, 2n)
    // Positions [0, half) were unchanged (frame from add_inplace_propagate)
    proof {
        // Positions [0, half): unchanged from old_out by frame chain.
        // Sub_borrow loops only modified scratch, not out.
        // add_inplace_propagate only modified [out_off+half, out_off+2n).
        // So positions [out_off, out_off+half) still equal old_out.
        assert forall |j: int| 0 <= j < 2 * n
            implies 0 <= (#[trigger] out@[(out_off as int + j)]).sem() < LIMB_BASE()
        by {
            if j >= half as int {
                // From add_inplace_propagate's valid limbs postcondition on [half, half+n+half)
                let jj = j - half as int;
                assert(0 <= jj && jj < (n + half) as int);
                assert(out@[((out_off + half) as int + jj)].sem() < LIMB_BASE());
                assert((out_off as int + j) == (out_off + half) as int + jj);
            }
            // j < half: out@[(out_off+j)] == old_out[(out_off+j)] from frame
            // old_out[(out_off+j)].sem() < LIMB_BASE() from precondition
        }
    }
}

} //  verus!
