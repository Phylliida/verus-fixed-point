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
    assert(z1_full_val < z0_val + z2_val + 2 * P) by(nonlinear_arith)
        requires
            z1_full_val == (a_lo_val + a_hi_val) * (b_lo_val + b_hi_val),
            z0_val == a_lo_val * b_lo_val,
            z2_val == a_hi_val * b_hi_val,
            a_lo_val < B, a_hi_val < B, b_lo_val < B, b_hi_val < B,
            a_lo_val >= 0, a_hi_val >= 0, b_lo_val >= 0, b_hi_val >= 0,
            P == B * B, B > 0;
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

} //  verus!
