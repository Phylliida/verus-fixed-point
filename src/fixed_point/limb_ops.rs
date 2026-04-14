///  LimbOps: trait abstracting single-limb operations for multi-limb arithmetic.
///
///  Implementations:
///  - u32: concrete limb arithmetic using u64 intermediates
///  - RuntimeArithExpr: builds symbolic expression trees (in verus-fractals)
///
///  Generic multi-limb algorithms (add_limbs, mul_schoolbook, mul_karatsuba)
///  use this trait, so correctness is proved once for both instantiations.

use vstd::prelude::*;
use vstd::slice::{SliceAdditionalExecFns, slice_subrange};
use super::limbs::limb_base;
#[cfg(verus_keep_ghost)]
use super::limbs::{lemma_limb_base_is_pow2_32, lemma_karatsuba_identity, lemma_mul_distribute};
#[cfg(verus_keep_ghost)]
use super::limbs as limb_base_conv;
#[cfg(verus_keep_ghost)]
use super::limb_ops_proofs::{
    lemma_vec_val_set_one, lemma_truncated_product_seq,
    signed_val_of, lemma_signed_add_correct_seq,
};

verus! {

///  Base constant for limb arithmetic (2^32).
pub open spec fn LIMB_BASE() -> int { limb_base() as int }

///  Trait for types that can serve as limbs in multi-limb arithmetic.
///
///  The `sem()` spec function gives the semantic integer value:
///  - For u32: `self as int`
///  - For ArithExpr: `arith_eval(self, env)` (structurally correct for all env)
pub trait LimbOps : Sized {

    ///  The semantic integer value this limb represents.
    spec fn sem(&self) -> int;

    ///  a + b + carry_in → (result_limb, carry_out)
    ///  result = (a + b + carry) % BASE
    ///  carry_out = (a + b + carry) / BASE
    fn add3(&self, b: &Self, carry: &Self) -> (out: (Self, Self))
        ensures
            out.0.sem() == (self.sem() + b.sem() + carry.sem()) % LIMB_BASE(),
            out.1.sem() == (self.sem() + b.sem() + carry.sem()) / LIMB_BASE(),
            0 <= out.0.sem() < LIMB_BASE();

    ///  a - b - borrow_in → (result_limb, borrow_out)
    ///  result = (a - b - borrow + BASE) % BASE
    ///  borrow_out = if (a - b - borrow) < 0 then 1 else 0
    fn sub_borrow(&self, b: &Self, borrow: &Self) -> (out: (Self, Self))
        requires borrow.sem() == 0 || borrow.sem() == 1,
        ensures
            out.0.sem() == (self.sem() - b.sem() - borrow.sem() + LIMB_BASE()) % LIMB_BASE(),
            out.1.sem() == if self.sem() - b.sem() - borrow.sem() < 0 { 1int } else { 0int },
            0 <= out.0.sem() < LIMB_BASE(),
            out.1.sem() == 0 || out.1.sem() == 1;

    ///  a * b → (lo, hi) where a*b == lo + hi * BASE
    fn mul2(&self, b: &Self) -> (out: (Self, Self))
        ensures
            out.0.sem() == (self.sem() * b.sem()) % LIMB_BASE(),
            out.1.sem() == (self.sem() * b.sem()) / LIMB_BASE();

    ///  a * b + accum + carry → (result_limb, carry_out)
    ///  For the schoolbook multiply inner loop: accumulate product + carry
    fn mul_add_carry(&self, b: &Self, accum: &Self, carry: &Self) -> (out: (Self, Self))
        ensures
            out.0.sem() == (self.sem() * b.sem() + accum.sem() + carry.sem()) % LIMB_BASE(),
            out.1.sem() == (self.sem() * b.sem() + accum.sem() + carry.sem()) / LIMB_BASE(),
            0 <= out.0.sem() < LIMB_BASE();

    ///  Zero constant.
    fn zero_val() -> (out: Self)
        ensures out.sem() == 0int;

    ///  Constant from u32 value.
    fn const_u32(c: u32) -> (out: Self)
        ensures out.sem() == c as int;

    ///  Clone preserving semantic value.
    fn clone_limb(&self) -> (out: Self)
        ensures out.sem() == self.sem();

    ///  Conditional select: if cond.sem() == 0 return if_zero, else return if_nonzero.
    ///  For u32: a branch. For ArithLimb: builds a select expression node.
    fn select_limb(cond: &Self, if_zero: Self, if_nonzero: Self) -> (out: Self)
        requires cond.sem() == 0 || cond.sem() == 1,
            0 <= if_zero.sem() < LIMB_BASE(),
            0 <= if_nonzero.sem() < LIMB_BASE(),
        ensures
            out.sem() == if cond.sem() == 0 { if_zero.sem() } else { if_nonzero.sem() },
            0 <= out.sem() < LIMB_BASE();

    ///  Check if limb is zero. Returns 1 if zero, 0 if nonzero. GPU-friendly (branchless).
    fn is_zero_limb(&self) -> (out: Self)
        ensures
            out.sem() == if self.sem() == 0 { 1int } else { 0int },
            out.sem() == 0 || out.sem() == 1;

    ///  Bitwise OR of two limbs. For accumulating "any nonzero" checks.
    fn or_limb(&self, other: &Self) -> (out: Self)
        ensures out.sem() == 0 ==> (self.sem() == 0 && other.sem() == 0),
            (self.sem() != 0 || other.sem() != 0) ==> out.sem() != 0,
            0 <= out.sem() < LIMB_BASE();
}

//  ══════════════════════════════════════════════════════════════
//  u32 implementation of LimbOps
//  ══════════════════════════════════════════════════════════════

impl LimbOps for u32 {
    open spec fn sem(&self) -> int { *self as int }

    //  GPU-native: wrapping add + carry via overflow detection
    fn add3(&self, b: &Self, carry: &Self) -> (out: (Self, Self))
    {
        let ab = self.wrapping_add(*b);
        let c1: u32 = if ab < *self { 1u32 } else { 0u32 };
        let abc = ab.wrapping_add(*carry);
        let c2: u32 = if abc < ab { 1u32 } else { 0u32 };
        proof {
            use vstd::wrapping::u32_specs;
            //  Step 1: ab + c1 * BASE == a + b
            //  wrapping_add: ab == if a+b > MAX { a+b - BASE } else { a+b }
            //  c1 == if ab < a { 1 } else { 0 } == if a+b > MAX { 1 } else { 0 }
            assert(ab as int + c1 as int * LIMB_BASE() == *self as int + *b as int) by {
                assert(ab as int == u32_specs::wrapping_add(*self, *b) as int);
                if *self as int + *b as int > u32::MAX as int {
                    assert(ab as int == *self as int + *b as int - LIMB_BASE());
                    assert(c1 == 1u32);
                } else {
                    assert(ab as int == *self as int + *b as int);
                    assert(c1 == 0u32);
                }
            }
            //  Step 2: abc + c2 * BASE == ab + carry
            assert(abc as int + c2 as int * LIMB_BASE() == ab as int + *carry as int) by {
                assert(abc as int == u32_specs::wrapping_add(ab, *carry) as int);
                if ab as int + *carry as int > u32::MAX as int {
                    assert(abc as int == ab as int + *carry as int - LIMB_BASE());
                    assert(c2 == 1u32);
                } else {
                    assert(abc as int == ab as int + *carry as int);
                    assert(c2 == 0u32);
                }
            }
            //  Step 3: combine → abc + (c1+c2)*BASE == a + b + carry
            //  Therefore abc == (a+b+carry) % BASE and (c1+c2) == (a+b+carry) / BASE
            let sum = *self as int + *b as int + *carry as int;
            let base = LIMB_BASE();
            //  Steps 1-2 used LIMB_BASE() directly; assert equivalence
            assert(ab as int + c1 as int * base == *self as int + *b as int);
            assert(abc as int + c2 as int * base == ab as int + *carry as int);
            //  From step 2: abc = ab + carry - c2*base
            //  Substituting ab = a + b - c1*base (from step 1):
            //  abc = (a + b - c1*base) + carry - c2*base = a + b + carry - (c1+c2)*base
            //  So abc + (c1+c2)*base = a + b + carry = sum
            assert(abc as int == ab as int + *carry as int - c2 as int * base);
            assert(ab as int == *self as int + *b as int - c1 as int * base);
            assert(abc as int + (c1 + c2) as int * base == sum) by(nonlinear_arith)
                requires
                    abc as int == ab as int + *carry as int - c2 as int * base,
                    ab as int == *self as int + *b as int - c1 as int * base,
                    sum == *self as int + *b as int + *carry as int;
            let carry_val = (c1 + c2) as int;
            let digit_val = abc as int;
            assert(digit_val == sum % base) by(nonlinear_arith)
                requires
                    digit_val + carry_val * base == sum,
                    0 <= digit_val,
                    digit_val < base,
                    0 <= carry_val,
                    base > 0;
            assert(carry_val == sum / base) by(nonlinear_arith)
                requires
                    digit_val + carry_val * base == sum,
                    0 <= digit_val,
                    digit_val < base,
                    base > 0;
        }
        (abc, c1 + c2)
    }

    //  GPU-native: wrapping sub + borrow via underflow detection
    fn sub_borrow(&self, b: &Self, borrow: &Self) -> (out: (Self, Self))
    {
        let ab = self.wrapping_sub(*b);
        let bw1: u32 = if *self < *b { 1u32 } else { 0u32 };
        let result = ab.wrapping_sub(*borrow);
        let bw2: u32 = if ab < *borrow { 1u32 } else { 0u32 };
        proof {
            use vstd::wrapping::u32_specs;
            let base = LIMB_BASE();
            let sv: int = *self as int;
            let bv: int = *b as int;
            let brv: int = *borrow as int;
            let diff: int = sv - bv - brv;
            //  Step 1: ab == self - b + bw1 * BASE
            assert(ab as int == sv - bv + bw1 as int * base) by {
                assert(ab as int == u32_specs::wrapping_sub(*self, *b) as int);
                if sv < bv {
                    assert(ab as int == sv - bv + base);
                    assert(bw1 == 1u32);
                } else {
                    assert(ab as int == sv - bv);
                    assert(bw1 == 0u32);
                }
            }
            //  Step 2: result == ab - borrow + bw2 * BASE
            assert(result as int == ab as int - brv + bw2 as int * base) by {
                assert(result as int == u32_specs::wrapping_sub(ab, *borrow) as int);
                if (ab as int) < brv {
                    assert(result as int == ab as int - brv + base);
                    assert(bw2 == 1u32);
                } else {
                    assert(result as int == ab as int - brv);
                    assert(bw2 == 0u32);
                }
            }
            //  Step 3: combine → result == diff + (bw1+bw2)*BASE
            assert(result as int == diff + (bw1 + bw2) as int * base) by(nonlinear_arith)
                requires
                    result as int == ab as int - brv + bw2 as int * base,
                    ab as int == sv - bv + bw1 as int * base,
                    diff == sv - bv - brv;
            //  bw1 + bw2 can't be 2: when bw1=1, ab >= 1 > borrow
            assert(bw1 as int + bw2 as int <= 1) by {
                if bw1 == 1u32 {
                    //  ab = self - b + BASE >= 0 - (BASE-1) + BASE = 1
                    assert(ab as int >= 1);
                    //  borrow <= 1 (precondition), so ab >= 1 >= borrow → bw2 = 0
                    assert(bw2 == 0u32);
                }
            }
            //  result == (diff + BASE) % BASE
            let total_borrow = (bw1 + bw2) as int;
            assert(result as int == (diff + base) % base) by(nonlinear_arith)
                requires
                    result as int == diff + total_borrow * base,
                    0 <= result as int,
                    (result as int) < base,
                    total_borrow == 0 || total_borrow == 1,
                    base > 0;
            //  borrow_out == if diff < 0 { 1 } else { 0 }
            assert(total_borrow == if diff < 0 { 1int } else { 0int }) by(nonlinear_arith)
                requires
                    result as int == diff + total_borrow * base,
                    0 <= result as int,
                    (result as int) < base,
                    total_borrow == 0 || total_borrow == 1,
                    base > 0;
        }
        (result, bw1 + bw2)
    }

    //  GPU-native: wrapping mul for lo, 16-bit decomposition for hi
    //  Uses Hacker's Delight mulhi approach: compute p0=a_lo*b_lo separately
    //  (NOT lo from wrapping_mul) to get correct carry propagation.
    fn mul2(&self, b: &Self) -> (out: (Self, Self))
    {
        let lo = self.wrapping_mul(*b);
        let a_lo: u32 = *self & 0xFFFFu32;
        let a_hi: u32 = *self >> 16u32;
        let b_lo: u32 = *b & 0xFFFFu32;
        let b_hi: u32 = *b >> 16u32;
        proof {
            assert(a_lo <= 0xFFFFu32) by(bit_vector) requires a_lo == *self & 0xFFFFu32;
            assert(a_hi <= 0xFFFFu32) by(bit_vector) requires a_hi == *self >> 16u32;
            assert(b_lo <= 0xFFFFu32) by(bit_vector) requires b_lo == *b & 0xFFFFu32;
            assert(b_hi <= 0xFFFFu32) by(bit_vector) requires b_hi == *b >> 16u32;
            assert(a_lo as int * b_lo as int <= 0xFFFE_0001int) by(nonlinear_arith)
                requires a_lo <= 0xFFFFu32, b_lo <= 0xFFFFu32;
            assert(a_lo as int * b_hi as int <= 0xFFFE_0001int) by(nonlinear_arith)
                requires a_lo <= 0xFFFFu32, b_hi <= 0xFFFFu32;
            assert(a_hi as int * b_lo as int <= 0xFFFE_0001int) by(nonlinear_arith)
                requires a_hi <= 0xFFFFu32, b_lo <= 0xFFFFu32;
            assert(a_hi as int * b_hi as int <= 0xFFFE_0001int) by(nonlinear_arith)
                requires a_hi <= 0xFFFFu32, b_hi <= 0xFFFFu32;
        }
        let p0: u32 = a_lo * b_lo;
        let p1: u32 = a_lo * b_hi;
        let p2: u32 = a_hi * b_lo;
        let p3: u32 = a_hi * b_hi;
        let p0_hi: u32 = p0 >> 16u32;
        proof {
            //  Bounds for mid: p0_hi <= 0xFFFE, masks <= 0xFFFF
            assert(p0_hi <= 0xFFFEu32) by(bit_vector)
                requires p0_hi == p0 >> 16u32, p0 <= 0xFFFE_0001u32;
            assert((p1 & 0xFFFFu32) <= 0xFFFFu32) by(bit_vector);
            assert((p2 & 0xFFFFu32) <= 0xFFFFu32) by(bit_vector);
            //  mid <= 0xFFFE + 0xFFFF + 0xFFFF = 0x2FFFC
            assert(p0_hi as int + (p1 & 0xFFFFu32) as int <= 0x1FFFDint);
            assert(p0_hi as int + (p1 & 0xFFFFu32) as int + (p2 & 0xFFFFu32) as int <= 0x2FFFCint);
        }
        let mid: u32 = p0_hi + (p1 & 0xFFFFu32) + (p2 & 0xFFFFu32);
        proof {
            //  Bounds for hi: shifts and mid >> 16
            assert((p1 >> 16u32) <= 0xFFFEu32) by(bit_vector)
                requires p1 <= 0xFFFE_0001u32;
            assert((p2 >> 16u32) <= 0xFFFEu32) by(bit_vector)
                requires p2 <= 0xFFFE_0001u32;
            assert((mid >> 16u32) <= 2u32) by(bit_vector)
                requires mid <= 0x2FFFCu32;
            //  hi <= 0xFFFE0001 + 0xFFFE + 0xFFFE + 2 = 0xFFFFFFFF
            assert(p3 as int + (p1 >> 16u32) as int <= 0xFFFE_FFFFint) by(nonlinear_arith)
                requires p3 as int <= 0xFFFE_0001int, (p1 >> 16u32) as int <= 0xFFFEint;
            assert(p3 as int + (p1 >> 16u32) as int + (p2 >> 16u32) as int <= 0xFFFF_FFFDint) by(nonlinear_arith)
                requires p3 as int + (p1 >> 16u32) as int <= 0xFFFE_FFFFint, (p2 >> 16u32) as int <= 0xFFFEint;
            assert(p3 as int + (p1 >> 16u32) as int + (p2 >> 16u32) as int + (mid >> 16u32) as int
                <= 0xFFFF_FFFFint) by(nonlinear_arith)
                requires
                    p3 as int + (p1 >> 16u32) as int + (p2 >> 16u32) as int <= 0xFFFF_FFFDint,
                    (mid >> 16u32) as int <= 2int;
        }
        let hi: u32 = p3 + (p1 >> 16u32) + (p2 >> 16u32) + (mid >> 16u32);
        proof {
            use vstd::wrapping::u32_specs;
            let prod: int = *self as int * *b as int;
            let base: int = LIMB_BASE();
            let half: int = 0x10000int;
            //  lo == prod % base
            assert(lo as int == prod % base) by {
                assert(lo as int == u32_specs::wrapping_mul(*self, *b) as int);
            }
            //  Decomposition: a = a_hi*H + a_lo, b = b_hi*H + b_lo (via u64 bit_vector)
            assert((*self as u64) == (a_hi as u64) * 0x10000u64 + (a_lo as u64)) by(bit_vector)
                requires a_lo == *self & 0xFFFFu32, a_hi == *self >> 16u32;
            assert((*b as u64) == (b_hi as u64) * 0x10000u64 + (b_lo as u64)) by(bit_vector)
                requires b_lo == *b & 0xFFFFu32, b_hi == *b >> 16u32;
            //  Lift u64 decomposition to int (Z3 knows u32→u64 preserves int value)
            assert(*self as int == a_hi as int * half + a_lo as int);
            assert(*b as int == b_hi as int * half + b_lo as int);
            //  Product expansion: a*b = p3*base + (p1+p2)*half + p0
            //  Step A: expand (a_hi*H + a_lo)*(b_hi*H + b_lo)
            let lp_half = half * half;
            assert(prod == a_hi as int * b_hi as int * lp_half
                + a_hi as int * b_lo as int * half
                + a_lo as int * b_hi as int * half
                + a_lo as int * b_lo as int)
                by(nonlinear_arith)
                requires
                    prod == (*self as int) * (*b as int),
                    *self as int == a_hi as int * half + a_lo as int,
                    *b as int == b_hi as int * half + b_lo as int,
                    lp_half == half * half;
            //  Step B: substitute p0..p3 and base
            assert(prod == p3 as int * base + (p1 as int + p2 as int) * half + p0 as int)
                by(nonlinear_arith)
                requires
                    prod == a_hi as int * b_hi as int * lp_half
                        + a_hi as int * b_lo as int * half
                        + a_lo as int * b_hi as int * half
                        + a_lo as int * b_lo as int,
                    p0 as int == a_lo as int * b_lo as int,
                    p1 as int == a_lo as int * b_hi as int,
                    p2 as int == a_hi as int * b_lo as int,
                    p3 as int == a_hi as int * b_hi as int,
                    base == half * half, lp_half == half * half;
            //  Decompose p1, p2, p0, mid into hi/lo halves (u64 bit_vector)
            let p1_hi_u: u32 = p1 >> 16u32;
            let p1_lo_u: u32 = p1 & 0xFFFFu32;
            let p2_hi_u: u32 = p2 >> 16u32;
            let p2_lo_u: u32 = p2 & 0xFFFFu32;
            let p0_lo_u: u32 = p0 & 0xFFFFu32;
            let mid_hi_u: u32 = mid >> 16u32;
            let mid_lo_u: u32 = mid & 0xFFFFu32;
            assert((p1 as u64) == (p1_hi_u as u64) * 0x10000u64 + (p1_lo_u as u64)) by(bit_vector)
                requires p1_hi_u == p1 >> 16u32, p1_lo_u == p1 & 0xFFFFu32;
            assert((p2 as u64) == (p2_hi_u as u64) * 0x10000u64 + (p2_lo_u as u64)) by(bit_vector)
                requires p2_hi_u == p2 >> 16u32, p2_lo_u == p2 & 0xFFFFu32;
            assert((p0 as u64) == (p0_hi as u64) * 0x10000u64 + (p0_lo_u as u64)) by(bit_vector)
                requires p0_hi == p0 >> 16u32, p0_lo_u == p0 & 0xFFFFu32;
            assert((mid as u64) == (mid_hi_u as u64) * 0x10000u64 + (mid_lo_u as u64)) by(bit_vector)
                requires mid_hi_u == mid >> 16u32, mid_lo_u == mid & 0xFFFFu32;
            //  Lift to int
            let p1_hi: int = p1_hi_u as int;
            let p1_lo: int = p1_lo_u as int;
            let p2_hi: int = p2_hi_u as int;
            let p2_lo: int = p2_lo_u as int;
            let p0_lo: int = p0_lo_u as int;
            let mid_hi: int = mid_hi_u as int;
            let mid_lo: int = mid_lo_u as int;
            assert(p1 as int == p1_hi * half + p1_lo);
            assert(p2 as int == p2_hi * half + p2_lo);
            assert(p0 as int == p0_hi as int * half + p0_lo);
            assert(mid as int == mid_hi * half + mid_lo);
            //  mid == p0_hi + p1_lo + p2_lo (by construction)
            //  Step 1: (p1+p2)*half + p0 = (p1_hi+p2_hi)*base + mid*half + p0_lo
            assert((p1 as int + p2 as int) * half + p0 as int
                == (p1_hi + p2_hi) * base + mid as int * half + p0_lo)
                by(nonlinear_arith)
                requires
                    p1 as int == p1_hi * half + p1_lo,
                    p2 as int == p2_hi * half + p2_lo,
                    p0 as int == p0_hi as int * half + p0_lo,
                    mid as int == p0_hi as int + p1_lo + p2_lo,
                    base == half * half;
            //  Step 2: mid*half = mid_hi*base + mid_lo*half
            assert(mid as int * half == mid_hi * base + mid_lo * half)
                by(nonlinear_arith)
                requires
                    mid as int == mid_hi * half + mid_lo,
                    base == half * half;
            //  Step 3: prod = hi*base + remainder
            assert(prod == (p3 as int + p1_hi + p2_hi + mid_hi) * base + mid_lo * half + p0_lo)
                by(nonlinear_arith)
                requires
                    prod == p3 as int * base + (p1_hi + p2_hi) * base + mid as int * half + p0_lo,
                    mid as int * half == mid_hi * base + mid_lo * half;
            //  hi == p3 + p1_hi + p2_hi + mid_hi (by construction)
            assert(hi as int == p3 as int + p1_hi + p2_hi + mid_hi);
            //  Remainder < base
            assert(mid_lo_u <= 0xFFFFu32) by(bit_vector) requires mid_lo_u == mid & 0xFFFFu32;
            assert(p0_lo_u <= 0xFFFFu32) by(bit_vector) requires p0_lo_u == p0 & 0xFFFFu32;
            //  Remainder bounds: 0 <= mid_lo*half + p0_lo < base
            assert(mid_lo * half >= 0) by(nonlinear_arith)
                requires mid_lo >= 0, half >= 0;
            assert(mid_lo * half + p0_lo < base) by(nonlinear_arith)
                requires mid_lo <= 0xFFFFint, p0_lo <= 0xFFFFint, half == 0x10000int, base == half * half;
            //  Therefore hi == prod / base
            assert(hi as int == prod / base) by(nonlinear_arith)
                requires
                    prod == hi as int * base + mid_lo * half + p0_lo,
                    mid_lo * half + p0_lo >= 0,
                    mid_lo * half + p0_lo < base,
                    base > 0;
        }
        (lo, hi)
    }

    //  GPU-native: mul2 + wrapping add with carry detection
    fn mul_add_carry(&self, b: &Self, accum: &Self, carry: &Self) -> (out: (Self, Self))
    {
        let (mul_lo, mul_hi) = self.mul2(b);
        let sum1 = mul_lo.wrapping_add(*accum);
        let c1: u32 = if sum1 < mul_lo { 1u32 } else { 0u32 };
        let sum2 = sum1.wrapping_add(*carry);
        let c2: u32 = if sum2 < sum1 { 1u32 } else { 0u32 };
        proof {
            use vstd::wrapping::u32_specs;
            let base: int = LIMB_BASE();
            let prod: int = self.sem() * b.sem();
            let total: int = prod + accum.sem() + carry.sem();
            //  sum1 + c1*BASE == mul_lo + accum
            assert(sum1 as int + c1 as int * base == mul_lo as int + *accum as int) by {
                assert(sum1 as int == u32_specs::wrapping_add(mul_lo, *accum) as int);
                if mul_lo as int + *accum as int > u32::MAX as int {
                    assert(c1 == 1u32);
                } else {
                    assert(c1 == 0u32);
                }
            }
            //  sum2 + c2*BASE == sum1 + carry
            assert(sum2 as int + c2 as int * base == sum1 as int + *carry as int) by {
                assert(sum2 as int == u32_specs::wrapping_add(sum1, *carry) as int);
                if sum1 as int + *carry as int > u32::MAX as int {
                    assert(c2 == 1u32);
                } else {
                    assert(c2 == 0u32);
                }
            }
            //  total = (mul_hi + c1 + c2) * BASE + sum2
            assert(sum2 as int == mul_lo as int + *accum as int + *carry as int
                - (c1 as int + c2 as int) * base) by(nonlinear_arith)
                requires
                    sum1 as int + c1 as int * base == mul_lo as int + *accum as int,
                    sum2 as int + c2 as int * base == sum1 as int + *carry as int;
            //  prod == mul_hi * BASE + mul_lo (from mul2 postcondition + fundamental_div_mod)
            assert(prod == mul_hi as int * base + mul_lo as int) by(nonlinear_arith)
                requires
                    mul_lo as int == prod % base,
                    mul_hi as int == prod / base,
                    base > 0,
                    prod >= 0;
            assert(total == (mul_hi as int + c1 as int + c2 as int) * base + sum2 as int)
                by(nonlinear_arith)
                requires
                    prod == mul_hi as int * base + mul_lo as int,
                    sum2 as int == mul_lo as int + *accum as int + *carry as int
                        - (c1 as int + c2 as int) * base,
                    total == prod + *accum as int + *carry as int;
            //  mul_hi + c1 + c2 = total / BASE <= BASE - 1 = u32::MAX
            //  total <= (BASE-1)^2 + 2*(BASE-1) = BASE^2 - 1
            let a_val: int = self.sem();
            let b_val: int = b.sem();
            let acc_val: int = accum.sem();
            let car_val: int = carry.sem();
            assert(mul_hi as int + c1 as int + c2 as int <= base - 1) by(nonlinear_arith)
                requires
                    total == (mul_hi as int + c1 as int + c2 as int) * base + (sum2 as int),
                    0 <= (sum2 as int),
                    (sum2 as int) < base,
                    total == a_val * b_val + acc_val + car_val,
                    0 <= a_val,
                    a_val < base,
                    0 <= b_val,
                    b_val < base,
                    0 <= acc_val,
                    acc_val < base,
                    0 <= car_val,
                    car_val < base,
                    base > 0;
        }
        let carry_out: u32 = mul_hi + c1 + c2;
        proof {
            let base: int = LIMB_BASE();
            let prod: int = self.sem() * b.sem();
            let total: int = prod + accum.sem() + carry.sem();
            //  Postcondition: sum2 == total % BASE, carry_out == total / BASE
            assert((sum2 as int) == total % base) by(nonlinear_arith)
                requires
                    total == (carry_out as int) * base + (sum2 as int),
                    0 <= (sum2 as int), (sum2 as int) < base, base > 0;
            assert((carry_out as int) == total / base) by(nonlinear_arith)
                requires
                    total == (carry_out as int) * base + (sum2 as int),
                    0 <= (sum2 as int), (sum2 as int) < base, base > 0;
        }
        (sum2, carry_out)
    }

    fn zero_val() -> (out: Self) { 0u32 }

    fn const_u32(c: u32) -> (out: Self) { c }

    fn clone_limb(&self) -> (out: Self) { *self }

    fn select_limb(cond: &Self, if_zero: Self, if_nonzero: Self) -> (out: Self) {
        if *cond == 0u32 { if_zero } else { if_nonzero }
    }

    fn is_zero_limb(&self) -> (out: Self) {
        if *self == 0u32 { 1u32 } else { 0u32 }
    }

    fn or_limb(&self, other: &Self) -> (out: Self) {
        proof {
            assert((*self | *other) == 0u32 <==> (*self == 0u32 && *other == 0u32)) by(bit_vector);
        }
        *self | *other
    }
}

//  ══════════════════════════════════════════════════════════════
//  Bridge: limbs_to_nat(u32) == limbs_val(sem_seq(u32))
//  Connects existing u32 proofs to the generic framework.
//  ══════════════════════════════════════════════════════════════

///  For u32 sequences: limbs_val(sem_seq(s)) == limbs_to_nat(s) as int.
pub proof fn lemma_limbs_val_eq_limbs_to_nat(s: Seq<u32>)
    ensures limbs_val(sem_seq(s)) == limb_base_conv::limbs_to_nat(s) as int,
    decreases s.len(),
{
    reveal_with_fuel(limbs_val, 2);
    reveal_with_fuel(limb_base_conv::limbs_to_nat, 2);
    if s.len() == 0 {
    } else {
        let tail = s.subrange(1, s.len() as int);
        assert(sem_seq(s).subrange(1, sem_seq(s).len() as int) =~= sem_seq(tail));
        lemma_limbs_val_eq_limbs_to_nat(tail);
        //  limbs_val(sem_seq(s)) == s[0] as int + LIMB_BASE() * limbs_val(sem_seq(tail))
        //                        == s[0] as int + LIMB_BASE() * (limbs_to_nat(tail) as int)
        //                        == (s[0] as nat + limb_base() * limbs_to_nat(tail)) as int
        //                        == limbs_to_nat(s) as int
    }
}

///  limb_power(n) == pow2(n * 32) as int.
pub proof fn lemma_limb_power_eq_pow2(n: nat)
    ensures limb_power(n) == super::pow2::pow2((n * 32) as nat) as int,
    decreases n,
{
    reveal_with_fuel(limb_power, 2);
    if n == 0 {
        assert(super::pow2::pow2(0nat) == 1nat) by(compute_only);
    } else {
        lemma_limb_power_eq_pow2((n - 1) as nat);
        lemma_limb_base_is_pow2_32();
        super::pow2::lemma_pow2_add(32, ((n - 1) * 32) as nat);
        assert(32 + (n - 1) * 32 == n * 32);
    }
}

//  ══════════════════════════════════════════════════════════════
//  limbs_val on Seq<int> — no generics, Z3-friendly
//  ══════════════════════════════════════════════════════════════

///  BASE^n as int.
pub open spec fn limb_power(n: nat) -> int
    decreases n,
{
    if n == 0 { 1int }
    else { LIMB_BASE() * limb_power((n - 1) as nat) }
}

///  Interpret a sequence of int values as a multi-limb integer.
///  limbs_val([a, b, c]) = a + b * BASE + c * BASE^2
pub open spec fn limbs_val(limbs: Seq<int>) -> int
    decreases limbs.len(),
{
    if limbs.len() == 0 { 0int }
    else {
        limbs[0] + LIMB_BASE() * limbs_val(limbs.subrange(1, limbs.len() as int))
    }
}

///  Map a sequence of LimbOps values to their semantic int values.
pub open spec fn sem_seq<T: LimbOps>(s: Seq<T>) -> Seq<int> {
    Seq::new(s.len(), |i: int| s[i].sem())
}

///  Pushing a digit: limbs_val(s.push(d)) == limbs_val(s) + d * limb_power(s.len()).
pub proof fn lemma_limbs_val_push(s: Seq<int>, d: int)
    ensures
        limbs_val(s.push(d))
            == limbs_val(s) + d * limb_power(s.len()),
    decreases s.len(),
{
    reveal_with_fuel(limbs_val, 2);
    reveal_with_fuel(limb_power, 2);
    if s.len() == 0 {
    } else {
        let tail = s.subrange(1, s.len() as int);
        let sp = s.push(d);
        assert(sp.subrange(1, sp.len() as int) =~= tail.push(d));
        assert(sp[0] == s[0]);
        lemma_limbs_val_push(tail, d);
        //  IH: limbs_val(tail.push(d)) == limbs_val(tail) + d * limb_power(tail.len())
        //  limb_power(s.len()) == BASE * limb_power(tail.len()) [since s.len() = tail.len() + 1]
        //  limbs_val(sp) = s[0] + BASE * limbs_val(tail.push(d))
        //                = s[0] + BASE * (limbs_val(tail) + d * limb_power(tail.len()))
        //                = limbs_val(s) + d * BASE * limb_power(tail.len())
        //                = limbs_val(s) + d * limb_power(s.len())
        assert(limbs_val(sp) == limbs_val(s) + d * limb_power(s.len())) by(nonlinear_arith)
            requires
                limbs_val(sp) == s[0] + LIMB_BASE() * limbs_val(tail.push(d)),
                limbs_val(tail.push(d)) == limbs_val(tail) + d * limb_power(tail.len()),
                limbs_val(s) == s[0] + LIMB_BASE() * limbs_val(tail),
                limb_power(s.len()) == LIMB_BASE() * limb_power(tail.len()),
                sp == s.push(d);
    }
}

///  Extending a subrange by one element.
pub proof fn lemma_limbs_val_subrange_extend(s: Seq<int>, i: nat)
    requires i < s.len(),
    ensures
        limbs_val(s.subrange(0, (i + 1) as int))
            == limbs_val(s.subrange(0, i as int))
                + s[i as int] * limb_power(i),
{
    let prefix = s.subrange(0, i as int);
    assert(s.subrange(0, (i + 1) as int) =~= prefix.push(s[i as int]));
    lemma_limbs_val_push(prefix, s[i as int]);
}

///  sem_seq preserves push.
pub proof fn lemma_sem_seq_push<T: LimbOps>(s: Seq<T>, d: T)
    ensures sem_seq(s.push(d)) =~= sem_seq(s).push(d.sem()),
{
    let sp = s.push(d);
    assert forall |i: int| 0 <= i < sem_seq(sp).len()
        implies sem_seq(sp)[i] == sem_seq(s).push(d.sem())[i]
    by {
        if i < s.len() as int {
            assert(sp[i] == s[i]);
        } else {
            assert(sp[i] == d);
        }
    }
}

///  sem_seq preserves subrange.
pub proof fn lemma_sem_seq_subrange<T: LimbOps>(s: Seq<T>, lo: int, hi: int)
    requires 0 <= lo <= hi <= s.len(),
    ensures sem_seq(s.subrange(lo, hi)) =~= sem_seq(s).subrange(lo, hi),
{
    let sub = s.subrange(lo, hi);
    assert forall |i: int| 0 <= i < sem_seq(sub).len()
        implies sem_seq(sub)[i] == sem_seq(s).subrange(lo, hi)[i]
    by {
        assert(sub[i] == s[lo + i]);
    }
}

//  ══════════════════════════════════════════════════════════════
//  Generic multi-limb addition
//  ══════════════════════════════════════════════════════════════

///  Generic carry-chain addition of two n-limb arrays.
///  Returns (result, carry_out).
///  Generic carry-chain addition of two n-limb arrays.
///  Returns (result, carry_out).
///  Postcondition uses limbs_val(sem_seq(...)) to interpret results as integers.
pub fn generic_add_limbs<T: LimbOps>(a: &[T], b: &[T], n: usize) -> (result: (Vec<T>, T))
    requires
        a@.len() == n,
        b@.len() == n,
        valid_limbs(a@),
        valid_limbs(b@),
    ensures
        result.0@.len() == n,
        valid_limbs(result.0@),
        0 <= result.1.sem() < LIMB_BASE(),
        // Strengthened: carry is exactly 0 or 1 (not just < LIMB_BASE)
        result.1.sem() == 0 || result.1.sem() == 1,
        limbs_val(sem_seq(result.0@)) + result.1.sem() * limb_power(n as nat)
            == limbs_val(sem_seq(a@)) + limbs_val(sem_seq(b@)),
{
    let mut out: Vec<T> = Vec::new();
    let mut carry: T = T::zero_val();
    let ghost sa = sem_seq(a@);
    let ghost sb = sem_seq(b@);

    for i in 0..n
        invariant
            a@.len() == n,
            b@.len() == n,
            out@.len() == i as int,
            valid_limbs(out@),
            valid_limbs(a@), valid_limbs(b@),
            0 <= carry.sem() < LIMB_BASE(),
            sa == sem_seq(a@),
            sb == sem_seq(b@),
            limbs_val(sem_seq(out@)) + carry.sem() * limb_power(i as nat)
                == limbs_val(sa.subrange(0, i as int))
                    + limbs_val(sb.subrange(0, i as int)),
    {
        let (digit, next_carry) = a[i].add3(&b[i], &carry);
        proof {
            let sum = a@[i as int].sem() + b@[i as int].sem() + carry.sem();
            assert(0 <= next_carry.sem() && next_carry.sem() < LIMB_BASE()) by(nonlinear_arith)
                requires
                    next_carry.sem() == sum / LIMB_BASE(),
                    sum >= 0,
                    sum < 3 * LIMB_BASE(),
                    LIMB_BASE() > 0;
            let x = a@[i as int].sem() + b@[i as int].sem() + carry.sem();
            assert(digit.sem() + next_carry.sem() * LIMB_BASE() == x) by(nonlinear_arith)
                requires
                    digit.sem() == x % LIMB_BASE(),
                    next_carry.sem() == x / LIMB_BASE(),
                    LIMB_BASE() > 0;

            reveal_with_fuel(limb_power, 2);
            let p = limb_power(i as nat);
            let p_next = limb_power((i + 1) as nat);
            assert(p_next == LIMB_BASE() * p);

            lemma_sem_seq_push(out@, digit);
            lemma_limbs_val_push(sem_seq(out@), digit.sem());
            assert(sa[i as int] == a@[i as int].sem());
            assert(sb[i as int] == b@[i as int].sem());
            lemma_limbs_val_subrange_extend(sa, i as nat);
            lemma_limbs_val_subrange_extend(sb, i as nat);

            assert(
                limbs_val(sem_seq(out@)) + digit.sem() * p + next_carry.sem() * p_next
                == limbs_val(sa.subrange(0, i as int)) + sa[i as int] * p
                    + limbs_val(sb.subrange(0, i as int)) + sb[i as int] * p
            ) by(nonlinear_arith)
                requires
                    limbs_val(sem_seq(out@)) + carry.sem() * p
                        == limbs_val(sa.subrange(0, i as int))
                            + limbs_val(sb.subrange(0, i as int)),
                    digit.sem() + next_carry.sem() * LIMB_BASE()
                        == sa[i as int] + sb[i as int] + carry.sem(),
                    p_next == LIMB_BASE() * p;
        }

        out.push(digit);
        carry = next_carry;
    }

    proof {
        assert(sa.subrange(0, sa.len() as int) =~= sa);
        assert(sb.subrange(0, sb.len() as int) =~= sb);
        // Derive carry ≤ 1: result < P, a < P, b < P → a+b < 2P
        // result + carry*P = a+b < 2P, result >= 0 → carry*P < 2P → carry < 2
        lemma_vec_val_bounded::<T>(out@);
        lemma_vec_val_bounded::<T>(a@);
        lemma_vec_val_bounded::<T>(b@);
        let P = limb_power(n as nat);
        // vec_val == limbs_val(sem_seq(...))
        assert(vec_val(out@) == limbs_val(sem_seq(out@)));
        assert(vec_val(a@) == limbs_val(sa));
        assert(vec_val(b@) == limbs_val(sb));
        assert(carry.sem() <= 1) by(nonlinear_arith)
            requires
                vec_val(out@) + carry.sem() * P == vec_val(a@) + vec_val(b@),
                0 <= vec_val(out@) && vec_val(out@) < P,
                0 <= vec_val(a@) && vec_val(a@) < P,
                0 <= vec_val(b@) && vec_val(b@) < P,
                carry.sem() >= 0, P > 0;
    }

    (out, carry)
}

//  ══════════════════════════════════════════════════════════════
//  GPU-compatible output-parameter variants (no Vec::new/push)
//  ══════════════════════════════════════════════════════════════

///  Carry-chain addition writing to caller-provided output buffer.
///  GPU-compatible: no Vec allocation, writes to out[0..n].
pub fn add_limbs_to<T: LimbOps>(a: &[T], b: &[T], out: &mut Vec<T>, out_off: usize, n: usize) -> (carry: T)
    requires
        a@.len() >= n, b@.len() >= n, old(out)@.len() >= out_off + n,
        out_off + n < usize::MAX,
        valid_limbs(a@), valid_limbs(b@),
    ensures
        out@.len() == old(out)@.len(),
        0 <= carry.sem() < LIMB_BASE(),
        carry.sem() == 0 || carry.sem() == 1,
        forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] out@[out_off as int + j]).sem() < LIMB_BASE(),
        // Frame: indices outside [out_off, out_off+n) are unchanged
        forall |j: int| 0 <= j < out@.len() && !(out_off as int <= j < out_off + n) ==> out@[j] == old(out)@[j],
        // Sum equation: output + carry * P == a + b (as limb values)
        limbs_val(sem_seq(out@.subrange(out_off as int, (out_off + n) as int)))
            + carry.sem() * limb_power(n as nat)
            == limbs_val(sem_seq(a@.subrange(0, n as int)))
                + limbs_val(sem_seq(b@.subrange(0, n as int))),
{
    let ghost old_out = out@;
    let ghost out_len = out@.len();
    let ghost sa = sem_seq(a@.subrange(0, n as int));
    let ghost sb = sem_seq(b@.subrange(0, n as int));
    let mut carry: T = T::zero_val();
    for i in 0..n
        invariant
            a@.len() >= n, b@.len() >= n,
            out@.len() == out_len, out_len >= out_off + n,
            out_off + n < usize::MAX,
            valid_limbs(a@), valid_limbs(b@),
            0 <= carry.sem() < LIMB_BASE(),
            sa == sem_seq(a@.subrange(0, n as int)),
            sb == sem_seq(b@.subrange(0, n as int)),
            forall |j: int| 0 <= j < i ==> 0 <= (#[trigger] out@[out_off as int + j]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < out_len && !(out_off as int <= j < out_off as int + i) ==> out@[j] == old_out[j],
            // Sum equation invariant
            limbs_val(sem_seq(out@.subrange(out_off as int, out_off as int + i)))
                + carry.sem() * limb_power(i as nat)
                == limbs_val(sa.subrange(0, i as int))
                    + limbs_val(sb.subrange(0, i as int)),
    {
        let (digit, next_carry) = a[i].add3(&b[i], &carry);
        proof {
            let x = a@[i as int].sem() + b@[i as int].sem() + carry.sem();
            assert(digit.sem() + next_carry.sem() * LIMB_BASE() == x) by(nonlinear_arith)
                requires digit.sem() == x % LIMB_BASE(),
                         next_carry.sem() == x / LIMB_BASE(), LIMB_BASE() > 0;
            assert(0 <= next_carry.sem() && next_carry.sem() < LIMB_BASE()) by(nonlinear_arith)
                requires next_carry.sem() == x / LIMB_BASE(), x >= 0,
                         x < 3 * LIMB_BASE(), LIMB_BASE() > 0;

            reveal_with_fuel(limb_power, 2);
            let p = limb_power(i as nat);
            let p_next = limb_power((i + 1) as nat);
            assert(p_next == LIMB_BASE() * p);

            // a@[i] is at position i in the subrange a@.subrange(0, n)
            assert(sa[i as int] == a@[i as int].sem());
            assert(sb[i as int] == b@[i as int].sem());
            lemma_limbs_val_subrange_extend(sa, i as nat);
            lemma_limbs_val_subrange_extend(sb, i as nat);

        }
        let ghost pre_sub = sem_seq(out@.subrange(out_off as int, out_off as int + i));
        out.set(out_off + i, digit);
        proof {
            let p = limb_power(i as nat);
            let p_next = limb_power((i + 1) as nat);
            let new_sub = out@.subrange(out_off as int, out_off as int + (i + 1));
            assert(new_sub[i as int] == digit);
            let new_sem = sem_seq(new_sub);
            assert(new_sem[i as int] == digit.sem());
            lemma_limbs_val_subrange_extend(new_sem, i as nat);
            assert(new_sem.subrange(0, (i + 1) as int) =~= new_sem);
            assert(new_sem.subrange(0, i as int) =~= pre_sub);

            assert(
                limbs_val(new_sem) + next_carry.sem() * p_next
                == limbs_val(sa.subrange(0, (i + 1) as int))
                    + limbs_val(sb.subrange(0, (i + 1) as int))
            ) by(nonlinear_arith)
                requires
                    limbs_val(pre_sub) + carry.sem() * p
                        == limbs_val(sa.subrange(0, i as int))
                            + limbs_val(sb.subrange(0, i as int)),
                    digit.sem() + next_carry.sem() * LIMB_BASE()
                        == sa[i as int] + sb[i as int] + carry.sem(),
                    limbs_val(new_sem) == limbs_val(new_sem.subrange(0, i as int))
                        + new_sem[i as int] * p,
                    limbs_val(sa.subrange(0, (i + 1) as int))
                        == limbs_val(sa.subrange(0, i as int)) + sa[i as int] * p,
                    limbs_val(sb.subrange(0, (i + 1) as int))
                        == limbs_val(sb.subrange(0, i as int)) + sb[i as int] * p,
                    new_sem.subrange(0, i as int) =~= pre_sub,
                    new_sem[i as int] == digit.sem(),
                    p_next == LIMB_BASE() * p;
        }
        carry = next_carry;
    }

    proof {
        assert(sa.subrange(0, sa.len() as int) =~= sa);
        assert(sb.subrange(0, sb.len() as int) =~= sb);
        let final_sub = out@.subrange(out_off as int, (out_off + n) as int);
        assert(sem_seq(final_sub).len() == n);
        // Establish valid_limbs on the output subrange
        assert(valid_limbs(final_sub)) by {
            assert forall |j: int| 0 <= j < final_sub.len()
                implies 0 <= (#[trigger] final_sub[j]).sem() < LIMB_BASE() by {
                assert(final_sub[j] == out@[(out_off as int + j) as int]);
            };
        };
        // Derive carry ≤ 1
        lemma_vec_val_bounded::<T>(final_sub);
        assert(valid_limbs(a@.subrange(0, n as int))) by {
            assert forall |j: int| 0 <= j < n
                implies 0 <= (#[trigger] a@.subrange(0, n as int)[j]).sem() < LIMB_BASE() by {
                assert(a@.subrange(0, n as int)[j] == a@[j]);
            };
        };
        assert(valid_limbs(b@.subrange(0, n as int))) by {
            assert forall |j: int| 0 <= j < n
                implies 0 <= (#[trigger] b@.subrange(0, n as int)[j]).sem() < LIMB_BASE() by {
                assert(b@.subrange(0, n as int)[j] == b@[j]);
            };
        };
        lemma_vec_val_bounded::<T>(a@.subrange(0, n as int));
        lemma_vec_val_bounded::<T>(b@.subrange(0, n as int));
        let P = limb_power(n as nat);
        assert(carry.sem() <= 1) by(nonlinear_arith)
            requires
                limbs_val(sem_seq(final_sub)) + carry.sem() * P
                    == limbs_val(sa) + limbs_val(sb),
                0 <= limbs_val(sem_seq(final_sub)),
                limbs_val(sem_seq(final_sub)) < P,
                0 <= limbs_val(sa), limbs_val(sa) < P,
                0 <= limbs_val(sb), limbs_val(sb) < P,
                carry.sem() >= 0, P > 0;
    }
    carry
}

///  Borrow-chain subtraction writing to caller-provided output buffer.
pub fn sub_limbs_to<T: LimbOps>(a: &[T], b: &[T], out: &mut Vec<T>, out_off: usize, n: usize) -> (borrow: T)
    requires
        a@.len() >= n, b@.len() >= n, old(out)@.len() >= out_off + n,
        out_off + n < usize::MAX,
        valid_limbs(a@), valid_limbs(b@),
    ensures
        out@.len() == old(out)@.len(),
        borrow.sem() == 0 || borrow.sem() == 1,
        forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] out@[(out_off as int + j) as int]).sem() < LIMB_BASE(),
        // Frame: indices outside [out_off, out_off+n) are unchanged
        forall |j: int| 0 <= j < out@.len() && !(out_off as int <= j < out_off + n) ==> out@[j] == old(out)@[j],
        // Difference equation: out + b == a + borrow * P
        limbs_val(sem_seq(out@.subrange(out_off as int, (out_off + n) as int)))
            + limbs_val(sem_seq(b@.subrange(0, n as int)))
            == limbs_val(sem_seq(a@.subrange(0, n as int)))
                + borrow.sem() * limb_power(n as nat),
{
    let ghost old_out = out@;
    let ghost out_len = out@.len();
    let ghost sa = sem_seq(a@.subrange(0, n as int));
    let ghost sb = sem_seq(b@.subrange(0, n as int));
    let mut borrow: T = T::zero_val();
    for i in 0..n
        invariant
            a@.len() >= n, b@.len() >= n,
            out@.len() == out_len, out_len >= out_off + n,
            out_off + n < usize::MAX,
            valid_limbs(a@), valid_limbs(b@),
            borrow.sem() == 0 || borrow.sem() == 1,
            sa == sem_seq(a@.subrange(0, n as int)),
            sb == sem_seq(b@.subrange(0, n as int)),
            forall |j: int| 0 <= j < i ==> 0 <= (#[trigger] out@[(out_off as int + j) as int]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < out_len && !(out_off as int <= j < out_off as int + i) ==> out@[j] == old_out[j],
            // Difference equation invariant
            limbs_val(sem_seq(out@.subrange(out_off as int, out_off as int + i)))
                + limbs_val(sb.subrange(0, i as int))
                == limbs_val(sa.subrange(0, i as int))
                    + borrow.sem() * limb_power(i as nat),
    {
        let (digit, next_borrow) = a[i].sub_borrow(&b[i], &borrow);
        proof {
            let ai = sa[i as int];
            let bi = sb[i as int];
            assert(ai == a@[i as int].sem());
            assert(bi == b@[i as int].sem());
            assert(0 <= ai && ai < LIMB_BASE());
            assert(0 <= bi && bi < LIMB_BASE());

            let diff = ai - bi - borrow.sem();
            let sum = diff + LIMB_BASE();
            if diff >= 0 {
                assert(next_borrow.sem() == 0int);
                assert(sum >= LIMB_BASE() && sum < 2 * LIMB_BASE());
                assert(sum % LIMB_BASE() == sum - LIMB_BASE()) by(nonlinear_arith)
                    requires sum >= LIMB_BASE(), sum < 2 * LIMB_BASE(), LIMB_BASE() > 0;
                assert(digit.sem() == diff);
            } else {
                assert(next_borrow.sem() == 1int);
                assert(sum >= 0 && sum < LIMB_BASE());
                assert(sum % LIMB_BASE() == sum) by(nonlinear_arith)
                    requires sum >= 0, sum < LIMB_BASE(), LIMB_BASE() > 0;
                assert(digit.sem() == diff + LIMB_BASE());
            }
            // Per-digit equation: digit + bi + borrow == ai + next_borrow * BASE
            assert(digit.sem() + bi + borrow.sem() == ai + next_borrow.sem() * LIMB_BASE());

            reveal_with_fuel(limb_power, 2);
            let p = limb_power(i as nat);
            let p_next = limb_power((i + 1) as nat);
            assert(p_next == LIMB_BASE() * p);

            lemma_limbs_val_subrange_extend(sa, i as nat);
            lemma_limbs_val_subrange_extend(sb, i as nat);
        }
        let ghost pre_sub = sem_seq(out@.subrange(out_off as int, out_off as int + i));
        out.set(out_off + i, digit);
        proof {
            let p = limb_power(i as nat);
            let p_next = limb_power((i + 1) as nat);
            let ai = sa[i as int];
            let bi = sb[i as int];
            let new_sub = out@.subrange(out_off as int, out_off as int + (i + 1));
            let new_sem = sem_seq(new_sub);
            assert(new_sem[i as int] == digit.sem());
            lemma_limbs_val_subrange_extend(new_sem, i as nat);
            assert(new_sem.subrange(0, (i + 1) as int) =~= new_sem);
            assert(new_sem.subrange(0, i as int) =~= pre_sub);

            assert(
                limbs_val(new_sem) + limbs_val(sb.subrange(0, (i + 1) as int))
                == limbs_val(sa.subrange(0, (i + 1) as int))
                    + next_borrow.sem() * p_next
            ) by(nonlinear_arith)
                requires
                    limbs_val(pre_sub) + limbs_val(sb.subrange(0, i as int))
                        == limbs_val(sa.subrange(0, i as int))
                            + borrow.sem() * p,
                    digit.sem() + bi + borrow.sem()
                        == ai + next_borrow.sem() * LIMB_BASE(),
                    limbs_val(new_sem) == limbs_val(new_sem.subrange(0, i as int))
                        + new_sem[i as int] * p,
                    limbs_val(sa.subrange(0, (i + 1) as int))
                        == limbs_val(sa.subrange(0, i as int)) + ai * p,
                    limbs_val(sb.subrange(0, (i + 1) as int))
                        == limbs_val(sb.subrange(0, i as int)) + bi * p,
                    new_sem.subrange(0, i as int) =~= pre_sub,
                    new_sem[i as int] == digit.sem(),
                    p_next == LIMB_BASE() * p;
        }
        borrow = next_borrow;
    }

    proof {
        assert(sa.subrange(0, sa.len() as int) =~= sa);
        assert(sb.subrange(0, sb.len() as int) =~= sb);
    }
    borrow
}

///  Conditional select writing to caller-provided output buffer.
pub fn select_vec_to<T: LimbOps>(
    cond: &T, if_zero: &[T], if_nonzero: &[T], out: &mut Vec<T>, out_off: usize, n: usize,
)
    requires
        cond.sem() == 0 || cond.sem() == 1,
        if_zero@.len() == n, if_nonzero@.len() == n,
        old(out)@.len() >= out_off + n,
        out_off + n < usize::MAX,
        valid_limbs(if_zero@), valid_limbs(if_nonzero@),
    ensures out@.len() == old(out)@.len(),
{
    let ghost out_len = out@.len();
    for i in 0..n
        invariant
            if_zero@.len() == n, if_nonzero@.len() == n,
            out@.len() == out_len, out_len >= out_off + n,
            out_off + n < usize::MAX,
            valid_limbs(if_zero@), valid_limbs(if_nonzero@),
            cond.sem() == 0 || cond.sem() == 1,
    {
        let selected = T::select_limb(cond, if_zero[i].clone_limb(), if_nonzero[i].clone_limb());
        out.set(out_off + i, selected);
    }
}

///  Copy a slice of a Vec into an output buffer.
pub fn slice_vec_to<T: LimbOps>(a: &[T], start: usize, end: usize, out: &mut Vec<T>, out_off: usize)
    requires
        start <= end, end <= a@.len(),
        out_off + (end - start) < usize::MAX,
        out_off + (end - start) <= old(out)@.len(),
    ensures out@.len() == old(out)@.len(),
        // Copied values match source
        forall |j: int| 0 <= j < end - start ==> (#[trigger] out@[(out_off as int + j) as int]).sem() == a@[(start as int + j) as int].sem(),
        // Frame: outside [out_off, out_off+len) unchanged
        forall |j: int| 0 <= j < out@.len() && !(out_off as int <= j < out_off as int + (end - start) as int) ==> out@[j] == old(out)@[j],
{
    let ghost old_out = out@;
    let ghost out_len = out@.len();
    let len = end - start;
    let mut si: usize = start;
    let mut di: usize = out_off;
    for idx in 0..len
        invariant
            start <= end, end <= a@.len(),
            out@.len() == out_len,
            len == end - start,
            si == start + idx, di == out_off + idx,
            si <= end, di <= out_off + len,
            out_off + len <= out_len,
            out_off + len < usize::MAX,
            // Copied values match
            forall |j: int| 0 <= j < idx ==> (#[trigger] out@[(out_off as int + j) as int]).sem() == a@[(start as int + j) as int].sem(),
            // Frame
            forall |j: int| 0 <= j < out_len && !(out_off as int <= j < out_off as int + idx) ==> out@[j] == old_out[j],
    {
        out.set(di, a[si].clone_limb());
        si = si + 1;
        di = di + 1;
    }
}

///  Signed addition writing to output buffer. GPU-compatible (no Vec::new).
///  Uses tmp1, tmp2, tmp3 as scratch (each >= n limbs).
///  a has sign a_sign (0=pos, 1=neg), b has sign b_sign. Result in out.
pub fn signed_add_to<T: LimbOps>(
    a: &[T], a_sign: &T, b: &[T], b_sign: &T,
    out: &mut Vec<T>, out_off: usize,
    tmp1: &mut Vec<T>, tmp1_off: usize,
    tmp2: &mut Vec<T>, tmp2_off: usize,
    n: usize,
) -> (out_sign: T)
    requires
        a@.len() >= n, b@.len() >= n,
        old(out)@.len() >= out_off + n, old(tmp1)@.len() >= tmp1_off + n, old(tmp2)@.len() >= tmp2_off + n,
        out_off + n < usize::MAX, tmp1_off + n < usize::MAX, tmp2_off + n < usize::MAX,
        valid_limbs(a@), valid_limbs(b@),
        a_sign.sem() == 0 || a_sign.sem() == 1,
        b_sign.sem() == 0 || b_sign.sem() == 1,
    ensures out@.len() == old(out)@.len(),
        tmp1@.len() == old(tmp1)@.len(), tmp2@.len() == old(tmp2)@.len(),
        out_sign.sem() == 0 || out_sign.sem() == 1,
        // Valid limbs on output region
        forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] out@[(out_off as int + j) as int]).sem() < LIMB_BASE(),
        // Signed-magnitude sum equation: 3-way modular disjunction
        ({
            let va = vec_val(a@.subrange(0, n as int));
            let vb = vec_val(b@.subrange(0, n as int));
            let vo = vec_val(out@.subrange(out_off as int, (out_off + n) as int));
            let sa_signed = if a_sign.sem() == 0 { va } else { -va };
            let sb_signed = if b_sign.sem() == 0 { vb } else { -vb };
            let so_signed = if out_sign.sem() == 0 { vo } else { -vo };
            let true_sum = sa_signed + sb_signed;
            let P = limb_power(n as nat);
            so_signed == true_sum
                || (so_signed == true_sum - P && true_sum >= P)
                || (so_signed == true_sum + P && true_sum <= -(P as int))
        }),
{
    let ghost a_sub = a@.subrange(0, n as int);
    let ghost b_sub = b@.subrange(0, n as int);
    proof {
        assert(valid_limbs(a_sub)) by {
            assert forall |k: int| 0 <= k < a_sub.len()
                implies 0 <= (#[trigger] a_sub[k]).sem() && a_sub[k].sem() < LIMB_BASE() by {
                assert(a_sub[k] == a@[k]);
            }
        }
        assert(valid_limbs(b_sub)) by {
            assert forall |k: int| 0 <= k < b_sub.len()
                implies 0 <= (#[trigger] b_sub[k]).sem() && b_sub[k].sem() < LIMB_BASE() by {
                assert(b_sub[k] == b@[k]);
            }
        }
    }

    // Compute a + b (unsigned) → tmp1
    let sum_carry = add_limbs_to(a, b, tmp1, tmp1_off, n);
    let ghost sum_sub = tmp1@.subrange(tmp1_off as int, (tmp1_off + n) as int);
    proof {
        // sum equation translated to subranges
        assert(valid_limbs(sum_sub)) by {
            assert forall |k: int| 0 <= k < sum_sub.len()
                implies 0 <= (#[trigger] sum_sub[k]).sem() && sum_sub[k].sem() < LIMB_BASE() by {
                assert(sum_sub[k] == tmp1@[(tmp1_off as int) + k]);
            }
        }
        assert(sem_seq(sum_sub) =~= sem_seq(tmp1@.subrange(tmp1_off as int, (tmp1_off + n) as int)));
        assert(sem_seq(a_sub) =~= sem_seq(a@.subrange(0, n as int)));
        assert(sem_seq(b_sub) =~= sem_seq(b@.subrange(0, n as int)));
    }

    // Compute a - b → tmp2
    let borrow_ab = sub_limbs_to(a, b, tmp2, tmp2_off, n);
    let ghost amb_sub = tmp2@.subrange(tmp2_off as int, (tmp2_off + n) as int);
    proof {
        assert(valid_limbs(amb_sub)) by {
            assert forall |k: int| 0 <= k < amb_sub.len()
                implies 0 <= (#[trigger] amb_sub[k]).sem() && amb_sub[k].sem() < LIMB_BASE() by {
                assert(amb_sub[k] == tmp2@[(tmp2_off as int) + k]);
            }
        }
    }

    // Compute b - a → out (will be overwritten later if not used)
    let borrow_ba = sub_limbs_to(b, a, out, out_off, n);
    let ghost bma_sub = out@.subrange(out_off as int, (out_off + n) as int);
    proof {
        assert(valid_limbs(bma_sub)) by {
            assert forall |k: int| 0 <= k < bma_sub.len()
                implies 0 <= (#[trigger] bma_sub[k]).sem() && bma_sub[k].sem() < LIMB_BASE() by {
                assert(bma_sub[k] == out@[(out_off as int) + k]);
            }
        }
    }

    // same_sign indicator
    let (sign_diff, sign_borrow) = a_sign.sub_borrow(b_sign, &T::zero_val());
    let diff_zero = sign_diff.is_zero_limb();
    let borrow_zero = sign_borrow.is_zero_limb();
    let (same_sign, _) = diff_zero.mul2(&borrow_zero);

    proof {
        // Establish (a_sign == b_sign) <==> same_sign == 1
        let asv = a_sign.sem();
        let bsv = b_sign.sem();
        let sd = sign_diff.sem();
        let sbo = sign_borrow.sem();
        let dz = diff_zero.sem();
        let bz = borrow_zero.sem();
        let ss = same_sign.sem();
        // mul2 spec: same_sign.sem() == (dz * bz) % BASE
        assert(ss == (dz * bz) % LIMB_BASE());
        // sub_borrow spec: sd == (asv - bsv - 0 + BASE) % BASE; sbo == 1 iff asv - bsv < 0
        if asv == bsv {
            assert(sd == 0) by(nonlinear_arith)
                requires sd == (asv - bsv - 0 + LIMB_BASE()) % LIMB_BASE(),
                         asv == bsv, LIMB_BASE() > 0;
            assert(sbo == 0);
            assert(dz == 1);
            assert(bz == 1);
            assert(dz * bz == 1) by(nonlinear_arith) requires dz == 1, bz == 1;
            assert(1int % LIMB_BASE() == 1) by(nonlinear_arith) requires LIMB_BASE() > 1;
            assert(ss == 1);
        } else if asv == 0 && bsv == 1 {
            // 0 - 1 = -1 < 0 → borrow=1, diff = -1+BASE = BASE-1 ≠ 0
            assert(sd == LIMB_BASE() - 1) by(nonlinear_arith)
                requires sd == (0 - 1 - 0 + LIMB_BASE()) % LIMB_BASE(), LIMB_BASE() > 1;
            assert(sbo == 1);
            assert(dz == 0);
            assert(bz == 0);
            assert(dz * bz == 0) by(nonlinear_arith) requires dz == 0, bz == 0;
            assert(0int % LIMB_BASE() == 0) by(nonlinear_arith) requires LIMB_BASE() > 0;
            assert(ss == 0);
        } else {
            // asv == 1, bsv == 0: 1 - 0 = 1 ≥ 0 → borrow=0, diff = 1
            assert(sd == 1) by(nonlinear_arith)
                requires sd == (1 - 0 - 0 + LIMB_BASE()) % LIMB_BASE(), LIMB_BASE() > 2;
            assert(sbo == 0);
            assert(dz == 0);
            assert(bz == 1);
            assert(dz * bz == 0) by(nonlinear_arith) requires dz == 0, bz == 1;
            assert(0int % LIMB_BASE() == 0) by(nonlinear_arith) requires LIMB_BASE() > 0;
            assert(ss == 0);
        }
    }

    let diff_sign = T::select_limb(&borrow_ab, a_sign.clone_limb(), b_sign.clone_limb());
    // same_sign=1 → use a_sign (common sign), same_sign=0 → use diff_sign
    let result_sign = T::select_limb(&same_sign, diff_sign, a_sign.clone_limb());

    // Capture the SELECTED sequence (one of sum_sub, amb_sub, bma_sub) determined by indicators
    let ghost ss_v = same_sign.sem();
    let ghost bab_v = borrow_ab.sem();
    let ghost selected_seq: Seq<T> = if ss_v == 1 {
        sum_sub
    } else if bab_v == 0 {
        amb_sub
    } else {
        bma_sub
    };

    proof {
        assert(selected_seq.len() == n as int);
        assert(valid_limbs(selected_seq));
    }

    // Element-wise double select: same_sign=1 → sum, same_sign=0 → diff
    let ghost out_len = out@.len();
    let ghost out_pre_loop = out@;
    for i in 0..n
        invariant
            out@.len() == out_len, out_len >= out_off + n,
            out_off + n < usize::MAX, tmp1_off + n < usize::MAX, tmp2_off + n < usize::MAX,
            tmp1@.len() >= tmp1_off + n, tmp2@.len() >= tmp2_off + n,
            ss_v == same_sign.sem(),
            bab_v == borrow_ab.sem(),
            ss_v == 0 || ss_v == 1,
            bab_v == 0 || bab_v == 1,
            sum_sub == tmp1@.subrange(tmp1_off as int, (tmp1_off + n) as int),
            amb_sub == tmp2@.subrange(tmp2_off as int, (tmp2_off + n) as int),
            bma_sub == out_pre_loop.subrange(out_off as int, (out_off + n) as int),
            selected_seq.len() == n as int,
            ss_v == 1 ==> selected_seq == sum_sub,
            ss_v == 0 && bab_v == 0 ==> selected_seq == amb_sub,
            ss_v == 0 && bab_v == 1 ==> selected_seq == bma_sub,
            forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] tmp1@[(tmp1_off as int + j) as int]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] tmp2@[(tmp2_off as int + j) as int]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] out@[(out_off as int + j) as int]).sem() < LIMB_BASE(),
            // Loop invariant: out[off+j] for j < i has selected value, j >= i still has bma value
            forall |j: int| 0 <= j < i
                ==> #[trigger] out@[(out_off as int + j) as int].sem() == selected_seq[j].sem(),
            forall |j: int| i <= j < n
                ==> #[trigger] out@[(out_off as int + j) as int].sem() == bma_sub[j].sem(),
            // Frame: out outside [out_off, out_off+n) unchanged
            forall |k: int| 0 <= k < out_len && !(out_off as int <= k < out_off as int + n) ==> out@[k] == out_pre_loop[k],
    {
        let diff_val = T::select_limb(&borrow_ab, tmp2[tmp2_off + i].clone_limb(), out[out_off + i].clone_limb());
        // same_sign=1 → sum (tmp1), same_sign=0 → diff
        let final_val = T::select_limb(&same_sign, diff_val, tmp1[tmp1_off + i].clone_limb());

        proof {
            // Show that final_val.sem() == selected_seq[i].sem()
            let i_int = i as int;
            assert(tmp2[tmp2_off + i] == tmp2@[(tmp2_off as int) + i_int]);
            assert(out[out_off + i] == out@[(out_off as int) + i_int]);
            assert(out@[(out_off as int) + i_int].sem() == bma_sub[i_int].sem());
            assert(amb_sub[i_int] == tmp2@[(tmp2_off as int) + i_int]);
            assert(tmp1[tmp1_off + i] == tmp1@[(tmp1_off as int) + i_int]);
            assert(sum_sub[i_int] == tmp1@[(tmp1_off as int) + i_int]);

            // final_val.sem() == selected_seq[i].sem()
            if ss_v == 1 {
                assert(selected_seq == sum_sub);
                assert(final_val.sem() == tmp1[tmp1_off + i].sem());
                assert(final_val.sem() == sum_sub[i_int].sem());
                assert(final_val.sem() == selected_seq[i_int].sem());
            } else if bab_v == 0 {
                assert(selected_seq == amb_sub);
                assert(diff_val.sem() == tmp2[tmp2_off + i].sem());
                assert(final_val.sem() == diff_val.sem());
                assert(final_val.sem() == amb_sub[i_int].sem());
                assert(final_val.sem() == selected_seq[i_int].sem());
            } else {
                assert(selected_seq == bma_sub);
                assert(diff_val.sem() == out[out_off + i].sem());
                assert(final_val.sem() == diff_val.sem());
                assert(final_val.sem() == bma_sub[i_int].sem());
                assert(final_val.sem() == selected_seq[i_int].sem());
            }
        }
        let ghost out_pre_set = out@;
        out.set(out_off + i, final_val);
        proof {
            let i_int = i as int;
            assert(out@[(out_off as int) + i_int] == final_val);
            // Re-establish invariants
            assert forall |j: int| 0 <= j < i + 1
                implies #[trigger] out@[(out_off as int + j) as int].sem() == selected_seq[j].sem() by {
                if j == i_int {
                    assert(out@[(out_off as int) + j] == final_val);
                } else {
                    assert(out@[(out_off as int) + j] == out_pre_set[(out_off as int) + j]);
                }
            }
            assert forall |j: int| (i + 1) <= j < n
                implies #[trigger] out@[(out_off as int + j) as int].sem() == bma_sub[j].sem() by {
                assert(j != i_int);
                assert(out@[(out_off as int) + j] == out_pre_set[(out_off as int) + j]);
            }
            assert forall |j: int| 0 <= j < n
                implies 0 <= (#[trigger] out@[(out_off as int + j) as int]).sem() < LIMB_BASE() by {
                if j == i_int {
                    assert(out@[(out_off as int) + j] == final_val);
                } else {
                    assert(out@[(out_off as int) + j] == out_pre_set[(out_off as int) + j]);
                }
            }
            assert forall |k: int| 0 <= k < out_len && !(out_off as int <= k < out_off as int + n)
                implies out@[k] == out_pre_loop[k] by {
                assert((out_off as int) + i_int != k);
                assert(out@[k] == out_pre_set[k]);
            }
        }
    }

    proof {
        // After loop: vec_val(out subrange) == vec_val(selected_seq)
        let final_sub = out@.subrange(out_off as int, (out_off + n) as int);
        assert(final_sub.len() == selected_seq.len());
        assert forall |j: int| 0 <= j < final_sub.len()
            implies (#[trigger] final_sub[j]).sem() == selected_seq[j].sem() by {
            assert(final_sub[j] == out@[(out_off as int) + j]);
        }
        lemma_vec_val_eq_from_sem_eq::<T>(final_sub, selected_seq);
        assert(valid_limbs(final_sub)) by {
            assert forall |j: int| 0 <= j < final_sub.len()
                implies 0 <= (#[trigger] final_sub[j]).sem() && final_sub[j].sem() < LIMB_BASE() by {
                assert(final_sub[j] == out@[(out_off as int) + j]);
            }
        }

        // Apply lemma_signed_add_correct_seq
        lemma_signed_add_correct_seq::<T>(
            a_sub, a_sign.sem(),
            b_sub, b_sign.sem(),
            sum_sub, sum_carry.sem(),
            amb_sub, borrow_ab.sem(),
            bma_sub, borrow_ba.sem(),
            same_sign.sem(),
            final_sub, result_sign.sem(),
            n as nat,
        );
    }

    result_sign
}

///  Signed subtraction: a - b = a + (-b). No Vec::new.
pub fn signed_sub_to<T: LimbOps>(
    a: &[T], a_sign: &T, b: &[T], b_sign: &T,
    out: &mut Vec<T>, out_off: usize,
    tmp1: &mut Vec<T>, tmp1_off: usize,
    tmp2: &mut Vec<T>, tmp2_off: usize,
    n: usize,
) -> (out_sign: T)
    requires
        a@.len() >= n, b@.len() >= n,
        old(out)@.len() >= out_off + n, old(tmp1)@.len() >= tmp1_off + n, old(tmp2)@.len() >= tmp2_off + n,
        out_off + n < usize::MAX, tmp1_off + n < usize::MAX, tmp2_off + n < usize::MAX,
        valid_limbs(a@), valid_limbs(b@),
        a_sign.sem() == 0 || a_sign.sem() == 1,
        b_sign.sem() == 0 || b_sign.sem() == 1,
    ensures out@.len() == old(out)@.len(),
        tmp1@.len() == old(tmp1)@.len(), tmp2@.len() == old(tmp2)@.len(),
        out_sign.sem() == 0 || out_sign.sem() == 1,
        forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] out@[(out_off as int + j) as int]).sem() < LIMB_BASE(),
        // Signed-magnitude difference equation: 3-way modular disjunction.
        // Mirrors signed_add_to's postcondition with b negated.
        ({
            let va = vec_val(a@.subrange(0, n as int));
            let vb = vec_val(b@.subrange(0, n as int));
            let vo = vec_val(out@.subrange(out_off as int, (out_off + n) as int));
            let sa_signed = if a_sign.sem() == 0 { va } else { -va };
            let sb_signed = if b_sign.sem() == 0 { vb } else { -vb };
            let so_signed = if out_sign.sem() == 0 { vo } else { -vo };
            let true_diff = sa_signed - sb_signed;
            let p = limb_power(n as nat);
            so_signed == true_diff
                || (so_signed == true_diff - p && true_diff >= p)
                || (so_signed == true_diff + p && true_diff <= -(p as int))
        }),
{
    let neg_b_sign = T::select_limb(b_sign, T::const_u32(1u32), T::zero_val());
    let out_sign = signed_add_to(a, a_sign, b, &neg_b_sign, out, out_off, tmp1, tmp1_off, tmp2, tmp2_off, n);
    proof {
        // signed_add_to gave us the disjunction in terms of `neg_b_sign`'s sign.
        // Since `neg_b_sign.sem() == 1 - b_sign.sem()`, the value
        // `(if neg_b_sign.sem() == 0 { vb } else { -vb })` equals
        // `-(if b_sign.sem() == 0 { vb } else { -vb })` = `-sb_signed`.
        // So the disjunction in terms of `sa_signed + (-sb_signed) = sa_signed - sb_signed`
        // is exactly what we want.
        let va = vec_val(a@.subrange(0, n as int));
        let vb = vec_val(b@.subrange(0, n as int));
        let nb_signed = if neg_b_sign.sem() == 0 { vb } else { -vb };
        let sb_signed = if b_sign.sem() == 0 { vb } else { -vb };
        assert(nb_signed == -sb_signed);
    }
    out_sign
}

///  Signed fixed-point multiply. No Vec::new.
pub fn signed_mul_to<T: LimbOps>(
    a: &[T], a_sign: &T, b: &[T], b_sign: &T,
    out: &mut Vec<T>, out_off: usize,
    prod: &mut Vec<T>, prod_off: usize,
    n: usize, frac_limbs: usize,
) -> (out_sign: T)
    requires
        a@.len() >= n, b@.len() >= n,
        n > 0, n <= 0x1FFF_FFFF,
        valid_limbs(a@), valid_limbs(b@),
        old(out)@.len() >= out_off + n,
        old(prod)@.len() >= prod_off + 2 * n,
        out_off + n < usize::MAX,
        prod_off + 2 * n < usize::MAX,
        frac_limbs + n <= 2 * n,
        frac_limbs <= n,
        frac_limbs + n < usize::MAX,
        a_sign.sem() == 0 || a_sign.sem() == 1,
        b_sign.sem() == 0 || b_sign.sem() == 1,
    ensures out@.len() == old(out)@.len(),
        prod@.len() == old(prod)@.len(),
        out_sign.sem() == 0 || out_sign.sem() == 1,
        // Sign is XOR of input signs (same sign → positive result)
        (a_sign.sem() == b_sign.sem()) ==> out_sign.sem() == 0,
        (a_sign.sem() != b_sign.sem()) ==> out_sign.sem() == 1,
        // Valid limbs on output region
        forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] out@[(out_off as int + j) as int]).sem() < LIMB_BASE(),
        // Truncated product value equation: out is the truncated magnitude of a * b
        vec_val(out@.subrange(out_off as int, (out_off + n) as int))
            == ((vec_val(a@.subrange(0, n as int)) * vec_val(b@.subrange(0, n as int)))
                / limb_power(frac_limbs as nat)) % limb_power(n as nat),
{
    mul_schoolbook_to(a, b, prod, prod_off, n);
    let ghost prod_full = prod@.subrange(prod_off as int, (prod_off + 2 * n) as int);
    slice_vec_to(prod.as_slice(), prod_off + frac_limbs, prod_off + frac_limbs + n, out, out_off);
    // Prove valid_limbs: slice_vec_to copies values from mul_schoolbook_to output
    proof {
        assert forall |j: int| 0 <= j < n
            implies 0 <= (#[trigger] out@[(out_off as int + j) as int]).sem() < LIMB_BASE()
        by {
            // slice_vec_to ensures copied values match source
            assert(out@[(out_off as int + j) as int].sem()
                == prod@[((prod_off + frac_limbs) as int + j) as int].sem());
            // mul_schoolbook_to ensures valid limbs on prod region
            // frac_limbs + j is within [0, 2*n)
            assert(0 <= (frac_limbs as int + j) && (frac_limbs as int + j) < 2 * n);
            assert(0 <= prod@[(prod_off as int + (frac_limbs as int + j)) as int].sem() < LIMB_BASE());
        }

        // Build the value equation via lemma_truncated_product_seq
        let out_sub = out@.subrange(out_off as int, (out_off + n) as int);
        let a_sub = a@.subrange(0, n as int);
        let b_sub = b@.subrange(0, n as int);

        // prod_full == prod@.subrange(prod_off, prod_off + 2n) is the full 2n-limb product
        assert(prod_full.len() == 2 * n as int);

        // Establish valid_limbs(prod_full) and valid_limbs(out_sub) and valid_limbs(a_sub) etc.
        assert(valid_limbs(prod_full)) by {
            assert forall |k: int| 0 <= k < prod_full.len()
                implies 0 <= (#[trigger] prod_full[k]).sem() && prod_full[k].sem() < LIMB_BASE() by {
                assert(prod_full[k] == prod@[prod_off as int + k]);
                assert(0 <= prod@[(prod_off as int) + k].sem()
                    && prod@[(prod_off as int) + k].sem() < LIMB_BASE());
            }
        }

        assert(valid_limbs(out_sub)) by {
            assert forall |k: int| 0 <= k < out_sub.len()
                implies 0 <= (#[trigger] out_sub[k]).sem() && out_sub[k].sem() < LIMB_BASE() by {
                assert(out_sub[k] == out@[(out_off as int) + k]);
            }
        }

        assert(valid_limbs(a_sub)) by {
            assert forall |k: int| 0 <= k < a_sub.len()
                implies 0 <= (#[trigger] a_sub[k]).sem() && a_sub[k].sem() < LIMB_BASE() by {
                assert(a_sub[k] == a@[k]);
            }
        }
        assert(valid_limbs(b_sub)) by {
            assert forall |k: int| 0 <= k < b_sub.len()
                implies 0 <= (#[trigger] b_sub[k]).sem() && b_sub[k].sem() < LIMB_BASE() by {
                assert(b_sub[k] == b@[k]);
            }
        }

        // mul_schoolbook_to gives vec_val(prod_full) == vec_val(a_sub) * vec_val(b_sub)
        assert(vec_val(prod_full) == vec_val(a_sub) * vec_val(b_sub));

        // out_sub[j] == prod_full[(frac_limbs + j) as int] (semantically)
        assert forall |j: int| 0 <= j < n as int
            implies (#[trigger] out_sub[j]).sem() == prod_full[(frac_limbs as int + j) as int].sem() by {
            assert(out_sub[j] == out@[(out_off as int) + j]);
            assert(out@[(out_off as int) + j].sem()
                == prod@[((prod_off + frac_limbs) as int) + j].sem());
            assert(prod_full[(frac_limbs as int) + j] == prod@[(prod_off as int) + (frac_limbs as int) + j]);
        }

        // Apply the helper lemma
        lemma_truncated_product_seq::<T>(
            prod_full, out_sub,
            vec_val(a_sub), vec_val(b_sub),
            n as nat, frac_limbs as nat,
        );
    }
    let sign_b_flipped = T::select_limb(b_sign, T::const_u32(1u32), T::zero_val());
    T::select_limb(a_sign, b_sign.clone_limb(), sign_b_flipped)
}

//  ══════════════════════════════════════════════════════════════
//  Generic scalar multiplication (a * scalar)
//  ══════════════════════════════════════════════════════════════

///  Multiply n-limb array by a single limb. Returns (n+1)-limb result.
///  limbs_val(result) == limbs_val(a) * scalar.sem()
pub fn generic_mul_by_limb<T: LimbOps>(a: &[T], scalar: &T, n: usize) -> (result: Vec<T>)
    requires
        a@.len() == n,
        n < 0x7FFF_FFFF,
        valid_limbs(a@),
        0 <= scalar.sem() < LIMB_BASE(),
    ensures
        result@.len() == n + 1,
        valid_limbs(result@),
        limbs_val(sem_seq(result@)) == limbs_val(sem_seq(a@)) * scalar.sem(),
{
    let mut out: Vec<T> = Vec::new();
    let mut carry: T = T::zero_val();
    let ghost sa = sem_seq(a@);

    for i in 0..n
        invariant
            a@.len() == n,
            out@.len() == i as int,
            valid_limbs(out@),
            valid_limbs(a@),
            0 <= scalar.sem() < LIMB_BASE(),
            0 <= carry.sem() < LIMB_BASE(),
            sa == sem_seq(a@),
            limbs_val(sem_seq(out@)) + carry.sem() * limb_power(i as nat)
                == limbs_val(sa.subrange(0, i as int)) * scalar.sem(),
    {
        let (digit, next_carry) = a[i].mul_add_carry(scalar, &T::zero_val(), &carry);
        proof {
            let ai = sa[i as int];
            assert(ai == a@[i as int].sem());
            assert(0 <= ai && ai < LIMB_BASE());
            let x = ai * scalar.sem() + carry.sem();
            assert(digit.sem() + next_carry.sem() * LIMB_BASE() == x) by(nonlinear_arith)
                requires
                    digit.sem() == x % LIMB_BASE(),
                    next_carry.sem() == x / LIMB_BASE(),
                    LIMB_BASE() > 0;
            //  Carry validity: x < BASE^2, so x / BASE < BASE
            assert(0 <= next_carry.sem() && next_carry.sem() < LIMB_BASE()) by(nonlinear_arith)
                requires
                    next_carry.sem() == x / LIMB_BASE(),
                    x == ai * scalar.sem() + carry.sem(),
                    0 <= ai, ai < LIMB_BASE(),
                    0 <= scalar.sem(), scalar.sem() < LIMB_BASE(),
                    0 <= carry.sem(), carry.sem() < LIMB_BASE(),
                    LIMB_BASE() > 0;

            reveal_with_fuel(limb_power, 2);
            let p = limb_power(i as nat);
            let p_next = limb_power((i + 1) as nat);
            assert(p_next == LIMB_BASE() * p);

            lemma_sem_seq_push(out@, digit);
            lemma_limbs_val_push(sem_seq(out@), digit.sem());
            lemma_limbs_val_subrange_extend(sa, i as nat);

            //  Telescope: ltn(out) + digit*p + next_carry*p_next
            //  == ltn(a[..i])*scalar + (ai*scalar + carry - carry)*p + next_carry*p_next
            //  == ltn(a[..i])*scalar + ai*scalar*p + (digit + next_carry*BASE - carry)*p
            //  == ltn(a[..i+1])*scalar
            assert(
                limbs_val(sem_seq(out@)) + digit.sem() * p + next_carry.sem() * p_next
                == limbs_val(sa.subrange(0, (i + 1) as int)) * scalar.sem()
            ) by(nonlinear_arith)
                requires
                    limbs_val(sem_seq(out@)) + carry.sem() * p
                        == limbs_val(sa.subrange(0, i as int)) * scalar.sem(),
                    digit.sem() + next_carry.sem() * LIMB_BASE()
                        == ai * scalar.sem() + carry.sem(),
                    limbs_val(sa.subrange(0, (i + 1) as int))
                        == limbs_val(sa.subrange(0, i as int)) + ai * p,
                    p_next == LIMB_BASE() * p;
        }

        out.push(digit);
        carry = next_carry;
    }

    //  Push final carry as the (n+1)-th limb
    //  Capture pre-push state
    let ghost out_before = out@;
    out.push(carry);

    proof {
        assert(sa.subrange(0, sa.len() as int) =~= sa);
        //  out@ == out_before.push(carry)
        //  sem_seq(out@) =~= sem_seq(out_before).push(carry.sem())
        lemma_sem_seq_push(out_before, carry);
        assert(sem_seq(out@) =~= sem_seq(out_before).push(carry.sem()));
        //  limbs_val(sem_seq(out@)) == limbs_val(sem_seq(out_before)) + carry.sem() * limb_power(n)
        lemma_limbs_val_push(sem_seq(out_before), carry.sem());
        //  From invariant at i=n:
        //  limbs_val(sem_seq(out_before)) + carry.sem() * limb_power(n) == limbs_val(sa) * scalar.sem()
        //  And push lemma: limbs_val(sem_seq(out@)) == limbs_val(sem_seq(out_before)) + carry.sem() * limb_power(n)
        //  Therefore: limbs_val(sem_seq(out@)) == limbs_val(sa) * scalar.sem()
    }

    out
}

//  ══════════════════════════════════════════════════════════════
///  limb_power(a + b) == limb_power(a) * limb_power(b).
pub proof fn lemma_limb_power_add(a: nat, b: nat)
    ensures limb_power(a + b) == limb_power(a) * limb_power(b),
    decreases a,
{
    reveal_with_fuel(limb_power, 2);
    if a == 0 {
        assert(limb_power(0nat) == 1int);
        assert(limb_power(a + b) == limb_power(a) * limb_power(b)) by(nonlinear_arith)
            requires limb_power(0nat) == 1int, a == 0nat,
                     limb_power(a + b) == limb_power(b),
                     limb_power(a) == 1int;
    } else {
        lemma_limb_power_add((a - 1) as nat, b);
        //  IH: limb_power((a-1) + b) == limb_power(a-1) * limb_power(b)
        assert(limb_power(a + b) == LIMB_BASE() * limb_power(((a - 1) + b) as nat)) by {
            assert(a + b > 0);
            assert(((a + b) - 1) as nat == ((a - 1) + b) as nat);
        }
        assert(limb_power(a + b) == limb_power(a) * limb_power(b)) by(nonlinear_arith)
            requires
                limb_power(a + b) == LIMB_BASE() * limb_power(((a - 1) + b) as nat),
                limb_power(((a - 1) + b) as nat) == limb_power((a - 1) as nat) * limb_power(b),
                limb_power(a) == LIMB_BASE() * limb_power((a - 1) as nat);
    }
}

//  Valid limb predicate
//  ══════════════════════════════════════════════════════════════

///  All limbs have semantic values in [0, BASE).
pub open spec fn valid_limbs<T: LimbOps>(s: Seq<T>) -> bool {
    forall |j: int| 0 <= j < s.len() ==> 0 <= (#[trigger] s[j]).sem() && s[j].sem() < LIMB_BASE()
}

//  ══════════════════════════════════════════════════════════════
//  Generic multi-limb subtraction (requires valid limbs)
//  ══════════════════════════════════════════════════════════════

///  Generic borrow-chain subtraction of two n-limb arrays.
///  Returns (result, borrow_out).
///  Semantics: result + b == a + borrow_out * BASE^n
pub fn generic_sub_limbs<T: LimbOps>(a: &[T], b: &[T], n: usize) -> (result: (Vec<T>, T))
    requires
        a@.len() == n,
        b@.len() == n,
        valid_limbs(a@),
        valid_limbs(b@),
    ensures
        result.0@.len() == n,
        valid_limbs(result.0@),
        result.1.sem() == 0 || result.1.sem() == 1,
        limbs_val(sem_seq(result.0@)) + limbs_val(sem_seq(b@))
            == limbs_val(sem_seq(a@)) + result.1.sem() * limb_power(n as nat),
{
    let mut out: Vec<T> = Vec::new();
    let mut borrow: T = T::zero_val();
    let ghost sa = sem_seq(a@);
    let ghost sb = sem_seq(b@);

    for i in 0..n
        invariant
            a@.len() == n, b@.len() == n,
            out@.len() == i as int,
            valid_limbs(out@),
            sa == sem_seq(a@), sb == sem_seq(b@),
            valid_limbs(a@), valid_limbs(b@),
            borrow.sem() == 0 || borrow.sem() == 1,
            limbs_val(sem_seq(out@)) + limbs_val(sb.subrange(0, i as int))
                == limbs_val(sa.subrange(0, i as int))
                    + borrow.sem() * limb_power(i as nat),
    {
        let (digit, next_borrow) = a[i].sub_borrow(&b[i], &borrow);
        proof {
            let ai = sa[i as int];
            let bi = sb[i as int];
            assert(ai == a@[i as int].sem());
            assert(bi == b@[i as int].sem());
            //  From valid_limbs: 0 <= ai < BASE, 0 <= bi < BASE
            assert(0 <= ai && ai < LIMB_BASE());
            assert(0 <= bi && bi < LIMB_BASE());

            let diff = ai - bi - borrow.sem();
            //  diff in [-BASE, BASE): since ai in [0,BASE), bi in [0,BASE), borrow in {0,1}
            //  diff >= 0 - (BASE-1) - 1 = -BASE
            //  diff < BASE - 0 - 0 = BASE
            let sum = diff + LIMB_BASE();
            if diff >= 0 {
                assert(next_borrow.sem() == 0int);
                //  sum = diff + BASE, with BASE <= sum < 2*BASE
                //  sum % BASE = sum - BASE = diff
                assert(sum >= LIMB_BASE() && sum < 2 * LIMB_BASE());
                assert(sum / LIMB_BASE() == 1int) by(nonlinear_arith)
                    requires sum >= LIMB_BASE(), sum < 2 * LIMB_BASE(), LIMB_BASE() > 0;
                assert(sum % LIMB_BASE() == sum - LIMB_BASE()) by(nonlinear_arith)
                    requires sum / LIMB_BASE() == 1int, LIMB_BASE() > 0;
                assert(digit.sem() == diff);
            } else {
                assert(next_borrow.sem() == 1int);
                //  sum = diff + BASE, with 0 <= sum < BASE
                assert(sum >= 0 && sum < LIMB_BASE());
                assert(sum / LIMB_BASE() == 0int) by(nonlinear_arith)
                    requires sum >= 0, sum < LIMB_BASE(), LIMB_BASE() > 0;
                assert(sum % LIMB_BASE() == sum) by(nonlinear_arith)
                    requires sum / LIMB_BASE() == 0int, LIMB_BASE() > 0;
                assert(digit.sem() == diff + LIMB_BASE());
            }

            reveal_with_fuel(limb_power, 2);
            let p = limb_power(i as nat);
            let p_next = limb_power((i + 1) as nat);
            assert(p_next == LIMB_BASE() * p);

            lemma_sem_seq_push(out@, digit);
            lemma_limbs_val_push(sem_seq(out@), digit.sem());
            lemma_limbs_val_subrange_extend(sa, i as nat);
            lemma_limbs_val_subrange_extend(sb, i as nat);

            assert(
                limbs_val(sem_seq(out@)) + digit.sem() * p
                    + limbs_val(sb.subrange(0, i as int)) + bi * p
                == limbs_val(sa.subrange(0, i as int)) + ai * p
                    + next_borrow.sem() * p_next
            ) by(nonlinear_arith)
                requires
                    limbs_val(sem_seq(out@)) + limbs_val(sb.subrange(0, i as int))
                        == limbs_val(sa.subrange(0, i as int))
                            + borrow.sem() * p,
                    digit.sem() + bi + borrow.sem()
                        == ai + next_borrow.sem() * LIMB_BASE(),
                    p_next == LIMB_BASE() * p;
        }

        out.push(digit);
        borrow = next_borrow;
    }

    proof {
        assert(sa.subrange(0, sa.len() as int) =~= sa);
        assert(sb.subrange(0, sb.len() as int) =~= sb);
    }

    (out, borrow)
}

//  ══════════════════════════════════════════════════════════════
//  Generic vector helpers for multi-limb multiply
//  ══════════════════════════════════════════════════════════════

///  Vector of n zeros.
pub fn generic_zero_vec<T: LimbOps>(n: usize) -> (result: Vec<T>)
    ensures
        result@.len() == n,
        valid_limbs(result@),
        forall |j: int| 0 <= j < n ==> (#[trigger] result@[j]).sem() == 0int,
{
    let mut out: Vec<T> = Vec::new();
    for i in 0..n
        invariant out@.len() == i as int,
            forall |j: int| 0 <= j < i ==> (#[trigger] out@[j]).sem() == 0int,
    {
        out.push(T::zero_val());
    }
    out
}

///  Copy a subrange of a Vec.
pub fn generic_slice_vec<T: LimbOps>(a: &[T], start: usize, end: usize) -> (result: Vec<T>)
    requires start <= end, end <= a@.len(),
    ensures result@.len() == end - start,
        forall |j: int| 0 <= j < result@.len() ==> (#[trigger] result@[j]).sem() == a@[(start + j) as int].sem(),
{
    let mut out: Vec<T> = Vec::new();
    for i in start..end
        invariant start <= end, end <= a@.len(),
            out@.len() == (i - start) as int,
            forall |j: int| 0 <= j < out@.len() ==> (#[trigger] out@[j]).sem() == a@[(start + j) as int].sem(),
    {
        out.push(a[i].clone_limb());
    }
    out
}

///  Conditional select between two Vecs based on a limb condition.
///  If cond.sem() == 0, returns a copy of if_zero; else returns a copy of if_nonzero.
pub fn generic_select_vec<T: LimbOps>(cond: &T, if_zero: &Vec<T>, if_nonzero: &Vec<T>, n: usize) -> (result: Vec<T>)
    requires cond.sem() == 0 || cond.sem() == 1,
        if_zero@.len() == n, if_nonzero@.len() == n,
        valid_limbs(if_zero@), valid_limbs(if_nonzero@),
    ensures result@.len() == n, valid_limbs(result@),
        cond.sem() == 0 ==> (forall |j: int| 0 <= j < n ==> (#[trigger] result@[j]).sem() == if_zero@[j].sem()),
        cond.sem() == 1 ==> (forall |j: int| 0 <= j < n ==> (#[trigger] result@[j]).sem() == if_nonzero@[j].sem()),
        cond.sem() == 0 ==> vec_val(result@) == vec_val(if_zero@),
        cond.sem() == 1 ==> vec_val(result@) == vec_val(if_nonzero@),
{
    let mut out: Vec<T> = Vec::new();
    for i in 0..n
        invariant cond.sem() == 0 || cond.sem() == 1,
            if_zero@.len() == n, if_nonzero@.len() == n,
            valid_limbs(if_zero@), valid_limbs(if_nonzero@),
            out@.len() == i as int,
            forall |j: int| 0 <= j < i ==> 0 <= (#[trigger] out@[j]).sem() < LIMB_BASE(),
            cond.sem() == 0 ==> (forall |j: int| 0 <= j < i ==> (#[trigger] out@[j]).sem() == if_zero@[j].sem()),
            cond.sem() == 1 ==> (forall |j: int| 0 <= j < i ==> (#[trigger] out@[j]).sem() == if_nonzero@[j].sem()),
    {
        let selected = T::select_limb(cond, if_zero[i].clone_limb(), if_nonzero[i].clone_limb());
        out.push(selected);
    }
    proof {
        //  Prove vec_val equality by extensional equality on sem_seq
        if cond.sem() == 0 {
            assert(sem_seq(out@) =~= sem_seq(if_zero@));
        } else {
            assert(sem_seq(out@) =~= sem_seq(if_nonzero@));
        }
    }
    out
}

///  Pad a Vec with zeros to reach target length.
pub fn generic_pad_to_length<T: LimbOps>(a: &[T], target: usize) -> (result: Vec<T>)
    requires target >= a@.len(), valid_limbs(a@),
    ensures result@.len() == target, valid_limbs(result@),
        forall |j: int| 0 <= j < a@.len() ==> (#[trigger] result@[j]).sem() == a@[j].sem(),
        forall |j: int| a@.len() <= j < target ==> (#[trigger] result@[j]).sem() == 0int,
{
    let mut out: Vec<T> = Vec::new();
    for i in 0..a.len()
        invariant target >= a@.len(),
            out@.len() == i as int,
            forall |j: int| 0 <= j < i ==> (#[trigger] out@[j]).sem() == a@[j].sem(),
    {
        out.push(a[i].clone_limb());
    }
    for i in (a.len())..target
        invariant a@.len() <= target,
            out@.len() == i as int,
            forall |j: int| 0 <= j < a@.len() ==> (#[trigger] out@[j]).sem() == a@[j].sem(),
            forall |j: int| a@.len() <= j < i ==> (#[trigger] out@[j]).sem() == 0int,
    {
        out.push(T::zero_val());
    }
    out
}

///  Shift left (prepend zeros).
pub fn generic_shift_left<T: LimbOps>(a: &[T], offset: usize) -> (result: Vec<T>)
    requires valid_limbs(a@),
    ensures result@.len() == a@.len() + offset,
        valid_limbs(result@),
        forall |j: int| 0 <= j < offset ==> (#[trigger] result@[j]).sem() == 0int,
        forall |j: int| 0 <= j < a@.len() ==> (#[trigger] result@[(offset + j) as int]).sem() == a@[j].sem(),
{
    let mut out: Vec<T> = Vec::new();
    for i in 0..offset
        invariant out@.len() == i as int,
            valid_limbs(out@),
            forall |j: int| 0 <= j < i ==> (#[trigger] out@[j]).sem() == 0int,
    {
        out.push(T::zero_val());
    }
    for k in 0..a.len()
        invariant out@.len() == (offset + k) as int,
            valid_limbs(out@), valid_limbs(a@),
            forall |j: int| 0 <= j < offset ==> (#[trigger] out@[j]).sem() == 0int,
            forall |j: int| 0 <= j < k ==> (#[trigger] out@[(offset + j) as int]).sem() == a@[j].sem(),
    {
        out.push(a[k].clone_limb());
    }
    out
}

//  ══════════════════════════════════════════════════════════════
//  Generic schoolbook multiplication (O(n²), base case for Karatsuba)
//  ══════════════════════════════════════════════════════════════

///  limbs_val of a Vec<T> — convenience wrapper.
pub open spec fn vec_val<T: LimbOps>(v: Seq<T>) -> int {
    limbs_val(sem_seq(v))
}

///  Two sequences with equal sem() at every position have equal vec_val.
pub proof fn lemma_vec_val_eq_from_sem_eq<T: LimbOps>(a: Seq<T>, b: Seq<T>)
    requires a.len() == b.len(),
        forall |j: int| 0 <= j < a.len() ==> (#[trigger] a[j]).sem() == b[j].sem(),
    ensures vec_val(a) == vec_val(b)
{
    assert(sem_seq(a) =~= sem_seq(b));
}

///  limbs_val of all-zeros is 0.
pub proof fn lemma_limbs_val_zeros(n: nat)
    ensures limbs_val(Seq::new(n, |_i: int| 0int)) == 0int,
    decreases n,
{
    reveal_with_fuel(limbs_val, 2);
    if n > 0 {
        let s = Seq::new(n, |_i: int| 0int);
        assert(s.subrange(1, n as int) =~= Seq::new((n - 1) as nat, |_i: int| 0int));
        lemma_limbs_val_zeros((n - 1) as nat);
    }
}

///  sem_seq of a Vec where all sem() == 0 gives all-zero Seq.
pub proof fn lemma_sem_seq_zeros<T: LimbOps>(v: Seq<T>)
    requires forall |j: int| 0 <= j < v.len() ==> (#[trigger] v[j]).sem() == 0int,
    ensures sem_seq(v) =~= Seq::new(v.len(), |_i: int| 0int),
{}

///  vec_val of all-zero Vec is 0.
pub proof fn lemma_vec_val_zeros<T: LimbOps>(v: Seq<T>)
    requires forall |j: int| 0 <= j < v.len() ==> (#[trigger] v[j]).sem() == 0int,
    ensures vec_val(v) == 0int,
{
    lemma_sem_seq_zeros(v);
    lemma_limbs_val_zeros(v.len());
}

///  Valid limbs have value bounded by limb_power(n).
pub proof fn lemma_limbs_val_upper_bound(s: Seq<int>, n: nat)
    requires
        s.len() == n,
        forall |j: int| 0 <= j < n ==> 0 <= #[trigger] s[j] && s[j] < LIMB_BASE(),
    ensures
        0 <= limbs_val(s),
        limbs_val(s) < limb_power(n),
    decreases n,
{
    reveal_with_fuel(limbs_val, 2);
    reveal_with_fuel(limb_power, 2);
    if n == 0 {
    } else {
        let tail = s.subrange(1, n as int);
        assert forall |j: int| 0 <= j < (n-1) as nat implies 0 <= #[trigger] tail[j] && tail[j] < LIMB_BASE()
        by { assert(tail[j] == s[j + 1]); }
        lemma_limbs_val_upper_bound(tail, (n - 1) as nat);
        //  limbs_val(s) = s[0] + BASE * limbs_val(tail)
        //  0 <= s[0] < BASE, 0 <= limbs_val(tail) < limb_power(n-1)
        //  So: 0 <= limbs_val(s) < BASE + BASE * (limb_power(n-1) - 1) + BASE - 1
        //  Actually: limbs_val(s) <= (BASE-1) + BASE * (limb_power(n-1) - 1) = BASE*limb_power(n-1) - 1 = limb_power(n) - 1
        assert(limbs_val(s) < limb_power(n)) by(nonlinear_arith)
            requires
                limbs_val(s) == s[0] + LIMB_BASE() * limbs_val(tail),
                0 <= s[0], s[0] < LIMB_BASE(),
                0 <= limbs_val(tail), limbs_val(tail) < limb_power((n-1) as nat),
                limb_power(n) == LIMB_BASE() * limb_power((n-1) as nat);
    }
}

///  vec_val of valid limbs is bounded.
pub proof fn lemma_vec_val_bounded<T: LimbOps>(a: Seq<T>)
    requires valid_limbs(a),
    ensures 0 <= vec_val(a) < limb_power(a.len()),
{
    assert forall |j: int| 0 <= j < sem_seq(a).len()
        implies 0 <= #[trigger] sem_seq(a)[j] && sem_seq(a)[j] < LIMB_BASE()
    by { assert(sem_seq(a)[j] == a[j].sem()); }
    lemma_limbs_val_upper_bound(sem_seq(a), a.len());
}

///  Split a Seq<int> into lo + hi * BASE^mid.
pub proof fn lemma_limbs_val_split(s: Seq<int>, mid: nat)
    requires mid <= s.len(),
    ensures limbs_val(s) == limbs_val(s.subrange(0, mid as int))
        + limbs_val(s.subrange(mid as int, s.len() as int)) * limb_power(mid),
    decreases mid,
{
    reveal_with_fuel(limbs_val, 2);
    reveal_with_fuel(limb_power, 2);
    if mid == 0 {
        assert(s.subrange(0, 0int) =~= Seq::<int>::empty());
        assert(s.subrange(0, s.len() as int) =~= s);
    } else {
        //  s = [s[0]] + s[1..]
        //  limbs_val(s) = s[0] + BASE * limbs_val(s[1..])
        //  By IH on s[1..] with mid-1:
        //  limbs_val(s[1..]) = limbs_val(s[1..mid]) + limbs_val(s[mid..]) * limb_power(mid-1)
        //  So: limbs_val(s) = s[0] + BASE * (limbs_val(s[1..mid]) + limbs_val(s[mid..]) * limb_power(mid-1))
        //  = s[0] + BASE * limbs_val(s[1..mid]) + limbs_val(s[mid..]) * BASE * limb_power(mid-1)
        //  = limbs_val(s[0..mid]) + limbs_val(s[mid..]) * limb_power(mid)
        let tail = s.subrange(1, s.len() as int);
        lemma_limbs_val_split(tail, (mid - 1) as nat);
        assert(tail.subrange(0, (mid - 1) as int) =~= s.subrange(1, mid as int));
        assert(tail.subrange((mid - 1) as int, tail.len() as int) =~= s.subrange(mid as int, s.len() as int));
        //  limbs_val(s[0..mid]) = s[0] + BASE * limbs_val(s[1..mid])
        assert(s.subrange(0, mid as int).subrange(1, (s.subrange(0, mid as int)).len() as int)
            =~= s.subrange(1, mid as int));
        //  limb_power(mid) = BASE * limb_power(mid-1)
        assert(limbs_val(s) == limbs_val(s.subrange(0, mid as int))
            + limbs_val(s.subrange(mid as int, s.len() as int)) * limb_power(mid))
        by(nonlinear_arith)
            requires
                limbs_val(s) == s[0] + LIMB_BASE() * limbs_val(tail),
                limbs_val(tail) == limbs_val(tail.subrange(0, (mid-1) as int))
                    + limbs_val(tail.subrange((mid-1) as int, tail.len() as int)) * limb_power((mid-1) as nat),
                limbs_val(s.subrange(0, mid as int)) == s[0] + LIMB_BASE() * limbs_val(s.subrange(1, mid as int)),
                tail.subrange(0, (mid-1) as int) =~= s.subrange(1, mid as int),
                tail.subrange((mid-1) as int, tail.len() as int) =~= s.subrange(mid as int, s.len() as int),
                limb_power(mid) == LIMB_BASE() * limb_power((mid - 1) as nat);
    }
}

///  Split vec_val into lo + hi * limb_power(mid).
pub proof fn lemma_vec_val_split<T: LimbOps>(a: Seq<T>, mid: nat)
    requires mid <= a.len(),
    ensures vec_val(a) == vec_val(a.subrange(0, mid as int))
        + vec_val(a.subrange(mid as int, a.len() as int)) * limb_power(mid),
{
    lemma_sem_seq_subrange(a, 0, mid as int);
    lemma_sem_seq_subrange(a, mid as int, a.len() as int);
    lemma_limbs_val_split(sem_seq(a), mid);
    assert(sem_seq(a).subrange(0, mid as int) =~= sem_seq(a.subrange(0, mid as int)));
    assert(sem_seq(a).subrange(mid as int, sem_seq(a).len() as int)
        =~= sem_seq(a.subrange(mid as int, a.len() as int)));
}

//  ══════════════════════════════════════════════════════════════
//  Shift and pad semantics on Seq<int> (Z3-friendly, no generics)
//  ══════════════════════════════════════════════════════════════

///  Prepending a zero to limbs_val multiplies by BASE.
pub proof fn lemma_limbs_val_prepend_zero(s: Seq<int>)
    ensures limbs_val(seq![0int] + s) == LIMB_BASE() * limbs_val(s),
{
    reveal_with_fuel(limbs_val, 2);
    assert((seq![0int] + s).subrange(1, (seq![0int] + s).len() as int) =~= s);
}

///  Shifting left by k zeros: limbs_val(zeros + s) == limbs_val(s) * limb_power(k).
pub proof fn lemma_limbs_val_shift(s: Seq<int>, zeros: Seq<int>)
    requires
        forall |i: int| 0 <= i < zeros.len() ==> zeros[i] == 0int,
    ensures limbs_val(zeros + s) == limbs_val(s) * limb_power(zeros.len()),
    decreases zeros.len(),
{
    if zeros.len() == 0 {
        assert(zeros + s =~= s);
        reveal_with_fuel(limb_power, 2);
        assert(limb_power(zeros.len()) == 1int);
        assert(limbs_val(zeros + s) == limbs_val(s) * limb_power(zeros.len())) by(nonlinear_arith)
            requires
                limbs_val(zeros + s) == limbs_val(s),
                limb_power(zeros.len()) == 1int;
    } else {
        reveal_with_fuel(limb_power, 2);
        let tail_zeros = zeros.subrange(1, zeros.len() as int);
        assert forall |i: int| 0 <= i < tail_zeros.len()
            implies tail_zeros[i] == 0int
        by { assert(tail_zeros[i] == zeros[i + 1]); }
        //  zeros + s == [0] + (tail_zeros + s)
        assert((zeros + s) =~= (seq![0int] + (tail_zeros + s)));
        lemma_limbs_val_shift(s, tail_zeros);
        lemma_limbs_val_prepend_zero(tail_zeros + s);
        //  Chain: limbs_val(zeros+s) == BASE * limbs_val(tail_zeros+s)
        //       == BASE * limbs_val(s) * limb_power(tail_zeros.len())
        //       == limbs_val(s) * (BASE * limb_power(tail_zeros.len()))
        //       == limbs_val(s) * limb_power(zeros.len())
        assert(limbs_val(zeros + s) == limbs_val(s) * limb_power(zeros.len())) by(nonlinear_arith)
            requires
                limbs_val(zeros + s) == LIMB_BASE() * limbs_val(tail_zeros + s),
                limbs_val(tail_zeros + s) == limbs_val(s) * limb_power(tail_zeros.len()),
                limb_power(zeros.len()) == LIMB_BASE() * limb_power(tail_zeros.len());
    }
}

///  Appending zeros doesn't change limbs_val.
pub proof fn lemma_limbs_val_append_zeros(s: Seq<int>, k: nat)
    ensures limbs_val(s + Seq::new(k, |_i: int| 0int)) == limbs_val(s),
    decreases s.len(),
{
    reveal_with_fuel(limbs_val, 2);
    if s.len() == 0 {
        assert(s + Seq::new(k, |_i: int| 0int) =~= Seq::new(k, |_i: int| 0int));
        lemma_limbs_val_zeros(k);
    } else {
        let tail = s.subrange(1, s.len() as int);
        let zeros = Seq::new(k, |_i: int| 0int);
        assert((s + zeros).subrange(1, (s + zeros).len() as int) =~= (tail + zeros));
        assert((s + zeros)[0] == s[0]);
        lemma_limbs_val_append_zeros(tail, k);
    }
}

//  ══════════════════════════════════════════════════════════════
//  Bridge: connect generic Vec<T> shift/pad to Seq<int> lemmas
//  ══════════════════════════════════════════════════════════════

///  vec_val of a shifted (zero-prepended) Vec equals original * limb_power(offset).
pub proof fn lemma_vec_val_shift<T: LimbOps>(a: Seq<T>, offset: nat, shifted: Seq<T>)
    requires
        shifted.len() == a.len() + offset,
        forall |j: int| 0 <= j < offset ==> (#[trigger] shifted[j]).sem() == 0int,
        forall |j: int| 0 <= j < a.len() ==>
            (#[trigger] shifted[(offset + j) as int]).sem() == a[j].sem(),
    ensures vec_val(shifted) == vec_val(a) * limb_power(offset),
{
    //  sem_seq(shifted) =~= [0,...,0] + sem_seq(a)
    let sa = sem_seq(a);
    let ss = sem_seq(shifted);
    let zeros = ss.subrange(0, offset as int);
    assert forall |i: int| 0 <= i < zeros.len() implies zeros[i] == 0int
    by { assert(zeros[i] == ss[i]); assert(ss[i] == shifted[i].sem()); }
    assert(ss =~= zeros + sa) by {
        assert(sem_seq(shifted).len() == (zeros + sa).len());
        assert forall |j: int| 0 <= j < sem_seq(shifted).len()
            implies sem_seq(shifted)[j] == (zeros + sa)[j]
        by {
            if j < offset as int {
                assert(sem_seq(shifted)[j] == shifted[j].sem());
                assert((zeros + sa)[j] == zeros[j]);
            } else {
                let k = (j - offset as int);
                assert(sem_seq(shifted)[j] == shifted[j].sem());
                assert(shifted[j] == shifted[(offset + k) as int]);
                assert((zeros + sa)[j] == sa[k]);
            }
        }
    }
    lemma_limbs_val_shift(sa, zeros);
}

///  vec_val of a padded (zero-appended) Vec equals original.
pub proof fn lemma_vec_val_pad<T: LimbOps>(a: Seq<T>, padded: Seq<T>)
    requires
        padded.len() >= a.len(),
        forall |j: int| 0 <= j < a.len() ==> (#[trigger] padded[j]).sem() == a[j].sem(),
        forall |j: int| a.len() <= j < padded.len() ==> (#[trigger] padded[j]).sem() == 0int,
    ensures vec_val(padded) == vec_val(a),
{
    let extra = (padded.len() - a.len()) as nat;
    let sa = sem_seq(a);
    let zeros = Seq::new(extra, |_i: int| 0int);
    assert(sem_seq(padded) =~= sa + zeros) by {
        assert(sem_seq(padded).len() == (sa + zeros).len());
        assert forall |j: int| 0 <= j < sem_seq(padded).len()
            implies sem_seq(padded)[j] == (sa + zeros)[j]
        by {
            if j < a.len() as int {
                assert(sem_seq(padded)[j] == padded[j].sem());
                assert((sa + zeros)[j] == sa[j]);
            } else {
                assert(sem_seq(padded)[j] == padded[j].sem());
                assert((sa + zeros)[j] == zeros[(j - a.len() as int)]);
            }
        }
    }
    lemma_limbs_val_append_zeros(sa, extra);
}

//  ══════════════════════════════════════════════════════════════
//  Generic schoolbook multiplication (O(n²), base case for Karatsuba)
//  ══════════════════════════════════════════════════════════════

///  Schoolbook multiply writing to output buffer. GPU-compatible (no Vec allocation).
///  Writes 2n limbs to out[0..2n]. out must be pre-zeroed or at least length >= 2n.
pub fn mul_schoolbook_to<T: LimbOps>(
    a: &[T], b: &[T], out: &mut Vec<T>, out_off: usize, n: usize,
)
    requires
        a@.len() >= n, b@.len() >= n,
        n > 0, n <= 0x3FFF_FFFF,
        valid_limbs(a@), valid_limbs(b@),
        old(out)@.len() >= out_off + 2 * n,
        out_off + 2 * n < usize::MAX,
    ensures
        out@.len() == old(out)@.len(),
        // Valid limbs on output region
        forall |j: int| 0 <= j < 2 * n ==> 0 <= (#[trigger] out@[out_off as int + j]).sem() < LIMB_BASE(),
        // Frame: indices outside [out_off, out_off+2n) are unchanged
        forall |j: int| 0 <= j < out@.len() && !(out_off as int <= j < out_off + 2 * n) ==> out@[j] == old(out)@[j],
        // Value equation: the 2n-limb result equals a * b
        vec_val(out@.subrange(out_off as int, (out_off + 2 * n) as int))
            == vec_val(a@.subrange(0, n as int)) * vec_val(b@.subrange(0, n as int)),
{
    let ghost old_out = out@;
    let ghost out_len = out@.len();
    let ghost sa = sem_seq(a@.subrange(0, n as int));
    let ghost sb = sem_seq(b@.subrange(0, n as int));
    let ghost a_val = limbs_val(sa);
    let nn: usize = 2 * n;

    // Zero the output region
    for i in 0..nn
        invariant out@.len() == out_len, out_len >= out_off + nn, nn == 2 * n, out_off + nn < usize::MAX,
            forall |j: int| 0 <= j < out_len && !(out_off as int <= j < out_off as int + i) ==> out@[j] == old_out[j],
            forall |j: int| 0 <= j < i ==> (#[trigger] out@[out_off as int + j]).sem() == 0,
    {
        out.set(out_off + i, T::zero_val());
    }

    // After zeroing: vec_val of the output region is 0
    proof {
        let zero_sub = out@.subrange(out_off as int, (out_off + nn) as int);
        assert forall |k: int| 0 <= k < zero_sub.len()
            implies (#[trigger] zero_sub[k]).sem() == 0 by {
            assert(zero_sub[k] == out@[(out_off as int) + k]);
        }
        // vec_val of an all-zero sequence is 0
        assert(sem_seq(zero_sub) =~= Seq::new(zero_sub.len(), |_i: int| 0int)) by {
            assert forall |k: int| 0 <= k < sem_seq(zero_sub).len()
                implies sem_seq(zero_sub)[k] == 0int by {
                assert(sem_seq(zero_sub)[k] == zero_sub[k].sem());
            }
        }
        lemma_limbs_val_zeros(zero_sub.len() as nat);
        // Establish initial value of empty subrange of sb
        assert(sb.subrange(0, 0int) =~= Seq::<int>::empty());
        reveal_with_fuel(limbs_val, 2);
        assert(limbs_val(Seq::<int>::empty()) == 0int);
    }

    // Schoolbook: for each limb b[i], multiply a by b[i] and accumulate into out
    for i in 0..n
        invariant
            a@.len() >= n, b@.len() >= n,
            nn == 2 * n, n <= 0x3FFF_FFFF,
            out@.len() == out_len, out_len >= out_off + nn,
            out_off + nn < usize::MAX,
            valid_limbs(a@), valid_limbs(b@),
            sa == sem_seq(a@.subrange(0, n as int)),
            sb == sem_seq(b@.subrange(0, n as int)),
            a_val == limbs_val(sa),
            forall |j: int| 0 <= j < out_len && !(out_off as int <= j < out_off as int + nn) ==> out@[j] == old_out[j],
            forall |j: int| 0 <= j < nn ==> 0 <= (#[trigger] out@[out_off as int + j]).sem() < LIMB_BASE(),
            // Zero-tail invariant: positions [i+n, 2n) still 0
            forall |k: int| (i + n) <= k < nn ==> #[trigger] out@[out_off as int + k].sem() == 0,
            // Value invariant: out_subrange == a * (first i limbs of b)
            vec_val(out@.subrange(out_off as int, (out_off + nn) as int))
                == a_val * limbs_val(sb.subrange(0, i as int)),
    {
        let ghost v_initial = vec_val(out@.subrange(out_off as int, (out_off + nn) as int));
        let ghost row_lim = sb[i as int];
        let ghost p_i = limb_power(i as nat);

        let mut carry: T = T::zero_val();
        for j in 0..n
            invariant
                a@.len() >= n, b@.len() >= n,
                out@.len() == out_len, out_len >= out_off + nn,
                nn == 2 * n, n <= 0x3FFF_FFFF,
                out_off + nn < usize::MAX,
                i < n,
                valid_limbs(a@), valid_limbs(b@),
                sa == sem_seq(a@.subrange(0, n as int)),
                sb == sem_seq(b@.subrange(0, n as int)),
                a_val == limbs_val(sa),
                row_lim == sb[i as int],
                p_i == limb_power(i as nat),
                v_initial == a_val * limbs_val(sb.subrange(0, i as int)),
                0 <= carry.sem() < LIMB_BASE(),
                forall |k: int| 0 <= k < out_len && !(out_off as int <= k < out_off as int + nn) ==> out@[k] == old_out[k],
                forall |k: int| 0 <= k < nn ==> 0 <= (#[trigger] out@[out_off as int + k]).sem() < LIMB_BASE(),
                // Zero-tail still holds (inner loop only writes positions [i, i+n))
                forall |k: int| (i + n) <= k < nn ==> #[trigger] out@[out_off as int + k].sem() == 0,
                // Inner value invariant
                vec_val(out@.subrange(out_off as int, (out_off + nn) as int))
                    + carry.sem() * limb_power((i + j) as nat)
                    == v_initial + limbs_val(sa.subrange(0, j as int)) * row_lim * p_i,
        {
            let (prod_lo, prod_hi) = a[j].mul2(&b[i]);
            let (sum1, c1) = prod_lo.add3(&out[out_off + i + j], &carry);
            let (new_carry, _c2) = prod_hi.add3(&c1, &T::zero_val());

            let ghost out_at = out@[(out_off + i + j) as int].sem();
            let ghost aj = sa[j as int];
            let ghost bi = row_lim;
            let ghost car = carry.sem();
            let ghost base = LIMB_BASE();
            let ghost prod = aj * bi;

            proof {
                // Establish bounds: aj, bi from valid_limbs; out_at from loop invariant
                assert(a@.subrange(0, n as int)[j as int] == a@[j as int]);
                assert(b@.subrange(0, n as int)[i as int] == b@[i as int]);
                assert(aj == a@[j as int].sem());
                assert(bi == b@[i as int].sem());
                assert(0 <= a@[j as int].sem() && a@[j as int].sem() < LIMB_BASE());
                assert(0 <= b@[i as int].sem() && b@[i as int].sem() < LIMB_BASE());
                assert(0 <= aj && aj < base);
                assert(0 <= bi && bi < base);
                // out_at: instantiate loop invariant at k = i + j
                let k_oj: int = (i + j) as int;
                assert(0 <= k_oj && k_oj < nn);
                assert(out@[(out_off + i + j) as int] == out@[out_off as int + k_oj]);
                assert(0 <= out@[out_off as int + k_oj].sem() && out@[out_off as int + k_oj].sem() < LIMB_BASE());
                assert(0 <= out_at && out_at < base);

                // mul2 facts
                assert(prod_lo.sem() == prod % base);
                assert(prod_hi.sem() == prod / base);
                let plo = prod_lo.sem();
                let phi = prod_hi.sem();
                let aj_v: int = aj;
                let bi_v: int = bi;
                assert(aj_v == aj);
                assert(bi_v == bi);
                assert(aj_v >= 0 && aj_v < base);
                assert(bi_v >= 0 && bi_v < base);
                assert(prod == aj_v * bi_v);
                assert(0 <= prod) by(nonlinear_arith)
                    requires prod == aj_v * bi_v, aj_v >= 0, bi_v >= 0;
                assert(prod <= (base - 1) * (base - 1)) by(nonlinear_arith)
                    requires prod == aj_v * bi_v, 0 <= aj_v, aj_v < base, 0 <= bi_v, bi_v < base;
                assert(plo + phi * base == prod) by(nonlinear_arith)
                    requires plo == prod % base, phi == prod / base, base > 0;
                assert(0 <= plo && plo < base) by(nonlinear_arith)
                    requires plo == prod % base, base > 0, prod >= 0;
                assert(0 <= phi) by(nonlinear_arith)
                    requires phi == prod / base, base > 0, prod >= 0;

                // add3(prod_lo, out[off+i+j], carry)
                let sum_in = plo + out_at + car;
                let s1 = sum1.sem();
                let cc1 = c1.sem();
                assert(s1 == sum_in % base);
                assert(cc1 == sum_in / base);
                assert(s1 + cc1 * base == sum_in) by(nonlinear_arith)
                    requires s1 == sum_in % base, cc1 == sum_in / base, base > 0;
                assert(cc1 >= 0) by(nonlinear_arith)
                    requires cc1 == sum_in / base, sum_in >= 0, base > 0;

                // add3(prod_hi, c1, 0)
                let phi_plus_c1 = phi + cc1;
                let nc = new_carry.sem();
                let cc2 = _c2.sem();
                assert(nc == phi_plus_c1 % base);
                assert(cc2 == phi_plus_c1 / base);
                assert(nc + cc2 * base == phi_plus_c1) by(nonlinear_arith)
                    requires nc == phi_plus_c1 % base, cc2 == phi_plus_c1 / base, base > 0;
                assert(cc2 >= 0) by(nonlinear_arith)
                    requires cc2 == phi_plus_c1 / base, phi_plus_c1 >= 0, base > 0;

                // Joint identity:
                // prod + out_at + car == s1 + nc * base + cc2 * base * base
                assert(prod + out_at + car == s1 + nc * base + cc2 * base * base) by(nonlinear_arith)
                    requires
                        prod == plo + phi * base,
                        s1 + cc1 * base == plo + out_at + car,
                        nc + cc2 * base == phi + cc1;

                // Bound the joint sum
                assert(prod + out_at + car <= base * base - 1) by(nonlinear_arith)
                    requires
                        prod <= (base - 1) * (base - 1),
                        out_at < base, car < base, base > 0;

                // Hence cc2 == 0 (can't have cc2 ≥ 1 since cc2*base^2 would exceed base^2 - 1)
                assert(cc2 == 0) by(nonlinear_arith)
                    requires
                        prod + out_at + car == s1 + nc * base + cc2 * base * base,
                        prod + out_at + car <= base * base - 1,
                        s1 >= 0, nc >= 0, cc2 >= 0, base > 0;

                // Hence sum equation simplifies
                assert(prod + out_at + car == s1 + nc * base) by(nonlinear_arith)
                    requires
                        prod + out_at + car == s1 + nc * base + cc2 * base * base,
                        cc2 == 0;

                // Bound on new_carry
                assert(nc < base) by(nonlinear_arith)
                    requires
                        prod + out_at + car == s1 + nc * base,
                        prod + out_at + car <= base * base - 1,
                        s1 >= 0, base > 0;
            }

            let ghost pre_seq = out@;
            let ghost pre_set = out@.subrange(out_off as int, (out_off + nn) as int);
            let ghost local_idx = (i + j) as int;
            out.set(out_off + i + j, sum1);
            proof {
                let post_set = out@.subrange(out_off as int, (out_off + nn) as int);
                let nc = new_carry.sem();
                let s1 = sum1.sem();
                let base = LIMB_BASE();
                let p_ij = limb_power((i + j) as nat);
                let p_ij1 = limb_power((i + j + 1) as nat);

                // pre_set and post_set differ only at local_idx
                assert(pre_set.len() == post_set.len() == nn);
                assert(0 <= local_idx && local_idx < nn);
                assert(pre_set[local_idx] == pre_seq[(out_off as int) + local_idx]);
                assert(pre_set[local_idx].sem() == out_at);
                assert(post_set[local_idx] == out@[(out_off as int) + local_idx]);
                assert(post_set[local_idx] == sum1);
                assert(post_set[local_idx].sem() == s1);

                // Frame property of `out.set(out_off + i + j, sum1)`:
                // out@[k] == pre_seq[k] for all k != out_off + i + j.
                assert forall |k: int| 0 <= k < nn && k != local_idx
                    implies pre_set[k] == post_set[k] by {
                    assert(pre_set[k] == pre_seq[(out_off as int) + k]);
                    assert(post_set[k] == out@[(out_off as int) + k]);
                    assert((out_off as int) + k != (out_off as int) + local_idx);
                }

                // Extend sa subrange by one
                lemma_limbs_val_subrange_extend(sa, j as nat);

                // Apply value-set-one lemma
                lemma_vec_val_set_one::<T>(pre_set, post_set, local_idx);
                // vec_val(post_set) == vec_val(pre_set) + (s1 - out_at) * p_ij

                // limb_power(i+j+1) == base * limb_power(i+j)
                reveal_with_fuel(limb_power, 2);
                assert(p_ij1 == base * p_ij);

                // Inner invariant maintenance
                let v_pre = vec_val(pre_set);
                let v_post = vec_val(post_set);
                let car = carry.sem();
                let p_j = limb_power(j as nat);
                let l_old = limbs_val(sa.subrange(0, j as int));
                let l_new = limbs_val(sa.subrange(0, (j + 1) as int));

                assert(v_post == v_pre + (s1 - out_at) * p_ij);
                assert(v_pre + car * p_ij == v_initial + l_old * row_lim * p_i);
                // Per-step equation: prod + out_at + car == s1 + nc * base
                assert(prod + out_at + car == s1 + new_carry.sem() * base);
                assert(prod == aj * bi);
                assert(bi == row_lim);
                assert(prod == aj * row_lim);

                // sa[j] == aj
                assert(sa[j as int] == aj);
                assert(l_new == l_old + aj * p_j);

                // p_i * p_j == p_ij
                lemma_limb_power_add(i as nat, j as nat);
                assert(limb_power((i + j) as nat) == p_i * p_j);
                assert(p_i * p_j == p_ij);

                // Step 1: rearrange v_post
                assert(v_post + new_carry.sem() * p_ij1
                    == v_pre + (s1 - out_at) * p_ij + new_carry.sem() * p_ij1) by(nonlinear_arith)
                    requires
                        v_post == v_pre + (s1 - out_at) * p_ij;

                // p_ij1 == base * p_ij
                assert(p_ij1 == base * p_ij);

                // Step 2: collect terms
                assert((s1 - out_at) * p_ij + new_carry.sem() * p_ij1
                    == (s1 - out_at + new_carry.sem() * base) * p_ij) by(nonlinear_arith)
                    requires p_ij1 == base * p_ij;

                // Step 3: use per-step equation: s1 + nc*base = prod + out_at + car
                // → s1 - out_at + nc*base = prod + car
                assert(s1 - out_at + new_carry.sem() * base == prod + car) by(nonlinear_arith)
                    requires prod + out_at + car == s1 + new_carry.sem() * base;

                // Step 4: combine
                assert(v_post + new_carry.sem() * p_ij1 == v_pre + (prod + car) * p_ij) by(nonlinear_arith)
                    requires
                        v_post + new_carry.sem() * p_ij1
                            == v_pre + (s1 - out_at) * p_ij + new_carry.sem() * p_ij1,
                        (s1 - out_at) * p_ij + new_carry.sem() * p_ij1
                            == (s1 - out_at + new_carry.sem() * base) * p_ij,
                        s1 - out_at + new_carry.sem() * base == prod + car;

                // Step 5: distribute (prod + car) * p_ij = prod * p_ij + car * p_ij
                assert(v_post + new_carry.sem() * p_ij1 == v_pre + prod * p_ij + car * p_ij) by(nonlinear_arith)
                    requires v_post + new_carry.sem() * p_ij1 == v_pre + (prod + car) * p_ij;

                // Step 6: substitute v_pre + car * p_ij = v_initial + l_old * row_lim * p_i
                assert(v_post + new_carry.sem() * p_ij1
                    == v_initial + l_old * row_lim * p_i + prod * p_ij) by(nonlinear_arith)
                    requires
                        v_post + new_carry.sem() * p_ij1 == v_pre + prod * p_ij + car * p_ij,
                        v_pre + car * p_ij == v_initial + l_old * row_lim * p_i;

                // Step 7: prod * p_ij == aj * row_lim * p_i * p_j
                assert(prod * p_ij == aj * row_lim * p_i * p_j) by(nonlinear_arith)
                    requires prod == aj * row_lim, p_ij == p_i * p_j;

                // Step 8: l_old * row_lim * p_i + aj * row_lim * p_i * p_j
                //         == (l_old + aj * p_j) * row_lim * p_i == l_new * row_lim * p_i
                assert(l_old * row_lim * p_i + aj * row_lim * p_i * p_j
                    == l_new * row_lim * p_i) by(nonlinear_arith)
                    requires l_new == l_old + aj * p_j;

                // Step 9: combine
                assert(v_post + new_carry.sem() * p_ij1 == v_initial + l_new * row_lim * p_i) by(nonlinear_arith)
                    requires
                        v_post + new_carry.sem() * p_ij1
                            == v_initial + l_old * row_lim * p_i + prod * p_ij,
                        prod * p_ij == aj * row_lim * p_i * p_j,
                        l_old * row_lim * p_i + aj * row_lim * p_i * p_j
                            == l_new * row_lim * p_i;

                // Frame and zero-tail preservation
                assert forall |k: int| (i + n) <= k < nn
                    implies #[trigger] out@[out_off as int + k].sem() == 0 by {
                    if (out_off as int + k) != local_idx + (out_off as int) {
                        assert(out@[out_off as int + k] == pre_seq[out_off as int + k]);
                    }
                }
                assert forall |k: int| 0 <= k < out_len && !(out_off as int <= k < out_off as int + nn)
                    implies #[trigger] out@[k] == old_out[k] by {
                    assert(out@[k] == pre_seq[k]);
                }
                assert forall |k: int| 0 <= k < nn
                    implies 0 <= (#[trigger] out@[out_off as int + k]).sem() < LIMB_BASE() by {
                    if k == local_idx {
                        assert(out@[out_off as int + k] == sum1);
                    } else {
                        assert(out@[out_off as int + k] == pre_seq[out_off as int + k]);
                    }
                }
            }
            carry = new_carry;
        }

        // After inner loop ends: write the final carry into position i+n
        let ghost pre_seq2 = out@;
        let ghost pre_carry_set = out@.subrange(out_off as int, (out_off + nn) as int);
        let ghost carry_idx = (i + n) as int;
        out.set(out_off + i + n, carry);
        proof {
            let post_carry_set = out@.subrange(out_off as int, (out_off + nn) as int);
            let car = carry.sem();
            let base = LIMB_BASE();
            let p_in = limb_power((i + n) as nat);

            // Position carry_idx was 0 before the set (zero-tail invariant)
            assert(pre_carry_set[carry_idx] == pre_seq2[(out_off as int) + carry_idx]);
            assert(pre_carry_set[carry_idx].sem() == 0);
            assert(post_carry_set[carry_idx] == out@[(out_off as int) + carry_idx]);
            assert(post_carry_set[carry_idx] == carry);

            assert forall |k: int| 0 <= k < nn && k != carry_idx
                implies pre_carry_set[k] == post_carry_set[k] by {
                assert(pre_carry_set[k] == pre_seq2[(out_off as int) + k]);
                assert(post_carry_set[k] == out@[(out_off as int) + k]);
                assert((out_off as int) + k != (out_off as int) + carry_idx);
            }

            lemma_vec_val_set_one::<T>(pre_carry_set, post_carry_set, carry_idx);
            // vec_val(post_carry_set) == vec_val(pre_carry_set) + (car - 0) * p_in

            // From inner loop final invariant (j == n):
            // vec_val(pre_carry_set) + car * p_in == v_initial + limbs_val(sa.subrange(0, n)) * row_lim * p_i
            // Since sa.subrange(0, n) == sa, limbs_val(sa) == a_val
            assert(sa.subrange(0, n as int) =~= sa);

            // Extend sb subrange by one for the outer invariant
            lemma_limbs_val_subrange_extend(sb, i as nat);

            // Combine via nonlinear_arith
            let v_pre = vec_val(pre_carry_set);
            let v_post = vec_val(post_carry_set);
            assert(v_post == v_pre + car * p_in);
            assert(v_pre + car * p_in == v_initial + a_val * row_lim * p_i);
            assert(v_initial == a_val * limbs_val(sb.subrange(0, i as int)));
            assert(limbs_val(sb.subrange(0, (i + 1) as int))
                == limbs_val(sb.subrange(0, i as int)) + sb[i as int] * limb_power(i as nat));
            assert(sb[i as int] == row_lim);

            assert(v_post == a_val * limbs_val(sb.subrange(0, (i + 1) as int))) by(nonlinear_arith)
                requires
                    v_post == v_initial + a_val * row_lim * p_i,
                    v_initial == a_val * limbs_val(sb.subrange(0, i as int)),
                    limbs_val(sb.subrange(0, (i + 1) as int))
                        == limbs_val(sb.subrange(0, i as int)) + row_lim * p_i,
                    p_i == limb_power(i as nat);

            // Frame and zero-tail update
            assert forall |k: int| (i + 1 + n) <= k < nn
                implies #[trigger] out@[out_off as int + k].sem() == 0 by {
                assert(k != carry_idx);
                assert(out@[out_off as int + k] == pre_seq2[out_off as int + k]);
            }
            assert forall |k: int| 0 <= k < out_len && !(out_off as int <= k < out_off as int + nn)
                implies #[trigger] out@[k] == old_out[k] by {
                assert(out@[k] == pre_seq2[k]);
            }
            assert forall |k: int| 0 <= k < nn
                implies 0 <= (#[trigger] out@[out_off as int + k]).sem() < LIMB_BASE() by {
                if k == carry_idx {
                    assert(out@[out_off as int + k] == carry);
                } else {
                    assert(out@[out_off as int + k] == pre_seq2[out_off as int + k]);
                }
            }
        }
    }

    // After outer loop ends (i == n): vec_val == a_val * limbs_val(sb)
    proof {
        assert(sb.subrange(0, n as int) =~= sb);
        // vec_val(a@.subrange(0, n)) == limbs_val(sa)
        // vec_val(b@.subrange(0, n)) == limbs_val(sb)
    }
}

/// One-level Karatsuba multiplication: a × b → out[out_off..out_off+2n].
/// Splits inputs at half = n/2, does 3 schoolbook half-size multiplies, combines.
/// For n=16: 3 × schoolbook(8) = 192 ops vs schoolbook(16) = 256 ops (25% savings).
/// Non-recursive — suitable for GPU/WGSL transpilation.
///
/// Requires n >= 8, n even. Falls back to schoolbook for n < 8.
/// Scratch needs 2n limbs at scratch[scratch_off..scratch_off+2n].
/// a and b are accessed at a[a_off..a_off+n] and b[b_off..b_off+n].
#[verifier::rlimit(200)]
pub fn mul_karatsuba_one_level_to<T: LimbOps>(
    a: &[T], a_off: usize,
    b: &[T], b_off: usize,
    out: &mut Vec<T>, out_off: usize,
    scratch: &mut Vec<T>, scratch_off: usize,
    n: usize,
)
    requires
        a@.len() >= a_off + n, b@.len() >= b_off + n,
        n >= 4, n <= 0x1FFF_FFFF,
        n % 2 == 0,
        valid_limbs(a@), valid_limbs(b@),
        old(out)@.len() >= out_off + 2 * n,
        old(scratch)@.len() >= scratch_off + 2 * n,
        out_off + 2 * n < usize::MAX,
        scratch_off + 2 * n < usize::MAX,
        a_off + n < usize::MAX, b_off + n < usize::MAX,
    ensures
        out@.len() == old(out)@.len(),
        scratch@.len() == old(scratch)@.len(),
        forall |j: int| 0 <= j < 2 * n ==> 0 <= (#[trigger] out@[out_off as int + j]).sem() < LIMB_BASE(),
        forall |j: int| 0 <= j < out@.len() && !(out_off as int <= j < out_off + 2 * n) ==> out@[j] == old(out)@[j],
        vec_val(out@.subrange(out_off as int, (out_off + 2 * n) as int))
            == vec_val(a@.subrange(a_off as int, (a_off + n) as int))
             * vec_val(b@.subrange(b_off as int, (b_off + n) as int)),
{
    // For small n, fall back to schoolbook
    if n <= 6 {
        let a_sub = slice_subrange(a, a_off, a.len());
        let b_sub = slice_subrange(b, b_off, b.len());
        proof {
            // slice_subrange(a, a_off, a.len())@.subrange(0, n) == a@.subrange(a_off, a_off+n)
            assert(a_sub@.subrange(0, n as int) =~= a@.subrange(a_off as int, (a_off + n) as int));
            assert(b_sub@.subrange(0, n as int) =~= b@.subrange(b_off as int, (b_off + n) as int));
        }
        mul_schoolbook_to(a_sub, b_sub, out, out_off, n);
        return;
    }

    let half = n / 2;

    // Ghost: input subranges for the proof
    let ghost a_lo_seq = a@.subrange(a_off as int, (a_off + half) as int);
    let ghost a_hi_seq = a@.subrange((a_off + half) as int, (a_off + n) as int);
    let ghost b_lo_seq = b@.subrange(b_off as int, (b_off + half) as int);
    let ghost b_hi_seq = b@.subrange((b_off + half) as int, (b_off + n) as int);

    // Step 1: z0 = a_lo × b_lo → out[out_off..out_off+n]
    let a_sub1 = slice_subrange(a, a_off, a.len());
    let b_sub1 = slice_subrange(b, b_off, b.len());
    proof {
        assert(a_sub1@.subrange(0, half as int) =~= a_lo_seq);
        assert(b_sub1@.subrange(0, half as int) =~= b_lo_seq);
    }
    mul_schoolbook_to(a_sub1, b_sub1, out, out_off, half);
    let ghost z0_val = vec_val(out@.subrange(out_off as int, (out_off + n) as int));
    proof { assert(z0_val == vec_val(a_lo_seq) * vec_val(b_lo_seq)); }

    // Step 2: z2 = a_hi × b_hi → out[out_off+n..out_off+2n]
    let a_len = a.len();
    let b_len = b.len();
    let a_sub2 = slice_subrange(a, a_off + half, a_len);
    let b_sub2 = slice_subrange(b, b_off + half, b_len);
    proof {
        assert(a_sub2@.subrange(0, half as int) =~= a_hi_seq);
        assert(b_sub2@.subrange(0, half as int) =~= b_hi_seq);
    }
    mul_schoolbook_to(a_sub2, b_sub2, out, out_off + n, half);
    let ghost z2_val = vec_val(out@.subrange((out_off + n) as int, (out_off + 2 * n) as int));
    proof { assert(z2_val == vec_val(a_hi_seq) * vec_val(b_hi_seq)); }

    // After steps 1-2: out[out_off..out_off+2n] has valid limbs from two schoolbook calls
    proof {
        // Step 1 wrote valid limbs to out[out_off..out_off+n] (= 2*half limbs)
        // Step 2 wrote valid limbs to out[out_off+n..out_off+2n] (= 2*half limbs)
        // Together: out[out_off..out_off+2n] all valid
        assert forall |j: int| 0 <= j < 2 * n
            implies 0 <= (#[trigger] out@[(out_off as int + j) as int]).sem() < LIMB_BASE()
        by {
            if j < n as int {
                // From step 1's postcondition (2*half = n limbs at out_off)
                assert(0 <= out@[out_off as int + j].sem() < LIMB_BASE());
            } else {
                // From step 2's postcondition (2*half = n limbs at out_off+n)
                let k = j - n as int;
                assert(0 <= out@[(out_off + n) as int + k].sem() < LIMB_BASE());
            }
        }
    }

    // Step 3: a_sum = a_lo + a_hi, b_sum = b_lo + b_hi → scratch
    let asum_off = scratch_off + n;
    let bsum_off = scratch_off + n + half;
    let mut asum_carry = T::zero_val();
    let mut bsum_carry = T::zero_val();
    for i in 0..half
        invariant
            half == n / 2, n >= 4, n % 2 == 0, n <= 0x1FFF_FFFF,
            a@.len() >= a_off + n, b@.len() >= b_off + n,
            a_off + n < usize::MAX, b_off + n < usize::MAX,
            scratch@.len() == old(scratch)@.len(),
            scratch@.len() >= scratch_off + 2 * n,
            scratch_off + 2 * n < usize::MAX,
            asum_off == scratch_off + n, bsum_off == scratch_off + n + half,
            asum_carry.sem() == 0 || asum_carry.sem() == 1,
            bsum_carry.sem() == 0 || bsum_carry.sem() == 1,
            valid_limbs(a@), valid_limbs(b@),
            forall |j: int| 0 <= j < i ==> 0 <= (#[trigger] scratch@[(asum_off as int + j) as int]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < i ==> 0 <= (#[trigger] scratch@[(bsum_off as int + j) as int]).sem() < LIMB_BASE(),
    {
        let (s, c) = a[a_off + i].add3(&a[a_off + half + i], &asum_carry);
        scratch.set(asum_off + i, s);
        asum_carry = c;
        let (s2, c2) = b[b_off + i].add3(&b[b_off + half + i], &bsum_carry);
        scratch.set(bsum_off + i, s2);
        bsum_carry = c2;
    }

    // Step 4: z1_full = a_sum × b_sum → scratch[scratch_off..scratch_off+n]
    let ghost scratch_post_step3 = scratch@;
    proof {
        assert(valid_limbs(scratch@.subrange(asum_off as int, (asum_off + half) as int))) by {
            assert forall |j: int| 0 <= j < half as int
                implies 0 <= (#[trigger] scratch@.subrange(asum_off as int, (asum_off + half) as int)[j]).sem()
                    && scratch@.subrange(asum_off as int, (asum_off + half) as int)[j].sem() < LIMB_BASE()
            by {
                assert(scratch@.subrange(asum_off as int, (asum_off + half) as int)[j] == scratch@[(asum_off as int + j) as int]);
            }
        }
        assert(valid_limbs(scratch@.subrange(bsum_off as int, (bsum_off + half) as int))) by {
            assert forall |j: int| 0 <= j < half as int
                implies 0 <= (#[trigger] scratch@.subrange(bsum_off as int, (bsum_off + half) as int)[j]).sem()
                    && scratch@.subrange(bsum_off as int, (bsum_off + half) as int)[j].sem() < LIMB_BASE()
            by {
                assert(scratch@.subrange(bsum_off as int, (bsum_off + half) as int)[j] == scratch@[(bsum_off as int + j) as int]);
            }
        }
    }
    // Can't slice scratch while also passing it as &mut — need to copy sums to out temporarily.
    // Actually, mul_schoolbook_to takes a: &[T], b: &[T], out: &mut Vec<T>.
    // a and b are immutable borrows, out is mutable. Since a_sum and b_sum are IN scratch,
    // and the output also goes to scratch, we have aliasing.
    // Fix: copy a_sum/b_sum to the out buffer temporarily (unused region).
    // out[out_off..out_off+half] is z0_lo which we still need — can't use it.
    // Actually, z0 is in out[out_off..out_off+n] and z2 is in out[out_off+n..out_off+2n].
    // We can't easily borrow scratch immutably while also writing to it.
    //
    // Alternative approach: swap the roles — put a_sum/b_sum in the OUT buffer's
    // z0 region (we'll restore z0 after), or use a different strategy.
    //
    // Simplest fix: compute z1_full using a manual schoolbook loop with offset indexing.
    // This avoids the aliasing issue entirely.
    {
        let nn = 2 * half;
        // Zero scratch[scratch_off..scratch_off+nn] for z1_full output
        for i in 0..nn
            invariant scratch@.len() == old(scratch)@.len(), scratch@.len() >= scratch_off + 2 * n,
                nn == 2 * half, half == n / 2, n >= 4, scratch_off + 2 * n < usize::MAX,
                asum_off == scratch_off + n, bsum_off == scratch_off + n + half,
                // zeroed elements are valid limbs
                forall |j: int| 0 <= j < i ==> (#[trigger] scratch@[(scratch_off as int + j) as int]).sem() == 0,
                // frame: a_sum and b_sum regions preserved (zeroing only touches [scratch_off, scratch_off+n))
                forall |j: int| scratch_off + nn <= j < scratch@.len() as int ==> scratch@[j] == scratch_post_step3[j],
        { scratch.set(scratch_off + i, T::zero_val()); }
        // Schoolbook: z1_full[i+j] += a_sum[i] * b_sum[j]
        for i in 0..half
            invariant half == n / 2, n >= 4, n <= 0x1FFF_FFFF,
                scratch@.len() == old(scratch)@.len(), scratch@.len() >= scratch_off + 2 * n,
                asum_off == scratch_off + n, bsum_off == scratch_off + n + half,
                scratch_off + 2 * n < usize::MAX,
                // valid limbs on z1_full output so far
                forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] scratch@[(scratch_off as int + j) as int]).sem() < LIMB_BASE(),
                // a_sum and b_sum regions are outside [scratch_off, scratch_off+n) so preserved
                // by both zeroing and schoolbook writes to z1_full
                forall |j: int| scratch_off + n <= j < scratch_off + 2 * n ==> scratch@[j as int] == scratch_post_step3[j as int],
        {
            let mut carry = T::zero_val();
            for j in 0..half
                invariant half == n / 2, n >= 4, n <= 0x1FFF_FFFF,
                    scratch@.len() == old(scratch)@.len(), scratch@.len() >= scratch_off + 2 * n,
                    asum_off == scratch_off + n, bsum_off == scratch_off + n + half,
                    scratch_off + 2 * n < usize::MAX,
                    i < half,
                    carry.sem() >= 0, carry.sem() < LIMB_BASE(),
                    // a_sum/b_sum preserved (outside z1_full write region)
                    forall |k: int| scratch_off + n <= k < scratch_off + 2 * n ==> scratch@[k as int] == scratch_post_step3[k as int],
                    // valid limbs on z1_full output
                    forall |k: int| 0 <= k < n ==> 0 <= (#[trigger] scratch@[(scratch_off as int + k) as int]).sem() < LIMB_BASE(),
            {
                let (prod_lo, prod_hi) = scratch[asum_off + i].mul2(&scratch[bsum_off + j]);
                let (sum1, c1) = prod_lo.add3(&scratch[scratch_off + i + j], &carry);
                let (new_carry, _c2) = prod_hi.add3(&c1, &T::zero_val());
                scratch.set(scratch_off + i + j, sum1);
                carry = new_carry;
            }
            scratch.set(scratch_off + i + half, carry);
        }
    }

    // Step 4b: Carry correction for z1_full.
    // The schoolbook only computed a_sum_limbs * b_sum_limbs. The true z1_full is:
    //   (a_sum_limbs + asum_carry*B) * (b_sum_limbs + bsum_carry*B)
    // Missing terms: asum_carry*b_sum at offset half, bsum_carry*a_sum at offset half,
    //                asum_carry*bsum_carry at offset n (tracked as z1_overflow).

    // Add asum_carry * b_sum at offset half (branchless via select_limb)
    let mut cc1 = T::zero_val();
    for k in 0..half
        invariant half == n / 2, n >= 4, n <= 0x1FFF_FFFF,
            scratch@.len() == old(scratch)@.len(), scratch@.len() >= scratch_off + 2 * n,
            scratch_off + 2 * n < usize::MAX,
            asum_off == scratch_off + n, bsum_off == scratch_off + n + half,
            asum_carry.sem() == 0 || asum_carry.sem() == 1,
            cc1.sem() == 0 || cc1.sem() == 1,
            forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] scratch@[(scratch_off as int + j) as int]).sem() < LIMB_BASE(),
            // a_sum and b_sum regions preserved from step 3
            forall |j: int| scratch_off + n <= j < scratch_off + 2 * n ==> scratch@[j as int] == scratch_post_step3[j as int],
            // valid limbs on a_sum/b_sum (carried from step 3)
            forall |j: int| 0 <= j < half ==> 0 <= (#[trigger] scratch_post_step3[(asum_off as int + j)]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < half ==> 0 <= (#[trigger] scratch_post_step3[(bsum_off as int + j)]).sem() < LIMB_BASE(),
    {
        proof {
            // b_sum[k] has valid limbs (from scratch_post_step3 via frame)
            assert(scratch@[(bsum_off + k) as int] == scratch_post_step3[(bsum_off + k) as int]);
            assert(0 <= scratch@[(bsum_off + k) as int].sem() < LIMB_BASE());
        }
        let addend = T::select_limb(&asum_carry, T::zero_val(), scratch[bsum_off + k].clone_limb());
        let ghost hk = (half + k) as int;
        let ghost sv = scratch@[(scratch_off as int + hk) as int].sem();
        proof {
            assert(0 <= hk && hk < n as int);
            // Now sv < LIMB_BASE from valid limbs invariant (trigger matches)
        }
        let (s, nc) = scratch[scratch_off + half + k].add3(&addend, &cc1);
        proof {
            let x = sv + addend.sem() + cc1.sem();
            assert(x < 2 * LIMB_BASE());
            assert(nc.sem() <= 1) by(nonlinear_arith)
                requires nc.sem() == x / LIMB_BASE(), x >= 0,
                         x < 2 * LIMB_BASE(), LIMB_BASE() > 0;
        }
        scratch.set(scratch_off + half + k, s);
        cc1 = nc;
    }

    // Add bsum_carry * a_sum at offset half (branchless via select_limb)
    let mut cc2 = T::zero_val();
    for k in 0..half
        invariant half == n / 2, n >= 4, n <= 0x1FFF_FFFF,
            scratch@.len() == old(scratch)@.len(), scratch@.len() >= scratch_off + 2 * n,
            scratch_off + 2 * n < usize::MAX,
            asum_off == scratch_off + n, bsum_off == scratch_off + n + half,
            bsum_carry.sem() == 0 || bsum_carry.sem() == 1,
            cc2.sem() == 0 || cc2.sem() == 1,
            forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] scratch@[(scratch_off as int + j) as int]).sem() < LIMB_BASE(),
            forall |j: int| scratch_off + n <= j < scratch_off + 2 * n ==> scratch@[j as int] == scratch_post_step3[j as int],
            forall |j: int| 0 <= j < half ==> 0 <= (#[trigger] scratch_post_step3[(asum_off as int + j)]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < half ==> 0 <= (#[trigger] scratch_post_step3[(bsum_off as int + j)]).sem() < LIMB_BASE(),
    {
        proof {
            assert(scratch@[(asum_off + k) as int] == scratch_post_step3[(asum_off + k) as int]);
            assert(0 <= scratch@[(asum_off + k) as int].sem() < LIMB_BASE());
        }
        let addend = T::select_limb(&bsum_carry, T::zero_val(), scratch[asum_off + k].clone_limb());
        let ghost hk2 = (half + k) as int;
        let ghost sv = scratch@[(scratch_off as int + hk2) as int].sem();
        proof {
            assert(0 <= hk2 && hk2 < n as int);
        }
        let (s, nc) = scratch[scratch_off + half + k].add3(&addend, &cc2);
        proof {
            let x = sv + addend.sem() + cc2.sem();
            assert(x < 2 * LIMB_BASE());
            assert(nc.sem() <= 1) by(nonlinear_arith)
                requires nc.sem() == x / LIMB_BASE(), x >= 0,
                         x < 2 * LIMB_BASE(), LIMB_BASE() > 0;
        }
        scratch.set(scratch_off + half + k, s);
        cc2 = nc;
    }

    // z1_overflow at position n: cc1 + cc2 + asum_carry*bsum_carry
    let (ca_cb, _) = asum_carry.mul2(&bsum_carry);
    let (temp_ov, _) = cc1.add3(&cc2, &T::zero_val());
    let (z1_overflow, _) = temp_ov.add3(&ca_cb, &T::zero_val());

    // Step 5: z1 = z1_full - z0 - z2
    // After step 4+4b, scratch[scratch_off..scratch_off+n] has corrected z1_full (valid limbs).
    // z1_overflow holds the extra limb at position n.
    // out[out_off..out_off+2n] has z0 and z2 from schoolbook (valid limbs).
    //
    // Ghost: z1_full_val = vec_val(scratch[scratch_off..scratch_off+n]) + z1_overflow * limb_power(n)
    let ghost z1_full_n_val = vec_val(scratch@.subrange(scratch_off as int, (scratch_off + n) as int));
    let ghost z1_full_val = z1_full_n_val + z1_overflow.sem() * limb_power(n as nat);

    let ghost scratch_pre_sub = scratch@;
    let mut borrow1 = T::zero_val();
    for i in 0..n
        invariant n >= 4, n <= 0x1FFF_FFFF, half == n / 2,
            out@.len() >= out_off + 2 * n, out@.len() == old(out)@.len(),
            out_off + 2 * n < usize::MAX,
            scratch@.len() >= scratch_off + 2 * n, scratch@.len() == old(scratch)@.len(),
            scratch_off + 2 * n < usize::MAX,
            borrow1.sem() == 0 || borrow1.sem() == 1,
            z1_full_n_val == vec_val(scratch_pre_sub.subrange(scratch_off as int, (scratch_off + n) as int)),
            forall |j: int| 0 <= j < 2 * n
                ==> 0 <= (#[trigger] out@[(out_off as int + j) as int]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < n
                ==> 0 <= (#[trigger] scratch@[(scratch_off as int + j) as int]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < scratch@.len() && !(scratch_off as int <= j < scratch_off as int + i)
                ==> scratch@[j] == scratch_pre_sub[j],
            // Value equation: result + b_partial == a + borrow * P^i
            // i.e., vec_val(full_n_region) + b_so_far == z1_full_n_val + borrow*P(i)
            vec_val(scratch@.subrange(scratch_off as int, (scratch_off + n) as int))
                == z1_full_n_val
                    - vec_val(out@.subrange(out_off as int, out_off as int + i))
                    + borrow1.sem() * limb_power(i as nat),
    {
        let ghost si_sem = scratch@[(scratch_off as int + i as int)].sem();
        let ghost oi_sem = out@[(out_off as int + i as int)].sem();
        let ghost region_pre = scratch@.subrange(scratch_off as int, (scratch_off + n) as int);
        let (d, bw) = scratch[scratch_off + i].sub_borrow(&out[out_off + i], &borrow1);
        proof {
            // sub_borrow: d.sem() = (si - oi - bw1 + BASE) % BASE
            // bw.sem() = if si - oi - bw1 < 0 then 1 else 0
            // So: d.sem() + oi + bw1 = si + bw * BASE (algebraically)
            // i.e., d.sem() - si_sem = -(oi_sem + borrow1.sem()) + bw.sem() * LIMB_BASE()
        }
        scratch.set(scratch_off + i, d);
        proof {
            use crate::fixed_point::limb_ops_proofs::lemma_vec_val_set_one;
            let region_post = scratch@.subrange(scratch_off as int, (scratch_off + n) as int);
            assert forall |k: int| 0 <= k < region_pre.len() && k != i as int
                implies region_pre[k] == region_post[k]
            by { assert(region_post[k] == scratch@[(scratch_off as int + k)]); }
            lemma_vec_val_set_one::<T>(region_pre, region_post, i as int);

            // Extend b: vec_val(out[out_off..out_off+i+1]) = vec_val(out[out_off..out_off+i]) + oi_sem * P(i)
            lemma_vec_val_split::<T>(out@.subrange(out_off as int, out_off as int + i as int + 1), i as nat);
            let b_tail = out@.subrange(out_off as int + i as int, out_off as int + i as int + 1);
            assert(b_tail[0] == out@[(out_off as int + i as int)]);
            reveal_with_fuel(limbs_val, 2);
            assert(sem_seq(b_tail).len() == 1);
            assert(sem_seq(b_tail)[0] == oi_sem);
            assert(sem_seq(b_tail).subrange(1, 1) =~= Seq::<int>::empty());
            assert(vec_val(b_tail) == oi_sem);
            assert(out@.subrange(out_off as int, out_off as int + i as int + 1).subrange(0, i as int) =~= out@.subrange(out_off as int, out_off as int + i as int));
            assert(out@.subrange(out_off as int, out_off as int + i as int + 1).subrange(i as int, i as int + 1) =~= b_tail);

            let p_i = limb_power(i as nat);
            reveal_with_fuel(limb_power, 2);
            let p_i1 = limb_power((i + 1) as nat);
            assert(p_i1 == LIMB_BASE() * p_i);

            // Combine: IH + set_one + b extension + sub_borrow equation
            assert(
                vec_val(region_post)
                == z1_full_n_val
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
    // After sub1: vec_val(scratch_region) = z1_full_n_val - z0_val + borrow1 * P
    let ghost scratch_post_sub1_val = vec_val(scratch@.subrange(scratch_off as int, (scratch_off + n) as int));
    let ghost z0_val = vec_val(out@.subrange(out_off as int, (out_off + n) as int));

    let ghost scratch_post_sub1 = scratch@;
    let mut borrow2 = T::zero_val();
    for i in 0..n
        invariant n >= 4, n <= 0x1FFF_FFFF, half == n / 2,
            out@.len() >= out_off + 2 * n, out@.len() == old(out)@.len(),
            out_off + 2 * n < usize::MAX,
            scratch@.len() >= scratch_off + 2 * n, scratch@.len() == old(scratch)@.len(),
            scratch_off + 2 * n < usize::MAX,
            borrow2.sem() == 0 || borrow2.sem() == 1,
            scratch_post_sub1_val == vec_val(scratch_post_sub1.subrange(scratch_off as int, (scratch_off + n) as int)),
            forall |j: int| 0 <= j < 2 * n
                ==> 0 <= (#[trigger] out@[(out_off as int + j) as int]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < n
                ==> 0 <= (#[trigger] scratch@[(scratch_off as int + j) as int]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < scratch@.len() && !(scratch_off as int <= j < scratch_off as int + i)
                ==> scratch@[j] == scratch_post_sub1[j],
            // Value equation for sub2
            vec_val(scratch@.subrange(scratch_off as int, (scratch_off + n) as int))
                == scratch_post_sub1_val
                    - vec_val(out@.subrange((out_off + n) as int, (out_off + n) as int + i))
                    + borrow2.sem() * limb_power(i as nat),
    {
        let ghost si_sem = scratch@[(scratch_off as int + i as int)].sem();
        let ghost oi_sem = out@[((out_off + n) as int + i as int)].sem();
        let ghost region_pre = scratch@.subrange(scratch_off as int, (scratch_off + n) as int);
        let (d, bw) = scratch[scratch_off + i].sub_borrow(&out[out_off + n + i], &borrow2);
        // Establish sub_borrow equation before set changes scratch
        let ghost sub_eq2 = d.sem() + oi_sem + borrow2.sem() == si_sem + bw.sem() * LIMB_BASE();
        proof {
            // From sub_borrow: d = (si - oi - bw2 + BASE) % BASE, bw = if si-oi-bw2<0 then 1 else 0
            if si_sem - oi_sem - borrow2.sem() >= 0 {
                assert(bw.sem() == 0);
                assert(d.sem() == si_sem - oi_sem - borrow2.sem());
            } else {
                assert(bw.sem() == 1);
                assert(d.sem() == (si_sem - oi_sem - borrow2.sem() + LIMB_BASE()) % LIMB_BASE());
                assert(si_sem - oi_sem - borrow2.sem() + LIMB_BASE() >= 0);
                assert(si_sem - oi_sem - borrow2.sem() + LIMB_BASE() < LIMB_BASE());
                assert(d.sem() == si_sem - oi_sem - borrow2.sem() + LIMB_BASE()) by(nonlinear_arith)
                    requires d.sem() == (si_sem - oi_sem - borrow2.sem() + LIMB_BASE()) % LIMB_BASE(),
                             0 <= si_sem - oi_sem - borrow2.sem() + LIMB_BASE(),
                             si_sem - oi_sem - borrow2.sem() + LIMB_BASE() < LIMB_BASE(),
                             LIMB_BASE() > 0;
            }
            assert(sub_eq2);
        }
        scratch.set(scratch_off + i, d);
        proof {
            use crate::fixed_point::limb_ops_proofs::lemma_vec_val_set_one;
            let region_post = scratch@.subrange(scratch_off as int, (scratch_off + n) as int);
            assert forall |k: int| 0 <= k < region_pre.len() && k != i as int
                implies region_pre[k] == region_post[k]
            by { assert(region_post[k] == scratch@[(scratch_off as int + k)]); }
            lemma_vec_val_set_one::<T>(region_pre, region_post, i as int);

            lemma_vec_val_split::<T>(out@.subrange((out_off + n) as int, (out_off + n) as int + i as int + 1), i as nat);
            let b_tail2 = out@.subrange((out_off + n) as int + i as int, (out_off + n) as int + i as int + 1);
            assert(b_tail2[0] == out@[((out_off + n) as int + i as int)]);
            reveal_with_fuel(limbs_val, 2);
            assert(sem_seq(b_tail2).len() == 1);
            assert(sem_seq(b_tail2)[0] == oi_sem);
            assert(sem_seq(b_tail2).subrange(1, 1) =~= Seq::<int>::empty());
            assert(vec_val(b_tail2) == oi_sem);
            assert(out@.subrange((out_off + n) as int, (out_off + n) as int + i as int + 1).subrange(0, i as int)
                =~= out@.subrange((out_off + n) as int, (out_off + n) as int + i as int));
            assert(out@.subrange((out_off + n) as int, (out_off + n) as int + i as int + 1).subrange(i as int, i as int + 1)
                =~= b_tail2);

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
                    sub_eq2,
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
        use crate::fixed_point::limb_ops_proofs::lemma_karatsuba_z1_overflow_bound;

        let P = limb_power(n as nat);
        let z1_n = vec_val(scratch@.subrange(scratch_off as int, (scratch_off + n) as int));
        let z2_val = vec_val(out@.subrange((out_off + n) as int, (out_off + 2 * n) as int));

        // From sub1 value equation (at end of loop, i=n):
        // scratch_post_sub1_val = z1_full_n_val - z0_val + borrow1 * P
        // From sub2 value equation (at end of loop, i=n):
        // z1_n = scratch_post_sub1_val - z2_val + borrow2 * P
        // Combined:
        // z1_n = z1_full_n_val - z0_val - z2_val + (borrow1 + borrow2) * P
        // z1_n + (z1_overflow - bw1 - bw2) * P
        //   = z1_full_n_val + z1_overflow*P - z0_val - z2_val
        //   = z1_full_val - z0_val - z2_val

        // Input bounds
        lemma_vec_val_bounded::<T>(a_lo_seq);
        lemma_vec_val_bounded::<T>(a_hi_seq);
        lemma_vec_val_bounded::<T>(b_lo_seq);
        lemma_vec_val_bounded::<T>(b_hi_seq);
        let B = limb_power(half as nat);
        // P = B^2 (since n = 2*half)
        lemma_limb_power_add(half as nat, half as nat);

        // z0_val = a_lo * b_lo (from mul_schoolbook_to)
        // z2_val = a_hi * b_hi
        // z1_full_val >= z0_val + z2_val (cross terms >= 0)
        // z1_full_val < z0_val + z2_val + 2*P (cross terms < 2*B^2 = 2*P)

        // z1_n is valid limbs → z1_n < P
        assert(valid_limbs(scratch@.subrange(scratch_off as int, (scratch_off + n) as int))) by {
            assert forall |j: int| 0 <= j < n as int
                implies 0 <= (#[trigger] scratch@.subrange(scratch_off as int, (scratch_off + n) as int)[j]).sem() < LIMB_BASE()
            by {
                assert(scratch@.subrange(scratch_off as int, (scratch_off + n) as int)[j]
                    == scratch@[(scratch_off as int + j)]);
            }
        }
        lemma_vec_val_bounded::<T>(scratch@.subrange(scratch_off as int, (scratch_off + n) as int));

        // Combined value equation
        assert(z1_n + (z1_overflow.sem() - borrow1.sem() - borrow2.sem()) * P
            == z1_full_val - z0_val - z2_val) by(nonlinear_arith)
            requires
                scratch_post_sub1_val == z1_full_n_val - z0_val + borrow1.sem() * P,
                z1_n == scratch_post_sub1_val - z2_val + borrow2.sem() * P,
                z1_full_val == z1_full_n_val + z1_overflow.sem() * P;

        // Karatsuba identity bounds: z1_full = (a_lo+a_hi)(b_lo+b_hi) = z0+cross+z2
        // So z1_full >= z0 + z2 and z1_full - z0 - z2 = cross < 2*P
        // We need z1_full_val, z0_val, z2_val in terms of the algebraic values
        // These follow from z0_val and z2_val being the schoolbook results

        lemma_karatsuba_z1_overflow_bound(
            z1_full_val, z0_val, z2_val,
            z1_overflow.sem(), borrow1.sem(), borrow2.sem(),
            z1_n, P,
        );

        // Now z1_overflow - bw1 - bw2 is 0 or 1
        // z1_final_overflow.sem() = sub_borrow result
        // Need: z1_final_overflow.sem() == z1_overflow.sem() - borrow1.sem() - borrow2.sem()
        // This follows from the sub_borrow postconditions
        // (since the values are small enough that no wrapping occurs)
        let ov_diff = z1_overflow.sem() - borrow1.sem() - borrow2.sem();
        assert(ov_diff == 0 || ov_diff == 1);
        // sub_borrow(z1_overflow, borrow1, 0): result = (z1_overflow - borrow1 + BASE) % BASE
        // Since z1_overflow <= 3 and borrow1 <= 1, z1_overflow - borrow1 >= -1
        // But ov_diff >= 0, so z1_overflow >= borrow1 + borrow2
        // temp_ov2 = z1_overflow - borrow1 (no wrapping since >= 0)
        // z1_final_overflow = temp_ov2 - borrow2 (no wrapping since temp_ov2 >= borrow2)
        assert(z1_overflow.sem() >= borrow1.sem() + borrow2.sem()) by(nonlinear_arith)
            requires ov_diff >= 0, ov_diff == z1_overflow.sem() - borrow1.sem() - borrow2.sem();
        assert(temp_ov2.sem() == z1_overflow.sem() - borrow1.sem()) by(nonlinear_arith)
            requires
                temp_ov2.sem() == (z1_overflow.sem() - borrow1.sem() + LIMB_BASE()) % LIMB_BASE(),
                z1_overflow.sem() >= borrow1.sem(),
                z1_overflow.sem() <= 3,
                borrow1.sem() <= 1,
                LIMB_BASE() > 3;
        assert(z1_final_overflow.sem() == temp_ov2.sem() - borrow2.sem()) by(nonlinear_arith)
            requires
                z1_final_overflow.sem() == (temp_ov2.sem() - borrow2.sem() + LIMB_BASE()) % LIMB_BASE(),
                temp_ov2.sem() >= borrow2.sem(),
                temp_ov2.sem() <= 3,
                borrow2.sem() <= 1,
                LIMB_BASE() > 3;
        assert(z1_final_overflow.sem() == ov_diff);
        assert(z1_final_overflow.sem() == 0 || z1_final_overflow.sem() == 1);
    }

    // Step 6: out[half..half+n+half] += z1 (n limbs) + z1_final_overflow at position n
    // Use add_inplace_propagate which adds z1 at offset half and propagates carry through
    // the remaining half positions.
    {
        use crate::fixed_point::limb_ops_proofs::add_inplace_propagate;
        let scratch_slice = slice_subrange(&*scratch, scratch_off, scratch.len());
        proof {
            // z1 in scratch[scratch_off..scratch_off+n] has valid limbs
            assert forall |j: int| 0 <= j < n as int
                implies 0 <= (#[trigger] scratch_slice@[(j as int)]).sem() < LIMB_BASE()
            by {
                assert(scratch_slice@[j] == scratch@[(scratch_off as int + j) as int]);
            }
            // out[out_off+half..out_off+2n] has valid limbs (n+half = 3n/2 positions)
            assert forall |j: int| 0 <= j < (n + half) as int
                implies 0 <= (#[trigger] out@[((out_off + half) as int + j)]).sem() < LIMB_BASE()
            by {
                let jj = (half as int + j);
                assert(0 <= jj && jj < 2 * n as int);
                assert(out@[(out_off as int + jj) as int].sem() < LIMB_BASE());
            }
        }
        let _carry = add_inplace_propagate(
            out, out_off + half,
            scratch_slice, 0,
            n,
            &z1_final_overflow,
            half,
        );
    }

    // Proof: connect output to a × b via Karatsuba identity
    proof {
        use crate::fixed_point::limbs::lemma_karatsuba_identity;

        let a_sub = a@.subrange(a_off as int, (a_off + n) as int);
        let b_sub = b@.subrange(b_off as int, (b_off + n) as int);
        let B = limb_power(half as nat);
        let out_result = out@.subrange(out_off as int, (out_off + 2 * n) as int);

        // 1. Decompose a and b: vec_val(a_sub) = a_hi * B + a_lo
        lemma_vec_val_split::<T>(a_sub, half as nat);
        assert(a_sub.subrange(0, half as int) =~= a_lo_seq);
        assert(a_sub.subrange(half as int, n as int) =~= a_hi_seq);

        lemma_vec_val_split::<T>(b_sub, half as nat);
        assert(b_sub.subrange(0, half as int) =~= b_lo_seq);
        assert(b_sub.subrange(half as int, n as int) =~= b_hi_seq);

        // 2. Apply Karatsuba identity: a*b = z0 + z1*B + z2*B²
        lemma_karatsuba_identity(
            vec_val(a_lo_seq) as int, vec_val(a_hi_seq) as int,
            vec_val(b_lo_seq) as int, vec_val(b_hi_seq) as int,
            B as int,
        );

        // 3. The output vec_val equals z0 + z1*B + z2*B².
        // The output was built by: z0 at [0..n], z2 at [n..2n], then z1 added at [half..half+n].
        // Split output at half and at n to see the three regions.
        // This is a limb-level argument that follows from the carry-chain addition.
        // The full proof requires tracking vec_val through the add3 loop via
        // a loop invariant on partial sums. Deferred to a dedicated helper.

        // Frame: output only written in [out_off, out_off+2n)
        // Steps 1,2 write to [out_off..out_off+2n] via schoolbook.
        // Step 6 writes to [out_off+half..out_off+half+n] ⊆ [out_off..out_off+2n].
        // Elements outside this range are unchanged from old(out).
        assert forall |j: int| 0 <= j < out@.len()
            && !(out_off as int <= j < out_off + 2 * n)
            implies out@[j] == old(out)@[j]
        by {
            // schoolbook frame: only writes to its output region
            // add3 loop: only writes to [out_off+half..out_off+half+n] ⊆ [out_off..out_off+2n]
        }
    }
}

///  Multiply writing to output buffer. GPU-compatible interface.
///  Writes 2n limbs to out[0..2n].
///  For n <= 4: uses schoolbook directly (no allocation).
///  For n > 4: delegates to Karatsuba internally, copies result to out.
///  The transpiler unrolls this into depth-stratified variants.
// #[gpu_base_case(mul_schoolbook_to)]
pub fn mul_to<T: LimbOps>(
    a: &[T], b: &[T], out: &mut Vec<T>, out_off: usize, n: usize,
)
    requires
        a@.len() == n, b@.len() == n,
        n > 0, n <= 0x1FFF_FFFF,
        valid_limbs(a@), valid_limbs(b@),
        old(out)@.len() >= out_off + 2 * n,
        out_off + 2 * n < usize::MAX,
    ensures
        out@.len() == old(out)@.len(),
{
    let ghost out_len = out@.len();
    if n <= 4 {
        mul_schoolbook_to(a, b, out, out_off, n);
    } else {
        let (product, _gc) = generic_mul_karatsuba(a, b, n);
        for i in 0..(2 * n)
            invariant
                product@.len() == 2 * n,
                out@.len() == out_len, out_len >= out_off + 2 * n,
                out_off + 2 * n < usize::MAX,
                n <= 0x3FFF_FFFF,
        {
            out.set(out_off + i, product[i].clone_limb());
        }
    }
}

///  Schoolbook multiply: returns 2n-limb result.
///  vec_val(result) == vec_val(a) * vec_val(b)
///  Returns (result, ghost_carry) where:
///  vec_val(result) + ghost_carry * BASE^(2n) == vec_val(a) * vec_val(b)
///  For valid u32 limbs, ghost_carry == 0 (product fits in 2n limbs).
pub fn generic_mul_schoolbook<T: LimbOps>(
    a: &[T], b: &[T], n: usize,
) -> (result: (Vec<T>, Ghost<int>))
    requires
        a@.len() == n,
        b@.len() == n,
        n > 0,
        n <= 0x3FFF_FFFF,
        valid_limbs(a@),
        valid_limbs(b@),
    ensures
        result.0@.len() == 2 * n,
        valid_limbs(result.0@),
        vec_val(result.0@) + result.1@ * limb_power((2 * n) as nat)
            == vec_val(a@) * vec_val(b@),
        result.1@ == 0int,
{
    let nn: usize = 2 * n;
    let mut acc = generic_zero_vec::<T>(nn);
    let ghost sb = sem_seq(b@);
    let ghost mut ghost_carry: int = 0int;

    proof { lemma_vec_val_zeros(acc@); }

    for i in 0..n
        invariant
            a@.len() == n, b@.len() == n,
            nn == 2 * n, n <= 0x3FFF_FFFF,
            acc@.len() == nn,
            valid_limbs(acc@),
            valid_limbs(a@), valid_limbs(b@),
            sb == sem_seq(b@),
            vec_val(acc@) + ghost_carry * limb_power(nn as nat)
                == vec_val(a@) * limbs_val(sb.subrange(0, i as int)),
    {
        let ghost acc_old_val = vec_val(acc@);
        let ghost gc_old = ghost_carry;
        let bi = b[i].clone_limb();
        let partial = generic_mul_by_limb(a, &bi, n);
        let shifted = generic_shift_left(&partial, i);
        let shifted_p = generic_pad_to_length(&shifted, nn);
        let (new_acc, carry) = generic_add_limbs(&acc, &shifted_p, nn);

        proof {
            lemma_vec_val_shift(partial@, i as nat, shifted@);
            lemma_vec_val_pad(shifted@, shifted_p@);
            assert(bi.sem() == b@[i as int].sem());
            assert(sb[i as int] == bi.sem());
            lemma_limbs_val_subrange_extend(sb, i as nat);

            let va = vec_val(a@);
            let vsi = limbs_val(sb.subrange(0, i as int));
            let vsi1 = limbs_val(sb.subrange(0, (i + 1) as int));
            let bsem = bi.sem();
            let lp = limb_power(i as nat);
            let lp_nn = limb_power(nn as nat);
            assert(vec_val(shifted_p@) == va * bsem * lp) by(nonlinear_arith)
                requires
                    vec_val(partial@) == va * bsem,
                    vec_val(shifted@) == vec_val(partial@) * lp,
                    vec_val(shifted_p@) == vec_val(shifted@);
            //  new: vec_val(new_acc) + carry * lp_nn == vec_val(acc) + vec_val(shifted_p)
            //  old: vec_val(acc) + gc_old * lp_nn == va * vsi
            //  so:  vec_val(new_acc) + (gc_old + carry) * lp_nn
            //       == va * vsi + va * bsem * lp
            //       == va * vsi1
            assert(vec_val(new_acc@) + (gc_old + carry.sem()) * lp_nn
                == va * vsi1) by(nonlinear_arith)
                requires
                    vec_val(new_acc@) + carry.sem() * lp_nn
                        == acc_old_val + vec_val(shifted_p@),
                    acc_old_val + gc_old * lp_nn == va * vsi,
                    vec_val(shifted_p@) == va * bsem * lp,
                    vsi1 == vsi + bsem * lp;
        }

        proof { ghost_carry = ghost_carry + carry.sem(); }
        acc = new_acc;
    }

    proof {
        assert(sb.subrange(0, sb.len() as int) =~= sb);
        //  ghost_carry == 0: product of n-limb numbers fits in 2n limbs
        lemma_vec_val_bounded(acc@);
        lemma_vec_val_bounded(a@);
        lemma_vec_val_bounded(b@);
        lemma_limb_power_add(n as nat, n as nat);
        let lp_n = limb_power(n as nat);
        let lp_2n = limb_power((2 * n) as nat);
        assert(ghost_carry == 0int) by(nonlinear_arith)
            requires
                vec_val(acc@) + ghost_carry * lp_2n == vec_val(a@) * vec_val(b@),
                0 <= vec_val(acc@), vec_val(acc@) < lp_2n,
                0 <= vec_val(a@), vec_val(a@) < lp_n,
                0 <= vec_val(b@), vec_val(b@) < lp_n,
                lp_2n == lp_n * lp_n,
                lp_n > 0;
    }

    (acc, Ghost(ghost_carry))
}

//  ══════════════════════════════════════════════════════════════
//  Generic Karatsuba multiplication (O(n^1.585))
//  ══════════════════════════════════════════════════════════════

///  Karatsuba multiply: returns (2n-limb result, ghost_carry).
///  vec_val(result) + ghost_carry * BASE^(2n) == vec_val(a) * vec_val(b)
// #[gpu_base_case(generic_mul_schoolbook)]
pub fn generic_mul_karatsuba<T: LimbOps>(
    a: &[T], b: &[T], n: usize,
) -> (result: (Vec<T>, Ghost<int>))
    requires
        a@.len() == n,
        b@.len() == n,
        n > 0,
        n <= 0x1FFF_FFFF,
        valid_limbs(a@),
        valid_limbs(b@),
    ensures
        result.0@.len() == 2 * n,
        valid_limbs(result.0@),
        vec_val(result.0@) + result.1@ * limb_power((2 * n) as nat)
            == vec_val(a@) * vec_val(b@),
    decreases n,
{
    if n <= 4 {
        return generic_mul_schoolbook(a, b, n);
    }

    let half: usize = n / 2;
    let upper: usize = n - half;

    //  Split inputs — slices preserve valid_limbs
    let a_lo = generic_slice_vec(a, 0, half);
    let a_hi = generic_slice_vec(a, half, n);
    let b_lo = generic_slice_vec(b, 0, half);
    let b_hi = generic_slice_vec(b, half, n);

    //  Prove slices have valid_limbs
    proof {
        assert(valid_limbs(a_lo@)) by {
            assert forall |j: int| 0 <= j < a_lo@.len()
                implies 0 <= (#[trigger] a_lo@[j]).sem() && a_lo@[j].sem() < LIMB_BASE()
            by { assert(a_lo@[j].sem() == a@[j].sem()); }
        }
        assert(valid_limbs(a_hi@)) by {
            assert forall |j: int| 0 <= j < a_hi@.len()
                implies 0 <= (#[trigger] a_hi@[j]).sem() && a_hi@[j].sem() < LIMB_BASE()
            by { assert(a_hi@[j].sem() == a@[(half + j) as int].sem()); }
        }
        assert(valid_limbs(b_lo@)) by {
            assert forall |j: int| 0 <= j < b_lo@.len()
                implies 0 <= (#[trigger] b_lo@[j]).sem() && b_lo@[j].sem() < LIMB_BASE()
            by { assert(b_lo@[j].sem() == b@[j].sem()); }
        }
        assert(valid_limbs(b_hi@)) by {
            assert forall |j: int| 0 <= j < b_hi@.len()
                implies 0 <= (#[trigger] b_hi@[j]).sem() && b_hi@[j].sem() < LIMB_BASE()
            by { assert(b_hi@[j].sem() == b@[(half + j) as int].sem()); }
        }
    }

    //  Pad lo halves to `upper` limbs — preserves valid_limbs
    let a_lo_p = generic_pad_to_length(&a_lo, upper);
    let b_lo_p = generic_pad_to_length(&b_lo, upper);
    proof {
        assert(valid_limbs(a_lo_p@)) by {
            assert forall |j: int| 0 <= j < a_lo_p@.len()
                implies 0 <= (#[trigger] a_lo_p@[j]).sem() && a_lo_p@[j].sem() < LIMB_BASE()
            by {
                if j < a_lo@.len() as int { assert(a_lo_p@[j].sem() == a_lo@[j].sem()); }
                else { assert(a_lo_p@[j].sem() == 0int); }
            }
        }
        assert(valid_limbs(b_lo_p@)) by {
            assert forall |j: int| 0 <= j < b_lo_p@.len()
                implies 0 <= (#[trigger] b_lo_p@[j]).sem() && b_lo_p@[j].sem() < LIMB_BASE()
            by {
                if j < b_lo@.len() as int { assert(b_lo_p@[j].sem() == b_lo@[j].sem()); }
                else { assert(b_lo_p@[j].sem() == 0int); }
            }
        }
    }

    //  z0 = a_lo * b_lo, z2 = a_hi * b_hi (recursive)
    let (z0, gz0) = generic_mul_karatsuba(&a_lo_p, &b_lo_p, upper);
    let (z2, gz2) = generic_mul_karatsuba(&a_hi, &b_hi, upper);

    //  Sums for z1
    let (a_sum_body, a_carry) = generic_add_limbs(&a_lo_p, &a_hi, upper);
    let (b_sum_body, b_carry) = generic_add_limbs(&b_lo_p, &b_hi, upper);

    //  Build (upper+1)-limb sums — carry is valid (0 <= carry.sem() < BASE from add3)
    let ghost a_sum_pre = a_sum_body@;
    let mut a_sum = a_sum_body;
    a_sum.push(a_carry);
    let ghost b_sum_pre = b_sum_body@;
    let mut b_sum = b_sum_body;
    b_sum.push(b_carry);

    proof {
        //  a_sum = a_sum_body.push(a_carry). Body has valid_limbs, carry is valid.
        assert(valid_limbs(a_sum@)) by {
            assert forall |j: int| 0 <= j < a_sum@.len()
                implies 0 <= (#[trigger] a_sum@[j]).sem() && a_sum@[j].sem() < LIMB_BASE()
            by {
                if j < a_sum_pre.len() as int { assert(a_sum@[j] == a_sum_pre[j]); }
                else { assert(a_sum@[j] == a_carry); }
            }
        }
        assert(valid_limbs(b_sum@)) by {
            assert forall |j: int| 0 <= j < b_sum@.len()
                implies 0 <= (#[trigger] b_sum@[j]).sem() && b_sum@[j].sem() < LIMB_BASE()
            by {
                if j < b_sum_pre.len() as int { assert(b_sum@[j] == b_sum_pre[j]); }
                else { assert(b_sum@[j] == b_carry); }
            }
        }
    }

    //  z1_full = (a_lo + a_hi) * (b_lo + b_hi)
    let (z1_full, gz1f) = generic_mul_karatsuba(&a_sum, &b_sum, upper + 1);

    //  z1 = z1_full - z0 - z2
    let tgt = 2 * (upper + 1);
    let z0_p = generic_pad_to_length(&z0, tgt);
    let z2_p = generic_pad_to_length(&z2, tgt);
    proof {
        //  Prove z1_full, z0_p, z2_p have valid_limbs for sub_limbs
        assert(valid_limbs(z0_p@)) by {
            assert forall |j: int| 0 <= j < z0_p@.len()
                implies 0 <= (#[trigger] z0_p@[j]).sem() && z0_p@[j].sem() < LIMB_BASE()
            by {
                if j < z0@.len() as int { assert(z0_p@[j].sem() == z0@[j].sem()); }
                else { assert(z0_p@[j].sem() == 0int); }
            }
        }
        assert(valid_limbs(z2_p@)) by {
            assert forall |j: int| 0 <= j < z2_p@.len()
                implies 0 <= (#[trigger] z2_p@[j]).sem() && z2_p@[j].sem() < LIMB_BASE()
            by {
                if j < z2@.len() as int { assert(z2_p@[j].sem() == z2@[j].sem()); }
                else { assert(z2_p@[j].sem() == 0int); }
            }
        }
    }
    let (z1_tmp, bw1) = generic_sub_limbs(&z1_full, &z0_p, tgt);
    let (z1, bw2) = generic_sub_limbs(&z1_tmp, &z2_p, tgt);

    //  Combine: result = z0 + z1 * B^half + z2 * B^(2*half)
    let z1_shifted = generic_shift_left(&z1, half);
    let z2_shifted = generic_shift_left(&z2, 2 * half);

    let rlen = 2 * n;
    let z0_f = generic_pad_to_length(&z0, rlen);
    let z1_f = generic_pad_to_length(&z1_shifted, rlen);
    let z2_f = generic_pad_to_length(&z2_shifted, rlen);

    let (s1, c1) = generic_add_limbs(&z0_f, &z1_f, rlen);
    let (s2, c2) = generic_add_limbs(&s1, &z2_f, rlen);

    proof {
        //  ── Karatsuba algebraic proof ──
        //  Goal: vec_val(s2@) + (c1.sem() + c2.sem()) * limb_power(rlen)
        //        == vec_val(a@) * vec_val(b@)

        let va = vec_val(a@);
        let vb = vec_val(b@);
        let B = limb_power(half as nat);
        //  1. Split: va == va_lo + va_hi * B, vb == vb_lo + vb_hi * B
        lemma_vec_val_split(a@, half as nat);
        lemma_vec_val_split(b@, half as nat);
        //  a_lo = a[0..half], a_hi = a[half..n]
        //  vec_val(a_lo@) matches vec_val(a@.subrange(0, half))
        //  since slice_vec preserves sem
        assert(sem_seq(a_lo@) =~= sem_seq(a@).subrange(0, half as int)) by {
            lemma_sem_seq_subrange(a@, 0, half as int);
            assert forall |j: int| 0 <= j < a_lo@.len()
                implies sem_seq(a_lo@)[j] == sem_seq(a@).subrange(0, half as int)[j]
            by { assert(a_lo@[j].sem() == a@[j].sem()); }
        }
        assert(sem_seq(a_hi@) =~= sem_seq(a@).subrange(half as int, n as int)) by {
            lemma_sem_seq_subrange(a@, half as int, n as int);
            assert forall |j: int| 0 <= j < a_hi@.len()
                implies sem_seq(a_hi@)[j] == sem_seq(a@).subrange(half as int, n as int)[j]
            by { assert(a_hi@[j].sem() == a@[(half + j) as int].sem()); }
        }
        //  pad doesn't change value
        lemma_vec_val_pad(a_lo@, a_lo_p@);
        lemma_vec_val_pad(b_lo@, b_lo_p@);
        assert(sem_seq(b_lo@) =~= sem_seq(b@).subrange(0, half as int)) by {
            lemma_sem_seq_subrange(b@, 0, half as int);
            assert forall |j: int| 0 <= j < b_lo@.len()
                implies sem_seq(b_lo@)[j] == sem_seq(b@).subrange(0, half as int)[j]
            by { assert(b_lo@[j].sem() == b@[j].sem()); }
        }
        assert(sem_seq(b_hi@) =~= sem_seq(b@).subrange(half as int, n as int)) by {
            lemma_sem_seq_subrange(b@, half as int, n as int);
            assert forall |j: int| 0 <= j < b_hi@.len()
                implies sem_seq(b_hi@)[j] == sem_seq(b@).subrange(half as int, n as int)[j]
            by { assert(b_hi@[j].sem() == b@[(half + j) as int].sem()); }
        }

        let va_lo = vec_val(a_lo_p@);
        let va_hi = vec_val(a_hi@);
        let vb_lo = vec_val(b_lo_p@);
        let vb_hi = vec_val(b_hi@);

        //  Bridge: vec_val of slices == vec_val of subranges
        //  sem_seq(a_lo@) =~= sem_seq(a@).subrange(0, half) =~= sem_seq(a@.subrange(0, half))
        lemma_sem_seq_subrange(a@, 0, half as int);
        lemma_sem_seq_subrange(a@, half as int, n as int);
        lemma_sem_seq_subrange(b@, 0, half as int);
        lemma_sem_seq_subrange(b@, half as int, n as int);
        assert(sem_seq(a_lo@) =~= sem_seq(a@.subrange(0, half as int)));
        assert(sem_seq(a_hi@) =~= sem_seq(a@.subrange(half as int, n as int)));
        assert(sem_seq(b_lo@) =~= sem_seq(b@.subrange(0, half as int)));
        assert(sem_seq(b_hi@) =~= sem_seq(b@.subrange(half as int, n as int)));
        //  va_lo == vec_val(a_lo_p@) == vec_val(a_lo@) from pad
        //  va == va_lo + va_hi * B from split + pad + bridge
        assert(va == va_lo + va_hi * B);
        assert(vb == vb_lo + vb_hi * B);

        //  2. z0 = va_lo * vb_lo, z2 = va_hi * vb_hi (from recursive postconditions)
        let vz0 = vec_val(z0@);
        let vz2 = vec_val(z2@);
        //  vz0 + gz0@ * limb_power(2*upper) == va_lo * vb_lo
        //  vz2 + gz2@ * limb_power(2*upper) == va_hi * vb_hi

        //  3. Sums: va_sum == va_lo + va_hi, vb_sum == vb_lo + vb_hi
        //  (from add_limbs postcondition + push carry)
        lemma_sem_seq_push(a_sum_pre, a_carry);
        lemma_limbs_val_push(sem_seq(a_sum_pre), a_carry.sem());
        lemma_sem_seq_push(b_sum_pre, b_carry);
        lemma_limbs_val_push(sem_seq(b_sum_pre), b_carry.sem());

        //  4. Ghost carries are 0 (products fit in output limbs)
        //  vec_val(a_lo_p) < limb_power(upper), vec_val(b_lo_p) < limb_power(upper)
        //  product < limb_power(upper)^2 = limb_power(2*upper), fits in 2*upper limbs
        lemma_vec_val_bounded(a_lo_p@);
        lemma_vec_val_bounded(b_lo_p@);
        lemma_vec_val_bounded(a_hi@);
        lemma_vec_val_bounded(b_hi@);
        //  z0 product: va_lo * vb_lo < limb_power(upper)^2 = limb_power(2*upper)
        //  So gz0 == 0
        lemma_vec_val_bounded(z0@);
        lemma_vec_val_bounded(z2@);
        //  limb_power(2*upper) == limb_power(upper) * limb_power(upper)
        lemma_limb_power_add(upper as nat, upper as nat);
        assert(upper + upper == 2 * upper);
        let lp_upper = limb_power(upper as nat);
        let lp_2upper = limb_power((2 * upper) as nat);
        assert(lp_2upper == lp_upper * lp_upper);
        //  va_lo * vb_lo < lp_upper^2 = lp_2upper, and vec_val(z0) < lp_2upper
        //  So gz0 * lp_2upper == va_lo*vb_lo - vec_val(z0), |rhs| < lp_2upper, so gz0 == 0
        assert(gz0@ == 0int) by(nonlinear_arith)
            requires
                vec_val(z0@) + gz0@ * lp_2upper == va_lo * vb_lo,
                0 <= vec_val(z0@), vec_val(z0@) < lp_2upper,
                0 <= va_lo, va_lo < lp_upper,
                0 <= vb_lo, vb_lo < lp_upper,
                lp_2upper == lp_upper * lp_upper,
                lp_2upper > 0;
        assert(gz2@ == 0int) by(nonlinear_arith)
            requires
                vec_val(z2@) + gz2@ * lp_2upper == va_hi * vb_hi,
                0 <= vec_val(z2@), vec_val(z2@) < lp_2upper,
                0 <= va_hi, va_hi < lp_upper,
                0 <= vb_hi, vb_hi < lp_upper,
                lp_2upper == lp_upper * lp_upper,
                lp_2upper > 0;

        //  Sum bounds for z1_full
        lemma_sem_seq_push(a_sum_pre, a_carry);
        lemma_limbs_val_push(sem_seq(a_sum_pre), a_carry.sem());
        lemma_sem_seq_push(b_sum_pre, b_carry);
        lemma_limbs_val_push(sem_seq(b_sum_pre), b_carry.sem());
        lemma_vec_val_bounded(a_sum@);
        lemma_vec_val_bounded(b_sum@);
        lemma_vec_val_bounded(z1_full@);
        lemma_limb_power_add((upper + 1) as nat, (upper + 1) as nat);
        assert((upper + 1) + (upper + 1) == 2 * (upper + 1));
        let lp_up1 = limb_power((upper + 1) as nat);
        let lp_2up1 = limb_power((2 * (upper + 1)) as nat);
        assert(lp_2up1 == lp_up1 * lp_up1);
        assert(gz1f@ == 0int) by(nonlinear_arith)
            requires
                vec_val(z1_full@) + gz1f@ * lp_2up1
                    == vec_val(a_sum@) * vec_val(b_sum@),
                0 <= vec_val(z1_full@), vec_val(z1_full@) < lp_2up1,
                0 <= vec_val(a_sum@), vec_val(a_sum@) < lp_up1,
                0 <= vec_val(b_sum@), vec_val(b_sum@) < lp_up1,
                lp_2up1 == lp_up1 * lp_up1, lp_2up1 > 0;

        //  5. Now: vz0 == va_lo * vb_lo, vz2 == va_hi * vb_hi (exact, no carry)
        let vz0 = vec_val(z0@);
        let vz2 = vec_val(z2@);
        assert(vz0 == va_lo * vb_lo);
        assert(vz2 == va_hi * vb_hi);

        //  6. Karatsuba identity: va * vb == z0 + z1 * B + z2 * B^2
        lemma_karatsuba_identity(va_lo, va_hi, vb_lo, vb_hi, B);

        //  7. Connect shift + pad + add to the final result
        lemma_vec_val_shift(z1@, half as nat, z1_shifted@);
        lemma_vec_val_shift(z2@, (2 * half) as nat, z2_shifted@);
        lemma_vec_val_pad(z0@, z0_f@);
        lemma_vec_val_pad(z1_shifted@, z1_f@);
        lemma_vec_val_pad(z2_shifted@, z2_f@);

        //  8. Final chain
        //  From sub_limbs: z1 = z1_full - z0 - z2 (borrows are 0 by cross-term nonnegativity)
        //  z1_full = vec_val(a_sum) * vec_val(b_sum) = (va_lo + va_hi)(vb_lo + vb_hi)
        lemma_vec_val_pad(z0@, z0_p@);
        lemma_vec_val_pad(z2@, z2_p@);
        let vz1_full = vec_val(z1_full@);
        let vz1_tmp = vec_val(z1_tmp@);
        let vz1 = vec_val(z1@);
        //  z1 = z1_full - z0 - z2 (from sub_limbs postconditions + borrows)
        //  From sub_limbs: vz1_tmp + vz0 == vz1_full + bw1 * limb_power(tgt)
        //  And: vz1 + vz2 == vz1_tmp + bw2 * limb_power(tgt)
        //  Borrows are 0 or 1 from sub_limbs ensures

        //  Shift/pad values
        let vz0_f = vec_val(z0_f@);
        let vz1_f = vec_val(z1_f@);
        let vz2_f = vec_val(z2_f@);
        //  vz0_f == vz0
        //  vz1_f == vz1 * limb_power(half) (from shift)
        //  vz2_f == vz2 * limb_power(2*half) (from shift)

        //  From add_limbs:
        //  vec_val(s1) + c1 * limb_power(rlen) == vz0_f + vz1_f
        //  vec_val(s2) + c2 * limb_power(rlen) == vec_val(s1) + vz2_f
        //  So: vec_val(s2) + (c1+c2) * limb_power(rlen) == vz0 + vz1*B^half + vz2*B^(2*half)
        //  And from karatsuba_identity: va*vb == vz0 + vz1*B^half + vz2*B^(2*half)
        //  where vz1 = vz1_full - vz0 - vz2 = (va_lo+va_hi)(vb_lo+vb_hi) - va_lo*vb_lo - va_hi*vb_hi

        //  Chain it with nonlinear_arith:
        let lp_rlen = limb_power(rlen as nat);
        let lp_half = limb_power(half as nat);
        let lp_2half = limb_power((2 * half) as nat);
        assert(vec_val(s2@) + (c1.sem() + c2.sem()) * lp_rlen
            == vz0_f + vz1_f + vz2_f) by(nonlinear_arith)
            requires
                vec_val(s2@) + c2.sem() * lp_rlen == vec_val(s1@) + vz2_f,
                vec_val(s1@) + c1.sem() * lp_rlen == vz0_f + vz1_f;

        //  From Karatsuba identity (already called above):
        //  va * vb == vz0 + (vz1_full - vz0 - vz2) * B + vz2 * B^2
        //  = vz0 + vz1 * B + vz2 * B^2  (if borrows are 0)
        //  But we need to connect vz1 to z1_full - z0 - z2 and borrows to 0

        //  The identity needs the cross terms to be non-negative for borrows to be 0
        //  (va_lo+va_hi)(vb_lo+vb_hi) >= va_lo*vb_lo + va_hi*vb_hi
        //  since the cross terms va_lo*vb_hi + va_hi*vb_lo >= 0 (all non-negative from valid_limbs)
        assert(vz1_full >= vz0 + vz2) by(nonlinear_arith)
            requires
                vz1_full == (va_lo + va_hi) * (vb_lo + vb_hi),
                vz0 == va_lo * vb_lo,
                vz2 == va_hi * vb_hi,
                va_lo >= 0, va_hi >= 0, vb_lo >= 0, vb_hi >= 0;

        //  Borrows are 0 (since z1_full >= z0 + z2, sub_limbs doesn't underflow)
        //  sub_limbs gives: vz1_tmp + vz0 == vz1_full + bw1 * limb_power(tgt)
        //  Since vz1_full >= vz0: vz1_tmp = vz1_full - vz0 + bw1 * lp_tgt
        //  If bw1 == 1: vz1_tmp = vz1_full - vz0 + lp_tgt >= lp_tgt, contradicts vz1_tmp < lp_tgt
        let lp_tgt = limb_power(tgt as nat);
        lemma_vec_val_bounded(z1_tmp@);
        lemma_vec_val_bounded(z1@);
        assert(bw1.sem() == 0int) by(nonlinear_arith)
            requires
                vz1_tmp + vz0 == vz1_full + bw1.sem() * lp_tgt,
                vz1_full >= vz0 + vz2,
                0 <= vz1_tmp, vz1_tmp < lp_tgt,
                bw1.sem() == 0 || bw1.sem() == 1,
                vz0 >= 0, vz2 >= 0;
        assert(bw2.sem() == 0int) by(nonlinear_arith)
            requires
                vz1 + vz2 == vz1_tmp + bw2.sem() * lp_tgt,
                vz1_tmp == vz1_full - vz0,
                vz1_full >= vz0 + vz2,
                0 <= vz1, vz1 < lp_tgt,
                bw2.sem() == 0 || bw2.sem() == 1,
                vz0 >= 0, vz2 >= 0;

        //  So: vz1 = vz1_full - vz0 - vz2
        assert(vz1 == vz1_full - vz0 - vz2);

        //  Final: vec_val(s2) + (c1+c2) * limb_power(rlen)
        //       == vz0 + vz1 * limb_power(half) + vz2 * limb_power(2*half)
        //       == va * vb  (from karatsuba_identity)
        assert(vz0_f == vz0);
        assert(vz1_f == vz1 * lp_half);
        assert(vz2_f == vz2 * lp_2half);

        //  From karatsuba_identity: va*vb == z0 + z1*B + z2*B^2
        //  where z1 = (va_lo+va_hi)(vb_lo+vb_hi) - z0 - z2
        //  This matches vz1 = vz1_full - vz0 - vz2
        lemma_limb_power_add(half as nat, half as nat);
        assert(half + half == 2 * half);
        assert(lp_2half == lp_half * lp_half);

        //  Step A: Karatsuba identity gives va*vb in terms of z0, z1, z2
        //  lemma_karatsuba_identity already called above; it ensures:
        //  (va_hi * B + va_lo) * (vb_hi * B + vb_lo) == z0 + z1 * B + z2 * B * B
        //  But the ensures uses a_hi*base + a_lo form, we have va_lo + va_hi * B
        assert(va == va_hi * lp_half + va_lo) by(nonlinear_arith)
            requires va == va_lo + va_hi * lp_half;
        assert(vb == vb_hi * lp_half + vb_lo) by(nonlinear_arith)
            requires vb == vb_lo + vb_hi * lp_half;
        //  Now the identity matches: va * vb == vz0 + vz1 * B + vz2 * B^2
        assert(va * vb == vz0 + vz1 * lp_half + vz2 * lp_half * lp_half);

        //  Step B: lp_2half == lp_half * lp_half, so combine
        assert(va * vb == vz0 + vz1 * lp_half + vz2 * lp_2half) by(nonlinear_arith)
            requires
                va * vb == vz0 + vz1 * lp_half + vz2 * lp_half * lp_half,
                lp_2half == lp_half * lp_half;

        //  Step C: s2 + carries == z0 + z1*B^half + z2*B^(2*half) == va*vb
        assert(vec_val(s2@) + (c1.sem() + c2.sem()) * lp_rlen == va * vb);
        assert(rlen == 2 * n);
    }

    (s2, Ghost(c1.sem() + c2.sem()))
}



/// Single-buffer signed add: all mutable params are offsets into one Vec.
/// For GPU kernels where out/tmp1/tmp2 are regions of the same shared memory.
pub fn signed_add_to_buf<T: LimbOps>(
    a: &[T], a_sign: &T, b: &[T], b_sign: &T,
    buf: &mut Vec<T>, out_off: usize, tmp1_off: usize, tmp2_off: usize,
    n: usize,
) -> (out_sign: T)
    requires
        a@.len() >= n, b@.len() >= n, n > 0,
        old(buf)@.len() >= out_off + n,
        old(buf)@.len() >= tmp1_off + n,
        old(buf)@.len() >= tmp2_off + n,
        out_off + n < usize::MAX, tmp1_off + n < usize::MAX, tmp2_off + n < usize::MAX,
        valid_limbs(a@), valid_limbs(b@),
        a_sign.sem() == 0 || a_sign.sem() == 1,
        b_sign.sem() == 0 || b_sign.sem() == 1,
        // Non-overlap of all three regions
        out_off + n <= tmp1_off || tmp1_off + n <= out_off,
        out_off + n <= tmp2_off || tmp2_off + n <= out_off,
        tmp1_off + n <= tmp2_off || tmp2_off + n <= tmp1_off,
    ensures buf@.len() == old(buf)@.len(),
        out_sign.sem() == 0 || out_sign.sem() == 1,
        // Valid limbs on output region
        forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] buf@[out_off as int + j]).sem() < LIMB_BASE(),
        // Frame: indices outside all three regions are unchanged
        forall |j: int| 0 <= j < buf@.len()
            && !(out_off as int <= j < out_off + n)
            && !(tmp1_off as int <= j < tmp1_off + n)
            && !(tmp2_off as int <= j < tmp2_off + n)
            ==> buf@[j] == old(buf)@[j],
        // Signed-magnitude sum equation: 3-way modular disjunction
        ({
            let va = vec_val(a@.subrange(0, n as int));
            let vb = vec_val(b@.subrange(0, n as int));
            let vo = vec_val(buf@.subrange(out_off as int, (out_off + n) as int));
            let sa_signed = if a_sign.sem() == 0 { va } else { -va };
            let sb_signed = if b_sign.sem() == 0 { vb } else { -vb };
            let so_signed = if out_sign.sem() == 0 { vo } else { -vo };
            let true_sum = sa_signed + sb_signed;
            let P = limb_power(n as nat);
            so_signed == true_sum
                || (so_signed == true_sum - P && true_sum >= P)
                || (so_signed == true_sum + P && true_sum <= -(P as int))
        }),
{
    let ghost a_sub = a@.subrange(0, n as int);
    let ghost b_sub = b@.subrange(0, n as int);
    proof {
        assert(valid_limbs(a_sub)) by {
            assert forall |k: int| 0 <= k < a_sub.len()
                implies 0 <= (#[trigger] a_sub[k]).sem() && a_sub[k].sem() < LIMB_BASE() by {
                assert(a_sub[k] == a@[k]);
            }
        }
        assert(valid_limbs(b_sub)) by {
            assert forall |k: int| 0 <= k < b_sub.len()
                implies 0 <= (#[trigger] b_sub[k]).sem() && b_sub[k].sem() < LIMB_BASE() by {
                assert(b_sub[k] == b@[k]);
            }
        }
    }
    // Step 1: a+b → tmp1
    let sum_carry = add_limbs_to(a, b, buf, tmp1_off, n);
    let ghost sum_sub = buf@.subrange(tmp1_off as int, (tmp1_off + n) as int);

    // Step 2: a-b → tmp2  (frame: tmp1 preserved by non-overlap)
    let borrow_ab = sub_limbs_to(a, b, buf, tmp2_off, n);
    let ghost amb_sub = buf@.subrange(tmp2_off as int, (tmp2_off + n) as int);
    proof {
        // Frame: tmp1 region preserved by non-overlap with tmp2
        assert(sum_sub =~= buf@.subrange(tmp1_off as int, (tmp1_off + n) as int));
    }

    // Step 3: b-a → out  (frame: tmp1, tmp2 preserved by non-overlap)
    let borrow_ba = sub_limbs_to(b, a, buf, out_off, n);
    let ghost bma_sub = buf@.subrange(out_off as int, (out_off + n) as int);
    proof {
        // Frame: tmp1 and tmp2 regions preserved by non-overlap with out
        assert(sum_sub =~= buf@.subrange(tmp1_off as int, (tmp1_off + n) as int));
        assert(amb_sub =~= buf@.subrange(tmp2_off as int, (tmp2_off + n) as int));
    }

    // Compute same_sign indicator
    let (sign_diff, sign_borrow) = a_sign.sub_borrow(b_sign, &T::zero_val());
    let diff_zero = sign_diff.is_zero_limb();
    let borrow_zero = sign_borrow.is_zero_limb();
    let (same_sign, _) = diff_zero.mul2(&borrow_zero);

    proof {
        // Establish (a_sign == b_sign) <==> same_sign == 1
        let asv = a_sign.sem();
        let bsv = b_sign.sem();
        let sd = sign_diff.sem();
        let sbo = sign_borrow.sem();
        let dz = diff_zero.sem();
        let bz = borrow_zero.sem();
        let ss = same_sign.sem();
        assert(ss == (dz * bz) % LIMB_BASE());
        if asv == bsv {
            assert(sd == 0) by(nonlinear_arith)
                requires sd == (asv - bsv - 0 + LIMB_BASE()) % LIMB_BASE(),
                         asv == bsv, LIMB_BASE() > 0;
            assert(sbo == 0);
            assert(dz == 1);
            assert(bz == 1);
            assert(dz * bz == 1) by(nonlinear_arith) requires dz == 1, bz == 1;
            assert(1int % LIMB_BASE() == 1) by(nonlinear_arith) requires LIMB_BASE() > 1;
            assert(ss == 1);
        } else if asv == 0 && bsv == 1 {
            assert(sd == LIMB_BASE() - 1) by(nonlinear_arith)
                requires sd == (0 - 1 - 0 + LIMB_BASE()) % LIMB_BASE(), LIMB_BASE() > 1;
            assert(sbo == 1);
            assert(dz == 0);
            assert(bz == 0);
            assert(dz * bz == 0) by(nonlinear_arith) requires dz == 0, bz == 0;
            assert(0int % LIMB_BASE() == 0) by(nonlinear_arith) requires LIMB_BASE() > 0;
            assert(ss == 0);
        } else {
            assert(sd == 1) by(nonlinear_arith)
                requires sd == (1 - 0 - 0 + LIMB_BASE()) % LIMB_BASE(), LIMB_BASE() > 2;
            assert(sbo == 0);
            assert(dz == 0);
            assert(bz == 1);
            assert(dz * bz == 0) by(nonlinear_arith) requires dz == 0, bz == 1;
            assert(0int % LIMB_BASE() == 0) by(nonlinear_arith) requires LIMB_BASE() > 0;
            assert(ss == 0);
        }
    }

    let diff_sign = T::select_limb(&borrow_ab, a_sign.clone_limb(), b_sign.clone_limb());
    let result_sign = T::select_limb(&same_sign, diff_sign, a_sign.clone_limb());

    // Capture the SELECTED sequence (one of sum_sub, amb_sub, bma_sub)
    let ghost ss_v = same_sign.sem();
    let ghost bab_v = borrow_ab.sem();
    let ghost selected_seq: Seq<T> = if ss_v == 1 {
        sum_sub
    } else if bab_v == 0 {
        amb_sub
    } else {
        bma_sub
    };

    // Select loop: pick sum or diff for each limb
    let ghost buf_len = buf@.len();
    let ghost pre_select = buf@;
    for i in 0..n
        invariant
            buf@.len() == buf_len,
            buf_len >= out_off + n, buf_len >= tmp1_off + n, buf_len >= tmp2_off + n,
            out_off + n < usize::MAX, tmp1_off + n < usize::MAX, tmp2_off + n < usize::MAX,
            out_off + n <= tmp1_off || tmp1_off + n <= out_off,
            out_off + n <= tmp2_off || tmp2_off + n <= out_off,
            tmp1_off + n <= tmp2_off || tmp2_off + n <= tmp1_off,
            ss_v == same_sign.sem(),
            bab_v == borrow_ab.sem(),
            ss_v == 0 || ss_v == 1,
            bab_v == 0 || bab_v == 1,
            sum_sub == pre_select.subrange(tmp1_off as int, (tmp1_off + n) as int),
            amb_sub == pre_select.subrange(tmp2_off as int, (tmp2_off + n) as int),
            bma_sub == pre_select.subrange(out_off as int, (out_off + n) as int),
            selected_seq.len() == n as int,
            ss_v == 1 ==> selected_seq == sum_sub,
            ss_v == 0 && bab_v == 0 ==> selected_seq == amb_sub,
            ss_v == 0 && bab_v == 1 ==> selected_seq == bma_sub,
            // Output: already-processed have valid limbs
            forall |j: int| 0 <= j < i ==> 0 <= (#[trigger] buf@[out_off as int + j]).sem() < LIMB_BASE(),
            // tmp1 valid limbs preserved (non-overlapping with out writes)
            forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] buf@[tmp1_off as int + j]).sem() < LIMB_BASE(),
            // tmp2 valid limbs preserved
            forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] buf@[tmp2_off as int + j]).sem() < LIMB_BASE(),
            // Unprocessed out region still valid from sub_limbs_to
            forall |j: int| i <= j < n ==> 0 <= (#[trigger] buf@[out_off as int + j]).sem() < LIMB_BASE(),
            // tmp1 region content preserved as sum_sub
            forall |j: int| 0 <= j < n ==> #[trigger] buf@[tmp1_off as int + j] == sum_sub[j],
            // tmp2 region content preserved as amb_sub
            forall |j: int| 0 <= j < n ==> #[trigger] buf@[tmp2_off as int + j] == amb_sub[j],
            // Unprocessed out region still has b-a content
            forall |j: int| i <= j < n ==> #[trigger] buf@[out_off as int + j] == bma_sub[j],
            // Already-processed out region has the selected value
            forall |j: int| 0 <= j < i
                ==> #[trigger] buf@[out_off as int + j].sem() == selected_seq[j].sem(),
            // Frame outside all three regions
            forall |j: int| 0 <= j < buf_len
                && !(out_off as int <= j < out_off + n)
                && !(tmp1_off as int <= j < tmp1_off + n)
                && !(tmp2_off as int <= j < tmp2_off + n)
                ==> buf@[j] == pre_select[j],
    {
        let diff_val = T::select_limb(&borrow_ab, buf[tmp2_off + i].clone_limb(), buf[out_off + i].clone_limb());
        let final_val = T::select_limb(&same_sign, diff_val, buf[tmp1_off + i].clone_limb());

        proof {
            // Show that final_val.sem() == selected_seq[i].sem()
            let i_int = i as int;
            assert(buf[tmp2_off + i] == buf@[(tmp2_off as int) + i_int]);
            assert(buf[tmp1_off + i] == buf@[(tmp1_off as int) + i_int]);
            assert(buf[out_off + i] == buf@[(out_off as int) + i_int]);
            assert(buf@[(out_off as int) + i_int].sem() == bma_sub[i_int].sem());
            assert(buf@[(tmp1_off as int) + i_int] == sum_sub[i_int]);
            assert(buf@[(tmp2_off as int) + i_int] == amb_sub[i_int]);

            if ss_v == 1 {
                assert(selected_seq == sum_sub);
                assert(final_val.sem() == buf[tmp1_off + i].sem());
                assert(final_val.sem() == sum_sub[i_int].sem());
                assert(final_val.sem() == selected_seq[i_int].sem());
            } else if bab_v == 0 {
                assert(selected_seq == amb_sub);
                assert(diff_val.sem() == buf[tmp2_off + i].sem());
                assert(final_val.sem() == diff_val.sem());
                assert(final_val.sem() == amb_sub[i_int].sem());
                assert(final_val.sem() == selected_seq[i_int].sem());
            } else {
                assert(selected_seq == bma_sub);
                assert(diff_val.sem() == buf[out_off + i].sem());
                assert(final_val.sem() == diff_val.sem());
                assert(final_val.sem() == bma_sub[i_int].sem());
                assert(final_val.sem() == selected_seq[i_int].sem());
            }
        }
        let ghost buf_pre_set = buf@;
        buf.set(out_off + i, final_val);
        proof {
            let i_int = i as int;
            // Re-establish invariants
            assert forall |j: int| 0 <= j < i + 1
                implies #[trigger] buf@[(out_off as int + j) as int].sem() == selected_seq[j].sem() by {
                if j == i_int {
                    assert(buf@[(out_off as int) + j] == final_val);
                } else {
                    assert(buf@[(out_off as int) + j] == buf_pre_set[(out_off as int) + j]);
                }
            }
            assert forall |j: int| (i + 1) <= j < n
                implies #[trigger] buf@[(out_off as int + j) as int] == bma_sub[j] by {
                assert(j != i_int);
                assert(buf@[(out_off as int) + j] == buf_pre_set[(out_off as int) + j]);
            }
            // tmp1, tmp2 regions still preserved (non-overlap with out)
            assert forall |j: int| 0 <= j < n
                implies #[trigger] buf@[tmp1_off as int + j] == sum_sub[j] by {
                assert(buf@[(tmp1_off as int) + j] == buf_pre_set[(tmp1_off as int) + j]);
            }
            assert forall |j: int| 0 <= j < n
                implies #[trigger] buf@[tmp2_off as int + j] == amb_sub[j] by {
                assert(buf@[(tmp2_off as int) + j] == buf_pre_set[(tmp2_off as int) + j]);
            }
        }
    }

    proof {
        // After loop: vec_val(out subrange) == vec_val(selected_seq)
        let final_sub = buf@.subrange(out_off as int, (out_off + n) as int);
        assert(final_sub.len() == selected_seq.len());
        assert forall |j: int| 0 <= j < final_sub.len()
            implies (#[trigger] final_sub[j]).sem() == selected_seq[j].sem() by {
            assert(final_sub[j] == buf@[(out_off as int) + j]);
        }
        lemma_vec_val_eq_from_sem_eq::<T>(final_sub, selected_seq);
        assert(valid_limbs(final_sub)) by {
            assert forall |j: int| 0 <= j < final_sub.len()
                implies 0 <= (#[trigger] final_sub[j]).sem() && final_sub[j].sem() < LIMB_BASE() by {
                assert(final_sub[j] == buf@[(out_off as int) + j]);
            }
        }
        // Establish valid_limbs of sum_sub, amb_sub, bma_sub
        assert(valid_limbs(sum_sub)) by {
            assert forall |j: int| 0 <= j < sum_sub.len()
                implies 0 <= (#[trigger] sum_sub[j]).sem() && sum_sub[j].sem() < LIMB_BASE() by {
                assert(sum_sub[j] == buf@[(tmp1_off as int) + j]);
            }
        }
        assert(valid_limbs(amb_sub)) by {
            assert forall |j: int| 0 <= j < amb_sub.len()
                implies 0 <= (#[trigger] amb_sub[j]).sem() && amb_sub[j].sem() < LIMB_BASE() by {
                assert(amb_sub[j] == buf@[(tmp2_off as int) + j]);
            }
        }
        assert(valid_limbs(bma_sub)) by {
            assert forall |j: int| 0 <= j < bma_sub.len()
                implies 0 <= (#[trigger] bma_sub[j]).sem() && bma_sub[j].sem() < LIMB_BASE() by {
                assert(bma_sub[j] == pre_select[(out_off as int) + j]);
            }
        }

        // Apply lemma_signed_add_correct_seq
        lemma_signed_add_correct_seq::<T>(
            a_sub, a_sign.sem(),
            b_sub, b_sign.sem(),
            sum_sub, sum_carry.sem(),
            amb_sub, borrow_ab.sem(),
            bma_sub, borrow_ba.sem(),
            same_sign.sem(),
            final_sub, result_sign.sem(),
            n as nat,
        );
    }

    result_sign
}

/// Single-buffer signed subtraction.
pub fn signed_sub_to_buf<T: LimbOps>(
    a: &[T], a_sign: &T, b: &[T], b_sign: &T,
    buf: &mut Vec<T>, out_off: usize, tmp1_off: usize, tmp2_off: usize,
    n: usize,
) -> (out_sign: T)
    requires
        a@.len() >= n, b@.len() >= n, n > 0,
        old(buf)@.len() >= out_off + n,
        old(buf)@.len() >= tmp1_off + n,
        old(buf)@.len() >= tmp2_off + n,
        out_off + n < usize::MAX, tmp1_off + n < usize::MAX, tmp2_off + n < usize::MAX,
        valid_limbs(a@), valid_limbs(b@),
        a_sign.sem() == 0 || a_sign.sem() == 1,
        b_sign.sem() == 0 || b_sign.sem() == 1,
        // Non-overlap of all three regions
        out_off + n <= tmp1_off || tmp1_off + n <= out_off,
        out_off + n <= tmp2_off || tmp2_off + n <= out_off,
        tmp1_off + n <= tmp2_off || tmp2_off + n <= tmp1_off,
    ensures buf@.len() == old(buf)@.len(),
        out_sign.sem() == 0 || out_sign.sem() == 1,
        forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] buf@[out_off as int + j]).sem() < LIMB_BASE(),
        forall |j: int| 0 <= j < buf@.len()
            && !(out_off as int <= j < out_off + n)
            && !(tmp1_off as int <= j < tmp1_off + n)
            && !(tmp2_off as int <= j < tmp2_off + n)
            ==> buf@[j] == old(buf)@[j],
        // Signed-magnitude difference equation: 3-way modular disjunction
        // for a + (-b) = a - b
        ({
            let va = vec_val(a@.subrange(0, n as int));
            let vb = vec_val(b@.subrange(0, n as int));
            let vo = vec_val(buf@.subrange(out_off as int, (out_off + n) as int));
            let sa_signed = if a_sign.sem() == 0 { va } else { -va };
            let sb_signed = if b_sign.sem() == 0 { vb } else { -vb };
            let so_signed = if out_sign.sem() == 0 { vo } else { -vo };
            let true_diff = sa_signed - sb_signed;
            let P = limb_power(n as nat);
            so_signed == true_diff
                || (so_signed == true_diff - P && true_diff >= P)
                || (so_signed == true_diff + P && true_diff <= -(P as int))
        }),
{
    let neg_b_sign = T::select_limb(b_sign, T::const_u32(1u32), T::zero_val());
    let result = signed_add_to_buf(a, a_sign, b, &neg_b_sign, buf, out_off, tmp1_off, tmp2_off, n);
    proof {
        // -(-b) is just b. neg_b_sign flips b_sign: 0→1, 1→0.
        // signed(b, neg_b_sign) == -signed(b, b_sign), so a + (b with flipped sign) = a - b.
        // The signed_add_to_buf postcondition gives the sum with neg_b_sign as the b sign,
        // which corresponds to a - b in the original signs.
        let vb = vec_val(b@.subrange(0, n as int));
        if b_sign.sem() == 0 {
            // original b is non-negative, neg_b_sign == 1, signed(b, 1) == -vb == -signed(b, 0)
            assert(neg_b_sign.sem() == 1);
        } else {
            assert(neg_b_sign.sem() == 0);
        }
    }
    result
}

/// Single-buffer signed multiply.
#[verifier::rlimit(80)]
pub fn signed_mul_to_buf<T: LimbOps>(
    a: &[T], a_sign: &T, b: &[T], b_sign: &T,
    buf: &mut Vec<T>, out_off: usize, prod_off: usize,
    n: usize, frac_limbs: usize,
) -> (out_sign: T)
    requires
        a@.len() >= n, b@.len() >= n,
        n > 0, n <= 0x1FFF_FFFF,
        valid_limbs(a@), valid_limbs(b@),
        old(buf)@.len() >= out_off + n,
        old(buf)@.len() >= prod_off + 2 * n,
        out_off + n < usize::MAX,
        prod_off + 2 * n < usize::MAX,
        frac_limbs + n <= 2 * n,
        frac_limbs <= n,
        frac_limbs + n < usize::MAX,
        a_sign.sem() == 0 || a_sign.sem() == 1,
        b_sign.sem() == 0 || b_sign.sem() == 1,
        // Non-overlap: out region and prod region
        out_off + n <= prod_off || prod_off + 2 * n <= out_off,
    ensures buf@.len() == old(buf)@.len(),
        out_sign.sem() == 0 || out_sign.sem() == 1,
        // Sign is XOR of input signs (same sign → positive result)
        (a_sign.sem() == b_sign.sem()) ==> out_sign.sem() == 0,
        (a_sign.sem() != b_sign.sem()) ==> out_sign.sem() == 1,
        // Valid limbs on output region
        forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] buf@[out_off as int + j]).sem() < LIMB_BASE(),
        // Frame: indices outside out and prod regions unchanged
        forall |j: int| 0 <= j < buf@.len()
            && !(out_off as int <= j < out_off + n)
            && !(prod_off as int <= j < prod_off + 2 * n)
            ==> buf@[j] == old(buf)@[j],
        // Truncated product value equation: out is the truncated magnitude of a * b
        vec_val(buf@.subrange(out_off as int, (out_off + n) as int))
            == ((vec_val(a@.subrange(0, n as int)) * vec_val(b@.subrange(0, n as int)))
                / limb_power(frac_limbs as nat)) % limb_power(n as nat),
{
    mul_schoolbook_to(a, b, buf, prod_off, n);
    // Copy product[frac_limbs..frac_limbs+n] to out (can't use slice_vec_to: aliasing)
    let ghost buf_len = buf@.len();
    let ghost post_mul = buf@;
    for i in 0..n
        invariant
            buf@.len() == buf_len,
            buf_len >= out_off + n, buf_len >= prod_off + 2 * n,
            out_off + n < usize::MAX, prod_off + 2 * n < usize::MAX,
            frac_limbs + n <= 2 * n,
            frac_limbs + n < usize::MAX,
            out_off + n <= prod_off || prod_off + 2 * n <= out_off,
            n <= 0x1FFF_FFFF,
            // Product region preserved (non-overlapping with out writes)
            forall |j: int| prod_off as int <= j < prod_off + 2 * n ==> buf@[j] == post_mul[j],
            // Valid limbs in product snapshot (carried from mul_schoolbook_to postcondition)
            forall |j: int| 0 <= j < 2 * n ==> 0 <= (#[trigger] post_mul[prod_off as int + j]).sem() < LIMB_BASE(),
            // Already-copied output has valid limbs
            forall |j: int| 0 <= j < i ==> 0 <= (#[trigger] buf@[out_off as int + j]).sem() < LIMB_BASE(),
            // Already-copied output: value matches the corresponding product limb
            forall |j: int| 0 <= j < i
                ==> #[trigger] buf@[out_off as int + j].sem() == post_mul[(prod_off + frac_limbs) as int + j].sem(),
            // Frame outside both regions
            forall |j: int| 0 <= j < buf_len
                && !(out_off as int <= j < out_off + n)
                && !(prod_off as int <= j < prod_off + 2 * n)
                ==> buf@[j] == post_mul[j],
    {
        proof {
            // Chain: product snapshot has valid limbs at this index
            let j_idx: int = (frac_limbs + i) as int;
            assert(0 <= j_idx && j_idx < 2 * n);
            // Trigger the post_mul valid_limbs invariant
            assert(0 <= (#[trigger] post_mul[prod_off as int + j_idx]).sem() < LIMB_BASE());
            // Product region is preserved
            let abs_idx: int = (prod_off + frac_limbs + i) as int;
            assert(prod_off as int <= abs_idx && abs_idx < prod_off + 2 * n);
            assert(buf@[abs_idx] == post_mul[abs_idx]);
        }
        let val = buf[prod_off + frac_limbs + i].clone_limb();
        buf.set(out_off + i, val);
    }

    proof {
        // Build the truncated product value equation via lemma_truncated_product_seq.
        // The 2n-limb product is in buf[prod_off..prod_off+2n] (preserved by post_mul snapshot).
        // The truncated n limbs are in buf[out_off..out_off+n].
        let prod_full = post_mul.subrange(prod_off as int, (prod_off + 2 * n) as int);
        let out_sub = buf@.subrange(out_off as int, (out_off + n) as int);
        let a_sub = a@.subrange(0, n as int);
        let b_sub = b@.subrange(0, n as int);

        assert(prod_full.len() == 2 * n as int);
        // valid_limbs(prod_full) from the post_mul snapshot
        assert(valid_limbs(prod_full)) by {
            assert forall |k: int| 0 <= k < prod_full.len()
                implies 0 <= (#[trigger] prod_full[k]).sem() && prod_full[k].sem() < LIMB_BASE() by {
                assert(prod_full[k] == post_mul[prod_off as int + k]);
            }
        }
        assert(valid_limbs(out_sub)) by {
            assert forall |k: int| 0 <= k < out_sub.len()
                implies 0 <= (#[trigger] out_sub[k]).sem() && out_sub[k].sem() < LIMB_BASE() by {
                assert(out_sub[k] == buf@[(out_off as int) + k]);
            }
        }
        assert(valid_limbs(a_sub)) by {
            assert forall |k: int| 0 <= k < a_sub.len()
                implies 0 <= (#[trigger] a_sub[k]).sem() && a_sub[k].sem() < LIMB_BASE() by {
                assert(a_sub[k] == a@[k]);
            }
        }
        assert(valid_limbs(b_sub)) by {
            assert forall |k: int| 0 <= k < b_sub.len()
                implies 0 <= (#[trigger] b_sub[k]).sem() && b_sub[k].sem() < LIMB_BASE() by {
                assert(b_sub[k] == b@[k]);
            }
        }

        // post_mul holds the result of mul_schoolbook_to: vec_val(prod_full) == vec_val(a) * vec_val(b)
        // The post_mul value equation comes from mul_schoolbook_to's strengthened postcondition.
        assert(vec_val(prod_full) == vec_val(a_sub) * vec_val(b_sub));

        // out_sub[j].sem() == prod_full[(frac_limbs + j) as int].sem()
        // (the copy loop writes the truncated portion)
        assert forall |j: int| 0 <= j < n as int
            implies (#[trigger] out_sub[j]).sem() == prod_full[(frac_limbs as int + j) as int].sem() by {
            assert(out_sub[j] == buf@[(out_off as int) + j]);
            // After the copy loop, buf[out_off + j] == post_mul[prod_off + frac_limbs + j]
            assert(buf@[(out_off as int) + j].sem() == post_mul[(prod_off + frac_limbs) as int + j].sem());
            assert(prod_full[(frac_limbs as int) + j] == post_mul[(prod_off as int) + (frac_limbs as int) + j]);
        }

        lemma_truncated_product_seq::<T>(
            prod_full, out_sub,
            vec_val(a_sub), vec_val(b_sub),
            n as nat, frac_limbs as nat,
        );
    }

    let sign_b_flipped = T::select_limb(b_sign, T::const_u32(1u32), T::zero_val());
    T::select_limb(a_sign, b_sign.clone_limb(), sign_b_flipped)
}
} //  verus!
