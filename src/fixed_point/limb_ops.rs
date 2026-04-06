///  LimbOps: trait abstracting single-limb operations for multi-limb arithmetic.
///
///  Implementations:
///  - u32: concrete limb arithmetic using u64 intermediates
///  - RuntimeArithExpr: builds symbolic expression trees (in verus-fractals)
///
///  Generic multi-limb algorithms (add_limbs, mul_schoolbook, mul_karatsuba)
///  use this trait, so correctness is proved once for both instantiations.

use vstd::prelude::*;
use super::limbs::limb_base;
#[cfg(verus_keep_ghost)]
use super::limbs::{lemma_limb_base_is_pow2_32, lemma_karatsuba_identity, lemma_mul_distribute};
#[cfg(verus_keep_ghost)]
use super::limbs as limb_base_conv;

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
            assert(prod == p3 as int * base + (p1 as int + p2 as int) * half + p0 as int)
                by(nonlinear_arith)
                requires
                    prod == (*self as int) * (*b as int),
                    *self as int == a_hi as int * half + a_lo as int,
                    *b as int == b_hi as int * half + b_lo as int,
                    p0 as int == a_lo as int * b_lo as int,
                    p1 as int == a_lo as int * b_hi as int,
                    p2 as int == a_hi as int * b_lo as int,
                    p3 as int == a_hi as int * b_hi as int,
                    base == half * half;
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
pub fn generic_add_limbs<T: LimbOps>(a: &Vec<T>, b: &Vec<T>, n: usize) -> (result: (Vec<T>, T))
    requires
        a@.len() == n,
        b@.len() == n,
        valid_limbs(a@),
        valid_limbs(b@),
    ensures
        result.0@.len() == n,
        valid_limbs(result.0@),
        0 <= result.1.sem() < LIMB_BASE(),
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
    }

    (out, carry)
}

//  ══════════════════════════════════════════════════════════════
//  GPU-compatible output-parameter variants (no Vec::new/push)
//  ══════════════════════════════════════════════════════════════

///  Carry-chain addition writing to caller-provided output buffer.
///  GPU-compatible: no Vec allocation, writes to out[0..n].
pub fn add_limbs_to<T: LimbOps>(a: &Vec<T>, b: &Vec<T>, out: &mut Vec<T>, n: usize) -> (carry: T)
    requires
        a@.len() == n, b@.len() == n, old(out)@.len() >= n,
        valid_limbs(a@), valid_limbs(b@),
    ensures
        out@.len() == old(out)@.len(),
        0 <= carry.sem() < LIMB_BASE(),
        forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] out@[j]).sem() < LIMB_BASE(),
{
    let ghost out_len = out@.len();
    let mut carry: T = T::zero_val();
    for i in 0..n
        invariant
            a@.len() == n, b@.len() == n,
            out@.len() == out_len, out_len >= n,
            valid_limbs(a@), valid_limbs(b@),
            0 <= carry.sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < i ==> 0 <= (#[trigger] out@[j]).sem() < LIMB_BASE(),
    {
        let (digit, next_carry) = a[i].add3(&b[i], &carry);
        out.set(i, digit);
        carry = next_carry;
    }
    carry
}

///  Borrow-chain subtraction writing to caller-provided output buffer.
pub fn sub_limbs_to<T: LimbOps>(a: &Vec<T>, b: &Vec<T>, out: &mut Vec<T>, n: usize) -> (borrow: T)
    requires
        a@.len() == n, b@.len() == n, old(out)@.len() >= n,
        valid_limbs(a@), valid_limbs(b@),
    ensures
        out@.len() == old(out)@.len(),
        borrow.sem() == 0 || borrow.sem() == 1,
        forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] out@[j]).sem() < LIMB_BASE(),
{
    let ghost out_len = out@.len();
    let mut borrow: T = T::zero_val();
    for i in 0..n
        invariant
            a@.len() == n, b@.len() == n,
            out@.len() == out_len, out_len >= n,
            valid_limbs(a@), valid_limbs(b@),
            borrow.sem() == 0 || borrow.sem() == 1,
            forall |j: int| 0 <= j < i ==> 0 <= (#[trigger] out@[j]).sem() < LIMB_BASE(),
    {
        let (digit, next_borrow) = a[i].sub_borrow(&b[i], &borrow);
        out.set(i, digit);
        borrow = next_borrow;
    }
    borrow
}

///  Conditional select writing to caller-provided output buffer.
pub fn select_vec_to<T: LimbOps>(
    cond: &T, if_zero: &Vec<T>, if_nonzero: &Vec<T>, out: &mut Vec<T>, n: usize,
)
    requires
        cond.sem() == 0 || cond.sem() == 1,
        if_zero@.len() == n, if_nonzero@.len() == n,
        old(out)@.len() >= n,
        valid_limbs(if_zero@), valid_limbs(if_nonzero@),
    ensures out@.len() == old(out)@.len(),
{
    let ghost out_len = out@.len();
    for i in 0..n
        invariant
            if_zero@.len() == n, if_nonzero@.len() == n,
            out@.len() == out_len, out_len >= n,
            valid_limbs(if_zero@), valid_limbs(if_nonzero@),
            cond.sem() == 0 || cond.sem() == 1,
    {
        let selected = T::select_limb(cond, if_zero[i].clone_limb(), if_nonzero[i].clone_limb());
        out.set(i, selected);
    }
}

///  Copy a slice of a Vec into an output buffer.
pub fn slice_vec_to<T: LimbOps>(a: &Vec<T>, start: usize, end: usize, out: &mut Vec<T>, out_off: usize)
    requires
        start <= end, end <= a@.len(),
        out_off + (end - start) < usize::MAX,
        out_off + (end - start) <= old(out)@.len(),
    ensures out@.len() == old(out)@.len(),
{
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
    a: &Vec<T>, a_sign: &T, b: &Vec<T>, b_sign: &T,
    out: &mut Vec<T>, tmp1: &mut Vec<T>, tmp2: &mut Vec<T>,
    n: usize,
) -> (out_sign: T)
    requires
        a@.len() == n, b@.len() == n,
        old(out)@.len() >= n, old(tmp1)@.len() >= n, old(tmp2)@.len() >= n,
        valid_limbs(a@), valid_limbs(b@),
        a_sign.sem() == 0 || a_sign.sem() == 1,
        b_sign.sem() == 0 || b_sign.sem() == 1,
    ensures out@.len() == old(out)@.len(),
        tmp1@.len() == old(tmp1)@.len(), tmp2@.len() == old(tmp2)@.len(),
        out_sign.sem() == 0 || out_sign.sem() == 1,
{
    // Compute a + b (unsigned) → tmp1
    let _sum_carry = add_limbs_to(a, b, tmp1, n);
    // Compute a - b → tmp2
    let borrow_ab = sub_limbs_to(a, b, tmp2, n);
    // Compute b - a → out (will be overwritten later if not used)
    let _borrow_ba = sub_limbs_to(b, a, out, n);

    // same_sign indicator
    let (sign_diff, sign_borrow) = a_sign.sub_borrow(b_sign, &T::zero_val());
    let diff_zero = sign_diff.is_zero_limb();
    let borrow_zero = sign_borrow.is_zero_limb();
    let (same_sign, _) = diff_zero.mul2(&borrow_zero);

    // diff_sign result: select a-b (tmp2) or b-a (out) based on borrow_ab
    // Write to tmp1 (reuse since sum is no longer needed after final select)
    // Wait — tmp1 has the sum, which we still need for same_sign case.
    // We need all three alive: sum(tmp1), a-b(tmp2), b-a(out).
    // Then: diff_selected = select(borrow_ab, tmp2, out) → can't write to tmp2 or out.
    // Solution: do the TWO selects in sequence, writing directly to out.
    //
    // Step 1: If same_sign, out = tmp1 (sum). If diff_sign, out = select(borrow, tmp2, out).
    // But we can't read out and write out simultaneously.
    //
    // Simplest: do element-wise select in a loop.
    let diff_sign = T::select_limb(&borrow_ab, a_sign.clone_limb(), b_sign.clone_limb());
    // same_sign=1 → use a_sign (common sign), same_sign=0 → use diff_sign
    let result_sign = T::select_limb(&same_sign, diff_sign, a_sign.clone_limb());

    // Element-wise double select: same_sign=1 → sum, same_sign=0 → diff
    let ghost out_len = out@.len();
    for i in 0..n
        invariant
            out@.len() == out_len, out_len >= n,
            tmp1@.len() >= n, tmp2@.len() >= n,
            same_sign.sem() == 0 || same_sign.sem() == 1,
            borrow_ab.sem() == 0 || borrow_ab.sem() == 1,
            forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] tmp1@[j]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] tmp2@[j]).sem() < LIMB_BASE(),
            forall |j: int| 0 <= j < n ==> 0 <= (#[trigger] out@[j]).sem() < LIMB_BASE(),
    {
        let diff_val = T::select_limb(&borrow_ab, tmp2[i].clone_limb(), out[i].clone_limb());
        // same_sign=1 → sum (tmp1), same_sign=0 → diff
        let final_val = T::select_limb(&same_sign, diff_val, tmp1[i].clone_limb());
        out.set(i, final_val);
    }

    result_sign
}

///  Signed subtraction: a - b = a + (-b). No Vec::new.
pub fn signed_sub_to<T: LimbOps>(
    a: &Vec<T>, a_sign: &T, b: &Vec<T>, b_sign: &T,
    out: &mut Vec<T>, tmp1: &mut Vec<T>, tmp2: &mut Vec<T>,
    n: usize,
) -> (out_sign: T)
    requires
        a@.len() == n, b@.len() == n,
        old(out)@.len() >= n, old(tmp1)@.len() >= n, old(tmp2)@.len() >= n,
        valid_limbs(a@), valid_limbs(b@),
        a_sign.sem() == 0 || a_sign.sem() == 1,
        b_sign.sem() == 0 || b_sign.sem() == 1,
    ensures out@.len() == old(out)@.len(),
        tmp1@.len() == old(tmp1)@.len(), tmp2@.len() == old(tmp2)@.len(),
        out_sign.sem() == 0 || out_sign.sem() == 1,
{
    let neg_b_sign = T::select_limb(b_sign, T::const_u32(1u32), T::zero_val());
    signed_add_to(a, a_sign, b, &neg_b_sign, out, tmp1, tmp2, n)
}

///  Signed fixed-point multiply. No Vec::new.
pub fn signed_mul_to<T: LimbOps>(
    a: &Vec<T>, a_sign: &T, b: &Vec<T>, b_sign: &T,
    out: &mut Vec<T>, prod: &mut Vec<T>,
    n: usize, frac_limbs: usize,
) -> (out_sign: T)
    requires
        a@.len() == n, b@.len() == n,
        n > 0, n <= 0x1FFF_FFFF,
        valid_limbs(a@), valid_limbs(b@),
        old(out)@.len() >= n,
        old(prod)@.len() >= 2 * n,
        frac_limbs + n <= 2 * n,
        frac_limbs + n < usize::MAX,
        a_sign.sem() == 0 || a_sign.sem() == 1,
        b_sign.sem() == 0 || b_sign.sem() == 1,
    ensures out@.len() == old(out)@.len(),
        prod@.len() == old(prod)@.len(),
        out_sign.sem() == 0 || out_sign.sem() == 1,
{
    mul_schoolbook_to(a, b, prod, n);
    slice_vec_to(prod, frac_limbs, frac_limbs + n, out, 0);
    let sign_b_flipped = T::select_limb(b_sign, T::const_u32(1u32), T::zero_val());
    T::select_limb(a_sign, b_sign.clone_limb(), sign_b_flipped)
}

//  ══════════════════════════════════════════════════════════════
//  Generic scalar multiplication (a * scalar)
//  ══════════════════════════════════════════════════════════════

///  Multiply n-limb array by a single limb. Returns (n+1)-limb result.
///  limbs_val(result) == limbs_val(a) * scalar.sem()
pub fn generic_mul_by_limb<T: LimbOps>(a: &Vec<T>, scalar: &T, n: usize) -> (result: Vec<T>)
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
pub fn generic_sub_limbs<T: LimbOps>(a: &Vec<T>, b: &Vec<T>, n: usize) -> (result: (Vec<T>, T))
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
pub fn generic_slice_vec<T: LimbOps>(a: &Vec<T>, start: usize, end: usize) -> (result: Vec<T>)
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
pub fn generic_pad_to_length<T: LimbOps>(a: &Vec<T>, target: usize) -> (result: Vec<T>)
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
pub fn generic_shift_left<T: LimbOps>(a: &Vec<T>, offset: usize) -> (result: Vec<T>)
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
    a: &Vec<T>, b: &Vec<T>, out: &mut Vec<T>, n: usize,
)
    requires
        a@.len() == n, b@.len() == n,
        n > 0, n <= 0x3FFF_FFFF,
        valid_limbs(a@), valid_limbs(b@),
        old(out)@.len() >= 2 * n,
    ensures
        out@.len() == old(out)@.len(),
{
    let ghost out_len = out@.len();
    let nn: usize = 2 * n;

    // Zero the output region
    for i in 0..nn
        invariant out@.len() == out_len, out_len >= nn, nn == 2 * n,
    {
        out.set(i, T::zero_val());
    }

    // Schoolbook: for each limb b[i], multiply a by b[i] and accumulate into out
    for i in 0..n
        invariant
            a@.len() == n, b@.len() == n,
            nn == 2 * n, n <= 0x3FFF_FFFF,
            out@.len() == out_len, out_len >= nn,
            valid_limbs(a@), valid_limbs(b@),
    {
        let mut carry: T = T::zero_val();
        for j in 0..n
            invariant
                a@.len() == n, b@.len() == n,
                out@.len() == out_len, out_len >= nn,
                nn == 2 * n, n <= 0x3FFF_FFFF,
                i < n,
                valid_limbs(a@), valid_limbs(b@),
                0 <= carry.sem() < LIMB_BASE(),
        {
            let (prod_lo, prod_hi) = a[j].mul2(&b[i]);
            let (sum1, c1) = prod_lo.add3(&out[i + j], &carry);
            let (new_carry, _c2) = prod_hi.add3(&c1, &T::zero_val());
            out.set(i + j, sum1);
            carry = new_carry;
        }
        out.set(i + n, carry);
    }
}

///  Multiply writing to output buffer. GPU-compatible interface.
///  Writes 2n limbs to out[0..2n].
///  For n <= 4: uses schoolbook directly (no allocation).
///  For n > 4: delegates to Karatsuba internally, copies result to out.
///  The transpiler unrolls this into depth-stratified variants.
// #[gpu_base_case(mul_schoolbook_to)]
pub fn mul_to<T: LimbOps>(
    a: &Vec<T>, b: &Vec<T>, out: &mut Vec<T>, n: usize,
)
    requires
        a@.len() == n, b@.len() == n,
        n > 0, n <= 0x1FFF_FFFF,
        valid_limbs(a@), valid_limbs(b@),
        old(out)@.len() >= 2 * n,
    ensures
        out@.len() == old(out)@.len(),
{
    let ghost out_len = out@.len();
    if n <= 4 {
        mul_schoolbook_to(a, b, out, n);
    } else {
        let (product, _gc) = generic_mul_karatsuba(a, b, n);
        for i in 0..(2 * n)
            invariant
                product@.len() == 2 * n,
                out@.len() == out_len, out_len >= 2 * n,
                n <= 0x3FFF_FFFF,
        {
            out.set(i, product[i].clone_limb());
        }
    }
}

///  Schoolbook multiply: returns 2n-limb result.
///  vec_val(result) == vec_val(a) * vec_val(b)
///  Returns (result, ghost_carry) where:
///  vec_val(result) + ghost_carry * BASE^(2n) == vec_val(a) * vec_val(b)
///  For valid u32 limbs, ghost_carry == 0 (product fits in 2n limbs).
pub fn generic_mul_schoolbook<T: LimbOps>(
    a: &Vec<T>, b: &Vec<T>, n: usize,
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
    a: &Vec<T>, b: &Vec<T>, n: usize,
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

} //  verus!
