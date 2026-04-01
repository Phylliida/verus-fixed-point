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
            out.1.sem() == (self.sem() + b.sem() + carry.sem()) / LIMB_BASE();

    ///  a - b - borrow_in → (result_limb, borrow_out)
    ///  result = (a - b - borrow + BASE) % BASE
    ///  borrow_out = if (a - b - borrow) < 0 then 1 else 0
    fn sub_borrow(&self, b: &Self, borrow: &Self) -> (out: (Self, Self))
        requires borrow.sem() == 0 || borrow.sem() == 1,
        ensures
            out.0.sem() == (self.sem() - b.sem() - borrow.sem() + LIMB_BASE()) % LIMB_BASE(),
            out.1.sem() == if self.sem() - b.sem() - borrow.sem() < 0 { 1int } else { 0int };

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
            out.1.sem() == (self.sem() * b.sem() + accum.sem() + carry.sem()) / LIMB_BASE();

    ///  Zero constant.
    fn zero_val() -> (out: Self)
        ensures out.sem() == 0int;

    ///  Constant from u32 value.
    fn const_u32(c: u32) -> (out: Self)
        ensures out.sem() == c as int;
}

//  ══════════════════════════════════════════════════════════════
//  u32 implementation of LimbOps
//  ══════════════════════════════════════════════════════════════

impl LimbOps for u32 {
    open spec fn sem(&self) -> int { *self as int }

    fn add3(&self, b: &Self, carry: &Self) -> (out: (Self, Self))
    {
        let sum: u64 = *self as u64 + *b as u64 + *carry as u64;
        let base: u64 = 4_294_967_296u64;
        let digit: u32 = (sum % base) as u32;
        let c_out: u32 = (sum / base) as u32;
        (digit, c_out)
    }

    fn sub_borrow(&self, b: &Self, borrow: &Self) -> (out: (Self, Self))
    {
        //  borrow is 0 or 1, so a + BASE - b - borrow >= BASE - (2^32-1) - 1 = 0
        let a_wide: u64 = *self as u64 + 4_294_967_296u64;
        proof {
            assert(a_wide >= *b as u64 + *borrow as u64) by(nonlinear_arith)
                requires *borrow <= 1u32, a_wide == *self as u64 + 4_294_967_296u64,
                         *b <= u32::MAX;
        }
        let result: u64 = a_wide - *b as u64 - *borrow as u64;
        let base: u64 = 4_294_967_296u64;
        let digit: u32 = (result % base) as u32;
        let raw: i64 = *self as i64 - *b as i64 - *borrow as i64;
        let borrow_out: u32 = if raw < 0 { 1u32 } else { 0u32 };
        (digit, borrow_out)
    }

    fn mul2(&self, b: &Self) -> (out: (Self, Self))
    {
        proof {
            assert((*self as u64) * (*b as u64) <= u64::MAX)
                by(nonlinear_arith)
                requires *self <= u32::MAX, *b <= u32::MAX;
        }
        let prod: u64 = *self as u64 * *b as u64;
        let base: u64 = 4_294_967_296u64;
        let lo: u32 = (prod % base) as u32;
        let hi: u32 = (prod / base) as u32;
        (lo, hi)
    }

    fn mul_add_carry(&self, b: &Self, accum: &Self, carry: &Self) -> (out: (Self, Self))
    {
        proof {
            //  (2^32-1)^2 + 2*(2^32-1) = 2^64 - 1 = u64::MAX
            assert((*self as u64) * (*b as u64) + (*accum as u64) + (*carry as u64) <= u64::MAX)
                by(nonlinear_arith)
                requires *self <= u32::MAX, *b <= u32::MAX,
                         *accum <= u32::MAX, *carry <= u32::MAX;
        }
        let prod: u64 = *self as u64 * *b as u64 + *accum as u64 + *carry as u64;
        let base: u64 = 4_294_967_296u64;
        let digit: u32 = (prod % base) as u32;
        let c_out: u32 = (prod / base) as u32;
        (digit, c_out)
    }

    fn zero_val() -> (out: Self) { 0u32 }

    fn const_u32(c: u32) -> (out: Self) { c }
}

} //  verus!
