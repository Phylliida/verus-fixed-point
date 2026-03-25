# verus-fixed-point Architecture

## Current State: 412 verified, 0 errors, 15 files, zero assumes

## Architecture

```
GPU Fractal Rendering (future)
        ↑
Exec Interval Arithmetic
  add_interval, sub_interval, neg_interval, mul_interval_nonneg,
  mul_interval_general (min4/max4), square_interval (3-case)
        ↑
Exec Signed Arithmetic
  add_rfp (structural equality with spec!), neg_rfp, mul_rfp,
  sub_rfp, div_rfp (Newton-Raphson), mul_reduce_rfp, from_u32
        ↑
Exec Unsigned Limb Ops
  add_limbs (carry chain), sub_limbs (borrow chain),
  mul_schoolbook O(n²), mul_karatsuba O(n^1.585),
  div_by_u32 (full correctness!), cmp_limbs, is_all_zero,
  shift_left, shift_right_limbs, pad_to_length, zero_vec, slice_vec
        ↑
Base-2^32 Uniqueness Bridge
  lemma_limbs_to_nat_unique — if ltn(a) == ltn(b) and len equal, then a == b
  lemma_limbs_nat_to_limbs_identity — a == nat_to_limbs(ltn(a), n)
        ↑
Exec NTT
  RuntimeModularInt (add/sub/mul/copy exec ops)
  bit_reverse_permutation, ntt_butterfly_exec (Cooley-Tukey in-place)
  mul_ntt pipeline: limbs→modular→NTT→pointwise→INTT→scale→carry→limbs
        ↑
Newton-Raphson Division
  recip_newton: x_{n+1} = x_n * (2 - b*x_n), O(n^1.585 * log n)
  div_rfp: a * recip(b), recip_interval, div_interval
  Convergence proofs: see "Truncated Newton Convergence" below
        ↑
Spec Interval Arithmetic
  FixedPointInterval with ghost exact: Rational
  wf: lo.view() <= exact <= hi.view()
  add/sub/neg/reduce/promote — all maintain ghost exact
  reduce is the ONLY place precision is lost
        ↑
Spec FixedPoint Arithmetic
  add_spec, sub_spec, neg_spec, mul_spec (widening), promote_spec
  All exact — view() of result IS the mathematical operation
        ↑
Spec Foundations
  FixedPoint { limbs: Seq<u32>, sign: bool, n: nat, frac: nat }
  view() → Rational via from_frac_spec(signed_value, pow2(frac))
  limbs_to_nat, nat_to_limbs, pow2 + 57 lemmas
  ModularInt + full Ring axioms (associativity, distributivity proved!)
  NTT specs: forward, inverse, DFT eval, convolution theorem, bit-reverse
```

## Key Design Decisions

1. **Sign-magnitude representation** — simpler mul proofs, canonical zero invariant
   (`sign == true ==> magnitude != 0`)

2. **Ghost exact tracking on intervals** — the `exact: Rational` field is the true
   mathematical value. exec lo/hi are just bounds. Field axioms hold at ghost level.

3. **Spec operations are EXACT** — `add_spec`, `mul_spec` etc. use `nat_to_limbs`
   which gives the precise result. No approximation at the spec level.

4. **reduce is the only approximation** — `reduce_down` (toward -∞) and `reduce_up`
   (toward +∞) are sign-aware directed rounding. Proven to preserve containment.

5. **Base-2^32 uniqueness** — THE breakthrough that connected exec to spec.

6. **`frac_exec` field** — RuntimeFixedPointInterval stores frac as a usize (not just
   Ghost) so exec operations can access it for Newton division, from_u32 construction, etc.

## reduce_rfp_floor: The Shift Fix

**Bug found and fixed:** The original `reduce_rfp_floor` shifted by `a.n - target_n` limbs
(the limb count difference). For mul results (2N limbs, 2F frac) → (N limbs, F frac), the
correct shift is `(a.frac - target_frac) / 32 = F/32` limbs (the fractional precision
difference). These differ when there are integer bits (D = N*32 - F > 0).

**Example:** N=2, F=32. Product 1.5×1.0=1.5 as wide limbs `[0, 2^31, 1, 0]` (n=4, frac=64).
- Old (wrong): shift by 2 limbs → `[1, 0]` → value ≈ 0
- New (correct): shift by 1 limb → `[2^31, 1]` → value = 1.5 ✓

**Postcondition:** Uses modulo to handle potential overflow gracefully:
```
ltn(result) == (ltn(a) / pow2(shift_limbs * 32)) % pow2(target_n * 32)
```
When there's no overflow, the modulo is a no-op and this simplifies to exact floor division.

## Truncated Newton Convergence

The exec Newton iteration uses `reduce_rfp_floor` at each step, introducing floor truncation.
The mathematical analysis shows:

**Error recurrence:** `e_{k+1} ≤ e_k² / S + 2` where S = pow2(frac), accounting for two
floor operations per step.

**Convergence to fixpoint:** The iteration converges to |e| ≤ 3 (not 0), giving ~3 ULP
accuracy. This is sufficient for interval arithmetic (widen by ±4 ULP).

**Proven spec lemmas:**
- `lemma_first_step_error` — First step is exact: bx₀ = b, x₁ = 2S - b
- `lemma_first_step_error_bound` — After first step with b ∈ [S, 3S/2]: error ≤ S/2
- `lemma_truncated_half_stable` — e ≤ S/2 preserved (S ≥ 8)
- `lemma_truncated_fixpoint_3` — e ≤ 3 is a fixpoint (S ≥ 12)
- `lemma_truncated_error_nonincreasing` — e doesn't grow for e ∈ [4, S/2]
- `lemma_bx_amgm` — For bx ∈ [0, 2S]: bx*(2S-bx) ≤ S² (AM-GM)
- `lemma_bx_bound_preserved` — bx ≤ S+1 is self-preserving via AM-GM

**Precondition:** `b ∈ [S, 3S/2]` (1.0 ≤ b_real ≤ 1.5). Callers normalize b to this range.

## Remaining Work

### 1. Exec↔Spec Connection for Newton Loop (next step)
Connect the exec `mul_rfp → reduce_rfp_floor` chain to `ltn(bx) = (b*x/S) % pow2(n*32)`.
This chains mul structural equality through reduce modulo. Once done, `lemma_bx_bound_preserved`
becomes the loop invariant proof and the convergence postcondition follows.

### 2. recip_interval Containment
With the convergence postcondition: widen Newton result by ±4 ULP, prove the interval
contains the exact reciprocal 1/b.

### 3. RuntimeFieldOps<Rational> Trait Implementation
Blocked on #2. All ring ops ready, only recip/div need proven containment.

### 4. NTT Full Correctness
Stage-by-stage loop invariant matching Cooley-Tukey decomposition.

### 5. Perturbation Theory (in verus-fractals)
PerturbedValue type, perturb_step, glitch_detect, rebase.

## Lessons Learned (Updated)

1-10. (See previous version — all still apply)

11. **`nat - nat` gives `int` in Verus.** Every subtraction of nats produces int,
    requiring explicit `as nat` casts and proofs of non-negativity.

12. **`nonlinear_arith` can't prove `(x/32)*32 == x` from `x%32 == 0`.**
    Use `lemma_fundamental_div_mod(x, 32)` instead.

13. **AM-GM at the integer level** — `bx*(2S-bx) ≤ S²` for bx ∈ [0, 2S] is the key
    bound for Newton loop invariant preservation. Proved via `nonlinear_arith`.

14. **Modulo postcondition avoids circular overflow dependencies.** When overflow bounds
    depend on convergence which depends on the reduce output, use modulo postcondition
    (always valid) and prove modulo is no-op separately.
