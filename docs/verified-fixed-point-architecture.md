# verus-fixed-point Session Summary

## What We Built

From an empty repo to **381 verified lemmas, 0 errors, 15 files, zero assumes** —
a formally verified arbitrary-precision fixed-point arithmetic library in Verus.

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
  This was THE key lemma that unlocked structural equality between exec and spec.
        ↑
Exec NTT
  RuntimeModularInt (add/sub/mul/copy exec ops)
  bit_reverse_permutation, ntt_butterfly_exec (Cooley-Tukey in-place)
  mul_ntt pipeline: limbs→modular→NTT→pointwise→INTT→scale→carry→limbs
        ↑
Newton-Raphson Division
  recip_newton: x_{n+1} = x_n * (2 - b*x_n), O(n^1.585 * log n)
  div_rfp: a * recip(b), recip_interval, div_interval
  Convergence proof: 1 - b*x' = (1-b*x)² (integer identity, fully proved)
  Error bound: |error_k| ≤ m^{2^k} (inductive, fully proved)
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

5. **Base-2^32 uniqueness** — THE breakthrough that connected exec to spec. If two
   u32 sequences of the same length have the same `limbs_to_nat`, they're identical.
   This means exec-computed limbs ARE the spec model's limbs — structural equality,
   not just equivalence.

6. **`frac_exec` field** — RuntimeFixedPointInterval stores frac as a usize (not just
   Ghost) so exec operations can access it for Newton division, from_u32 construction, etc.

## What's Proven (Highlights)

- **Karatsuba algebraic identity** — `(a_hi*B + a_lo)(b_hi*B + b_lo) = z0 + z1*B + z2*B²`
  proved step-by-step via distributive law. No-overflow and combine lemmas for all carries/borrows.

- **Modular arithmetic Ring axioms** — associativity of add and mul mod p,
  distributive law, all proved from `lemma_fundamental_div_mod`.

- **Newton convergence** — `1 - b*x*(2-b*x) = (1-b*x)²` (the core identity),
  plus `|error_k| ≤ m^{2^k}` (inductive error bound).

- **cmp_signed_rfp → Rational ordering** — exec comparison of RuntimeFixedPoints
  proven to correspond to `lt_spec`/`eqv_spec` on Rational views. All 4 sign cases.

- **div_by_u32 full correctness** — `ltn(quot) * divisor + remainder == ltn(a)`.
  Top-down loop invariant with ghost accumulators, `q < BASE` proof, set-stability.

- **add_rfp structural equality** — `result@ == a@.add_spec(b@)`. The exec-computed
  FixedPoint IS the spec-level add result, not just eqv. Same for mul_rfp, neg_rfp.

- **Interval add containment** — `lo.view() <= exact_sum <= hi.view()` where
  exact_sum = ghost_a + ghost_b. Chain through `lemma_le_add_both` + eqv bridge.

## What's NOT Yet Proven / Remaining Work

### 1. Truncated Newton Convergence (THE remaining hard proof)

The pure Newton identity is proved: `1 - b*x' = (1-b*x)²`.
The error bound is proved: `|e_k| ≤ m^{2^k}`.

**What's missing:** connecting this to the EXEC Newton which has `reduce_rfp_floor`
(truncation) at each step. The truncated recurrence is:
```
e_{k+1} = e_k² + δ_k   where |δ_k| ≤ 1 ULP = 2^(-frac)
```

For convergence: once `|e_k|` is small enough, `|e_k|² + 2^(-frac) < |e_k|`,
so the error keeps shrinking. After log₂(frac) iterations, error < 1 ULP.

**Literature insight:** The MDPI paper "Divisions and Square Roots with Tight Error
Analysis from Newton-Raphson Iteration in Secure Fixed-Point Arithmetic" handles
exactly this — tight error bounds for Newton with fixed-point truncation.

**Approach:** Define `truncated_error(b, x, frac) = b * ltn(x) - pow2(frac)`
at the integer level. Prove: each exec step satisfies
`|truncated_error_{k+1}| ≤ |truncated_error_k|² / pow2(frac) + 1`.
For `|e_0| < pow2(frac)` and `k ≥ log2(frac)`: `|e_k| < 2`.

### 2. RuntimeFieldOps<Rational> Trait Implementation

**Blocked on #1.** The trait requires `rf_recip` with exact ghost ensures:
`out.rf_view() == self.rf_view().recip()`. The ghost exact IS a Rational (works),
but `wf_spec` requires `lo.view() <= exact <= hi.view()` which needs proven
containment of the Newton reciprocal.

**All ring operations are ready:** add, sub, neg, mul (both nonneg and general),
copy, zero_like, one_like, comparison. Only recip/div need the truncated convergence.

### 3. Perturbation Theory (goes in verus-fractals, not verus-fixed-point)

Types and operations for deep fractal zoom:
- `PerturbedValue { reference: RuntimeFixedPoint, delta: RuntimeFixedPointInterval }`
- `perturb_step`: δ_{n+1} = 2*Z_n*δ_n + δ_n² + δ_c
- `glitch_detect`: interval width check
- `rebase`: shift to new reference point

### 4. NTT Full Correctness

The exec butterfly runs and is verified wf-preserving. The spec-level NTT is defined
(DFT matrix, forward/inverse, convolution theorem). The butterfly identity is proven.
**Not yet proven:** that the exec butterfly output equals `ntt_forward_spec(input)`.
This needs a stage-by-stage loop invariant matching the Cooley-Tukey decomposition.

### 5. General Interval Mul Containment

The min4/max4 exec selection is proven to produce bounds where lo ≤ all corners and
hi ≥ all corners. **Not yet formally proven:** that the ghost exact product falls
between lo and hi. Structurally sound (from `Interval::lemma_mul_containment`) but
the formal chain connecting exec min/max to the Rational-level containment is verbose.

## Crate Structure

```
verus-fixed-point/
├── Cargo.toml
├── docs/
│   ├── design.md              (original design document)
│   └── session-summary.md     (this file)
├── src/
│   ├── lib.rs
│   ├── runtime_fixed_point.rs  (exec: RuntimeFixedPoint, RuntimeFixedPointInterval,
│   │                            all exec limb ops, interval ops, Newton, NTT mul)
│   └── fixed_point/
│       ├── mod.rs              (FixedPoint spec struct, view, wf, signed_value)
│       ├── pow2.rs             (pow2 spec + lemmas, pow_int)
│       ├── limbs.rs            (limbs_to_nat, nat_to_limbs, uniqueness, split, etc.)
│       ├── constructors.rs     (zero, one proof constructors)
│       ├── comparison.rs       (eqv/le/lt via Rational delegation)
│       ├── view_lemmas.rs      (from_frac bridge lemmas: neg, mul, add, sub, ordering)
│       ├── arithmetic.rs       (spec add/sub/neg/mul/promote)
│       ├── promotion.rs        (promote_n, promote with fractional shift)
│       ├── reduce.rs           (ceil_div, reduce_down/up with directed rounding)
│       ├── interval.rs         (FixedPointInterval with ghost exact)
│       ├── modular.rs          (ModularInt spec + Ring axioms + RuntimeModularInt exec)
│       ├── ntt.rs              (NTT specs + exec butterfly + NTT mul pipeline)
│       └── newton_convergence.rs (convergence identity + error bounds)
```

## Dependencies

- `vstd` — Verus standard library
- `verus-rational` — Rational type, field axioms, ordering lemmas
- `verus-interval-arithmetic` — Interval spec type, containment lemmas
- `verus-quadratic-extension` — RuntimeFieldOps trait (for future impl)
- `verus-algebra` — Ring/Field/OrderedField trait hierarchy

## Lessons Learned

1. **`nonlinear_arith` is very limited.** Can't prove distributive law, modular
   properties, or multi-variable polynomial identities. Break everything into
   2-variable steps with explicit `requires`.

2. **`nat` subtraction produces `int`.** Every `a - b` for nats becomes int,
   causing type issues in `nonlinear_arith` blocks and spec functions.

3. **`lemma_fundamental_div_mod` is crucial.** The only way to prove modular
   arithmetic properties (associativity etc.) — provides `x == d*(x/d) + x%d`.

4. **Ghost fields can't be accessed at exec level.** `frac: Ghost<nat>` means
   Newton can't construct `two` or `one`. Fixed by adding `frac_exec: usize`.

5. **`reveal_with_fuel` needed for recursive spec unfolding.** Z3 won't unfold
   recursive spec functions automatically. `reveal_with_fuel(f, k)` forces k steps.

6. **Base-2^32 uniqueness was the key insight.** Without it, exec results only
   have `ltn(exec_limbs) == ltn(spec_limbs)` — same value but potentially
   different sequences. Uniqueness gives structural equality, which Z3 propagates.

7. **Save mutable state before mutation.** The `div_by_u32` bug: `rem` was updated
   before the proof block tried to use it to reason about `cur`. Always save
   `let ghost old_rem = rem` before `rem = new_rem`.

8. **`Vec::set` doesn't change other indices.** But Z3 needs explicit assertions
   like `v.subrange(i+1, n) =~= old_v.subrange(i+1, n)` after `v.set(i, x)`.

9. **Overflow proofs must come BEFORE the exec operation.** Verus checks overflow
   at the point of computation, not retroactively. Put the overflow bound in a
   `proof {}` block before `let product = a * b`.

10. **Karatsuba proof needs very small steps.** Even `(a+b)*c == a*c + b*c`
    can't be proved in one `nonlinear_arith` call. Use `lemma_mul_distribute`
    (our own helper) and chain through named intermediates.
