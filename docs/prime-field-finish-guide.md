# Finishing the Prime Field mul_mod Proof (117 verified, 6 errors)

## Status

The verified prime field Z/pZ has all spec-level Ring axioms proved, all runtime
operations verified (add_mod, neg_mod, sub_mod), and mul_mod exec code written.
The remaining work is proving `mersenne_reduce_exec`'s modular postcondition.

### Current errors (from `verus_check` on `prime_field.rs`)

| # | Function | Error | Root cause |
|---|----------|-------|------------|
| 1-2 | `mersenne_carry_folds` | postcondition not satisfied (x2) | Modular postcondition added but never proved |
| 3 | `mersenne_reduce_exec` | rlimit exceeded | Function too large (~200 lines exec+proof) |
| 4-5 | `mersenne_reduce_exec` | requires not satisfied, assertion failed (x3) | Cascades from rlimit |
| 6 | `mul_mod` | postcondition not satisfied | Cascades from reduce_exec |

## Why the Previous Approach Failed

The previous session inlined the carry fold code (fold3-fold9) directly into
`mersenne_reduce_exec` so all intermediate variables would be visible for the
chain proof. This made the function ~200 lines with `#[verifier::rlimit(20)]`,
which still exceeds the solver budget. All subsequent assertion failures cascade
from the rlimit exceeded error.

## The Fix: Distributed Modular Postconditions

**Key insight**: instead of inlining carry folds for variable visibility, add
modular postconditions to `mersenne_carry_early` and `mersenne_carry_late`.
Each function proves its own piece. Then `mersenne_carry_folds` chains them,
and `mersenne_reduce_exec` becomes short enough for the solver.

### Mathematical basis

Each carry fold round is a Mersenne reduction step. The carries **telescope**:

```
Early chain (3 fold rounds):
  fold3 + cy3*lp = fold2 + wcy*BASE*c     ...(1)
  fold4 + cy4*lp = fold3 + cy2*c           ...(2)
  fold5 + cy5*lp = fold4 + cy3*c           ...(3)

Sum (1)+(2)+(3), cancel fold3 and fold4:
  fold5 + (cy3+cy4+cy5)*lp = fold2 + wcy*BASE*c + cy2*c + cy3*c

Rearrange:
  fold5 + cy4*c + cy5*c = fold2 + wcy*BASE*c + cy2*c - (cy3+cy4+cy5)*(lp-c)
                        = fold2 + wcy*BASE*c + cy2*c - K*p    (K = cy3+cy4+cy5)

Therefore: (fold5 + cy4*c + cy5*c) % p == (fold2 + wcy*BASE*c + cy2*c) % p
```

Same approach for the late chain (4 fold rounds):
```
  fold9 = fold5 + cy4*c + cy5*c - K'*p    (K' = cy6+cy7+cy8)
  => fold9 % p == (fold5 + cy4*c + cy5*c) % p
```

After conditional subtract: `result % p == fold9 % p` and `result < p`.

Chaining all three: `result % p == (fold2 + wcy*BASE*c + cy2*c) % p`.

And the Phase 1 proof (already written, just needs rlimit budget):
`(fold2 + wcy*BASE*c + cy2*c) % p == product % p`.

## Concrete Steps

### Step 1: Add `lemma_carry_early_mod` proof fn

Place before `mersenne_carry_early`. Takes ghost values for the 3 fold equations
and proves the telescoping sum equals K*p.

```rust
proof fn lemma_carry_early_mod(
    lp: int, ci: int,
    f2: int, wbc: int, cy2c: int,      // fold2 val, wcy*BASE*c, cy2*c
    f3: int, c3: int,                   // fold3 + cy3*lp == f2 + wbc
    f4: int, c4: int,                   // fold4 + cy4*lp == f3 + cy2c
    f5: int, c5: int,                   // fold5 + cy5*lp == f4 + cy3*c
)
    requires
        lp > 0, ci > 0, lp > ci,
        f2 >= 0, f3 >= 0, f4 >= 0, f5 >= 0,
        c3 >= 0, c4 >= 0, c5 >= 0, wbc >= 0, cy2c >= 0,
        f3 + c3 * lp == f2 + wbc,
        f4 + c4 * lp == f3 + cy2c,
        f5 + c5 * lp == f4 + c3 * ci,
    ensures
        (f5 + c4 * ci + c5 * ci) as nat % ((lp - ci) as nat)
            == (f2 + wbc + cy2c) as nat % ((lp - ci) as nat),
{
    let k: int = c3 + c4 + c5;
    // Telescoping: sum 3 equations, cancel f3 and f4
    assert(f5 + c4 * ci + c5 * ci + k * (lp - ci) == f2 + wbc + cy2c)
        by(nonlinear_arith)
        requires
            f3 + c3 * lp == f2 + wbc,
            f4 + c4 * lp == f3 + cy2c,
            f5 + c5 * lp == f4 + c3 * ci,
            k == c3 + c4 + c5;
    // Modular conclusion
    assert(f5 + c4 * ci + c5 * ci >= 0) by(nonlinear_arith)
        requires f5 >= 0, c4 >= 0, c5 >= 0, ci >= 0;
    assert(k >= 0) by(nonlinear_arith) requires c3 >= 0, c4 >= 0, c5 >= 0;
    lemma_mod_add_left(
        (k * (lp - ci)) as nat,
        (f5 + c4 * ci + c5 * ci) as nat,
        (lp - ci) as nat,
    );
    assert(((k * (lp - ci)) as nat) % ((lp - ci) as nat) == 0nat)
        by(nonlinear_arith) requires lp > ci, k >= 0;
}
```

### Step 2: Add modular postcondition to `mersenne_carry_early`

Add to ensures:
```rust
(vec_val(out.0@) + out.1 as int * (c as int) + out.2 as int * (c as int)) as nat
    % ((limb_power(n as nat) - c as int) as nat)
== (vec_val(fold2@) + wide_cy as int * LIMB_BASE() * (c as int)
    + cy2 as int * (c as int)) as nat
    % ((limb_power(n as nat) - c as int) as nat),
```

And add proof at end of function body:
```rust
proof {
    let lp = limb_power(n as nat);
    let ci = c as int;
    lemma_vec_val_bounded(fold2@); lemma_vec_val_bounded(fold3@);
    lemma_vec_val_bounded(fold4@); lemma_vec_val_bounded(fold5@);
    lemma_vec_val_bounded(wcy_vec@); lemma_vec_val_bounded(cy2_vec@);
    lemma_vec_val_bounded(cy3_vec@);
    lemma_limb_power_add(1, 1); reveal_with_fuel(limb_power, 2);
    assert(lp > ci) by(nonlinear_arith)
        requires lp >= LIMB_BASE() * LIMB_BASE(), ci < LIMB_BASE(), ci > 0;
    lemma_carry_early_mod(lp, ci,
        vec_val(fold2@), vec_val(wcy_vec@), vec_val(cy2_vec@),
        vec_val(fold3@), cy3 as int,
        vec_val(fold4@), cy4 as int,
        vec_val(fold5@), cy5 as int);
}
```

**Key detail**: The requires `f5 + c5 * lp == f4 + c3 * ci` is satisfied
because:
- `generic_add_limbs` gives: `vec_val(fold5@) + cy5*lp == vec_val(fold4@) + vec_val(cy3_vec@)`
- `scalar_to_padded_vec` gives: `vec_val(cy3_vec@) == cy3_c as int`
- exec: `cy3_c = cy3 * c` (no overflow since cy3 <= 1, c < BASE)
- So: `vec_val(cy3_vec@) == cy3 as int * ci == c3 * ci`

### Step 3: Add `lemma_carry_late_mod` proof fn

Same telescoping approach for the 4 late fold rounds:

```rust
proof fn lemma_carry_late_mod(
    lp: int, ci: int,
    f5: int, c4i: int, c5i: int,       // inputs from early
    f6: int, c6: int,                   // fold6 + cy6*lp = f5 + cy4*c
    f7: int, c7: int,                   // fold7 + cy7*lp = f6 + cy5*c
    f8: int, c8: int,                   // fold8 + cy8*lp = f7 + fc
    fc: int,                            // (cy6+cy7)*c
    f9: int,                            // fold9 = f8 + cy8*c (cy9==0)
)
    requires
        lp > 0, ci > 0, lp > ci,
        f5 >= 0, f6 >= 0, f7 >= 0, f8 >= 0, f9 >= 0,
        c4i >= 0, c5i >= 0, c6 >= 0, c7 >= 0, c8 >= 0,
        f6 + c6 * lp == f5 + c4i * ci,
        f7 + c7 * lp == f6 + c5i * ci,
        f8 + c8 * lp == f7 + fc,
        fc == (c6 + c7) * ci,
        f9 == f8 + c8 * ci,            // cy9 == 0
    ensures
        f9 as nat % ((lp - ci) as nat)
            == (f5 + c4i * ci + c5i * ci) as nat % ((lp - ci) as nat),
{
    let k: int = c6 + c7 + c8;
    assert(f9 + k * (lp - ci) == f5 + c4i * ci + c5i * ci)
        by(nonlinear_arith)
        requires
            f6 + c6 * lp == f5 + c4i * ci,
            f7 + c7 * lp == f6 + c5i * ci,
            f8 + c8 * lp == f7 + (c6 + c7) * ci,
            f9 == f8 + c8 * ci,
            k == c6 + c7 + c8;
    // ... same mod conclusion as early ...
}
```

### Step 4: Add modular postcondition to `mersenne_carry_late`

Add to ensures:
```rust
vec_val(out@) as nat % ((limb_power(n as nat) - c as int) as nat)
    == (vec_val(fold5@) + cy4 as int * (c as int) + cy5 as int * (c as int)) as nat
        % ((limb_power(n as nat) - c as int) as nat),
(vec_val(out@) as nat) < ((limb_power(n as nat) - c as int) as nat),
```

The proof needs:
1. Prove cy9 == 0 (already in existing code)
2. Call `lemma_carry_late_mod` for the chain
3. Call `lemma_cond_sub` for the first conditional subtract
4. Prove second conditional subtract is a no-op (r1 < p => bw2 == 1)
5. Conclude: out == r1, r1 % p == fold9 % p == (fold5+cy4*c+cy5*c) % p

### Step 5: Fix `mersenne_carry_folds`

With early and late having modular postconditions, the proof is trivial
(Z3 chains the equalities automatically):
```rust
fn mersenne_carry_folds(...) -> (out: Vec<u32>)
    requires ...
    ensures
        ..., // existing structural postconditions
        vec_val(out@) as nat % p == (fold2 + wcy*BASE*c + cy2*c) as nat % p,
        vec_val(out@) as nat < p,
{
    let (fold5, cy4, cy5) = mersenne_carry_early(fold2, cy2, wide_cy, n, c);
    let r = mersenne_carry_late(&fold5, cy4, cy5, n, c);
    // from early: (fold5+cy4*c+cy5*c) % p == (fold2+wcy*BASE*c+cy2*c) % p
    // from late:  r % p == (fold5+cy4*c+cy5*c) % p
    // Z3 chains automatically
    r
}
```

### Step 6: Rewrite `mersenne_reduce_exec`

Remove ALL inlined carry fold code (lines ~793-867). Remove `#[verifier::rlimit(20)]`.
Use `mersenne_carry_folds` instead:

```rust
fn mersenne_reduce_exec(product: &Vec<u32>, n: usize, c: u32) -> (out: Vec<u32>)
    requires ...
    ensures ...
{
    // Split + first fold + second fold (existing code, ~30 lines)
    let lo = generic_slice_vec(product, 0, n);
    let hi = generic_slice_vec(product, n, 2 * n);
    let hi_c = generic_mul_by_limb(&hi, &c_limb, n);
    let lo_pad = generic_pad_to_length(&lo, n + 1);
    let (wide, wide_cy) = generic_add_limbs(&lo_pad, &hi_c, n + 1);
    let wide_lo = generic_slice_vec(&wide, 0, n);
    let wide_top: u32 = wide[n];
    let (wt_lo, wt_hi) = wide_top.mul2(&c_limb);
    let wt_vec = pair_to_padded_vec(wt_lo, wt_hi, n);
    let (fold2, cy2) = generic_add_limbs(&wide_lo, &wt_vec, n);

    proof { /* carry bounds: wide_cy <= 1, cy2 <= 1 */ }

    // Carry folds + conditional subtract (ONE CALL)
    let r = mersenne_carry_folds(&fold2, cy2, wide_cy, n, c);

    proof {
        // Phase 1: (fold2 + wcy*BASE*c + cy2*c) % p == product % p
        // (existing ~30-line algebraic proof from lines 918-969)
        // ...
        // From carry_folds postcondition: r % p == (fold2+extra) % p
        // Transitivity: r % p == product % p
    }
    r
}
```

This makes the function ~80 lines total (exec + Phase 1 proof), well within
default rlimit.

### Step 7: `mul_mod` should verify automatically

It just calls `mersenne_reduce_exec` and proves `gc == 0`. No changes needed.

## Technical Details

### `generic_add_limbs` postcondition (key reference)
```rust
vec_val(result.0@) + result.1.sem() * limb_power(n as nat)
    == vec_val(a@) + vec_val(b@)
```
Where `.sem()` on u32 is `self as int`.

### `generic_sub_limbs` postcondition
```rust
vec_val(result.0@) + vec_val(b@) == vec_val(a@) + result.1.sem() * limb_power(n as nat)
```

### `lemma_mod_add_left(a, b, p)` — the workhorse
```
ensures (a % p + b) % p == (a + b) % p
```
Used to peel off K*p from the telescoping sum.

### `lemma_cond_sub` — conditional subtract correctness
```
requires diff + pv == val + borrow * lp, pv == lp - ci, 2*ci <= lp, ...
ensures
    borrow == 0 ==> diff == val % pv && diff < pv
    borrow == 1 ==> val == val % pv && val < pv
```

### Why `2 * ci <= lp` holds
- `ci < LIMB_BASE()` (from PrimeSpec)
- `lp = limb_power(n) >= limb_power(2) = LIMB_BASE()^2` (from n >= 2)
- So `2*ci < 2*LIMB_BASE() <= LIMB_BASE()^2 <= lp`
- Prove: `lemma_limb_power_add(1, 1); reveal_with_fuel(limb_power, 2);`

### Why `lp > ci` holds
Same reasoning: `lp >= LIMB_BASE()^2 > LIMB_BASE() > ci`.

### The `lp >= LIMB_BASE()^2` for general n >= 2
Use `lemma_limb_power_add(2, (n-2) as nat)` to get
`limb_power(n) == limb_power(2) * limb_power(n-2)`, then
`limb_power(n-2) >= 1` (limb_power is always >= 1, may need fuel).
Or: the existing carry_late code already establishes
`lpl >= limb_power(2nat)` (see line 843), so this pattern is known to work.

## What Can Be Removed After Completion

- `lemma_reduce_chain` and `lemma_mersenne_chain` — these were written for the
  inlined approach. The distributed approach (early/late mod lemmas) supersedes
  them. Keep as mathematical documentation if desired.
- The inlined carry fold code in `mersenne_reduce_exec` (lines ~793-867)
- The `#[verifier::rlimit(20)]` annotation on `mersenne_reduce_exec`

## Potential Issues

1. **nonlinear_arith with 3-4 equations**: The telescoping proof feeds 3-4 fold
   equations to `by(nonlinear_arith)`. If the solver struggles, fall back to
   step-by-step substitution (2 equations each), like `lemma_reduce_chain` does.

2. **vec_val connections**: Z3 needs to connect `vec_val(cy3_vec@)` to
   `cy3 as int * c as int`. This chain goes through:
   - `scalar_to_padded_vec` postcondition: `vec_val(cy3_vec@) == cy3_c as int`
   - exec: `cy3_c = cy3 * c` (u32 multiplication, no overflow)
   If Z3 can't close this automatically, add explicit `assert(vec_val(cy3_vec@) == cy3 as int * ci)`.

3. **Phase 1 proof in `mersenne_reduce_exec`**: The existing algebraic proof
   (lines 918-969) should work once the function is shortened. If not, extract
   it into a separate `proof fn lemma_phase1_reduce(...)`.

## File Map

```
verus-fixed-point/src/fixed_point/prime_field.rs
  Lines 1-178:    SpecPrimeField + Ring trait implementation (DONE)
  Lines 180-201:  lemma_pseudo_mersenne_reduce (DONE)
  Lines 203-500:  Helper functions and chain lemmas (DONE)
  Lines 500-610:  lemma_reduce_chain (DONE, may be superseded)
  Lines 612-657:  mersenne_carry_early (NEEDS modular postcondition)
  Lines 659-727:  mersenne_carry_late (NEEDS modular postcondition + cond_sub proof)
  Lines 729-746:  mersenne_carry_folds (NEEDS proof from chaining)
  Lines 748-975:  mersenne_reduce_exec (NEEDS rewrite: remove inline, use carry_folds)
  Lines 977-1207: RuntimePrimeField methods (add_mod DONE, mul_mod NEEDS reduce_exec)
```
