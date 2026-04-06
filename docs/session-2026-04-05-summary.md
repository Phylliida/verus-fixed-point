# Session Summary: mul_mod + BoundedPrimeField + GPU Plan (2026-04-05)

## What Was Accomplished

### 1. mul_mod Fully Verified (117 → 150 verified, 0 errors)

**Problem**: `mersenne_reduce_exec` was ~200 lines with `#[verifier::rlimit(20)]` and still exceeded solver budget. All 6 errors cascaded from this.

**Solution**: Distributed modular postconditions with telescoping carries.

Instead of inlining carry folds for variable visibility (which bloats the function), we added modular postconditions to helper functions:

- **`lemma_carry_early_mod`**: Proves fold3-fold5 telescoping. Sum 3 fold equations, cancel fold3/fold4:
  ```
  fold5 + (cy3+cy4+cy5)*(lp-c) == fold2 + wcy*BASE*c + cy2*c
  ```
  Therefore `(fold5 + cy4*c + cy5*c) % p == (fold2 + wcy*BASE*c + cy2*c) % p`.

- **`lemma_carry_late_mod`**: Same for fold6-fold9 + conditional subtract.

- **`mersenne_carry_early`** and **`mersenne_carry_late`**: Now have modular postconditions in their ensures. `mersenne_carry_folds` chains them automatically (Z3 transitivity).

- **`mersenne_reduce_exec`**: Shrunk from ~200 to ~80 lines. Phase 1 algebraic proof (fold2 + extra ≡ product mod p) now fits comfortably within default rlimit. Split the big nonlinear_arith assertion into 3 steps (s*lp, k_reduce*lp, final chain) for robustness.

- **`mul_mod`**: Added explicit assertions connecting `vec_val(product@)` to `self.model@ * other.model@` and proving `vec_val(r@) == (a*b) % p`.

**Key technique**: `lemma_mod_add_left(k*p, value, p)` converts `value + k*p ≡ value (mod p)`. Used with `lemma_fundamental_div_mod` for the `(k*p) % p == 0` fact.

### 2. RuntimeOrderedRingOps Trait (verus-algebra, 351 verified)

**New trait** in `verus-algebra/src/traits/runtime.rs`:

```rust
pub trait RuntimeOrderedRingOps<V: OrderedRing>: Sized + View<V = V> {
    spec fn wf_spec(&self) -> bool;
    open spec fn add_wf(&self, rhs: &Self) -> bool { true }  // default: no-op
    open spec fn mul_wf(&self, rhs: &Self) -> bool { true }  // default: no-op
    
    fn add(...) requires self.wf_spec(), rhs.wf_spec(), self.add_wf(rhs) ...
    fn mul(...) requires self.wf_spec(), rhs.wf_spec(), self.mul_wf(rhs) ...
    fn le(...), fn lt(...), fn eq(...), fn neg(...), fn sub(...),
    fn copy(...), fn zero_like(...), fn one_like(...)
}
```

**Design**: Self-contained (not extending RuntimeRingOps) to support types where spec model differs between ring and ordering layers. For exact types (RuntimeRational, RuntimeQExt), `add_wf`/`mul_wf` default to `true` — no breaking changes. For BoundedPrimeField, they check bound constraints.

### 3. BoundedPrimeField<N, C> (71 verified, 0 errors, zero assumes)

**Architecture**:
```
SpecPrimeField<S>  ←→  RuntimePrimeField     (Ring, modular, UNCHANGED)
                            ↑ wraps
int (OrderedRing)  ←→  BoundedPrimeField<N,C> (ordered, bounded)
```

**Centered representation**: `centered(value, p) = if value <= (p-1)/2 { value } else { value - p }`. Maps [0, p) to [-(p-1)/2, (p-1)/2].

**Core lemmas** (all require p odd, i.e., p % 2 == 1):
- `lemma_centered_add`: `centered((a+b) % p) == centered(a) + centered(b)` when `|sum| ≤ (p-1)/2`
- `lemma_centered_mul`: Same for multiplication, using ka/kb case split (4 cases)
- `lemma_centered_neg`: `centered(p-a) == -centered(a)` for a > 0
- `lemma_centered_bounded`: `|centered(a)| ≤ (p-1)/2` always
- `lemma_centered_zero`: `centered(0) == 0`
- `lemma_odd_half`: For odd p > 2, `p == 2*half + 1` (via `fundamental_div_mod`)

**Exec helpers**:
- `is_negative_centered(val)`: Checks `centered(val) < 0` at runtime. Computes `2*val` via `generic_add_limbs(val, val)`, then compares against p via `generic_sub_limbs`. Carry > 0 → definitely negative. Carry == 0 → check borrow from p-subtraction.
- `limbs_equal(a, b, n)`: Limb-by-limb Vec<u32> comparison.

**Const generics**: `BoundedPrimeField<const N: usize, const C: u32>` fixes the prime p = 2^(32N) - C. All wf values share the same field — critical for eq/le correctness (no cross-prime comparison issues).

**Trait implementation** (`RuntimeOrderedRingOps<int>`):
- `add`: delegates to `inner.add_mod()`, proves centered correctness via `lemma_centered_add`
- `sub`: uses `inner.neg_mod()` + `inner.add_mod()` directly (not via trait neg, which hides the bound)
- `neg`: delegates to `inner.neg_mod()`, proves via `lemma_centered_neg`
- `mul`: delegates to `inner.mul_mod()`, proves via `lemma_centered_mul`
- `eq`: implemented as `le(a,b) && le(b,a)` — avoids needing positional representation uniqueness proof
- `le`: sign comparison via `is_negative_centered` + raw limb subtraction for same-sign values
- `lt`: `le && !eq`
- `copy`: `generic_slice_vec` to clone limbs
- `zero_like`: `generic_zero_vec` + `lemma_vec_val_zeros`
- `one_like`: `scalar_to_padded_vec(1, N)` (made pub for this)

**Dynamic bounds**:
- `add_wf`: `self.bound@ + rhs.bound@ ≤ half_prime`
- `mul_wf`: `self.bound@ * rhs.bound@ ≤ half_prime`
- Output bounds: add → `a.bound + b.bound`, mul → `a.bound * b.bound`

### 4. Rlimit Fixes

Adding new code increased Z3 context for existing functions:
- `mersenne_reduce_exec`: Split 7-require nonlinear_arith into 3 steps
- `recip_newton`: Scoped `fundamental_div_mod` inside `assert by {}` to reduce pollution

**Final state**: 898 verified, 0 errors across full verus-fixed-point crate.

## GPU Mandelbrot Plan

### Architecture

```
CPU path:  generic_add_limbs<u32>       → direct execution
GPU path:  generic_add_limbs<ArithLimb> → RuntimeArithExpr tree → WGSL
Both share: SpecPrimeField Ring proofs, LimbOps postconditions
```

The LimbOps trait is the key abstraction. `ArithLimb` (from verus-fractals) implements `LimbOps` by building expression trees instead of computing values. When `GenericPrimeField<ArithLimb>` calls `add_mod`, it generates an `ArithExpr` tree that encodes the full carry chain + conditional subtract. This tree compiles to WGSL.

### Phases

**Phase 1: Refactor RuntimePrimeField<T: LimbOps>** (START HERE)
- Convert `RuntimePrimeField` from `Vec<u32>` to `Vec<T>` in-place
- `c_exec` stays `u32` (small constant, converted to T via LimbOps methods)
- `make_p_limbs`, `pair_to_padded_vec`, `scalar_to_padded_vec` become generic
- `BoundedPrimeField<N, C>` pins to `RuntimePrimeField<u32>` explicitly
- Proofs transfer because they use `vec_val(limbs@) = limbs_val(sem_seq(limbs@))` which is generic via `T::sem()`
- Safety: commit first, revert if >20 proofs break
- Target: 898 verified, 0 errors

**Phase 2: ArithLimb Instantiation** (verus-fractals)
- `gen_prime_field_add_mod(a_vars, b_vars, n, c) → Vec<RuntimeArithExpr>`
- Constructs `GenericPrimeField<ArithLimb>` with variable-reference limbs
- Operations build expression trees; extract result limb expressions
- Pattern already demonstrated by `gen_mandelbrot_step` in gpu_codegen.rs

**Phase 3: Perturbation Kernel Assembly**
- Both reference orbit (`Z² + c`) and perturbation (`2Zδ + δ² + Δc`) on GPU
- Per-pixel iteration loop with escape detection via centered comparison
- ArithExpr → GpuExpr lowering (1:1 structural map)
- Iteration loop and escape check as GpuStmt control flow

**Phase 4: Fully Verified WGSL Emission**
- Through verus-gpu-transpiler GpuIR with verified wgsl_emit.rs
- No trusted template code — entire shader from verified IR
- Trust boundary: only GPU hardware execution

**Phase 5: CPU Setup + WebGPU Viewer**
- Initial center/zoom computed on CPU
- Convert to prime field limb arrays
- Upload, dispatch compute shader, read back iteration counts
- Color map and display

### Key Design Decisions
- **Refactor in-place** (not parallel type) — maximum code reuse
- **Fully verified emission** (not quick prototype) — no trusted template
- **Reference orbits on GPU** — needed for rebasing at deep zoom, same GenericPrimeField<ArithLimb>
- **BoundedPrimeField for escape** — centered ordering with dynamic bounds

## Technical Reference

### Files Modified This Session

| File | Lines | Change |
|------|-------|--------|
| `prime_field.rs` | ~1330 | +221 lines: carry lemmas, postconditions, reduce_exec rewrite, rlimit fixes |
| `bounded_prime_field.rs` | ~560 | NEW: centered representation, exec helpers, trait impl |
| `verus-algebra/.../runtime.rs` | ~200 | +60 lines: RuntimeOrderedRingOps trait |
| `runtime_fixed_point.rs` | minor | Scoped fundamental_div_mod for rlimit |

### Key Functions and Their Roles

| Function | File | Purpose |
|----------|------|---------|
| `lemma_carry_early_mod` | prime_field.rs | Telescoping proof for fold3-5 |
| `lemma_carry_late_mod` | prime_field.rs | Telescoping proof for fold6-9 |
| `mersenne_carry_early` | prime_field.rs | Early carry folds with modular postcondition |
| `mersenne_carry_late` | prime_field.rs | Late carry folds + conditional subtract with modular postcondition |
| `mersenne_carry_folds` | prime_field.rs | Chains early + late (Z3 transitivity) |
| `mersenne_reduce_exec` | prime_field.rs | Full Mersenne reduction (~80 lines) |
| `centered(value, p)` | bounded_prime_field.rs | Map [0,p) to [-(p-1)/2, (p-1)/2] |
| `is_negative_centered` | bounded_prime_field.rs | Runtime sign detection via 2x + p-compare |
| `lemma_odd_half(p)` | bounded_prime_field.rs | Establishes p == 2*half + 1 for odd p |

### Patterns Discovered

1. **Telescoping carries**: Sum N fold equations, cancel intermediates → `result + K*p == input`. One `lemma_mod_add_left` converts to modular equivalence.

2. **`by(nonlinear_arith)` can't unfold spec fns**: Use explicit case splits and `assert(centered(a, p) == a as int)` to guide Z3, then `by(nonlinear_arith)` for the arithmetic.

3. **`lemma_odd_half(p)`**: For any centered representation proof, call this first to establish `p == 2*half + 1`. Uses `fundamental_div_mod(p-1, 2)` + `(p-1) % 2 == 0` from p odd.

4. **Const generics for same-field guarantee**: `BoundedPrimeField<const N: usize, const C: u32>` ensures all wf values share the same prime. Critical for eq/le correctness.

5. **`eq` via `le(a,b) && le(b,a)`**: Avoids positional representation uniqueness proof (which requires proving `limbs_val` is injective on valid-digit sequences).

6. **sub via inner methods, not trait neg**: The trait's neg hides the output bound (only ensures `out.wf_spec()`). Using `inner.neg_mod()` + `inner.add_mod()` directly preserves bound visibility for the proof.

7. **Split big nonlinear_arith**: When a single assertion with 7+ requires hits rlimit, break into 2-3 intermediate steps (each ≤ 3 equations). Step-by-step substitution.
