# verus-fixed-point: Design Document

## Goal

A formally verified fixed-point arithmetic library for Verus, designed for GPU shader
use (deep fractal zooms). All fixed-point operations are **exact** — the spec directly
corresponds to the implementation with no approximation gap. Precision management is
handled at the interval layer via explicit `reduce` operations.

## Non-goals

- Arbitrary-precision bignum (that's verus-rational/verus-bigint)
- Floating-point emulation
- Dynamic precision changes at runtime (precision is a compile-time const generic)

## Architecture

```
Layer 3:  FixedPointInterval<N, FRAC>     (exec, GPU-friendly)
          wraps two FixedPoints + Ghost<Interval>
          reduce() is the ONLY place precision is lost
          reuses all spec-level Interval proofs from verus-interval-arithmetic

Layer 2:  Interval (spec, from verus-interval-arithmetic)
          ~220 lemmas already proved: containment, monotonicity, etc.
          no changes needed — reused as-is

Layer 1:  FixedPoint<N, FRAC>             (exec, the core type)
          view() -> Rational              (exact, no approximation)
          all arithmetic is exact          (spec == exec)

Layer 0:  Rational (spec, from verus-rational)
          field axioms, ordering, etc.     (already proved)
```

Key property: **no leakage between layers**. FixedPoint operations are exact, so proofs
at the Rational level carry over perfectly. The only approximation is `reduce`, which
is explicit and tracked by interval width.

## Core Types

### FixedPoint<const N: usize, const FRAC: usize>

```rust
/// Fixed-point number with N u32 limbs, FRAC fractional bits.
/// Sign-magnitude representation: separate sign + unsigned limbs.
///
/// Total magnitude bits: N * 32
/// Integer bits: N * 32 - FRAC
/// Fractional bits: FRAC
///
/// Represents: (-1)^sign * magnitude * 2^(-FRAC)
/// where magnitude is the unsigned integer formed by the limbs.
pub struct FixedPoint<const N: usize, const FRAC: usize> {
    pub sign: bool,           // true = negative
    pub limbs: [u32; N],      // little-endian unsigned magnitude
}
```

**Why sign-magnitude over two's complement:**
- Simpler multiplication (multiply magnitudes, XOR signs)
- No asymmetry (two's complement has one extra negative value)
- GPU shaders work with unsigned integers; sign-magnitude maps cleanly
- Easier to reason about in proofs (magnitude is always non-negative)

**Canonical zero invariant:** `wf_spec` requires `sign == true ==> limbs_to_nat(limbs) != 0`.
This eliminates the -0/+0 ambiguity inherent in sign-magnitude. Zero is always
represented as `{ sign: false, limbs: [0; N] }`. This is one extra proof obligation
on every operation that constructs a FixedPoint, but it means equality is structural
(`a == b <==> a@ eqv b@`) and simplifies all downstream reasoning about zero.

**Spec interpretation:**
```rust
impl<const N: usize, const FRAC: usize> FixedPoint<N, FRAC> {
    /// The exact rational value this fixed-point number represents.
    pub open spec fn view(&self) -> Rational {
        let magnitude: nat = limbs_to_nat(self.limbs);
        let sign_factor: int = if self.sign { -1 } else { 1 };
        Rational::from_frac_spec(sign_factor * magnitude, pow2(FRAC))
    }
}
```

### FixedPointInterval<const N: usize, const FRAC: usize>

```rust
/// Interval backed by fixed-point endpoints.
/// The ghost `exact` tracks the true value being computed on.
pub struct FixedPointInterval<const N: usize, const FRAC: usize> {
    pub lo: FixedPoint<N, FRAC>,    // lower bound (rounded toward -inf)
    pub hi: FixedPoint<N, FRAC>,    // upper bound (rounded toward +inf)
    pub model: Ghost<Interval>,      // spec-level interval
}

/// Well-formedness:
///   lo.view() == model@.lo
///   hi.view() == model@.hi
///   model@.wf_spec()    (i.e., lo <= hi)
```

## Operations & Properties

### FixedPoint — all exact

| Operation | Signature | Property |
|-----------|-----------|----------|
| `add` | `(a: FP<N,F>, b: FP<N,F>) -> FP<N,F>` | `out@ == a@ + b@` (requires no overflow) |
| `sub` | `(a: FP<N,F>, b: FP<N,F>) -> FP<N,F>` | `out@ == a@ - b@` (requires no overflow) |
| `neg` | `(a: FP<N,F>) -> FP<N,F>` | `out@ == -a@` |
| `mul` | `(a: FP<N,F>, b: FP<N,F>) -> FP<{2*N},{2*F}>` | `out@ == a@ * b@` (exact, widens) |
| `cmp` | `(a: FP<N,F>, b: FP<N,F>) -> Ordering` | matches `a@.le_spec(b@)` etc. |
| `is_zero` | `(a: FP<N,F>) -> bool` | `result == (a@ eqv zero)` |
| `from_int` | `(n: i64) -> FP<N,F>` | `out@ == Rational::from_int(n)` |

**Exact means exact.** No rounding modes, no error terms, no approximation.
The `view()` of the result is always precisely the mathematical operation applied
to the `view()`s of the inputs.

Multiplication widens: two N-limb inputs produce a 2N-limb output. This is
where the interval layer comes in — `reduce` narrows back to N limbs.

### FixedPointInterval — precision management

| Operation | Property |
|-----------|----------|
| `add` | exact (delegates to FP add) |
| `sub` | exact (delegates to FP sub) |
| `neg` | exact (delegates to FP neg) |
| `mul` | exact but widens to `FixedPointInterval<2N, 2F>` |
| `square` | exact but widens, tighter than mul (uses `square_spec`) |
| `reduce` | **narrows precision**: lo rounds down, hi rounds up |
| `contains` | `self@.lo <= x <= self@.hi` (spec level) |
| `width` | `self@.hi - self@.lo` (tracks precision loss) |

`reduce` is the critical operation:
```rust
/// Narrow a wide interval to working precision.
/// This is the ONLY place precision is lost.
/// Proven to preserve containment via existing Interval lemmas.
pub fn reduce<const M: usize, const FM: usize>(
    wide: FixedPointInterval<M, FM>
) -> FixedPointInterval<N, FRAC>
    ensures
        // anything in the input interval is in the output interval
        forall |x: Rational| wide@.contains(x) ==> result@.contains(x)
```

**What reduce does mechanically:** Going from `FixedPoint<M, FM>` to
`FixedPoint<N, FRAC>` where `FM > FRAC`:

1. **Bit-shift** the magnitude right by `(FM - FRAC)` bits. This rescales
   from `* 2^(-FM)` to `* 2^(-FRAC)`. For `lo` use floor-shift (round toward
   zero then adjust for sign), for `hi` use ceil-shift.
2. **Truncate** to N limbs (the upper limbs after shifting). If any upper limbs
   are nonzero, the value doesn't fit — this is an overflow condition.

The shift is NOT just dropping limbs. Example: `FixedPoint<8, 192>` to
`FixedPoint<4, 96>` requires shifting right by 96 bits (3 full limbs), then
keeping the bottom 4 limbs. The shift amount `FM - FRAC` will typically be
a multiple of 32 (if FRAC conventions align), making it a pure limb-drop,
but the general case handles arbitrary bit offsets.

Proof obligation: `floor_shift(magnitude, FM - FRAC) * 2^(-FRAC)`
`== floor_dyadic_spec(value, FRAC)`, connecting our bit operations to
the existing dyadic rounding lemmas in verus-interval-arithmetic.

### Promotion (widening without precision loss)

When combining values of different precisions (e.g., a widened mul result with a
working-precision value), we need `promote`:

```rust
/// Widen a FixedPoint to a larger representation.
/// Zero-extends limbs, adjusts scale. Exact — no information lost.
/// Proves: result.view() == self.view()
pub fn promote<const M: usize, const FM: usize>(
    a: FixedPoint<N, FRAC>
) -> FixedPoint<M, FM>
    requires N <= M, FRAC <= FM
```

This is needed because `z_sq.add(c)` requires both operands at the same type.

### Mandelbrot iteration example

```
fn mandelbrot_step(z: FPI<4,96>, c: FPI<4,96>) -> FPI<4,96> {
    let z_sq = z.square();              // FPI<8,192>, exact
    let c_wide = c.promote::<8, 192>(); // FPI<8,192>, exact (zero-extend + scale)
    let sum = z_sq.add(&c_wide);        // FPI<8,192>, exact
    sum.reduce()                         // FPI<4,96>, lo rounded down, hi rounded up
}
```

After K iterations, the interval width tells you exactly how much precision you've
lost. When it gets too wide, increase N.

## Relationship to Existing Crates

### verus-rational
- `Rational` is our spec type — `view()` returns a `Rational`
- All field/ring axioms already proved
- We prove FixedPoint ops produce the same Rational results

### verus-interval-arithmetic
- `Interval` (spec level) is our interval model — reused as-is
- ~220 lemmas (containment, monotonicity, wf preservation) — all reused
- `floor_dyadic_spec` / `ceil_dyadic_spec` — directly relevant to our `reduce`
- `RuntimeInterval` is the CPU-exact version; `FixedPointInterval` is the GPU-fast version

### verus-algebra
- `Ring`, `Field`, `OrderedField` traits
- FixedPoint values view as Rationals, which already implement these traits
- `FixedPointInterval` could implement `RuntimeFieldOps<Rational>` since the ghost
  exact value IS a Rational and all field reasoning goes through Interval containment

## Multi-limb Arithmetic Foundations

The core of this library is proving multi-limb arithmetic correct. These are
the foundational lemmas we need:

### limbs_to_nat / nat_to_limbs

```rust
/// Interpret N little-endian u32 limbs as a nat.
pub open spec fn limbs_to_nat<const N: usize>(limbs: [u32; N]) -> nat {
    // limbs[0] + limbs[1] * 2^32 + limbs[2] * 2^64 + ...
}
```

### Multi-limb addition with carry

```rust
/// Add two N-limb numbers, returning N-limb result + carry bit.
/// Proves: result_nat + carry * 2^(N*32) == a_nat + b_nat
pub fn add_limbs(a: [u32; N], b: [u32; N]) -> (result: [u32; N], carry: u32)
```

### Multi-limb multiplication (Karatsuba)

For general use across precision levels, we use Karatsuba multiplication
(O(N^1.585)) rather than schoolbook (O(N^2)). This matters at higher precisions
(N=16 limbs = 512 bits and beyond).

**Karatsuba recurrence:** To multiply N-limb a and b, split each into
high/low halves (N/2 limbs each):
```
a = a_hi * B + a_lo       (where B = 2^(N/2 * 32))
b = b_hi * B + b_lo
a * b = z2 * B^2 + z1 * B + z0
  where z0 = a_lo * b_lo
        z2 = a_hi * b_hi
        z1 = (a_lo + a_hi)(b_lo + b_hi) - z0 - z2
```
3 recursive multiplications instead of 4. Base case: single-limb u32 * u32 -> u64.

```rust
/// Multiply two N-limb numbers via Karatsuba, returning 2N-limb exact result.
/// Proves: result_nat == a_nat * b_nat
/// Recursive: splits into 3 half-size multiplications.
pub fn mul_karatsuba(a: [u32; N], b: [u32; N]) -> (result: [u32; {2*N}])
```

**Proof strategy:** Induct on N. At each level, prove the recurrence identity
holds over nat, then show the limb operations (split, add-with-carry,
shift-and-accumulate) faithfully implement it. The key lemma is that the
intermediate `(a_lo + a_hi)` may be (N/2 + 1) limbs (one extra carry), which
needs careful handling.

### Shift / truncation for reduce

```rust
/// Right-shift by k bits, rounding down (floor).
/// Proves: result_nat == a_nat / 2^k (integer division)
pub fn shift_right_floor(a: [u32; M], k: usize) -> [u32; N]

/// Right-shift by k bits, rounding up (ceil).
/// Proves: result_nat == ceil(a_nat / 2^k)
pub fn shift_right_ceil(a: [u32; M], k: usize) -> [u32; N]
```

## Const Generics Strategy

Rust const generics don't yet support expressions like `{2*N}` in stable.
Since we want the library to be general across precision levels, our approach:

1. **Trait-based widening**: `trait MulWide { type Wide; fn mul_wide(...) -> Self::Wide; }`
   defines the N -> 2N relationship at the type level.
2. **Macro generation**: `define_fixed_point!(4, 8, 16)` generates all concrete types,
   cross-size operations, and trait impls. The proofs are written once in the macro
   body and instantiated for each size.
3. **Core algorithms are generic over slices**: Internal functions like `add_limbs`,
   `karatsuba_mul`, `shift_right` operate on `&[u32]` slices with length preconditions,
   avoiding the const generic expression problem entirely. The const-generic wrapper
   types are thin shells that call into the slice-based core.

This gives us the generality we want while working within Rust's current const
generic limitations. Adding a new precision level is one line in the macro invocation.

## Scaling to Extreme Precision (2^10000 zoom and beyond)

At zoom depth 2^D, you need ~D fractional bits to distinguish adjacent pixels.
For D=10000, that's ~313 u32 limbs. The design supports this with no architectural
changes — N can be any size via macro instantiation.

### Performance at extreme precision

| Precision | Limbs (N) | Karatsuba mul | NTT mul | Add/sub |
|-----------|-----------|---------------|---------|---------|
| 128-bit   | 4         | ~64 ops       | (overkill) | 4 ops |
| 512-bit   | 16        | ~580 ops      | ~260 ops | 16 ops |
| 1024-bit  | 32        | ~1,740 ops    | ~580 ops | 32 ops |
| 10000-bit | 313       | ~8,500 ops    | ~2,700 ops | 313 ops |
| 100000-bit| 3125      | ~260,000 ops  | ~40,000 ops | 3125 ops |

(ops = u32 multiplications; add/sub is u32 additions)

### NTT (Number Theoretic Transform) multiplication

For very deep zooms (N > ~64 limbs), NTT-based multiplication gives O(N log N)
instead of Karatsuba's O(N^1.585). This is significant at high precision:
at N=3125, NTT is ~6.5x faster than Karatsuba.

**How it works:** NTT is the integer analogue of FFT. Multiply by:
1. NTT-transform both inputs (O(N log N))
2. Pointwise multiply in transform domain (O(N))
3. Inverse NTT (O(N log N))
4. Carry propagation (O(N))

Work modulo a prime p where p = k * 2^m + 1 (NTT-friendly prime), chosen so
that N divides 2^m. Common choice: p = 2^32 - 2^20 + 1 (Goldilocks prime) for
u32 limbs, or use multiple primes + CRT for larger products.

**Proof strategy:** Prove NTT is a ring homomorphism (preserves + and *) from
Z[x]/(x^N - 1) to Z^N, then show that polynomial multiplication via evaluate-
pointwise-multiply-interpolate recovers the correct product. The carry propagation
step is proved separately (same as schoolbook carry chain).

**Integration:** Same interface as Karatsuba — `mul_ntt(a, b) -> result` with
`ensures result_nat == a_nat * b_nat`. The FixedPoint layer doesn't care which
multiplication backend is used. We can dispatch based on N:
- N <= 16: Karatsuba (lower constant overhead)
- N > 16: NTT (better asymptotic)

NTT also maps well to GPU compute shaders (butterfly operations are parallel).

### Perturbation theory for fractal rendering

At extreme zoom depths, the dominant rendering technique is **perturbation theory**:
instead of computing each pixel's orbit at full precision, compute one reference
orbit at full precision (on CPU), then for each pixel compute only the delta
from the reference orbit at much lower precision (on GPU).

**Mathematical basis:** For Mandelbrot z_{n+1} = z_n^2 + c, write
z_n = Z_n + delta_n where Z_n is the reference orbit. Then:
```
delta_{n+1} = 2 * Z_n * delta_n + delta_n^2 + delta_c
```
Z_n is precomputed at full precision. delta_n and delta_c are small (relative
to Z_n), so they can be represented at much lower precision — often 128-256 bits
suffices even at 10000-bit zoom depth.

**How this fits our design:**
- `FixedPointInterval<N_full, FRAC_full>` — reference orbit, computed on CPU,
  N_full = 313 limbs for 10000-bit zoom
- `FixedPointInterval<N_delta, FRAC_delta>` — per-pixel delta, computed on GPU,
  N_delta = 4-8 limbs (128-256 bits)
- The interval width of the delta tells you when the perturbation approximation
  has degraded and the pixel needs to be "rebased" to a closer reference point
  or recomputed at full precision
- `promote` and `reduce` handle the precision transitions between reference
  and delta computations

**Key operations for perturbation:**
- `mul_mixed(full: FP<N_full>, delta: FP<N_delta>) -> FP<N_delta>`:
  multiply a full-precision reference value by a low-precision delta, keeping
  only delta-precision bits in the result. This is NOT exact — it's a reduce
  wrapped around a conceptually wider multiply. But the interval tracks the error.
- `rebase(delta: FPI<N_delta>, new_ref: FP<N_full>, old_ref: FP<N_full>) -> FPI<N_delta>`:
  shift delta to be relative to a new reference point.

This turns a 10000-bit GPU problem into a 256-bit GPU problem for 99%+ of pixels,
making real-time deep zoom rendering feasible.

## Implementation Phases

### Phase 1: Core FixedPoint type
- [ ] Crate scaffolding (Cargo.toml, lib.rs, module structure)
- [ ] `limbs_to_nat` spec function + basic properties
- [ ] `FixedPoint<N, FRAC>` struct + `view() -> Rational`
- [ ] Well-formedness predicate
- [ ] Zero / one constants
- [ ] Equality and comparison

### Phase 2: Exact arithmetic
- [ ] Multi-limb addition with carry chain (+ correctness proof)
- [ ] Multi-limb subtraction with borrow chain (+ correctness proof)
- [ ] Negation
- [ ] FixedPoint add/sub wrapping limb ops (+ exact spec correspondence)
- [ ] Karatsuba multiplication (+ correctness proof via induction on N)
- [ ] FixedPoint mul with widening (+ exact spec correspondence)
- [ ] Promotion (widening without precision loss)

### Phase 3: Precision management
- [ ] Right-shift floor / ceil (for reduce)
- [ ] Prove floor_shift corresponds to floor_dyadic_spec
- [ ] Prove ceil_shift corresponds to ceil_dyadic_spec
- [ ] Truncation from wide to narrow with rounding

### Phase 4: FixedPointInterval
- [ ] Struct definition + wf_spec
- [ ] Interval add/sub/neg (delegating to exact FP ops)
- [ ] Interval mul (widening, then reduce)
- [ ] Interval square (tighter than mul-self)
- [ ] Prove containment via existing Interval lemmas
- [ ] reduce operation with proven soundness

### Phase 5: Algebra integration
- [ ] RuntimeFieldOps<Rational> for FixedPointInterval
- [ ] Verify it can plug into RuntimeQExt for quadratic extensions
- [ ] Mandelbrot iteration example as integration test

### Phase 6: NTT multiplication
- [ ] NTT-friendly prime selection (Goldilocks or multi-prime CRT)
- [ ] NTT forward/inverse transform (butterfly operations)
- [ ] Prove NTT is a ring homomorphism
- [ ] Pointwise multiply + inverse NTT + carry propagation
- [ ] End-to-end correctness: `result_nat == a_nat * b_nat`
- [ ] Dispatch: Karatsuba for N <= 16, NTT for N > 16

### Phase 7: Perturbation theory support
- [ ] `mul_mixed` (full-precision * delta-precision -> delta-precision)
- [ ] `rebase` (shift delta to new reference point)
- [ ] Reference orbit storage (sequence of full-precision values)
- [ ] Proven error tracking: interval width bounds perturbation error
- [ ] Glitch detection: when delta interval grows too wide, flag for recompute

### Phase 8: GPU codegen (future)
- [ ] WGSL/GLSL code generation from verified algorithms
- [ ] Or: extraction of the Rust exec code to shader-compatible form
- [ ] NTT butterfly maps naturally to GPU compute shader workgroups
