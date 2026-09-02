# Floating-Point Associativity-Gap Verification Plan

## Baseline and scope

This work uses the `float-associativity-verification` branch, based on
`update-lean-4.34`.  The repository is based on upstream Talos commit
`24047c6`, and every Lean package is pinned to `leanprover/lean4:v4.34.0-rc2`.

The first verified operation uses WebAssembly `f32`.  Inputs `a`, `b`, and `c`
must be finite and satisfy `|a| <= 1`, `|b| <= 1`, and `|c| <= 1`.  The target
epsilon is `2^-20`.  These hypotheses exclude NaNs, infinities, and overflow,
and they give a meaningful magnitude-independent error bound.

## Program

Add a hand-written WAT module exporting this function:

```wat
(module
  (func (export "assoc_gap")
    (param f32 f32 f32) (result f32)
    local.get 0
    local.get 1
    local.get 2
    f32.add
    f32.add
    local.get 0
    local.get 1
    f32.add
    local.get 2
    f32.add
    f32.sub
    f32.abs))
```

The function returns
`abs((a + (b + c)) - ((a + b) + c))`, with every arithmetic operation using
WebAssembly binary32 semantics.

## Milestones

1. Add the decoded WAT example and verify its function signature, export, and
   instruction sequence.  Add executable checks for an exactly associative
   input and a finite non-associative input.
2. Prove a symbolic small-step trace for arbitrary input bit patterns.  Package
   the trace as `SmallStep.TerminatesWith`, and derive `PartiallyMeets`.
3. Add a reusable pure binary32 model.  Decode finite bit patterns to exact
   dyadic values, classify exceptional values, model round-to-nearest with
   ties-to-even, and specify canonical NaN behavior.
4. Make `f32.add` and `f32.sub` use a pure executable implementation whose
   result can be related to the mathematical model without trusted floating-
   point bridge axioms.  Keep the native implementation only as a differential
   test oracle if it remains useful.
5. Prove finite-result and rounding-error lemmas for binary32 addition,
   subtraction, and absolute value.  Include normal, subnormal, signed-zero,
   infinity, and NaN cases in the operation-level specification.
6. Prove that finite inputs bounded by one produce a finite associativity gap
   strictly below `2^-20`.
7. Compose the numerical theorem with the symbolic WAT execution theorem to
   obtain a fuel-independent `SmallStep.TerminatesWith` theorem for the decoded
   program.

## Validation

At each milestone, run the affected package build under Lean 4.34.  Final
validation consists of the interpreter and codelib builds, executable decoder
and edge-case checks, differential tests against native binary32, `git diff
--check`, and `#print axioms` on the final theorem.  The final theorem must not
depend on the existing trusted axioms in `CodeLib.IEEE32.Exec`.

Each buildable milestone will be committed and pushed to
`origin/float-associativity-verification`.  Progress, decisions, commands,
results, and outstanding work will be recorded in `journal.md`.

## Completion status

All seven milestones are complete on `float-associativity-verification`.
The final public theorem is
`CodeLib.IEEE32.assocGap_terminates_lt_epsilon`.  It combines the arbitrary-
input symbolic execution trace with finite-input numerical hypotheses and
proves that the returned binary32 value is finite and strictly below the fixed
real tolerance `epsilon = 2^-20`.

## Exceptional-value extension

The extension now also specifies and proves canonical NaN propagation,
signed-infinity identities and invalid combinations, and overflow for finite
addition and subtraction.  The overflow theorem uses the exact scaled
round-to-nearest threshold `2^277 - 2^252`, corresponding to the real midpoint
`2^128 - 2^103` above the largest finite binary32 value.

## Floating-point operation roadmap

The next phase extends the proof-visible IEEE-754 layer across the operation
families used by WebAssembly programs.  Each milestone has four deliverables:
an executable operation used by the interpreter, native differential tests,
operation-level specifications, and a decoded or hand-written WAT example with
a fuel-independent small-step theorem.  Proof statements will distinguish
finite, NaN, infinity, overflow, underflow, subnormal, and signed-zero behavior
where those cases are semantically relevant.

1. **Binary32 multiplication.**  Generalize the ties-to-even rounder to exact
   dyadic products, implement `f32.mul` without the native floating-point
   bridge, and prove finite error, zero/infinity/NaN, overflow, and underflow
   results.  Verify a WAT `mul_error` program against a fixed error bound.
2. **Binary32 division.**  Add exact rational rounding with quotient/remainder
   tie handling.  Prove normal and subnormal rounding, division by zero,
   zero/infinity, infinity/infinity, NaN, overflow, and underflow behavior.
   Verify a WAT relative-error example on a bounded nonzero domain.
3. **Binary32 square root.**  Add correctly rounded integer-square-root
   semantics.  Prove exact-square examples, a rounding enclosure, signed-zero,
   positive infinity, NaN, and negative-input behavior.  Verify a WAT
   square-and-root program under a nonnegative bounded-input hypothesis.
4. **Selection, comparison, sign, conversion, and integral rounding.**  Make
   comparisons, `min`, `max`, `copysign`, integer/float conversions, saturating
   conversions, `ceil`, `floor`, `trunc`, and `nearest` proof-visible.  Remove
   the corresponding legacy bridge axioms once their users have constructive
   replacements.  Add WAT examples proving ordered clamps, sign transfer,
   conversion round trips on exact ranges, saturation, and integral-rounding
   properties.
5. **Binary64.**  Parameterize or reproduce the verified representation and
   rounding results for 11 exponent bits and 52 fraction bits.  Replace native
   `f64` arithmetic in the reference semantics and verify representative f64
   error-bound and exceptional-value programs.
6. **SIMD.**  Lift verified scalar operations lane-wise to `f32x4` and `f64x2`.
   Verify example vector programs with per-lane postconditions, including NaN
   lanes and signed zeros where applicable.
7. **Transcendental algorithms.**  WebAssembly core has no transcendental
   instructions, so model concrete Wasm implementations or imports rather than
   inventing opcodes.  Start with range-reduced polynomial `exp2` or `sin` on a
   small stated interval; prove the approximation error plus accumulated
   floating-point error, and connect that bound to an example module's
   execution theorem.  Broader-domain reduction and correctly-rounded library
   contracts remain separate follow-up results.

### Sequencing and validation

Multiplication precedes division and square root because it establishes the
general dyadic rounding interface reused by later proofs.  Scalar f32 coverage
precedes f64 and SIMD to keep each semantic change reviewable.  Transcendental
work begins only after the core scalar error lemmas can bound every primitive
operation used by the selected algorithm.

Every milestone is committed and pushed independently.  It must build under
`leanprover/lean4:v4.34.0-rc2`, pass its executable comparisons and WAT
examples, pass `git diff --check`, and have its public theorems checked with
`#print axioms`.  Repository-wide failures in unchanged pinned dependencies
will continue to be recorded separately from the affected-target results.

### Roadmap implementation status

The representative end-to-end slice is implemented for every category above:

- f32 multiplication, division, and square root use pure integer/dyadic or
  rational rounding, with exact WAT execution theorems and exceptional-value
  examples.
- f32 comparison, min/max, copysign, integral rounding, and integer conversion
  are proof-visible.  Clamp, nearest-integer, conversion, and concrete
  round-trip programs exercise the operations.
- f64 scalar arithmetic, square root, selection, comparison, sign, and
  integral-rounding operations use a pure binary64 model.  A WAT multiplication
  theorem and full-width differential suite provide the first end-to-end f64
  instance.
- SIMD multiplication is lifted lane-wise for both `f32x4` and `f64x2`, with
  decoded WAT programs and per-lane theorems covering signed zero, infinity,
  and NaN lanes.
- The algorithm-level transcendental example implements `x - x^3 / 6` in
  ordinary f32 instructions.  Its arbitrary-input theorem gives the exact
  rounded program result, and a fixed-input analytic theorem connects the
  result to real sine and a strict epsilon bound.

This completes representative verified programs, not every quantitative
theorem suggested by the roadmap.  The next strengthening work is: general
real error bounds for multiplication/division/square root; proof-visible f64
integer conversions; removal of the five compatibility axioms in
`CodeLib.IEEE32.Exec`; and a nontrivial-interval Taylor-plus-roundoff theorem
for the sine polynomial.  Native floating point remains only as a regression
oracle for the implemented operations, except for the explicitly noted f64
conversion seam.

### Strengthening execution plan

1. Prove quantitative contracts for the exact dyadic, rational, and integer-
   square-root rounders.  Lift them to real-valued f32 multiplication,
   division, and square-root bounds under explicit finite/non-overflow domain
   hypotheses, then compose each result with its WAT execution theorem.
2. Replace the remaining native f64 integer-conversion seam with scaled-
   integer definitions for all four integer-to-f64 operations, four trapping
   conversions, and four saturating conversions.  Compare deterministic
   full-width samples and boundary cases with native `Float`, and expose
   operation and example-program theorems in CodeLib.
3. Remove the five compatibility axioms in `CodeLib.IEEE32.Exec`.  Preserve
   the names used by generated projects as proved compatibility theorems,
   derive the positive/negative saturation lemmas from scaled-value ordering,
   and rebuild the `FloatTrunc` and `FloatRound` specifications.
4. Strengthen the cubic sine example from one fixed input to a stated
   nontrivial interval.  Combine a real Taylor remainder theorem with the
   primitive f32 roundoff contracts, and attach the combined bound to the
   fuel-independent WAT execution theorem.

The f64 conversion implementation and axiom-removal refactor are complete and
pushed.  The first quantitative rounder contract now proves the exact signed
integer error of `roundDyadicMagnitude`, and its lift proves the real f32
multiplication error is at most `2^-23` whenever both finite inputs have
absolute value at most one.  Rational division, integer square root, and the
interval sine proof remain the next proof work.  Every passing unit above will
be committed and pushed before work proceeds to the next unit.
